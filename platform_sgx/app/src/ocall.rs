use std::fs::File;
use std::io::prelude::*;
use std::io::*;
use std::mem;
use std::net::TcpStream;
use std::os::unix::prelude::FromRawFd;
use std::time::SystemTime;
use std::{ptr, slice, str};

use log::warn;
use sgx_types::error::*;
use sgx_types::function::*;
use sgx_types::types::*;

use log::{debug, error, info};
use serde::{Deserialize, Serialize};

use crate::OUTPUT_BUFFER_SIZE;
use crate::SGX_PLATFORM_HEADER_SIZE;

#[derive(Serialize, Deserialize, Debug)]
pub struct IasQuoteReport {
    quote_timestamp: String,
    quote_status: String,
    // The whole response body.
    quote_report_raw: String,
    quote_body: String,
    quote_signature: String,
    quote_certificate: String,
    platform_info_blob: String,
}

#[no_mangle]
pub unsafe extern "C" fn u_log_ocall(
    string_ptr: *mut u8,
    string_len: u32,
    string_capacity: u32,
) -> u32 {
    let s = String::from_raw_parts(string_ptr, string_len as usize, string_capacity as usize);
    info!("[+] Enclave: {}", s);
    std::mem::forget(s);
    string_capacity
}

#[no_mangle]
pub unsafe extern "C" fn ocall_get_sigrl_from_intel(
    epid: *const EpidGroupId,
    epid_len: usize,
    socket_fd: c_int,
    sigrl: *mut u8,
    len: u32,
    sigrl_len: *mut u32,
    enclave_pub_key: *const u8,
    enclave_pub_key_len: u32,
) -> SgxStatus {
    info!(
        "[+] Performing ocall_get_sigrl_from_intel... The EPID is {:?}",
        *epid
    );
    // Forward this request and the public key to the SP.
    // Wrap a new tcp stream from the raw socket fd.
    let socket = TcpStream::from_raw_fd(socket_fd);
    let socket_clone = socket.try_clone().unwrap();
    let mut reader = BufReader::new(socket);
    let mut writer = BufWriter::new(socket_clone);

    let enclave_key = std::slice::from_raw_parts(enclave_pub_key, enclave_pub_key_len as usize);

    // Send EPID and its length first.
    // Then public key.
    writer.write(b"EPID:\n").unwrap();
    writer.write(epid_len.to_string().as_bytes()).unwrap();
    writer.write(b"\n").unwrap();
    writer.write(&*epid).unwrap();
    writer.write(enclave_key).unwrap();
    writer.write(b"\n").unwrap();
    writer.flush().unwrap();

    // Receive SigRL.
    info!("[+] Receiving SigRL from the SP!");
    let mut s = String::with_capacity(128);
    reader.read_line(&mut s).unwrap();

    // Get the length of the sigrl.
    let length = s[..s.len() - 1].parse::<usize>().unwrap();
    info!("[+] SigRL length = {}.", length);
    *sigrl_len = length as u32;

    // Get SigRL.
    let mut buf = Vec::with_capacity(len as usize);
    reader.read(&mut buf).unwrap();
    debug!("[+] SigRL is {:?}", buf);

    // Copy back to the buffer.
    ptr::copy(buf.as_ptr(), sigrl, length);

    // Do NOT implicitly destroy this stream; otherwise this stream will be closed
    // accidentally, thus resulting in a corrupted state.
    mem::forget(writer);
    mem::forget(reader);

    SgxStatus::Success
}

#[no_mangle]
pub unsafe extern "C" fn ocall_get_quote_report_from_intel(
    socket_fd: c_int,
    quote_buf: *const u8,
    quote_len: u32,
    quote_report: *mut u8,
    _quote_report_buf_len: u32,
    quote_report_len: *mut u32,
    sig: *mut u8,
    _sig_buf_len: u32,
    sig_len: *mut u32,
    cert: *mut u8,
    _cert_buf_len: u32,
    cert_len: *mut u32,
) -> SgxStatus {
    info!("[+] Performing ocall_get_quote_report_from_intel...");

    // Create the socket.
    let socket = TcpStream::from_raw_fd(socket_fd);
    let socket_clone = socket.try_clone().unwrap();

    let mut reader = BufReader::new(socket);
    let mut writer = BufWriter::new(socket_clone);

    // Encode the quote and send a json to the SP.
    let quote = slice::from_raw_parts(quote_buf, quote_len as usize);
    let encoded_quote = base64::encode(quote);
    let quote_json = format!("{{\"isvEnclaveQuote\":\"{}\"}}", encoded_quote);

    debug!("[+] Generated quote json as {}", quote_json);

    // Forward quote to the SP.
    writer.write(b"QUOTE\n").unwrap();
    writer
        .write(quote_json.len().to_string().as_bytes())
        .unwrap();
    writer.write(b"\n").unwrap();
    writer.write(quote_json.as_bytes()).unwrap();
    writer.write(b"\n").unwrap();
    writer.flush().unwrap();

    info!("[+] Successfully sent the quote to the SP.");

    // There will be three important data structures:
    // 1. The report of the quote generated by Intel;
    // 2. The corresponding signature;
    // 3. The certificate for checking that this report is valid.

    // First, determine the length of the quote_report.
    let mut s = String::with_capacity(128);
    reader.read_line(&mut s).unwrap();
    let length = s[..s.len() - 1].parse::<usize>().unwrap();
    // Prepare a buffer.
    let mut quote_report_buf = vec![0u8; length];
    reader.read_exact(&mut quote_report_buf).unwrap();

    // Parse into IasQuoteReport type.
    let ias_quote_report: IasQuoteReport = serde_json::from_slice(&quote_report_buf).unwrap();
    debug!(
        "[+] Successfully get quote report as {:?}",
        ias_quote_report
    );

    let res = check_status(&ias_quote_report);
    if res != SgxStatus::Success {
        return res;
    }

    // Copy from the quote report to the output pointers.
    ptr::copy(
        ias_quote_report.quote_report_raw.as_ptr(),
        quote_report,
        ias_quote_report.quote_report_raw.len(),
    );
    ptr::copy(
        ias_quote_report.quote_signature.as_ptr(),
        sig,
        ias_quote_report.quote_signature.len(),
    );
    ptr::copy(
        ias_quote_report.quote_certificate.as_ptr(),
        cert,
        ias_quote_report.quote_certificate.len(),
    );

    // Set return lengths.
    *quote_report_len = ias_quote_report.quote_report_raw.len() as u32;
    *sig_len = ias_quote_report.quote_signature.len() as u32;
    *cert_len = ias_quote_report.quote_certificate.len() as u32;

    // Forget resources not owned by Rust.
    mem::forget(reader);
    mem::forget(writer);

    SgxStatus::Success
}

#[no_mangle]
pub unsafe extern "C" fn ocall_sgx_epid_init_quote(
    ret_ti: *mut TargetInfo,
    ret_gid: *mut EpidGroupId,
) -> SgxStatus {
    info!("[+] Performing ocall_sgx_epid_init_quote...");

    // This will call the low-level C-API provided by the SGX library.
    sgx_init_quote(ret_ti, ret_gid)
}

#[no_mangle]
pub unsafe extern "C" fn ocall_sgx_dcap_init_quote(ret_ti: *mut TargetInfo) -> SgxStatus {
    info!("[+] Performing ocall_sgx_dcap_init_quote...");

    // This will call the low-level C-API provided by the SGX library.
    let res = sgx_qe_get_target_info(ret_ti);
    if res != Quote3Error::Success {
        SgxStatus::Unexpected
    } else {
        SgxStatus::Success
    }
}

#[no_mangle]
pub unsafe extern "C" fn ocall_send_quote(
    socket_fd: c_int,
    quote: *const u8,
    quote_size: u32,
) -> SgxStatus {
    info!("[+] Performing ocall_send_quote...");

    // Construct the socket.
    let socket = TcpStream::from_raw_fd(socket_fd);
    let mut writer = BufWriter::new(socket);

    let quote_buf = slice::from_raw_parts(quote, quote_size as usize);
    writer.write(quote_size.to_string().as_bytes()).unwrap();
    writer.write(b"\n").unwrap();
    writer.write(&quote_buf).unwrap();
    writer.write(b"\n").unwrap();
    writer.flush().unwrap();

    mem::forget(writer);
    SgxStatus::Success
}

#[no_mangle]
pub unsafe extern "C" fn ocall_send_pubkey(
  socket_fd: c_int,
    enclave_pub_key: *const u8,
    enclave_pub_key_len: u32,
) -> SgxStatus {
  info!("[+] Performing ocall_send_pubkey...");

  let socket = TcpStream::from_raw_fd(socket_fd);
  let mut writer = BufWriter::new(socket);
  let enclave_key = std::slice::from_raw_parts(enclave_pub_key, enclave_pub_key_len as usize);

  writer.write(enclave_key).unwrap();
  writer.write(b"\n").unwrap();
  writer.flush().unwrap();

  mem::forget(writer);

  SgxStatus::Success
}

/// This API is a thin wrapper around the core sgx_ql_get_quote_size() API. The size returned in this API will indicate
/// the size of the quote buffer required in the sgx_qe_get_quote() API.
#[no_mangle]
pub unsafe extern "C" fn ocall_qe_get_quote_size(quote_size: *mut u32) -> SgxStatus {
    info!("[+] Performing ocall_qe_get_quote_size...");

    // This will call the low-level C-API provided by the SGX library.
    let res = sgx_qe_get_quote_size(quote_size);
    if res != Quote3Error::Success {
        SgxStatus::Unexpected
    } else {
        SgxStatus::Success
    }
}

#[no_mangle]
pub unsafe extern "C" fn ocall_qe_get_quote(
    p_app_report: *const Report,
    p_quote: *mut u8,
    quote_size: u32,
) -> SgxStatus {
    info!("[+] Performing ocall_qe_get_quote...");

    // This will call the low-level C-API provided by the SGX library.
    let res = sgx_qe_get_quote(p_app_report, quote_size, p_quote);
    if res != Quote3Error::Success {
        SgxStatus::Unexpected
    } else {
        SgxStatus::Success
    }
}

#[no_mangle]
pub unsafe extern "C" fn ocall_get_quote(
    p_sigrl: *const u8,
    sigrl_len: u32,
    p_report: *const Report,
    quote_type: QuoteSignType,
    p_spid: *const Spid,
    p_nonce: *const QuoteNonce,
    p_qe_report: *mut Report,
    p_quote: *mut u8,
    _maxlen: u32,
    p_quote_len: *mut u32,
) -> SgxStatus {
    info!("[+] Performing ocall_get_quote...");

    // Calculate the real quote length.
    let mut real_quote_len = 0u32;
    let ret = sgx_calc_quote_size(p_sigrl, sigrl_len, &mut real_quote_len as *mut u32);

    if ret != SgxStatus::Success {
        error!("[-] sgx_calc_quote_size returned as {}", ret);
        return ret;
    }

    // Set the quote size.
    info!("[+] Calculated the quote size: {}", real_quote_len);
    *p_quote_len = real_quote_len;

    let ret = sgx_get_quote(
        p_report,
        quote_type,
        p_spid,
        p_nonce,
        p_sigrl,
        sigrl_len,
        p_qe_report,
        p_quote as *mut Quote,
        real_quote_len,
    );

    if ret != SgxStatus::Success {
        error!(
            "[-] Failed to execute sgx_calc_quote_size, returned as {}",
            ret
        );
        return ret;
    }

    info!("[+] Quote successfully generated.");

    ret
}

#[no_mangle]
pub unsafe extern "C" fn ocall_get_update_info(
    platform_blob: *const PlatformInfo,
    enclave_trusted: i32,
    update_info: *mut UpdateInfoBit,
) -> SgxStatus {
    info!("[+] Performing sgx_report_attestation_status...");

    sgx_report_attestation_status(platform_blob, enclave_trusted, update_info)
}

#[no_mangle]
pub unsafe extern "C" fn ocall_get_timepoint(time_point: *mut u64) -> SgxStatus {
    info!("[+] Getting current time.");

    let time = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map_err(|e| {
            error!("[-] Failed to get time due to {}.", e.to_string());
            return SgxStatus::BadStatus;
        })
        .unwrap();

    *time_point = time.as_secs();

    SgxStatus::Success
}

#[no_mangle]
pub unsafe extern "C" fn ocall_write_data(
    path: *const u8,
    path_size: u32,
    data: *const u8,
    data_size: u32,
) -> SgxStatus {
    info!("[+] Writing data...");

    let path_str = str::from_utf8(slice::from_raw_parts(path, path_size as usize)).unwrap();
    let mut file = File::create(path_str)
        .map_err(|e| {
            error!("[+] IO Error: {}", e.to_string());
            return SgxStatus::DeviceBusy;
        })
        .unwrap();

    let data_buf = slice::from_raw_parts(data, data_size as usize);

    match file.write_all(data_buf) {
        Ok(_) => SgxStatus::Success,

        Err(e) => {
            error!("[-] IO Error: {:?}", e);
            SgxStatus::DeviceBusy
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn ocall_read_data(
    path: *const u8,
    path_size: u32,
    data: *mut u8,
    data_buf_size: u32,
    data_size: *mut u32,
) -> SgxStatus {
    info!("[+] Reading data...");

    let path_str = str::from_utf8(slice::from_raw_parts(path, path_size as usize)).unwrap();
    let mut file = File::open(path_str)
        .map_err(|e| {
            error!("[+] IO Error: {}", e.to_string());
            return SgxStatus::DeviceBusy;
        })
        .unwrap();

    let data_buf = slice::from_raw_parts_mut(data, data_buf_size as usize);

    file.read(data_buf)
        .map_err(|e| {
            error!("[+] IO Error: {}", e.to_string());
            return SgxStatus::DeviceBusy;
        })
        .unwrap();

    // Copy back.
    ptr::copy(data_buf.as_ptr(), data, data_buf.len());
    *data_size = data_buf.len() as u32;

    SgxStatus::Success
}

/// Performs a check if the target TCB is too low to meet IAS's requirements.
/// By invoking `sgx_report_attestation_status` for analysis, we can know how
/// to fix this status code.
fn check_status(isv_enclave_quote: &IasQuoteReport) -> SgxStatus {
    // We can also check the freshness of the quote report by adding an extra nonce.

    if isv_enclave_quote.quote_status == "GROUP_OUT_OF_DATE"
        || isv_enclave_quote.quote_status == "CONFIGURATION_NEEDED"
    {
        // Decode the platform info blob and inquiry the SGX why this would happen.
        // This field is encoded by base16.
        let platform_blob_decoded = base16::decode(&isv_enclave_quote.platform_info_blob)
            .expect("[-] Base16 decode for PlatformInfoBlob failed.");
        let mut platform_blob = PlatformInfo::default();

        // TLV Header + TLV Payload (Platform Information Blob to be processed by SGX
        // Platform SW.) = 4 + 101 = 105.
        if platform_blob_decoded.len() != SGX_PLATFORM_INFO_SIZE + SGX_PLATFORM_HEADER_SIZE {
            error!(
                "[-] PlatformInfoBlob is corrupted or missing. Got {}",
                platform_blob_decoded.len()
            );
            return SgxStatus::InvalidParameter;
        }

        platform_blob
            .platform_info
            .copy_from_slice(&platform_blob_decoded[4..]);

        // Call sgx_report_attestation_status.
        let mut update_info = UpdateInfoBit::default();
        let res = unsafe { sgx_report_attestation_status(&platform_blob, 1, &mut update_info) };
        match res {
            SgxStatus::UpdateNeeded => {
                warn!("[?] The TCB version is outdated. Please consider an update, but you can still trust this enclave if you do not think it is a problem.");
                // Check more details.
                //
                // A security upgrade for your computing device is required for this
                // application to continue to provide you with a high degree of security
                // for this system.
                //
                // It the user's discretion whether to trust the enclave, but a hardware update
                // that fixes potential vulnerabilities are definitely more welcomed.
                warn!("[+] Update details: {:?}", update_info);
            }

            SgxStatus::Success => {
                // A strange case; maybe this should not happten?
                info!("[+] IAS returned outdated status but inquiry to `sgx_report_attestation_status` returned success.");
            }

            _ => {
                error!(
                    "[-] Failed to consult `sgx_report_attestation_status` due to {:?}",
                    res
                );
                return SgxStatus::Unexpected;
            }
        }
    } else if isv_enclave_quote.quote_status != "OK" {
        error!(
            "[-] The status for quote report is not correct. Got {}.",
            isv_enclave_quote.quote_status
        );

        return SgxStatus::BadStatus;
    }

    SgxStatus::Success
}

#[no_mangle]
pub unsafe extern "C" fn ocall_receive_data(
    socket_fd: c_int,
    data_buf: *mut u8,
    data_buf_len: u32,
    data_size: *mut u32,
) -> SgxStatus {
    // Wrap a new tcp stream from the raw socket fd.
    let socket = TcpStream::from_raw_fd(socket_fd);
    let mut reader = BufReader::new(socket);
    let mut str_len = String::with_capacity(OUTPUT_BUFFER_SIZE);

    // Read length.
    reader
        .read_line(&mut str_len)
        .map_err(|e| {
            error!("[-] Failed to receive data due to {:?}", e);
            return SgxStatus::InvalidParameter;
        })
        .unwrap();

    if str_len.is_empty() {
        error!("[-] Failed to receive any data length! Is the socket closed?");
        return SgxStatus::InvalidParameter;
    }

    *data_size = str_len[..str_len.len() - 1]
        .parse()
        .map_err(|e| {
            error!("[-] Failed to parse the data size due to {:?}", e);
            return SgxStatus::InvalidParameter;
        })
        .unwrap();

    if data_buf_len < *data_size {
        return SgxStatus::InvalidParameter;
    }

    let mut buf = vec![0u8; (*data_size + 1) as usize];
    reader
        .read_exact(&mut buf)
        .map_err(|e| {
            error!("[-] Failed to receive data due to {:?}", e);
            return SgxStatus::InvalidParameter;
        })
        .unwrap();
    core::ptr::copy(buf.as_ptr(), data_buf, *data_size as usize);

    // Do not destroy the socket.
    mem::forget(reader);

    SgxStatus::Success
}
