use std::io::BufWriter;
use std::io::Write;
use std::mem;
use std::net::TcpStream;
use std::os::unix::prelude::FromRawFd;

use sgx_types::error::*;
use sgx_types::function::*;
use sgx_types::types::*;

#[no_mangle]
pub unsafe extern "C" fn u_log_ocall(
    string_ptr: *mut u8,
    string_len: u32,
    string_capacity: u32,
) -> u32 {
    let s = String::from_raw_parts(string_ptr, string_len as usize, string_capacity as usize);
    println!("{}", s);
    std::mem::forget(s);
    string_capacity
}

#[no_mangle]
pub unsafe extern "C" fn ocall_get_sigrl_from_intel(
    epid: *const EpidGroupId,
    epid_len: usize,
    socket_fd: i32,
) -> SgxStatus {
    println!(
        "[+] Performing ocall_get_sigrl_from_intel... The EPID is {:?}",
        *epid
    );
    // Forward this request to the SP.
    // Wrap a new tcp stream from the raw socket fd.
    let socket = TcpStream::from_raw_fd(socket_fd);
    let mut writer = BufWriter::new(socket);

    // Send EPID and its length first.
    writer.write(b"EPID:\n").unwrap();
    writer.write(epid_len.to_string().as_bytes()).unwrap();
    writer.write(b"\n").unwrap();
    writer.write(&*epid).unwrap();
    writer.flush().unwrap();
    // Do NOT implicitly destroy this stream; otherwise this stream will be closed
    // accidentally, thus resulting in a corrupted state.
    mem::forget(writer);

    SgxStatus::Success
}

#[no_mangle]
pub unsafe extern "C" fn ocall_sgx_init_quote(
    ret_ti: *mut TargetInfo,
    ret_gid: *mut EpidGroupId,
) -> SgxStatus {
    println!("[+] Performing ocall_sgx_init_quote...");

    // This will call the low-level C-API provided by the SGX library.
    sgx_init_quote(ret_ti, ret_gid)
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
    println!("Performing ocall_get_quote...");

    // Calculate the real quote length.
    let mut real_quote_len = 0u32;
    let ret = sgx_calc_quote_size(p_sigrl, sigrl_len, &mut real_quote_len as *mut u32);

    if ret != SgxStatus::Success {
        println!("sgx_calc_quote_size returned as {}", ret);
        return ret;
    }

    // Set the quote size.
    println!("Calculated the quote size: {}", real_quote_len);
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
        println!("Failed to execute sgx_calc_quote_size, returned as {}", ret);
        return ret;
    }

    ret
}

#[no_mangle]
pub unsafe extern "C" fn ocall_get_update_info(
    platform_blob: *const PlatformInfo,
    enclave_trusted: i32,
    update_info: *mut UpdateInfoBit,
) -> SgxStatus {
    println!("Performing sgx_report_attestation_status...");

    sgx_report_attestation_status(platform_blob, enclave_trusted, update_info)
}
