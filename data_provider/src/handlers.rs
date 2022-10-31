use crate::dh::{handle_enclave_pubkey, KeyPair, KDF_MAGIC_STR};
use crate::utils::*;
use crate::{IAS_CONTENT_TYPE_HEADER, IAS_KEY_HEADER};

use curl::easy::{Easy, List};
use log::{debug, error, info};

use std::fs;
use std::io::*;
use std::mem;
use std::net::TcpStream;

use ring::agreement::PublicKey;

// Some useful constants.
pub const BREAKLINE: &'static [u8] = b"\n";
pub const DEFAULT_BUFFER_LEN: usize = 0x400;
pub const EPID_LEN: usize = 0x04;
pub const HTTP_OK: u32 = 200;

pub fn send_sigrl(writer: &mut BufWriter<TcpStream>, sigrl: Vec<u8>) -> Result<()> {
    writer.write(sigrl.len().to_string().as_bytes()).unwrap();
    writer.write(BREAKLINE).unwrap();
    writer.write(&sigrl).unwrap();
    writer.write(BREAKLINE).unwrap();
    writer.flush().unwrap();

    Ok(())
}

pub fn send_initial_messages(
    writer: &mut BufWriter<TcpStream>,
    spid: &String,
    linkable: bool,
    public_key: &PublicKey,
    pubkey_signature: &Vec<u8>,
) -> Result<()> {
    writer.write(b"0").unwrap();
    writer.write(BREAKLINE).unwrap();
    writer.flush().unwrap();

    writer.write(&public_key.as_ref()[1..]).unwrap();
    writer.write(BREAKLINE).unwrap();
    writer
        .write(pubkey_signature.len().to_string().as_bytes())
        .unwrap();
    writer.write(BREAKLINE).unwrap();
    writer.flush().unwrap();

    writer.write(&pubkey_signature).unwrap();
    writer.write(BREAKLINE).unwrap();

    writer.write(spid.as_bytes()).unwrap();
    writer.write(BREAKLINE).unwrap();
    writer
        .write((linkable as i64).to_string().as_bytes())
        .unwrap();
    writer.write(BREAKLINE).unwrap();
    writer.flush().unwrap();

    Ok(())
}

pub fn get_sigrl(ias_key: &String, epid: &[u8; EPID_LEN]) -> Result<Vec<u8>> {
    let mut easy = Easy::new();
    let mut sigrl = Vec::new();
    let mut full_url = get_full_url("sigrl");

    // Encode the epid and append it to the full URL.
    let gid = unsafe { mem::transmute::<[u8; EPID_LEN], u32>(*epid) }.to_le();
    full_url.push_str(&format!("/{:08x?}", gid));

    easy.url(&full_url).unwrap();

    // Set the header.
    let mut header = List::new();
    let header_str = format!("{}: {}", IAS_KEY_HEADER, ias_key);

    info!(
        "\n[+] Requesting {}\n[+] HTTP header:\n\t{}",
        full_url, header_str
    );

    header.append(&header_str).unwrap();
    easy.http_headers(header).unwrap();

    {
        // Open a temporary context for this callback.
        // We need to return the ownership of sig_rl.
        let mut transfer = easy.transfer();
        transfer
            .write_function(|data| {
                sigrl.extend_from_slice(data);
                Ok(data.len())
            })
            .unwrap();
        transfer.perform().unwrap();
    }

    if let Err(_) = easy.perform() {
        return Err(Error::from(ErrorKind::ConnectionRefused));
    }

    let code = easy.response_code().unwrap();
    info!("[+] Request sent. Got status code {}.", code);

    debug!(
        "[+] Response body: {}",
        std::str::from_utf8(&sigrl).unwrap()
    );

    if code != HTTP_OK {
        // Leave an error message and die.
        error!("[-] Got non 200 status code.");

        Err(Error::from(ErrorKind::PermissionDenied))
    } else {
        Ok(sigrl)
    }
}

/// Returns a serde serialized three-tuple in bytes: (quote_report, sig, cert).
pub fn get_quote_report(ias_key: &String, report_json: &Vec<u8>) -> Result<Vec<u8>> {
    let mut easy = Easy::new();
    let full_url = get_full_url("report");
    let mut response_header = Vec::new();
    let mut response_buf = Vec::new();

    // Set the headers.
    let mut header = List::new();
    let key_header = format!("{}: {}", IAS_KEY_HEADER, ias_key);
    let content_type_header = format!("{}: {}", IAS_CONTENT_TYPE_HEADER, "application/json");

    info!(
        "\n[+] Requesting {}\n[+] HTTP header:\n\t{}\n\t{}",
        full_url, key_header, content_type_header,
    );

    header.append(&content_type_header).unwrap();
    header.append(&key_header).unwrap();
    easy.http_headers(header).unwrap();
    easy.post_fields_copy(report_json.as_slice()).unwrap();
    easy.url(&full_url).unwrap();
    // We need to send a POST request to the server.
    easy.post(true).unwrap();

    {
        let mut transfer = easy.transfer();
        transfer
            .write_function(|data| {
                response_buf.extend_from_slice(data);
                Ok(data.len())
            })
            .unwrap();

        transfer
            .header_function(|data| {
                response_header.extend_from_slice(&data);
                true
            })
            .unwrap();

        transfer.perform().unwrap();
    }

    let code = easy.response_code().unwrap();
    info!("[+] Request sent. Got status code {}.", code);

    debug!(
        "[+] Response body:\n{}\nResponse header:\n{}",
        std::str::from_utf8(&response_buf).unwrap(),
        std::str::from_utf8(&response_header).unwrap()
    );

    if code != HTTP_OK {
        error!("[-] Got non 200 status code.");
        // Leave an error message and die.
        Err(Error::from(ErrorKind::PermissionDenied))
    } else {
        // Parse the result.
        parse_quote_report(response_header, response_buf)
    }
}

pub fn connect(address: &String, port: &u16) -> Result<TcpStream> {
    // Create the full address for the server.
    let mut full_address = String::new();
    full_address.push_str(address);
    full_address.push_str(":");
    full_address.push_str(&port.to_string());

    info!("[+] Connecting to {}", full_address);

    TcpStream::connect(&full_address)
}

pub fn exec_dcap_workflow(
    reader: &mut BufReader<TcpStream>,
    writer: &mut BufWriter<TcpStream>,
    key_pair: &mut KeyPair,
    dp_information: &DpInformation,
) -> Result<()> {
    let public_key = &key_pair.pub_k;
    let pubkey_signature = &key_pair.signature;

    // Send remote attestation type.
    writer.write(b"1").unwrap();
    writer.write(BREAKLINE).unwrap();
    writer.flush().unwrap();

    // Send public key and the signature.
    writer.write(&public_key.as_ref()[1..]).unwrap();
    writer.write(BREAKLINE).unwrap();
    writer
        .write(pubkey_signature.len().to_string().as_bytes())
        .unwrap();
    writer.write(BREAKLINE).unwrap();
    writer.flush().unwrap();

    writer.write(&pubkey_signature).unwrap();
    writer.write(BREAKLINE).unwrap();
    writer.flush().unwrap();

    info!("[+] Waiting for public key of the enclave.");
    let enclave_pubkey = handle_enclave_pubkey(reader)
        .map_err(|_| {
            error!("[-] Failed to parse enclave public key.");
            return Error::from(ErrorKind::InvalidData);
        })
        .unwrap();
    info!("[+] Succeeded.");

    info!("[+] Computing ephemeral session key.");
    key_pair
        .compute_shared_key(&enclave_pubkey, KDF_MAGIC_STR.as_bytes())
        .unwrap();
    info!("[+] Succeeded.");

    // Verify the quote sent from the enclave.
    info!("[+] Verifying the quote...");
    verify_dcap_quote(reader)?;
    info!("[+] Quote valid!");

    // Send initial encrypted data. Trivial data 1,2,3 are just for test.
    info!("[+] Sending encrypted vector data.");
    send_vecaes_data(writer, &dp_information.data_path, &key_pair)?;
    info!("[+] Succeeded.");

    Ok(())
}

pub fn verify_dcap_quote(reader: &mut BufReader<TcpStream>) -> Result<()> {
    let mut len = String::with_capacity(DEFAULT_BUFFER_LEN);
    reader.read_line(&mut len).unwrap();

    let quote_size = len[..len.len() - 1].parse::<usize>().or_else(|e| {
        error!("[-] Cannot parse quote length due to {:?}.", e);
        Err(Error::from(ErrorKind::InvalidData))
    })?;

    let mut quote = vec![0u8; quote_size + 1];
    reader.read_exact(&mut quote).unwrap();
    quote.truncate(quote_size);

    // TODO.

    Ok(())
}

pub fn exec_epid_workflow(
    reader: &mut BufReader<TcpStream>,
    writer: &mut BufWriter<TcpStream>,
    key_pair: &mut KeyPair,
    dp_information: &DpInformation,
) -> Result<()> {
    // Send Spid and public key to the application enclave.
    info!("[+] Sending initial messages including SPID and public key.");
    send_initial_messages(
        writer,
        &dp_information.spid,
        dp_information.linkable,
        &key_pair.pub_k,
        &key_pair.signature,
    )
    .unwrap();
    info!("[+] Succeeded.");

    info!("[+] Waiting for Extended Group ID.");
    let sigrl = handle_epid(reader, &dp_information.ias_key)?;
    info!("[+] Succeeded.");

    info!("[+] Waiting for public key of the enclave.");
    let enclave_pubkey = handle_enclave_pubkey(reader)
        .map_err(|_| {
            error!("[-] Failed to parse enclave public key.");
            return Error::from(ErrorKind::InvalidData);
        })
        .unwrap();
    info!("[+] Succeeded.");

    debug!("[+] The public key of the enclave is {:?}", enclave_pubkey);

    info!("[+] Fetching Signature Revocation List from Intel.");
    send_sigrl(writer, sigrl)?;
    info!("[+] Succeeded.");

    // Handle quote.
    info!("[+] Verifying quote.");
    handle_quote(reader, writer, &dp_information.ias_key)?;
    info!("[+] Succeeded.");

    // Compute shared key.
    info!("[+] Computing ephemeral session key.");
    key_pair
        .compute_shared_key(&enclave_pubkey, KDF_MAGIC_STR.as_bytes())
        .unwrap();
    info!("[+] Succeeded.");

    // Send initial encrypted data. Trivial data 1,2,3 are just for test.
    info!("[+] Sending encrypted vector data.");
    send_vecaes_data(writer, &dp_information.data_path, &key_pair)?;
    info!("[+] Succeeded.");

    Ok(())
}

pub fn handle_epid(reader: &mut BufReader<TcpStream>, ias_key: &String) -> Result<Vec<u8>> {
    let mut s = String::with_capacity(DEFAULT_BUFFER_LEN);
    // Wait for the EPID.
    reader.read_line(&mut s).unwrap();

    if !s.starts_with("EPID:") {
        error!("[-] Expecting an EPID. Got {}.", s);
        return Err(Error::from(ErrorKind::InvalidData));
    }

    // Read length.
    s.clear();
    reader.read_line(&mut s).unwrap();
    if s.chars().next().unwrap().to_digit(10).unwrap() as usize != EPID_LEN {
        error!("[-] Expecting EPID length to be 4. Got {}.", s);
        return Err(Error::from(ErrorKind::InvalidData));
    }

    // Read EPID itself.
    let mut epid = [0u8; EPID_LEN];
    reader.read_exact(&mut epid).unwrap();
    debug!("[+] EPID: {:?}", epid);

    // Get the SigRL from the IAS.
    let sigrl = get_sigrl(ias_key, &epid).unwrap();
    if !sigrl.is_empty() {
        let sigrl_str = String::from_utf8(sigrl.clone()).unwrap();
        debug!("[+] Got SigRL: {:?}", sigrl_str);
    } else {
        debug!("[+] SigRL is empty!");
    }

    parse_sigrl(&sigrl)
}

pub fn handle_quote(
    reader: &mut BufReader<TcpStream>,
    writer: &mut BufWriter<TcpStream>,
    ias_key: &String,
) -> Result<()> {
    let mut s = String::with_capacity(DEFAULT_BUFFER_LEN);
    reader.read_line(&mut s).unwrap();

    if !s.starts_with("QUOTE") {
        error!("[-] Expecting a quote, got {}", s);
        return Err(Error::from(ErrorKind::InvalidData));
    }

    // Get quote length.
    s.clear();
    reader.read_line(&mut s).unwrap();

    let quote_len = s[..s.len() - 1]
        .parse::<usize>()
        .expect("[-] Not a valid length!");

    debug!("[+] Read quote length: {}.", quote_len);
    let mut quote_buf = vec![0u8; quote_len];

    // Read quote.
    reader.read_exact(&mut quote_buf).unwrap();
    debug!("content: {}", String::from_utf8(quote_buf.clone()).unwrap());

    // Get quote report from Intel.
    let quote_report = get_quote_report(ias_key, &quote_buf).unwrap();
    // Send it to the application enclave.
    writer
        .write(quote_report.len().to_string().as_bytes())
        .unwrap();
    writer.write(BREAKLINE).unwrap();
    writer.write(&quote_report).unwrap();
    writer.write(BREAKLINE).unwrap();
    writer.flush().unwrap();

    Ok(())
}

pub fn send_vecaes_data(
    writer: &mut BufWriter<TcpStream>,
    path: &String,
    key: &KeyPair,
) -> Result<()> {
    // Read from the given path.
    let data = fs::read(path)?;
    info!("{:?}", data);
    // Encrypt the data first.
    let encrypted_input = key.encrypt_with_smk(&data).map_err(|_| {
        error!("[-] Cannot encrypt the input.");
        Error::from(ErrorKind::InvalidData)
    })?;

    info!("[+] The encrypted data is {:?}", encrypted_input);

    writer
        .write(encrypted_input.len().to_string().as_bytes())
        .unwrap();
    writer.write(BREAKLINE).unwrap();
    writer.write(&encrypted_input).unwrap();
    writer.write(BREAKLINE).unwrap();
    writer.flush().unwrap();

    Ok(())
}
