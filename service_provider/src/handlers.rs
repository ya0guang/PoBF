use crate::{IAS_BASE_REQUEST, IAS_BASE_URL, IAS_KEY_HEADER};

use curl::easy::{Easy, List};

use std::io::*;
use std::mem;
use std::net::TcpStream;

pub fn send_sigrl(writer: &mut BufWriter<TcpStream>, sigrl: Vec<u8>) -> Result<()> {
    writer.write(sigrl.len().to_string().as_bytes()).unwrap();
    writer.write(b"\n").unwrap();
    writer.write(&sigrl).unwrap();
    writer.write(b"\n").unwrap();
    writer.flush().unwrap();

    Ok(())
}

pub fn send_spid(writer: &mut BufWriter<TcpStream>, spid: &String) -> Result<()> {
    writer.write(b"0\n").unwrap();
    writer.write(spid.as_bytes()).unwrap();
    writer.write(b"\n").unwrap();
    writer.flush().unwrap();

    Ok(())
}

pub fn get_full_url(request: &str) -> String {
    format!("{}{}{}", IAS_BASE_URL, IAS_BASE_REQUEST, request)
}

pub fn get_sigrl(ias_key: &String, epid: &[u8; 4]) -> Result<Vec<u8>> {
    let mut easy = Easy::new();
    let mut sigrl = Vec::new();
    let mut full_url = get_full_url("sigrl");

    // Encode the epid and append it to the full URL.
    let gid = unsafe { mem::transmute::<[u8; 4], u32>(*epid) }.to_le();
    full_url.push_str(&format!("/{:08x?}", gid));

    easy.url(&full_url).unwrap();

    // Set the header.
    let mut header = List::new();
    let header_str = format!("{}: {}", IAS_KEY_HEADER, ias_key);

    println!(
        "[+] Requesting {}\n[+] HTTP header: {}",
        full_url, header_str
    );

    header.append(&header_str).unwrap();
    easy.http_headers(header).unwrap();

    {
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
    println!("[+] Request sent. Got status code {}.", code);

    if code != 200 {
        // Leave an error message and die.
        println!(
            "[+] Response body: {}",
            std::str::from_utf8(&sigrl).unwrap()
        );

        Err(Error::from(ErrorKind::PermissionDenied))
    } else {
        Ok(sigrl)
    }
}

pub fn connect(address: &String, port: &u16) -> Result<TcpStream> {
    // Create the full address for the server.
    let mut full_address = String::new();
    full_address.push_str(address);
    full_address.push_str(":");
    full_address.push_str(&port.to_string());

    println!("[+] Connecting to {}", full_address);

    TcpStream::connect(&full_address)
}

pub fn handle_epid(
    reader: &mut BufReader<TcpStream>,
    writer: &mut BufWriter<TcpStream>,
    ias_key: &String,
) -> Result<Vec<u8>> {
    writer.write(b"1\n").unwrap();
    writer.flush().unwrap();

    let mut s = String::with_capacity(512);
    // Wait for the EPID.
    reader.read_line(&mut s).unwrap();

    if !s.starts_with("EPID:") {
        println!("[-] Expecting an EPID. Got {}.", s);
        return Err(Error::from(ErrorKind::InvalidData));
    }

    // Read length.
    s.clear();
    reader.read_line(&mut s).unwrap();
    if s.chars().next().unwrap() != '4' {
        println!("[-] Expecting EPID length to be 4. Got {}.", s);
        return Err(Error::from(ErrorKind::InvalidData));
    }

    // Read EPID itself.
    let mut epid = [0u8; 4];
    reader.read_exact(&mut epid).unwrap();
    println!("[+] EPID: {:?}", epid);

    // Get the SigRL from the IAS.
    let sigrl = get_sigrl(ias_key, &epid).unwrap();
    if !sigrl.is_empty() {
        let sigrl_str = String::from_utf8(sigrl.clone()).unwrap();
        println!("[+] Got SigRL: {:?}", sigrl_str);
    } else {
        println!("[+] SigRL is empty!");
    }

    parse_sigrl(&sigrl)
}

pub fn parse_sigrl(sigrl: &Vec<u8>) -> Result<Vec<u8>> {
    if sigrl.is_empty() {
        Ok(Vec::new())
    } else {
        Ok(base64::decode(std::str::from_utf8(sigrl).unwrap()).unwrap())
    }
}

pub fn handle_quote(
    reader: &mut BufReader<TcpStream>,
    writer: &mut BufWriter<TcpStream>,
    key: &String,
) -> Result<()> {
    let mut s = String::with_capacity(128);
    reader.read_line(&mut s).unwrap();

    if !s.starts_with("QUOTE") {
        println!("[-] Expecting a quote, got {}", s);
    }

    // Get quote length.
    reader.read_line(&mut s).unwrap();
    let quote_len = s[..s.len() - 1]
        .parse::<usize>()
        .expect("[-] Not a valid length!");

    println!("[+] Read quote length: {}.", quote_len);
    let mut quote_buf = vec![0u8; quote_len];

    // Read Quote.
    reader.read_exact(&mut quote_buf).unwrap();
    Ok(())
}
