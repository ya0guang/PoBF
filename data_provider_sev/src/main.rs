use std::{
    io::{BufRead, BufReader, BufWriter, Error, ErrorKind, Read, Result, Write},
    net::TcpStream,
};

use log::info;
use pobf_crypto::{handle_sev_pubkey, init_keypair, KeyPair};

fn init_logger() {
    if std::env::var("RUST_LOG").is_err() {
        std::env::set_var("RUST_LOG", "info");
    }
    env_logger::init();
}

fn main() {
    init_logger();

    let socket = connect(&"127.0.0.1", 2333).expect("[-] Cannot connect to the given address");
    let socket_clone = socket.try_clone().unwrap();
    let mut reader = BufReader::new(socket);
    let mut writer = BufWriter::new(socket_clone);

    let key_pair = init_keypair().unwrap();
    exec_sev_workflow(&mut reader, &mut writer, key_pair)
        .expect("[-] failed to execute SEV workflow");
}

pub fn connect(address: &str, port: u16) -> Result<TcpStream> {
    // Create the full address for the server.
    let mut full_address = String::new();
    full_address.push_str(address);
    full_address.push_str(":");
    full_address.push_str(&port.to_string());

    info!("[+] Connecting to {}", full_address);

    TcpStream::connect(&full_address)
}

pub fn exec_sev_workflow(
    reader: &mut BufReader<TcpStream>,
    writer: &mut BufWriter<TcpStream>,
    mut key_pair: KeyPair,
) -> Result<Vec<u8>> {
    let public_key = &key_pair.pub_k;
    info!("[+] Receiving the attestation report");
    let mut len = String::with_capacity(128);
    reader.read_line(&mut len)?;
    let report_len = len[..len.len() - 1]
        .parse::<usize>()
        .map_err(|_| Error::from(ErrorKind::InvalidData))?;
    let mut report = vec![0u8; report_len];
    reader.read_exact(&mut report)?;

    info!("[+] Sending public key");
    writer.write_all(public_key.as_ref())?;
    writer.flush()?;

    info!("[+] Receiving peer public key");
    let mut peer_pub_key = vec![0u8; 0x20];
    reader.read_exact(&mut peer_pub_key)?;
    let peer_pub_key = handle_sev_pubkey(reader).unwrap();

    key_pair.compute_shared_key(&peer_pub_key, b"").unwrap();
    let session_key = &key_pair.session_key;
    info!("key is {session_key:02x?}");

    info!("[+] Sending data...");
    writer.write(b"12\n")?;
    writer.flush()?;
    writer.write(b"111111111111")?;
    writer.flush()?;

    todo!()
}
