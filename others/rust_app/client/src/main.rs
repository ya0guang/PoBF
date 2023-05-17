use std::env;
use std::fs;
use std::io::*;
use std::net::TcpStream;

use pobf_crypto::handle_sev_pubkey;
use pobf_crypto::init_keypair;

const ADDRESS: &str = "127.0.0.1:7788";

fn main() {
    let stream = TcpStream::connect(ADDRESS).unwrap();
    let stream_clone = stream.try_clone().unwrap();
    let mut reader = BufReader::new(stream);
    let mut writer = BufWriter::new(stream_clone);

    let args: Vec<String> = env::args().collect();
    let data_path = &args[1];
    let data = fs::read(data_path).unwrap();
    println!("Reading {}", data_path);

    let mut key_pair = init_keypair().unwrap();
    let public_key = &key_pair.pub_k;

    println!("[+] Sending public key");
    writer.write_all(public_key.as_ref()).unwrap();
    writer.flush().unwrap();

    println!("[+] Receiving peer public key");
    let peer_pub_key = handle_sev_pubkey(&mut reader).unwrap();
    key_pair.compute_shared_key(&peer_pub_key, b"").unwrap();

    println!("[+] Sending data...");
    // Read the data and encrypt it.
    let data = key_pair.encrypt_with_smk(&data).unwrap();
    writer.write_all(data.len().to_string().as_bytes()).unwrap();
    writer.write_all(b"\n").unwrap();
    writer.flush().unwrap();
    writer.write_all(&data).unwrap();
    writer.flush().unwrap();

    println!("[+] Receiving the data...");

    let mut len = String::with_capacity(128);
    reader.read_line(&mut len).unwrap();
    let buf_len = len[..len.len() - 1].parse::<usize>().unwrap();
    let mut buf = vec![0u8; buf_len];
    reader.read_exact(&mut buf).unwrap();

    // Decrypt the data.
    let out = key_pair.decrypt_with_smk(&buf).unwrap();

    std::fs::write("./data.txt", out).unwrap();
}
