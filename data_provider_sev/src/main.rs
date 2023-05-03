use std::{
    fs,
    fs::File,
    io::{BufRead, BufReader, BufWriter, Error, ErrorKind, Read, Result, Write},
    net::TcpStream,
};

use clap::{Parser, Subcommand};
use log::info;
use pobf_crypto::{handle_sev_pubkey, init_keypair, KeyPair};
use serde::{Deserialize, Serialize};

const DEFAULT_MANIFEST_PATH: &str = "manifest.json";

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
#[clap(propagate_version = true)]
struct Args {
    #[clap(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Run { manifest_path: String },
}

#[derive(Deserialize, Serialize)]
pub struct DpInformation {
    pub address: String,
    pub port: u16,
    pub data_path: String,
}

fn init_logger() {
    if std::env::var("RUST_LOG").is_err() {
        std::env::set_var("RUST_LOG", "info");
    }
    env_logger::init();
}

fn main() {
    init_logger();

    let args = Args::parse();

    match args.command {
        Commands::Run { manifest_path } => {
            let f = File::open(&manifest_path)
                .or_else(|_| File::open(DEFAULT_MANIFEST_PATH))
                .unwrap();
            let manifest = serde_json::from_reader::<_, DpInformation>(f)
                .expect("[-] Failed to parse the manifest");
            let socket = connect(&manifest.address, manifest.port)
                .expect("[-] Cannot connect to the given address");
            let socket_clone = socket.try_clone().unwrap();
            let mut reader = BufReader::new(socket);
            let mut writer = BufWriter::new(socket_clone);

            let key_pair = init_keypair().unwrap();
            let data = exec_sev_workflow(&mut reader, &mut writer, &manifest.data_path, key_pair)
                .expect("[-] failed to execute SEV workflow");
            fs::write("./output.txt", &data).unwrap();
            info!("[+] Finished");
        }
    }
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
    data_path: &str,
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
    let peer_pub_key = handle_sev_pubkey(reader).unwrap();
    key_pair.compute_shared_key(&peer_pub_key, b"").unwrap();

    info!("[+] Sending data...");
    // Read the data and encrypt it.
    let data = key_pair.encrypt_with_smk(&fs::read(data_path)?).unwrap();
    writer.write_all(data.len().to_string().as_bytes())?;
    writer.write_all(b"\n")?;
    writer.flush()?;
    writer.write_all(&data)?;
    writer.flush()?;

    info!("[+] Receiving the data...");
    len.clear();
    reader.read_line(&mut len)?;
    let buf_len = len[..len.len() - 1].parse::<usize>().unwrap();
    let mut buf = vec![0u8; buf_len];
    reader.read_exact(&mut buf)?;

    // Decrypt the data.
    Ok(key_pair.decrypt_with_smk(&buf).unwrap())
}
