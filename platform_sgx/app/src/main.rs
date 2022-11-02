extern crate base16;
extern crate base64;
extern crate clap;
extern crate env_logger;
extern crate hex;
extern crate serde;
extern crate serde_json;
extern crate sgx_types;
extern crate sgx_urts;

mod ocall;

use clap::{Parser, Subcommand};
use log::{debug, error, info};
use sgx_types::error::*;
use sgx_types::types::*;
use sgx_urts::enclave::SgxEnclave;
use std::fs::File;
use std::io::prelude::*;
use std::io::*;
use std::net::TcpListener;
use std::net::TcpStream;
use std::os::unix::prelude::AsRawFd;

static ENCLAVE_FILE: &'static str = "enclave.signed.so";
static SGX_PLATFORM_HEADER_SIZE: usize = 0x4;
const OUTPUT_BUFFER_SIZE: usize = 2048;

#[derive(Default)]
struct RaMessage {
    spid: Spid,
    linkable: i64,
    public_key: Vec<u8>,
    signature: Vec<u8>,
    ra_type: u8,
}

extern "C" {
    fn private_computing_entry(
        eid: EnclaveId,
        retval: *mut SgxStatus,
        socket_fd: c_int,
        spid: *const Spid,
        linkable: i64,
        ra_type: u8,
        public_key: *const u8,
        public_key_len: u32,
        pubkey_signature: *const u8,
        pubkey_signature_len: u32,
        encrypted_output_buffer_ptr: *mut u8,
        encrypted_output_buffer_size: u32,
        encrypted_output_size: *mut u32,
    ) -> SgxStatus;

    /// Legacy function.
    #[allow(unused)]
    fn start_remote_attestation(
        eid: EnclaveId,
        retval: *mut SgxStatus,
        socket_fd: c_int,
        spid: *const Spid,
        linkable: i64,
        public_key: *const u8,
        public_key_len: u32,
        pubkey_signature: *const u8,
        pubkey_signature_len: u32,
    ) -> SgxStatus;
}

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
#[clap(propagate_version = true)]
struct Args {
    #[clap(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// do private computation on encrypted data with a sealed key
    /// Also listen to the request from the SP to perform the RA.
    Cal { address: String, port: u16 },
}

fn main() {
    if std::env::var("RUST_LOG").is_err() {
        std::env::set_var("RUST_LOG", "INFO");
    }
    env_logger::init();

    let enclave = match SgxEnclave::create(ENCLAVE_FILE, false) {
        Ok(r) => {
            info!("[+] Init Enclave Successful, eid: {}!", r.eid());
            r
        }
        Err(x) => {
            error!("[-] Init Enclave Failed, reason: {}!", x.as_str());
            return;
        }
    };

    let args = Args::parse();
    match args.command {
        Commands::Cal { address, port } => {
            let listener = match listen(&address, &port) {
                Ok(res) => res,
                Err(e) => {
                    error!(
                        "[-] Failed to bind to the given address due to {}.",
                        e.to_string()
                    );
                    return;
                }
            };

            match server_run(listener, &enclave) {
                Err(e) => {
                    error!("[-] Error running the server due to {}.", e.to_string());
                    return;
                }
                _ => (),
            }
        }
    };
}

fn listen(address: &String, port: &u16) -> Result<TcpListener> {
    // Create the full address for the server.
    let full_address = format!("{}:{}", address, port);
    info!("[+] Listening to {}", full_address);

    TcpListener::bind(&full_address)
}

fn read_file(path: &String) -> Result<Vec<u8>> {
    let mut f = File::open(&path)?;
    let mut buf = Vec::new();

    f.read_to_end(&mut buf)?;

    Ok(buf)
}

fn server_run(listener: TcpListener, enclave: &SgxEnclave) -> Result<()> {
    match listener.accept() {
        Ok((socket, addr)) => {
            info!("[+] Got connection from {:?}", addr);

            // Expose the raw socket fd.
            let socket_fd = socket.as_raw_fd();
            let socket_clone = socket.try_clone().unwrap();
            let mut reader = BufReader::new(socket);
            let mut writer = BufWriter::new(socket_clone);
            let message = receive_ra_message(&mut reader)?;

            // Execute the PoBF private computing entry.
            let result = exec_private_computing(enclave, socket_fd, &message);
            
            //Send the data back.
            info!("[+] Send the data back to the data provider...");
            writer.write(result.len().to_string().as_bytes())?;
            writer.write(b"\n")?;
            writer.write(&result)?;
            writer.write(b"\n")?;
            writer.flush()?;

            Ok(())
        }

        Err(e) => Err(e),
    }
}

/// Receives initial messages from the data provider a.k.a. the service provider.
fn receive_ra_message(reader: &mut BufReader<TcpStream>) -> Result<RaMessage> {
    let mut message = RaMessage::default();
    let mut ra_buf = String::with_capacity(128);

    // Check remote attestation type.
    reader.read_line(&mut ra_buf).unwrap();
    if !ra_buf.len() == 2 {
        error!("[-] Remote attestation type is incorrect.");
        return Err(Error::from(ErrorKind::InvalidData));
    }

    // Parse it.
    let ra_type = match ra_buf.chars().next().unwrap() {
        '0' => 0,
        '1' => 1,
        _ => {
            error!("[-] Incorrect remote attestation type!");
            return Err(Error::from(ErrorKind::InvalidData));
        }
    } as u8;

    message.public_key = vec![0u8; 65];
    message.signature = vec![0u8; 0];
    let mut str_buf = String::with_capacity(OUTPUT_BUFFER_SIZE);

    // Read public key.
    reader.read_exact(&mut message.public_key)?;
    message.public_key.truncate(64);

    // Read signature.
    str_buf.clear();
    reader.read_line(&mut str_buf)?;
    let signature_len = str_buf[..str_buf.len() - 1].parse::<usize>().or_else(|e| {
        error!(
            "[-] Cannot parse signature length! Error: {}",
            e.to_string()
        );
        Err(ErrorKind::InvalidData)
    })?;

    message.signature.resize(signature_len + 1, 0u8);
    reader.read_exact(&mut message.signature)?;
    message.signature.truncate(signature_len);

    if ra_type == 0 {
        let mut spid_buf = String::with_capacity(33);
        // Read SPID.
        reader.read_line(&mut spid_buf)?;
        // Decode it.
        let decoded_spid = hex::decode(&spid_buf[..32]).or_else(|e| {
            error!(
                "[-] Cannot decode the spid received from socket! Error: {}",
                e.to_string()
            );
            Err(ErrorKind::InvalidData)
        })?;
        message.spid.id.copy_from_slice(&decoded_spid[..16]);

        // Read linkable.
        reader.read_line(&mut str_buf)?;
        message.linkable = str_buf[..1].parse::<i64>().or_else(|e| {
            error!("[-] Cannot parse `linkable`! Error: {}", e.to_string());
            Err(ErrorKind::InvalidData)
        })?;
    }

    message.ra_type = ra_type;

    Ok(message)
}

fn exec_private_computing(
    enclave: &SgxEnclave,
    socket_fd: c_int,
    ra_message: &RaMessage,
) -> Vec<u8> {
    let mut retval = SgxStatus::Success;
    let mut encrypted_output: Vec<u8> = vec![0u8; OUTPUT_BUFFER_SIZE];
    let mut encrypted_output_size: u32 = 0;

    unsafe {
        private_computing_entry(
            enclave.eid(),
            &mut retval,
            socket_fd,
            &ra_message.spid,
            ra_message.linkable,
            ra_message.ra_type,
            ra_message.public_key.as_ptr() as *const u8,
            ra_message.public_key.len() as u32,
            ra_message.signature.as_ptr() as *const u8,
            ra_message.signature.len() as u32,
            encrypted_output.as_mut_ptr(),
            OUTPUT_BUFFER_SIZE as _,
            &mut encrypted_output_size as _,
        )
    };
    match retval {
        SgxStatus::Success => {
            info!(
                "[+] ECALL Successful, returned size: {}",
                encrypted_output_size
            );
            encrypted_output.truncate(encrypted_output_size as _);
            info!(
                "[+] output encrypted data: {:02X?}",
                &encrypted_output[..(encrypted_output_size as usize - MAC_SIZE) as _]
            );
            info!(
                "[+] output encrypted data mac: {:02X?}",
                &encrypted_output[(encrypted_output_size as usize - MAC_SIZE) as _..]
            );
        }
        e => {
            error!("[-] ECALL Enclave Failed, reason: {}!", e.as_str());
        }
    }

    encrypted_output
}
