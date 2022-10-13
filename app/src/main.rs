extern crate sgx_types;
extern crate sgx_urts;

mod ocall;

use clap::{Parser, Subcommand};
use sgx_types::error::*;
use sgx_types::types::*;
use sgx_urts::enclave::SgxEnclave;
use std::fs::File;
use std::io::prelude::*;
use std::io::Result;
use std::io::{BufReader, BufWriter};
use std::mem::size_of;
use std::net::TcpListener;
use std::os::unix::prelude::AsRawFd;

static ENCLAVE_FILE: &'static str = "enclave.signed.so";
const OUTPUT_BUFFER_SIZE: usize = 2048;

extern "C" {
    fn private_computing_entry(
        eid: EnclaveId,
        retval: *mut SgxStatus,
        sealed_key_ptr: *mut u8,
        sealed_key_size: u32,
        encrypted_input_ptr: *mut u8,
        encrypted_input_size: u32,
        encrypted_output_buffer_ptr: *mut u8,
        encrypted_output_buffer_size: u32,
        encrypted_output_size: *mut u32,
    ) -> SgxStatus;

    fn start_remote_attestation(
        eid: EnclaveId,
        retval: *mut SgxStatus,
        socket_fd: i32,
        ti: *mut TargetInfo,
        ti_len: u32,
    ) -> SgxStatus;

    fn generate_quote(
        eid: EnclaveId,
        retval: *mut SgxStatus,
        ti: *const TargetInfo,
        ti_len: u32,
        sigrl: *const u8,
        sigrl_len: u32,
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
    Cal {
        key_path: String,
        data_path: String,
        address: String,
        port: u16,
    },
}

fn main() {
    let enclave = match SgxEnclave::create(ENCLAVE_FILE, false) {
        Ok(r) => {
            println!("[+] Init Enclave Successful, eid: {}!", r.eid());
            r
        }
        Err(x) => {
            println!("[-] Init Enclave Failed, reason: {}!", x.as_str());
            return;
        }
    };

    let args = Args::parse();
    match args.command {
        Commands::Cal {
            key_path,
            data_path,
            address,
            port,
        } => {
            // Sealed [0] * 16
            let sealed_key_log = read_file(&key_path).unwrap();
            // Encrypted [42] * 16
            let encrypted_data_vec = read_file(&data_path).unwrap();

            let listener = match listen(&address, &port) {
                Ok(res) => res,
                Err(e) => {
                    println!("{}", e.to_string());
                    return;
                }
            };

            match server_start(listener, &enclave, &encrypted_data_vec, &sealed_key_log) {
                Err(e) => {
                    println!("Error running the server: {}", e.to_string());
                    return;
                }
                _ => (),
            }
        }
    };
}

fn listen(address: &String, port: &u16) -> Result<TcpListener> {
    // Create the full address for the server.
    let mut full_address = String::new();
    full_address.push_str(address);
    full_address.push_str(":");
    full_address.push_str(&port.to_string());

    println!("[+] Listening to {}", full_address);

    TcpListener::bind(&full_address)
}

fn read_file(path: &String) -> Result<Vec<u8>> {
    let mut f = File::open(&path).expect(&format!("File {} not found", path));
    let mut buf = Vec::new();

    f.read_to_end(&mut buf)?;

    Ok(buf)
}

fn server_start(
    listener: TcpListener,
    enclave: &SgxEnclave,
    data: &Vec<u8>,
    key: &Vec<u8>,
) -> Result<()> {
    let mut ra_done = false;

    match listener.accept() {
        Ok((socket, addr)) => {
            println!("[+] Got connection from {:?}", addr);

            // Expose the raw socket fd.
            let socket_fd = socket.as_raw_fd();
            let mut ti = TargetInfo::default();

            // Create the buffer.
            // let socket_clone = socket.try_clone().unwrap();
            let mut reader = BufReader::new(socket);
            // let mut writer = BufWriter::new(socket_clone);
            loop {
                // Command explanations:
                // 1: Do RA.
                // 2: Execute private computing.
                // 3: Read SigRL.
                //
                // Other keys are used to quit the server.
                // For receiving the socket data.
                let mut s = String::with_capacity(1);
                let size = reader.read_line(&mut s).unwrap();

                if size == 0 {
                    continue;
                }

                println!("[+] Successfully read {} bytes from the client.", size);

                match s.chars().next().unwrap() {
                    '1' => {
                        println!("[+] Performing remote attestation!");

                        match exec_remote_attestation(&enclave, socket_fd, &mut ti) {
                            SgxStatus::Success => ra_done = true,
                            _ => panic!("[-] Remote attestation intial state failed."),
                        }
                    }

                    '2' => {
                        // Should do RA first.
                        if !ra_done {
                            println!(
                                "[-] You should first do remote attestation before private computing!"
                            );
                            continue;
                        } else {
                            println!("[+] Performing private computating!");

                            exec_private_computing(enclave, key, data);

                            println!("[+] Private computing successfully done!");
                        }
                    }
                    '3' => {
                        println!("[+] Receiving SigRL from the SP!");
                        // Read SigRL's length.
                        let mut s = String::with_capacity(OUTPUT_BUFFER_SIZE);
                        reader.read_line(&mut s).unwrap();
                        let length = s[..s.len() - 1].parse::<usize>().unwrap();
                        println!("[+] SigRL length = {}.", length);

                        // Read SigRL.
                        let mut sigrl = Vec::with_capacity(length);
                        reader.read(&mut sigrl).unwrap();
                        println!("[+] SigRl is {:?}", sigrl);

                        // Generate quote.
                        match exec_generate_quote(&enclave, socket_fd, &sigrl, &ti) {
                            SgxStatus::Success => println!("[+] Successfully generated quote!"),
                            _ => panic!("[-] Remote attestation quote generation failed."),
                        }
                    }

                    // Throw away.
                    _ => {
                        println!("[+] Quitting the server...");

                        return Ok(());
                    }
                }
            }
        }

        Err(e) => return Err(e),
    }
}

fn exec_remote_attestation(
    enclave: &SgxEnclave,
    socket_fd: c_int,
    ti: &mut TargetInfo,
) -> SgxStatus {
    let mut retval = SgxStatus::Success;
    let len = std::mem::size_of::<TargetInfo>();
    unsafe {
        start_remote_attestation(
            enclave.eid(),
            &mut retval,
            socket_fd,
            ti as *mut _,
            len as u32,
        );
    }

    retval
}

fn exec_generate_quote(
    enclave: &SgxEnclave,
    socket_fd: c_int,
    sigrl: &Vec<u8>,
    ti: &TargetInfo,
) -> SgxStatus {
    let mut retval = SgxStatus::Success;

    unsafe {
        generate_quote(
            enclave.eid(),
            &mut retval,
            ti,
            size_of::<TargetInfo>() as u32,
            sigrl.as_slice().as_ptr(),
            sigrl.len() as u32,
        )
    };

    retval
}

fn exec_private_computing(
    enclave: &SgxEnclave,
    sealed_key_log: &Vec<u8>,
    encrypted_input: &Vec<u8>,
) -> Vec<u8> {
    let mut retval = SgxStatus::Success;
    let mut encrypted_output: Vec<u8> = vec![0u8; OUTPUT_BUFFER_SIZE];
    let mut encrypted_output_size: u32 = 0;

    unsafe {
        private_computing_entry(
            enclave.eid(),
            &mut retval,
            sealed_key_log.as_ptr() as *mut u8,
            sealed_key_log.len() as u32,
            encrypted_input.as_ptr() as *mut u8,
            encrypted_input.len() as u32,
            encrypted_output.as_mut_ptr(),
            OUTPUT_BUFFER_SIZE as _,
            &mut encrypted_output_size as _,
        )
    };
    match retval {
        SgxStatus::Success => {
            println!(
                "[+] ECALL Successful, returned size: {}",
                encrypted_output_size
            );
            encrypted_output.truncate(encrypted_output_size as _);
            println!(
                "[+] output encrypted data: {:02X?}",
                &encrypted_output[..(encrypted_output_size as usize - MAC_SIZE) as _]
            );
            println!(
                "[+] output encrypted data mac: {:02X?}",
                &encrypted_output[(encrypted_output_size as usize - MAC_SIZE) as _..]
            );
        }
        e => {
            println!("[-] ECALL Enclave Failed, reason: {}!", e.as_str());
        }
    }

    encrypted_output
}
