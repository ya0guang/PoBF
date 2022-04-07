extern crate sgx_types;
extern crate sgx_urts;

mod ocall;

use clap::{Parser, Subcommand};
use sgx_types::error::*;
use sgx_types::types::*;
use sgx_urts::enclave::SgxEnclave;
use std::fs::File;
use std::io::prelude::*;

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
    Cal { key_path: String, data_path: String },
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
        } => {
            // Sealed [0] * 16
            let mut key_file = File::open(key_path).expect("key file not found");
            let mut sealed_key_log = Vec::new();
            key_file.read_to_end(&mut sealed_key_log).unwrap();

            // Encrypted [42] * 16
            let mut data_file = File::open(data_path).expect("data file not found");
            let mut encrypted_data_vec = Vec::new();
            data_file.read_to_end(&mut encrypted_data_vec).unwrap();
            exec_private_computing(&enclave, &sealed_key_log, &encrypted_data_vec);
        }
    };
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
