extern crate sgx_types;
extern crate sgx_urts;

use clap::{Parser, Subcommand};
use sgx_types::*;
use sgx_urts::SgxEnclave;

static ENCLAVE_FILE: &'static str = "enclave.signed.so";
const SEALED_LOG_SIZE: usize = 1024;

extern "C" {

    fn private_computing_entry(
        eid: sgx_enclave_id_t,
        retval: *mut sgx_status_t,
        sealed_key_ptr: *mut u8,
        sealed_key_size: u32,
        encrypted_input_ptr: *mut u8,
        encrypted_input_size: u32,
        encrypted_output_buffer_ptr: *mut u8,
        encrypted_output_buffer_size: u32,
        encrypted_output_size: *mut u32,
    ) -> sgx_status_t;

    fn generate_fixed_sealeddata(
        eid: sgx_enclave_id_t,
        retval: *mut sgx_status_t,
        sealed_log_ptr: *mut u8,
        sealed_log_size: u32,
    ) -> sgx_status_t;

    #[allow(dead_code)]
    fn verify_sealeddata_for_fixed(
        eid: sgx_enclave_id_t,
        retval: *mut sgx_status_t,
        sealed_log_ptr: *const u8,
        sealed_log_size: u32,
    ) -> sgx_status_t;
}

/// Simple program to greet a person
#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
#[clap(propagate_version = true)]
struct Args {
    #[clap(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Generate a sealed input
    Gen,

    /// Calculate the hash of a sealed input
    Cal,
}

fn main() {
    let args = Args::parse();

    let enclave = match init_enclave() {
        Ok(r) => {
            println!("[+] Init Enclave Successful {}!", r.geteid());
            r
        }
        Err(x) => {
            println!("[-] Init Enclave Failed {}!", x.as_str());
            return;
        }
    };

    // Encrypted input preparation
    // Encrypted [42] * 16
    let encrypted_data: [u8; 16] = [
        0x29, 0xa2, 0xf0, 0xe4, 0x4a, 0x9c, 0x89, 0xb8, 0xd9, 0x02, 0xe8, 0x93, 0x5b, 0x98, 0xd4,
        0x52,
    ];
    let encrypted_data_mac: [u8; SGX_AESGCM_MAC_SIZE] = [
        0x6b, 0xbb, 0xcb, 0x9c, 0xb8, 0x7e, 0x5b, 0xcb, 0xfe, 0x31, 0x38, 0xf0, 0x9c, 0x1f, 0x0a,
        0x28,
    ];
    let mut encrypted_data_vec = Vec::new();
    encrypted_data_vec.extend_from_slice(&encrypted_data);
    encrypted_data_vec.extend_from_slice(&encrypted_data_mac);

    match args.command {
        Commands::Gen => {
            generate_sealed_key(&enclave);
        }
        Commands::Cal => {
            let sealed_key_log = generate_sealed_key(&enclave);
            exec_private_computing(&enclave, sealed_key_log, &encrypted_data_vec);
        }
    };

    println!("[+] say_something success...");
    enclave.destroy();
}

fn generate_sealed_key(enclave: &SgxEnclave) -> [u8; SEALED_LOG_SIZE] {
    let mut retval = sgx_status_t::SGX_SUCCESS;

    let mut sealed_log = [0u8; SEALED_LOG_SIZE as usize];

    let rv = unsafe {
        generate_fixed_sealeddata(
            enclave.geteid(),
            &mut retval,
            sealed_log.as_mut_ptr() as *mut u8,
            SEALED_LOG_SIZE as u32,
        )
    };

    match rv {
        sgx_status_t::SGX_SUCCESS => {}
        _ => panic!("Failed ECALL to create sealed data"),
    }

    // uncomment the following line to print the sealed data
    // let rv = unsafe {
    //     verify_sealeddata_for_fixed(
    //         enclave.geteid(),
    //         &mut retval,
    //         sealed_log.as_ptr() as *const u8,
    //         SEALED_LOG_SIZE as u32,
    //     )
    // };
    // match rv {
    //     sgx_status_t::SGX_SUCCESS => {}
    //     _ => panic!("[-] ECALL Enclave Failed {}!", rv.as_str()),
    // }
    // println!("Sealed log after verification: {:?}", sealed_log);

    sealed_log
}

fn exec_private_computing(
    enclave: &SgxEnclave,
    sealed_key_log: [u8; SEALED_LOG_SIZE],
    encrypted_input: &Vec<u8>,
) -> Vec<u8> {
    let mut retval = sgx_status_t::SGX_SUCCESS;

    // default output buffer size is 2048
    let encrypted_output_buffer_size = 2048;
    let mut encrypted_output: Vec<u8> = vec![0u8; encrypted_output_buffer_size];
    let mut encrypted_output_size: u32 = 0;

    let rv = unsafe {
        private_computing_entry(
            enclave.geteid(),
            &mut retval,
            sealed_key_log.as_ptr() as *mut u8,
            SEALED_LOG_SIZE as u32,
            encrypted_input.as_ptr() as *mut u8,
            encrypted_input.len() as u32,
            encrypted_output.as_mut_ptr(),
            encrypted_output_buffer_size as _,
            &mut encrypted_output_size as _,
        )
    };
    match rv {
        sgx_status_t::SGX_SUCCESS => {
            println!(
                "[+] ECALL Successful, returned size: {}",
                encrypted_output_size
            );
            encrypted_output.truncate(encrypted_output_size as _);
            println!(
                "[+] output encrypted data: {:02X?}",
                &encrypted_output[..(encrypted_output_size - 16) as _]
            );
            println!(
                "[+] output encrypted data mac: {:02X?}",
                &encrypted_output[(encrypted_output_size - 16) as _..]
            );
        }
        e => {
            println!("[-] ECALL Enclave Failed {}!", e.as_str());
        }
    }

    encrypted_output
}

fn init_enclave() -> SgxResult<SgxEnclave> {
    let mut launch_token: sgx_launch_token_t = [0; SEALED_LOG_SIZE];
    let mut launch_token_updated: i32 = 0;
    // call sgx_create_enclave to initialize an enclave instance
    // Debug Support: set 2nd parameter to 1
    let debug = 0;
    let mut misc_attr = sgx_misc_attribute_t {
        secs_attr: sgx_attributes_t { flags: 0, xfrm: 0 },
        misc_select: 0,
    };
    SgxEnclave::create(
        ENCLAVE_FILE,
        debug,
        &mut launch_token,
        &mut launch_token_updated,
        &mut misc_attr,
    )
}
