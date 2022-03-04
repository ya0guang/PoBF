extern crate sgx_types;
extern crate sgx_urts;

use clap::{Parser, Subcommand};
use sgx_types::*;
use sgx_urts::SgxEnclave;

static ENCLAVE_FILE: &'static str = "enclave.signed.so";
const SEALED_LOG_SIZE: usize = 1024;

extern "C" {
    fn sample_task(
        eid: sgx_enclave_id_t,
        retval: *mut sgx_status_t,
        sealed_log: *mut u8,
        sealed_log_size: u32,
    ) -> sgx_status_t;
}

extern "C" {
    fn create_sealeddata_for_fixed(
        eid: sgx_enclave_id_t,
        retval: *mut sgx_status_t,
        sealed_log: *mut u8,
        sealed_log_size: u32,
    ) -> sgx_status_t;
}

extern "C" {
    fn verify_sealeddata_for_fixed(
        eid: sgx_enclave_id_t,
        retval: *mut sgx_status_t,
        sealed_log: *const u8,
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

    let sealed_output = match args.command {
        Commands::Gen => generate_sealed_input(&enclave),
        Commands::Cal => {
            let sealed_log = generate_sealed_input(&enclave);
            exec_sample_task(&enclave, sealed_log)
        }
    };

    println!("[+] say_something success...");
    enclave.destroy();
}

fn generate_sealed_input(enclave: &SgxEnclave) -> [u8; SEALED_LOG_SIZE] {
    let mut retval = sgx_status_t::SGX_SUCCESS;

    let mut sealed_log = [0u8; SEALED_LOG_SIZE as usize];

    let rv = unsafe {
        create_sealeddata_for_fixed(
            enclave.geteid(),
            &mut retval,
            sealed_log.as_ptr() as *mut u8,
            SEALED_LOG_SIZE as u32,
        )
    };

    match rv {
        sgx_status_t::SGX_SUCCESS => {}
        _ => panic!("Failed ECALL to create sealed data"),
    }

    // println!("Sealed log after sealing: {:?}", sealed_log);

    let rv = unsafe {
        verify_sealeddata_for_fixed(
            enclave.geteid(),
            &mut retval,
            sealed_log.as_ptr() as *const u8,
            SEALED_LOG_SIZE as u32,
        )
    };

    match rv {
        sgx_status_t::SGX_SUCCESS => {}
        _ => panic!("[-] ECALL Enclave Failed {}!", rv.as_str()),
    }

    println!("Sealed log after verifying: {:?}", sealed_log);

    sealed_log
}

fn exec_sample_task(enclave: &SgxEnclave, sealed_log: [u8; SEALED_LOG_SIZE]) -> [u8; SEALED_LOG_SIZE] {
    let mut retval = sgx_status_t::SGX_SUCCESS;

    let rv = unsafe {
        sample_task(
            enclave.geteid(),
            &mut retval,
            sealed_log.as_ptr() as *mut u8,
            SEALED_LOG_SIZE as u32,
        )
    };

    match rv {
        sgx_status_t::SGX_SUCCESS => {}
        _ => {
            panic!("[-] ECALL Enclave Failed {}!", rv.as_str());
        }
    }

    // println!("Sealed log after sealing: {:?}", sealed_log);

    let rv = unsafe {
        verify_sealeddata_for_fixed(
            enclave.geteid(),
            &mut retval,
            sealed_log.as_ptr() as *const u8,
            SEALED_LOG_SIZE as u32,
        )
    };

    match rv {
        sgx_status_t::SGX_SUCCESS => {}
        _ => panic!("[-] ECALL Enclave Failed {}!", rv.as_str()),
    }

    println!("Unsealed data: {:?}", sealed_log);

    sealed_log
}

fn init_enclave() -> SgxResult<SgxEnclave> {
    let mut launch_token: sgx_launch_token_t = [0; SEALED_LOG_SIZE];
    let mut launch_token_updated: i32 = 0;
    // call sgx_create_enclave to initialize an enclave instance
    // Debug Support: set 2nd parameter to 1
    let debug = 1;
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
