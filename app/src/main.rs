extern crate sgx_types;
extern crate sgx_urts;

use clap::{Parser, Subcommand};
use sgx_types::*;
use sgx_urts::SgxEnclave;

static ENCLAVE_FILE: &'static str = "enclave.signed.so";
const SEALED_LOG_SIZE: u32 = 1024;

extern "C" {
    fn say_something(
        eid: sgx_enclave_id_t,
        retval: *mut sgx_status_t,
        some_string: *const u8,
        len: usize,
    ) -> sgx_status_t;
}

extern "C" {
    fn create_sealeddata_for_fixed(
        eid: sgx_enclave_id_t,
        retval: *mut sgx_status_t,
        sealed_log: * mut u8,
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

    match args.command {
        Commands::Gen => generate_sealed_input(&enclave),
        Commands::Cal => calculate_hash(),
    }

    let input_string = String::from("This is a normal world string passed into Enclave!\n");
    let mut retval = sgx_status_t::SGX_SUCCESS;

    let result = unsafe {
        say_something(
            enclave.geteid(),
            &mut retval,
            input_string.as_ptr() as *const u8,
            input_string.len(),
        )
    };
    match result {
        sgx_status_t::SGX_SUCCESS => {}
        _ => {
            println!("[-] ECALL Enclave Failed {}!", result.as_str());
            return;
        }
    }
    println!("[+] say_something success...");
    enclave.destroy();
}

fn generate_sealed_input(enclave: &SgxEnclave) {

    let mut retval = sgx_status_t::SGX_SUCCESS;

    let mut sealed_log = [0u8; SEALED_LOG_SIZE as usize];

    let rv = unsafe {
        create_sealeddata_for_fixed(
            enclave.geteid(),
            &mut retval,
            sealed_log.as_ptr() as *mut u8,
            SEALED_LOG_SIZE
        )
    };

    match rv {
        sgx_status_t::SGX_SUCCESS => {}
        _ => {
            println!("[-] ECALL Enclave Failed {}!", rv.as_str());
            return;
        }
    }

    println!("Sealed log: {:?}", sealed_log);
}

fn calculate_hash() {

}

fn init_enclave() -> SgxResult<SgxEnclave> {
    let mut launch_token: sgx_launch_token_t = [0; 1024];
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
