extern crate aes;
extern crate aes_gcm;
extern crate base64;
extern crate clap;
extern crate cmac;
extern crate curl;
extern crate env_logger;
extern crate log;
extern crate pem;
extern crate ring;
extern crate serde_json;

mod dh;
mod handlers;
mod utils;

use clap::{Parser, Subcommand};
use handlers::*;
use log::info;

use std::io::*;

use crate::{dh::init_keypair, utils::*};

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
#[clap(propagate_version = true)]
struct Args {
    #[clap(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Run {
        address: String,
        port: u16,
        spid: String,
        key: String,
        // Whether this subscription allows multiple requests from one platform.
        linkable: bool,
    },
}

/// Configurations for the IAS.
const IAS_BASE_URL: &'static str = "https://api.trustedservices.intel.com";
/// Use the newest APIs. (v3 is decprecated.)
const IAS_BASE_REQUEST: &'static str = "/sgx/dev/attestation/v4/";
const IAS_KEY_HEADER: &'static str = "Ocp-Apim-Subscription-Key";
const IAS_CONTENT_TYPE_HEADER: &'static str = "Content-Type";
const IAS_XIAS_SIGNCERT_HEADER: &'static str = "X-IASReport-Signing-Certificate";
const IAS_XIAS_SIG_HEADER: &'static str = "X-IASReport-Signature";
const IAS_QUOTE_TIMESTAMP: &'static str = "\"timestamp\"";
const ISV_ENCLAVE_QUOTE_STATUS: &'static str = "\"isvEnclaveQuoteStatus\"";
const PLATFORM_INFO_BLOB: &'static str = "\"platformInfoBlob\"";
const ISV_ENCLAVE_QUOTE_BODY: &'static str = "\"isvEnclaveQuoteBody\"";

fn main() {
    init_logger();

    let mut key_pair = init_keypair().unwrap();
    let args = Args::parse();
    match args.command {
        Commands::Run {
            address,
            port,
            spid,
            key,
            linkable,
        } => {
            let socket = connect(&address, &port).expect("[-] Cannot connect to the given address");
            let socket_clone = socket.try_clone().unwrap();
            let mut reader = BufReader::new(socket);
            let mut writer = BufWriter::new(socket_clone);

            exec_full_workflow(
                &mut reader,
                &mut writer,
                &mut key_pair,
                &spid,
                linkable,
                &key,
            )
            .expect("[-] Failed to execute workflow.");
        }
    }

    info!("[+] Finished!");
}
