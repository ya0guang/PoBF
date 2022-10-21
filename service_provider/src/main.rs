extern crate aes;
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
use dh::*;
use handlers::*;
use log::{debug, info};

use std::io::*;

use crate::utils::*;

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

// Configurations for the IAS.
static IAS_BASE_URL: &'static str = "https://api.trustedservices.intel.com";
// Use the newest APIs. (v3 is decprecated.)
static IAS_BASE_REQUEST: &'static str = "/sgx/dev/attestation/v4/";
static IAS_KEY_HEADER: &'static str = "Ocp-Apim-Subscription-Key";
static IAS_CONTENT_TYPE_HEADER: &'static str = "Content-Type";
static IAS_XIAS_SIGNCERT_HEADER: &'static str = "X-IASReport-Signing-Certificate";
static IAS_XIAS_SIG_HEADER: &'static str = "X-IASReport-Signature";
static IAS_QUOTE_TIMESTAMP: &'static str = "\"timestamp\"";
static ISV_ENCLAVE_QUOTE_STATUS: &'static str = "\"isvEnclaveQuoteStatus\"";
static PLATFORM_INFO_BLOB: &'static str = "\"platformInfoBlob\"";
static ISV_ENCLAVE_QUOTE_BODY: &'static str = "\"isvEnclaveQuoteBody\"";

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

            // Send Spid and public key to the application enclave.
            info!("[+] Sending initial messages including SPID and public key.");
            send_initial_messages(
                &mut writer,
                &spid,
                linkable,
                &key_pair.pub_k,
                &key_pair.signature,
            )
            .unwrap();
            info!("[+] Succeeded.");

            info!("[+] Waiting for Extended Group ID.");
            let sigrl =
                handle_epid(&mut reader, &mut writer, &key).expect("[-] EPID receiving failed.");
            info!("[+] Succeeded.");

            info!("[+] Waiting for public key of the enclave.");
            let enclave_pubkey = handle_enclave_pubkey(&mut reader).unwrap();
            info!("[+] Succeeded.");

            debug!("[+] The public key of the enclave is {:?}", enclave_pubkey);

            info!("[+] Fetching Signature Revocation List from Intel.");
            send_sigrl(&mut writer, sigrl).unwrap();
            info!("[+] Succeeded.");

            // Handle quote.
            info!("[+] Verifying quote.");
            handle_quote(&mut reader, &mut writer, &key).unwrap();
            info!("[+] Succeeded.");

            // Compute shared key.
            info!("[+] Computing ephemeral session key.");
            key_pair
                .compute_shared_key(&enclave_pubkey, KDF_MAGIC_STR.as_bytes())
                .unwrap();
            info!("[+] Succeeded.");

            // Quit.
            writer.write(b"qqqq\n").unwrap();
        }
    }

    info!("[+] Finished!");
}
