extern crate aes;
extern crate base64;
extern crate clap;
extern crate cmac;
extern crate curl;
extern crate pem;
extern crate ring;
extern crate serde_json;

mod dh;
mod handlers;
mod utils;

use clap::{Parser, Subcommand};
use dh::*;
use handlers::*;

use std::io::*;

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
    // Generate key pair.
    let (private_key, public_key) = open_session().unwrap();
    println!("[+] Key pair: {:?} and {:?}", private_key, public_key);
    // Sign the public key.
    let pubkey_signature = sign_with_ecdsa(public_key.as_ref()).unwrap();
    println!("[+] Signature is {:?}", pubkey_signature);

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
            send_initial_messages(&mut writer, &spid, linkable, &public_key, &pubkey_signature).unwrap();

            let sigrl =
                handle_epid(&mut reader, &mut writer, &key).expect("[-] EPID receiving failed.");
            let enclave_pubkey = handle_enclave_pubkey(&mut reader).unwrap();
            println!("[+] The public key of the enclave is {:?}", enclave_pubkey);

            send_sigrl(&mut writer, sigrl).unwrap();

            // Handle quote.
            handle_quote(&mut reader, &mut writer, &key).unwrap();

            // Compute shared key.
            let session_key =
                compute_shared_key(private_key, &enclave_pubkey, KDF_MAGIC_STR.as_bytes()).unwrap();

            println!("[+] The session key sampled as {:?}", session_key);

            // Quit.
            writer.write(b"qqqq\n").unwrap();
        }
    }

    println!("[+] Finished!");
}
