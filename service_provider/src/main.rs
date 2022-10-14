extern crate base64;
extern crate clap;
extern crate curl;
extern crate serde;

mod handlers;

use clap::{Parser, Subcommand};
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
    },
}

// Configurations for the IAS.
static IAS_BASE_URL: &'static str = "https://api.trustedservices.intel.com";
// Use the newest APIs. (v3 is decprecated.)
static IAS_BASE_REQUEST: &'static str = "/sgx/dev/attestation/v4/";
static IAS_KEY_HEADER: &'static str = "Ocp-Apim-Subscription-Key";
static IAS_CONTENT_TYPE_HEADER: &'static str = "Content-Type";

fn main() {
    let args = Args::parse();
    match args.command {
        Commands::Run {
            address,
            port,
            spid,
            key,
        } => {
            let socket = connect(&address, &port).expect("[-] Cannot connect to the given address");
            let socket_clone = socket.try_clone().unwrap();
            let mut reader = BufReader::new(socket);
            let mut writer = BufWriter::new(socket_clone);

            // Send Spid to the application enclave.
            send_spid(&mut writer, &spid).unwrap();

            let sigrl =
                handle_epid(&mut reader, &mut writer, &key).expect("[-] EPID receiving failed.");
            send_sigrl(&mut writer, sigrl).unwrap();

            // Handle quote.
            handle_quote(&mut reader, &mut writer, &key).unwrap();

            // Quite.
            writer.write(b"q\n").unwrap();
        }
    }

    println!("[+] Finished!");
}
