extern crate aes;
extern crate aes_gcm;
extern crate base64;
extern crate clap;
extern crate cmac;
extern crate curl;
extern crate env_logger;
extern crate log;
extern crate pem;
extern crate rand;
extern crate ring;
extern crate serde_json;
extern crate sgx_types;
extern crate sgx_urts;

mod dh;
mod handlers;
mod utils;

use clap::{Parser, Subcommand};
use handlers::*;
use log::{error, info};
use sgx_types::{error::Quote3Error, types::*};

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
        dp_manifest_path: String,
        /// 0 for EPID; 1 for ECDSA (a.k.a. DCAP).
        ra_type: u8,
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
const DEFAULT_MANIFEST_PATH: &'static str = "manifest.json";

/// The enclave path
const ENCLAVE_FILE: &'static str = "../lib/enclave.signed.so";

extern "C" {
    fn sgx_tvl_verify_qve_report_and_identity(
        eid: EnclaveId,
        retval: *mut Quote3Error,
        p_quote: *const u8,
        quote_size: u32,
        p_qve_report_info: *const QlQeReportInfo,
        expiration_check_date: i64,
        collateral_expiration_status: u32,
        quote_verification_result: QlQvResult,
        p_supplemental_data: *const u8,
        supplemental_data_size: u32,
        qve_isvsvn_threshold: u16,
    ) -> Quote3Error;
}

fn main() {
    init_logger();

    let mut key_pair = init_keypair().unwrap();
    let args = Args::parse();
    match args.command {
        Commands::Run {
            address,
            port,
            dp_manifest_path,
            ra_type,
        } => {
            let socket = connect(&address, &port).expect("[-] Cannot connect to the given address");
            let socket_clone = socket.try_clone().unwrap();
            let mut reader = BufReader::new(socket);
            let mut writer = BufWriter::new(socket_clone);
            let dp_information =
                parse_manifest(&dp_manifest_path).expect("[-] Sp manifest file IO error.");

            let data = match ra_type {
                0 => exec_epid_workflow(&mut reader, &mut writer, &mut key_pair, &dp_information)
                    .expect("[-] Failed to execute EPID workflow!"),

                1 => exec_dcap_workflow(&mut reader, &mut writer, &mut key_pair, &dp_information)
                    .expect("[-] Failed to execute DCAP workflow!"),

                _ => {
                    error!("[-] Unrecognized remote attestation type!");
                    return;
                }
            };

            info!("[+] Received result: {:?}", data);
        }
    }

    info!("[+] Finished!");
}
