use crate::{
    DEFAULT_MANIFEST_PATH, IAS_BASE_REQUEST, IAS_BASE_URL, IAS_QUOTE_TIMESTAMP,
    IAS_XIAS_SIGNCERT_HEADER, IAS_XIAS_SIG_HEADER, ISV_ENCLAVE_QUOTE_BODY,
    ISV_ENCLAVE_QUOTE_STATUS, PLATFORM_INFO_BLOB,
};

use std::env;
use std::fs::*;
use std::io::*;

use base64::prelude::BASE64_STANDARD_NO_PAD;
use base64::Engine;
use log::error;
use serde::{Deserialize, Serialize};

#[derive(Deserialize, Serialize)]
pub struct DpInformation {
    pub address: String,
    pub port: u16,
    pub spid: String,
    pub ias_key: String,
    pub linkable: bool,
    pub data_path: String,
    pub ra_type: u8,
}

#[derive(Serialize, Deserialize)]
pub struct IasQuoteReport {
    quote_timestamp: String,
    quote_status: String,

    // The whole response body.
    quote_report_raw: String,
    quote_body: String,
    quote_signature: String,
    quote_certificate: String,

    // A TLV containing an opaque binary blob that the Service Provider and
    // the ISV SGX Application are supposed to forward to SGX Platform
    // SW. This field is encoded using Base 16 encoding scheme.
    // This field is optional, it will only be present if one the following
    // conditions is met:
    // * isvEnclaveQuoteStatus is equal to GROUP_REVOKED,
    //     GROUP_OUT_OF_DATE or CONFIGURATION_NEEDED,
    // * pseManifestStatus is equal to one of the following values:
    //     OUT_OF_DATE, REVOKED or RL_VERSION_MISMATCH.
    platform_info_blob: String,
}

pub fn get_full_url(request: &str) -> String {
    format!("{}{}{}", IAS_BASE_URL, IAS_BASE_REQUEST, request)
}

pub fn parse_sigrl(sigrl: &Vec<u8>) -> Result<Vec<u8>> {
    if sigrl.is_empty() {
        Ok(Vec::new())
    } else {
        Ok(BASE64_STANDARD_NO_PAD
            .decode(std::str::from_utf8(sigrl).unwrap())
            .unwrap())
    }
}

pub fn parse_quote_report(raw_header: Vec<u8>, raw_response: Vec<u8>) -> Result<Vec<u8>> {
    let mut quote_signature = String::new();
    let mut quote_certificate = String::new();
    // Extract the field of certificate and signature from the header.
    // Since this is a http response header, we can split it by \n.
    let header_str = String::from_utf8(raw_header).unwrap();
    let header_kv = header_str.lines();
    // Iterate over each line to check if this is target line.
    for line in header_kv.into_iter() {
        if line.starts_with(IAS_XIAS_SIG_HEADER) {
            quote_signature.push_str(line.rsplit_once(": ").unwrap().1);
        } else if line.starts_with(IAS_XIAS_SIGNCERT_HEADER) {
            quote_certificate.push_str(line.rsplit_once(": ").unwrap().1);
        }
    }

    // Extract some necessary fields from response body.
    let mut quote_status = String::new();
    let mut quote_body = String::new();
    let mut platform_info_blob = String::new();
    let mut quote_timestamp = String::new();

    let response_str = String::from_utf8(raw_response.clone()).unwrap();
    let response_kv: Vec<&str> = response_str.split(",").collect();
    // Iterate over each key-value pair.
    for kv in response_kv.into_iter() {
        // Throw away extra quote signs.
        if let Some((_, cur)) = kv.split_once(":") {
            if kv.starts_with(ISV_ENCLAVE_QUOTE_STATUS) {
                let status = &cur[1..cur.len() - 1];

                // Status error!
                if status != "OK"
                    && status != "GROUP_OUT_OF_DATE"
                    && status != "CONFIGURATION_NEEDED"
                {
                    println!("[-] Error status found returned as {}!", status);
                    return Err(Error::from(ErrorKind::InvalidData));
                }

                quote_status.push_str(status);
            } else if kv.starts_with(ISV_ENCLAVE_QUOTE_BODY) {
                quote_body.push_str(&cur[1..cur.len() - 1]);
            } else if kv.starts_with(PLATFORM_INFO_BLOB) {
                platform_info_blob.push_str(&cur[1..cur.len() - 1]);
            } else if kv.starts_with(IAS_QUOTE_TIMESTAMP) {
                quote_timestamp.push_str(&cur[1..cur.len() - 1]);
            }
        }
    }

    let quote_report = IasQuoteReport {
        quote_timestamp,
        quote_status,
        quote_signature,
        quote_report_raw: String::from_utf8(raw_response).unwrap(),
        quote_body,
        quote_certificate,
        platform_info_blob,
    };

    Ok(serde_json::to_vec(&quote_report).unwrap())
}

pub fn init_logger() {
    // Get environment variable.
    if env::var("RUST_LOG").is_err() {
        env::set_var("RUST_LOG", "INFO");
    }

    env_logger::init();
}

pub fn parse_manifest(path: &String) -> Result<DpInformation> {
    let f = File::open(path).or_else(|_| File::open(DEFAULT_MANIFEST_PATH))?;
    let dp_information: DpInformation =
        serde_json::from_reader(f).expect("[-] Failed to parse the manifest json file.");

    // Check lengths.
    if dp_information.data_path.is_empty() || dp_information.address.is_empty() {
        error!("[-] Found empty field which is expected to be non-empty.");

        Err(Error::from(ErrorKind::InvalidData))
    } else if dp_information.ra_type == 0
        && (dp_information.ias_key.is_empty() || dp_information.spid.is_empty())
    {
        error!("[-] IAS key or SPID is empty!");

        Err(Error::from(ErrorKind::InvalidData))
    } else {
        Ok(dp_information)
    }
}
