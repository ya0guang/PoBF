#![forbid(unsafe_code)]

#[cfg(not(feature = "sgx"))]
use crate::bogus::SealedData;
use crate::ocall::*;
use crate::ocall_log;
use alloc::vec::Vec;
use alloc::string::String;
#[cfg(feature = "sgx")]
use sgx_tseal::seal::SealedData;
use sgx_types::marker::ContiguousMemory;

pub fn from_sealed_log_for_fixed<'a, T: Copy + ContiguousMemory>(
    sealed_log: &Vec<u8>,
) -> Option<SealedData<T>> {
    let r = SealedData::<T>::from_slice(&sealed_log);

    match r {
        Ok(x) => Some(x),
        Err(e) => {
            ocall_log!("Error occurs {:?}", e);
            None
        }
    }
}

/// Special characters are http-encoded, we want to remove these base64-unrecognizable tokens.
/// Also, we do not need the CA cert here.
pub fn process_raw_cert(cert_raw: &Vec<u8>) -> String {
    let cert_removed = alloc::str::from_utf8(cert_raw).unwrap().replace("%0A", "");
    // Decode %.
    let cert = String::from(
        percent_encoding::percent_decode_str(&cert_removed)
            .decode_utf8()
            .unwrap(),
    );

    let v: Vec<&str> = cert.split("-----").collect();

    String::from(v[2])
}