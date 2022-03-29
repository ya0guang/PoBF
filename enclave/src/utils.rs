#[cfg(not(feature = "sgx"))]
use crate::bogus::SealedData;
#[cfg(feature = "sgx")]
use sgx_tseal::seal::SealedData;
use sgx_types::marker::ContiguousMemory;
use std::vec::Vec;

pub fn from_sealed_log_for_fixed<'a, T: Copy + ContiguousMemory>(
    sealed_log: &Vec<u8>,
) -> Option<SealedData<T>> {
    // let r = SealedData::<T>::from_bytes(sealed_log);
    let r = SealedData::<T>::from_slice(&sealed_log);

    // println!("DEBUG: from_sealed_log_for_fixed: {:?}", r);
    match r {
        Ok(x) => Some(x),
        Err(e) => {
            println!("Error occurs {:?}", e);
            None
        }
    }
}
