#![forbid(unsafe_code)]

#[cfg(not(feature = "sgx"))]
use crate::bogus::SealedData;
use crate::ocall::*;
use crate::ocall_log;
use alloc::vec::Vec;
use prusti_contracts::*;
#[cfg(feature = "sgx")]
use sgx_tseal::seal::SealedData;
use sgx_types::marker::ContiguousMemory;

#[trusted]
pub fn from_sealed_log_for_fixed<'a, T: Copy + ContiguousMemory>(
    sealed_log: &Vec<u8>,
) -> Option<SealedData<T>> {
    let r = SealedData::<T>::from_slice(&sealed_log);

    match r {
        Ok(x) => Some(x),
        Err(e) => {
            #[cfg(not(feature = "use_prusti"))]
            ocall_log!("Error occurs {:?}", e);

            None
        }
    }
}
