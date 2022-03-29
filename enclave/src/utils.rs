#[cfg(not(feature = "sgx"))]
use crate::bogus::SealedData;
#[cfg(feature = "sgx")]
use sgx_tseal::seal::SealedData;
use sgx_types::marker::ContiguousMemory;
use std::slice;
use std::vec::Vec;


pub fn from_sealed_log_for_fixed<'a, T: Copy + ContiguousMemory>(
    sealed_log: &Vec<u8>
) -> Option<SealedData<T>> {
    // let r = SealedData::<T>::from_bytes(sealed_log);
    let r = SealedData::<T>::from_slice(&sealed_log);

    // println!("DEBUG: from_sealed_log_for_fixed: {:?}", r);
    match r {
        Ok(x) => Some(x),
        Err(e) => {println!("Error occurs {:?}", e); None},
    }
}

pub fn to_sealed_log_for_fixed<T: Copy + ContiguousMemory>(
    sealed_data: &SealedData<T>,
    sealed_key_ptr: *mut u8,
    sealed_key_buffer_size: u32,
) -> Option<()> {
    if sealed_key_buffer_size < sealed_data.payload_size() as u32 {
        return None;
    } else {
        let bytes = match sealed_data.to_bytes() {
            Ok(x) => x,
            Err(_) => return None,
        };

        println!("DEBUG: sealed_bytes: {:?}", bytes);
        unsafe {
            std::ptr::copy_nonoverlapping(
                bytes.as_ptr(),
                sealed_key_ptr,
                bytes.len(),
            );
        }
        return Some(());
    }
}
