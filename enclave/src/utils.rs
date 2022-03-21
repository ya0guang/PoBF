use crate::types::*;
use sgx_tseal::SgxSealedData;
use sgx_types::marker::ContiguousMemory;
use sgx_types::*;

pub fn from_sealed_log_for_fixed<'a, T: Copy + ContiguousMemory>(
    sealed_log: *mut u8,
    sealed_log_size: u32,
) -> Option<SgxSealedData<'a, T>> {
    unsafe {
        SgxSealedData::<T>::from_raw_sealed_data_t(
            sealed_log as *mut sgx_sealed_data_t,
            sealed_log_size,
        )
    }
}

pub fn to_sealed_log_for_fixed<T: Copy + ContiguousMemory>(
    sealed_data: &SgxSealedData<T>,
    sealed_log: *mut u8,
    sealed_log_size: u32,
) -> Option<*mut sgx_sealed_data_t> {
    unsafe {
        sealed_data.to_raw_sealed_data_t(sealed_log as *mut sgx_sealed_data_t, sealed_log_size)
    }
}

pub fn key_from_sealed_buffer(sealed_buffer: &[u8]) -> AES128Key {
    let opt = from_sealed_log_for_fixed::<[u8; SEALED_DATA_SIZE]>(
        sealed_buffer.as_ptr() as *mut u8,
        BUFFER_SIZE as u32,
    );
    let sealed_data = match opt {
        Some(x) => x,
        _ => panic!("Failed to create sealed data"),
    };

    let result = sealed_data.unseal_data();
    let unsealed_data = match result {
        Ok(x) => x,
        Err(ret) => panic!("Failed to unseal data: {:?}", ret),
    };
    let data = unsealed_data.get_decrypt_txt();
    let mut key: AES128Key = AES128Key::default();
    println!("DEBUG: the AES128key is {:?}", key);
    key.copy_from_slice(data);
    key
}
