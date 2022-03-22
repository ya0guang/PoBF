use crate::state::*;

#[cfg(not(feature = "sgx"))]
use crate::bogus::SgxSealedData;
use crate::utils::*;
#[cfg(feature = "sgx")]
use sgx_tseal::SgxSealedData;
use sgx_types::*;
use std::vec::Vec;

#[derive(Copy, Clone, Debug)]
pub struct SealedData {
    pub inner: [u8; BUFFER_SIZE],
}

impl SealedData {
    pub fn new(raw: [u8; BUFFER_SIZE]) -> Self {
        SealedData { inner: raw }
    }

    pub fn from_ref(r: &[u8]) -> Self {
        let mut raw = [0_u8; BUFFER_SIZE];
        raw.copy_from_slice(r);
        SealedData { inner: raw }
    }
}

impl EncDec<Vec<u8>> for SealedData {
    fn decrypt(self, _key: &Vec<u8>) -> SgxResult<Self> {
        let opt = from_sealed_log_for_fixed::<[u8; SEALED_DATA_SIZE]>(
            self.inner.as_ptr() as *mut u8,
            BUFFER_SIZE as u32,
        );

        let sealed_data = match opt {
            Some(x) => x,
            _ => {
                println!("Failed to create sealed data");
                return Err(sgx_status_t::SGX_ERROR_FILE_NOT_SGX_FILE);
            }
        };

        let unsealed_data = sealed_data.unseal_data()?;
        let data = unsealed_data.get_decrypt_txt();
        let mut rv = SealedData {
            inner: [0u8; BUFFER_SIZE],
        };
        rv.inner[..data.len()].copy_from_slice(data);
        Ok(rv)
    }

    fn encrypt(self, _key: &Vec<u8>) -> SgxResult<Self> {
        let mut buffer = [0u8; SEALED_DATA_SIZE];
        buffer.copy_from_slice(&self.inner[..SEALED_DATA_SIZE]);
        let aad: [u8; 0] = [0_u8; 0];
        let result = SgxSealedData::<[u8; SEALED_DATA_SIZE]>::seal_data(&aad, &buffer)?;

        let rv = SealedData {
            inner: [0u8; BUFFER_SIZE],
        };
        let opt =
            to_sealed_log_for_fixed(&result, rv.inner.as_ptr() as *mut u8, BUFFER_SIZE as u32);
        if opt.is_none() {
            println!("Failed to convert sealed data to raw data");
            return Err(sgx_status_t::SGX_ERROR_UNEXPECTED);
        }
        Ok(rv)
    }
}
