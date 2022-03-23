#[cfg(feature = "sgx")]
extern crate sgx_tcrypto;
#[cfg(not(feature = "sgx"))]
use crate::bogus::*;
use crate::state::*;
use crate::utils::*;
#[cfg(feature = "sgx")]
use sgx_tcrypto::*;
use sgx_types::*;
use std::vec::Vec;

#[derive(Copy, Clone, Debug)]
pub struct ArrayAESData {
    pub inner: [u8; BUFFER_SIZE],
    pub mac: [u8; SGX_AESGCM_MAC_SIZE],
    pub length: usize,
}

impl ArrayAESData {
    pub fn new(raw: [u8; BUFFER_SIZE], mac: [u8; SGX_AESGCM_MAC_SIZE], length: usize) -> Self {
        ArrayAESData {
            inner: raw,
            mac,
            length,
        }
    }

    pub fn from_ref(raw_r: &[u8], mac_r: &[u8], length: usize) -> Self {
        let mut raw = [0_u8; BUFFER_SIZE];
        raw.copy_from_slice(raw_r);
        let mut mac = [0_u8; SGX_AESGCM_MAC_SIZE];
        assert!(mac_r.len() == SGX_AESGCM_MAC_SIZE);
        mac.copy_from_slice(mac_r);
        ArrayAESData {
            inner: raw,
            mac,
            length,
        }
    }
}

pub struct AES128Key {
    buffer: [u8; BUFFER_SIZE],
    inner: [u8; 16],
}

impl Default for AES128Key {
    fn default() -> Self {
        AES128Key {
            buffer: [0u8; BUFFER_SIZE],
            inner: [0u8; 16],
        }
    }
}

impl AES128Key {
    // Need to zeroize the buffer?
    pub fn from_sealed_buffer(sealed_buffer: &[u8]) -> SgxResult<Self> {
        assert!(sealed_buffer.len() == BUFFER_SIZE);
        let mut key = AES128Key::default();
        key.buffer.copy_from_slice(sealed_buffer);
        Ok(key)
    }

    fn unseal(&self) -> SgxResult<Self> {
        let opt = from_sealed_log_for_fixed::<[u8; SEALED_DATA_SIZE]>(
            self.buffer.as_ptr() as *mut u8,
            BUFFER_SIZE as u32,
        );
        let sealed_data = match opt {
            Some(x) => x,
            _ => {
                println!("Failed to create sealed data");
                return Err(sgx_status_t::SGX_ERROR_FILE_NOT_SGX_FILE);
            }
        };

        let result = sealed_data.unseal_data()?;
        let data = result.get_decrypt_txt();
        let mut temp_key = AES128Key::default();
        temp_key.inner.copy_from_slice(data);
        Ok(temp_key)
    }
}

impl EncDec<AES128Key> for ArrayAESData {
    // iv: default value [0u8; 12]
    fn decrypt(self, key: &AES128Key) -> SgxResult<Self> {
        let key = key.unseal()?;
        // can be a demo
        let ciphertext_slice = &self.inner[..self.length];
        let mut plaintext_vec: Vec<u8> = vec![0; self.length];
        let plaintext_slice = &mut plaintext_vec[..];
        let iv = [0u8; 12];
        let aad_array: [u8; 0] = [0; 0];
        println!(
            "aes_gcm_128_decrypt parameter prepared! {}",
            plaintext_slice.len()
        );

        // debug
        println!("DEBUG: ciphertext_slice: {:?}", ciphertext_slice);
        println!("DEBUG: mac: {:?}", self.mac);

        // After everything has been set, call API
        rsgx_rijndael128GCM_decrypt(
            &key.inner,
            ciphertext_slice,
            &iv,
            &aad_array,
            &self.mac,
            plaintext_slice,
        )?;

        let mut decrypted_buffer = [0u8; BUFFER_SIZE];
        decrypted_buffer[..self.length].copy_from_slice(plaintext_slice);

        Ok(ArrayAESData::new(decrypted_buffer, self.mac, self.length))
    }

    fn encrypt(self, key: &AES128Key) -> SgxResult<Self> {
        let key = key.unseal()?;
        let plaintext_slice = &self.inner[..self.length];
        let mut ciphertext_vec: Vec<u8> = vec![0; self.length];
        let ciphertext_slice = &mut ciphertext_vec[..];

        let aad_array: [u8; 0] = [0; 0];
        let mut mac_array: [u8; SGX_AESGCM_MAC_SIZE] = [0; SGX_AESGCM_MAC_SIZE];
        println!(
            "aes_gcm_128_encrypt parameter prepared! {}",
            plaintext_slice.len()
        );
        let iv = [0u8; 12];
        rsgx_rijndael128GCM_encrypt(
            &key.inner,
            plaintext_slice,
            &iv,
            &aad_array,
            ciphertext_slice,
            &mut mac_array,
        )?;

        let mut encrypt_buffer = [0u8; BUFFER_SIZE];

        encrypt_buffer[..self.length].copy_from_slice(ciphertext_slice);

        Ok(ArrayAESData::new(encrypt_buffer, mac_array, self.length))
    }
}
