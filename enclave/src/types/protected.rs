#[cfg(feature = "sgx")]
extern crate sgx_tcrypto;
#[cfg(not(feature = "sgx"))]
use crate::bogus::*;
use crate::state::*;
#[cfg(feature = "sgx")]
use sgx_tcrypto::*;
#[cfg(feature = "sgx")]
use sgx_tseal::SgxSealedData;
use sgx_types::SGX_AESGCM_MAC_SIZE;
use std::slice;
use std::vec::Vec;
use crate::utils::*;

#[derive(Copy, Clone, Debug)]
pub struct ProtectedData {
    pub inner: [u8; BUFFER_SIZE],
    pub mac: [u8; SGX_AESGCM_MAC_SIZE],
    pub length: usize,
}

impl ProtectedData {
    pub fn new(raw: [u8; BUFFER_SIZE], mac: [u8; SGX_AESGCM_MAC_SIZE], length: usize) -> Self {
        ProtectedData {
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
        ProtectedData {
            inner: raw,
            mac,
            length,
        }
    }
}

// pub type AES128Key = [u8; 16];
#[derive(Default)]
pub struct AES128Key {
    inner: [u8; 16],
}

impl AES128Key {
    pub fn from_sealed_buffer(sealed_buffer: &[u8]) -> Self {
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
        // println!("DEBUG: the AES128key is {:?}", key);
        key.inner.copy_from_slice(data);
        key
    }
}

impl EncDec<AES128Key> for ProtectedData {
    // iv: default value [0u8; 12]
    fn decrypt(self, key: &AES128Key) -> Self {
        // avoid unsafe!
        // can be a demo
        let ciphertext_slice = unsafe { slice::from_raw_parts(self.inner.as_ptr(), self.length) };

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
        let result = rsgx_rijndael128GCM_decrypt(
            &key.inner,
            &ciphertext_slice,
            &iv,
            &aad_array,
            &self.mac,
            plaintext_slice,
        );

        let mut decrypted_buffer = [0u8; BUFFER_SIZE];

        match result {
            Err(x) => {
                panic!("Error occurs in decryption, {:?}", x);
            }
            Ok(()) => {
                decrypted_buffer[..self.length].copy_from_slice(plaintext_slice);
            }
        };

        // zeroize the key
        ProtectedData::new(decrypted_buffer, self.mac, self.length)
    }

    fn encrypt(self, key: &AES128Key) -> Self {
        let plaintext_slice = unsafe { slice::from_raw_parts(self.inner.as_ptr(), self.length) };
        let mut ciphertext_vec: Vec<u8> = vec![0; self.length];
        let ciphertext_slice = &mut ciphertext_vec[..];

        let aad_array: [u8; 0] = [0; 0];
        let mut mac_array: [u8; SGX_AESGCM_MAC_SIZE] = [0; SGX_AESGCM_MAC_SIZE];
        println!(
            "aes_gcm_128_encrypt parameter prepared! {}",
            plaintext_slice.len()
        );
        let iv = [0u8; 12];
        let result = rsgx_rijndael128GCM_encrypt(
            &key.inner,
            &plaintext_slice,
            &iv,
            &aad_array,
            ciphertext_slice,
            &mut mac_array,
        );

        let mut encrypt_buffer = [0u8; BUFFER_SIZE];

        match result {
            Err(x) => {
                panic!("Error occurs in decryption, {:?}", x);
            }
            Ok(()) => {
                encrypt_buffer[..self.length].copy_from_slice(ciphertext_slice);
            }
        };

        ProtectedData::new(encrypt_buffer, mac_array, self.length)
    }
}
