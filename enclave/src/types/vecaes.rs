#[cfg(feature = "sgx")]
extern crate sgx_tcrypto;
use super::*;
#[cfg(not(feature = "sgx"))]
use crate::bogus::*;
use crate::ocall_log;
use crate::utils::*;
#[cfg(feature = "sgx")]
use sgx_tcrypto::*;
use sgx_types::*;
use std::vec::Vec;

pub struct VecAESData {
    inner: Vec<u8>,
}

impl From<Vec<u8>> for VecAESData {
    fn from(v: Vec<u8>) -> Self {
        VecAESData { inner: v }
    }
}

impl Into<Vec<u8>> for VecAESData {
    fn into(self) -> Vec<u8> {
        self.inner
    }
}

impl AsRef<[u8]> for VecAESData {
    fn as_ref(&self) -> &[u8] {
        &self.inner[..]
    }
}

impl VecAESData {
    pub fn new(raw: Vec<u8>) -> Self {
        VecAESData { inner: raw }
    }

    pub fn from_ref(raw: &[u8]) -> Self {
        // validity check
        assert!(raw.len() >= 32);
        assert!(raw.len() % 16 == 0);

        let mut inner = Vec::new();
        inner.extend_from_slice(raw);
        VecAESData { inner }
    }

    pub fn to_vec(self) -> Vec<u8> {
        self.inner
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
                ocall_log!("Failed to create sealed data",);
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

impl Encryption<AES128Key> for VecAESData {
    fn encrypt(self, key: &AES128Key) -> SgxResult<Self> {
        let key = key.unseal()?;

        let text_len = self.inner.len();
        let cipher_len = (text_len + 15) / 16 * 16;
        // what if not *16?
        let plaintext_slice = &self.inner[..];
        let mut ciphertext_vec: Vec<u8> = vec![0; cipher_len + 16];

        let mut mac_slice = [0u8; 16];

        let aad_array: [u8; 0] = [0; 0];
        ocall_log!("aes_gcm_128_encrypt parameter prepared!",);
        let iv = [0u8; 12];
        rsgx_rijndael128GCM_encrypt(
            &key.inner,
            plaintext_slice,
            &iv,
            &aad_array,
            &mut ciphertext_vec[..cipher_len],
            &mut mac_slice,
        )?;

        ciphertext_vec[cipher_len..(cipher_len + 16)].copy_from_slice(&mac_slice);
        Ok(VecAESData::new(ciphertext_vec))
    }
}

impl Decryption<AES128Key> for VecAESData {
    fn decrypt(self, key: &AES128Key) -> SgxResult<Self> {
        let key = key.unseal()?;

        // can be a demo
        let len = self.inner.len();
        let text_len = len - 16;
        let ciphertext_slice = &self.inner[..text_len];
        let mac_slice = &self.inner[text_len..(text_len + 16)].try_into().unwrap();
        let mut plaintext_vec: Vec<u8> = vec![0; text_len];
        let plaintext_slice = &mut plaintext_vec[..];

        let iv = [0u8; 12];
        let aad_array: [u8; 0] = [0; 0];

        // can this be checked towards MIRAI?
        ocall_log!("aes_gcm_128_decrypt parameter prepared!",);

        // After everything has been set, call API
        rsgx_rijndael128GCM_decrypt(
            &key.inner,
            ciphertext_slice,
            &iv,
            &aad_array,
            mac_slice,
            plaintext_slice,
        )?;

        Ok(VecAESData::new(plaintext_vec))
    }
}

impl EncDec<AES128Key> for VecAESData {}
