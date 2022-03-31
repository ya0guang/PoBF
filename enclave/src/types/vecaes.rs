#![forbid(unsafe_code)]

use super::*;
use crate::ocall::*;
use crate::utils::*;
use crate::{ocall_log, verified_log};
use sgx_crypto::aes::gcm::*;
use sgx_types::error::*;
use std::vec::Vec;

pub struct VecAESData {
    inner: Vec<u8>,
}

impl From<Vec<u8>> for VecAESData {
    fn from(v: Vec<u8>) -> Self {
        VecAESData { inner: v }
    }
}

impl From<&[u8]> for VecAESData {
    fn from(raw: &[u8]) -> Self {
        // validity check
        assert!(raw.len() >= 32);
        assert!(raw.len() % 16 == 0);

        let mut inner = Vec::new();
        inner.extend_from_slice(raw);
        VecAESData { inner }
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

pub struct AES128Key {
    buffer: Vec<u8>,
    inner: [u8; 16],
}

impl Default for AES128Key {
    fn default() -> Self {
        AES128Key {
            buffer: vec![],
            inner: [0u8; 16],
        }
    }
}

impl AES128Key {
    pub fn from_sealed_buffer(sealed_buffer: &[u8]) -> SgxResult<Self> {
        assert!(sealed_buffer.len() <= BUFFER_SIZE);
        let buffer = sealed_buffer.to_vec();
        let key = AES128Key {
            buffer,
            inner: [0u8; 16],
        };
        Ok(key)
    }

    fn unseal(&self) -> SgxResult<Self> {
        let opt = from_sealed_log_for_fixed::<[u8; SEALED_DATA_SIZE]>(&self.buffer);
        let sealed_data = match opt {
            Some(x) => x,
            _ => {
                verified_log!("Failed to create sealed data",);
                return Err(SgxStatus::NotSgxFile);
            }
        };

        let result = sealed_data.unseal()?;
        let data = result.to_plaintext();
        let mut temp_key = AES128Key::default();
        temp_key.inner.copy_from_slice(data);
        Ok(temp_key)
    }
}

impl Encryption<AES128Key> for VecAESData {
    fn encrypt(self, key: &AES128Key) -> SgxResult<Self> {
        let key = key.unseal()?;
        let aad_array: [u8; 0] = [0; 0];
        let aad = Aad::from(aad_array);
        let mut aes = AesGcm::new(&key.inner, Nonce::zeroed(), aad)?;
        let text_len = self.inner.len();
        let cipher_len = text_len.checked_add(15).unwrap() / 16 * 16;
        // what if not *16?
        let plaintext_slice = &self.inner[..];
        let mut ciphertext_vec: Vec<u8> = vec![0; cipher_len + 16];

        verified_log!("aes_gcm_128_encrypt parameter prepared!",);
        let mac = aes.encrypt(plaintext_slice, &mut ciphertext_vec[..cipher_len])?;
        ciphertext_vec[cipher_len..(cipher_len + 16)].copy_from_slice(&mac);
        Ok(VecAESData::from(ciphertext_vec))
    }
}

impl Decryption<AES128Key> for VecAESData {
    fn decrypt(self, key: &AES128Key) -> SgxResult<Self> {
        let key = key.unseal()?;
        let aad_array: [u8; 0] = [0; 0];
        let aad = Aad::from(aad_array);
        let mut aes = AesGcm::new(&key.inner, Nonce::zeroed(), aad)?;
        let len = self.inner.len();
        let text_len = len.checked_sub(16).unwrap();
        let ciphertext_slice = &self.inner[..text_len];
        let mac_slice = &self.inner[text_len..(text_len + 16)].try_into().unwrap();
        let mut plaintext_vec: Vec<u8> = vec![0; text_len];
        let plaintext_slice = &mut plaintext_vec[..];

        verified_log!("aes_gcm_128_decrypt parameter prepared!",);
        aes.decrypt(ciphertext_slice, plaintext_slice, mac_slice)?;
        Ok(VecAESData::from(plaintext_vec))
    }
}

impl EncDec<AES128Key> for VecAESData {}
