use aes_gcm::{aead::Aead, Aes128Gcm, AesGcm, KeyInit, Nonce};
use pobf_state::{Decryption, EncDec, Encryption, Result};
use zeroize::Zeroize;

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

impl Zeroize for VecAESData {
    fn zeroize(&mut self) {
        self.inner.zeroize();
    }
}

/// A struct used to represent the SEV key from MAA.
pub struct AES128Key {
    inner: [u8; 16],
}

impl From<Vec<u8>> for AES128Key {
    fn from(value: Vec<u8>) -> Self {
        Self {
            inner: {
                let mut data = [0u8; 16];
                data.copy_from_slice(&value[..16]);
                data
            },
        }
    }
}

impl Default for AES128Key {
    fn default() -> Self {
        AES128Key { inner: [0u8; 16] }
    }
}

impl Zeroize for AES128Key {
    fn zeroize(&mut self) {
        self.inner.zeroize();
    }
}

impl Encryption<AES128Key> for VecAESData {
    // For the sake of simplicity, we incorporate a static nonce into the ciphertext, but it is trivial to implement
    // AES-GCM algorithm using an OS-generated nonce.
    fn encrypt(self, key: &AES128Key) -> Result<Self> {
        let cipher = Aes128Gcm::new(key.inner.as_ref().into());
        let nonce = Nonce::from_slice(&[0u8; 12]);
        let ciphertext = cipher.encrypt(nonce, self.inner.as_slice()).unwrap();

        Ok(VecAESData::from(ciphertext))
    }
}

impl Decryption<AES128Key> for VecAESData {
    fn decrypt(self, key: &AES128Key) -> Result<Self> {
        let cipher = Aes128Gcm::new(key.inner.as_ref().into());
        let nonce = Nonce::from_slice(&[0u8; 12]);
        let plaintext = cipher.decrypt(nonce, self.inner.as_slice()).unwrap();

        Ok(VecAESData::from(plaintext))
    }
}

impl EncDec<AES128Key> for VecAESData {}
