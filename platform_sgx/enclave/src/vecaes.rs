#![forbid(unsafe_code)]

use crate::dh::DhSession;
use crate::ocall::*;
use crate::utils::*;
use alloc::vec;
use alloc::vec::Vec;
use mirai_annotations::*;
use sgx_crypto::aes::gcm::*;
use sgx_types::error::*;
use sgx_types::types::Mac128bit;
use sgx_types::types::MAC_128BIT_SIZE;
use zeroize::Zeroize;

cfg_if::cfg_if! {
  if #[cfg(mirai)] {
      use crate::mirai_types::*;
      use crate::mirai_types::mirai_comp::SecretTaint;
  } else {
      use pobf_state::*;

      type SecretTaint = ();
  }
}

pub const BUFFER_SIZE: usize = 1024;
pub const SEALED_DATA_SIZE: usize = 16;

pub struct VecAESData {
    inner: Vec<u8>,
}

#[cfg(mirai)]
// Give a sanitize function to `VecAESData`.
fn sanitize(input: VecAESData) -> VecAESData {
    precondition!(has_tag!(&input, SecretTaint));

    let inner = vec![];
    let ans = VecAESData { inner };

    // MIRAI has problem dealing with vector, so we mark it as an assumption here.
    // MIRAI will give an error if it is 100% certain that the condition does not hold.
    // This suppresses false positive.
    assumed_postcondition!(does_not_have_tag!(&ans, SecretTaint));
    ans
}

impl Zeroize for VecAESData {
    fn zeroize(&mut self) {
        self.inner.zeroize();
    }
}

impl From<Vec<u8>> for VecAESData {
    fn from(v: Vec<u8>) -> Self {
        VecAESData { inner: v }
    }
}

impl From<&[u8]> for VecAESData {
    fn from(raw: &[u8]) -> Self {
        // Validity check: should have a mac tag.
        checked_assume!(raw.len() >= MAC_128BIT_SIZE);

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

impl Zeroize for AES128Key {
    fn zeroize(&mut self) {
        self.inner.zeroize();
        self.buffer.zeroize();
    }
}

impl AES128Key {
    /// Sometimes, keys are not always from sealed, they can be ephemeral ones that are only valid for specific sessions.
    /// This function deals with such circumstances.
    pub fn from_ecdh_key(key: &DhSession) -> SgxResult<Self> {
        precondition!(has_tag!(key, SecretTaint));

        // Need to check the session's validity.
        if !key.is_valid() {
            return Err(SgxStatus::InvalidParameter);
        }

        let mut ret = Self::default();
        ret.inner = key
            .session_context()
            .smk()
            .as_ref()
            .clone()
            .try_into()
            .or_else(|_| Err(SgxStatus::InvalidParameter))?;

        let ans = Ok(ret);

        #[cfg(mirai)]
        add_tag!(&ans, SecretTaint);
        ans
    }

    // Deprecate.
    #[deprecated]
    #[allow(unused)]
    pub fn from_sealed_buffer(sealed_buffer: &[u8]) -> SgxResult<Self> {
        assert!(sealed_buffer.len() <= BUFFER_SIZE);
        let buffer = sealed_buffer.to_vec();
        let key = AES128Key {
            buffer,
            inner: [0u8; 16],
        };
        Ok(key)
    }

    // Deprecate.
    #[deprecated]
    #[allow(unused)]
    fn unseal(&self) -> SgxResult<Self> {
        let opt = from_sealed_log_for_fixed::<[u8; SEALED_DATA_SIZE]>(&self.buffer);
        let sealed_data = match opt {
            Some(x) => x,
            _ => {
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
    /// GCM uses CTR internally. It encrypts a counter value for each block, but it
    /// only uses as many bits as required from the last block. CTR turns the block
    /// cipher into a stream cipher so that output length = input length.
    fn encrypt(self, key: &AES128Key) -> SgxResult<Self> {
        cfg_if::cfg_if! {
            if #[cfg(mirai)] {
                precondition!(has_tag!(&self, SecretTaint));
                precondition!(has_tag!(key, SecretTaint));

                let ciphertext = sanitize(self);
                assumed_postcondition!(does_not_have_tag!(&ciphertext, SecretTaint));

                Ok(ciphertext)
            } else {
                // We do not need AAD tag so we set it to zero.
                let aad_array: [u8; 0] = [0; 0];
                let aad = Aad::from(aad_array);

                let mut aes = AesGcm::new(&key.inner, Nonce::zeroed(), aad)?;
                let mut ciphertext = vec![0u8; self.inner.len()];

                // Append the mac tag.
                let mac = aes.encrypt(&self.inner, ciphertext.as_mut_slice())?;
                ciphertext.extend_from_slice(&mac);

                Ok(VecAESData::from(ciphertext))
            }
        }
    }
}

impl Decryption<AES128Key> for VecAESData {
    fn decrypt(self, key: &AES128Key) -> SgxResult<Self> {
        precondition!(has_tag!(&self, SecretTaint));

        cfg_if::cfg_if! {
            if #[cfg(mirai)] {
                let plaintext_vec = VecAESData::from(self.inner);

                postcondition!(has_tag!(&plaintext_vec, SecretTaint));
                Ok(plaintext_vec)
            } else {
                let aad_array: [u8; 0] = [0; 0];
                let aad = Aad::from(aad_array);
                let mut aes = AesGcm::new(&key.inner, Nonce::zeroed(), aad)?;

                let len = self.inner.len();
                let text_len = len.checked_sub(16).unwrap();

                let ciphertext_slice = &self.inner[..text_len];
                let mac_slice: &Mac128bit = &self.inner[text_len..(text_len + 16)].try_into().unwrap();
                let mut plaintext_vec: Vec<u8> = vec![0; text_len];
                let plaintext_slice = &mut plaintext_vec[..];

                aes.decrypt(ciphertext_slice, plaintext_slice, mac_slice)?;
                Ok(VecAESData::from(plaintext_vec))
            }
        }
    }
}

impl EncDec<AES128Key> for VecAESData {}
