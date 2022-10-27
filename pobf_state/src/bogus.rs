use crate::*;
use alloc::vec;
use alloc::vec::*;
use prusti_contracts::*;
use zeroize::*;

pub struct VecAESData {
    inner: Vec<u8>,
}

impl Zeroize for VecAESData {
    #[trusted]
    fn zeroize(&mut self) {
        self.inner.zeroize();
    }
}

impl From<Vec<u8>> for VecAESData {
    #[trusted]
    fn from(v: Vec<u8>) -> Self {
        VecAESData { inner: v }
    }
}

impl From<&[u8]> for VecAESData {
    #[trusted]
    fn from(raw: &[u8]) -> Self {
        let mut inner = Vec::new();
        inner.extend_from_slice(raw);
        VecAESData { inner }
    }
}

impl Into<Vec<u8>> for VecAESData {
    #[trusted]
    fn into(self) -> Vec<u8> {
        self.inner
    }
}

impl AsRef<[u8]> for VecAESData {
    #[trusted]
    fn as_ref(&self) -> &[u8] {
        &self.inner[..]
    }
}

pub struct AES128Key {
    buffer: Vec<u8>,
    inner: [u8; 16],
}

impl Default for AES128Key {
    #[trusted]
    fn default() -> Self {
        AES128Key {
            buffer: vec![],
            inner: [0u8; 16],
        }
    }
}

impl Zeroize for AES128Key {
    #[trusted]
    fn zeroize(&mut self) {
        self.inner.zeroize();
        self.buffer.zeroize();
    }
}

impl AES128Key {}

impl Encryption<AES128Key> for VecAESData {
    #[trusted]
    fn encrypt(self, key: &AES128Key) -> Result<Self> {
        Ok(self)
    }
}

impl Decryption<AES128Key> for VecAESData {
    #[trusted]
    fn decrypt(self, key: &AES128Key) -> Result<Self> {
        Ok(self)
    }
}

impl EncDec<AES128Key> for VecAESData {}

/// A sample workflow for Prusti verification. All types are implemented in bogus types as Prusti cannot fully support all the features of Rust.
/// So we need this to circumvent the difficulties.
/// Prusti will try to verify if each step of the type state can be transitted into another, and
/// since we care about the correctness of type state transition, we "trust" all the internal
/// implementations of utility functions such as cryptographic algorithms.
#[cfg(feature = "use_prusti")]
#[allow(unused)]
pub fn pobf_workflow_verify() -> VecAESData {
    use task::*;

    let template = ComputingTaskTemplate::<Initialized>::new();
    let session: ComputingTaskSession<ChannelEstablished, AES128Key> =
        ComputingTaskSession::establish_channel(template);

    let task_data_received = ComputingTask::receive_data(session);

    let task_result_encrypted = task_data_received.compute();

    task_result_encrypted.take_result()
}
