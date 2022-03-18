extern crate sgx_tcrypto;

use crate::utils::*;
use sgx_tseal::SgxSealedData;
use sgx_types::marker::ContiguousMemory;
use std::vec::Vec;

pub const LOG_BUFFER_SIZE: usize = 1024;
pub const SEALED_DATA_SIZE: usize = 16;

pub struct Input;
pub struct Output;

pub trait IOState {}
impl IOState for Input {}
impl IOState for Output {}

pub struct Encrypted;
pub struct Decrypted;

pub trait EncryptionState {}
impl EncryptionState for Encrypted {}
impl EncryptionState for Decrypted {}

pub struct Sealed;
pub struct Invalid;

pub trait InputKeyState {
    type KeyState;
}

impl<D> InputKeyState for Data<Encrypted, Input, D>
where
    D: ContiguousMemory,
{
    type KeyState = Sealed;
}

impl<D> InputKeyState for Data<Decrypted, Input, D>
where
    D: ContiguousMemory,
{
    type KeyState = Invalid;
}

impl<D> InputKeyState for Data<Decrypted, Output, D>
where
    D: ContiguousMemory,
{
    type KeyState = Invalid;
}

impl<D> InputKeyState for Data<Encrypted, Output, D>
where
    D: ContiguousMemory,
{
    type KeyState = Invalid;
}

pub trait OutputKeyState {
    type KeyState;
}

impl<D> OutputKeyState for Data<Encrypted, Input, D>
where
    D: ContiguousMemory,
{
    type KeyState = Sealed;
}

impl<D> OutputKeyState for Data<Decrypted, Input, D>
where
    D: ContiguousMemory,
{
    type KeyState = Sealed;
}

impl<D> OutputKeyState for Data<Decrypted, Output, D>
where
    D: ContiguousMemory,
{
    type KeyState = Sealed;
}

impl<D> OutputKeyState for Data<Encrypted, Output, D>
where
    D: ContiguousMemory,
{
    type KeyState = Invalid;
}

pub trait EncDec {
    fn encrypt(self, key: &Vec<u8>) -> Self;
    fn decrypt(self, key: &Vec<u8>) -> Self;
}

#[derive(Copy, Clone, Debug)]
pub struct SealedData {
    pub inner: [u8; LOG_BUFFER_SIZE],
}

impl SealedData {
    pub fn new(raw: [u8; LOG_BUFFER_SIZE]) -> Self {
        SealedData { inner: raw }
    }

    pub fn from_ref(r: &[u8]) -> Self {
        let mut raw = [0_u8; LOG_BUFFER_SIZE];
        raw.copy_from_slice(r);
        SealedData { inner: raw }
    }
}

impl EncDec for SealedData {
    fn decrypt(self, _key: &Vec<u8>) -> Self {
        let opt = from_sealed_log_for_fixed::<[u8; SEALED_DATA_SIZE]>(
            self.inner.as_ptr() as *mut u8,
            LOG_BUFFER_SIZE as u32,
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
        let mut rv = SealedData {
            inner: [0u8; LOG_BUFFER_SIZE],
        };
        rv.inner[..data.len()].copy_from_slice(data);
        rv
    }

    fn encrypt(self, _key: &Vec<u8>) -> Self {
        let mut buffer = [0u8; SEALED_DATA_SIZE];
        buffer.copy_from_slice(&self.inner[..SEALED_DATA_SIZE]);
        let aad: [u8; 0] = [0_u8; 0];
        let result = SgxSealedData::<[u8; SEALED_DATA_SIZE]>::seal_data(&aad, &buffer);

        let sealed_data = match result {
            Ok(x) => x,
            Err(ret) => panic!("Failed to seal data: {:?}", ret),
        };
        let rv = SealedData {
            inner: [0u8; LOG_BUFFER_SIZE],
        };
        let opt = to_sealed_log_for_fixed(
            &sealed_data,
            rv.inner.as_ptr() as *mut u8,
            LOG_BUFFER_SIZE as u32,
        );
        if opt.is_none() {
            panic!("Failed to convert sealed data to raw data");
        }
        rv
    }
}

unsafe impl ContiguousMemory for SealedData {}

pub struct Data<S, T, D: ContiguousMemory>
where
    S: EncryptionState,
    T: IOState,
{
    // inner data
    raw: D,
    // Ecrypted / Decrypted
    _encryption_state: S,
    // Input / Output
    _io_state: T,
}

impl<D> Data<Encrypted, Input, D>
where
    D: ContiguousMemory,
{
    pub fn new(raw: D) -> Self {
        Self {
            raw,
            _encryption_state: Encrypted,
            _io_state: Input,
        }
    }
}

impl<D> Data<Encrypted, Input, D>
where
    D: ContiguousMemory + EncDec,
{
    pub fn decrypt(self, key: &Key<Sealed>) -> Data<Decrypted, Input, D> {
        Data {
            raw: self.raw.decrypt(&key.raw),
            _encryption_state: Decrypted,
            _io_state: Input,
        }
    }
}

impl<D> Data<Decrypted, Input, D>
where
    D: ContiguousMemory,
{
    pub fn invoke(self, fun: &dyn Fn(D) -> D) -> Data<Decrypted, Output, D> {
        Data {
            raw: fun(self.raw),
            _encryption_state: Decrypted,
            _io_state: Output,
        }
    }
}

impl<D> Data<Decrypted, Output, D>
where
    D: ContiguousMemory + EncDec,
{
    pub fn encrypt(self, key: &Key<Sealed>) -> Data<Encrypted, Output, D> {
        Data {
            raw: self.raw.encrypt(&key.raw),
            _encryption_state: Encrypted,
            _io_state: Output,
        }
    }
}

type AES128Key = [u8; 16];

pub struct Key<S> {
    pub raw: Vec<u8>,
    // Sealed / Invalid
    _key_state: S,
}

impl Key<Sealed> {
    pub fn new(raw: Vec<u8>) -> Key<Sealed> {
        Key {
            raw: raw,
            _key_state: Sealed,
        }
    }

    pub fn zeroize(mut self) -> Key<Invalid> {
        self.raw.fill(0);
        Key {
            raw: self.raw,
            _key_state: Invalid,
        }
    }
}

pub struct ProtectedAssets<S, T, D>
where
    Data<S, T, D>: InputKeyState,
    Data<S, T, D>: OutputKeyState,
    S: EncryptionState,
    T: IOState,
    D: ContiguousMemory,
{
    data: Data<S, T, D>,
    input_key: Key<<Data<S, T, D> as InputKeyState>::KeyState>,
    output_key: Key<<Data<S, T, D> as OutputKeyState>::KeyState>,
}

// impl<T> Borrow<T> for ProtectedAssets<Encrypted, T>
// where
//     Data<Encrypted, T>: InputKeyState,
//     Data<Encrypted, T>: OutputKeyState,
//     T: IOState,
// {
//     fn borrow(&self) -> &T {
//        panic!()
//     }
// }

impl<D> ProtectedAssets<Encrypted, Input, D>
where
    D: ContiguousMemory + EncDec,
{
    pub fn decrypt(self) -> ProtectedAssets<Decrypted, Input, D> {
        ProtectedAssets {
            data: self.data.decrypt(&self.input_key),
            input_key: self.input_key.zeroize(),
            output_key: self.output_key,
        }
    }

    pub fn new(raw: D, input_key: Vec<u8>, output_key: Vec<u8>) -> Self {
        ProtectedAssets {
            data: Data::new(raw),
            input_key: Key::new(input_key),
            output_key: Key::new(output_key),
        }
    }
}

impl<D> ProtectedAssets<Decrypted, Input, D>
where
    D: ContiguousMemory,
{
    pub fn invoke(self, fun: &dyn Fn(D) -> D) -> ProtectedAssets<Decrypted, Output, D> {
        ProtectedAssets {
            data: self.data.invoke(fun),
            input_key: self.input_key,
            output_key: self.output_key,
        }
    }
}

impl<D> ProtectedAssets<Decrypted, Output, D>
where
    D: ContiguousMemory + EncDec,
{
    pub fn encrypt(self) -> ProtectedAssets<Encrypted, Output, D> {
        ProtectedAssets {
            data: self.data.encrypt(&self.output_key),
            input_key: self.input_key,
            output_key: self.output_key.zeroize(),
        }
    }
}

impl<D> ProtectedAssets<Encrypted, Output, D>
where
    D: ContiguousMemory + EncDec,
{
    pub fn take(self) -> D {
        self.data.raw
    }
}
