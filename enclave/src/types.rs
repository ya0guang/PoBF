#[cfg(feature = "sgx")]
extern crate sgx_tcrypto;
#[cfg(feature = "sgx")]
use sgx_tcrypto::*;


#[cfg(not(feature = "sgx"))]
use crate::bogus::*;
use crate::utils::*;
#[cfg(not(feature = "sgx"))]
use crate::bogus::SgxSealedData;
#[cfg(feature = "sgx")]
use sgx_tseal::SgxSealedData;
use sgx_types::marker::ContiguousMemory;
use sgx_types::SGX_AESGCM_MAC_SIZE;
use std::marker::PhantomData;
use std::slice;
use std::vec::Vec;

pub const BUFFER_SIZE: usize = 1024;
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

// Key States and it's enforcements

pub struct Sealed;
pub struct Invalid;

pub trait InputKeyState {
    type KeyState;
}

impl<D, K> InputKeyState for Data<Encrypted, Input, D, K>
where
    D: ContiguousMemory + EncDec<K>,
{
    type KeyState = Sealed;
}

impl<D, K> InputKeyState for Data<Decrypted, Input, D, K>
where
    D: ContiguousMemory + EncDec<K>,
{
    type KeyState = Invalid;
}

impl<D, K> InputKeyState for Data<Decrypted, Output, D, K>
where
    D: ContiguousMemory + EncDec<K>,
{
    type KeyState = Invalid;
}

impl<D, K> InputKeyState for Data<Encrypted, Output, D, K>
where
    D: ContiguousMemory + EncDec<K>,
{
    type KeyState = Invalid;
}

pub trait OutputKeyState {
    type KeyState;
}

impl<D, K> OutputKeyState for Data<Encrypted, Input, D, K>
where
    D: ContiguousMemory + EncDec<K>,
{
    type KeyState = Sealed;
}

impl<D, K> OutputKeyState for Data<Decrypted, Input, D, K>
where
    D: ContiguousMemory + EncDec<K>,
{
    type KeyState = Sealed;
}

impl<D, K> OutputKeyState for Data<Decrypted, Output, D, K>
where
    D: ContiguousMemory + EncDec<K>,
{
    type KeyState = Sealed;
}

impl<D, K> OutputKeyState for Data<Encrypted, Output, D, K>
where
    D: ContiguousMemory + EncDec<K>,
{
    type KeyState = Invalid;
}

pub trait EncDec<K> {
    fn encrypt(self, key: &K) -> Self;
    fn decrypt(self, key: &K) -> Self;
}

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
    fn decrypt(self, _key: &Vec<u8>) -> Self {
        let opt = from_sealed_log_for_fixed::<[u8; SEALED_DATA_SIZE]>(
            self.inner.as_ptr() as *mut u8,
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
        let mut rv = SealedData {
            inner: [0u8; BUFFER_SIZE],
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
            inner: [0u8; BUFFER_SIZE],
        };
        let opt = to_sealed_log_for_fixed(
            &sealed_data,
            rv.inner.as_ptr() as *mut u8,
            BUFFER_SIZE as u32,
        );
        if opt.is_none() {
            panic!("Failed to convert sealed data to raw data");
        }
        rv
    }
}

unsafe impl ContiguousMemory for SealedData {}

#[derive(Copy, Clone, Debug)]
pub struct EncData {
    pub inner: [u8; BUFFER_SIZE],
    pub mac: [u8; SGX_AESGCM_MAC_SIZE],
    pub length: usize,
}

impl EncData {
    pub fn new(raw: [u8; BUFFER_SIZE], mac: [u8; SGX_AESGCM_MAC_SIZE], length: usize) -> Self {
        EncData {
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
        EncData {
            inner: raw,
            mac,
            length,
        }
    }
}

impl EncDec<AES128Key> for EncData {
    // iv: default value [0u8; 12]
    fn decrypt(self, key: &AES128Key) -> Self {
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
            key,
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
        EncData::new(decrypted_buffer, self.mac, self.length)
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
            key,
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

        EncData::new(encrypt_buffer, mac_array, self.length)
    }
}

unsafe impl ContiguousMemory for EncData {}

pub struct Data<S, T, D, K>
where
    S: EncryptionState,
    T: IOState,
    D: ContiguousMemory + EncDec<K>,
{
    // inner data
    raw: D,
    // Ecrypted / Decrypted
    _encryption_state: S,
    // Input / Output
    _io_state: T,
    _key_type: PhantomData<K>,
}

impl<D, K> Data<Encrypted, Input, D, K>
where
    D: ContiguousMemory + EncDec<K>,
{
    pub fn new(raw: D) -> Self {
        Self {
            raw,
            _encryption_state: Encrypted,
            _io_state: Input,
            _key_type: PhantomData,
        }
    }
}

impl<D, K> Data<Encrypted, Input, D, K>
where
    D: ContiguousMemory + EncDec<K>,
    K: Default,
{
    pub fn decrypt(self, key: &Key<K, Sealed>) -> Data<Decrypted, Input, D, K> {
        Data {
            raw: self.raw.decrypt(key.raw_ref()),
            _encryption_state: Decrypted,
            _io_state: Input,
            _key_type: PhantomData,
        }
    }
}

impl<D, K> Data<Decrypted, Input, D, K>
where
    D: ContiguousMemory + EncDec<K>,
{
    pub fn invoke(self, fun: &dyn Fn(D) -> D) -> Data<Decrypted, Output, D, K> {
        Data {
            raw: fun(self.raw),
            _encryption_state: Decrypted,
            _io_state: Output,
            _key_type: PhantomData,
        }
    }
}

impl<D, K> Data<Decrypted, Output, D, K>
where
    D: ContiguousMemory + EncDec<K>,
    K: Default,
{
    pub fn encrypt(self, key: &Key<K, Sealed>) -> Data<Encrypted, Output, D, K> {
        Data {
            raw: self.raw.encrypt(&key.raw_ref()),
            _encryption_state: Encrypted,
            _io_state: Output,
            _key_type: PhantomData,
        }
    }
}

pub struct Key<K, S> {
    pub raw: K,
    // Sealed / Invalid
    _key_state: S,
}

pub type AES128Key = [u8; 16];

impl<K> Key<K, Sealed>
where
    K: Default,
{
    pub fn new(raw: K) -> Key<K, Sealed> {
        Key {
            raw: raw,
            _key_state: Sealed,
        }
    }

    fn raw_ref(&self) -> &K {
        &self.raw
    }

    // zone allocator will zerorize self!
    pub fn zeroize(self) -> Key<K, Invalid> {
        Key {
            raw: K::default(),
            _key_state: Invalid,
        }
    }
}

pub struct ProtectedAssets<S, T, D, K>
where
    Data<S, T, D, K>: InputKeyState,
    Data<S, T, D, K>: OutputKeyState,
    S: EncryptionState,
    T: IOState,
    D: ContiguousMemory + EncDec<K>,
{
    data: Data<S, T, D, K>,
    input_key: Key<K, <Data<S, T, D, K> as InputKeyState>::KeyState>,
    output_key: Key<K, <Data<S, T, D, K> as OutputKeyState>::KeyState>,
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

impl<D, K> ProtectedAssets<Encrypted, Input, D, K>
where
    D: ContiguousMemory + EncDec<K>,
    K: Default,
{
    pub fn decrypt(self) -> ProtectedAssets<Decrypted, Input, D, K> {
        ProtectedAssets {
            data: self.data.decrypt(&self.input_key),
            input_key: self.input_key.zeroize(),
            output_key: self.output_key,
        }
    }

    pub fn new(raw: D, input_key: K, output_key: K) -> Self {
        ProtectedAssets {
            data: Data::new(raw),
            input_key: Key::new(input_key),
            output_key: Key::new(output_key),
        }
    }
}

impl<D, K> ProtectedAssets<Decrypted, Input, D, K>
where
    D: ContiguousMemory + EncDec<K>,
{
    pub fn invoke(self, fun: &dyn Fn(D) -> D) -> ProtectedAssets<Decrypted, Output, D, K> {
        ProtectedAssets {
            data: self.data.invoke(fun),
            input_key: self.input_key,
            output_key: self.output_key,
        }
    }
}

impl<D, K> ProtectedAssets<Decrypted, Output, D, K>
where
    D: ContiguousMemory + EncDec<K>,
    K: Default,
{
    pub fn encrypt(self) -> ProtectedAssets<Encrypted, Output, D, K> {
        ProtectedAssets {
            data: self.data.encrypt(&self.output_key),
            input_key: self.input_key,
            output_key: self.output_key.zeroize(),
        }
    }
}

impl<D, K> ProtectedAssets<Encrypted, Output, D, K>
where
    D: ContiguousMemory + EncDec<K>,
{
    pub fn take(self) -> D {
        self.data.raw
    }
}
