#![forbid(unsafe_code)]

// pub mod state;
pub mod vecaes;

// pub use state::*;
pub use vecaes::*;

use sgx_types::error::SgxResult;
use core::marker::PhantomData;

pub const BUFFER_SIZE: usize = 1024;
pub const SEALED_DATA_SIZE: usize = 16;

// the states of data is in:
// [Input, Output] * [Encrypt, Decrypt]
pub struct Input;
pub struct Output;

pub struct Encrypted;
pub struct Decrypted;

pub trait IOState {}
impl IOState for Input {}
impl IOState for Output {}

pub trait EncryptionState {}
impl EncryptionState for Encrypted {}
impl EncryptionState for Decrypted {}

// the state of key is in:
// [Sealed, Invalid]
pub struct Sealed; // the key is not yet used
pub struct Invalid; // the key has been used (only once)

/// The allowed states of the input key depend on the state of Data
pub trait InputKeyState {
    type KeyState;
}

impl<D, K> InputKeyState for Data<Encrypted, Input, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Sealed;
}

impl<D, K> InputKeyState for Data<Decrypted, Input, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Invalid;
}

impl<D, K> InputKeyState for Data<Decrypted, Output, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Invalid;
}

impl<D, K> InputKeyState for Data<Encrypted, Output, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Invalid;
}

/// The allowed states of the output key depend on the state of Data
pub trait OutputKeyState {
    type KeyState;
}

impl<D, K> OutputKeyState for Data<Encrypted, Input, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Sealed;
}

impl<D, K> OutputKeyState for Data<Decrypted, Input, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Sealed;
}

impl<D, K> OutputKeyState for Data<Decrypted, Output, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Sealed;
}

impl<D, K> OutputKeyState for Data<Encrypted, Output, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Invalid;
}

#[allow(private_in_public)]
trait Decryption<K>
where
    Self: Sized,
{
    fn decrypt(self, key: &K) -> SgxResult<Self>;
}

#[allow(private_in_public)]
trait Encryption<K>
where
    Self: Sized,
{
    fn encrypt(self, key: &K) -> SgxResult<Self>;
}

pub trait EncDec<K>
where
    Self: Sized + Decryption<K> + Encryption<K>,
{
}

pub struct Data<S, T, D, K>
where
    S: EncryptionState,
    T: IOState,
    D: EncDec<K>,
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
    D: EncDec<K>,
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
    D: EncDec<K>,
    K: Default,
{
    pub fn decrypt(self, key: &Key<K, Sealed>) -> SgxResult<Data<Decrypted, Input, D, K>> {
        let raw = self.raw.decrypt(key.raw_ref())?;

        Ok(Data {
            raw,
            _encryption_state: Decrypted,
            _io_state: Input,
            _key_type: PhantomData,
        })
    }
}

impl<D, K> Data<Decrypted, Input, D, K>
where
    D: EncDec<K>,
{
    pub fn invoke(self, fun: &dyn Fn(D) -> D) -> SgxResult<Data<Decrypted, Output, D, K>> {
        let raw = fun(self.raw);
        Ok(Data {
            raw,
            _encryption_state: Decrypted,
            _io_state: Output,
            _key_type: PhantomData,
        })
    }
}

impl<D, K> Data<Decrypted, Output, D, K>
where
    D: EncDec<K>,
    K: Default,
{
    pub fn encrypt(self, key: &Key<K, Sealed>) -> SgxResult<Data<Encrypted, Output, D, K>> {
        let raw = self.raw.encrypt(key.raw_ref())?;
        Ok(Data {
            raw,
            _encryption_state: Encrypted,
            _io_state: Output,
            _key_type: PhantomData,
        })
    }
}

pub struct Key<K, S> {
    pub raw: K,
    // Sealed / Invalid
    _key_state: S,
}

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

    // zone allocator will zerorize(consume) self!
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
    D: EncDec<K>,
{
    data: Data<S, T, D, K>,
    input_key: Key<K, <Data<S, T, D, K> as InputKeyState>::KeyState>,
    output_key: Key<K, <Data<S, T, D, K> as OutputKeyState>::KeyState>,
}

impl<D, K> ProtectedAssets<Encrypted, Input, D, K>
where
    D: EncDec<K>,
    K: Default,
{
    pub fn decrypt(self) -> SgxResult<ProtectedAssets<Decrypted, Input, D, K>> {
        let data = self.data.decrypt(&self.input_key)?;
        Ok(ProtectedAssets {
            data,
            input_key: self.input_key.zeroize(),
            output_key: self.output_key,
        })
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
    D: EncDec<K>,
{
    pub fn invoke(
        self,
        fun: &dyn Fn(D) -> D,
    ) -> SgxResult<ProtectedAssets<Decrypted, Output, D, K>> {
        let data = self.data.invoke(fun)?;

        Ok(ProtectedAssets {
            data,
            input_key: self.input_key,
            output_key: self.output_key,
        })
    }
}

impl<D, K> ProtectedAssets<Decrypted, Output, D, K>
where
    D: EncDec<K>,
    K: Default,
{
    pub fn encrypt(self) -> SgxResult<ProtectedAssets<Encrypted, Output, D, K>> {
        let data = self.data.encrypt(&self.output_key)?;

        Ok(ProtectedAssets {
            data,
            input_key: self.input_key,
            output_key: self.output_key.zeroize(),
        })
    }
}

impl<D, K> ProtectedAssets<Encrypted, Output, D, K>
where
    D: EncDec<K>,
{
    pub fn take(self) -> D {
        self.data.raw
    }
}
