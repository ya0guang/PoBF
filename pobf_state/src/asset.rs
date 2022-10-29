#![forbid(unsafe_code)]

use crate::*;
use core::marker::PhantomData;
use prusti_contracts::*;
#[cfg(feature = "sgx")]
use sgx_types::error::SgxResult as Result;
use zeroize::Zeroize;
#[cfg(not(feature = "sgx"))]
type Result<T> = core::result::Result<T, ()>;

pub const BUFFER_SIZE: usize = 1024;
pub const SEALED_DATA_SIZE: usize = 16;

// the states of data is in:
// [Input, Output] * [Encrypt, Decrypt]
pub struct Input;
pub struct Output;

pub struct Encrypted;
pub struct Decrypted;

pub trait IOState {
    /// This function is not used in any normal code.
    /// In prusti contracts, we need to check if the resulting type matches the given type,
    /// which is answered by this pure function.
    #[pure]
    fn is_input(&self) -> bool;
}

#[refine_trait_spec]
impl IOState for Input {
    #[pure]
    #[ensures(result == true)]
    fn is_input(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl IOState for Output {
    #[pure]
    #[ensures(result == false)]
    fn is_input(&self) -> bool {
        false
    }
}

pub trait EncryptionState {
    /// This function is not used in any normal code.
    /// In prusti contracts, we need to check if the resulting type matches the given type,
    /// which is answered by this pure function.
    #[pure]
    fn is_encrypted(&self) -> bool;
}

#[refine_trait_spec]
impl EncryptionState for Encrypted {
    #[pure]
    #[ensures(result == true)]
    fn is_encrypted(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl EncryptionState for Decrypted {
    #[pure]
    #[ensures(result == false)]
    fn is_encrypted(&self) -> bool {
        false
    }
}

// the state of key is in:
// [Sealed, Invalid]
pub struct Sealed; // the key is not yet used
pub struct Invalid; // the key has been used (only once)

pub trait KeyState {
    #[pure]
    fn is_sealed(&self) -> bool;
}

#[refine_trait_spec]
impl KeyState for Sealed {
    #[pure]
    #[ensures(result == true)]
    fn is_sealed(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl KeyState for Invalid {
    #[pure]
    #[ensures(result == false)]
    fn is_sealed(&self) -> bool {
        false
    }
}

/// The allowed states of the input key depend on the state of Data
pub trait InputKeyState {
    type KeyState;

    #[pure]
    fn is_sealed(&self) -> bool;
}

#[refine_trait_spec]
impl<D, K> InputKeyState for Data<Encrypted, Input, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Sealed;

    #[pure]
    #[ensures(result == true)]
    fn is_sealed(&self) -> bool {
        true
    }
}
#[refine_trait_spec]
impl<D, K> InputKeyState for Data<Decrypted, Input, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Invalid;

    #[pure]
    #[ensures(result == false)]
    fn is_sealed(&self) -> bool {
        false
    }
}

#[refine_trait_spec]
impl<D, K> InputKeyState for Data<Decrypted, Output, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Invalid;

    #[pure]
    #[ensures(result == false)]
    fn is_sealed(&self) -> bool {
        false
    }
}

#[refine_trait_spec]
impl<D, K> InputKeyState for Data<Encrypted, Output, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Invalid;

    #[pure]
    #[ensures(result == false)]
    fn is_sealed(&self) -> bool {
        false
    }
}

/// The allowed states of the output key depend on the state of Data
pub trait OutputKeyState {
    type KeyState;

    #[pure]
    fn is_sealed(&self) -> bool;
}

#[refine_trait_spec]
impl<D, K> OutputKeyState for Data<Encrypted, Input, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Sealed;

    #[pure]
    #[ensures(result == true)]
    fn is_sealed(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl<D, K> OutputKeyState for Data<Decrypted, Input, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Sealed;

    #[pure]
    #[ensures(result == true)]
    fn is_sealed(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl<D, K> OutputKeyState for Data<Decrypted, Output, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Sealed;

    #[pure]
    #[ensures(result == true)]
    fn is_sealed(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl<D, K> OutputKeyState for Data<Encrypted, Output, D, K>
where
    D: EncDec<K>,
{
    type KeyState = Invalid;

    #[pure]
    #[ensures(result == false)]
    fn is_sealed(&self) -> bool {
        false
    }
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
    /// Prusti contract checks if encryption state and io state match the given types.
    #[ensures((&result._encryption_state).is_encrypted())]
    #[ensures((&result._io_state).is_input())]
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
    K: Default + Zeroize,
{
    #[trusted]
    #[requires((&key)._key_state.is_sealed())]
    #[requires(old(&self)._encryption_state.is_encrypted())]
    #[requires(old(&self)._io_state.is_input())]
    #[ensures(
      if let Ok(x) = result.as_ref() {
        !x._encryption_state.is_encrypted() && x._io_state.is_input()
      } else {
        true
      }
    )]
    pub fn decrypt(self, key: &Key<K, Sealed>) -> Result<Data<Decrypted, Input, D, K>> {
        // Moved. No need to zeroize it.
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
    #[trusted]
    #[requires(!old(&self)._encryption_state.is_encrypted())]
    #[requires(old(&self)._io_state.is_input())]
    #[ensures(
      if let Ok(x) = result.as_ref() {
        !x._encryption_state.is_encrypted() && !x._io_state.is_input()
      } else {
        true
      }
    )]
    pub fn invoke(self, fun: &dyn Fn(D) -> D) -> Result<Data<Decrypted, Output, D, K>> {
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
    K: Default + Zeroize,
{
    #[trusted]
    #[requires((&key)._key_state.is_sealed())]
    #[requires(!old(&self)._encryption_state.is_encrypted())]
    #[requires(!old(&self)._io_state.is_input())]
    #[ensures(
      if let Ok(x) = result.as_ref() {
        x._encryption_state.is_encrypted() && !x._io_state.is_input()
      } else {
        true
      }
    )]
    pub fn encrypt(self, key: &Key<K, Sealed>) -> Result<Data<Encrypted, Output, D, K>> {
        // TODO: zeroize previous raw data.
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

impl<K> Zeroize for Key<K, Sealed>
where
    K: Default + Zeroize,
{
    fn zeroize(&mut self) {
        self.raw.zeroize();
    }
}

impl<K> Key<K, Sealed>
where
    K: Default + Zeroize,
{
    #[ensures((&result._key_state).is_sealed())]
    pub fn new(raw: K) -> Key<K, Sealed> {
        Key {
            raw,
            _key_state: Sealed,
        }
    }

    #[trusted]
    fn raw_ref(&self) -> &K {
        &self.raw
    }

    // Zone allocator will zerorize(consume) self!
    #[ensures(!(&result._key_state).is_sealed())]
    pub fn _zeroize(&mut self) -> Key<K, Invalid> {
        self.zeroize();

        Key {
            raw: K::default(),
            _key_state: Invalid,
        }
    }
}

// Main definition for Typestate.
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
    K: Default + Zeroize,
{
    #[trusted]
    #[requires(old(&self).data._encryption_state.is_encrypted())]
    #[requires(old(&self).input_key._key_state.is_sealed())]
    #[requires(old(&self).output_key._key_state.is_sealed())]
    #[ensures(
      if let Ok(x) = result.as_ref() {
        !x.input_key._key_state.is_sealed() && x.output_key._key_state.is_sealed() &&
        !x.data._encryption_state.is_encrypted()
      } else {
        true
      }
    )]
    pub fn decrypt(mut self) -> Result<ProtectedAssets<Decrypted, Input, D, K>> {
        let data = self.data.decrypt(&self.input_key)?;

        Ok(ProtectedAssets {
            data,
            input_key: self.input_key._zeroize(),
            output_key: self.output_key,
        })
    }

    #[trusted]
    #[ensures((&result).data._encryption_state.is_encrypted())]
    #[ensures((&result).input_key._key_state.is_sealed())]
    #[ensures((&result).output_key._key_state.is_sealed())]
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
    #[trusted]
    #[requires(!old(&self).data._encryption_state.is_encrypted())]
    #[requires(!old(&self).input_key._key_state.is_sealed())]
    #[requires(old(&self).output_key._key_state.is_sealed())]
    #[ensures(
      if let Ok(x) = result.as_ref() {
        !x.input_key._key_state.is_sealed() && x.output_key._key_state.is_sealed() &&
        !x.data._encryption_state.is_encrypted()
      } else {
        true
      }
    )]
    pub fn invoke(self, fun: &dyn Fn(D) -> D) -> Result<ProtectedAssets<Decrypted, Output, D, K>> {
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
    K: Default + Zeroize,
{
    #[trusted]
    #[requires(!old(&self).data._encryption_state.is_encrypted())]
    #[requires(!old(&self).input_key._key_state.is_sealed())]
    #[requires(old(&self).output_key._key_state.is_sealed())]
    #[ensures(
      if let Ok(x) = result.as_ref() {
        !x.input_key._key_state.is_sealed() && !x.output_key._key_state.is_sealed() &&
        x.data._encryption_state.is_encrypted()
      } else {
        true
      }
    )]
    pub fn encrypt(mut self) -> Result<ProtectedAssets<Encrypted, Output, D, K>> {
        let data = self.data.encrypt(&self.output_key)?;

        Ok(ProtectedAssets {
            data,
            input_key: self.input_key,
            output_key: self.output_key._zeroize(),
        })
    }
}

impl<D, K> ProtectedAssets<Encrypted, Output, D, K>
where
    D: EncDec<K>,
{
    #[trusted]
    pub fn take(self) -> D {
        self.data.raw
    }
}
