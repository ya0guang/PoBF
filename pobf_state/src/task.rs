#![forbid(unsafe_code)]
#![allow(unused_imports)]

use crate::*;
use core::marker::PhantomData;
use prusti_contracts::*;
use zeroize::Zeroize;

#[cfg(feature = "prusti")]
use crate::bogus::*;
#[cfg(feature = "sgx")]
use sgx_types::error::SgxResult as Result;
#[cfg(not(feature = "sgx"))]
type Result<T> = core::result::Result<T, ()>;

pub trait TaskState {
    #[pure]
    fn is_initialized(&self) -> bool {
        false
    }

    #[pure]
    fn is_channel_established(&self) -> bool {
        false
    }

    #[pure]
    fn is_result_encrypted(&self) -> bool {
        false
    }

    #[pure]
    fn is_result_decrypted(&self) -> bool {
        false
    }

    #[pure]
    fn is_data_decrypted(&self) -> bool {
        false
    }

    #[pure]
    fn is_data_received(&self) -> bool {
        false
    }

    #[pure]
    fn is_finished(&self) -> bool {
        false
    }
}
pub trait DataState {}
pub trait KeyState {
    #[pure]
    fn is_invalid_key(&self) -> bool {
        false
    }

    #[pure]
    fn is_uninitialized(&self) -> bool {
        false
    }

    #[pure]
    fn is_allowed_once(&self) -> bool {
        false
    }

    #[pure]
    fn is_allowed_twice(&self) -> bool {
        false
    }
}

// Common States for Data and Key
pub struct Uninitialized;
impl DataState for Uninitialized {}

#[refine_trait_spec]
impl KeyState for Uninitialized {
    #[pure]
    #[ensures(result == true)]
    fn is_uninitialized(&self) -> bool {
        true
    }
}

pub struct Invalid;
impl DataState for Invalid {}

#[refine_trait_spec]
impl KeyState for Invalid {
    #[pure]
    #[ensures(result == true)]
    fn is_invalid_key(&self) -> bool {
        true
    }
}

// Task States
pub struct Initialized;
#[refine_trait_spec]
impl TaskState for Initialized {
    #[pure]
    #[ensures(result == true)]
    fn is_initialized(&self) -> bool {
        true
    }
}
pub struct ChannelEstablished;
#[refine_trait_spec]
impl TaskState for ChannelEstablished {
    #[pure]
    #[ensures(result == true)]
    fn is_channel_established(&self) -> bool {
        true
    }
}
pub struct DataReceived;
#[refine_trait_spec]
impl TaskState for DataReceived {
    #[pure]
    #[ensures(result == true)]
    fn is_data_received(&self) -> bool {
        true
    }
}
//These two states are transient and not permitted to be used by the users!
struct DataDecrypted;
#[refine_trait_spec]
impl TaskState for DataDecrypted {
    #[pure]
    #[ensures(result == true)]
    fn is_data_decrypted(&self) -> bool {
        true
    }
}
struct ResultDecrypted;
#[refine_trait_spec]
impl TaskState for ResultDecrypted {
    #[pure]
    #[ensures(result == true)]
    fn is_result_decrypted(&self) -> bool {
        true
    }
}
pub struct ResultEncrypted;
#[refine_trait_spec]
impl TaskState for ResultEncrypted {
    #[pure]
    #[ensures(result == true)]
    fn is_result_encrypted(&self) -> bool {
        true
    }
}
pub struct Finished;
#[refine_trait_spec]
impl TaskState for Finished {
    #[pure]
    #[ensures(result == true)]
    fn is_finished(&self) -> bool {
        true
    }
}

// Data States

pub struct EncryptedInput;
impl DataState for EncryptedInput {}
pub struct DecryptedInput;

impl DataState for DecryptedInput {}
pub struct DecryptedOutput;
impl DataState for DecryptedOutput {}
pub struct EncryptedOutput;
impl DataState for EncryptedOutput {}

pub trait ConfidentialDataState {
    type State;

    #[pure]
    fn is_uninitialized(&self) -> bool {
        false
    }

    #[pure]
    fn is_invalid_data(&self) -> bool {
        false
    }

    #[pure]
    fn is_encrypted_input(&self) -> bool {
        false
    }

    #[pure]
    fn is_encrypted_output(&self) -> bool {
        false
    }

    #[pure]
    fn is_decrypted_input(&self) -> bool {
        false
    }

    #[pure]
    fn is_decrypted_output(&self) -> bool {
        false
    }
}

#[refine_trait_spec]
impl ConfidentialDataState for Initialized {
    type State = Uninitialized;

    #[pure]
    #[ensures(result == true)]
    fn is_uninitialized(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl ConfidentialDataState for ChannelEstablished {
    type State = Uninitialized;

    #[pure]
    #[ensures(result == true)]
    fn is_uninitialized(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl ConfidentialDataState for DataReceived {
    type State = EncryptedInput;

    #[pure]
    #[ensures(result == true)]
    fn is_encrypted_input(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl ConfidentialDataState for DataDecrypted {
    type State = DecryptedInput;

    #[pure]
    #[ensures(result == true)]
    fn is_decrypted_input(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl ConfidentialDataState for ResultDecrypted {
    type State = DecryptedOutput;

    #[pure]
    #[ensures(result == true)]
    fn is_decrypted_output(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl ConfidentialDataState for ResultEncrypted {
    type State = EncryptedOutput;

    #[pure]
    #[ensures(result == true)]
    fn is_encrypted_input(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl ConfidentialDataState for Finished {
    type State = Invalid;

    #[pure]
    #[ensures(result == true)]
    fn is_invalid_data(&self) -> bool {
        true
    }
}

pub trait SessionKeyState {
    type State;

    #[pure]
    fn is_invalid_key(&self) -> bool {
        false
    }

    #[pure]
    fn is_uninitialized(&self) -> bool {
        false
    }

    #[pure]
    fn is_allowed_once(&self) -> bool {
        false
    }

    #[pure]
    fn is_allowed_twice(&self) -> bool {
        false
    }
}

// Key States
pub struct AllowedTwice;

#[refine_trait_spec]
impl KeyState for AllowedTwice {
    #[pure]
    #[ensures(result == true)]
    fn is_allowed_twice(&self) -> bool {
        true
    }
}
// This state is transient and not permitted to be used by the users!
struct AllowedOnce;

#[refine_trait_spec]
impl KeyState for AllowedOnce {
    #[pure]
    #[ensures(result == true)]
    fn is_allowed_once(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl SessionKeyState for Initialized {
    type State = Uninitialized;

    #[pure]
    #[ensures(result == true)]
    fn is_uninitialized(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl SessionKeyState for ChannelEstablished {
    type State = AllowedTwice;

    #[pure]
    #[ensures(result == true)]
    fn is_allowed_twice(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl SessionKeyState for DataReceived {
    type State = AllowedTwice;

    #[pure]
    #[ensures(result == true)]
    fn is_allowed_twice(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl SessionKeyState for DataDecrypted {
    type State = AllowedOnce;

    #[pure]
    #[ensures(result == true)]
    fn is_allowed_once(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl SessionKeyState for ResultDecrypted {
    type State = AllowedOnce;

    #[pure]
    #[ensures(result == true)]
    fn is_allowed_once(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl SessionKeyState for ResultEncrypted {
    type State = Invalid;

    #[pure]
    #[ensures(result == true)]
    fn is_invalid_key(&self) -> bool {
        true
    }
}

#[refine_trait_spec]
impl SessionKeyState for Finished {
    type State = Invalid;

    #[pure]
    #[ensures(result == true)]
    fn is_invalid_key(&self) -> bool {
        true
    }
}

pub struct Key<K, S>
where
    S: KeyState,
    K: Zeroize + Default,
{
    pub raw: K,
    // Sealed / Invalid
    pub _state: S,
}

impl<K> Key<K, AllowedTwice>
where
    K: Zeroize + Default,
{
    #[ensures((&result)._state.is_allowed_twice())]
    fn from(raw: K) -> Self {
        Key {
            raw,
            _state: AllowedTwice,
        }
    }

    #[requires((&self)._state.is_allowed_twice())]
    #[ensures((&result)._state.is_allowed_once())]
    fn once(self) -> Key<K, AllowedOnce> {
        Key {
            raw: self.raw,
            _state: AllowedOnce,
        }
    }
}

#[refine_trait_spec]
impl<K> Zeroize for Key<K, AllowedOnce>
where
    K: Default + Zeroize,
{
    #[requires((&self)._state.is_allowed_once())]
    #[ensures((&self)._state.is_allowed_once())]
    fn zeroize(&mut self) {
        self.raw.zeroize();
    }
}

impl<K> Key<K, AllowedOnce>
where
    K: Zeroize + Default,
{
    #[requires((&self)._state.is_allowed_once())]
    #[ensures((&result)._state.is_invalid_key())]
    fn once(mut self) -> Key<K, Invalid> {
        self.raw.zeroize();
        Key {
            raw: K::default(),
            _state: Invalid,
        }
    }
}

pub struct Data<S, D, K>
where
    S: DataState,
    D: EncDec<K>,
{
    // inner data
    raw: D,
    _state: S,
    _key_type: PhantomData<K>,
}

pub struct ComputingTaskTemplate<S>
where
    S: TaskState,
{
    _state: S,
}

impl ComputingTaskTemplate<Initialized> {
    #[ensures((&result)._state.is_initialized())]
    pub fn new() -> Self {
        Self {
            _state: Initialized,
        }
    }
}

pub struct ComputingTaskSession<S, K>
where
    S: TaskState + SessionKeyState,
    K: Zeroize + Default,
    <S as SessionKeyState>::State: KeyState,
{
    pub key: Key<K, <S as SessionKeyState>::State>,
    _state: S,
}

impl<K> ComputingTaskSession<ChannelEstablished, K>
where
    K: Zeroize + Default,
{
    #[cfg(not(feature = "prusti"))]
    pub fn establish_channel<F: FnMut() -> K>(
        _template: ComputingTaskTemplate<Initialized>,
        mut attestation_callback: F,
    ) -> Self {
        let key = attestation_callback();

        ComputingTaskSession {
            key: Key::from(key),
            _state: ChannelEstablished,
        }
    }

    #[cfg(feature = "prusti")]
    #[trusted]
    #[requires((&_template)._state.is_initialized())]
    #[ensures((&result)._state.is_channel_established())]
    #[ensures((&result)._state.is_allowed_twice())]
    pub fn establish_channel(_template: ComputingTaskTemplate<Initialized>) -> Self {
        ComputingTaskSession {
            key: Key::from(K::default()),
            _state: ChannelEstablished,
        }
    }
}

pub struct ComputingTask<S, K, D>
where
    S: TaskState + ConfidentialDataState + SessionKeyState,
    K: Zeroize + Default,
    D: EncDec<K>,
    <S as ConfidentialDataState>::State: DataState,
    <S as SessionKeyState>::State: KeyState,
{
    data: Data<<S as ConfidentialDataState>::State, D, K>,
    key: Key<K, <S as SessionKeyState>::State>,
    _state: S,
}

/// Bypass the loan checking of Prusti by specifying a specialized version of ComputingTask.
#[cfg(feature = "prusti")]
impl ComputingTask<DataReceived, AES128Key, VecAESData>
where
    VecAESData: EncDec<AES128Key>,
    AES128Key: Zeroize + Default,
{
    #[trusted]
    #[requires((&session)._state.is_channel_established())]
    #[requires((&session)._state.is_allowed_twice())]
    #[ensures((&result)._state.is_data_received())]
    #[ensures((&result)._state.is_encrypted_input())]
    #[ensures((&result)._state.is_allowed_twice())]
    pub fn receive_data(session: ComputingTaskSession<ChannelEstablished, AES128Key>) -> Self {
        let data = bogus::VecAESData::from(alloc::vec![0u8; 0]);
        ComputingTask {
            key: session.key,
            data: Data {
                raw: data,
                _state: EncryptedInput,
                _key_type: PhantomData,
            },
            _state: DataReceived,
        }
    }
}

#[cfg(feature = "prusti")]
impl ComputingTask<DataReceived, AES128Key, VecAESData> {
    /// The function now verifies.
    /// It involves several complex steps.
    #[requires((&self)._state.is_allowed_twice())]
    #[requires((&self)._state.is_data_received())]
    #[requires((&self)._state.is_encrypted_input())]
    #[ensures((&result)._state.is_result_encrypted())]
    #[ensures((&result)._state.is_encrypted_output())]
    #[ensures((&result)._state.is_allowed_once())]
    pub fn compute(self) -> ComputingTask<ResultEncrypted, AES128Key, VecAESData> {
        let decrypted = self.decrypt_data();
        let result = decrypted.do_compute();
        result.encrypt_result()
    }
}

impl<K, D> ComputingTask<DataReceived, K, D>
where
    K: Zeroize + Default,
    D: EncDec<K>,
{
    #[cfg(not(feature = "prusti"))]
    pub fn receive_data<F: FnMut() -> D>(
        session: ComputingTaskSession<ChannelEstablished, K>,
        mut receive_callback: F,
    ) -> Self {
        let data = receive_callback();
        ComputingTask {
            key: session.key,
            data: Data {
                raw: data,
                _state: EncryptedInput,
                _key_type: PhantomData,
            },
            _state: DataReceived,
        }
    }

    #[cfg(not(feature = "prusti"))]
    fn decrypt_data(self) -> Result<ComputingTask<DataDecrypted, K, D>> {
        let data = self.data.raw.decrypt(&self.key.raw)?;
        Ok(ComputingTask {
            key: self.key.once(),
            data: Data {
                raw: data,
                _state: DecryptedInput,
                _key_type: PhantomData,
            },
            _state: DataDecrypted,
        })
    }

    #[cfg(not(feature = "prusti"))]
    pub fn compute(
        self,
        compute_callback: &dyn Fn(D) -> D,
    ) -> ComputingTask<ResultEncrypted, K, D> {
        let decrypted = self.decrypt_data().unwrap();
        let result = decrypted.do_compute(compute_callback).unwrap();
        result.encrypt_result().unwrap()
    }

    #[cfg(feature = "prusti")]
    #[trusted]
    #[requires((&self)._state.is_allowed_twice())]
    #[requires((&self)._state.is_data_received())]
    #[requires((&self)._state.is_encrypted_input())]
    #[ensures((&result)._state.is_data_decrypted())]
    #[ensures((&result)._state.is_decrypted_input())]
    #[ensures((&result)._state.is_allowed_once())]
    fn decrypt_data(self) -> ComputingTask<DataDecrypted, K, D> {
        let data = self.data.raw.decrypt(&self.key.raw).unwrap();
        ComputingTask {
            key: self.key.once(),
            data: Data {
                raw: data,
                _state: DecryptedInput,
                _key_type: PhantomData,
            },
            _state: DataDecrypted,
        }
    }
}

impl<K, D> ComputingTask<ResultEncrypted, K, D>
where
    K: Zeroize + Default,
    D: EncDec<K>,
{
    #[trusted]
    #[requires((&self)._state.is_result_encrypted())]
    #[requires((&self)._state.is_encrypted_output())]
    #[requires((&self)._state.is_invalid_key())]
    pub fn take_result(self) -> D {
        self.data.raw
    }
}

#[cfg(feature = "prusti")]
impl ComputingTask<DataDecrypted, AES128Key, VecAESData> {
    #[trusted]
    #[requires((&self)._state.is_allowed_once())]
    #[requires((&self)._state.is_decrypted_input())]
    #[requires((&self)._state.is_data_decrypted())]
    #[ensures((&result)._state.is_result_decrypted())]
    #[ensures((&result)._state.is_decrypted_output())]
    #[ensures((&result)._state.is_allowed_once())]
    pub fn do_compute(self) -> ComputingTask<ResultDecrypted, AES128Key, VecAESData> {
        ComputingTask {
            key: self.key,
            data: Data {
                raw: self.data.raw,
                _state: DecryptedOutput,
                _key_type: PhantomData,
            },
            _state: ResultDecrypted,
        }
    }
}

impl<K, D> ComputingTask<DataDecrypted, K, D>
where
    K: Zeroize + Default,
    D: EncDec<K>,
{
    #[cfg(not(feature = "prusti"))]
    fn do_compute(self, task: &dyn Fn(D) -> D) -> Result<ComputingTask<ResultDecrypted, K, D>> {
        Ok(ComputingTask {
            key: self.key,
            data: Data {
                raw: task(self.data.raw),
                _state: DecryptedOutput,
                _key_type: PhantomData,
            },
            _state: ResultDecrypted,
        })
    }
}

impl<K, D> ComputingTask<ResultDecrypted, K, D>
where
    K: Zeroize + Default,
    D: EncDec<K>,
{
    #[cfg(not(feature = "prusti"))]
    fn encrypt_result(self) -> Result<ComputingTask<ResultEncrypted, K, D>> {
        let data = self.data.raw.encrypt(&self.key.raw)?;

        Ok(ComputingTask {
            key: self.key.once(),
            data: Data {
                raw: data,
                _state: EncryptedOutput,
                _key_type: PhantomData,
            },
            _state: ResultEncrypted,
        })
    }

    #[cfg(feature = "prusti")]
    #[trusted]
    #[requires((&self)._state.is_allowed_once())]
    #[requires((&self)._state.is_decrypted_output())]
    #[requires((&self)._state.is_result_decrypted())]
    #[ensures((&result)._state.is_result_encrypted())]
    #[ensures((&result)._state.is_encrypted_output())]
    #[ensures((&result)._state.is_invalid_key())]
    fn encrypt_result(self) -> ComputingTask<ResultEncrypted, K, D> {
        let data = self.data.raw.encrypt(&self.key.raw).unwrap();

        ComputingTask {
            key: self.key.once(),
            data: Data {
                raw: data,
                _state: EncryptedOutput,
                _key_type: PhantomData,
            },
            _state: ResultEncrypted,
        }
    }
}
