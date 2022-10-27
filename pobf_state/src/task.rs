#![forbid(unsafe_code)]

use crate::bogus::*;
use crate::*;
use core::marker::PhantomData;
use prusti_contracts::*;
#[cfg(feature = "sgx")]
use sgx_types::error::SgxResult as Result;
use zeroize::Zeroize;
#[cfg(not(feature = "sgx"))]
type Result<T> = core::result::Result<T, ()>;

pub trait TaskState {
    #[pure]
    fn is_initialized(&self) -> bool;

    #[pure]
    fn is_channel_established(&self) -> bool;

    #[pure]
    fn is_result_encrypted(&self) -> bool;

    #[pure]
    fn is_result_decrypted(&self) -> bool;

    #[pure]
    fn is_data_decrypted(&self) -> bool;

    #[pure]
    fn is_data_received(&self) -> bool;

    #[pure]
    fn is_finished(&self) -> bool;
}
pub trait DataState {}
pub trait KeyState {
    #[pure]
    fn is_uninitialized(&self) -> bool;

    #[pure]
    fn is_invalid(&self) -> bool;

    #[pure]
    fn is_allowed_twice(&self) -> bool;

    #[pure]
    fn is_allowed_once(&self) -> bool;
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

    #[pure]
    #[ensures(result == false)]
    fn is_invalid(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_allowed_twice(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_allowed_once(&self) -> bool {
        false
    }
}
pub struct Invalid;
impl DataState for Invalid {}

#[refine_trait_spec]
impl KeyState for Invalid {
    #[pure]
    #[ensures(result == false)]
    fn is_uninitialized(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == true)]
    fn is_invalid(&self) -> bool {
        true
    }

    #[pure]
    #[ensures(result == false)]
    fn is_allowed_twice(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_allowed_once(&self) -> bool {
        false
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

    #[pure]
    #[ensures(result == false)]
    fn is_channel_established(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_result_encrypted(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_data_received(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_finished(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_result_decrypted(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_data_decrypted(&self) -> bool {
        false
    }
}
pub struct ChannelEstablished;
#[refine_trait_spec]
impl TaskState for ChannelEstablished {
    #[pure]
    #[ensures(result == false)]
    fn is_initialized(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == true)]
    fn is_channel_established(&self) -> bool {
        true
    }

    #[pure]
    #[ensures(result == false)]
    fn is_result_encrypted(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_data_received(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_finished(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_result_decrypted(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_data_decrypted(&self) -> bool {
        false
    }
}
pub struct DataReceived;
#[refine_trait_spec]
impl TaskState for DataReceived {
    #[pure]
    #[ensures(result == false)]
    fn is_initialized(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_channel_established(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_result_encrypted(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == true)]
    fn is_data_received(&self) -> bool {
        true
    }

    #[pure]
    #[ensures(result == false)]
    fn is_finished(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_result_decrypted(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_data_decrypted(&self) -> bool {
        false
    }
}
//These two states are transient and not permitted to be used by the users!
struct DataDecrypted;
#[refine_trait_spec]
impl TaskState for DataDecrypted {
    #[pure]
    #[ensures(result == false)]
    fn is_initialized(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_channel_established(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_result_encrypted(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_data_received(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_finished(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_result_decrypted(&self) -> bool {
        false
    }

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
    #[ensures(result == false)]
    fn is_initialized(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_channel_established(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_result_encrypted(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_data_received(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_finished(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == true)]
    fn is_result_decrypted(&self) -> bool {
        true
    }

    #[pure]
    #[ensures(result == false)]
    fn is_data_decrypted(&self) -> bool {
        false
    }
}
pub struct ResultEncrypted;
#[refine_trait_spec]
impl TaskState for ResultEncrypted {
    #[pure]
    #[ensures(result == false)]
    fn is_initialized(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_channel_established(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == true)]
    fn is_result_encrypted(&self) -> bool {
        true
    }

    #[pure]
    #[ensures(result == false)]
    fn is_data_received(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_finished(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_result_decrypted(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_data_decrypted(&self) -> bool {
        false
    }
}
pub struct Finished;
#[refine_trait_spec]
impl TaskState for Finished {
    #[pure]
    #[ensures(result == false)]
    fn is_initialized(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_channel_established(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_result_encrypted(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_data_received(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == true)]
    fn is_finished(&self) -> bool {
        true
    }

    #[pure]
    #[ensures(result == false)]
    fn is_result_decrypted(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_data_decrypted(&self) -> bool {
        false
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
}
impl ConfidentialDataState for Initialized {
    type State = Uninitialized;
}

impl ConfidentialDataState for ChannelEstablished {
    type State = Uninitialized;
}

impl ConfidentialDataState for DataReceived {
    type State = EncryptedInput;
}

impl ConfidentialDataState for DataDecrypted {
    type State = DecryptedInput;
}

impl ConfidentialDataState for ResultDecrypted {
    type State = DecryptedOutput;
}

impl ConfidentialDataState for ResultEncrypted {
    type State = EncryptedOutput;
}

impl ConfidentialDataState for Finished {
    type State = Invalid;
}

pub trait SessionKeyState {
    type State;
}

// Key States
pub struct AllowedTwice;
#[refine_trait_spec]
impl KeyState for AllowedTwice {
    #[pure]
    #[ensures(result == false)]
    fn is_uninitialized(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_invalid(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == true)]
    fn is_allowed_twice(&self) -> bool {
        true
    }

    #[pure]
    #[ensures(result == false)]
    fn is_allowed_once(&self) -> bool {
        false
    }
}
// This state is transient and not permitted to be used by the users!
struct AllowedOnce;
#[refine_trait_spec]
impl KeyState for AllowedOnce {
    #[pure]
    #[ensures(result == false)]
    fn is_uninitialized(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_invalid(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == false)]
    fn is_allowed_twice(&self) -> bool {
        false
    }

    #[pure]
    #[ensures(result == true)]
    fn is_allowed_once(&self) -> bool {
        true
    }
}

impl SessionKeyState for Initialized {
    type State = Uninitialized;
}

impl SessionKeyState for ChannelEstablished {
    type State = AllowedTwice;
}

impl SessionKeyState for DataReceived {
    type State = AllowedTwice;
}

impl SessionKeyState for DataDecrypted {
    type State = AllowedOnce;
}

impl SessionKeyState for ResultDecrypted {
    type State = AllowedOnce;
}

impl SessionKeyState for ResultEncrypted {
    type State = Invalid;
}

impl SessionKeyState for Finished {
    type State = Invalid;
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

impl<K, S> Key<K, S>
where
    S: KeyState,
    K: Zeroize + Default,
{
    #[pure]
    pub fn is_allowed_twice(&self) -> bool {
        self._state.is_allowed_twice()
    }
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

impl<K> Zeroize for Key<K, AllowedOnce>
where
    K: Default + Zeroize,
{
    #[trusted]
    fn zeroize(&mut self) {
        self.raw.zeroize();
    }
}

impl<K> Key<K, AllowedOnce>
where
    K: Zeroize + Default,
{
    // FIXME: Is this logically flawed?
    #[requires((&self)._state.is_allowed_once())]
    #[ensures((&result)._state.is_invalid())]
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

// impl<K> ComputingTaskSession<ChannelEstablished, K> {
//     pub fn establish_channel(template: ComputingTaskTemplate<Initialized>, key: K) -> ComputingTaskSession<ChannelEstablished, K> {
//         ComputingTaskSession {
//             key: K,
//             _state: ChannelEstablished,
//         }
//     }
// }

pub struct ComputingTaskSession<S, K>
where
    S: TaskState + SessionKeyState,
    K: Zeroize + Default,
    <S as SessionKeyState>::State: KeyState,
{
    pub key: Key<K, <S as SessionKeyState>::State>,
    _state: S,
}

/// Very hacky: Prusti cannot properly verify a deeply nested generic type so we need to wrap it with an associated function to circumvent
/// verifying the inner types when prusti tries to unfold the expression.
#[pure]
#[trusted]
#[allow(unused)]
fn is_allowed_twice<S, K>(input: &ComputingTaskSession<S, K>) -> bool
where
    S: TaskState + SessionKeyState,
    K: Zeroize + Default,
    <S as SessionKeyState>::State: KeyState,
{
    input.key.is_allowed_twice()
}

impl<K> ComputingTaskSession<ChannelEstablished, K>
where
    K: Zeroize + Default,
{
    #[cfg(not(feature = "use_prusti"))]
    pub fn establish_channel(
        _template: ComputingTaskTemplate<Initialized>,
        attestation_callback: &dyn Fn() -> K,
    ) -> Self {
        let key = attestation_callback();
        ComputingTaskSession {
            key: Key::from(key),
            _state: ChannelEstablished,
        }
    }

    #[cfg(feature = "use_prusti")]
    #[trusted]
    #[requires((&_template)._state.is_initialized())]
    #[ensures((&result)._state.is_channel_established())]
    #[ensures(is_allowed_twice(&result))]
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
#[cfg(feature = "use_prusti")]
impl ComputingTask<DataReceived, AES128Key, VecAESData>
where
    VecAESData: EncDec<AES128Key>,
    AES128Key: Zeroize + Default,
{
    #[trusted]
    #[requires((&session)._state.is_channel_established())]
    #[requires(is_allowed_twice(&session))]
    #[ensures((&result)._state.is_data_received())]
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

#[cfg(feature = "use_prusti")]
impl ComputingTask<DataReceived, AES128Key, VecAESData> {
    /// The function now verifies.
    /// It involves several complex steps.
    #[requires((&self)._state.is_data_received())]
    #[ensures((&result)._state.is_result_encrypted())]
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
    #[cfg(not(feature = "use_prusti"))]
    pub fn receive_data(
        session: ComputingTaskSession<ChannelEstablished, K>,
        receive_callback: &dyn Fn() -> D,
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

    #[trusted]
    #[requires((&self)._state.is_data_received())]
    #[ensures((&result)._state.is_data_decrypted())]
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

    #[cfg(not(feature = "use_prusti"))]
    pub fn compute(
        self,
        compute_callback: &dyn Fn(D) -> D,
    ) -> ComputingTask<ResultEncrypted, K, D> {
        let decrypted = self.decrypt_data().unwrap();
        let result = decrypted.do_compute(compute_callback).unwrap();
        result.encrypt_result().unwrap()
    }
}

impl<K, D> ComputingTask<ResultEncrypted, K, D>
where
    K: Zeroize + Default,
    D: EncDec<K>,
{
    #[trusted]
    #[requires((&self)._state.is_result_encrypted())]
    pub fn take_result(self) -> D {
        self.data.raw
    }
}

#[cfg(feature = "use_prusti")]
impl ComputingTask<DataDecrypted, AES128Key, VecAESData> {
    #[trusted]
    #[requires((&self)._state.is_data_decrypted())]
    #[ensures((&result)._state.is_result_decrypted())]
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
    #[cfg(not(feature = "use_prusti"))]
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
    #[trusted]
    #[requires((&self)._state.is_result_decrypted())]
    #[ensures((&result)._state.is_result_encrypted())]
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
