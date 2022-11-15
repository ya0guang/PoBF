#![forbid(unsafe_code)]

use super::mirai_comp::*;
use core::marker::PhantomData;
use mirai_annotations::*;
use zeroize::Zeroize;

cfg_if::cfg_if! {
    if #[cfg(feature = "mirai")] {
        use crate::mirai_types::*;
    } else {
        use pobf_state::{Decryption, EncDec, Encryption};
    }
}

#[cfg(feature = "sgx")]
use sgx_types::error::SgxResult as Result;
#[cfg(not(feature = "sgx"))]
type Result<T> = core::result::Result<T, ()>;

pub trait TaskState {}
pub trait DataState {}
pub trait KeyState {}

// Common States for Data and Key
pub struct Uninitialized;
impl DataState for Uninitialized {}

impl KeyState for Uninitialized {}

pub struct Invalid;
impl DataState for Invalid {}

impl KeyState for Invalid {}

// Task States
pub struct Initialized;
impl TaskState for Initialized {}
pub struct ChannelEstablished;
impl TaskState for ChannelEstablished {}
pub struct DataReceived;
impl TaskState for DataReceived {}
//These two states are transient and not permitted to be used by the users!
struct DataDecrypted;
impl TaskState for DataDecrypted {}
struct ResultDecrypted;
impl TaskState for ResultDecrypted {}
pub struct ResultEncrypted;
impl TaskState for ResultEncrypted {}
pub struct Finished;
impl TaskState for Finished {}

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

impl KeyState for AllowedTwice {}
// This state is transient and not permitted to be used by the users!
struct AllowedOnce;

impl KeyState for AllowedOnce {}

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

impl<K> Key<K, AllowedTwice>
where
    K: Zeroize + Default,
{
    fn from(raw: K) -> Self {
        Key {
            raw,
            _state: AllowedTwice,
        }
    }

    fn once(self) -> Key<K, AllowedOnce> {
        precondition!(has_tag!(&self, SecretTaint));

        let ans = Key {
            raw: self.raw,
            _state: AllowedOnce,
        };

        postcondition!(has_tag!(&ans, SecretTaint));
        ans
    }
}

impl<K> Zeroize for Key<K, AllowedOnce>
where
    K: Default + Zeroize,
{
    fn zeroize(&mut self) {
        self.raw.zeroize();
    }
}

impl<K> Key<K, AllowedOnce>
where
    K: Zeroize + Default,
{
    fn once(mut self) -> Key<K, Invalid> {
        precondition!(has_tag!(&self, SecretTaint));

        self.raw.zeroize();
        let ans = Key {
            raw: K::default(),
            _state: Invalid,
        };

        assumed_postcondition!(does_not_have_tag!(&ans, SecretTaint));
        ans
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
    pub fn new() -> Self {
        let ans = Self {
            _state: Initialized,
        };

        postcondition!(does_not_have_tag!(&ans, SecretTaint));
        ans
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
    pub fn establish_channel(
        _template: ComputingTaskTemplate<Initialized>,
        attestation_callback: &dyn Fn() -> K,
    ) -> Self {
        precondition!(does_not_have_tag!(&_template, SecretTaint));

        let key = attestation_callback();
        verify!(has_tag!(&key, SecretTaint));

        let ans = ComputingTaskSession {
            key: Key::from(key),
            _state: ChannelEstablished,
        };

        add_tag!(&ans, SecretTaint);
        postcondition!(has_tag!(&ans, SecretTaint));
        ans
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

impl<K, D> ComputingTask<DataReceived, K, D>
where
    K: Zeroize + Default,
    D: EncDec<K>,
{
    pub fn receive_data(
        session: ComputingTaskSession<ChannelEstablished, K>,
        receive_callback: &dyn Fn() -> D,
    ) -> Self {
        precondition!(has_tag!(&session, SecretTaint));

        let data = receive_callback();
        verify!(has_tag!(&data, SecretTaint));

        let ans = ComputingTask {
            key: session.key,
            data: Data {
                raw: data,
                _state: EncryptedInput,
                _key_type: PhantomData,
            },
            _state: DataReceived,
        };

        add_tag!(&ans, SecretTaint);
        postcondition!(has_tag!(&ans, SecretTaint));
        ans
    }

    fn decrypt_data(self) -> Result<ComputingTask<DataDecrypted, K, D>> {
        precondition!(has_tag!(&self, SecretTaint));

        let data = self.data.raw.decrypt(&self.key.raw)?;
        verify!(has_tag!(&data, SecretTaint));

        let ans = Ok(ComputingTask {
            key: self.key.once(),
            data: Data {
                raw: data,
                _state: DecryptedInput,
                _key_type: PhantomData,
            },
            _state: DataDecrypted,
        });

        postcondition!(has_tag!(&ans, SecretTaint));
        ans
    }

    pub fn compute(
        self,
        compute_callback: &dyn Fn(D) -> D,
    ) -> ComputingTask<ResultEncrypted, K, D> {
        precondition!(has_tag!(&self, SecretTaint));

        let decrypted = self.decrypt_data().unwrap();
        let result = decrypted.do_compute(compute_callback).unwrap();
        let ans = result.encrypt_result().unwrap();

        assumed_postcondition!(does_not_have_tag!(&ans, SecretTaint));
        ans
    }
}

impl<K, D> ComputingTask<ResultEncrypted, K, D>
where
    K: Zeroize + Default,
    D: EncDec<K>,
{
    pub fn take_result(self) -> D {
        self.data.raw
    }
}

impl<K, D> ComputingTask<DataDecrypted, K, D>
where
    K: Zeroize + Default,
    D: EncDec<K>,
{
    fn do_compute(self, task: &dyn Fn(D) -> D) -> Result<ComputingTask<ResultDecrypted, K, D>> {
        precondition!(has_tag!(&self, SecretTaint));

        let ans = Ok(ComputingTask {
            key: self.key,
            data: Data {
                raw: task(self.data.raw),
                _state: DecryptedOutput,
                _key_type: PhantomData,
            },
            _state: ResultDecrypted,
        });

        postcondition!(has_tag!(&ans, SecretTaint));
        ans
    }
}

impl<K, D> ComputingTask<ResultDecrypted, K, D>
where
    K: Zeroize + Default,
    D: EncDec<K>,
{
    fn encrypt_result(self) -> Result<ComputingTask<ResultEncrypted, K, D>> {
        precondition!(has_tag!(&self, SecretTaint));

        let data = self.data.raw.encrypt(&self.key.raw)?;
        // Encryption will remove the tag here.
        assume!(does_not_have_tag!(&data, SecretTaint));

        verify!(has_tag!(&self.key, SecretTaint));
        let consumed_key = self.key.once();
        verify!(does_not_have_tag!(&consumed_key, SecretTaint));

        let ans = Ok(ComputingTask {
            key: consumed_key,
            data: Data {
                raw: data,
                _state: EncryptedOutput,
                _key_type: PhantomData,
            },
            _state: ResultEncrypted,
        });

        postcondition!(does_not_have_tag!(&ans, SecretTaint));
        ans
    }
}
