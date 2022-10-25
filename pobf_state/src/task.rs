#![forbid(unsafe_code)]

use core::marker::PhantomData;
use zeroize::Zeroize;
#[cfg(feature = "sgx")]
use sgx_types::error::SgxResult as Result;
#[cfg(not(feature = "sgx"))]
type Result<T> = core::result::Result<T, ()>;

pub const BUFFER_SIZE: usize = 1024;
pub const SEALED_DATA_SIZE: usize = 16;

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
    _state: S,
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
    fn zeroize(&mut self) {
        self.raw.zeroize();
    }
}

impl<K> Key<K, AllowedOnce>
where
    K: Zeroize + Default,
{
    fn once(mut self) -> Key<K, AllowedTwice> {
        self.raw.zeroize();
        Key {
            raw: K::default(),
            _state: AllowedTwice,
        }
    }
}

impl<K> Key<K, Invalid>
where
    K: Zeroize + Default,
{
    pub fn invalid() -> Self {
        Key {
            raw: K::default(),
            _state: Invalid,
        }
    }
}

#[allow(private_in_public)]
pub trait Decryption<K>
where
    Self: Sized + Zeroize,
{
    fn decrypt(self, key: &K) -> Result<Self>;
}

#[allow(private_in_public)]
pub trait Encryption<K>
where
    Self: Sized + Zeroize,
{
    fn encrypt(self, key: &K) -> Result<Self>;
}

pub trait EncDec<K>
where
    Self: Sized + Decryption<K> + Encryption<K>,
{
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
    key: Key<K, <S as SessionKeyState>::State>,
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
        let key = attestation_callback();
        ComputingTaskSession {
            key: Key::from(key),
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

impl<K, D> ComputingTask<DataReceived, K, D>
where
    K: Zeroize + Default,
    D: EncDec<K>,
{
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

    pub fn compute(
        self,
        compute_callback: &dyn Fn(&D) -> D,
    ) -> ComputingTask<ResultEncrypted, K, D> {
        let decrypted = self.decrypt_data().unwrap();
        let result = decrypted.do_compute(compute_callback).unwrap();
        result.encrypt_result().unwrap()
    }
}

impl<K, D> ComputingTask<DataDecrypted, K, D>
where
    K: Zeroize + Default,
    D: EncDec<K>,
{
    fn do_compute(self, task: &dyn Fn(&D) -> D) -> Result<ComputingTask<ResultDecrypted, K, D>> {
        Ok(ComputingTask {
            key: self.key,
            data: Data {
                raw: task(&self.data.raw),
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
    fn encrypt_result(self) -> Result<ComputingTask<ResultEncrypted, K, D>> {
        let data = self.data.raw.encrypt(&self.key.raw)?;
        self.key.once();
        Ok(ComputingTask {
            key: Key::invalid(),
            data: Data {
                raw: data,
                _state: EncryptedOutput,
                _key_type: PhantomData,
            },
            _state: ResultEncrypted,
        })
    }
}
