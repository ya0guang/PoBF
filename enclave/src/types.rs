use sgx_types::marker::ContiguousMemory;
use std::vec::Vec;

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

#[derive(Copy, Clone, Default, Debug)]
pub struct DataFixed {
    inner: [u8; 16],
}

unsafe impl ContiguousMemory for DataFixed {}

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
    D: ContiguousMemory,
{
    pub fn decrypt(self, _key: &Key<Sealed>) -> Data<Decrypted, Input, D> {
        Data {
            raw: self.raw,
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
    D: ContiguousMemory,
{
    pub fn encrypt(self, _key: &Key<Sealed>) -> Data<Encrypted, Output, D> {
        Data {
            raw: self.raw,
            _encryption_state: Encrypted,
            _io_state: Output,
        }
    }
}

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
    pub data: Data<S, T, D>,
    pub input_key: Key<<Data<S, T, D> as InputKeyState>::KeyState>,
    pub output_key: Key<<Data<S, T, D> as OutputKeyState>::KeyState>,
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
    D: ContiguousMemory,
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
    D: ContiguousMemory,
{
    pub fn encrypt(self) -> ProtectedAssets<Encrypted, Output, D> {
        ProtectedAssets {
            data: self.data.encrypt(&self.output_key),
            input_key: self.input_key,
            output_key: self.output_key.zeroize(),
        }
    }
}
