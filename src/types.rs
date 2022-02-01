use std::borrow::Borrow;

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

impl InputKeyState for Data<Encrypted, Input> {
    type KeyState = Sealed;
}

impl InputKeyState for Data<Decrypted, Input> {
    type KeyState = Invalid;
}

impl InputKeyState for Data<Decrypted, Output> {
    type KeyState = Invalid;
}

impl InputKeyState for Data<Encrypted, Output> {
    type KeyState = Invalid;
}

pub trait OutputKeyState {
    type KeyState;
}

impl OutputKeyState for Data<Encrypted, Input> {
    type KeyState = Sealed;
}

impl OutputKeyState for Data<Decrypted, Input> {
    type KeyState = Sealed;
}

impl OutputKeyState for Data<Decrypted, Output> {
    type KeyState = Sealed;
}

impl OutputKeyState for Data<Encrypted, Output> {
    type KeyState = Invalid;
}

pub struct Data<S, T>
where
    S: EncryptionState,
    T: IOState,
{
    raw: Vec<u8>,
    // Ecrypted / Decrypted
    _encryption_state: S,
    // Input / Output
    _io_state: T,
}

impl Data<Encrypted, Input> {
    pub fn new(raw: Vec<u8>) -> Self {
        Self {
            raw,
            _encryption_state: Encrypted,
            _io_state: Input,
        }
    }
}

impl Data<Encrypted, Input> {
    pub fn decrypt(self, _key: &Key<Sealed>) -> Data<Decrypted, Input> {
        Data {
            raw: self.raw,
            _encryption_state: Decrypted,
            _io_state: Input,
        }
    }
}

impl Data<Decrypted, Input> {
    pub fn invoke(self, fun: &dyn Fn(Vec<u8>) -> Vec<u8>) -> Data<Decrypted, Output> {
        Data {
            raw: fun(self.raw),
            _encryption_state: Decrypted,
            _io_state: Output,
        }
    }
}

impl Data<Decrypted, Output> {
    pub fn encrypt(self, _key: &Key<Sealed>) -> Data<Encrypted, Output> {
        Data {
            raw: self.raw,
            _encryption_state: Encrypted,
            _io_state: Output,
        }
    }
}

pub struct Key<S> {
    raw: Vec<u8>,
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

pub struct ProtectedAssets<S, T>
where
    Data<S, T>: InputKeyState,
    Data<S, T>: OutputKeyState,
    S: EncryptionState,
    T: IOState,
{
    pub data: Data<S, T>,
    pub input_key: Key<<Data<S, T> as InputKeyState>::KeyState>,
    pub output_key: Key<<Data<S, T> as OutputKeyState>::KeyState>,
}

impl<T> Borrow<T> for ProtectedAssets<Encrypted, T>
where
    Data<Encrypted, T>: InputKeyState,
    Data<Encrypted, T>: OutputKeyState,
    T: IOState,
{
    fn borrow(&self) -> &T {
       panic!()
    }
}

impl ProtectedAssets<Encrypted, Input> {
    pub fn decrypt(self) -> ProtectedAssets<Decrypted, Input> {
        ProtectedAssets {
            data: self.data.decrypt(&self.input_key),
            input_key: self.input_key.zeroize(),
            output_key: self.output_key,
        }
    }

    pub fn new(raw: Vec<u8>, input_key: Vec<u8>, output_key: Vec<u8>) -> Self {
        ProtectedAssets {
            data: Data::new(raw),
            input_key: Key::new(input_key),
            output_key: Key::new(output_key),
        }
    }
}

impl ProtectedAssets<Decrypted, Input> {
    pub fn invoke(self, fun: &dyn Fn(Vec<u8>) -> Vec<u8>) -> ProtectedAssets<Decrypted, Output> {
        ProtectedAssets {
            data: self.data.invoke(fun),
            input_key: self.input_key,
            output_key: self.output_key,
        }
    }
}

impl ProtectedAssets<Decrypted, Output> {
    pub fn encrypt(self) -> ProtectedAssets<Encrypted, Output> {
        ProtectedAssets {
            data: self.data.encrypt(&self.output_key),
            input_key: self.input_key,
            output_key: self.output_key.zeroize(),
        }
    }
}