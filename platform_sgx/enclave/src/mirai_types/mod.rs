#![cfg_attr(feature = "sgx", no_std)]
#![forbid(unsafe_code)]

use zeroize::Zeroize;

pub mod mirai_comp;
pub mod task;

#[cfg(feature = "sgx")]
use sgx_types::error::SgxResult as Result;
#[cfg(not(feature = "sgx"))]
type Result<T> = core::result::Result<T, ()>;

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
