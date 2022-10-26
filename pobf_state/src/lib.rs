#![no_std]
#![forbid(unsafe_code)]
#![allow(incomplete_features)]
#![feature(unsized_locals, unsized_fn_params)]

pub mod asset;
pub mod task;

#[cfg(feature = "sgx")]
use sgx_types::error::SgxResult as Result;
use zeroize::Zeroize;
#[cfg(not(feature = "sgx"))]
type Result<T> = core::result::Result<T, ()>;
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
