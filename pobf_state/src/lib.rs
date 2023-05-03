#![allow(incomplete_features)]
#![allow(private_in_public)]
#![cfg_attr(feature = "sgx", no_std)]
#![feature(unsized_locals, unsized_fn_params)]
#![feature(error_in_core)]
#![forbid(unsafe_code)]

extern crate alloc;
extern crate prusti_contracts;

pub mod task;

#[cfg(feature = "prusti")]
mod bogus;

use prusti_contracts::*;
use zeroize::Zeroize;

#[cfg(feature = "sgx")]
use sgx_types::error::SgxResult as Result;
#[cfg(not(feature = "sgx"))]
pub type Result<T> = core::result::Result<T, ()>;

pub trait Decryption<K>
where
    Self: Sized + Zeroize,
{
    /// Prusti cannot verify cryptography library code, so we mark them as trusted here.
    #[trusted]
    #[ensures(result.is_ok())]
    fn decrypt(self, key: &K) -> Result<Self>;
}

#[allow(private_in_public)]
pub trait Encryption<K>
where
    Self: Sized + Zeroize,
{
    /// Prusti cannot verify cryptography library code, so we mark them as trusted here.
    #[trusted]
    #[ensures(result.is_ok())]
    fn encrypt(self, key: &K) -> Result<Self>;
}

pub trait EncDec<K>
where
    Self: Sized + Decryption<K> + Encryption<K>,
{
}
