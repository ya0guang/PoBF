#![forbid(unsafe_code)]

use core::marker::PhantomData;
use sgx_types::error::*;

#[derive(Default)]
pub struct SealedData<T: ?Sized> {
    marker: PhantomData<T>,
}

pub struct UnsealedData<T: ?Sized> {
    marker: PhantomData<T>,
}

#[allow(unused)]
impl<T: ?Sized> SealedData<T> {
    pub fn seal(data: &T, aad: Option<&[u8]>) -> SgxResult<SealedData<T>> {
        unimplemented!()
    }

    pub fn payload_size(&self) -> u32 {
        unimplemented!()
    }

    pub fn to_bytes(&self) -> SgxResult<Vec<u8>> {
        unimplemented!()
    }

    pub fn from_slice(data: &[u8]) -> SgxResult<SealedData<T>> {
        unimplemented!()
    }

    pub fn unseal(self) -> SgxResult<UnsealedData<T>> {
        unimplemented!()
    }
}

impl<T: ?Sized> UnsealedData<T> {
    pub fn to_plaintext(&self) -> &T {
        unimplemented!()
    }
}
