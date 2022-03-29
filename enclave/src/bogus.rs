use core::marker::PhantomData;
use sgx_types::error::*;
use sgx_types::types::*;

#[derive(Default)]
pub struct SgxSealedData<'a, T: 'a + ?Sized> {
    marker: PhantomData<&'a T>,
}

pub struct SgxUnsealedData<'a, T: 'a + ?Sized> {
    marker: PhantomData<&'a T>,
}

#[allow(unused)]
impl<'a, T: 'a + ?Sized> SgxSealedData<'a, T> {
    pub unsafe fn from_raw_sealed_data_t(p: *mut CSealedData, len: u32) -> Option<Self> {
        unimplemented!()
    }

    pub unsafe fn to_raw_sealed_data_t(
        &self,
        p: *mut CSealedData,
        len: u32,
    ) -> Option<*mut CSealedData> {
        unimplemented!()
    }

    pub fn seal_data(additional_text: &[u8], encrypt_text: &'a T) -> SgxResult<Self> {
        unimplemented!()
    }

    pub fn unseal_data(&self) -> SgxResult<SgxUnsealedData<'a, T>> {
        unimplemented!()
    }
}

impl<'a, T: 'a + ?Sized> SgxUnsealedData<'a, T> {
    pub fn get_decrypt_txt(&self) -> &T {
        unimplemented!()
    }
}

#[allow(unused)]
#[allow(non_snake_case)]
pub fn rsgx_rijndael128GCM_decrypt(
    key: &Key128bit,
    src: &[u8],
    iv: &[u8],
    aad: &[u8],
    mac: &Mac128bit,
    dst: &mut [u8],
) -> SgxError {
    unimplemented!()
}

#[allow(unused)]
#[allow(non_snake_case)]
pub fn rsgx_rijndael128GCM_encrypt(
    key: &Key128bit,
    src: &[u8],
    iv: &[u8],
    aad: &[u8],
    dst: &mut [u8],
    mac: &mut Mac128bit,
) -> SgxError {
    unimplemented!()
}
