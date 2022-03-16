use core::marker::PhantomData;
use sgx_types::*;

pub struct SgxSealedData<'a, T: 'a + ?Sized> {
    marker: PhantomData<&'a T>,
}

pub struct SgxUnsealedData<'a, T: 'a + ?Sized> {
    marker: PhantomData<&'a T>,
}

impl<'a, T: 'a + ?Sized> SgxSealedData<'a, T> {
    pub unsafe fn from_raw_sealed_data_t(_p: *mut sgx_sealed_data_t, _len: u32) -> Option<Self> {
        unimplemented!()
    }

    pub unsafe fn to_raw_sealed_data_t(
        &self,
        _p: *mut sgx_sealed_data_t,
        _len: u32,
    ) -> Option<*mut sgx_sealed_data_t> {
        unimplemented!()
    }

    pub fn seal_data(_additional_text: &[u8], _encrypt_text: &'a T) -> SgxResult<Self> {
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
