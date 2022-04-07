#![forbid(unsafe_code)]

use crate::ocall::*;
use crate::types::*;
use crate::userfunc::vec_inc;
use crate::{ocall_log, verified_log};
use sgx_types::error::SgxResult;
use alloc::vec::Vec;

pub fn pobf_private_computing(
    data_buffer: &[u8],
    sealed_key_buffer: &[u8],
) -> SgxResult<VecAESData> {
    verified_log!("PoBF sample task AES started...");
    // initialize data from buffer
    let input_key = AES128Key::from_sealed_buffer(sealed_key_buffer)?;
    let output_key = AES128Key::from_sealed_buffer(sealed_key_buffer)?;
    let data = VecAESData::from(data_buffer);

    // privacy violation: cannot call decrypt directly on the data
    // captured by: compiler error
    #[cfg(feature = "direct_decrypt")]
    data.decrypt(&input_key)?;

    // privacy violation: cannot see through the key
    // captured by: compiler error
    #[cfg(feature = "access_inner")]
    let raw_key = input_key.inner;

    // safety violation: cannot read the key through dereferencing using unsafe
    // captured by: compiler error
    #[cfg(feature = "raw_read")]
    let raw_key = unsafe { *(&input_key as *const AES128Key as *const u8) };

    // safety violation: cannot write to the insecure world through dereferencing using unsafe
    // captured by: compiler error
    #[cfg(feature = "raw_write")]
    unsafe {
        *(0x3ffffff as *const u8 as *mut u8) = data_buffer[1];
    }

    // custom compuatation task
    let computation_task = &private_vec_compute;
    let result = pobf_workflow(data, input_key, output_key, computation_task);

    result
}

pub fn private_vec_compute<T>(input: T) -> T
where
    T: From<Vec<u8>> + Into<Vec<u8>>,
{
    let input_vec = input.into();

    let output_vec = vec_inc(input_vec);
    T::from(output_vec)
}

pub fn pobf_workflow<D: EncDec<K>, K: Default>(
    input_sealed: D,
    input_key: K,
    output_key: K,
    computation_task: &dyn Fn(D) -> D,
) -> SgxResult<D> {
    let enc_in: ProtectedAssets<Encrypted, Input, D, K> =
        ProtectedAssets::new(input_sealed, input_key, output_key);

    let dec_in: ProtectedAssets<Decrypted, Input, D, K> = enc_in.decrypt()?;

    // typestate violation: cannot take inner data from decrypted data
    // captured by: compiler error
    #[cfg(feature = "disallowed_trans")]
    let dec_in_data = dec_in.take();

    #[cfg(feature = "rude_copy")]
    let data_copy = dec_in.copy();

    let dec_out: ProtectedAssets<Decrypted, Output, D, K> = dec_in.invoke(computation_task)?;

    // privacy violation: cannot take the inner data from ProtectedAssets
    // captured by: compiler error
    #[cfg(feature = "access_key")]
    let de_out_data = dec_out.data;

    let en_out: ProtectedAssets<Encrypted, Output, D, K> = dec_out.encrypt()?;
    Ok(en_out.take())
}
