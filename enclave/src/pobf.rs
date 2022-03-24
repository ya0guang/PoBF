#![forbid(unsafe_code)]

use crate::ocall_log;
use crate::types::*;
use sgx_types::*;
use std::vec::Vec;

pub fn pobf_private_computing(
    data_buffer: &[u8],
    sealed_key_buffer: &[u8],
) -> SgxResult<VecAESData> {
    ocall_log!("PoBF sample task AES started...",);
    // initialize data from buffer
    let input_key = AES128Key::from_sealed_buffer(sealed_key_buffer)?;
    let output_key = AES128Key::from_sealed_buffer(sealed_key_buffer)?;
    let data = VecAESData::from_ref(data_buffer);

    // privacy violation: cannot call decrypt directly on the data
    // captured by: compiler error
    #[cfg(feature = "vio_privacy")]
    data.decrypt(&input_key)?;

    // privacy violation: cannot see through the key
    // captured by: compiler error
    #[cfg(feature = "vio_privacy")]
    let raw_key = input_key.inner;

    // safety violation: cannot see through the key using unsafe code by derefencing it
    // captured by: compiler error
    #[cfg(feature = "vio_unsafe")]
    let raw_key = unsafe { *(&input_key as *const AES128Key as *const u8) };

    // custom compuatation task
    let computation_task = &private_inc;
    let result = pobf_workflow(data, input_key, output_key, computation_task);

    result
}

// Require trait To Vector?
pub fn private_inc<T>(data: T) -> T
where
    T: From<Vec<u8>> + Into<Vec<u8>>,
{
    let vec_data = data.into();
    // try to violate key? Cannot see the key!
    // conditional compile some errors

    let step = 1;
    // this can be proven true by MIRAI
    ocall_log!("The step is {} in computation_enc", 1, step);

    
    let mut new = Vec::new();
    for i in vec_data.iter() {
        new.push(i + step);
    }

    // however, MIRAI complians about this
    // leakage violation: cannot log the secret data
    // captured by: MIRAI warnning
    ocall_log!("after increasing, the 0th data is {}", 1, new[0]);

    T::from(new)
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
    #[cfg(feature = "vio_typestate")]
    let dec_in_data = dec_in.take();

    let dec_out: ProtectedAssets<Decrypted, Output, D, K> = dec_in.invoke(computation_task)?;

    // privacy violation: cannot take the inner data from ProtectedAssets
    // captured by: compiler error
    #[cfg(feature = "vio_privacy")]
    let de_out_data = dec_out.data;

    let en_out: ProtectedAssets<Encrypted, Output, D, K> = dec_out.encrypt()?;
    Ok(en_out.take())
}
