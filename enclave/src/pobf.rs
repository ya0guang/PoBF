#![forbid(unsafe_code)]

use crate::ocall_log;
use crate::types::*;
use sgx_types::*;
use std::vec::Vec;

pub fn pobf_private_computing(
    data_buffer: &[u8],
    sealed_key_buffer: &[u8],
) -> SgxResult<VecAESData> {
    println!("PoBF sample task AES started...");
    // initialize data from buffer
    let input_key: vecaes::AES128Key = vecaes::AES128Key::from_sealed_buffer(sealed_key_buffer)?;
    let output_key: vecaes::AES128Key = vecaes::AES128Key::from_sealed_buffer(sealed_key_buffer)?;
    let data = VecAESData::from_ref(data_buffer);

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

    let result = pobf_ref_implementation(data, input_key, output_key, computation_task);

    result
}

pub fn private_inc(data: VecAESData) -> VecAESData {
    // try to violate key? Cannot see the key!
    // conditional compile some errors

    let step = 1;
    // this can be proven true by MIRAI
    ocall_log!("he step is {} in computation_enc", 1, step);

    let original = data.to_vec();
    let mut new = Vec::new();
    for i in original.iter() {
        new.push(i + step);
    }

    // however, MIRAI complians about this
    // leakage violation: cannot log the secret data
    // captured by: MIRAI warnning
    ocall_log!("after increasing, the 0th data is {}", 1, new[0]);

    VecAESData::new(new)
}

pub fn pobf_ref_implementation<D: EncDec<K>, K: Default>(
    input_sealed: D,
    input_key: K,
    output_key: K,
    computation_task: &dyn Fn(D) -> D,
) -> SgxResult<D> {
    let en_in: ProtectedAssets<Encrypted, Input, D, K> =
        ProtectedAssets::new(input_sealed, input_key, output_key);

    let de_in: ProtectedAssets<Decrypted, Input, D, K> = en_in.decrypt()?;

    // unsafe code violation: cannot use (unsafe) raw pointer dereferrence to steal data

    // typestate violation: cannot take inner data from decrypted data
    // captured by: compiler error
    #[cfg(feature = "vio_typestate")]
    let de_in_data = de_in.take();

    let de_out: ProtectedAssets<Decrypted, Output, D, K> = de_in.invoke(computation_task)?;

    // privacy violation: cannot take the inner data from ProtectedAssets
    // captured by: compiler error
    #[cfg(feature = "vio_privacy")]
    let de_out_data = de_out.data;

    let en_out: ProtectedAssets<Encrypted, Output, D, K> = de_out.encrypt()?;

    Ok(en_out.take())
}
