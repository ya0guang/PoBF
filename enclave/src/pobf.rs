#![forbid(unsafe_code)]

use crate::ocall_log;
use crate::types::*;
use sgx_types::*;
use std::vec::Vec;

pub fn pobf_sample_task_aaes(
    data: ArrayAESData,
    sealed_key_buffer: &[u8],
) -> SgxResult<ArrayAESData> {
    // initialize keys from buffer
    let input_key: AES128Key = AES128Key::from_sealed_buffer(sealed_key_buffer)?;
    let output_key: AES128Key = AES128Key::from_sealed_buffer(sealed_key_buffer)?;
    println!("PoBF sample task AES started...");
    // custom compuatation task
    let computation_task = &computation_aaes;

    let result = pobf_ref_implementation(data, input_key, output_key, computation_task);

    result
}

pub fn pobf_sample_task_vaes(
    data_buffer: &[u8],
    sealed_key_buffer: &[u8],
) -> SgxResult<VecAESData> {
    // initialize data from buffer
    let input_key: vecaes::AES128Key = vecaes::AES128Key::from_sealed_buffer(sealed_key_buffer)?;
    let output_key: vecaes::AES128Key = vecaes::AES128Key::from_sealed_buffer(sealed_key_buffer)?;
    let data = VecAESData::from_ref(data_buffer);

    println!("PoBF sample task AES started...");
    // custom compuatation task
    let computation_task = &computation_vaes;

    let result = pobf_ref_implementation(data, input_key, output_key, computation_task);

    result
}

pub fn computation_vaes(data: VecAESData) -> VecAESData {
    // try to violate key? Cannot see the key!
    // conditional compile some errors
    let original = data.to_vec();
    let mut new = Vec::new();
    for i in original.iter() {
        new.push(i + 1);
    }

    VecAESData::new(new)
}

pub fn pobf_ref_implementation<T: EncDec<K>, K: Default>(
    input_sealed: T,
    input_key: K,
    output_key: K,
    computation_task: &dyn Fn(T) -> T,
) -> SgxResult<T> {
    let protected_enc_in = ProtectedAssets::new(input_sealed, input_key, output_key);

    let protected_dec_in = protected_enc_in.decrypt()?;

    let protected_dec_out = protected_dec_in.invoke(computation_task)?;

    let protected_enc_out = protected_dec_out.encrypt()?;

    Ok(protected_enc_out.take())
}

// data to_vec!
pub fn computation_aaes(data: ArrayAESData) -> ArrayAESData {
    // try to violate key? Cannot see the key!
    // conditional compile some errors

    let mut output_data = ArrayAESData::new([0u8; BUFFER_SIZE], data.mac, data.length);

    let step = 1;
    // this can be proven true by MIRAI
    ocall_log!("he step is {} in computation_enc", 1, step);

    for i in 0..output_data.length {
        output_data.inner[i] = data.inner[i] + step;
    }

    // however, MIRAI complians about this
    ocall_log!(
        "after increasing, the 0th data is {}",
        1,
        output_data.inner[0]
    );
    output_data
}

pub fn pobf_sample_task_seal(data: SealedData) -> SgxResult<SealedData> {
    println!("PoBF sample task seal started...");

    pobf_ref_implementation(data, vec![], vec![], &computation_sealed)
}

pub fn computation_sealed(data: SealedData) -> SealedData {
    let mut new_data = SealedData::new([0u8; BUFFER_SIZE]);

    for i in 0..SEALED_DATA_SIZE {
        new_data.inner[i] = data.inner[i] + 1;
    }
    new_data
}

