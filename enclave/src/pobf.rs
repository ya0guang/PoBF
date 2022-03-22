#![forbid(unsafe_code)]

use crate::types::*;
use mirai_annotations::*;
// #[macro_use]
// use crate::ocall::*;
use sgx_types::marker::ContiguousMemory;

pub fn pobf_sample_task_aes(data: EncData, inkey: AES128Key, outkey: AES128Key) -> EncData {
    println!("PoBF sample task AES started...");

    pobf_ref_implementation(data, inkey, outkey, &computation_enc)
}



pub fn pobf_ref_implementation<T: ContiguousMemory + EncDec<K>, K: Default>(
    input_sealed: T,
    input_key: K,
    output_key: K,
    f: &dyn Fn(T) -> T,
) -> T {
    let protected_enc_in = ProtectedAssets::new(input_sealed, input_key, output_key);

    let protected_dec_in = protected_enc_in.decrypt();

    let protected_dec_out = protected_dec_in.invoke(f);

    let protected_enc_out = protected_dec_out.encrypt();

    protected_enc_out.take()
}

pub fn computation_enc(data: EncData) -> EncData {
    let mut new_data = EncData::new([0u8; BUFFER_SIZE], data.mac, data.length);
    
    let step = 1;
    // this can be proven true by MIRAI
    verify!(step == 1);
    println!("the step is {} in computation_enc", step);

    for i in 0..new_data.length {
        new_data.inner[i] = data.inner[i] + step;
    }

    // however, MIRAI complians about this
    verify!(new_data.inner[0] == 1);
    println!("after increasing, the 0th data is {}", new_data.inner[0]);

    new_data
}


pub fn pobf_sample_task_seal(data: SealedData) -> SealedData {
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

