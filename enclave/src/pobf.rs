#![forbid(unsafe_code)]

use crate::types::*;

pub fn pobf_ref_implementation(input_sealed: SealedData) -> SealedData {
    let protected_enc_in = ProtectedAssets::new(input_sealed, vec![1], vec![1]);

    let protected_dec_in = protected_enc_in.decrypt();

    let protected_dec_out = protected_dec_in.invoke(&computation_sealed);

    let protected_enc_out = protected_dec_out.encrypt();

    protected_enc_out.take()
}

pub fn computation_sealed(data: SealedData) -> SealedData {
    let mut new_data = SealedData::new([0u8; BUFFER_SIZE]);

    for i in 0..SEALED_DATA_SIZE {
        new_data.inner[i] = data.inner[i] + 1;
    }
    new_data
}

pub fn computation_enc(data: EncData) -> EncData {
    let mut new_data = EncData::new([0u8; BUFFER_SIZE], data.mac, data.length);

    for i in 0..new_data.length {
        new_data.inner[i] = data.inner[i] + 1;
    }
    new_data
}
