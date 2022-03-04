#![crate_name = "helloworldsampleenclave"]
#![crate_type = "staticlib"]
#![cfg_attr(not(target_env = "sgx"), no_std)]
#![cfg_attr(target_env = "sgx", feature(rustc_private))]

extern crate sgx_types;
#[cfg(not(target_env = "sgx"))]
#[macro_use]
extern crate sgx_tstd as std;
mod types;
mod utils;

use sgx_rand::{Rng, StdRng};
use sgx_tseal::SgxSealedData;
use sgx_types::*;
use std::io::{self, Write};
use std::slice;
use std::string::String;
use std::vec::Vec;
use types::*;
use utils::*;

#[no_mangle]
pub extern "C" fn sample_task(sealed_log: *mut u8, sealed_log_size: u32) -> sgx_status_t {
    assert!(sealed_log_size == LOG_BUFFER_SIZE as u32);
    let selaed_buffer = unsafe {
        slice::from_raw_parts_mut(sealed_log, LOG_BUFFER_SIZE)
    };

    let sealed_data = SealedData::from_ref(selaed_buffer);
    let protected_enc_in = ProtectedAssets::new(sealed_data, vec![1], vec![1]);

    let protected_dec_in = protected_enc_in.decrypt();

    let protected_dec_out = protected_dec_in.invoke(&computation);

    let protected_enc_out = protected_dec_out.encrypt();

    let output = protected_enc_out.take();

    unsafe {std::ptr::copy(output.inner.as_ptr(), selaed_buffer.as_mut_ptr(), LOG_BUFFER_SIZE)}

    // let sealed_data =  SealedData::new(sealed_log as [u8; LOG_BUFFER_SIZE]);

    sgx_status_t::SGX_SUCCESS
}

fn computation(data: SealedData) -> SealedData {
    let mut new_data = SealedData::new([0u8; LOG_BUFFER_SIZE]);

    for i in 0..SEALED_DATA_SIZE {
        new_data.inner[i] = data.inner[i] + 1;
    }
    new_data
}


#[no_mangle]
pub extern "C" fn create_sealeddata_for_fixed(
    sealed_log: *mut u8,
    sealed_log_size: u32,
) -> sgx_status_t {
    let data = [42u8; 16];

    // commented to make the result deterministic
    // let mut rand = match StdRng::new() {
    //     Ok(rng) => rng,
    //     Err(_) => {
    //         return sgx_status_t::SGX_ERROR_UNEXPECTED;
    //     }
    // };
    // rand.fill_bytes(&mut data);

    let aad: [u8; 0] = [0_u8; 0];
    let result = SgxSealedData::<[u8; 16]>::seal_data(&aad, &data);
    let sealed_data = match result {
        Ok(x) => x,
        Err(ret) => {
            return ret;
        }
    };

    let opt = to_sealed_log_for_fixed(&sealed_data, sealed_log, sealed_log_size);
    if opt.is_none() {
        return sgx_status_t::SGX_ERROR_INVALID_PARAMETER;
    }

    println!("{:?}", data);

    sgx_status_t::SGX_SUCCESS
}

#[no_mangle]
pub extern "C" fn verify_sealeddata_for_fixed(
    sealed_log: *mut u8,
    sealed_log_size: u32,
) -> sgx_status_t {
    let opt = from_sealed_log_for_fixed::<[u8; 16]>(sealed_log, sealed_log_size);
    let sealed_data = match opt {
        Some(x) => x,
        None => {
            return sgx_status_t::SGX_ERROR_INVALID_PARAMETER;
        }
    };

    let result = sealed_data.unseal_data();
    let unsealed_data = match result {
        Ok(x) => x,
        Err(ret) => {
            return ret;
        }
    };

    let data = unsealed_data.get_decrypt_txt();

    println!("{:?}", data);

    sgx_status_t::SGX_SUCCESS
}
