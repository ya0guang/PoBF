#![crate_name = "helloworldsampleenclave"]
#![crate_type = "staticlib"]
#![cfg_attr(not(target_env = "sgx"), no_std)]
#![cfg_attr(target_env = "sgx", feature(rustc_private))]

extern crate sgx_types;
#[cfg(not(target_env = "sgx"))]
#[macro_use]
extern crate sgx_tstd as std;
mod pobf;
mod types;
mod utils;

// use sgx_rand::{Rng, StdRng};
use pobf::*;
use sgx_tseal::SgxSealedData;
use sgx_types::*;
use std::slice;
use types::*;
use utils::*;

#[no_mangle]
pub extern "C" fn sample_task(sealed_log: *mut u8, sealed_log_size: u32) -> sgx_status_t {
    assert!(sealed_log_size == BUFFER_SIZE as u32);
    let sealed_buffer = unsafe { slice::from_raw_parts_mut(sealed_log, BUFFER_SIZE) };

    let sealed_data = SealedData::from_ref(sealed_buffer);

    let sealed_output = pobf_ref_implementation(sealed_data, vec![0], vec![0], &computation_sealed);

    sealed_buffer.copy_from_slice(sealed_output.inner.as_ref());

    sgx_status_t::SGX_SUCCESS
}

// TODO: reform the size field!
#[no_mangle]
pub extern "C" fn sample_task_aes(
    sealed_key_log: *mut u8,
    sealed_key_log_size: u32,
    encrypted_data: *mut u8,
    encrypted_data_size: u32,
    encrypted_data_mac: *mut u8,
) -> sgx_status_t {
    assert!(sealed_key_log_size == BUFFER_SIZE as u32);
    assert!(encrypted_data_size <= BUFFER_SIZE as u32);
    let sealed_key_buffer = unsafe { slice::from_raw_parts_mut(sealed_key_log, BUFFER_SIZE) };

    let data_buffer = unsafe { slice::from_raw_parts_mut(encrypted_data, BUFFER_SIZE) };
    let data_mac = unsafe { slice::from_raw_parts_mut(encrypted_data_mac, SGX_AESGCM_MAC_SIZE) };
    let data = EncData::from_ref(data_buffer, data_mac, encrypted_data_size as usize);

    let input_key: AES128Key = key_from_sealed_buffer(sealed_key_buffer);
    let output_key: AES128Key = input_key.clone();

    let encrypted_output = pobf_ref_implementation(
        data,
        input_key,
        output_key,
        &computation_enc,
    );

    data_buffer.copy_from_slice(encrypted_output.inner.as_ref());
    data_mac.copy_from_slice(encrypted_output.mac.as_ref());

    sgx_status_t::SGX_SUCCESS
}

#[no_mangle]
pub extern "C" fn create_sealeddata_for_fixed(
    sealed_log: *mut u8,
    sealed_log_size: u32,
) -> sgx_status_t {
    let data = [0u8; 16];

    // uncomment to get random result
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
