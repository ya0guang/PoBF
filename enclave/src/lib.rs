#![crate_name = "helloworldsampleenclave"]
#![crate_type = "staticlib"]
#![cfg_attr(feature = "sgx", no_std)]
#![cfg_attr(target_env = "sgx", feature(rustc_private))]

extern crate sgx_types;
#[cfg(feature = "sgx")]
#[cfg(not(target_env = "sgx"))]
#[macro_use]
extern crate sgx_tstd as std;
#[cfg(not(feature = "sgx"))]
mod bogus;
mod ocall;
mod pobf;
mod types;
mod utils;

#[cfg(not(feature = "sgx"))]
use bogus::*;
use pobf::*;
#[cfg(feature = "sgx")]
use sgx_tseal::SgxSealedData;
use sgx_types::*;
use std::slice;
use types::*;
use utils::*;

#[no_mangle]
pub extern "C" fn private_computing_entry(
    sealed_buffer_ptr: *mut u8,
    sealed_buffer_size: u32,
    encrypted_data_ptr: *mut u8,
    encrypted_data_size: u32,
) -> sgx_status_t {
    assert!(sealed_buffer_size == BUFFER_SIZE as u32);
    assert!(encrypted_data_size <= BUFFER_SIZE as u32);

    let sealed_key = unsafe { slice::from_raw_parts_mut(sealed_buffer_ptr, BUFFER_SIZE) };

    let encrypted_data =
        unsafe { slice::from_raw_parts_mut(encrypted_data_ptr, encrypted_data_size as usize) };

    let encrypted_output = match pobf_private_computing(encrypted_data, sealed_key) {
        Ok(x) => x,
        Err(e) => {
            println!("Error occurs when invoking pobf_sample_task_aaes");
            return e;
        }
    };

    // append mac to the buffer
    encrypted_data.copy_from_slice(encrypted_output.inner.as_ref());

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
