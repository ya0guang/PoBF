#![crate_name = "pobfref"]
#![crate_type = "staticlib"]
#![cfg_attr(feature = "sgx", no_std)]

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
    sealed_key_ptr: *mut u8,
    sealed_key_size: u32,
    encrypted_input_ptr: *mut u8,
    encrypted_input_size: u32,
    encrypted_output_buffer_ptr: *mut u8,
    encrypted_output_buffer_size: u32,
    encrypted_output_size: *mut u32,
) -> sgx_status_t {
    assert!(sealed_key_size == BUFFER_SIZE as u32);

    let sealed_key = unsafe { slice::from_raw_parts_mut(sealed_key_ptr, sealed_key_size as usize) };

    let encrypted_input =
        unsafe { slice::from_raw_parts_mut(encrypted_input_ptr, encrypted_input_size as usize) };

    let encrypted_output = match pobf_private_computing(encrypted_input, sealed_key) {
        Ok(x) => x,
        Err(e) => {
            println!("Error occurs when invoking pobf_sample_task_aaes");
            return e;
        }
    };

    let encrypted_output_buffer_size = encrypted_output_buffer_size as usize;
    let encrypted_output_slice = encrypted_output.as_ref();
    let encrypted_output_length = encrypted_output_slice.len();
    unsafe {
        std::ptr::write(encrypted_output_size, encrypted_output_length as u32);
    }
    if encrypted_output_length > encrypted_output_buffer_size {
        return sgx_status_t::SGX_ERROR_UNEXPECTED;
    }

    let encrypted_output_buffer = unsafe {
        slice::from_raw_parts_mut(encrypted_output_buffer_ptr, encrypted_output_buffer_size)
    };
    encrypted_output_buffer[..encrypted_output_length].copy_from_slice(encrypted_output_slice);
    sgx_status_t::SGX_SUCCESS
}

#[no_mangle]
pub extern "C" fn generate_sealed_key(
    sealed_log_ptr: *mut u8,
    sealed_log_size: u32,
) -> sgx_status_t {

    println!("[+] Generating sealed data...");
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

    let opt = to_sealed_log_for_fixed(&sealed_data, sealed_log_ptr, sealed_log_size);
    if opt.is_none() {
        return sgx_status_t::SGX_ERROR_INVALID_PARAMETER;
    }

    sgx_status_t::SGX_SUCCESS
}
