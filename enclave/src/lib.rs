#![crate_name = "pobfref"]
#![crate_type = "staticlib"]
#![cfg_attr(feature = "sgx", no_std)]
#![feature(vec_into_raw_parts)]

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
use ocall::*;
use pobf::*;
#[cfg(feature = "sgx")]
use sgx_tseal::seal::SealedData;
use sgx_types::error::SgxStatus;
use std::slice;

#[no_mangle]
pub extern "C" fn private_computing_entry(
    sealed_key_ptr: *mut u8,
    sealed_key_size: u32,
    encrypted_input_ptr: *mut u8,
    encrypted_input_size: u32,
    encrypted_output_buffer_ptr: *mut u8,
    encrypted_output_buffer_size: u32,
    encrypted_output_size: *mut u32,
) -> SgxStatus {
    verified_log!("[+] private_computing_entry",);

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
        return SgxStatus::Unexpected;
    }

    let encrypted_output_buffer = unsafe {
        slice::from_raw_parts_mut(encrypted_output_buffer_ptr, encrypted_output_buffer_size)
    };
    encrypted_output_buffer[..encrypted_output_length].copy_from_slice(encrypted_output_slice);
    SgxStatus::Success
}

#[no_mangle]
pub extern "C" fn generate_sealed_key(
    sealed_key_ptr: *mut u8,
    sealed_key_buffer_size: u32,
    sealed_key_size: *mut u32,
) -> SgxStatus {
    println!("[+] Generating sealed data...");
    let data = [0u8; 16];

    // uncomment to get random result
    // let mut rand = match StdRng::new() {
    //     Ok(rng) => rng,
    //     Err(_) => {
    //         return SgxStatus::Unexpected;
    //     }
    // };
    // rand.fill_bytes(&mut data);

    let result = SealedData::<[u8; 16]>::seal(&data, None);
    let sealed_key = match result {
        Ok(x) => x,
        Err(ret) => {
            return ret;
        }
    };

    if sealed_key_buffer_size < sealed_key.payload_size() as u32 {
        return SgxStatus::Unexpected;
    }

    let sealed_key_bytes = match sealed_key.to_bytes() {
        Ok(x) => x,
        Err(_) => return SgxStatus::Unexpected,
    };

    // prepare output buffer
    unsafe {
        std::ptr::copy_nonoverlapping(
            sealed_key_bytes.as_ptr(),
            sealed_key_ptr,
            sealed_key_bytes.len(),
        );
    }
    unsafe {
        std::ptr::write(sealed_key_size, sealed_key_bytes.len() as u32);
    }

    SgxStatus::Success
}
