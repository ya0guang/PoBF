#![crate_name = "pobfref"]
#![crate_type = "staticlib"]
#![cfg_attr(feature = "sgx", no_std)]
#![feature(vec_into_raw_parts)]
#![feature(allocator_api)]

extern crate alloc;
extern crate clear_on_drop;
extern crate prusti_contracts;
#[cfg(feature = "sgx")]
extern crate sgx_no_tstd;
extern crate sgx_types;

#[cfg(not(feature = "sgx"))]
mod bogus;
mod verify_utils;

#[cfg(feature = "mirai")]
mod mirai_defs;
mod ocall;
mod pobf;
mod pobf_verifier;
mod types;
mod userfunc;
mod utils;

use alloc::slice;
use clear_on_drop::clear_stack_and_regs_on_return;
use ocall::*;
use pobf::*;
use prusti_contracts::*;
use sgx_types::error::SgxStatus;

static DEFAULT_PAGE_SIZE_ENTRY: usize = 0x4;
static DEFAULT_PAGE_SIZE_LEAF: usize = 0x1;

#[no_mangle]
#[trusted]
pub extern "C" fn private_computing_entry(
    sealed_key_ptr: *mut u8,
    sealed_key_size: u32,
    encrypted_input_ptr: *mut u8,
    encrypted_input_size: u32,
    encrypted_output_buffer_ptr: *mut u8,
    encrypted_output_buffer_size: u32,
    encrypted_output_size: *mut u32,
) -> SgxStatus {
    ocall_log!("[+] private_computing_entry");

    let sealed_key = unsafe { slice::from_raw_parts_mut(sealed_key_ptr, sealed_key_size as usize) };

    let encrypted_input =
        unsafe { slice::from_raw_parts_mut(encrypted_input_ptr, encrypted_input_size as usize) };

    let f = || pobf_private_computing(encrypted_input, sealed_key);
    let res = clear_stack_and_regs_on_return(DEFAULT_PAGE_SIZE_LEAF, f);

    let encrypted_output = match res {
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
        core::ptr::write(encrypted_output_size, encrypted_output_length as u32);
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
