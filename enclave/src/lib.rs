#![crate_name = "pobfref"]
#![crate_type = "staticlib"]
#![cfg_attr(feature = "sgx", no_std)]
#![feature(vec_into_raw_parts)]
#![feature(allocator_api)]

extern crate alloc;
extern crate base64;
extern crate clear_on_drop;
extern crate percent_encoding;
#[cfg(feature = "sgx")]
extern crate sgx_no_tstd;
extern crate sgx_trts;
extern crate sgx_tse;
extern crate sgx_tseal;
extern crate sgx_types;
extern crate webpki;

#[cfg(not(feature = "sgx"))]
mod bogus;
mod dh;
mod ocall;
mod pobf;
mod pobf_verifier;
mod ra_utils;
mod types;
mod userfunc;
mod utils;

use alloc::slice;
use clear_on_drop::clear_stack_and_regs_on_return;
use ocall::*;
use pobf::*;
use ra_utils::*;

use sgx_types::{error::SgxStatus, types::*};

use crate::dh::*;

static DEFAULT_PAGE_SIZE_ENTRY: usize = 0x4;
static DEFAULT_PAGE_SIZE_LEAF: usize = 0x1;

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
    ocall_log!("[+] private_computing_entry");

    let sealed_key = unsafe { slice::from_raw_parts_mut(sealed_key_ptr, sealed_key_size as usize) };

    let encrypted_input =
        unsafe { slice::from_raw_parts_mut(encrypted_input_ptr, encrypted_input_size as usize) };

    let f = || pobf_private_computing(encrypted_input, sealed_key);
    let res = clear_stack_and_regs_on_return(DEFAULT_PAGE_SIZE_ENTRY, f);

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

#[no_mangle]
pub extern "C" fn start_remote_attestation(
    socket_fd: i32,
    spid: *const Spid,
    linkable: i64,
    public_key: *const u8,
    public_key_len: u32,
    pubkey_signature: *const u8,
    pubkey_signature_len: u32,
) -> SgxStatus {
    // Convert FFI-types to Rust-types.
    let r_spid = unsafe { &*spid };
    let r_public_key: &[u8; 64] =
        unsafe { core::slice::from_raw_parts(public_key, public_key_len as usize) }
            .try_into()
            .unwrap();
    let r_signature =
        unsafe { core::slice::from_raw_parts(pubkey_signature, pubkey_signature_len as usize) };

    let _ = remote_attestation_callback(socket_fd, r_spid, linkable, r_public_key, r_signature);

    SgxStatus::Success
}
