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
mod userfunc;
mod utils;
mod vecaes;

use alloc::slice;
use clear_on_drop::clear_stack_and_regs_on_return;
use ocall::*;
use pobf::*;

use sgx_types::{error::SgxStatus, types::*};

use crate::{dh::*, vecaes::VecAESData};

static DEFAULT_PAGE_SIZE_ENTRY: usize = 0x4;
static DEFAULT_PAGE_SIZE_LEAF: usize = 0x1;

#[no_mangle]
pub extern "C" fn private_computing_entry(
    socket_fd: c_int,
    spid_ptr: *const Spid,
    linkable: i64,
    public_key_ptr: *const u8,
    public_key_len: u32,
    signature_ptr: *const u8,
    signature_len: u32,
    encrypted_output_buffer_ptr: *mut u8,
    encrypted_output_buffer_size: u32,
    encrypted_output_size: *mut u32,
) -> SgxStatus {
    ocall_log!("[+] private_computing_entry");

    // Construct Rust data structures from FFI-types.
    let spid = unsafe { &*spid_ptr };
    let public_key: &[u8; ECP_COORDINATE_SIZE] =
        unsafe { slice::from_raw_parts(public_key_ptr, public_key_len as usize) }
            .try_into()
            .unwrap();
    let signature = unsafe { slice::from_raw_parts(signature_ptr, signature_len as usize) };

    let result = pobf_workflow(socket_fd, spid, linkable, public_key, signature);

    // Copy the result back to the outside world.
    unsafe {
        core::ptr::copy(
            result.as_ref().as_ptr(),
            encrypted_output_buffer_ptr,
            result.as_ref().len(),
        );

        *encrypted_output_size = result.as_ref().len() as u32;
    }

    // Remote attestation callback.
    // let remote_attestation_callback =
    //     || pobf_remote_attestation(socket_fd, spid, linkable, public_key, signature);
    // let receive_data_callback = || pobf_receive_data(socket_fd);
    // PoBF main entry callback.
    // let pobf_private_computing_callback = || {
    //     pobf_private_computing(
    //         encrypted_input,
    //         sealed_key,
    //         &remote_attestation_callback,
    //         &receive_data_callback,
    //     )
    // };
    // let res =
    //     clear_stack_and_regs_on_return(DEFAULT_PAGE_SIZE_ENTRY, pobf_private_computing_callback);

    // let encrypted_output = match res {
    //     Ok(x) => x,
    //     Err(e) => {
    //         println!("Error occurs when invoking pobf_sample_task_aaes");
    //         return e;
    //     }
    // };

    // let encrypted_output_buffer_size = encrypted_output_buffer_size as usize;
    // let encrypted_output_slice = encrypted_output.as_ref();
    // let encrypted_output_length = encrypted_output_slice.len();
    // unsafe {
    //     core::ptr::write(encrypted_output_size, encrypted_output_length as u32);
    // }
    // if encrypted_output_length > encrypted_output_buffer_size {
    //     return SgxStatus::Unexpected;
    // }

    // let encrypted_output_buffer = unsafe {
    //     slice::from_raw_parts_mut(encrypted_output_buffer_ptr, encrypted_output_buffer_size)
    // };
    // encrypted_output_buffer[..encrypted_output_length].copy_from_slice(encrypted_output_slice);
    SgxStatus::Success
}

/// To be deprecated.
#[allow(unused)]
#[no_mangle]
pub extern "C" fn start_remote_attestation(
    socket_fd: c_int,
    spid: *const Spid,
    linkable: i64,
    public_key: *const u8,
    public_key_len: u32,
    pubkey_signature: *const u8,
    pubkey_signature_len: u32,
) -> SgxStatus {
    // Convert FFI-types to Rust-types.
    let r_spid = unsafe { &*spid };
    let r_public_key: &[u8; ECP_COORDINATE_SIZE] =
        unsafe { core::slice::from_raw_parts(public_key, public_key_len as usize) }
            .try_into()
            .unwrap();
    let r_signature =
        unsafe { core::slice::from_raw_parts(pubkey_signature, pubkey_signature_len as usize) };

    let _ = pobf_remote_attestation(socket_fd, r_spid, linkable, r_public_key, r_signature);

    SgxStatus::Success
}
