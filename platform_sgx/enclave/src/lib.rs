#![allow(unused)]
#![crate_name = "pobfref"]
#![crate_type = "staticlib"]
#![cfg_attr(feature = "sgx", no_std)]
#![feature(vec_into_raw_parts)]
#![feature(allocator_api)]

extern crate alloc;
extern crate base64;
extern crate clear_on_drop;
extern crate mirai_annotations;
extern crate percent_encoding;
#[cfg(all(feature = "sgx", not(mirai)))]
extern crate sgx_no_tstd;
extern crate sgx_trts;
extern crate sgx_tse;
extern crate sgx_tseal;
extern crate sgx_types;
extern crate webpki;

#[cfg(not(feature = "sgx"))]
mod bogus;
mod dh;
#[cfg(mirai)]
mod mirai_types;
mod networking_utils;
mod ocall;
mod pobf;
mod pobf_verifier;
mod userfunc;
mod utils;
mod vecaes;

#[cfg(feature = "task_db")]
mod db_persistent;

use alloc::slice;
use clear_on_drop::*;
use ocall::*;
use pobf::*;
use zeroize::*;

use sgx_types::{error::SgxStatus, types::*};

use crate::dh::*;

static DEFAULT_PAGE_SIZE_LEAF: usize = 0x20;

#[no_mangle]
pub extern "C" fn private_computing_entry(
    socket_fd: c_int,
    spid_ptr: *const Spid,
    linkable: i64,
    ra_type: u8,
    public_key_ptr: *const u8,
    public_key_len: u32,
    signature_ptr: *const u8,
    signature_len: u32,
    encrypted_output_buffer_ptr: *mut u8,
    encrypted_output_buffer_size: u32,
    encrypted_output_size: *mut u32,
    stack: u16,
) -> SgxStatus {
    #[cfg(feature = "task_db")]
    db::DUMPER.call_once(|| alloc::boxed::Box::new(crate::db_persistent::SgxPersistentLayer));

    verified_log!("[+] private_computing_entry");
    cfg_if::cfg_if! {
        if #[cfg(feature = "native_enclave")] {
            verified_log!("[+] Running ephemeral enclave!");
        } else {
            verified_log!("[+] Running persistent PoBF enclave!");
        }
    }

    // Construct Rust data structures from FFI-types.
    let spid = unsafe { &*spid_ptr };
    let public_key: &[u8; ECP_COORDINATE_SIZE] =
        unsafe { slice::from_raw_parts(public_key_ptr, public_key_len as usize) }
            .try_into()
            .unwrap();
    let signature = unsafe { slice::from_raw_parts(signature_ptr, signature_len as usize) };

    let mut result = pobf_workflow(
        socket_fd, spid, linkable, ra_type, public_key, signature, stack,
    );

    let output_size = result.as_ref().len() as u32;
    let rv = if output_size <= encrypted_output_buffer_size {
        // Copy the result back to the outside world.
        unsafe {
            core::ptr::copy(
                result.as_ref().as_ptr(),
                encrypted_output_buffer_ptr,
                result.as_ref().len(),
            );

            *encrypted_output_size = output_size;
        }
        SgxStatus::Success
    } else {
        SgxStatus::InvalidParameter
    };

    // Clear result.
    result.zeroize();
    rv
}

/// To be deprecated.
#[allow(unused)]
#[no_mangle]
#[deprecated]
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

    let _ = pobf_remote_attestation(socket_fd, r_spid, linkable, 0, r_public_key, r_signature);

    SgxStatus::Success
}

/// Built with debug mode.
#[cfg(debug_assertions)]
#[no_mangle]
pub fn __assert_fail() {}
