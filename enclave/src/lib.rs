#![crate_name = "pobfref"]
#![crate_type = "staticlib"]
#![cfg_attr(feature = "sgx", no_std)]
#![feature(vec_into_raw_parts)]
#![feature(allocator_api)]

extern crate alloc;
extern crate base64;
extern crate clear_on_drop;
extern crate prusti_contracts;
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
mod verify_utils;

#[cfg(feature = "mirai")]
mod mirai_defs;
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
use prusti_contracts::*;
use sgx_types::error::SgxStatus;
use ra_utils::*;

use sgx_types::{error::SgxStatus, types::*};

use crate::dh::*;

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
    ocall_log!("[+] Start to perform remote attestation!");

    // Set peer.
    let pubkey: &[u8; 64] =
        unsafe { alloc::slice::from_raw_parts(public_key, public_key_len as usize) }
            .try_into()
            .unwrap();
    let pubkey_sign: &[u8] =
        unsafe { alloc::slice::from_raw_parts(pubkey_signature, pubkey_signature_len as usize) };

    let res = Peer::new(pubkey, pubkey_sign);
    if let Err(e) = res {
        ocall_log!("[-] Public key signature is invalid.");
        return e;
    }

    ocall_log!("[+] Peer authentication passed.");

    let mut peer = res.unwrap();
    peer.role = DhSessionRole::Initiator;

    // Step 0: Get the public key generated from the enclave.
    let res = dh::open_dh_session();
    if let Err(e) = res {
        return e;
    }
    ocall_log!("[+] enclave key pair OK!");

    let mut session = res.unwrap();

    // Compute the shared_key.
    let res = session.compute_shared_key(&peer);
    if let Err(e) = res {
        ocall_log!("{:?}", e);
        return e;
    }

    ocall_log!("[+] DH key sampled! {:?}", session);

    // Step 1: Ocall to get the target information and the EPID.
    let res = init_quote();
    if let Err(e) = res {
        return e;
    }

    let ti = res.unwrap().0;
    let eg = res.unwrap().1;

    // Step 2: Forward this information to the application which later forwards to service provider who later verifies the information with the help of the IAS.
    ocall_log!("[+] Start to get SigRL from Intel!");
    let res = get_sigrl_from_intel(&eg, socket_fd, session.session_context().pub_k());
    if let Err(e) = res {
        return e;
    }

    let sigrl_buf = res.unwrap();

    // Step 3: Generate the report.
    ocall_log!("[+] Start to perform report generation!");
    // Extract the ecc handle.
    let res = get_report(&ti, &session.session_context());
    if let Err(e) = res {
        return e;
    }

    let report = res.unwrap();

    // Step 4: Convert the report into a quote type.
    ocall_log!("[+] Start to perform quote generation!");
    let res = unsafe { get_quote(&sigrl_buf, &report, &*spid, linkable) };

    if let Err(e) = res {
        return e;
    }

    let qw = res.unwrap();
    let qe_report = &qw.qe_report;

    // Step 5: Verify this quote.
    let res = verify_report(qe_report);
    if let Err(e) = res {
        return e;
    }

    // Step 6: Check if the qe_report is produced on the same platform.
    if !same_platform(qe_report, &ti) {
        ocall_log!("[-] This quote report does belong to this platform.");
        return SgxStatus::UnrecognizedPlatform;
    }

    ocall_log!("[+] This quote is genuine for this platform.");

    // Step 7: Check if this quote is replayed.
    if !check_quote_integrity(&qw) {
        ocall_log!("[-] This quote is tampered by malicious party. Abort.");
        return SgxStatus::BadStatus;
    }

    ocall_log!("[+] The integrity of this quote is ok.");

    // Step 8: This quote is valid. Forward this quote to IAS.
    ocall_log!("[+] Start to get quote report from Intel!");
    let res = get_quote_report_from_intel(&qw, socket_fd);
    if let Err(e) = res {
        return e;
    }

    ocall_log!("[+] Successfully get quote report.");

    // Step 9: Verify this quote report: is this genuinely issues by Intel?
    ocall_log!("[+] Start to verify quote report!");
    let quote_triple = res.unwrap();
    let quote_report = quote_triple.0;
    let sig = quote_triple.1;
    let cert = quote_triple.2;

    if !verify_quote_report(&quote_report, &sig, &cert) {
        ocall_log!("[-] This quote report is tampered by malicious party. Abort.");
        return SgxStatus::BadStatus;
    }

    ocall_log!("[+] Signature is valid!");

    // Step 10: Seal the report on the computer.
    ocall_log!("[+] Sealing the report!");
    let res = seal_attestation_report(&quote_report);

    if let Err(e) = res {
        ocall_log!("[-] Cannot seal the report.");
        return e;
    }

    ocall_log!("[+] Remote attestation completed! Enjoy :)");

    SgxStatus::Success
}
