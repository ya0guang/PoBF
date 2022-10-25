#![allow(unused_imports)]
#[cfg(not(feature = "sgx"))]
use mirai_annotations::*;

use alloc::string::String;
use libc::{c_char, ssize_t};
use sgx_libc as libc;
use sgx_types::{error::SgxStatus, types::*};

extern "C" {
    fn u_log_ocall(
        result: *mut u32,
        string_ptr: *mut u8,
        string_len: u32,
        string_capacity: u32,
    ) -> SgxStatus;

    pub fn ocall_sgx_init_quote(
        ret_val: *mut SgxStatus,
        ret_ti: *mut TargetInfo,
        ret_gid: *mut EpidGroupId,
    ) -> SgxStatus;

    pub fn ocall_get_sigrl_from_intel(
        ret_val: *mut SgxStatus,
        epid: *const EpidGroupId,
        epid_len: usize,
        socket_fd: c_int,
        sigrl: *mut u8,
        len: u32,
        sigrl_len: *mut u32,
        enclave_pub_key: *const u8,
        enclave_pub_key_len: u32,
    ) -> SgxStatus;

    pub fn ocall_get_quote(
        ret_val: *mut SgxStatus,
        p_sigrl: *const u8,
        sigrl_len: u32,
        p_report: *const Report,
        quote_type: QuoteSignType,
        p_spid: *const Spid,
        p_nonce: *const QuoteNonce,
        p_qe_report: *mut Report,
        p_quote: *mut u8,
        maxlen: u32,
        p_quote_len: *mut u32,
    ) -> SgxStatus;

    pub fn ocall_get_quote_report_from_intel(
        ret_val: *mut SgxStatus,
        socket_fd: c_int,
        quote_buf: *const u8,
        quote_len: u32,
        quote_report: *mut u8,
        quote_report_buf_len: u32,
        quote_report_len: *mut u32,
        sig: *mut u8,
        sig_buf_len: u32,
        sig_len: *mut u32,
        cert: *mut u8,
        cert_buf_len: u32,
        cert_len: *mut u32,
    ) -> SgxStatus;

    pub fn ocall_get_timepoint(ret_val: *mut SgxStatus, time_point: *mut u64) -> SgxStatus;

    pub fn ocall_receive_data(
        ret_val: *mut SgxStatus,
        socket_fd: c_int,
        data_buf: *mut u8,
        data_buf_len: u32,
        data_size: *mut u32,
    ) -> SgxStatus;

    pub fn ocall_write_data(
        ret_val: *mut SgxStatus,
        path: *const u8,
        path_size: u32,
        data: *const u8,
        data_size: u32,
    ) -> SgxStatus;

    pub fn ocall_read_data(
        ret_val: *mut SgxStatus,
        path: *const u8,
        path_size: u32,
        data: *mut u8,
        data_buf_size: u32,
        data_size: *mut u32,
    ) -> SgxStatus;
}

pub fn log(s: String) -> SgxStatus {
    let mut rv: u32 = 0;
    let (string_ptr, len, cap) = s.into_raw_parts();
    let result = unsafe { u_log_ocall(&mut rv as _, string_ptr as _, len as _, cap as _) };
    // automatic Rust drop
    let _ = unsafe { alloc::string::String::from_raw_parts(string_ptr, len, cap) };
    result
}

// Verifies that all the arguments are static
#[macro_export]
macro_rules! ocall {
    ($func:ident, $($invar:expr, $arg:expr),*) => {
        $ (
            #[cfg(not(feature = "sgx"))]
            mirai_annotations::verify!($invar == $arg);
        )*
        $func($($arg),*);
    };
}

#[macro_export]
macro_rules! ocall_print {
    ($formator:expr, $($invar:expr, $arg:expr),*) => {
        $ (
            #[cfg(not(feature = "sgx"))]
            mirai_annotations::verify!($invar == $arg);
        )*
        println!($formator, $($arg),*);
    };
}

#[macro_export]
macro_rules! ocall_log {
    ($str: expr) => {
        let s = alloc::format!($str);
        log(s)
    };
    ($formator:expr, $($arg:expr),+ $(,)?) => {

        let s = alloc::format!($formator, $($arg),+);
        log(s)
    };
}

#[macro_export]
macro_rules! println {
    () => {
        log(alloc::string::String::from("[user function output]"));
        ocall_log!("\n")
    };
    ($($arg:expr),+ $(,)? ) => {
        log(alloc::string::String::from("[user function output]"));
        ocall_log!($($arg),+);
    }
}

#[macro_export]
macro_rules! verified_log {
    ($str:expr) => {
        ocall_log!($str);
    };
    ($formator:expr, $($invar:expr, $arg:expr),+ $(,)?) => {
        $ (
            #[cfg(not(feature = "sgx"))]
            mirai_annotations::verify!($invar == $arg);
        )*
        ocall_log!($formator, $($arg),+);
    };
}
