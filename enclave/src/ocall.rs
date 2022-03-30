#![allow(unused_imports)]
#[cfg(not(feature = "sgx"))]
use mirai_annotations::*;

use libc::{c_char, ssize_t};
use sgx_libc as libc;
use sgx_types::error::SgxStatus;
use std::string::String;

extern "C" {
    pub fn u_log_ocall(
        result: *mut u32,
        string_ptr: *mut u8,
        string_len: u32,
        string_capacity: u32,
    ) -> SgxStatus;
}

pub fn log(s: String) -> SgxStatus {
    let mut rv: u32 = 0;
    let (string_ptr, len, cap) = s.into_raw_parts();
    let result = unsafe { u_log_ocall(&mut rv as _, string_ptr as _, len as _, cap as _) };
    // for memory deallocation
    let _ = unsafe { String::from_raw_parts(string_ptr, len, cap) };
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
    ($formator:expr, $($arg:expr),*) => {

        let s = format!($formator, $($arg),*);
        log(s)
    };
}

#[macro_export]
macro_rules! verified_log {
    ($formator:expr, $($invar:expr, $arg:expr),*) => {
        $ (
            #[cfg(not(feature = "sgx"))]
            mirai_annotations::verify!($invar == $arg);
        )*
        ocall_log!($formator, $($arg),*)
    };
}
