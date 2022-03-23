#![forbid(unsafe_code)]
#![allow(unused_imports)]
#[cfg(not(feature = "sgx"))]
use mirai_annotations::*;

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
macro_rules! ocall_log {
    ($formator:expr, $($invar:expr, $arg:expr),*) => {
        $ (
            #[cfg(not(feature = "sgx"))]
            mirai_annotations::verify!($invar == $arg);
        )*
        println!($formator, $($arg),*);
    };
}
