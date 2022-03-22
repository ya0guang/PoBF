use mirai_annotations::*;

#[macro_export]
// Verifies that all the arguments are static
macro_rules! ocall {
    ($func:ident, $($invar:expr, $arg:expr),*) => {
        $ (
            verify!($invar == $arg);
        )*
        $func($($arg),*);
    };
}

#[macro_export]
macro_rules! ocall_log {
    ($formator:expr, $($invar:expr, $arg:expr),*) => {
        $ (
            verify!($invar == $arg);
        )*
        println!($formator, $($arg),*);
    };
}

#[allow(unused)]
pub fn log(s: &str) {
    println!("{}", s);
}

#[allow(unused)]
pub fn safe_log_str(s: &str, invs: &str) {
    precondition!(s.eq(invs));
    println!("{}", s);
}

#[allow(unused)]
pub fn safe_log_int(s: i32, invs: i32) {
    precondition!(s == invs);
    println!("{}", s);
}
