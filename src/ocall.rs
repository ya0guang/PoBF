use mirai_annotations::*;

#[macro_export]
macro_rules! ocall {
    ($func:ident, $invar:expr, $arg:expr) => {
        verify!($invar == $arg);
        $func($arg);
    };
}

pub fn log(s: &str) {
    println!("{}", s);
}

pub fn safe_log_str(s: &str, invs: &str) {
    precondition!(s.eq(invs));
    println!("{}", s);
}

pub fn safe_log_int(s: i32, invs: i32) {
    precondition!(s == invs);
    println!("{}", s);
}