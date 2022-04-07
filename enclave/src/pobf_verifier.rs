#![forbid(unsafe_code)]

pub use crate::ocall::*;
pub use crate::ocall_log;
#[cfg(not(mirai))]
pub use crate::println;
#[cfg(mirai)]
pub use mirai_annotations::*;
