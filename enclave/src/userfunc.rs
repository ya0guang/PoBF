#![forbid(unsafe_code)]

use crate::ocall::*;
use crate::{ocall_log, verified_log};
use std::vec::Vec;

pub fn vec_inc(input: Vec<u8>) -> Vec<u8> {
    let step = 1;
    // this can be proven true by MIRAI
    verified_log!("The step is {} in computation_enc", 1, step);

    let mut output = Vec::new();
    for i in input.iter() {
        output.push(i + step);
    }

    // however, MIRAI complians about this
    // leakage violation: cannot log the secret data
    // captured by: MIRAI warnning
    #[cfg(mirai)]
    verified_log!("after increasing, the 0th data is {}", 1, output[0]);

    output
}
