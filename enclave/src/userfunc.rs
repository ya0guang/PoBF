#![forbid(unsafe_code)]

use crate::pobf_verifier::*;
use std::vec::Vec;

pub fn vec_inc(input: Vec<u8>) -> Vec<u8> {
    let step = 1;

    // this can be proven true by MIRAI
    println!("The step is {} in computation_enc", step);

    let mut output = Vec::new();
    for i in input.iter() {
        output.push(i + step);
    }

    // however, MIRAI complians about this
    // leakage violation: cannot log the secret data
    // captured by: MIRAI warnning
    println!("after increasing, the 0th data is {}", output[0]);

    output
}
