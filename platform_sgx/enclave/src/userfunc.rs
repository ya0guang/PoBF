#![forbid(unsafe_code)]

use alloc::vec::Vec;
#[cfg(mirai)]
use mirai_annotations::*;

#[cfg(mirai)]
use crate::mirai_types::mirai_comp::SecretTaint;
use crate::{log, ocall_log, println};

/// A sample function used to serve as the target task for MIRAI.
/// In order to verify that user function is correct, we need to temporarily move it to
/// the enclave crate.
pub fn sample_add(input: Vec<u8>) -> Vec<u8> {
    let step = 1;

    // this can be proven true by MIRAI
    #[cfg(feature = "leak_log")]
    {
        println!("The 0-th item is {} in sample_add", input[0]);
    }

    let mut output = Vec::new();
    for i in 0..input.len() {
        output.push(step + input[i]);
    }

    #[cfg(mirai)]
    add_tag!(&output, SecretTaint);

    output
}
