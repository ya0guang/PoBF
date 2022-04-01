#![forbid(unsafe_code)]

use crate::ocall::*;
use crate::{ocall_log, verified_log};
use std::vec::Vec;


pub fn vec_inc(input: Vec<u8>) -> Vec<u8> {
    let step = 1;
    // this can be proven true by MIRAI
    #[cfg(mirai)]
    mirai_annotations::verify!(mirai_annotations::does_not_have_tag!(&step, crate::types::SecretTaint));
    #[cfg(mirai)]
    verified_log!("The step is {} in computation_enc", 1, step);

    #[cfg(mirai)]
    mirai_annotations::verify!(mirai_annotations::does_not_have_tag!(&input, crate::types::SecretTaint));

    // mirai_annotations::add_tag!(&input, crate::types::SecretTaint);

    let mut output = Vec::new();
    for i in input.iter() {
        output.push(i + step);
    }

    // however, MIRAI complians about this
    // leakage violation: cannot log the secret data
    // captured by: MIRAI warnning
    #[cfg(mirai)]
    mirai_annotations::verify!(mirai_annotations::does_not_have_tag!(&output, crate::types::SecretTaint));
    #[cfg(mirai)]
    verified_log!("after increasing, the 0th data is {}", 1, output[0]);

    output
}
