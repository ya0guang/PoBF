use alloc::vec::Vec;
use mirai_annotations::*;

use crate::{log, mirai_types::mirai_comp::SecretTaint, ocall_log, println};

/// A sample function used to serve as the target task for MIRAI.
pub fn sample_add(input: Vec<u8>) -> Vec<u8> {
    precondition!(has_tag!(&input, SecretTaint));

    let step = 1;

    // this can be proven true by MIRAI
    #[cfg(feature = "leak_log")]
    {
        #[cfg(feature = "mirai")]
        verify!(does_not_have_tag!(&input, SecretTaint));
        println!("The step is {} in computation_enc", input[0]);
    }

    let mut output = Vec::new();
    for i in 0..input.len() {
        output.push(step + input[i]);
    }
    
    add_tag!(&output, SecretTaint);
    postcondition!(has_tag!(&output, SecretTaint));
    output
}
