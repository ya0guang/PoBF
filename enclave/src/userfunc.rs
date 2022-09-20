#![forbid(unsafe_code)]
#[allow(unused_imports)]
#[cfg(feature = "use_prusti")]
use crate::{pobf_verifier::*, verify_utils::*};
use alloc::vec::Vec;
#[cfg(feature = "use_prusti")]
use prusti_contracts::*;

#[cfg(not(feature = "use_prusti"))]
pub fn vec_inc(input: Vec<u8>) -> Vec<u8> {
    let step = 1;

    // this can be proven true by MIRAI
    #[cfg(feature = "leak_log")]
    {
        println!("The step is {} in computation_enc", step);
    }

    let mut output = Vec::new();
    for i in input.iter() {
        output.push(i + step);
    }

    // however, MIRAI complians about this
    // leakage violation: cannot log the secret data
    // captured by: MIRAI warnning
    #[cfg(feature = "leak_log")]
    {
        #[cfg(mirai)]
        verify!(output[0] == 1);
        println!("after increasing, the 0th data is {}", output[0]);
    }

    // safety violation: cannot leak out secret data through network stream write
    // captured by: compiler error
    #[cfg(feature = "leak_net")]
    {
        use std::net::TcpStream;
        match TcpStream::connect("localhost:10086") {
            Ok(mut stream) => {
                stream.write(&output).unwrap();
            }
            _ => {
                println!("failed to connect to server");
            }
        }
    }

    // safety violation: cannot leak out secret data through file write
    // captured by: compiler error
    #[cfg(feature = "leak_file")]
    {
        use std::fs::File;
        let mut file = File::create("./leaked.txt").unwrap();
        file.write_all(&output).unwrap();
    }

    output
}

/// A sample user function that copy each element in the given vector.
/// This is an equivalent version used to verify the above function's correctness.
#[cfg(feature = "use_prusti")]
#[requires(input.tainted())]
// Prevent verification failure on overflow.
#[requires(forall(
	|i: usize| 0 <= i && i < input.len() ==>
		0 <= *input.lookup(i) && *input.lookup(i) + step <= u8::MAX
))]
#[ensures(input.len() == result.len())]
#[ensures(forall(
	|i: usize| (0 <= i && i < input.len()) ==>
		*input.lookup(i) + step == *result.lookup(i)
))]
#[ensures((&result).tainted())]
#[allow(unused)]
pub fn vec_play(input: &VecWrapperU8, step: u8) -> VecWrapperU8 {
    let mut output = VecWrapperU8::new();

    let mut i = 0usize;
    while i < input.len() {
        body_invariant!(0 <= i && i < input.len());
        body_invariant!(output.len() == i);
        body_invariant!(output.len() <= input.len());
        body_invariant!(*input.lookup(i) + step <= u8::MAX);
        body_invariant!(forall (
            |j: usize| (0 <= j && j < output.len()) ==>
                *input.lookup(j) + step == *output.lookup(j)
        ));
        body_invariant!((&output).tainted() && (&input).tainted());

        output.push(*input.index(i) + step);
        i += 1;
    }

    // Safety violation: Leak log.
    // The function tries to log a sensitive data to the outside.
    // Captured by Prusti verification failure.
    // note: the failing assertion is here
    //    --> src/verify_utils.rs:113:16
    //    |
    // 113 |     #[requires(!(&self).tainted())]
    //    |                ^^^^^^^^^^^^^^^^^^
    #[cfg(feature = "leak_log")]
    {
        input.log_index(0);
    }

    // Safety violation: cannot leak out secret data through network stream write
    // captured by: compiler error
    #[cfg(feature = "leak_net")]
    {
        input.send_to_network("localhost:10086");
    }
    
    // Safety violation: cannot leak out secret data through network stream write
    // captured by: compiler error
    #[cfg(feature = "leak_file")]
    {
        input.write_to_file("./leaked.txt");
    }

    output
}
