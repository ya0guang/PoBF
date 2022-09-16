#![forbid(unsafe_code)]

use crate::pobf_verifier::*;
#[cfg(feature = "use_prusti")]
use crate::verify_utils::*;
use alloc::vec::Vec;
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

/// A sample user function that increment each element in the given vector.
/// This is an equivalent version used to verify the above function's correctness.
#[cfg(feature = "use_prusti")]
#[ensures(input.len() == result.len())]
#[ensures(forall(
	|i: usize| (0 <= i && i < input.len()) ==>
		*input.lookup(i)== *result.lookup(i)
))]
pub fn vec_play(input: &VecWrapperU8) -> VecWrapperU8 {
    let mut output = VecWrapperU8::new();

    let mut i = 0usize;
    while i < input.len() {
        body_invariant!(0 <= i && i < input.len());
        body_invariant!(output.len() == i);
        body_invariant!(output.len() <= input.len());

        body_invariant!(forall (
            |j: usize| (0 <= j && j < output.len()) ==>
                *input.lookup(j)== *output.lookup(j)
        ));

        output.push(*input.index(i));
        i += 1;
    }

    output
}
