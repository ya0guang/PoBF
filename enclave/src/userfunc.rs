#![forbid(unsafe_code)]

use core::ops::Index;

use crate::pobf_verifier::*;
use alloc::vec::Vec;
use prusti_contracts::*;

// TODO: Use prusti to check that if anything would be leaked.
#[allow(unused)]
#[trusted]
pub fn vec_inc(input: Vec<u8>) -> Vec<u8> {
    let step = 1u8;

    // this can be proven true by MIRAI
    #[cfg(feature = "leak_log")]
    #[cfg(not(feature = "use_prusti"))]
    {
        println!("The step is {} in computation_enc", step);
    }

    let mut output = Vec::new();
    let mut i = 0usize;

    while i < input.len() {
        let val = input.index(i);
        output.push(val + step);
        i += 1;
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
