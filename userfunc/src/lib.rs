use alloc::vec::Vec;

pub fn vec_inc(input: Vec<u8>) -> Vec<u8> {
    let step = 1;

    // this can be proven true by MIRAI
    #[cfg(feature = "leak_log")]
    {
        #[cfg(mirai)]
        verify!(step == 1);
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
        verify!(output[0] == 10);
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
