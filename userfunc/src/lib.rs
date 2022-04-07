use alloc::vec::Vec;

pub fn vec_inc(input: Vec<u8>) -> Vec<u8> {
    let step = 1;

    println!("The step is {} in computation_enc", step);

    let mut output = Vec::new();
    for i in input.iter() {
        output.push(i + step);
    }


    println!("after increasing, the 0th data is {}", output[0]);

    output
}
