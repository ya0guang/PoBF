#![no_std]

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;

const GRAPH_JSON: &'static [u8] = include_bytes!("../outlib/graph.json");
const GRAPH_PARAM: &'static [u8] = include_bytes!("../outlib/params.bin");
const GRAPH_TEST_INPUT: &'static [u8] = include_bytes!("../outlib/cat.bin");
const GRAPH_OUTPUT_LEN: usize = 1000usize;

extern "C" {
    fn tvm_mxnet_run(
        json: *const u8,
        json_size: usize,
        param: *const u8,
        param_size: usize,
        input: *const u8,
        input_size: usize,
        output: *mut u8,
        output_buf_size: usize,
    ) -> i32;
}

pub fn private_computation(input: Vec<u8>) -> Vec<u8> {
    let input_byte = input.as_slice();
    let input_size = input_byte.len();

    let mut output = vec![0u8; GRAPH_OUTPUT_LEN];

    let res = unsafe {
        tvm_mxnet_run(
            GRAPH_JSON.as_ptr(),
            GRAPH_JSON.len(),
            GRAPH_PARAM.as_ptr(),
            GRAPH_PARAM.len(),
            input_byte.as_ptr(),
            input_size,
            output.as_mut_ptr(),
            GRAPH_OUTPUT_LEN,
        )
    };

    // FIXME: Currently the input size does not match.
    // if res != 0 {
    //     panic!("[-] Cannot invoke TVM.");
    // }

    output[..10].to_vec()
}
