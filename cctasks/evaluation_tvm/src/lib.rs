#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;

const GRAPH_JSON: &'static [u8] = include_bytes!("../outlib/graph.json");
const GRAPH_PARAM: &'static [u8] = include_bytes!("../outlib/params.bin");
const GRAPH_OUTPUT_LEN: usize = 1000usize;

extern "C" {
    fn tvm_resnet152_run(
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
    let input_size = 1 * 3 * 224 * 224 * core::mem::size_of::<f32>();

    let mut output = vec![0u8; GRAPH_OUTPUT_LEN * core::mem::size_of::<f32>()];

    let res = unsafe {
        tvm_resnet152_run(
            GRAPH_JSON.as_ptr(),
            GRAPH_JSON.len(),
            GRAPH_PARAM.as_ptr(),
            GRAPH_PARAM.len(),
            input_byte.as_ptr(),
            input_size,
            output.as_mut_ptr(),
            GRAPH_OUTPUT_LEN * core::mem::size_of::<f32>(),
        )
    };

    if res != 0 {
        panic!("[-] TVM internal error. Check input size?");
    }

    output
}
