//! Adaptive version of `wasi/src/main.rs` at
//! https://github.com/kazum/tvm-wasm/blob/master/examples/wasi/src/main.rs

use image::{imageops::FilterType, GenericImageView};
use ndarray::Array;
use std::{collections::HashMap, convert::TryFrom, env, sync::Mutex};
use tvm_graph_rt::{Graph, GraphExecutor, SystemLibModule, Tensor};

const IMG_HEIGHT: usize = 224;
const IMG_WIDTH: usize = 224;

extern "C" {
    static __tvm_module_ctx: i32;
    fn __wasm_call_ctors();
}

#[no_mangle]
unsafe fn __get_tvm_module_ctx() -> i32 {
    // Refer a symbol in the libtvmwasm.a to make sure that the link of the
    // library is not optimized out.
    __tvm_module_ctx
}

lazy_static::lazy_static! {
  static ref SYSLIB: SystemLibModule = SystemLibModule::default();
  static ref GRAPH_EXECUTOR: Mutex<GraphExecutor<'static, 'static>> = {
      unsafe {
          // This is necessary to invoke TVMBackendRegisterSystemLibSymbol
          // API calls.
          __wasm_call_ctors();
      }
      let graph = Graph::try_from(include_str!(concat!(
          env!("CARGO_MANIFEST_DIR"),
          "/../wasm-graph/lib/graph.json"
      )))
      .unwrap();
      let params_bytes =
          include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/../wasm-graph/lib/graph.params"));
      let params = tvm_graph_rt::load_param_dict(params_bytes)
          .unwrap()
          .into_iter()
          .map(|(k, v)| (k, v.to_owned()))
          .collect::<HashMap<String, Tensor<'static>>>();

      let mut exec = GraphExecutor::new(graph, &*SYSLIB).unwrap();
      exec.load_params(params);

      Mutex::new(exec)
  };
}

/// Convert a raw imnage into Tensor if needed.
pub fn preprocess(img: image::DynamicImage) -> Tensor<'static> {
    println!("original image dimensions: {:?}", img.dimensions());
    let img = img
        .resize_exact(IMG_HEIGHT as u32, IMG_WIDTH as u32, FilterType::Nearest)
        .to_rgb8();
    println!("resized image dimensions: {:?}", img.dimensions());
    let mut pixels: Vec<f32> = vec![];
    for pixel in img.pixels() {
        let tmp = pixel.0;
        // normalize the RGB channels using mean, std of imagenet1k
        let tmp = [
            (tmp[0] as f32 - 123.0) / 58.395, // R
            (tmp[1] as f32 - 117.0) / 57.12,  // G
            (tmp[2] as f32 - 104.0) / 57.375, // B
        ];
        for e in &tmp {
            pixels.push(*e);
        }
    }

    // (H,W,C) -> (C,H,W)
    let arr = Array::from_shape_vec((IMG_HEIGHT, IMG_WIDTH, 3), pixels).unwrap();
    let arr = arr.permuted_axes([2, 0, 1]);
    let arr = Array::from_iter(arr.into_iter().map(|&v| v));

    Tensor::from(arr)
}

/// Perform the ResNet prediction phase.
pub fn private_computation(input: Vec<u8>) -> Vec<u8> {
    // Load image from byte array.
    let img = image::load_from_memory_with_format(&input, image::ImageFormat::Png).unwrap();
    let tensor = preprocess(img);

    let mut executor = GRAPH_EXECUTOR.lock().unwrap();
    executor.set_input("data", tensor);
    executor.run();
    let output = executor.get_output(0).unwrap().to_vec::<f32>();
    unsafe { std::slice::from_raw_parts(output.as_ptr() as *const u8, output.len() * 4) }.to_vec()
}
