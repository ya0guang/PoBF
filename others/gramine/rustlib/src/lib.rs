use std::time::*;

// Settings for private computation functions.
cfg_if::cfg_if! {
  if #[cfg(feature = "task_tvm")] {
      use evaluation_tvm::private_computation;
  } else if #[cfg(feature = "task_fann")] {
      use fann::private_computation;
  } else if #[cfg(feature = "task_fasta")] {
      use fasta::private_computation;
  } else if #[cfg(feature = "task_polybench")] {
      use polybench::private_computation;
  } else if #[cfg(feature = "task_sample")] {
      use sample_add::private_computation;
  }
}

#[no_mangle]
pub unsafe extern "C" fn gramine_rust_entry(
    input: *const u8,
    input_len: u32,
    output: *mut u8,
    output_buf_len: u32,
    output_len: *mut u32,
) -> i32 {
    let now = Instant::now();
    let input_buf = std::slice::from_raw_parts(input, input_len as usize).to_vec();
    #[cfg(feature = "task_polybench")]
    let output_buf = {
        let res = private_computation(input_buf, &|| {
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos() as u64
        });
        println!("{}", String::from_utf8(res.clone()).unwrap());
        res
    };

    #[cfg(not(feature = "task_polybench"))]
    let output_buf = private_computation(input_buf);

    let elapsed = now.elapsed();
    println!("Elapsed: {:.2?}", elapsed);

    if output_buf.len() > output_buf_len as usize {
        println!(
            "[!] The buffer size is insufficient! Expected {}, got {}.",
            output_buf.len(),
            output_buf_len
        );
        -1
    } else {
        std::ptr::copy(output_buf.as_ptr(), output, output_buf.len());
        *output_len = output_buf.len() as u32;

        0
    }
}
