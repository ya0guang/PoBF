use std::time::*;

// Settings for private computation functions.
cfg_if::cfg_if! {
    if #[cfg(feature = "task_tvm")] {
        use evaluation_tvm::private_computation;
        const INPUT_DATA: &'static [u8] = include_bytes!("../../../data/task_tvm/data.bin");
    } else if #[cfg(feature = "task_fann")] {
        use fann::private_computation;
        const INPUT_DATA: &'static [u8] = include_bytes!("../../../data/task_fann/data.bin");
    } else if #[cfg(feature = "task_fasta")] {
        use fasta::private_computation;
        const INPUT_DATA: &'static [u8] = include_bytes!("../../../data/task_fasta/data.bin");
    } else if #[cfg(feature = "task_polybench")] {
        use polybench::private_computation;
        const INPUT_DATA: &'static [u8] = include_bytes!("../../../data/task_polybench/data.bin");
    } else if #[cfg(feature = "task_sample")] {
        use sample_add::private_computation;
        const INPUT_DATA: &'static [u8] = include_bytes!("../../../data/task_sample/data.bin");
    }
}

// TODO: Add networking?
fn main() {
    let now = Instant::now();
    {
        #[cfg(feature = "task_polybench")]
        {
            let res = private_computation(INPUT_DATA.to_vec(), &|| {
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_nanos() as u64
            });
            println!("{}", String::from_utf8(res).unwrap());
        }

        #[cfg(not(feature = "task_polybench"))]
        {
            private_computation(INPUT_DATA.to_vec());
        }
    }
    let elapsed = now.elapsed();
    println!("Elapsed: {:.2?}", elapsed);
}
