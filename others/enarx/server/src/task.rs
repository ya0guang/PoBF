#![allow(unused_imports)]

use std::io::{Read, Result, Write};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

cfg_if::cfg_if! {
  if #[cfg(feature = "task_tvm")] {
      use wasm_runtime::private_computation;
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

pub async fn handle_client(mut stream: TcpStream) -> Result<()> {
    let mut length = vec![0u8; std::mem::size_of::<u64>()];
    stream.read_exact(&mut length).await?;
    let data_len = u64::from_le_bytes(length.try_into().unwrap()) as usize;
    let input = {
        let mut input = vec![0u8; data_len + 1];
        stream.read_exact(&mut input).await?;
        println!("Read data.");
        input[1..].to_vec()
    };

    let output = perform_task(input);
    let mut vec = vec![0u8; 10000];
    stream.read(&mut vec).await?;
    stream.write(&(output.len() as u64).to_le_bytes()).await?;
    stream.write(b"\n").await?;
    stream.flush().await?;
    stream.write(&output).await?;
    stream.write(b"\n").await?;
    stream.flush().await?;
    println!("Sent data. Length = {}", output.len());
    println!("Finished!");

    Ok(())
}

fn perform_task(input: Vec<u8>) -> Vec<u8> {
    let now = Instant::now();
    #[cfg(feature = "task_polybench")]
    {
        let res = private_computation(input, &|| {
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos() as u64
        });
        println!("{}", String::from_utf8(res.clone()).unwrap());
        let elapsed = now.elapsed();
        println!("Elapsed: {:.2?}", elapsed);
        res
    }

    #[cfg(not(feature = "task_polybench"))]
    {
        let res = private_computation(input);
        let elapsed = now.elapsed();
        println!("Elapsed: {:.2?}", elapsed);

        res
    }
}
