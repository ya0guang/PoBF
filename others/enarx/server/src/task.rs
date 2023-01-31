#![allow(unused_imports)]

use std::io::{Read, Result, Write};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

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

pub async fn handle_client(mut stream: TcpStream) -> Result<()> {
    let mut length = vec![0u8; 1024];
    let read_len = stream.read(&mut length).await?;
    let data_len = String::from_utf8(length[..read_len - 1].to_vec()).unwrap().parse::<usize>().unwrap();
    println!("Data length = {}", data_len);
    let mut input = vec![0u8; data_len];
    stream.read_exact(&mut input).await?;
    println!("Read data.");

    let output = perform_task(input);
    stream.write(output.len().to_string().as_bytes()).await?;
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
