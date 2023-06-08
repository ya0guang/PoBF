#![allow(unused_imports)]

use std::io::{Read, Result, Write};
use std::time::{Instant, SystemTime, UNIX_EPOCH};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;

cfg_if::cfg_if! {
    if #[cfg(feature = "task_tvm")] {
        use wasm_runtime::private_computation;
    } else if #[cfg(feature = "task_db")] {
        use db::private_computation;
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
        let mut input = vec![0u8; data_len];
        stream.read_exact(&mut input).await?;
        println!("Read data with length {data_len}");
        input.to_vec()
    };

    let output = perform_task(input);
    stream.write(output.len().to_string().as_bytes()).await?;
    stream.write(b"\n").await?;
    stream.flush().await?;
    stream.write_all(&output).await?;
    stream.flush().await?;
    println!(
        "output is {:?}",
        std::str::from_utf8(&output[..(100).min(output.len())]).unwrap_or_default()
    );
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
