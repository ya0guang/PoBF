use std::{
    io::{BufRead, BufReader, BufWriter, Read, Result, Write},
    net::TcpStream,
    time::Instant,
};

use pobf_crypto::{handle_sev_pubkey, init_keypair};

cfg_if::cfg_if! {
    if #[cfg(feature = "task_tvm")] {
        use evaluation_tvm::private_computation;
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

pub fn handle_client(stream: TcpStream) -> Result<()> {
    let socket_clone = stream.try_clone().unwrap();
    let mut reader = BufReader::new(stream);
    let mut writer = BufWriter::new(socket_clone);

    // Generate two key pairs.
    println!("[+] Sampling key pairs");
    let mut key_pair = init_keypair().unwrap();
    let public_key = &key_pair.pub_k;
    println!("[+] Receiving peer public key");
    let peer_pub_key = handle_sev_pubkey(&mut reader).unwrap();
    println!("[+] Sending public key");
    writer.write_all(public_key.as_ref()).unwrap();
    writer.flush().unwrap();

    key_pair.compute_shared_key(&peer_pub_key, b"").unwrap();

    let mut length_str = String::with_capacity(512);
    reader.read_line(&mut length_str)?;
    let data_len = length_str[..length_str.len() - 1].parse::<usize>().unwrap();
    println!("Data length = {}", data_len);
    let mut input = vec![0u8; data_len];
    reader.read_exact(&mut input)?;
    println!("Read data.");
    let input = key_pair.decrypt_with_smk(&input).unwrap();

    let output = perform_task(input);
    let output = key_pair.encrypt_with_smk(&output).unwrap();
    writer.write(output.len().to_string().as_bytes())?;
    writer.write(b"\n")?;
    writer.flush()?;
    writer.write(&output)?;
    writer.write(b"\n")?;
    writer.flush()?;
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
