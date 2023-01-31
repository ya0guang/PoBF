use std::env;
use std::fs;
use std::io::*;
use std::net::TcpStream;

const ADDRESS: &str = "127.0.0.1:7788";

fn main() {
    let stream = TcpStream::connect(ADDRESS).unwrap();
    let stream_clone = stream.try_clone().unwrap();
    let mut reader = BufReader::new(stream);
    let mut writer = BufWriter::new(stream_clone);

    let args: Vec<String> = env::args().collect();
    let data_path = &args[1];
    let data = fs::read(data_path).unwrap();
    println!("Reading {}", data_path);

    // Send to the server.
    writer.write(&data.len().to_le_bytes()).unwrap();
    writer.write(b"\n").unwrap();
    writer.flush().unwrap();
    writer.write(&data).unwrap();
    writer.write(b"\n").unwrap();
    writer.flush().unwrap();
    println!("Sent data. Length = {}", data.len());

    let mut length_str = String::with_capacity(512);
    reader.read_line(&mut length_str).unwrap();
    let data_len = length_str[..length_str.len() - 1].parse::<usize>().unwrap();
    println!("Data length = {}", data_len);
    let mut input = vec![0u8; data_len];
    reader.read_exact(&mut input).unwrap();
    println!("Read data.");
    println!("Finished");
}
