#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]

mod task;
use std::env;
use std::io::Result;
use tokio::net::{TcpListener, TcpStream};
use std::os::wasi::prelude::FromRawFd;
use std::str::FromStr;

use crate::task::handle_client;

const ENCLAVE_TCS_NUM: usize = 10;
const ADDRESS: &str = "127.0.0.1:7788";

#[tokio::main(flavor = "current_thread")]
async fn main() -> Result<()> {
    {
        let fd_names = env::var("FD_NAMES").unwrap();
        let fd_count = env::var("FD_COUNT").unwrap();

        println!("{fd_names}, {fd_count}.");
        let fd_count = usize::from_str(&fd_count).unwrap();
        assert_eq!(
            fd_count,
            4, // STDIN, STDOUT, STDERR and a socket
            "unexpected amount of file descriptors received"
        );
        println!("Enarx FD NUM check passed");
    }

    let listener = {
      let listener = unsafe { std::net::TcpListener::from_raw_fd(3) };
      listener.set_nonblocking(true).unwrap();
      TcpListener::from_std(listener)?
    };

    println!("Server started.");

    loop {
        let socket = match listener.accept().await {
            Ok((socket, _)) => socket,
            Err(e) => panic!("[-] Failed! {:?}", e),
        };

        // Spawn a background task for each new connection.
        tokio::spawn(async move {
            println!("> CONNECTED");
            match handle_client(socket).await {
                Ok(()) => println!("> DISCONNECTED"),
                Err(e) => println!("> ERROR: {}", e),
            }
        });
    }
}
