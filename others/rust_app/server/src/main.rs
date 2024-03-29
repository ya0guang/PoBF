#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]

///! Taken from https://github.com/occlum/occlum/blob/master/tools/toolchains/dcap_lib/examples/dcap_test.rs
#[cfg(feature = "occlum")]
mod dcap;
mod task;

#[cfg(feature = "task_db")]
mod db_persistent;

use std::io::Result;
use std::net::TcpListener;

use pobf_thread_pool::ThreadPool;

const ENCLAVE_TCS_NUM: usize = 10;
const ADDRESS: &str = "127.0.0.1:7788";

fn main() {
    #[cfg(feature = "occlum")]
    dcap::dcap_demo();
    // Start listening to the port.
    let listener = match TcpListener::bind(ADDRESS) {
        Ok(res) => res,
        Err(e) => {
            panic!("[-] Failed to bind to the given address due to {}.", e);
        }
    };

    #[cfg(feature = "task_db")]
    db::DUMPER.call_once(|| Box::new(db_persistent::SgxPersistentLayer));

    let pool = ThreadPool::new(ENCLAVE_TCS_NUM);

    println!("Server started.");
    loop {
        match listener.accept() {
            Ok((stream, _)) => {
                if pool
                    .execute(move || task::handle_client(stream).unwrap())
                    .is_err()
                {
                    println!("[-] Job execution failed.");
                    break;
                }
            }
            Err(e) => panic!("[-] Failed! {:?}", e),
        }
    }
}
