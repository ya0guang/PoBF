#![allow(unused)]
#![feature(cstr_from_bytes_until_nul)]

use clap::{Arg, Parser};

use crate::{ffi::uninitialize, pobf::entry};

mod ffi;
mod key;
mod pobf;
mod vecaes;

#[cfg(feature = "task_db")]
mod db_persistent;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
#[clap(propagate_version = true)]
struct Args {
    #[clap(value_parser)]
    address: String,
    #[clap(value_parser)]
    port: u16,
    #[clap(value_parser, default_value_t = 0x20)]
    stack_size: u16,
}

fn init_logger() {
    if std::env::var("RUST_LOG").is_err() {
        std::env::set_var("RUST_LOG", "info");
    }
    env_logger::init();
}

fn main() {
    init_logger();

    let args = Args::parse();
    log::info!(
        "Performing PoBF workflow on AMD-SEV... Address is {}:{}",
        args.address,
        args.port
    );

    #[cfg(feature = "task_db")]
    db::DUMPER.call_once(|| Box::new(db_persistent::SgxPersistentLayer));

    match entry(&args.address, args.port, args.stack_size) {
        Ok(_) => log::info!("[+] Finished with success"),
        Err(err) => log::error!("[-] PoBF workflow returned {err}"),
    }

    unsafe {
        uninitialize();
    }
}
