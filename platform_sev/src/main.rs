#![allow(unused)]

use clap::{Arg, Parser};

use crate::pobf::entry;

mod ffi;
mod key;
mod pobf;
mod vecaes;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
#[clap(propagate_version = true)]
struct Args {
    #[clap(value_parser)]
    address: String,
    #[clap(value_parser)]
    port: u16,
}

fn init_logger() {
    if std::env::var("RUST_LOG").is_err() {
        std::env::set_var("RUST_LOG", "info");
    }
    env_logger::init();
}

fn main() {
    init_logger();

    log::info!("Performing PoBF workflow on AMD-SEV...");

    let args = Args::parse();
    match entry(&args.address, args.port) {
        Ok(_) => log::info!("[+] Finished with success"),
        Err(err) => log::error!("[-] PoBF workflow returned {err}"),
    }
}
