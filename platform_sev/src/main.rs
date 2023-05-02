#![allow(unused)]

use crate::pobf::pobf_workflow;

mod ffi;
mod key;
mod pobf;
mod vecaes;

fn init_logger() {
    if std::env::var("RUST_LOG").is_err() {
        std::env::set_var("RUST_LOG", "info");
    }
    env_logger::init();
}

fn main() {
    init_logger();

    log::info!("Performing PoBF workflow on AMD-SEV...");

    match pobf_workflow() {
        Ok(()) => log::info!("finished with success"),
        Err(err) => log::error!("PoBF workflow returned {err}"),
    }
}
