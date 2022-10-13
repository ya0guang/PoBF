extern crate clap;

use clap::{Parser, Subcommand};
use std::io::Result;
use std::io::Write;
use std::io::{BufReader, BufWriter};
use std::net::TcpStream;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
#[clap(propagate_version = true)]
struct Args {
    #[clap(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Run { address: String, port: u16 },
}

// Configurations for the IAS.
static IAS_BASE_URL: &'static str = "api.trustedservices.intel.com";
static IAS_PORT: u16 = 443;
// Use the newest APIs. (v3 is decprecated.)
static IAS_BASE_REQUEST: &'static str = "/dev/attestation/v4/";

fn main() {
    let args = Args::parse();
    match args.command {
        Commands::Run { address, port } => {
            let mut socket = connect(&address, &port).expect("Cannot connect to the given address");
            let socket_clone = socket.try_clone().unwrap();
            let mut reader = BufReader::new(socket);
            let mut writer = BufWriter::new(socket_clone);

            writer.write(b"1\n").unwrap();
            writer.flush().unwrap();
            
            // Wait for the EPID.

        }
    }
    println!("Hello, world!");
}

fn connect(address: &String, port: &u16) -> Result<TcpStream> {
    // Create the full address for the server.
    let mut full_address = String::new();
    full_address.push_str(address);
    full_address.push_str(":");
    full_address.push_str(&port.to_string());

    println!("Connecting to {}", full_address);

    TcpStream::connect(&full_address)
}
