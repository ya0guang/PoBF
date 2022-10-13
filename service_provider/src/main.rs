extern crate clap;
extern crate curl;

use clap::{Parser, Subcommand};
use curl::easy::{Easy, List};
use std::io::*;
use std::mem;
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
    Run {
        address: String,
        port: u16,
        spid: String,
        key: String,
    },
}

// Configurations for the IAS.
static IAS_BASE_URL: &'static str = "https://api.trustedservices.intel.com";
// Use the newest APIs. (v3 is decprecated.)
static IAS_BASE_REQUEST: &'static str = "/sgx/dev/attestation/v4/";
static IAS_KEY_HEADER: &'static str = "Ocp-Apim-Subscription-Key";

fn main() {
    let args = Args::parse();
    match args.command {
        Commands::Run {
            address,
            port,
            spid,
            key,
        } => {
            let socket = connect(&address, &port).expect("Cannot connect to the given address");
            let socket_clone = socket.try_clone().unwrap();
            let mut reader = BufReader::new(socket);
            let mut writer = BufWriter::new(socket_clone);

            handle_epid(&mut reader, &mut writer, &key).expect("[-] EPID receiving failed.");
        }
    }

    println!("[+] Finished!");
}

fn get_full_url(request: &str) -> String {
    format!("{}{}{}", IAS_BASE_URL, IAS_BASE_REQUEST, request)
}

fn get_sigrl(ias_key: &String, epid: &[u8; 4]) -> Result<()> {
    let mut easy = Easy::new();

    let mut full_url = get_full_url("sigrl");
    // Encode the epid and append it to the full URL.
    let gid = unsafe { mem::transmute::<[u8; 4], u32>(*epid) }.to_le();
    full_url.push_str(&format!("/{:08x?}", gid));

    easy.url(&full_url).unwrap();

    // Set the header.
    let mut header = List::new();
    let header_str = format!("{}: {}", IAS_KEY_HEADER, ias_key);

    println!(
        "[+] Requesting {}\n[+] HTTP header: {}",
        full_url, header_str
    );

    header.append(&header_str).unwrap();
    easy.http_headers(header).unwrap();

    if let Err(_) = easy.perform() {
        return Err(Error::from(ErrorKind::ConnectionRefused));
    }

    println!(
        "[+] Request sent. Got status code {}.",
        easy.response_code().unwrap()
    );

    Ok(())
}

fn connect(address: &String, port: &u16) -> Result<TcpStream> {
    // Create the full address for the server.
    let mut full_address = String::new();
    full_address.push_str(address);
    full_address.push_str(":");
    full_address.push_str(&port.to_string());

    println!("[+] Connecting to {}", full_address);

    TcpStream::connect(&full_address)
}

fn handle_epid(
    reader: &mut BufReader<TcpStream>,
    writer: &mut BufWriter<TcpStream>,
    ias_key: &String,
) -> Result<()> {
    writer.write(b"1\n").unwrap();
    writer.flush().unwrap();

    let mut s = String::with_capacity(512);
    // Wait for the EPID.
    reader.read_line(&mut s).unwrap();

    if !s.starts_with("EPID:") {
        println!("[-] Expecting an EPID. Got {}.", s);
        return Err(Error::from(ErrorKind::InvalidData));
    }

    // Read length.
    s.clear();
    reader.read_line(&mut s).unwrap();
    if s.chars().next().unwrap() != '4' {
        println!("[-] Expecting EPID length to be 4. Got {}.", s);
        return Err(Error::from(ErrorKind::InvalidData));
    }

    // Read EPID itself.
    let mut epid = [0u8; 4];
    reader.read_exact(&mut epid).unwrap();
    println!("[+] EPID: {:?}", epid);

    // Get the SigRL from the IAS.
    get_sigrl(ias_key, &epid)
}
