extern crate base16;
extern crate base64;
extern crate clap;
extern crate env_logger;
extern crate hex;
extern crate serde;
extern crate serde_json;
extern crate sgx_types;
extern crate sgx_urts;

mod ocall;

use clap::Parser;
use log::{error, info};
use sgx_types::error::*;
use sgx_types::types::*;
use sgx_urts::enclave::SgxEnclave;
use std::io::prelude::*;
use std::io::*;
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::os::unix::prelude::AsRawFd;
use std::sync::{mpsc, Arc, Mutex};
use std::thread;

static ENCLAVE_FILE: &'static str = "enclave.signed.so";
static SGX_PLATFORM_HEADER_SIZE: usize = 0x4;
const OUTPUT_BUFFER_SIZE: usize = 2048;
const ENCLAVE_TCS_NUM: usize = 10;

#[derive(Default)]
struct RaMessage {
    spid: Spid,
    linkable: i64,
    public_key: Vec<u8>,
    signature: Vec<u8>,
    ra_type: u8,
}

struct ThreadPool {
    workers: Vec<Worker>,
    sender: Option<mpsc::Sender<Job>>,
}

type Job = Box<dyn FnOnce() + Send + 'static>;

impl ThreadPool {
    pub fn new(size: usize) -> ThreadPool {
        assert!(size > 0);
        let (sender, receiver) = mpsc::channel();

        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        ThreadPool {
            workers,
            sender: Some(sender),
        }
    }

    pub fn execute<F>(&self, f: F) -> Result<()>
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);

        self.sender
            .as_ref()
            .unwrap()
            .send(job)
            .or_else(|_| Err(Error::from(ErrorKind::Other)))
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        drop(self.sender.take());

        for worker in &mut self.workers {
            println!("Shutting down worker {}", worker.id);

            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        }
    }
}

struct Worker {
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Job>>>) -> Worker {
        let thread = thread::spawn(move || loop {
            let message = receiver.lock().unwrap().recv();

            match message {
                Ok(job) => {
                    println!("Worker {id} got a job; executing.");

                    job();
                }
                Err(_) => {
                    println!("Worker {id} disconnected; shutting down.");
                    break;
                }
            }
        });

        Worker {
            id,
            thread: Some(thread),
        }
    }
}

extern "C" {
    fn private_computing_entry(
        eid: EnclaveId,
        retval: *mut SgxStatus,
        socket_fd: c_int,
        spid: *const Spid,
        linkable: i64,
        ra_type: u8,
        public_key: *const u8,
        public_key_len: u32,
        pubkey_signature: *const u8,
        pubkey_signature_len: u32,
        encrypted_output_buffer_ptr: *mut u8,
        encrypted_output_buffer_size: u32,
        encrypted_output_size: *mut u32,
    ) -> SgxStatus;

    /// Legacy function.
    #[allow(unused)]
    fn start_remote_attestation(
        eid: EnclaveId,
        retval: *mut SgxStatus,
        socket_fd: c_int,
        spid: *const Spid,
        linkable: i64,
        public_key: *const u8,
        public_key_len: u32,
        pubkey_signature: *const u8,
        pubkey_signature_len: u32,
    ) -> SgxStatus;
}

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
#[clap(propagate_version = true)]
struct Args {
    #[clap(value_parser)]
    address: String,
    #[clap(value_parser)]
    port: u16,
}

fn main() {
    let args = Args::parse();

    if std::env::var("RUST_LOG").is_err() {
        std::env::set_var("RUST_LOG", "INFO");
    }
    env_logger::init();

    let full_address = format!("{}:{}", &args.address, &args.port);
    info!("[+] Listening to {}", full_address);
    let listener = match TcpListener::bind(&full_address) {
        Ok(res) => res,
        Err(e) => {
            error!(
                "[-] Failed to bind to the given address due to {}.",
                e.to_string()
            );
            return;
        }
    };

    let enclave = match SgxEnclave::create(ENCLAVE_FILE, false) {
        Ok(r) => {
            info!("[+] Init Enclave Successful, eid: {}!", r.eid());
            r
        }
        Err(x) => {
            error!("[-] Init Enclave Failed, reason: {}!", x.as_str());
            return;
        }
    };
    let enclave = Arc::new(enclave);

    server_run(listener, enclave).unwrap();
}

// May need a mutex on enclave
fn server_run(listener: TcpListener, enclave: Arc<SgxEnclave>) -> Result<()> {
    // incoming() is an iterator that returns an infinite sequence of streams.

    let pool = ThreadPool::new(ENCLAVE_TCS_NUM);
    loop {
        match listener.accept() {
            Ok((stream, addr)) => {
                let encalve_cp = enclave.clone();

                if pool
                    .execute(move || handle_client(stream, addr, &encalve_cp).unwrap())
                    .is_err()
                {
                    error!("[-] Job execution failed.");
                    break;
                }
            }
            Err(e) => return Err(e),
        }
    }

    Ok(())
}

fn handle_client(stream: TcpStream, addr: SocketAddr, enclave: &SgxEnclave) -> Result<()> {
    info!("[+] Got connection from {:?}", addr);
    // Expose the raw socket fd.
    let socket_fd = stream.as_raw_fd();
    let socket_clone = stream.try_clone().unwrap();
    let mut reader = BufReader::new(stream);
    let mut writer = BufWriter::new(socket_clone);
    let message = receive_ra_message(&mut reader)?;

    // Execute the PoBF private computing entry.
    let result = exec_private_computing(&enclave, socket_fd, &message);

    //Send the data back.
    info!("[+] Send the data back to the data provider...");
    writer.write(result.len().to_string().as_bytes())?;
    writer.write(b"\n")?;
    writer.write(&result)?;
    writer.write(b"\n")?;
    writer.flush()?;

    Ok(())
}

/// Receives initial messages from the data provider a.k.a. the service provider.
fn receive_ra_message(reader: &mut BufReader<TcpStream>) -> Result<RaMessage> {
    let mut message = RaMessage::default();
    let mut ra_buf = String::with_capacity(128);

    // Check remote attestation type.
    reader.read_line(&mut ra_buf).unwrap();
    if !ra_buf.len() == 2 {
        error!("[-] Remote attestation type is incorrect.");
        return Err(Error::from(ErrorKind::InvalidData));
    }

    // Parse it.
    let ra_type = match ra_buf.chars().next().unwrap() {
        '0' => 0,
        '1' => 1,
        _ => {
            error!("[-] Incorrect remote attestation type!");
            return Err(Error::from(ErrorKind::InvalidData));
        }
    } as u8;

    message.public_key = vec![0u8; 65];
    message.signature = vec![0u8; 0];
    let mut str_buf = String::with_capacity(OUTPUT_BUFFER_SIZE);

    // Read public key.
    reader.read_exact(&mut message.public_key)?;
    message.public_key.truncate(64);

    // Read signature.
    str_buf.clear();
    reader.read_line(&mut str_buf)?;
    let signature_len = str_buf[..str_buf.len() - 1].parse::<usize>().or_else(|e| {
        error!(
            "[-] Cannot parse signature length! Error: {}",
            e.to_string()
        );
        Err(ErrorKind::InvalidData)
    })?;

    message.signature.resize(signature_len + 1, 0u8);
    reader.read_exact(&mut message.signature)?;
    message.signature.truncate(signature_len);

    if ra_type == 0 {
        let mut spid_buf = String::with_capacity(33);
        // Read SPID.
        reader.read_line(&mut spid_buf)?;
        // Decode it.
        let decoded_spid = hex::decode(&spid_buf[..32]).or_else(|e| {
            error!(
                "[-] Cannot decode the spid received from socket! Error: {}",
                e.to_string()
            );
            Err(ErrorKind::InvalidData)
        })?;
        message.spid.id.copy_from_slice(&decoded_spid[..16]);

        // Read linkable.
        reader.read_line(&mut str_buf)?;
        message.linkable = str_buf[..1].parse::<i64>().or_else(|e| {
            error!("[-] Cannot parse `linkable`! Error: {}", e.to_string());
            Err(ErrorKind::InvalidData)
        })?;
    }

    message.ra_type = ra_type;

    Ok(message)
}

fn exec_private_computing(
    enclave: &SgxEnclave,
    socket_fd: c_int,
    ra_message: &RaMessage,
) -> Vec<u8> {
    let mut retval = SgxStatus::Success;
    let mut encrypted_output: Vec<u8> = vec![0u8; OUTPUT_BUFFER_SIZE];
    let mut encrypted_output_size: u32 = 0;

    let res = unsafe {
        private_computing_entry(
            enclave.eid(),
            &mut retval,
            socket_fd,
            &ra_message.spid,
            ra_message.linkable,
            ra_message.ra_type,
            ra_message.public_key.as_ptr() as *const u8,
            ra_message.public_key.len() as u32,
            ra_message.signature.as_ptr() as *const u8,
            ra_message.signature.len() as u32,
            encrypted_output.as_mut_ptr(),
            OUTPUT_BUFFER_SIZE as _,
            &mut encrypted_output_size as _,
        )
    };
    match res {
        SgxStatus::Success => {
            info!(
                "[+] ECALL Successful, returned size: {}",
                encrypted_output_size
            );
            encrypted_output.truncate(encrypted_output_size as _);
            info!(
                "[+] output encrypted data: {:02X?}",
                &encrypted_output[..(encrypted_output_size as usize - MAC_SIZE) as _]
            );
            info!(
                "[+] output encrypted data mac: {:02X?}",
                &encrypted_output[(encrypted_output_size as usize - MAC_SIZE) as _..]
            );
        }
        e => {
            error!("[-] ECALL Enclave Failed, reason: {}!", e.as_str());
        }
    }

    encrypted_output
}
