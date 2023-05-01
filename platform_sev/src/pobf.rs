use std::{
    io::{BufRead, BufReader, BufWriter, Read, Write},
    net::{TcpListener, TcpStream},
};

use anyhow::{anyhow, Result};
use clear_on_drop::clear_stack_and_regs_on_return;
use log::{error, info};
use pobf_state::task::{ComputingTask, ComputingTaskSession, ComputingTaskTemplate, Initialized};

use crate::vecaes::{AES128Key, VecAESData};

const ADDRESS: &str = "127.0.0.1";
const PORT: u16 = 2333;
const NONCE: &str = "hurricane";
const DEFAULT_PAGE_SIZE_LEAF: usize = 0x20;

extern "C" {
    fn get_attestation_report(buf: *mut u8, len: usize, nonce: *const u8, nonce_len: usize) -> i64;
}

fn private_vec_compute<T>(input: T) -> T
where
    T: From<Vec<u8>> + Into<Vec<u8>>,
{
    input
}

fn get_reader_and_writer(
    address: &str,
    port: u16,
) -> Result<(BufReader<TcpStream>, BufWriter<TcpStream>)> {
    let full_address = format!("{address}:{port}");

    let listener = match TcpListener::bind(&full_address) {
        Ok(res) => res,
        Err(e) => {
            error!(
                "[-] Failed to bind to the given address due to {}.",
                e.to_string()
            );
            return Err(anyhow!("Failed to bind"));
        }
    };

    // Add thread pool here if there is any need to do so.
    let socket = listener.accept()?.0;
    let socket_clone = socket.try_clone()?;

    Ok((BufReader::new(socket), BufWriter::new(socket_clone)))
}

/// Performs the remote attestation step and returns a JWT report from Azure to the data provider.
/// The data provider then:
/// * validates JWT and nonce,
/// * generates an AES key used to encrypt the data,
/// * encrypted the AES key using RSA key from the JWT, and
/// * sends both the encrypted data and the encrypted AES key to the TEE.
///
/// The TEE then:
/// * decrypts the AES key using TPM, and
/// * decrypts the data using the decrypted AES key.
///
/// This function finally returns a valid and decrypted AES key. To keep best compatibility with SGX's data provider, we
/// maintain the length of the AES key to be 128 bit, and the encryption mode is AES-GCM with a secure nonce.
fn pobf_remote_attestation(
    reader: &mut BufReader<TcpStream>,
    writer: &mut BufWriter<TcpStream>,
) -> AES128Key {
    let mut vec = vec![0u8; 4096];
    let attestation_result =
        unsafe { get_attestation_report(vec.as_mut_ptr(), vec.len(), NONCE.as_ptr(), NONCE.len()) };

    if attestation_result != 0 {
        panic!("attestation failed with {attestation_result:#x}");
    } else {
        info!("attestation passed.");
        // Convert raw byte array into a string.
        let report = String::from_utf8(vec).unwrap();
        // Parse the report as a json object.
        let json_report = json::parse(&report).unwrap();
        // Return this report to the data provider.
        writer.write_all(report.as_bytes()).unwrap();
        writer.flush();

        todo!()
    }
}

fn pobf_receive_data(reader: &mut BufReader<TcpStream>) -> VecAESData {
    log::info!("[+] Receiving data from data provider...");

    // Get length of the data.
    let mut len = String::new();
    reader.read_line(&mut len).unwrap();
    let len = len.parse::<usize>().unwrap();

    // Prepare the buffer.
    let mut buf = vec![0u8; len];
    reader.read_exact(&mut buf).unwrap();

    buf.into()
}

/// The main entry of the PoBF workflow for AMD-SEV.
pub fn pobf_workflow() -> Result<()> {
    let (mut reader, mut writer) = get_reader_and_writer(ADDRESS, PORT)?;

    let session = {
        // To avoid multiple mutable borrows.
        let ra_callback = || pobf_remote_attestation(&mut reader, &mut writer);

        // Start the PoBF workflow.
        let f = || ComputingTaskTemplate::<Initialized>::new();
        let template = clear_stack_and_regs_on_return(DEFAULT_PAGE_SIZE_LEAF, f);
        let f = || ComputingTaskSession::establish_channel(template, ra_callback);
        clear_stack_and_regs_on_return(DEFAULT_PAGE_SIZE_LEAF, f)
    };

    let receive_callback = || pobf_receive_data(&mut reader);
    let f = || ComputingTask::receive_data(session, receive_callback);
    let task_data_received = clear_stack_and_regs_on_return(DEFAULT_PAGE_SIZE_LEAF, f);
    let f = || task_data_received.compute(&private_vec_compute);
    let task_result_encrypted = clear_stack_and_regs_on_return(DEFAULT_PAGE_SIZE_LEAF, f);
    let f = || task_result_encrypted.take_result();
    let result = clear_stack_and_regs_on_return(DEFAULT_PAGE_SIZE_LEAF, f);

    Ok(())
}
