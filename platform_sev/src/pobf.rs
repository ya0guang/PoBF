use std::{
    ffi::CStr,
    io::{BufRead, BufReader, BufWriter, Read, Write},
    net::{TcpListener, TcpStream},
};

use anyhow::{anyhow, Result};
use clear_on_drop::clear_stack_and_regs_on_return;
use log::{error, info};
use pobf_state::{
    get_time_summary,
    task::{ComputingTask, ComputingTaskSession, ComputingTaskTemplate, Initialized},
};
use pobf_thread_pool::{ThreadPool, TCS_NUM};
use ring::agreement::{agree_ephemeral, UnparsedPublicKey, X25519};

use crate::{
    ffi::get_attestation_report,
    key::get_keypair,
    vecaes::{AES128Key, VecAESData},
};

const ADDRESS: &str = "127.0.0.1";
const PORT: u16 = 2333;
const NONCE: &str = "hurricane";
const DEFAULT_PAGE_SIZE_LEAF: usize = 0x1;

// Settings for private computation functions.
cfg_if::cfg_if! {
   if #[cfg(feature = "task_tvm")] {
        use evaluation_tvm::private_computation;
    } else if #[cfg(feature = "task_fann")] {
        use fann::private_computation;
    } else if #[cfg(feature = "task_fasta")] {
        use fasta::private_computation;
    } else if #[cfg(feature = "task_polybench")] {
        use polybench::*;

        #[cfg(feature = "nussinov")]
        fun_polybench!(nussinov, 500, );

        #[cfg(feature = "floyd_warshall")]
        fun_polybench!(floyd_warshall, 500, );

        #[cfg(feature = "deriche")]
        fun_polybench!(deriche, 1024, 540, );

        #[cfg(feature = "adi")]
        fun_polybench!(adi, 250, 125, );

        #[cfg(feature = "fdtd_2d")]
        fun_polybench!(fdtd_2d, 250, 300, 125, );

        #[cfg(feature = "heat_3d")]
        fun_polybench!(heat_3d, 30, 125, );

        #[cfg(feature = "jacobi_1d")]
        fun_polybench!(jacobi_1d, 5000, 125, );

        #[cfg(feature = "jacobi_2d")]
        fun_polybench!(jacobi_2d, 325, 125, );

        #[cfg(feature = "seidel_2d")]
        fun_polybench!(seidel_2d, 500, 125, );

        #[cfg(feature = "correlation")]
        fun_polybench!(correlation, 300, 350, );

        #[cfg(feature = "covariance")]
        fun_polybench!(covariance, 300, 350, );

        #[cfg(feature = "gramschmidt")]
        fun_polybench!(gramschmidt, 250, 300, );

        #[cfg(feature = "lu")]
        fun_polybench!(lu, 500, );

        #[cfg(feature = "ludcmp")]
        fun_polybench!(ludcmp, 500, );

        #[cfg(feature = "trisolv")]
        fun_polybench!(trisolv, 500, );

        #[cfg(feature = "cholesky")]
        fun_polybench!(cholesky, 500, );

        #[cfg(feature = "durbin")]
        fun_polybench!(durbin, 500, );

        #[cfg(feature = "_2mm")]
        fun_polybench!(_2mm, 200, 225, 250, 275, );

        #[cfg(feature = "_3mm")]
        fun_polybench!(_3mm, 200, 225, 250, 275, 300, );

        #[cfg(feature = "atax")]
        fun_polybench!(atax, 475, 525, );

        #[cfg(feature = "bicg")]
        fun_polybench!(bicg, 475, 525, );

        #[cfg(feature = "doitgen")]
        fun_polybench!(doitgen, 35, 37, 40, );

        #[cfg(feature = "gemm")]
        fun_polybench!(gemm, 250, 275, 300, );

        #[cfg(feature = "gemver")]
        fun_polybench!(gemver, 5000, );

        #[cfg(feature = "gesummv")]
        fun_polybench!(gesummv, 5000, );

        #[cfg(feature = "mvt")]
        fun_polybench!(mvt, 1000, );

        #[cfg(feature = "symm")]
        fun_polybench!(symm, 250, 300, );

        #[cfg(feature = "syr2k")]
        fun_polybench!(syr2k, 250, 300, );

        #[cfg(feature = "syrk")]
        fun_polybench!(syrk, 250, 300, );

        #[cfg(feature = "trmm")]
        fun_polybench!(trmm, 250, 300, );
    } else if #[cfg(feature = "sample_add")] {
        use sample_add::private_computation;
    } else {
        /// Identity task.
        pub fn private_computation(input: Vec<u8>) -> Vec<u8> {
            input
        }
    }
}

fn private_vec_compute<T>(input: T) -> T
where
    T: From<Vec<u8>> + Into<Vec<u8>>,
{
    let input_vec: Vec<u8> = input.into();

    cfg_if::cfg_if! {
        if #[cfg(feature = "task_polybench")] {
            let timing_function = || {
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos() as u64
            };
            let output_vec = private_computation(input_vec, &timing_function);

        } else {
            let output_vec = private_computation(input_vec);
        }
    }

    T::from(output_vec)
}

pub fn entry(address: &str, port: u16) -> Result<()> {
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

    let pool = ThreadPool::new(TCS_NUM);
    loop {
        match listener.accept() {
            Ok((socket, addr)) => {
                if pool
                    .execute(move || {
                        let socket_clone = socket.try_clone().unwrap();
                        let reader = BufReader::new(socket);
                        let writer = BufWriter::new(socket_clone);
                        pobf_workflow(reader, writer).unwrap();
                    })
                    .is_err()
                {
                    error!("[-] Job execution failed.");
                    break;
                }
            }
            Err(e) => return Err(e.into()),
        }
    }

    Ok(())
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
        info!("[+] attestation passed.");
        // Convert raw byte array into a string.
        let report = CStr::from_bytes_until_nul(vec.as_slice())
            .unwrap_or_default()
            .to_str()
            .unwrap_or_default();

        // Return this report to the data provider.
        writer.write(report.len().to_string().as_bytes());
        writer.write(b"\n");
        writer.flush();
        writer.write(report.as_bytes()).unwrap();
        writer.flush();

        // Generate two key pairs.
        info!("[+] Sampling key pairs");
        let (prv_key, pub_key) = get_keypair();
        // Receive the peer public key.
        let mut peer_pub_key = vec![0u8; 0x20];
        reader.read_exact(&mut peer_pub_key).unwrap();
        let peer_pub_key = UnparsedPublicKey::new(&X25519, peer_pub_key);
        // Compute the session key and send its public key to the peer.
        let session_key =
            agree_ephemeral(prv_key, &peer_pub_key, ring::error::Unspecified, |key| {
                // No derivation algorithm for simplicity.
                Ok(key.to_vec())
            })
            .unwrap();
        writer.write_all(pub_key.as_ref());
        writer.flush();
        info!("[+] Key aggrement OK {session_key:02x?}");

        AES128Key::from(session_key)
    }
}

fn pobf_receive_data(reader: &mut BufReader<TcpStream>) -> VecAESData {
    info!("[+] Receiving data from data provider...");

    // Get length of the data.
    let mut len = String::with_capacity(128);
    reader.read_line(&mut len).unwrap();
    let len = len[..len.len() - 1].parse::<usize>().unwrap();
    // Prepare the buffer.
    let mut buf = vec![0u8; len];
    reader.read_exact(&mut buf).unwrap();

    info!("[+] Received data from data provider...");
    buf.into()
}

/// The main entry of the PoBF workflow for AMD-SEV.
pub fn pobf_workflow(
    mut reader: BufReader<TcpStream>,
    mut writer: BufWriter<TcpStream>,
) -> Result<()> {
    // Start the PoBF workflow.
    let ra_callback = || pobf_remote_attestation(&mut reader, &mut writer);
    let f = || ComputingTaskTemplate::<Initialized>::new();
    let template = clear_stack_and_regs_on_return(DEFAULT_PAGE_SIZE_LEAF, f);
    let f = || ComputingTaskSession::establish_channel(template, ra_callback);
    let session = clear_stack_and_regs_on_return(DEFAULT_PAGE_SIZE_LEAF, f);

    let receive_callback = || pobf_receive_data(&mut reader);
    let f = || ComputingTask::receive_data(session, receive_callback);
    let task_data_received = clear_stack_and_regs_on_return(DEFAULT_PAGE_SIZE_LEAF, f);
    let f = || task_data_received.compute(&private_vec_compute);
    let task_result_encrypted = clear_stack_and_regs_on_return(DEFAULT_PAGE_SIZE_LEAF, f);
    let f = || task_result_encrypted.take_result();
    let result = clear_stack_and_regs_on_return(DEFAULT_PAGE_SIZE_LEAF, f);

    // Send it back.
    info!("[+] Computation finished");
    let data: Vec<u8> = result.into();
    writer.write_all(data.len().to_string().as_bytes())?;
    writer.write_all(b"\n")?;
    writer.write_all(&data)?;
    writer.flush()?;

    info!(
        "[+] OK. The time breakdown is given by {}",
        get_time_summary(2445.432) // Set the cpu frequency here.
    );

    Ok(())
}
