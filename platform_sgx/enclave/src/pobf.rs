#![forbid(unsafe_code)]

use crate::dh::*;
use crate::ocall::*;
use crate::ra_utils::*;
use crate::userfunc::vec_inc;
use crate::vecaes::{AES128Key, VecAESData};
use crate::{ocall_log, verified_log};
use alloc::vec::Vec;
use pobf_state::task::*;
use sgx_types::error::SgxResult;
use sgx_types::error::SgxStatus;
use sgx_types::types::{c_int, Spid};

pub fn private_vec_compute<T>(input: T) -> T
where
    T: From<Vec<u8>> + Into<Vec<u8>>,
{
    let input_vec = input.into();

    let output_vec = vec_inc(input_vec);
    T::from(output_vec)
}

// TODO: generics on the return type
pub fn pobf_workflow(
    socket_fd: c_int,
    spid: &Spid,
    linkable: i64,
    ra_type: u8,
    public_key: &[u8; ECP_COORDINATE_SIZE],
    signature: &[u8],
) -> VecAESData {
    let ra_callback =
        move || pobf_remote_attestation(socket_fd, spid, linkable, ra_type, public_key, signature);

    let template = ComputingTaskTemplate::<Initialized>::new();
    let session = ComputingTaskSession::establish_channel(template, &ra_callback);

    let receive_data_callback = || pobf_receive_data(socket_fd);
    let task_data_received = ComputingTask::receive_data(session, &receive_data_callback);

    let task_result_encrypted = task_data_received.compute(&private_vec_compute);

    let result = task_result_encrypted.take_result();

    result
}

/// This is a callback for performing the remote attestation as well as the key exchange with the data provider
/// a.k.a., service provider. The function will return a wrapped ECDH key that implements Zeroize + Default trait.
/// Note that the AES128Key has the corresponding implementations.
#[must_use]
pub fn pobf_remote_attestation(
    socket_fd: c_int,
    spid: &Spid,
    linkable: i64,
    ra_type: u8,
    peer_pub_key: &[u8; ECP_COORDINATE_SIZE],
    signature: &[u8],
) -> AES128Key {
    ocall_log!(
        "[+] The remote attestation type is {}",
        if ra_type == 0 { "EPID" } else { "DCAP" }
    );
    ocall_log!("[+] Start to generate ECDH session key and perform remote attestation!");

    // We need to get the ECDH key.
    // Panic on error.
    let dh_session = perform_ecdh(peer_pub_key, signature).unwrap();
    assert_eq!(
        dh_session.session_status(),
        DhStatus::InProgress,
        "[-] Mismatched session status. Check if the code is correct?",
    );

    // Convert AlignKey128bit to AES128Key.
    let session_key = AES128Key::from_ecdh_key(&dh_session).unwrap();

    // Perform remote attestation.
    let mut res = SgxStatus::Success;
    match ra_type {
        0u8 => res = perform_epid_remote_attestation(socket_fd, spid, linkable, &dh_session),
        1u8 => res = perform_dcap_remote_attestation(socket_fd, &dh_session),
        _ => panic!("[-] Not a valid remote attestation type! Choose EPID or DCAP instead."),
    }

    if !res.is_success() {
        panic!("[-] Remote attestation failed due to {:?}.", res);
    }

    session_key
}

/// Receives the data as a vector from the data provider (encrypted data).
#[must_use]
pub fn pobf_receive_data(socket_fd: c_int) -> VecAESData {
    verified_log!("[+] Receiving secret data from data provider...");

    match receive_data(socket_fd) {
        Ok(data) => data,
        Err(e) => {
            panic!("[-] Failed to receive data due to {:?}.", e);
        }
    }
}
