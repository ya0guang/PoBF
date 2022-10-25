#![forbid(unsafe_code)]

use crate::dh::*;
use crate::ocall::*;
use crate::ra_utils::*;
use crate::types::*;
use crate::userfunc::vec_inc;
use crate::{ocall_log, verified_log};
use alloc::string::String;
use alloc::vec::Vec;
use clear_on_drop::clear_stack_and_regs_on_return;
use sgx_types::error::SgxResult;
use sgx_types::types::{c_int, Spid};
use zeroize::Zeroize;

pub fn pobf_private_computing(
    data_buffer: &[u8],
    sealed_key_buffer: &[u8],
    remote_attestation_callback: &dyn Fn() -> AES128Key,
    receive_data_callback: &dyn Fn() -> VecAESData,
) -> SgxResult<VecAESData> {
    // FIXME: move these two callbacks into type state. Now they are called for testing.
    let _ = remote_attestation_callback();
    let _ = receive_data_callback();

    verified_log!("[+] PoBF sample task AES started...");
    // initialize data from buffer
    let input_key = AES128Key::from_sealed_buffer(sealed_key_buffer)?;
    let output_key = AES128Key::from_sealed_buffer(sealed_key_buffer)?;
    let data = VecAESData::from(data_buffer);

    // privacy violation: cannot call decrypt directly on the data
    // captured by: compiler error
    #[cfg(feature = "direct_decrypt")]
    data.decrypt(&input_key)?;

    // privacy violation: cannot see through the key
    // captured by: compiler error
    #[cfg(feature = "access_inner")]
    let raw_key = input_key.inner;

    // safety violation: cannot read the key through dereferencing using unsafe
    // captured by: compiler error
    #[cfg(feature = "raw_read")]
    let raw_key = unsafe { *(&input_key as *const AES128Key as *const u8) };

    // safety violation: cannot write to the insecure world through dereferencing using unsafe
    // captured by: compiler error
    #[cfg(feature = "raw_write")]
    unsafe {
        *(0x3ffffff as *const u8 as *mut u8) = data_buffer[1];
    }

    // custom computation task
    let computation_task = &private_vec_compute;
    let f = || pobf_workflow(data, input_key, output_key, computation_task);

    clear_stack_and_regs_on_return(crate::DEFAULT_PAGE_SIZE_LEAF, f)
}

pub fn private_vec_compute<T>(input: T) -> T
where
    T: From<Vec<u8>> + Into<Vec<u8>>,
{
    let input_vec = input.into();

    let output_vec = vec_inc(input_vec);
    T::from(output_vec)
}

pub fn pobf_workflow<D: EncDec<K>, K: Default>(
    input_sealed: D,
    input_key: K,
    output_key: K,
    computation_task: &dyn Fn(D) -> D,
) -> SgxResult<D>
where
    K: Zeroize,
{
    let enc_in: ProtectedAssets<Encrypted, Input, D, K> =
        ProtectedAssets::new(input_sealed, input_key, output_key);

    let dec_in: ProtectedAssets<Decrypted, Input, D, K> = enc_in.decrypt()?;

    // Typestate violation: cannot take inner data from decrypted data
    // captured by: compiler error
    #[cfg(feature = "disallowed_trans")]
    let dec_in_data = dec_in.take();

    #[cfg(feature = "rude_copy")]
    let data_copy = dec_in.copy();

    let dec_out: ProtectedAssets<Decrypted, Output, D, K> = dec_in.invoke(computation_task)?;

    // privacy violation: cannot take the inner data from ProtectedAssets
    // captured by: compiler error
    #[cfg(feature = "access_key")]
    let de_out_data = dec_out.data;

    let en_out: ProtectedAssets<Encrypted, Output, D, K> = dec_out.encrypt()?;

    Ok(en_out.take())
}

/// This is a callback for performing the remote attestation as well as the key exchange with the data provider
/// a.k.a., service provider. The function will return a wrapped ECDH key that implements Zeroize + Default trait.
/// Note that the AES128Key has the corresponding implementations.
#[must_use]
pub fn pobf_remote_attestation(
    socket_fd: c_int,
    spid: &Spid,
    linkable: i64,
    peer_pub_key: &[u8; ECP_COORDINATE_SIZE],
    signature: &[u8],
) -> AES128Key {
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
    let res = perform_remote_attestation(socket_fd, spid, linkable, &dh_session);
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
