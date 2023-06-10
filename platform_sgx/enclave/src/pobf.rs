#![forbid(unsafe_code)]

use crate::dh::*;
use crate::networking_utils::*;
use crate::ocall::*;
use crate::vecaes::{AES128Key, VecAESData};
use crate::{ocall_log, verified_log};
use alloc::vec;
use alloc::vec::Vec;
use clear_on_drop::*;
use mirai_annotations::*;
use sgx_types::error::SgxStatus;
use sgx_types::types::{c_int, Spid};

// Settings for private computation functions.
cfg_if::cfg_if! {
   if #[cfg(feature = "task_tvm")] {
        use evaluation_tvm::private_computation;
    } else if #[cfg(feature = "task_db")] {
        use db::private_computation;
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
    } else if #[cfg(feature = "task_sample")] {
        use sample_add::private_computation;
    } else {
        /// Identity task.
        pub fn private_computation(input: Vec<u8>) -> Vec<u8> {
            input
        }
    }
}

// Task.
cfg_if::cfg_if! {
    if #[cfg(mirai)] {
        use crate::mirai_types::mirai_comp::SecretTaint;
        use crate::mirai_types::task::*;
    } else {
        use pobf_state::task::*;

        type SecretTaint = ();
    }
}

pub fn private_vec_compute<T>(input: T) -> T
where
    T: From<Vec<u8>> + Into<Vec<u8>>,
{
    cfg_if::cfg_if! {
        if #[cfg(feature = "mirai_sample")] {
            use crate::userfunc::sample_add;

            let input_vec: Vec<u8> = input.into();
            let output_vec = sample_add(input_vec);
            T::from(output_vec)
          } else if #[cfg(mirai)] {
            // Omit the userfunc because we are verifying the framework.
            add_tag!(&input, SecretTaint);
            input
        } else {
            let input_vec: Vec<u8> = input.into();

            cfg_if::cfg_if! {
                if #[cfg(feature = "task_polybench")] {
                    let timing_function = || unix_time(3).unwrap();
                    let output_vec = private_computation(input_vec, &timing_function);
                } else {
                    let output_vec = private_computation(input_vec);
                }
            }



            T::from(output_vec)
        }
    }
}

#[cfg(mirai)]
pub fn pobf_workflow(
    socket_fd: c_int,
    spid: &Spid,
    linkable: i64,
    ra_type: u8,
    public_key: &[u8; ECP_COORDINATE_SIZE],
    signature: &[u8],
    _: u16,
) -> VecAESData {
    precondition!(does_not_have_tag!(&socket_fd, SecretTaint));
    precondition!(does_not_have_tag!(spid, SecretTaint));
    precondition!(does_not_have_tag!(&linkable, SecretTaint));
    precondition!(does_not_have_tag!(&ra_type, SecretTaint));
    precondition!(does_not_have_tag!(public_key, SecretTaint));
    precondition!(does_not_have_tag!(signature, SecretTaint));

    let begin = unix_time(3).unwrap();

    let receive_callback = move || pobf_receive_data(socket_fd);
    let ra_callback =
        move || pobf_remote_attestation(socket_fd, spid, linkable, ra_type, public_key, signature);

    let template = ComputingTaskTemplate::<Initialized>::new();
    verify!(does_not_have_tag!(&template, SecretTaint));

    let session = ComputingTaskSession::establish_channel(template, &ra_callback);
    verify!(has_tag!(&session, SecretTaint));

    let task_data_received = ComputingTask::receive_data(session, &receive_callback);
    verify!(has_tag!(&task_data_received, SecretTaint));

    // Because MIRAI does not know "encryption" would sanitize the tag, so we
    // make encryption as an assumed sanitization operation so that we can
    // continue the verification.
    let task_result_encrypted = task_data_received.compute(&private_vec_compute);
    #[cfg(not(feature = "mirai_sample"))]
    assume!(does_not_have_tag!(&task_result_encrypted, SecretTaint));
    #[cfg(feature = "mirai_sample")]
    verify!(does_not_have_tag!(&task_result_encrypted, SecretTaint));

    let result = task_result_encrypted.take_result();
    verify!(does_not_have_tag!(&result, SecretTaint));

    let end = unix_time(3).unwrap();
    // Get execution time.

    let elapsed = core::time::Duration::from_nanos(end - begin);
    verified_log!(SecretTaint, "Job finished. Time used: {:?}.", elapsed);

    result
}

#[cfg(feature = "native_enclave")]
pub fn pobf_workflow(
    socket_fd: c_int,
    spid: &Spid,
    linkable: i64,
    ra_type: u8,
    public_key: &[u8; ECP_COORDINATE_SIZE],
    signature: &[u8],
    _stack: u16,
) -> VecAESData {
    use pobf_state::*;

    let begin = unix_time(3).unwrap();

    let key = pobf_remote_attestation(socket_fd, spid, linkable, ra_type, public_key, signature);
    let data = pobf_receive_data(socket_fd);
    let decrypted = data.decrypt(&key).unwrap();
    let result = private_vec_compute(decrypted);
    let encrypted = result.encrypt(&key).unwrap();

    let end = unix_time(3).unwrap();
    // Get execution time.

    let elapsed = core::time::Duration::from_nanos(end - begin);
    verified_log!(SecretTaint, "Job finished. Time used: {:?}.", elapsed);

    encrypted
}

#[cfg(feature = "native_zeroize")]
pub fn pobf_workflow(
    socket_fd: c_int,
    spid: &Spid,
    linkable: i64,
    ra_type: u8,
    public_key: &[u8; ECP_COORDINATE_SIZE],
    signature: &[u8],
    stack: u16,
) -> VecAESData {
    use clear_on_drop::*;
    use pobf_state::*;

    let f1 = || pobf_remote_attestation(socket_fd, spid, linkable, ra_type, public_key, signature);
    let f2 = || pobf_receive_data(socket_fd);

    let begin = unix_time(3).unwrap();
    let key = clear_stack_on_return_fnonce(stack as _, f1);
    let data = clear_stack_on_return_fnonce(stack as _, f2);
    let f = || data.decrypt(&key).unwrap();
    let decrypted = clear_stack_on_return_fnonce(stack as _, f);
    let f = || private_vec_compute(decrypted);
    let result = clear_stack_on_return_fnonce(stack as _, f);
    let f = || result.encrypt(&key).unwrap();
    let encrypted = clear_stack_on_return_fnonce(stack as _, f);

    let end = unix_time(3).unwrap();
    // Get execution time.

    let elapsed = core::time::Duration::from_nanos(end - begin);
    verified_log!(SecretTaint, "Job finished. Time used: {:?}.", elapsed);

    encrypted
}

#[cfg(all(
    not(feature = "native_enclave"),
    not(mirai),
    not(feature = "native_zeroize")
))]
pub fn pobf_workflow(
    socket_fd: c_int,
    spid: &Spid,
    linkable: i64,
    ra_type: u8,
    public_key: &[u8; ECP_COORDINATE_SIZE],
    signature: &[u8],
    stack: u16,
) -> VecAESData {
    let begin = unix_time(3).unwrap();
    let receive_callback = move || pobf_receive_data(socket_fd);
    let ra_callback =
        move || pobf_remote_attestation(socket_fd, spid, linkable, ra_type, public_key, signature);

    let f = || ComputingTaskTemplate::<Initialized>::new();
    let template = clear_stack_and_regs_on_return(stack as _, f);
    let f = || ComputingTaskSession::establish_channel(template, ra_callback);
    let session = clear_stack_and_regs_on_return(stack as _, f);
    let f = || ComputingTask::receive_data(session, receive_callback);
    let task_data_received = clear_stack_and_regs_on_return(stack as _, f);
    let f = || task_data_received.compute(&private_vec_compute);
    let task_result_encrypted = clear_stack_and_regs_on_return(stack as _, f);
    let f = || task_result_encrypted.take_result();
    let result = clear_stack_and_regs_on_return(stack as _, f);

    let end = unix_time(3).unwrap();
    // Get execution time.
    let output = pobf_state::get_time_summary(2100.0);
    // verified_log!("[+] Cost breakup: {output}");

    let elapsed = core::time::Duration::from_nanos(end - begin);
    verified_log!(
        SecretTaint,
        "Job finished. Time used: {:?}; breakup {}",
        elapsed,
        output
    );

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
    verified_log!("[+] Start to generate ECDH session key and perform remote attestation!");

    // We need to get the ECDH key.
    // Panic on error.
    let dh_session = perform_ecdh(peer_pub_key, signature).unwrap();
    add_tag!(&dh_session, SecretTaint);

    assert_eq!(
        dh_session.session_status(),
        DhStatus::InProgress,
        "[-] Mismatched session status. Check if the code is correct?",
    );

    // Convert AlignKey128bit to AES128Key.
    let session_key = AES128Key::from_ecdh_key(&dh_session).unwrap();
    // The session key is secret.
    verify!(has_tag!(&session_key, SecretTaint));

    // Perform remote attestation.
    let mut res = SgxStatus::Success;
    match ra_type {
        0u8 => res = perform_epid_remote_attestation(socket_fd, spid, linkable, &dh_session),
        1u8 => res = perform_dcap_remote_attestation(socket_fd, &dh_session),
        _ => assume_unreachable!(
            "[-] Not a valid remote attestation type! Choose EPID or DCAP instead."
        ),
    }

    if res != SgxStatus::Success {
        assume_unreachable!("[-] Remote attestation failed due to {:?}.", res);
    }

    session_key
}

/// Receives the data as a vector from the data provider (encrypted data).
#[must_use]
pub fn pobf_receive_data(socket_fd: c_int) -> VecAESData {
    verified_log!("[+] Receiving secret data from data provider...");

    let data = match receive_data(socket_fd) {
        Ok(data) => data,
        Err(e) => {
            assume_unreachable!("[-] Failed to receive data due to {:?}.", e);
        }
    };

    add_tag!(&data, SecretTaint);

    data
}
