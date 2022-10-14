use crate::ocall::*;
use crate::ocall_log;
use alloc::{vec, vec::*};
use sgx_crypto::ecc::EcKeyPair;
use sgx_crypto::sha::Sha256;
use sgx_tse::*;
use sgx_types::error::*;
use sgx_types::types::*;

pub struct QuoteWrapper {
    pub qe_report: Report,
    pub quote_nonce: QuoteNonce,
    pub quote_len: u32,
    pub quote: Vec<u8>,
}

pub fn init_quote() -> SgxResult<(TargetInfo, EpidGroupId)> {
    let mut eg = EpidGroupId::default();
    let mut ti = TargetInfo::default();
    let mut ret = SgxStatus::Success;
    let res = unsafe { ocall_sgx_init_quote(&mut ret, &mut ti, &mut eg) };

    match res {
        SgxStatus::Success => Ok((ti, eg)),
        _ => Err(res),
    }
}

pub fn get_sigrl_from_intel(eg: &EpidGroupId, socket_fd: c_int) -> SgxResult<Vec<u8>> {
    let mut sigrl_len = 0u32;
    let mut sigrl_buf = vec![0u8; 128];

    let mut ret = SgxStatus::Success;
    let res = unsafe {
        ocall_get_sigrl_from_intel(
            &mut ret,
            eg,
            eg.len(),
            socket_fd,
            sigrl_buf.as_mut_ptr(),
            128,
            &mut sigrl_len,
        )
    };

    match res {
        SgxStatus::Success => {
            // Throw away useless bytes.
            sigrl_buf.truncate(sigrl_len as usize);
            Ok(sigrl_buf)
        }

        _ => Err(res),
    }
}

pub fn get_report(ti: &TargetInfo, sigrl_buf: &Vec<u8>, spid: &Spid) -> SgxResult<Report> {
    let sigrl = sigrl_buf.as_slice();
    // Open the ECC context and sample a key pair.
    let ecc_handle = EcKeyPair::create().unwrap();
    let prv_k = ecc_handle.private_key();
    let pub_k = ecc_handle.public_key();

    // Fill ecc256 public key into report_data. This is the attestation key.
    let mut report_data = ReportData::default();
    let mut pub_k_gx = pub_k.public_key().gx.clone();
    pub_k_gx.reverse();
    let mut pub_k_gy = pub_k.public_key().gy.clone();
    pub_k_gy.reverse();
    report_data.d[..32].clone_from_slice(&pub_k_gx);
    report_data.d[32..].clone_from_slice(&pub_k_gy);

    // Get the report.
    Report::for_target(ti, &report_data)
}

pub fn get_quote(sigrl_buf: &Vec<u8>, report: &Report, spid: &Spid) -> SgxResult<QuoteWrapper> {
    // We currently hardcode this the subscription type to linkable.
    let quote_type = QuoteSignType::Linkable;
    let mut quote_nonce = QuoteNonce { rand: [0u8; 16] };
    let mut os_rng = sgx_trts::rand::Rng::new();
    os_rng.fill_bytes(&mut quote_nonce.rand);
    ocall_log!("[+] Quote nonce generated.");

    // Prepare quote.
    let mut qe_report = Report::default();
    const RET_QUOTE_BUF_LEN: u32 = 2048;
    let mut return_quote_buf: [u8; RET_QUOTE_BUF_LEN as usize] = [0; RET_QUOTE_BUF_LEN as usize];
    let mut quote_len: u32 = 0;
    let mut ret = SgxStatus::Success;

    // Need to convert sigrl pointer to null if the length is zero.
    // This is a must. If we invoke `sgx_calc_quote_size` with a zero-lengthed non-null
    // pointer, the function will return an error code indicating `InvalidParam`.
    let (sigrl_ptr, sigrl_len) = if sigrl_buf.len() == 0 {
        (core::ptr::null(), 0)
    } else {
        (sigrl_buf.as_ptr(), sigrl_buf.len() as u32)
    };

    // Call get_quote.
    let res = unsafe {
        // All these data are forwarded to the service provider.
        ocall_get_quote(
            &mut ret,
            sigrl_ptr,
            sigrl_len,
            report,
            quote_type,
            spid,
            &quote_nonce,
            &mut qe_report,
            return_quote_buf.as_mut_ptr(),
            RET_QUOTE_BUF_LEN,
            &mut quote_len,
        )
    };

    match res {
        SgxStatus::Success => Ok(QuoteWrapper {
            qe_report,
            quote_nonce,
            quote_len,
            quote: return_quote_buf.to_vec(),
        }),

        _ => Err(res),
    }
}

pub fn verify_report(qe_report: &Report, quote_nonce: &QuoteNonce) -> SgxResult<()> {
    match qe_report.verify() {
        Err(e) => {
            ocall_log!("[-] Quote report verification failed due to `{:?}`.", e);
            return Err(e);
        }
        Ok(_) => {
            ocall_log!("[+] Quote report verification passed.");
            return Ok(());
        }
    }
}

pub fn same_platform(qe_report: &Report, ti: &TargetInfo) -> bool {
    ti.mr_enclave.m == qe_report.body.mr_enclave.m
        && ti.attributes.flags == qe_report.body.attributes.flags
        && ti.attributes.xfrm == qe_report.body.attributes.xfrm
}

/// Checks `qe_report` to defend against replay attack.
///
/// The purpose of `p_qe_report` is for the ISV enclave to confirm the QUOTE
/// it received is not modified by the untrusted SW stack, and not a replay.
/// The implementation in QE is to generate a REPORT targeting the ISV
/// enclave (target info from `p_report)`, with the lower 32Bytes in
/// `report.data = SHA256(p_nonce||p_quote)`. The ISV enclave can verify the
/// `p_qe_report` and report.data to confirm the QUOTE has not be modified and
/// is not a replay. It is optional, but we enforce this check.
pub fn check_quote_integrity(qw: &QuoteWrapper) -> bool {
    // Prepare a buffer for hash.
    let mut rhs_vec = qw.quote_nonce.rand.to_vec();
    rhs_vec.extend(&qw.quote[..qw.quote_len as usize]);

    let mut shactx = Sha256::new().unwrap();
    shactx.update(&rhs_vec[..]).unwrap();
    let rhs_hash = shactx.finalize().unwrap();
    let lhs_hash = &qw.qe_report.body.report_data.d[..32];

    ocall_log!("[+] Checking hash of this quote!");
    ocall_log!("[+] The expected hash should be {:02x?}", rhs_hash.hash);
    ocall_log!("[+] The real hash is given by {:02x?}", lhs_hash);

    lhs_hash == rhs_hash.hash
}

pub fn get_quote_report_from_intel(qw: &QuoteWrapper, socket_fd: c_int) -> SgxResult<()> {
    let mut retval = SgxStatus::Success;

    let res = unsafe {
        ocall_get_quote_report_from_intel(
            &mut retval,
            socket_fd,
            qw.quote.as_ptr(),
            qw.quote.len() as u32,
        )
    };

    match res {
        SgxStatus::Success => Ok(()),
        _ => Err(res),
    }
}
