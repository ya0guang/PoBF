use crate::dh::*;
use crate::ocall::*;
use crate::ocall_log;
use crate::utils::process_raw_cert;
use crate::vecaes::VecAESData;
use alloc::{str, string::*, vec, vec::*};
use sgx_crypto::ecc::EcPublicKey;
use sgx_crypto::sha::Sha256;
use sgx_tse::*;
use sgx_tseal::seal::SealedData;
use sgx_tseal::seal::UnsealedData;
use sgx_types::error::*;
use sgx_types::types::*;

// A hardcoded certificate bytes from Intel CA Cert.
// We reject reading certificate from the outside world to prevent forage.
// Anyone can download this cert from Intel SGX developer zone.
// Link: https://certificates.trustedservices.intel.com/Intel_SGX_Attestation_RootCA.cer or
//       https://certificates.trustedservices.intel.com/Intel_SGX_Attestation_RootCA.pem
pub const IAS_CA_CERT: &'static [u8] = include_bytes!("../Intel_SGX_Attestation_RootCA.cer");

// The path where report stores.
pub const REPORT_PATH: &'static str = "../report.bin";
pub const REPORT_AAD: &'static str = "PoBF/enclave&INTEL-RA-V4";

// Buffer size control.
pub const SMALL_BUF_SIZE: usize = 128;
pub const MEDIUM_BUF_SIZE: usize = 1024;
pub const LARGE_BUF_SIZE: usize = 4096;

// For webpki trust anchor.
type SignatureAlgorithms = &'static [&'static webpki::SignatureAlgorithm];
static SUPPORTED_SIG_ALGS: SignatureAlgorithms = &[
    &webpki::ECDSA_P256_SHA256,
    &webpki::ECDSA_P256_SHA384,
    &webpki::ECDSA_P384_SHA256,
    &webpki::ECDSA_P384_SHA384,
    &webpki::RSA_PSS_2048_8192_SHA256_LEGACY_KEY,
    &webpki::RSA_PSS_2048_8192_SHA384_LEGACY_KEY,
    &webpki::RSA_PSS_2048_8192_SHA512_LEGACY_KEY,
    &webpki::RSA_PKCS1_2048_8192_SHA256,
    &webpki::RSA_PKCS1_2048_8192_SHA384,
    &webpki::RSA_PKCS1_2048_8192_SHA512,
    &webpki::RSA_PKCS1_3072_8192_SHA384,
];

pub struct QuoteWrapper {
    pub qe_report: Report,
    pub quote_nonce: QuoteNonce,
    pub quote_len: u32,
    pub quote: Vec<u8>,
}

pub fn perform_remote_attestation(
    socket_fd: c_int,
    spid: &Spid,
    linkable: i64,
    session: &DhSession,
) -> SgxStatus {
    // Step 1: Ocall to get the target information and the EPID.
    let res = init_quote();
    if let Err(e) = res {
        return e;
    }

    let ti = res.unwrap().0;
    let eg = res.unwrap().1;

    // Step 2: Forward this information to the application which later forwards to service provider who later verifies the information with the help of the IAS.
    ocall_log!("[+] Start to get SigRL from Intel!");
    let res = get_sigrl_from_intel(&eg, socket_fd, session.session_context().pub_k());
    if let Err(e) = res {
        return e;
    }

    let sigrl_buf = res.unwrap();

    // Step 3: Generate the report.
    ocall_log!("[+] Start to perform report generation!");
    // Extract the ecc handle.
    let res = get_report(&ti, session.session_context());
    if let Err(e) = res {
        return e;
    }

    let report = res.unwrap();

    // Step 4: Convert the report into a quote type.
    ocall_log!("[+] Start to perform quote generation!");
    let res = get_quote(&sigrl_buf, &report, &*spid, linkable);

    if let Err(e) = res {
        return e;
    }

    let qw = res.unwrap();
    let qe_report = &qw.qe_report;

    // Step 5: Verify this quote.
    let res = verify_report(qe_report);
    if let Err(e) = res {
        return e;
    }

    // Step 6: Check if the qe_report is produced on the same platform.
    if !same_platform(qe_report, &ti) {
        ocall_log!("[-] This quote report does belong to this platform.");
        return SgxStatus::UnrecognizedPlatform;
    }

    ocall_log!("[+] This quote is genuine for this platform.");

    // Step 7: Check if this quote is replayed.
    if !check_quote_integrity(&qw) {
        ocall_log!("[-] This quote is tampered by malicious party. Abort.");
        return SgxStatus::BadStatus;
    }

    ocall_log!("[+] The integrity of this quote is ok.");

    // Step 8: This quote is valid. Forward this quote to IAS.
    ocall_log!("[+] Start to get quote report from Intel!");
    let res = get_quote_report_from_intel(&qw, socket_fd);
    if let Err(e) = res {
        return e;
    }

    ocall_log!("[+] Successfully get quote report.");

    // Step 9: Verify this quote report: is this genuinely issues by Intel?
    ocall_log!("[+] Start to verify quote report!");
    let quote_triple = res.unwrap();
    let quote_report = quote_triple.0;
    let sig = quote_triple.1;
    let cert = quote_triple.2;

    if !verify_quote_report(&quote_report, &sig, &cert) {
        ocall_log!("[-] This quote report is tampered by malicious party. Abort.");
        return SgxStatus::BadStatus;
    }

    ocall_log!("[+] Signature is valid!");

    SgxStatus::Success
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

/// Invokes an OCALL to send the generated EPID to the Intel for getting the corresponding Sig
/// revocation list. This function also sends the public key of the enclave to the peer.
pub fn get_sigrl_from_intel(
    eg: &EpidGroupId,
    socket_fd: c_int,
    pub_k: &EcPublicKey,
) -> SgxResult<Vec<u8>> {
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
            pub_k.as_ref() as *const u8,
            pub_k.as_ref().len() as u32,
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

/// A safe wrapper for `ocall_receive_data`.
pub fn receive_data(socket_fd: c_int) -> SgxResult<VecAESData> {
    let mut encrypted_data_buf = vec![0u8; 2048];
    let mut str_len = String::with_capacity(512);
    let mut data_size = 0u32;

    // Perform an ocall.
    let mut ret_val = SgxStatus::Success;
    let ret = unsafe {
        ocall_receive_data(
            &mut ret_val,
            socket_fd,
            encrypted_data_buf.as_mut_ptr(),
            2048u32,
            &mut data_size,
        )
    };

    if !ret.is_success() {
        return Err(ret);
    }

    // Truncate the buffer.
    encrypted_data_buf.truncate(data_size as usize);

    Ok(VecAESData::from(encrypted_data_buf.as_slice()))
}

pub fn get_report(ti: &TargetInfo, ecc: &DhEccContext) -> SgxResult<Report> {
    let prv_k = &ecc.prv_k();
    let pub_k = &ecc.pub_k();

    // Fill ecc256 public key into report_data. This is the attestation key.
    let mut report_data = ReportData::default();
    let mut pub_k_gx = pub_k.public_key().gx.clone();
    pub_k_gx.reverse();
    let mut pub_k_gy = pub_k.public_key().gy.clone();
    pub_k_gy.reverse();
    report_data.d[..ECP256_KEY_SIZE].clone_from_slice(&pub_k_gx);
    report_data.d[ECP256_KEY_SIZE..].clone_from_slice(&pub_k_gy);

    // Get the report.
    match Report::for_target(ti, &report_data) {
        Ok(res) => Ok(res),
        Err(e) => Err(e),
    }
}

/// The identity of an ISV enclave and the validity of the platform can be verified using Attestation
/// Service for Intel SGX. The Attestation Service verifies only the validity of the platform. It is the
/// responsibility of the Service Provider to validate the ISV enclave identity. As a result of this
/// process, an Attestation Verification Report will be generated and sent back to the SP. The report
/// will include verification results for:
/// * `sgx_quote_t` structure generated by the platform for the ISV enclave
/// * Optional SGX Platform Service Security Property Descriptor provided by the platform.
pub fn get_quote(
    sigrl_buf: &Vec<u8>,
    report: &Report,
    spid: &Spid,
    linkable: i64,
) -> SgxResult<QuoteWrapper> {
    // Parse the quote type according to whether the request is linkable for single platform.
    let quote_type = match linkable {
        0 => QuoteSignType::Unlinkable,
        _ => QuoteSignType::Linkable,
    };

    let mut quote_nonce = QuoteNonce {
        rand: [0u8; AESCBC_IV_SIZE],
    };
    let mut os_rng = sgx_trts::rand::Rng::new();
    os_rng.fill_bytes(&mut quote_nonce.rand);
    ocall_log!("[+] Quote nonce generated.");

    // Prepare quote.
    let mut qe_report = Report::default();
    let mut return_quote_buf = [0; LARGE_BUF_SIZE];
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
            LARGE_BUF_SIZE as u32,
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

pub fn verify_report(qe_report: &Report) -> SgxResult<()> {
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

/// Returns a timepoint from the outside world. Unwraps an unsafe function here.
/// A pitfall of getting a 'trusted' time source from within the enclave is that
/// there is no "accurate" timestamp that be fetched by the enclave. A legacy
/// solution would be to fetch the timestamp using the /dev/mei0, but the time
/// can be delayed deliberately so that the accuracy of timestamp is tampered, as
/// this operation requires a network connection to Intel. So we cannot define
/// accuracy here, nor "trusted". However, at least, we need this functionality.
pub fn unix_time() -> SgxResult<u64> {
    let mut timestamp = 0u64;
    let mut ret = SgxStatus::Success;

    let res = unsafe { ocall_get_timepoint(&mut ret, &mut timestamp) };

    match res {
        SgxStatus::Success => Ok(timestamp),
        _ => Err(res),
    }
}

/// Returns true if the quote report is genuinely issued by Intel.
pub fn verify_quote_report(quote_report: &Vec<u8>, sig: &Vec<u8>, cert: &Vec<u8>) -> bool {
    // Decode each data field.
    let cert_processed = process_raw_cert(&cert);
    let sig_decoded = base64::decode(&sig).unwrap();
    let cert_decoded = base64::decode(&cert_processed).unwrap();

    // Construct a trust chain from the decoded certificate from IAS.
    let trust_chain = vec![cert_decoded.as_slice()];

    // Construct a certificate object from cert_decoded.
    // We use webpki with a patched binding to the `ring` crypto library.
    // Alternatives:
    //  * ring: not compatible with SGX; causes duplicate std symbols.
    //  * webpki: not compatible with SGX since it is dependent on low-level implementations of ring.
    //  * patched-ring: OK with SGX SDK v2.0.0.
    let sig_cert = webpki::EndEntityCert::try_from(cert_decoded.as_slice())
        .map_err(|e| {
            ocall_log!("[-] Invalid certificate for IAS. Error: {:?}", e);
            return false;
        })
        .unwrap();

    // We use an OCALL to get the current timestamp.
    let cur_time = unix_time().unwrap();
    ocall_log!("[+] Get current time: {}", cur_time);

    // Verify if the chain is rooted in
    // a trusted Attestation Report Signing CA Certificate. We have hardcoded the CA cert
    // into the enclave, so it must be secure.
    let trust_anchor = webpki::TrustAnchor::try_from_cert_der(IAS_CA_CERT).unwrap();

    if let Err(e) = sig_cert.verify_is_valid_tls_server_cert(
        SUPPORTED_SIG_ALGS,
        &webpki::TlsServerTrustAnchors(&[trust_anchor]),
        &trust_chain,
        webpki::Time::from_seconds_since_unix_epoch(cur_time),
    ) {
        ocall_log!("[-] This IAS certificate is invalid! Error: {:?}", e);
        return false;
    }

    ocall_log!("[+] IAS certificate check passed!");

    // An interesting fact about this is that if we do not use patched version of ring,
    // then verification becomes an endless loop.
    match sig_cert.verify_signature(
        &webpki::RSA_PKCS1_2048_8192_SHA256,
        quote_report,
        &sig_decoded,
    ) {
        Ok(()) => true,
        Err(e) => {
            ocall_log!("[-] The signature is invalid! Error: {:?}", e);
            false
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
    let lhs_hash = &qw.qe_report.body.report_data.d[..MAC_256BIT_SIZE];

    ocall_log!("[+] Checking hash of this quote!");
    ocall_log!("[+] The expected hash should be {:02x?}", rhs_hash.hash);
    ocall_log!("[+] The real hash is given by {:02x?}", lhs_hash);

    lhs_hash == rhs_hash.hash
}

pub fn get_quote_report_from_intel(
    qw: &QuoteWrapper,
    socket_fd: c_int,
) -> SgxResult<(Vec<u8>, Vec<u8>, Vec<u8>)> {
    let mut retval = SgxStatus::Success;

    // Prepare three buffers.
    let mut quote_report = vec![0u8; LARGE_BUF_SIZE];
    let mut sig = vec![0u8; LARGE_BUF_SIZE];
    let mut cert = vec![0u8; LARGE_BUF_SIZE];
    let mut quote_report_len = 0u32;
    let mut sig_len = 0u32;
    let mut cert_len = 0u32;

    let res = unsafe {
        ocall_get_quote_report_from_intel(
            &mut retval,
            socket_fd,
            qw.quote.as_ptr(),
            qw.quote_len,
            quote_report.as_mut_ptr(),
            LARGE_BUF_SIZE as u32,
            &mut quote_report_len,
            sig.as_mut_ptr(),
            LARGE_BUF_SIZE as u32,
            &mut sig_len,
            cert.as_mut_ptr(),
            LARGE_BUF_SIZE as u32,
            &mut cert_len,
        )
    };

    match res {
        SgxStatus::Success => {
            // Truncate the vectors.
            quote_report.truncate(quote_report_len as usize);
            sig.truncate(sig_len as usize);
            cert.truncate(cert_len as usize);

            Ok((quote_report, sig, cert))
        }
        _ => Err(res),
    }
}

/// After the remote attestation is done, we can temporarily store the report on the remote machine,
/// and we do not need to repeat the boilerplate attestation for a while. The user can decide if she
/// thinks the report should be expired and re-issues a new request for the remote attestation report.
pub fn seal_attestation_report(attestation_report: &Vec<u8>) -> SgxResult<()> {
    let sealed_data = SealedData::<[u8]>::seal(attestation_report, Some(REPORT_AAD.as_bytes()))?;
    let sealed_data_bytes = sealed_data.into_bytes().unwrap();

    let mut ret_val = SgxStatus::Success;

    let res = unsafe {
        ocall_write_data(
            &mut ret_val,
            REPORT_PATH.as_ptr(),
            REPORT_PATH.len() as u32,
            sealed_data_bytes.as_ptr(),
            sealed_data_bytes.len() as u32,
        )
    };

    match res {
        SgxStatus::Success => Ok(()),
        _ => Err(res),
    }
}

pub fn unseal_attestation_report() -> SgxResult<Vec<u8>> {
    let mut unsealed_data_bytes = vec![0u8; LARGE_BUF_SIZE];
    let mut ret_val = SgxStatus::Success;
    let mut data_size = 0u32;

    let res = unsafe {
        ocall_read_data(
            &mut ret_val,
            REPORT_PATH.as_ptr(),
            REPORT_PATH.len() as u32,
            unsealed_data_bytes.as_mut_ptr(),
            LARGE_BUF_SIZE as u32,
            &mut data_size,
        )
    };

    if res != SgxStatus::Success {
        return Err(res);
    }

    // Truncate the buffer.
    unsealed_data_bytes.truncate(data_size as usize);
    // Unseal it.
    let unsealed_data = UnsealedData::<[u8]>::unseal_from_bytes(unsealed_data_bytes)?;
    let aad = alloc::str::from_utf8(unsealed_data.to_aad()).unwrap();

    if aad != REPORT_AAD {
        Err(SgxStatus::NoPrivilege)
    } else {
        Ok(unsealed_data.to_plaintext().to_vec())
    }
}