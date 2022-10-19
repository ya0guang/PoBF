use sgx_crypto::ecc::*;
use sgx_tdh::Responder;
use sgx_types::{error::SgxResult, types::AlignKey128bit};

/// Time for expiration. We currently set it to 600 seconds (5 min).
/// If the key is expired, the both sides are notified and then re-negotiate a new one.
pub const DH_KEY_EXPIRATION: i64 = 600;

/// Denotes a Diffie-Hellman session status.
/// * `Closed` => This is either an invalid context or new context.
/// * `InProgress` => Not finished yet.
/// * `Active` => Valid, and a session key can be extracted from this status.
/// * (not sure) `Expired` => The session is valid but expired given the time limit.
#[derive(Debug)]
pub enum DhStatus {
    Closed,
    InProgress(Responder),
    Active(AlignKey128bit),
    // Maybe?
    Expired,
}

impl Default for DhStatus {
    fn default() -> Self {
        DhStatus::Closed
    }
}

/// A wrapper class for an empheral Diffie-Hellman session with the client.
#[derive(Debug)]
pub struct DhEccContext {
    ecc_handle: EcKeyPair,
    pub_k: EcPublicKey,
    prv_k: EcPrivateKey,
}

/// Defines a full Diffie-Hellman context.
#[derive(Debug, Default)]
pub struct DhSession {
    // A random nonce that marks this DH context.
    session_id: u64,
    session_status: DhStatus,
}

impl DhEccContext {
    pub fn ecc_handle(&self) -> &EcKeyPair {
        &self.ecc_handle
    }

    pub fn pub_k(&self) -> &EcPublicKey {
        &self.pub_k
    }

    pub fn prv_k(&self) -> &EcPrivateKey {
        &self.prv_k
    }
}

/// Opens an empheral Diffie-Hellman session context.
pub fn open_dh_session() -> SgxResult<DhEccContext> {
    // Open the ECC context and sample a key pair.
    let ecc_handle = EcKeyPair::create()?;
    let prv_k = ecc_handle.private_key();
    let pub_k = ecc_handle.public_key();

    Ok(DhEccContext {
        ecc_handle,
        pub_k,
        prv_k,
    })
}
