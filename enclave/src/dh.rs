use sgx_crypto::ecc::*;
use sgx_types::{
    error::{SgxResult, SgxStatus},
    types::{AlignKey128bit, DhSessionRole, Ec256PublicKey, ECP256_KEY_SIZE},
};

/// Time for expiration. We currently set it to 600 seconds (5 min).
/// If the key is expired, the both sides are notified and then re-negotiate a new one.
pub const DH_KEY_EXPIRATION: i64 = 600;

/// A magic string that identifies the key.
pub const KDF_MAGIC: &'static str = "enclave_key";

/// Generated from a NIST P256 ecliptic curve.
/// Be aware of the endianess. g^x and g^y are formatted in little endian.
pub const SP_PUBLIC_KEY: &'static [u8; 64] = &[
    0x21, 0x5b, 0xfa, 0x20, 0x80, 0x67, 0x36, 0x85, 0xf6, 0x19, 0xf0, 0xcb, 0x0f, 0x95, 0x31, 0x7b,
    0x1b, 0x44, 0x8f, 0x54, 0x0b, 0x49, 0x57, 0x19, 0x1f, 0x2e, 0x7b, 0x29, 0x83, 0x6a, 0x54, 0x5b,
    0xc5, 0xde, 0xdb, 0x90, 0x82, 0x69, 0x92, 0x1d, 0x99, 0xf6, 0xe4, 0x0f, 0x0c, 0x2f, 0x6d, 0x72,
    0xb3, 0x33, 0xa7, 0xa1, 0xcf, 0xcc, 0xb9, 0x95, 0xa1, 0x93, 0xe2, 0x0f, 0x5b, 0x80, 0xc1, 0x57,
];

/// A wrapper class for an empheral Diffie-Hellman session with the client.
/// Owned by the receiver. The key is define on the curve NIST P-256 a.k.a.
/// secp256r1, prime256v1.
#[derive(Debug)]
pub struct DhEccContext {
    ecc_handle: EcKeyPair,
    pub_k: EcPublicKey,
    prv_k: EcPrivateKey,
    shared_key: EcShareKey,
    smk: AlignKey128bit,
    role: DhSessionRole,
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

    pub fn shared_key(&self) -> &EcShareKey {
        &self.shared_key
    }

    pub fn smk(&self) -> &AlignKey128bit {
        &self.smk
    }
}

#[derive(Debug)]
pub struct Peer {
    pub role: DhSessionRole,
    pub_k: EcPublicKey,
}

impl From<&[u8; 64]> for Peer {
    fn from(peer_pub_k: &[u8; 64]) -> Self {
        // Convert from a raw byte array into Ecc256PubKey.
        let pub_k_gx = peer_pub_k[..ECP256_KEY_SIZE].to_vec();
        let pub_k_gy = peer_pub_k[ECP256_KEY_SIZE..].to_vec();
        let mut pub_256_k = Ec256PublicKey::default();

        pub_256_k.gx.copy_from_slice(
            pub_k_gx
                .iter()
                .copied()
                .rev()
                .collect::<alloc::vec::Vec<u8>>()
                .as_slice(),
        );
        pub_256_k.gy.copy_from_slice(
            pub_k_gy
                .iter()
                .copied()
                .rev()
                .collect::<alloc::vec::Vec<u8>>()
                .as_slice(),
        );

        Self {
            role: DhSessionRole::default(),
            pub_k: EcPublicKey::from(pub_256_k),
        }
    }
}

/// Denotes a Diffie-Hellman session status.
/// * `Closed` => This is either an invalid context or new context.
/// * `InProgress` => Not finished yet.
/// * `Active` => Valid, and a session key can be extracted from this status.
/// * (not sure) `Expired` => The session is valid but expired given the time limit.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum DhStatus {
    Closed,
    InProgress,
    Active,
    // Maybe?
    Expired,
}

impl Default for DhStatus {
    fn default() -> Self {
        DhStatus::Closed
    }
}

/// Defines a full Diffie-Hellman context.
#[derive(Debug)]
pub struct DhSession {
    // A random nonce that marks this DH context.
    session_id: u64,
    session_status: DhStatus,
    session_context: DhEccContext,
}

impl DhSession {
    pub fn session_id(&self) -> u64 {
        self.session_id
    }

    pub fn session_status(&self) -> DhStatus {
        self.session_status
    }

    pub fn mut_session_status(&mut self) -> &mut DhStatus {
        &mut self.session_status
    }

    pub fn session_context(&self) -> &DhEccContext {
        &self.session_context
    }

    pub fn mut_session_contexy(&mut self) -> &mut DhEccContext {
        &mut self.session_context
    }

    pub fn compute_shared_key(&mut self, peer: &Peer) -> SgxResult<()> {
        // Should first check the status.
        if self.session_status != DhStatus::InProgress {
            return Err(SgxStatus::InvalidState);
        }

        // Check if the public key is derived from this private key.
        if self.session_context.pub_k != self.session_context.prv_k.export_public_key().unwrap() {
            // Corrupted input.
            return Err(SgxStatus::InvalidParameter);
        }

        // Check if this is the reponder.
        if self.session_context.role != DhSessionRole::Responder
            || self.session_context.role == peer.role
        {
            return Err(SgxStatus::InvalidState);
        }

        // Compute the shared_key key.
        self.session_context.shared_key = self.session_context.prv_k.shared_key(&peer.pub_k)?;
        self.session_context.smk = self
            .session_context
            .shared_key
            .derive_key(KDF_MAGIC.as_bytes())?;

        Ok(())
    }
}

/// Opens an empheral Diffie-Hellman session context.
///
/// Since the enclave will receive a request from the SP, so we must know who should be
/// the intiator. We do not need to return a raw EccContext.
pub fn open_dh_session() -> SgxResult<DhSession> {
    // Generate a random number.
    let mut os_rng = sgx_trts::rand::Rng::new();
    let session_id = os_rng.next_u64();

    // Open the ECC context and sample a key pair.
    let ecc_handle = EcKeyPair::create()?;
    let prv_k = ecc_handle.private_key();
    let pub_k = ecc_handle.public_key();

    Ok(DhSession {
        session_id,
        session_status: DhStatus::InProgress,
        session_context: DhEccContext {
            ecc_handle,
            prv_k,
            pub_k,
            shared_key: EcShareKey::default(),
            smk: AlignKey128bit::default(),
            role: DhSessionRole::Responder,
        },
    })
}
