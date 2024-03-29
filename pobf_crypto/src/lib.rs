use std::io::*;
use std::net::TcpStream;
use std::time;

use aes_gcm::{
    aead::{Aead, KeyInit},
    Aes128Gcm, Nonce,
};

#[cfg(feature = "sgx")]
use aes::Aes128;
#[cfg(feature = "sgx")]
use cmac::{Cmac, Mac};

use log::{debug, error, info};
use pem::*;
use ring::agreement::*;
use ring::error::*;
use ring::signature;

pub type PobfCryptoResult<T> = std::result::Result<T, Unspecified>;

#[cfg(all(feature = "sgx", feature = "sev"))]
compile_error!("Cannot enable both sgx and sev!");

/// A magic string that identifies the key.
pub const KDF_MAGIC_STR: &'static str = "PoBF/enclave&session-key";
/// A magic number for CMAC.
pub const KDF_CMAC_MAGIC: &'static [u8] = &[0x00, 0x80, 0x00];
/// The ECDSA private key for the SP. Can be generated by OpenSSL.
/// This pem file must be encoded using PKCS#8 V1 format. Ring will
/// reject it otherwise.
pub const ECC_KEY: &'static [u8] = include_bytes!("../../pobf_keychain/key.pem");
/// The ECDSA public key for the SP.
#[allow(unused)]
pub const ECC_CERT: &'static [u8] = include_bytes!("../../pobf_keychain/cert.pem");

/// The P256 key length.
pub const P256_PUBKEY_LEN: usize = 0x40;
/// The P256 public key length for each coordinate.
pub const P256_PUBKEY_COORDINATE_LEN: usize = 0x20;
/// A header for public key coordinate.
pub const P256_PUBKEY_HEADER: u8 = 0x04;
/// The EC session key length.
pub const ECC_SESSION_KEY_LEN: usize = 0x10;

#[derive(Debug)]
pub struct KeyPair {
    /// Only used once.
    /// Computation on the private key will CONSUME it, leaving `None` at the place.
    pub prv_k: Option<EphemeralPrivateKey>,
    pub pub_k: PublicKey,
    pub signature: Vec<u8>,
    pub session_key: Vec<u8>,
    pub timestamp: u64,
}

impl KeyPair {
    pub fn new(keypair: (EphemeralPrivateKey, PublicKey), signature: Vec<u8>) -> Self {
        Self {
            prv_k: Some(keypair.0),
            pub_k: keypair.1,
            signature,
            session_key: Vec::new(),
            timestamp: 0u64,
        }
    }

    pub fn compute_shared_key(
        &mut self,
        peer_pub_key: &UnparsedPublicKey<Vec<u8>>,
        label: &[u8],
    ) -> PobfCryptoResult<()> {
        self.session_key = agree_ephemeral(
            self.prv_k.take().unwrap(),
            peer_pub_key,
            ring::error::Unspecified,
            |key_materials| key_derive_function(key_materials, label),
        )
        .map_err(|e| {
            error!("[-] Failed to compute the session key. {:?}", e);
            return Unspecified;
        })
        .unwrap();

        #[cfg(feature = "sev")]
        // Truncate the session key.
        self.session_key.truncate(0x10);

        // Set the current timestamp.
        self.timestamp = time::SystemTime::now()
            .duration_since(time::UNIX_EPOCH)
            .map_err(|e| {
                error!("[-] Failed to get the time. {:?}", e);
                return Unspecified;
            })
            .unwrap()
            .as_secs();

        debug!("[+] The session key sampled as {:?}", self.session_key);

        Ok(())
    }

    pub fn encrypt_with_smk(&self, input: &[u8]) -> PobfCryptoResult<Vec<u8>> {
        let aesctx = Aes128Gcm::new_from_slice(&self.session_key)
            .map_err(|e| {
                error!("[-] Failed to create AES context due to {:?}", e);
                return Unspecified;
            })
            .unwrap();
        let nonce = Nonce::from_slice(&[0u8; 12]);

        match aesctx.encrypt(&nonce, input) {
            Ok(ciphertext) => Ok(ciphertext),
            Err(_) => {
                error!("[-] Failed to encrypt the data!");
                Err(Unspecified)
            }
        }
    }

    pub fn decrypt_with_smk(&self, input: &[u8]) -> PobfCryptoResult<Vec<u8>> {
        let aesctx = Aes128Gcm::new_from_slice(&self.session_key)
            .map_err(|e| {
                error!("[-] Failed to create AES context due to {:?}", e);
                return Unspecified;
            })
            .unwrap();
        let nonce = Nonce::from_slice(&[0u8; 12]);

        match aesctx.decrypt(&nonce, input) {
            Ok(plaintext) => Ok(plaintext),
            Err(_) => {
                error!("[-] Failed to decrypt the data!");
                Err(Unspecified)
            }
        }
    }
}

#[cfg(feature = "sev")]
fn key_derive_function(shared_key: &[u8], _: &[u8]) -> PobfCryptoResult<Vec<u8>> {
    Ok(shared_key.to_vec())
}

#[cfg(feature = "sgx")]
/// This function should not be directly called; this is used as a callback.
/// We mimic the steps from the SGX SDK which uses AES CMAC as the HMAC function.
fn key_derive_function(shared_key: &[u8], label: &[u8]) -> PobfCryptoResult<Vec<u8>> {
    // Reverse it at first.
    let shared_key_rev = shared_key.iter().copied().rev().collect::<Vec<u8>>();
    // Be aware of the endianness.
    debug!("[+] The shared key is {:?}", shared_key_rev);

    if label.is_empty() {
        error!("[-] The label for KDF is empty!");
        return Err(Unspecified);
    }

    // Use an empty key to get the hashed derive key from the shared session key.
    let key = [0u8; ECC_SESSION_KEY_LEN];
    let mut mac = <Cmac<Aes128> as Mac>::new_from_slice(&key).unwrap();
    mac.update(shared_key_rev.as_slice());
    // Used for a second Cmac.
    let derive_key = mac.finalize().into_bytes();

    let derivation_len = label.len().checked_add(4).ok_or(Unspecified)?;
    let mut derivation = vec![0u8; label.len() + 4];
    derivation[0] = 0x01;
    derivation[1..derivation_len - 3].copy_from_slice(label);
    derivation[derivation_len - 3..].copy_from_slice(KDF_CMAC_MAGIC);

    mac = <Cmac<Aes128> as Mac>::new_from_slice(&derive_key).unwrap();
    mac.update(derivation.as_slice());

    Ok(mac.finalize().into_bytes().to_vec())
}

#[cfg(feature = "sgx")]
pub fn handle_enclave_pubkey(
    reader: &mut BufReader<TcpStream>,
) -> PobfCryptoResult<UnparsedPublicKey<Vec<u8>>> {
    let mut key_buf = vec![0u8; P256_PUBKEY_LEN + 1];
    reader.read_exact(&mut key_buf).unwrap();
    key_buf.truncate(P256_PUBKEY_LEN);

    // Convert the endianness.
    key_buf[..P256_PUBKEY_COORDINATE_LEN].reverse();
    key_buf[P256_PUBKEY_COORDINATE_LEN..].reverse();
    // Then insert "0x04" into the front.
    key_buf.insert(0, P256_PUBKEY_HEADER);

    // Convert to UnparsedPublicKey.
    Ok(UnparsedPublicKey::new(&ECDH_P256, key_buf))
}

#[cfg(feature = "sev")]
pub fn handle_sev_pubkey(
    reader: &mut BufReader<TcpStream>,
) -> PobfCryptoResult<UnparsedPublicKey<Vec<u8>>> {
    let mut key_buf = vec![0u8; 0x20];
    reader.read_exact(&mut key_buf).unwrap();
    Ok(UnparsedPublicKey::new(&X25519, key_buf))
}

pub fn open_session() -> PobfCryptoResult<(EphemeralPrivateKey, PublicKey)> {
    let rng = ring::rand::SystemRandom::new();
    #[cfg(feature = "sgx")]
    let private_key = EphemeralPrivateKey::generate(&ECDH_P256, &rng)
        .map_err(|_| {
            error!("[-] Cannot generate ephemeral key pair.");
            return Unspecified;
        })
        .unwrap();
    #[cfg(feature = "sev")]
    let private_key = EphemeralPrivateKey::generate(&X25519, &rng)
        .map_err(|_| {
            error!("[-] Cannot generate ephemeral key pair.");
            return Unspecified;
        })
        .unwrap();

    let public_key = private_key
        .compute_public_key()
        .map_err(|_| {
            error!("[-] Cannot compute public key from private key on the given P256 curve.");
            return Unspecified;
        })
        .unwrap();

    Ok((private_key, public_key))
}

pub fn sign_with_ecdsa(message: &[u8]) -> PobfCryptoResult<Vec<u8>> {
    let parsed_pem = parse(ECC_KEY).unwrap();

    let ecdsa_keypair = signature::EcdsaKeyPair::from_pkcs8(
        &signature::ECDSA_P256_SHA256_ASN1_SIGNING,
        parsed_pem.contents(),
    )
    .map_err(|e| {
        error!("[-] Failed to construct ECDSA key pair! {:?}", e);
        return Unspecified;
    })
    .unwrap();

    // Sign this message.
    let signature = ecdsa_keypair
        .sign(&ring::rand::SystemRandom::new(), message)
        .map_err(|_| {
            error!("[-] Signing failed.");
            return Unspecified;
        })
        .unwrap();

    Ok(signature.as_ref().to_vec())
}

pub fn init_keypair() -> PobfCryptoResult<KeyPair> {
    // Generate key pair.
    info!("[+] Sampling EC key pair.");
    let keypair = open_session()?;
    info!("[+] Succeeded.");
    debug!("[+] Key pair: {:?} and {:?}", keypair.0, keypair.1);

    // Sign the public key.
    let signature = sign_with_ecdsa(keypair.1.as_ref())?;
    debug!("[+] Signature is {:?}", signature);

    Ok(KeyPair::new(keypair, signature))
}
