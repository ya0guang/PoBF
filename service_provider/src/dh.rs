use std::io::*;
use std::net::TcpStream;

use aes::Aes128;
use cmac::{Cmac, Mac};
use ring::agreement::*;
use ring::error::*;

pub type Result<T> = std::result::Result<T, Unspecified>;

/// A magic string that identifies the key.
pub const KDF_MAGIC_STR: &'static str = "enclave_key";
/// A magic number for CMAC.
pub const KDF_CMAC_MAGIC: &'static [u8] = &[0x00, 0x80, 0x00];

/// This function should not be directly called; this is used as a callback.
/// We mimic the steps from the SGX SDK which uses AES CMAC as the HMAC function.
fn key_derive_function(shared_key: &[u8], label: &[u8]) -> Result<Vec<u8>> {
    // Reverse it at first.
    let shared_key_rev = shared_key.iter().copied().rev().collect::<Vec<u8>>();
    // Be aware of the endianness.
    println!("[+] The shared key is {:?}", shared_key_rev);

    if label.is_empty() {
        println!("[-] The label for KDF is empty!");
        return Err(Unspecified);
    }

    // Use an empty key to get the hashed derive key from the shared session key.
    let key = [0u8; 16];
    let mut mac = Cmac::<Aes128>::new_from_slice(&key).unwrap();
    mac.update(shared_key_rev.as_slice());
    // Used for a second Cmac.
    let mut derive_key = mac.finalize().into_bytes();

    let derivation_len = label.len().checked_add(4).ok_or(Unspecified)?;
    let mut derivation = vec![0u8; label.len() + 4];
    derivation[0] = 0x01;
    derivation[1..derivation_len - 3].copy_from_slice(label);
    derivation[derivation_len - 3..].copy_from_slice(KDF_CMAC_MAGIC);

    mac = Cmac::<Aes128>::new_from_slice(&derive_key).unwrap();
    mac.update(derivation.as_slice());

    Ok(mac.finalize().into_bytes().to_vec())
}

pub fn compute_shared_key(
    my_private_key: EphemeralPrivateKey,
    peer_pub_key: &UnparsedPublicKey<Vec<u8>>,
    label: &[u8],
) -> Result<Vec<u8>> {
    // Be aware of the endianness...
    // ring and SGX SDK use different ones.
    agree_ephemeral(
        my_private_key,
        peer_pub_key,
        ring::error::Unspecified,
        |key_materials| key_derive_function(key_materials, label),
    )
}

pub fn handle_enclave_pubkey(
    reader: &mut BufReader<TcpStream>,
) -> Result<UnparsedPublicKey<Vec<u8>>> {
    let mut key_buf = vec![0u8; 65];
    reader.read_exact(&mut key_buf).unwrap();
    key_buf.truncate(64);

    // Convert the endianness.
    key_buf[..32].reverse();
    key_buf[32..].reverse();
    // Then insert "0x04" into the front.
    key_buf.insert(0, 0x04);

    // Convert to UnparsedPublicKey.
    Ok(UnparsedPublicKey::new(&ECDH_P256, key_buf))
}

pub fn open_session() -> Result<(EphemeralPrivateKey, PublicKey)> {
    let rng = ring::rand::SystemRandom::new();
    let private_key = EphemeralPrivateKey::generate(&ECDH_P256, &rng)
        .map_err(|_| {
            return Unspecified;
        })
        .unwrap();
    let public_key = private_key
        .compute_public_key()
        .map_err(|_| {
            return Unspecified;
        })
        .unwrap();

    Ok((private_key, public_key))
}
