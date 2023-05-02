//! A simplified version of the ECDH key agreement protocol for AMD-SEV.

use ring::{
    agreement::{EphemeralPrivateKey, PublicKey, X25519},
    rand,
};

pub fn get_keypair() -> (EphemeralPrivateKey, PublicKey) {
    let rng = rand::SystemRandom::new();
    let prv_key = EphemeralPrivateKey::generate(&X25519, &rng).unwrap();
    let pub_key = prv_key.compute_public_key().unwrap();

    (prv_key, pub_key)
}
