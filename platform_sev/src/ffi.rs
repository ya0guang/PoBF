#[repr(C)]
pub enum EncryptionType {
    None = 0,
}

#[repr(u16)]
pub enum RsaScheme {
    RsaNull = 0x0010, // TPM2_ALG_NULL
    RsaEs = 0x0015,   // TPM2_ALG_RSAES
    RsaOaep = 0x0017, // TPM2_ALG_OAEP
}

#[repr(u16)]
pub enum RsaHashAlg {
    RsaSha1 = 0x0004,   // TPM2_ALG_SHA1
    RsaSha256 = 0x000B, // TPM2_ALG_SHA256
    RsaSha384 = 0x000C, // TPM2_ALG_SHA384
    RsaSha512 = 0x000D, // TPM2_ALG_SHA512
}

extern "C" {
    pub fn get_attestation_report(
        buf: *mut u8,
        len: usize,
        nonce: *const u8,
        nonce_len: usize,
    ) -> i64;

    pub fn encrypt(
        encryption_type: EncryptionType,
        jwt_token: *const u8,
        data: *const u8,
        data_size: u32,
        encrypted_data: *mut *mut u8,
        encrypted_data_size: *mut u32,
        encryption_metadata: *mut *mut u8, // Must be non-null pointer, but this is not used during encryption.
        encryption_metadata_size: *mut u32,
        rsa_wrap_alg_id: RsaScheme,
        rsa_hash_alg_id: RsaHashAlg,
    ) -> i64;

    pub fn decrypt(
        encryption_type: EncryptionType,
        encrypted_data: *const u8,
        encrypted_data_size: u32,
        _: *const u8,
        _: u32,
        decrypted_data: *mut *mut u8,
        decrypted_data_size: *mut u32,
        rsa_wrap_alg_id: RsaScheme,
        rsa_hash_alg_id: RsaHashAlg,
    ) -> i64;

    /// Should be called if remote attestation finishes.
    pub fn uninitialize();
}
