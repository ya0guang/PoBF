extern crate sgx_types;

mod bogus;
mod pobf;
mod types;
mod utils;
mod ocall;

use mirai_annotations::*;
use bogus::SgxSealedData;
use pobf::*;
use sgx_types::*;
use std::slice;
use types::*;
use utils::*;
use ocall::*;

#[no_mangle]
pub extern "C" fn sample_task(sealed_log: *mut u8, sealed_log_size: u32) -> sgx_status_t {
    assert!(sealed_log_size == LOG_BUFFER_SIZE as u32);

    // mirai doesn't complian???!
    ocall!(log, "1023", "1024");

    safe_log_str("1023", "1024");

    safe_log_int(1023, 1024);

    safe_log_str(&sealed_log_size.to_string(), "1024");

    let sealed_buffer = unsafe { slice::from_raw_parts_mut(sealed_log, LOG_BUFFER_SIZE) };

    let sealed_data = SealedData::from_ref(sealed_buffer);
    let sealed_output = pobf_ref_implementation(sealed_data);

    sealed_buffer.copy_from_slice(sealed_output.inner.as_ref());

    sgx_status_t::SGX_SUCCESS
}

#[no_mangle]
pub extern "C" fn create_sealeddata_for_fixed(
    sealed_log: *mut u8,
    sealed_log_size: u32,
) -> sgx_status_t {
    let data = [42u8; 16];

    // commented to make the result deterministic
    // let mut rand = match StdRng::new() {
    //     Ok(rng) => rng,
    //     Err(_) => {
    //         return sgx_status_t::SGX_ERROR_UNEXPECTED;
    //     }
    // };
    // rand.fill_bytes(&mut data);

    let aad: [u8; 0] = [0_u8; 0];
    let result = SgxSealedData::<[u8; 16]>::seal_data(&aad, &data);
    let sealed_data = match result {
        Ok(x) => x,
        Err(ret) => {
            return ret;
        }
    };

    let opt = to_sealed_log_for_fixed(&sealed_data, sealed_log, sealed_log_size);
    if opt.is_none() {
        return sgx_status_t::SGX_ERROR_INVALID_PARAMETER;
    }

    println!("{:?}", data);

    sgx_status_t::SGX_SUCCESS
}

#[no_mangle]
pub extern "C" fn verify_sealeddata_for_fixed(
    sealed_log: *mut u8,
    sealed_log_size: u32,
) -> sgx_status_t {
    let opt = from_sealed_log_for_fixed::<[u8; 16]>(sealed_log, sealed_log_size);
    let sealed_data = match opt {
        Some(x) => x,
        None => {
            return sgx_status_t::SGX_ERROR_INVALID_PARAMETER;
        }
    };

    let result = sealed_data.unseal_data();
    let unsealed_data = match result {
        Ok(x) => x,
        Err(ret) => {
            return ret;
        }
    };

    let data = unsealed_data.get_decrypt_txt();

    println!("{:?}", data);

    sgx_status_t::SGX_SUCCESS
}
