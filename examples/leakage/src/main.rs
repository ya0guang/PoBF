#[macro_use]
extern crate mirai_annotations;

// Include basic SGX definitions.
extern crate sgx_urts;
extern crate sgx_types;

use std::path::Path;

#[cfg(mirai)]
use mirai_annotations::{TagPropagation, TagPropagationSet};

use sgx_types::error::{SgxResult, SgxStatus};
use sgx_types::types::EnclaveId;
use sgx_urts::enclave::SgxEnclave;

struct KeyType<'a> (&'a[u8], bool);

#[cfg(mirai)]
struct SecretTaintKind<const MASK: TagPropagationSet> {}

#[cfg(mirai)]
const SECRET_TAINT_MASK: u128 = tag_propagation_set!(TagPropagation::Equals, TagPropagation::Ne);

#[cfg(mirai)]
type SecretTaint = SecretTaintKind<SECRET_TAINT_MASK>;

#[cfg(not(mirai))]
type SecretTaint = (); // Ensures code compiles in non-MIRAI builds
#[cfg(not(mirai))]
fn do_compute(secret: &[u8], key: &KeyType, enclave_path: &str) -> SgxResult<EnclaveId> {
	// MIRAI Precondition check. Should be used along with nightly Rust.
	precondition!(does_not_have_tag!(secret, SecretTaint));
	precondition!(does_not_have_tag!(key, SecretTaint));

	if !key.1 || secret.len() <= 0 {
		return Err(SgxStatus::InvalidParameter);
	}

	println!("[+] Reading secret {:?} and key {:?}", secret, key.0);


	if !Path::new(enclave_path).exists() {
		return Err(SgxStatus::EnclaveFileAccess);
	}

	let enclave = match SgxEnclave::create(enclave_path, false) {
		Ok(ans) => {
			println!("[+] Rust Enclave created successfully! EPID = {}", ans.eid());
			ans
		}
		Err(e) => {
			println("[-] Failed to create the enclave due to {}", e.as_str());
			return Err(e);
		}
	};

	add_tag!(&enclave, SecretTaint);

	Ok(enclave.eid())
}

fn main() {
	println!("Hello, world!");

	let mut v = vec![1, 2, 3];
  // Test unsafe code.
  let ptr = v.as_mut_ptr();

	let _ = unsafe {
		Vec::from_raw_parts(ptr, 3, 3)
	};
}