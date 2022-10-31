use std::env;

fn main() {
    println!("cargo:rerun-if-env-changed=SGX_MODE");
    println!("cargo:rerun-if-changed=build.rs");

    let sdk_dir = env::var("SGX_SDK").unwrap_or_else(|_| "/opt/intel/sgxsdk".to_string());

    println!("cargo:rustc-link-search=native={}/lib64", sdk_dir);

    // You may need to execute
    // sudo ln -s /usr/lib/x86_64-linux-gnu/libsgx_dcap_quoteverify.so.1 /usr/lib/x86_64-linux-gnu/libsgx_dcap_quoteverify.so
    println!("cargo:rustc-link-lib=dylib=sgx_dcap_quoteverify");
    println!("cargo:rustc-link-lib=dylib=sgx_dcap_ql");
}
