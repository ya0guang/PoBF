use std::env;

fn main() {
    println!("cargo:rerun-if-env-changed=SGX_MODE");
    println!("cargo:rerun-if-changed=build.rs");

    let sdk_dir = env::var("SGX_SDK").unwrap_or_else(|_| "/opt/intel/sgxsdk".to_string());
    let mode = env::var("SGX_MODE").unwrap_or_else(|_| "HW".to_string());

    println!("cargo:rustc-link-search=native=./lib");
    println!("cargo:rustc-link-lib=static=enclave_u");

    println!("cargo:rustc-link-search=native={}/lib64", sdk_dir);
    // Link against TVL library.
    // println!("cargo:rustc-link-lib=static=sgx_dcap_tvl");
    // You may need to execute
    // sudo ln -s /usr/lib/x86_64-linux-gnu/libsgx_dcap_quoteverify.so.1 /usr/lib/x86_64-linux-gnu/libsgx_dcap_quoteverify.so
    println!("cargo:rustc-link-lib=dylib=sgx_dcap_quoteverify");
    println!("cargo:rustc-link-lib=dylib=sgx_dcap_ql");

    match mode.as_str() {
        "SW" | "SIM" => {
            println!("cargo:rustc-link-lib=dylib=sgx_urts_sim")
        }
        "HW" | "HYPER" => {
            println!("cargo:rustc-link-lib=dylib=sgx_urts");
        }
        _ => {
            println!("cargo:rustc-link-lib=dylib=sgx_urts")
        }
    }
}
