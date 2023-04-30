fn main() {
    let lib_path = format!(
        "{}/attestation_lib",
        std::env::var("CARGO_MANIFEST_DIR").unwrap_or_default()
    );
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-link-search=native={lib_path}",);
    println!("cargo:rustc-link-lib=dylib=sev_attestation");
    println!("cargo:rustc-link-lib=dylib=azguestattestation");
    println!("cargo:rustc-env=LD_LIBRARY_PATH={lib_path}");
}
