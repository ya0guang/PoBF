use std::env;

fn main() {
    let dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-link-search=native={}/outlib", dir);
    println!("cargo:rustc-link-lib=static=model_entry");
}
