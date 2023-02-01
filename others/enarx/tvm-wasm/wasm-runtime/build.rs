fn main() {
    println!("cargo:rustc-link-lib=static=graph_wasm32");
    println!(
        "cargo:rustc-link-search=native={}",
        format!(
            "{}/{}",
            std::env::var("CARGO_MANIFEST_DIR").unwrap(),
            "../wasm-graph/lib"
        )
    );
}
