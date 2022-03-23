# PoBF Enclave

## Verifictaion

The main part of PoBF is verified towards the Rust compiler and MIRAI. The glue code (in `lib.rs` and `utils.rs`) which handles the input, output and type casting may contain unsafe code and are verified manually.

Since we only need to verify the implementation of PoBF in enclaves, successfully compilation **and** MIRAI executed without complians implies that the enclave is verified to hold PoBF properties.


### Usage

`make` will compile the enclave using Rust compiler, such that security checkes (e.g., type, memory safety) are enforced; `make mirai` runs MIRAI on the project, where potential leakage can be detected with warnnings.

### Violations

Here is a list of potential violations:

- Typestate violation: `vio_typestate`
- Unexpected unsafe code: `vio_unsafe`
- Structure privacy violation: `vio_privacy`

If you want to try to compile code that violates the PoBF rules, you can run`cargo build --features "vio_X"`, where all site that violates the corresponding rule can found by the Rust compiler.
Moreover, if you want to check all the violations, simply run `cargo build --features "violation"`.
