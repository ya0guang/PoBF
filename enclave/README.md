# PoBF Enclave

## Enclave Structure

- `lib.rs`: ECALL interfaces (contains unsafe code)
- `utils.rs`: utility functions (contains unsafe code)
- `pobf.rs`: PoBF core implementation
- `bogus.rs`: the bogus implementations designed for MIRAI verification (contains unsafe bogus implementations)
- `ocall.rs`: OCALL interfaces macros wrapping static verifications
- `types/mod.rs`: typestate implementation
- `types/vecaes.rs`: encrypted data structure wrapping a vector

## Verifictaion

The main part of PoBF is verified towards the Rust compiler and MIRAI. The glue code (in `lib.rs` and `utils.rs`) which handles the input, output and type casting may contain unsafe code and are verified manually.

Since we only need to verify the implementation of PoBF in enclaves, successfully compilation **and** MIRAI executed without complians implies that the enclave is verified to hold PoBF properties.


### Usage

Simply run `../verifier/pobf.py` in `enclave/` directory.

## Violations

Here is a list of potential violations with explainations why these violations can threat PoBF guarantees.

If you want to try to compile code that violates the PoBF rules, you can run`cargo build --features "vio_X"`, where all site that violates the corresponding rule can found by the Rust compiler.
Moreover, if you want to check all the violations, simply run `cargo build --features "violation"`.

### `vio_typestate`

This implies the permitted methods and state transitions of `ProtectedAsset` are violated.
Only limited set of operations in each state are permitted. For example,
developers cannot take out the private data when the data is not in an `Ecrypted Output` state,
otherwise the `Decrypted` data might be stolen, and further such secret can either be leaked from the enclave,
or remain uncleared in the enclave.

### `vio_unsafe`

This implies the enclave contains unsafe code.
Althogh unsafe code exists in `std`, Rust developers inspect those code carefully and tried their best to make them safe.
However, PoBF dont't expect unsafe code in its core components (e.g., the typestate and computation tasks).
This is because that unsafe code has the ability to steal or leak privacy,
such as reading raw (`Decrypted`) data and write outside the enclave.

### `vio_private`

This implies the code tries to access a private method or field of a strcut or trait.
Accessing the inner fields (e.g., `input_key`) of any protected data structure is not allowed,
thus exclude the possibility of direct access to sensitive data.
On the other hand, critical methods (e.g., `decrypt`) are also private,
since they should not be called directly be developers under PoBF framework.

### `vio_ocall`

This implies the enclave code OCALL(s) with non-constant parameter(s).
One of the explicit leakage through the enclave is embedding the secret into an OCALL parameter.
Therefore we forbid use of OCALL(s) with non-constant parameter, i.e.,
the value of a parameter cannot be determined in compilation.
Although this restriction may be too strong for a benign enclave,
PoBF ensures that all verified enclave cannot leak secret through OCALL.
