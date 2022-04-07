# PoBF Enclave

## Enclave Structure

- `lib.rs`: ECALL interfaces (contains unsafe code)
- `utils.rs`: utility functions
- `pobf.rs`: PoBF core implementation
- `bogus.rs`: the bogus implementations designed for MIRAI verification (contains unsafe bogus implementations)
- `ocall.rs`: OCALL interfaces macros wrapping static verifications (contains unsafe code)
- `userfunc.rs`: task functions provided by the user
- `types/mod.rs`: typestate implementation
- `types/vecaes.rs`: encrypted data structure wrapping a vector

## Verifictaion

The main part of PoBF is verified towards the Rust compiler and MIRAI. The glue code (in `lib.rs` and `utils.rs`) which handles the input, output and type casting may contain unsafe code and are verified manually.

Since we only need to verify the implementation of PoBF in enclaves, successfully compilation **and** MIRAI executed without complians implies that the enclave is verified to hold PoBF properties.


### Usage

Simply run `./demo-verify.sh` in `enclave/` directory.

## Violations

Here is a list of potential violations with explainations why these violations can threat PoBF guarantees.
There is also a list of attacke vectors captured in each category.

If you want to try to compile code that violates the PoBF rules, you can run`cargo build --features "vio_X"`, where all site that violates the corresponding rule can found by the Rust compiler.
Moreover, if you want to check all the violations, simply run `cargo build --features "violation"`.

### `vio_typestate`

This implies the permitted methods and state transitions of `ProtectedAsset` are violated.
Only limited set of operations in each state are permitted. For example,
developers cannot take out the private data when the data is not in an `Ecrypted Output` state,
otherwise the `Decrypted` data might be stolen, and further such secret can either be leaked from the enclave,
or remain uncleared in the enclave.

- State Transition Violation

Only limited set of operations can be performed on protected data in each state. 
For example, developers cannot `decrypt` the data when the data is already in `decrypted` state.
This violation may lead to unexpected decryption, further resulting in secret leak.

- Deferred Secret Destruction

The privacy is ruined right after the encryption/decrption operations.
If the attcker wants to defer the destruction of used secrets, the compiler will reject such operation
This violation may result in residue of the privacy.

#### Examples

- disallowed control flow/typestate transition (`disallowed_trans`)
- potential residue caused by copy (`reside_copy`)

### `vio_unsafe`

This implies the enclave contains unsafe code.
Althogh unsafe code exists in `std`, Rust developers inspect those code carefully and tried their best to make them safe.
However, PoBF dont't expect unsafe code in its core components (e.g., the typestate and computation tasks).
This is because that unsafe code has the ability to steal or leak privacy,
such as reading raw (`Decrypted`) data and write outside the enclave.

- Raw Pointer Dereference

Unsafe code can dereference raw pointers, which means that an attacker may steal the secrets embedded in
protected data structures, or even write them out to the insecure world given a pointer to the normal world.
An attacker can leverage unsafe Rust to nearly leak secret out.

- Other Unsafe Operations

Unsafe blocks could also easily break the secruity rules encoforced by Rust
x(e.g., borrow checker and lifetime checker).
Attacker can thus introduce memory errors to the code, leading to potential secret leak or residue.

#### Examples

- raw data reading (`raw_read`)
- raw data writing to teh insecure world (`raw_write`)

### `vio_private`

This implies the code tries to access a private method or field of a strcut or trait.
Accessing the inner fields (e.g., `input_key`) of any protected data structure is not allowed,
thus exclude the possibility of direct access to sensitive data.
On the other hand, critical methods (e.g., `decrypt`) are also private,
since they should not be called directly be developers under PoBF framework.

- Secret Data Field Access

The keys and decrypted data are private fields of a data structure, and accessing them can be danguerous
since the raw key and data might then be stolen and further lead to secret leak or residue.

- Private Method Invokation

Security-critical methods (e.g., `decrypt()`) are private, and their invokations are also protected.
Calling these methods directly may lead to unexpected results (e.g., unauthorized decryption).

#### Examples

- calling `decrypt()` directly on encrypted data (`direct_decrypt`)
- accessing the inner part of the key (`access_inner`)
- accessing the key nested in the protected data structure (`access_key`)

### `vio_ocall`

This implies the enclave code OCALL(s) with non-constant parameter(s).
One of the explicit leakage through the enclave is embedding the secret into an OCALL parameter.
Therefore we forbid use of OCALL(s) with non-constant parameter, i.e.,
the value of a parameter cannot be determined in compilation.
Although this restriction may be too strong for a benign enclave,
PoBF ensures that all verified enclave cannot leak secret through OCALL.

- Leak through OCALL

The arguments in OCALLs can contain sensitive data and the enclave can make OCALLs to the normal world with secrets in the arguments.
This may potetially leak secrets through OCALL.

#### Examples

- leak through network traffic (`leak_net`)
- file I/O (`leak_file`)
- logging (`leak_log`)
