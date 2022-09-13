# Verification of Consistency with the Theoretical PoBF Model - Execution Integrity

Briefly speaking, we have some goals:

* Memory safety: no `unsafe` code blocks in the CCaaS framework; can have `unsafe` edge functions while passing raw pointers
    at the edge of enclave and the outside world, which does not harm the security. **Realized via `#![forbid(unsafe_code)].**
* Typestate correctness: Currently there are four states in our PoBF implementation.
    We need to show that our Rust implementation is indeed consistent with the abstract model:
  * The control flow starts at the initial state.
  * After every invocation of state-transfer function, the state is indeed transferred, and
  * The old state cannot be used; i.e., we **cannot move backwards**.
  * The final state is reachable.
  A -> B -> C -> D. Need to show a -> b, b -> c, c -> d, then transitivity.

# Verification of Consistency with the Theoretical PoBF Model - No Leakage

Maybe MIRAI?...

Or we can use `PhantomData` and then verify it.

# Verification of Consistency with the Theoretical PoBF Model - No Residue

Ensures that the memory / stack is zeroed out, but we may need to integrate the `creusot` into the SGX SDK library because the allocator is defined there. I do not think it is a great choice. Alternatives :

* Extract that specific part into a new Rust source file and verify it.
* State this as a fact. ✅

# Problems of Integrating `creusot` into the crate

1. `creusot` is **intrusive**, which means the we may need to verify the **entire** project (may include external crates) if we
include it, because `creusot` rejects calls to **unverified** functions. A better choice may be extract core functionalities and then verify it.

2. Mismatched toolchain version. Rust-SGX-SDK requires nightly-2022-02-23, but `creusot` cannot compile under this version; nightly-2022-02-11 supports both,
but I am afraid some properties will not hold.

3. (Not sure) `creusot-contracts` conflicts with SGX-SDK... Cannot use `creusot_contracts` as an external crate.

* Need to edit configurations for all unsupported Rust language features for creusot.

* Closure is not supported by creusot, but is supported by prusti.

```sh
error[creusot]: MIR code used an unsupported Rvalue &raw mut (*_11)
  --> src/ocall.rs:22:39
   |
22 |     let result = unsafe { u_log_ocall(&mut rv as _, string_ptr as _, len as _, cap as _) };
   |                                       ^^^^^^^ -->
```

## Verify

Run `cargo creusot --features sgx, contracts` in `enclave`.
