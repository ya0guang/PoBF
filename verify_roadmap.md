# Verification Roadmap

## Verification of Consistency with the Theoretical PoBF Model - Execution Integrity

Briefly speaking, we have some goals:

* ✅ Memory safety: no `unsafe` code blocks in the CCaaS framework; can have `unsafe` edge functions while passing raw pointers at the edge of enclave and the outside world, which does not harm the security. **Realized via `#![forbid(unsafe_code)]`.** Also creusot will panic if there is any `unsafe` code.
* ✅ Typestate correctness: Currently there are four states in our PoBF implementation.
    We need to show that our Rust implementation is indeed consistent with the abstract model:
  * The control flow starts at the initial state.
  * After every invocation of state-transfer function, the state is indeed transferred, and
  * The old state cannot be used; i.e., we **cannot move backwards**.
  * The final state is reachable.
  A -> B -> C -> D. Need to show a -> b, b -> c, c -> d, then transitivity.

Approach: Only verify functions that deal with type transfer, and that other functions maintain the current type state.

## Verification of Consistency with the Theoretical PoBF Model - No Leakage

Maybe MIRAI?...

Or we can use `PhantomData` and then verify it -> ugly.

## Verification of Consistency with the Theoretical PoBF Model - No Residue

Ensures that the memory / stack is zeroed out, but we may need to integrate the `creusot` into the SGX SDK library because the allocator is defined there. I do not think it is a great choice. Alternatives :

* Extract that specific part into a new Rust source file and verify it.
* State this as a fact. ✅

## Problems of Integrating `creusot` into the crate

1. `creusot` is **intrusive**, which means the we may need to verify the **entire** project (may include external crates) if we
include it, because `creusot` rejects calls to **unverified** functions. A better choice may be extract core functionalities and then verify it.

2. Mismatched toolchain version. Rust-SGX-SDK requires nightly-2022-02-23, but `creusot` cannot compile under this version; nightly-2022-02-11 supports both,
but I am afraid some properties will not hold.

3. <s>(Not sure) `creusot-contracts` conflicts with SGX-SDK... Cannot use `creusot_contracts` as an external crate.</s> It supports `extern_spec` macro which states as fact that the function satisfies the given contracts. See [Prusti-dev](https://viperproject.github.io/prusti-dev/user-guide/verify/spec_ent.html) and [here](https://github.com/xldenis/creusot/blob/adf83838953dbb20d34c6a1f011011c3e9e6994c/creusot/tests/should_succeed/syntax/07_extern_spec.rs#L24).

* ✅ Need to edit configurations for all unsupported Rust language features for creusot.
* ✅ Closure is not supported by creusot, but is supported by prusti.  Closures are only used in `clear_stack`, but this cannot be verified based on MIR, so we just omit them.

```sh
error[creusot]: MIR code used an unsupported Rvalue &raw mut (*_11)
  --> src/ocall.rs:22:39
   |
22 |     let result = unsafe { u_log_ocall(&mut rv as _, string_ptr as _, len as _, cap as _) };
   |                                       ^^^^^^^ -->
```

4. Older version of `creusot` will report missing metadata for extern crate `creusot-contracts`... :()

```sh
extern location for creusot_contracts does not exist: /home/kali/PoBF/bin/play/target/debug/deps/libcreusot_contracts-ca550f1ce5abe243.rmeta
 --> src/main.rs:3:1
  |
3 | extern crate creusot_contracts;
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

5. Newer version of `creusot` is incompatible with the SDK's toolchain.

## Run

? Run `cargo creusot --features sgx, contracts` in `./enclave`.

## Prusti

Usable version is `b74ed28a0d8b946c67fb85f56edbeb81346aabd9` with `nightly-2022-02-11`.

Run

```shell
PRUSTI_NO_VERIFY_DEPS=true [/path/to/cargo-prusti] # Treat local dependencies as external crates so that prusti will not make attemps to verify them.
```

Make configurations so that some code is not compiled during Prusti check.
