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
MIRAI can be used when the secret tag is propagating to children, but it cannot verify if a secret tag is propagated from child to parent. E.g., if `s[0]` in `s: Vec<i32>` is secret tainted, then MIRAI won't complain about unsatisfied precondition `has_tag!(&s, SecretTaint)`.

```rust
    let mut v = Vec::new();
    v.push(1);
    add_tag!(&v[0], SecretTaint);
    // ~ Possible false verification?
    verify!(has_tag!(&v[0], SecretTaint));
```

I used a tag...

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

5. Newer version of `creusot` is incompatible with the SDK's toolchain; also it cannot verify function pointers (will yield impossible preconditions.)

## Run

? Run `cargo creusot --features sgx, contracts` in `./enclave`.

## Prusti

Usable version is `b74ed28a0d8b946c67fb85f56edbeb81346aabd9` with `nightly-2022-02-11`.

Run

```shell
PRUSTI_NO_VERIFY_DEPS=true [/path/to/cargo-prusti]
# Treat local dependencies as external crates so that prusti will not make attemps to verify them.
# Also remember to enable features.
```

Prusti cannot verify function pointers, and if we mark all functions involving function pointers, Prusti will panic...?
Maybe function pointers are runtime-object so that it cannot analyze it at compiler time; but our project relied heavily on that thing... **Current Rust verifier only supports relatively a small subset of Rust traits.**

```sh
thread 'rustc' panicked at 'not implemented: ty=Closure(DefId(0:275 ~ pobfref[c8aa]::pobf::pobf_private_computing::{closure#0}), [i32, extern "rust-call" fn(()) -> core::result::Result<types::vecaes::VecAESData, sgx_types::error::SgxStatus>, (types::vecaes::VecAESData, types::vecaes::AES128Key, types::vecaes::AES128Key, &fn(types::vecaes::VecAESData) -> types::vecaes::VecAESData {pobf::private_vec_compute::<types::vecaes::VecAESData>})])', analysis/src/mir_utils.rs:141:17
```

Make configurations so that some code is not compiled during Prusti check.

**CURRENT VERSION (02-11) OF PRUSTI WILL PANIC ON GENERIC TYPES.**

### Some very tricky problems

* Prusti will easily panic when there are nested generic types.

```rust
#[pure]
#[ensures(...)]
pub fn some_generic<D, K>(
    input: &ProtectedAssets<Encrypted, Output, D, K>)
  -> bool 
where
  D: EncDec<K>,
  K: Default
{
  ...
}
```
The above example will make Prusti die.

* Prusti cannot properly work with `Result`, so we avoid using it, and because our security scheme stipulates that the program aborts when error occurs, so we do not handle errors explicitly. We just let the program crash; so the return values are the inner values. Otherwise we need to verify the inner value via

```rust
#[pure]
#[ensures((&input).as_ref().unwrap().call_methods() == false)]
pub fn some_func<T>(input: &SgxResult<T>) -> bool {
  ...
}

// Along with external specifications.
#[extern_spec]
impl<T> SgxResult<T> {
  #[pure]
  #[requires((&self).is_ok())]
  fn unwrap(self) -> T;

  #[pure]
  #[ensures(result == match self {
    Ok(_) => true,
    Err(_) => false,
  })]
  fn is_ok(&self) -> bool;

  #[pure]
  // This will cause problems.
  fn as_ref(&self) -> Result<&T, &SgxStatus>;
}
```

The above code cannot compile due to `parameter is not Copy`; but the reason for that is mainly because Prusti cannot handle with deeply-nested generic types, and the ownership cannot be properly figured out, either.

A trick would be to define specific version for generic types, but sometimes it won't work, either :( Also, I do not think resort to `creusot` is a good idea because the it supports fewer traits of Rust language, plus its verification grammar is verbose, which lacks documentation, making the verification even hard to get around.

Maybe the latest build of Prusti can solve the problem, but we need to wait for the upcoming upgrade of Teaclave-SGX-SDK. I hope they will update to the newest toolchain.
