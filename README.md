# PoBF-compliant Platform Reference Implementation

## Requirements for Verifier

We need a (static) code analysis tool for Rust.

"Checked box" means that [MIRAI]() has implemented this functionality, 
and so far tested correct.

### Taint Analysis

- [X] Adding tags manually, or treat any arguments as secret
- [ ] Tag propagation: incomplete (e.g., sub/super-component)
- [X] Tag checks at specific positions

Please check the example in next section for more details.

### Formal Verification

- [ ] Verification of precondition
- [ ] Termination check
- [ ] Verification of Rust crate

MIRAI has these functionalities but cannot produce correct results for our code. 
Not sure if it's because that tag propagation is incorrect.

Here is a toy example, with detailed verification conditions commented:

```rs
#![cfg_attr(mirai, allow(incomplete_features), feature(generic_const_exprs))]

extern crate mirai_annotations;

use mirai_annotations::*;

#[cfg(mirai)]
use mirai_annotations::TagPropagationSet;

#[cfg(mirai)]
struct SecretTaintKind<const MASK: TagPropagationSet> {}

#[cfg(mirai)]
const SECRET_TAINT: TagPropagationSet = TAG_PROPAGATION_ALL;

#[cfg(mirai)]
type SecretTaint = SecretTaintKind<SECRET_TAINT>;

#[cfg(not(mirai))]
type SecretTaint = ();

struct A(u32);
struct B(u32);

fn a_to_b(a: A) -> B {
    // using macro to verify the precondition of a function
    precondition!(has_tag!(&a, SecretTaint));
    let b = B(a.0 + 1);
    // and potentially verify some postcondition holds
    postcondition!(has_tag!(&b, SecretTaint));
    b
}

fn b_to_a(b: B) -> A {
    precondition!(has_tag!(&b, SecretTaint));
    let a = A(b.0 + 1);
    a
}

fn main() {
    let a = A(1);
    // we could add tag for a variable
    add_tag!(&a, SecretTaint);
    let b = a_to_b(a);
    // and such tag can be checked existed
    // where sub-components and super-components propagate tag correctly
    verify!(has_tag!(&b, SecretTaint));
    let a = b_to_a(b);
    verify!(has_tag!(&a, SecretTaint));
    // And the verifier should be able to verify that such statement is reachable
    println!("reachable?");
}
```

For more information about how this fails in MIRAI, 
see [this issue](https://github.com/facebookexperimental/MIRAI/issues/1131).

Besides, we hope the whole project can be verified (rather than merely a single Rust file).

### Others

- [ ] Rust toolchain compatibility

Since we cannot use Rust-SGX-SDK with arbitrary toolchains, 
the verifier should at least be compatible with the toolchian of the SDK.

#### Potential Solutions

- Modify MIRAI: most promising, but may require learning a lot of MIRAI's implementation
- Develop our own tool (e.g., SMACK): additional functionalities required
- Use other tools: not sure if viable, especially for Rust

## Problems in the Rust Code

### Unsafe Code

When copying input, or constructing datatypes in the ECALL, 
we need to use unsafe code. Such construction might be wrapped.

Maybe we also need to separate OCALLs from the context 
and wrap them with precondition verifications? 
e.g., the input arguments should not be tainted by secrets.

#### Potential Solutions

- Provide a library to wrap unsafe code
- Transfer types directly across enclave boundry
- **Admit** this problem as a deficit

## TODOs

- Zone Allocator and its verification
- Verify this implementation (with a verifier)
- Formal proof of PoBF constraints

## Goals in the Long Run

- Runtime *Being Forgotten* report
- Trusted & verifiable 3rd-party build
- Meaningful attestation
- Trusted key exchange
- Apply PoBF on Teaclave
- Side-channel mitigations

## Related Documents

- [PoBF whitepaper overleaf link](https://www.overleaf.com/4268188831mdgcyfhmmfsg)
- [PoBF Slides keynote share](https://www.icloud.com/keynote/0da8dyFEr1CrbtnFFXST0UHnQ#PoBF)