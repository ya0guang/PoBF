# Requirements for Verifier

We need a (static) code analysis tool for Rust.

A series of functionality requirements are listed in each subsection, 
and corresponding minimal examples can be found in `./src/[topic].rs`.
After the requirements subsections, there will be a more complex example designed for MIRAI.

"Checked box" means that [MIRAI]() has implemented this functionality, 
and so far tested correct.

## Taint Analysis

- [X] Adding tags manually, or treat any arguments as secret
- [ ] Tag propagation: incomplete (e.g., sub/super-component)
- [X] Tag checks at specific positions

Check `src/taint.rs` for detailed examples.

## Formal Verification

- [ ] Verification of precondition
- [ ] Termination check
- [ ] Verification of Rust crate

Check `src/verify.rs` for detailed examples.

MIRAI has these functionalities but cannot produce correct results for our code. 
Not sure if it's because that tag propagation is incorrect.

## Others

- [ ] Rust toolchain compatibility

Since we cannot use Rust-SGX-SDK with arbitrary toolchains, 
the verifier should at least be compatible with the toolchian of the SDK.

## MIRAI example

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

### Potential Solutions

- Modify MIRAI: most promising, but may require learning a lot of MIRAI's implementation
- Develop our own tool (e.g., SMACK): additional functionalities required
- Use other tools: not sure if viable, especially for Rust
