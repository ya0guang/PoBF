# Requirements for Verifier

We need a (static) code analysis tool for Rust.

A series of functionality requirements are listed in each subsection, 
and corresponding minimal examples can be found in `./src/[topic].rs`.
After the requirements subsections, there will be a more complex example.


## Taint Analysis

- [ ] Adding tags manually, or treat any arguments as secret
- [ ] Tag propagation: incomplete (e.g., sub/super-component)
- [ ] Tag removal
- [ ] Tag checks at specific positions

Check `src/taint.rs` for detailed examples.

## Formal Verification

- [ ] Verification of precondition
- [ ] Termination check
- [ ] Verification of Rust crate

Check `src/verify.rs` for detailed examples.

## Others

- [ ] Verify towards a crate (rather than a single rust file)
- [ ] Rust toolchain compatibility

Since we cannot use Rust-SGX-SDK with arbitrary toolchains, 
the verifier should at least be compatible with the toolchian of the SDK.

## Complex Example

Here is a toy example, with detailed verification conditions commented,
and verifications annotated as macros:

```rs
struct A(u32);
struct B(u32);

fn a_to_b(a: A) -> B {
    // to verify the precondition of a function
    precondition!(has_tag!(&a, SecretTaint));
    let b = B(a.0 + 1);
    // and potentially verify that this postcondition holds
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
    // And the verifier should be able to verify that such statement can be reached
    println!("reachable?");
}
```
