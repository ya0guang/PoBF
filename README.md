# PoBF-compliant Platform Reference Implementation

## Requirements for Verifier

We need a (static) code analysis tool for Rust.

"Checked" means that [MIRAI]() has implemented this functionality, and so for tested correct.

### Taint Analysis

- [X] Adding tags manually
- [ ] Tag propagation: incomplete (e.g., sub/super-component)
- [X] Tag checks at specific positions

### Formal Verification

- [ ] Verification of precondition
- [ ] Termination check

MIRAI cannot produce correct results. Not sure if it's because that tag propagation is incorrect.

### Others

- [ ] Rust toolchain compatibility

#### Potential Solutions

- Modify MIRAI: most promising, but may require learning a lot of MIRAI's implementation
- Develop our own tool (e.g., SMACK): additional functionalities required
- Use other tools: not sure if viable, especially for Rust

## Problems in the Rust Code

### Unsafe Code

When copying input, or constructing datatypes in the ECALL, we need to use unsafe code. Also this cannot be avoided when constructing the output buffer.

Maybe we also need to seperate OCALLs?

#### Potential Solutions

- Provide a library to wrap unsafe code
- Transfer types directly across enclave boundry
- Admit this problem as a deficit

## TODOs

- Zone Allocator and its verification
- Verify this implementation (with a verifier)
- Formal proof of PoBF constraints

### Goals in the Long Run

- *Being Forgotten* report
- Trusted & verifiable build
- Meaningful attestation
- Key management
- Apply PoBF on Teaclave
- Side-channel mitigations

## Related Documents

- [PoBF whitepaper overleaf link](https://www.overleaf.com/4268188831mdgcyfhmmfsg)
- [PoBF Slides keynote share](https://www.icloud.com/keynote/0da8dyFEr1CrbtnFFXST0UHnQ#PoBF)