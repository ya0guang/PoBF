# PoBF-compliant Platform Reference Implementation

## Verifier

### Verifier in Rust

Suspended
`cargo-pobfv/`

### Verifier in Python

`verifier/`

Can verify:

- If `unsafe` is forbidden in the source code files
- If OCALL(s) potentially sensitive leak
- If Rust compiler can compile the code

## Problems in the Rust Code

### Unsafe Code

Automatic Check

#### Potential Solutions

- [X] Provide a library to wrap unsafe code
- [ ] Transfer types directly across enclave boundry
- [ ] **Admit** this problem as a deficit

## TODOs

- Zone Allocator and its verification
- Verifier in Rust?
- *Formal proof of PoBF constraints* partially done

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