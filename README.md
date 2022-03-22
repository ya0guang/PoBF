# PoBF-compliant Platform Reference Implementation

## Verifier requirements

Check [this Readme](verifier/README.md) for more details.

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