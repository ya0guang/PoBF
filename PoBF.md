# PoBF is ...

- A security principle
- A set of formally proved rules
- A reference implementation in Rust

## Design & Implementation

### Execution Integrity

- Rust
- Typestate

### Preventing Leakage

Check the OCALL parameters which may leak secret.

- Static Analysis (constant/taint analysis) (MIRAI)

### Scrubing Residue

`Zerorize` the Zone.
Zone <-> Stack + Reg + Heap

- For stack & reg: instrumentation (TODO)
- For heap: modify Rust's memory deallocator (TODO)

### TODOs?

- RA-TLS
- Secure secret provisioning

## Evaluation

### Security Evaluation

- What attack vectors are defended?

### Performace Evaluation

- Verification Overhead
- Runtime Overhead 
- Single- vs. Multi-User Enclave

### Case Study

- Porting efforts is acceptable
- Verifier can find the problems
