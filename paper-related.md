# PoBF Paper Org

## Motivation

- In-enclave isolation => sequential/concurrent service
- Privacy threats in CCC => 2 categories: leakage and residue
- Execution integrity (CFI + Memory safety) not enough => arbitrary calling sequence of service functions, need high-level workflow integrity
- Generalized Cloud CC scenario
- Residue? => some research take care of it (wenhao)
- Leakage? => information flow control

## Future Work

- Computation function chaining
- Dependent type to support function chaining workflow
  - Key use times is dependent on the length of the chain
  - Task status is also dependent on the length of the chain
