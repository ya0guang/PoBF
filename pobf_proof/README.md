# Proof of PoBF Security Constraints

The model is built on the **language** level, rather than on the **machine** level.
Therefore the model is mahcine-independent, but mimics the behaviors of common imperative languages because of Turing Completeness.

## Concerns

- May the model be too general? i.e., not modeling specific enclaves

## Simplified Model

### Capabilities of the Abstract Model

- Execution mode : enclave/normal
- Memory isolation: enclave and normal memory
- *Multi-threading*

### Memory Model (Enclave Model)

- Mode := `NormalMode` | `EnclaveMode`
- Value := `ConcretN(v: nat)` | `ConcretB (v: bool)` | `Any` | `Cleared`
- Location := `Stack(n: nat)` | `Ident(s: string)` | `RV`
- SecurityTag := `Secret` | `NotSecret` | `NonSense`
- EnclaveTag := `ZoneMem` | `NonZoneMem`
- TagValue := `Value * SecurityTag`
- Cell := `AppMem(v: TagValue)` | `DummyMem` | `UnusedMem` | `EncMem(z: EnclaveTag, v: TagValue)`
- Memory: functional list `Location -> Cell` 

The registers can be represented by location for Ident(s), e.g., Ident("rax").

### Enclave Program Model

- Exp := `ExpLoc(l: Location)` | `ExpVal(v: Value)` | `ExpUnary(e: Exp)` | `ExpBinary(E1 E2: Exp)`
- Com := `Nop` | `Eenter` | `Eexit` | `Asgn(l: Location, v: Exp)` | `Seq(c1 c2: Com)` | `If(b: Exp, c1 c2: Com)` | `While(b: Exp, c: Com)`
- Procedure := `Com`
- Accessible := `listof(Location)`
- State := `Mode * Memory * Accessible`

Branch, loop, and assignment are modeled, as well as the TEE context switches.
Semantics are modeled as relationships.

### Definitions

- Leak: secrets find on places other than the zone (i.e., secrets cannot stay on AppMem or nonzone EncMem)
- Residue: secret found in memory (other than RV).
- Critical: accessible vars contain secrets in the zone

### Security Constraints

#### For Leakage (proved)

For any critical procedure $p$ and initial state $st=(me, mo, vars, errs)$,, the execution of $p$ does not leak secret if:
1. the initial state $st$ does not leak secret
2. all memory writes (i.e., `Asgn`) in $p$ are within Zone if the value
is Secret
3. execution of $p$ aborts when error occurs

#### For Residue (proved)

`zeroize` is a procedure taking memory $me$ and accessible variables $vars$,
for every location $l \in vars$ where $c=me(l)$ is in Zone of the enclave,
the tagged value $v$ stored in the cell $c$ is cleared and the security tag is set to `NotSecret`.

For any critical procedure $p$, if it satisfies No-Leakage
requirement, the procedure $p'$ concatenating $p$ and `Zeroize` ($p'=p;\;zerorize$) satisfies No-Residue requirement.

#### Multi-threading (stuck)

If thread-specific Zone can only be accessible to the corresponding thread (i.e., dedicated Zone for each thread), then it satisfies No-Leakage and No-Residue.

## Usage

First, make sure that Coq is correctly installed.
Then run `coq_makefile -f _CoqProject -o Makefile` to generate a makefile.
Last, run `make` to compile the proof.
