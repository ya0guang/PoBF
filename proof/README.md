# Proof of PoBF Constraints

- Granularity of this model:

## Capabilities of the Abstract Machine Model

- Execution mode: enclave/normal
- machine model? functional/stack/register?

### Memory Model

- Linear Memory or Abstract Memory (named vars)
- Values: abstract/concrete values
- Cells: tagged secret levels + value
- Type: enclave(zone/not) or app
- Data structure: association List (mutable?) of Index * Type * Cell, mutable assoc. list is in Coq?
- Behavior of access
- Stack: need? how?

### Tasks

- Task: a list of procedures
- Procedure == Function
- Function: list of instr. + **a stack for arg passing?**
- How to say a procedure is critical?

### Instruction

Allowed operations

i := memory location
exp := var | mem(i) | stack(i) | imm(n) | fun(...) | rv(i)
statement := while *exp* do s end | s1; s2 | if *exp* then s1 else s2 end | eexit | eenter | read(i) | return exp | call proc. | var x := exp | 

- Enclave instr. (eenter/eexit)
- Memory Access (write/read/copy)
- Computation (unary & binary)
- Dereference
- **Declassification/Encryption**: how
- Branch
- Jump (**call** & direct jump with the function)
- **Any others**?

### Execution

- Input: (secret) tagged values on stack
- State: *stack*, *program(task(functions))*, memory, mode
- Execution as relation between states
- How to pass argument to a function?
  - Stack: binding of values?
  - Raw mem: PID instr?
- How to use a function as PID code?

