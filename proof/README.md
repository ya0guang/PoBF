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
- Error list.
- State: *stack*, *program(task(functions))*, memory, mode
- Execution as relation between states
- How to pass argument to a function?
  - Stack: binding of values?
  - Raw mem: PID instr?
- How to use a function as PID code?

### AST

security_tag := Secret | Declassified | Nonsense
enc_mem_tag  := ZoneMem | NonzoneMem
v   := nat | bool | Cleared | Any
tv  := v * security_tag
cell:= AppMem(tv) | UnusedMem | Encmem(enc_mem_tag, tv)
loc := Stack(n) | Var(str) | RV
exp := Loc(loc) | Val(v) | Unary(exp, op) | Binary(exp1, exp2, op)
com := Nop | Eenter | Eexit | Asgn (loc, exp) | Seq(com1, com2) 
      | If(exp, comt, come) | While(exp, com) | *call* | *declassification* 
