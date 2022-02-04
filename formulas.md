# Formalizing PoBF

## Definitions

1. protected data & keys include data in the four states and two keys
 
$P = \{d, k_i, k_o\}$, which contains data, input decryption key, and output encryption key.

2. $\textit{r}(e)$: the number of references to $e$, where $e \in P$

3. $\textit{s}(e)$: the status of $e$, where $\textit{s}(d) \in \{\textsf{S}_{E, I}, \textsf{S}_{E, O}, \textsf{S}_{D, I,} \textsf{S}_{D, O}, \textsf{I}\}$ and $\textit{k} \in \{\textsf{S}_{S}, \textsf{I}\}$, where $\textsf{I}$ represents *invalid*; *E*, *D*, *I*, *O*, *S* represents Encrypted, Decrypted, Input, Output, and Sealed in subscript.

## State Transition

See the state transition diagrams for keys and data.

## Security Requirements

### No Copy

Rule $\forall e \in P. G r(e) \le 1$, which means the number of references to protected data is always at most 1.

### Constraint on Modules

For each stage in the platform, we want the protected data and keys strictly follow the state rules, therefore enforcing the pre-condition and post-condition for each stage. We need to prove that each stage satisfies the constraints, and the precondition of the next stage is the post condition of the previous stage. Therefore we just need to enforce the pre-condition is satisfied, and the stages satisfy the constraints, but we don't need to enforce the pre-condition of stages other than the first one. 

For the first supporting module before execution

#### Supporting Modules; Before Execution

$\vdash (\textit{s}(k_i) = \textsf{S}_{S} \wedge \textit{s}(k_o) = \textsf{S}_{S} \wedge \textit{s}(d) = \textsf{S}_{E, I}) \\
    \{B.SM\} \\
    (\textit{s}(k_i) = \textsf{S}_{S} \wedge \textit{s}(k_o) = \textsf{S}_{S} \wedge \textit{s}(d) = \textsf{S}_{E, I})$

#### Before Function Phase


$\vdash (\textit{s}(k_i) = \textsf{S}_{S} \wedge \textit{s}(k_o) = \textsf{S}_{S} \wedge \textit{s}(d) = \textsf{S}_{E, I}) \\
    \{BF\} \\
    (\textit{s}(k_i) = \textsf{I} \wedge \textit{s}(k_o) = \textsf{S}_{S} \wedge \textit{s}(d) = \textsf{S}_{D, I})$

In the BF phase, $eid$ and $idk$ are consumed, so they should be sealed before the BF stage and consumed(invalidated) after this stage. The $did$ is produced by decryption so it will be sealed after the stage. The $oek$ is untouched in BF and its status remains sealed.

We can derive similar rules for other modules:

#### During Function Phase

$\vdash (\textit{s}(k_i) = \textsf{I} \wedge \textit{s}(k_o) = \textsf{S}_{S} \wedge \textit{s}(d) = \textsf{S}_{D, I}) \\
    \{DF\} \\
    (\textit{s}(k_i) = \textsf{I} \wedge \textit{s}(k_o) = \textsf{S}_{S} \wedge \textit{s}(d) = \textsf{S}_{D, O})$

#### After Function Phase

$\vdash (\textit{s}(k_i) = \textsf{I} \wedge \textit{s}(k_o) = \textsf{S}_{S} \wedge \textit{s}(d) = \textsf{S}_{D, O}) \\
    \{AF\} \\
    (\textit{s}(k_i) = \textsf{I} \wedge \textit{s}(k_o) = \textsf{I} \wedge \textit{s}(d) = \textsf{S}_{E, O})$



#### Supporting Modules; After Execution

$\vdash (\textit{s}(k_i) = \textsf{I} \wedge \textit{s}(k_o) = \textsf{I} \wedge \textit{s}(d) = \textsf{S}_{E, O}) \\
    \{A.SM\} \\
    (\textit{s}(k_i) = \textsf{I} \wedge \textit{s}(k_o) = \textsf{I} \wedge \textit{s}(d) = \textsf{S}_{E, O})$

We may enforce that the last supporting module executed after execution invalidates the data, which indicates the termination of the service cycle. However, the platform cannot leak out sensitive information if it cannot decrypt the encrypted output data, so we ignored this constraint for sanity and ease of verification.