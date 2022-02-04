# PoBF

## Definitions

### Been Forgotten

For a procedure($p$) dealing with secrets($S$) whose return value is $r_p$, $p(S)$, $BF(p(S)) \Leftrightarrow \lnot Leakage(p, S^*) \wedge \lnot Residue(p, S^*)$, Where $Leakage$ and $Residue$ are predicates and $S^*$ represents all variables which is affected(tainted) by $s \in S$.

*how to define leakage and residue?*

- Leakage

$Leakage(p, S^*)$ is true when $s^* \in S^*$ is accessible to entities other than $p$ or the sub-procedures of $p$ while $p$ is being executed.

- Residue

$Residue(p, S^*)$ is true when $s* \in S^* \setminus \{r_p\}$ is accessible to an entity after $p$ is executed.

## One Design

In the context of TEE, we specify a specific region called **zone**($\mathcal{Z}$) which is completely within the enclave memory, $\mathcal{Z} \subset \mathcal{E}$.

We restrict write to this zone when the procedure is running, and denote this rule as $\mathsf{W\_Restrict}(p(S), \mathcal{Z})$. More specifically,
$\mathsf{W\_Restrict}(p(S), \mathcal{Z}) \Leftrightarrow \forall op(arg*) \in p. \  op(arg*) = write(arg*) \implies args \in \mathcal{Z}$

So, we can prove $\mathsf{W\_Restrict}(p(S), \mathcal{Z}) \implies \lnot Leakage(p, S^*)$.

For the residue, we enforce a safe cleaning (zeroize memory) at the end of $p$ and denote as rule $\mathsf{Zeroize}(p(S), \mathcal{Z})$ where zero are written to all memory locations in $\mathcal{Z}$ other than the return value $r_p$.

We can also prove $\mathsf{Zeroize}(p(S), \mathcal{Z}) \implies \lnot Residue(p, S^*)$.

Therefore, we have $\mathsf{Zeroize}(p(S), \mathcal{Z}) \wedge \mathsf{W\_Restrict}(p(S), \mathcal{Z}) \implies BF(p(S))$, and we convert the Prove of Been Forgotten to a proof of the two rules.

We exclude the covert- and side-channels from the leakage just for simplicity. A non-interference rule could also be added to the definition of Been Forgotten to satisfy a stronger threat model. 
