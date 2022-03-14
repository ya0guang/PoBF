Require Import Bool Arith List Lia List String.
Require Import Lists.List.
Import ListNotations.

(* Execution modes *)
Inductive mode : Type := 
  | NormalMode
  | EnclaveMode (* maybe we should have another critical mode! *)
.

(* Abstract Memory model *)

(* Content stored in the memory *)

Inductive enc_mem_tag : Type :=
  | ZoneMem
  | NonzoneMem
.

Inductive security_tag : Type :=
  | Secret
  | Declassified
  | Nonsense
.

Definition sum_two_tags (t1 t2: security_tag) : security_tag := 
  match t1 with
  | Nonsense => Nonsense
  | Secret => match t2 with
              | Nonsense => Nonsense
              | _ => Secret
              end
  
  | Declassified => match t2 with
              | Nonsense => Nonsense
              | Secret => Secret
              | Declassified => Declassified
              end
  end.

Inductive value : Type :=
  | ConcreteN (v: nat) (* This may not be a nat here? *)
  | ConcreteB (v: bool)
  | Any
.

Inductive location : Type :=
  | Stack (n: nat) (* the stack should be bounded! *)
  | Ident (s: string)
  | RV
.

Definition eq_location (i1 i2: location) : bool := 
  match i1, i2 with
  | Stack n1, Stack n2 => n1 =? n2
  | Ident s1, Ident s2 => if string_dec s1 s2 then true else false
  | RV, RV => true
  | _, _ => false
  end.

Theorem eq_location_eq: forall i1 i2, eq_location i1 i2 = true <-> i1 = i2.
Proof.
  split. 
  - destruct i1 eqn:eqi1; destruct i2 eqn:eqi2; unfold eq_location; 
    intros; try discriminate H.
    + apply beq_nat_true in H. rewrite H. reflexivity.
    + destruct (string_dec s s0) as [Hs_eq | Hs_not_eq]. subst. reflexivity. discriminate H.
    + reflexivity.
  - destruct i1 eqn:eqi1; destruct i2 eqn:eqi2; unfold eq_location; 
    intros; try discriminate H.
    + apply Nat.eqb_eq. inversion H. reflexivity.
    + destruct (string_dec s s0) as [Hs_eq | Hs_not_eq]. reflexivity. inversion H.
      unfold not in Hs_not_eq. apply Hs_not_eq in H1. destruct H1. 
    + reflexivity.
Qed.

Theorem eq_location_ne: forall i1 i2, eq_location i1 i2 = false <-> i1 <> i2.
Proof.
  split.
  - unfold not. intros. apply eq_location_eq in H0. rewrite H0 in H. discriminate H.
  - unfold not. intros.
  destruct i1 eqn:eqi1; destruct i2 eqn:eqi2; unfold eq_location; try reflexivity.
    + destruct (n =? n0) eqn: eqn0. apply Nat.eqb_eq in eqn0. subst. destruct H. reflexivity. reflexivity.
    + destruct (string_dec s s0). subst. destruct H. reflexivity. reflexivity.
    + destruct H. reflexivity. 
Qed.

Lemma eq_location_refl: forall (l: location), eq_location l l = true.
Proof.
  intros l. assert (H: l = l). reflexivity.
  apply eq_location_eq. reflexivity.
Qed.

Definition tagged_value: Type := prod value security_tag.

Definition tagged_value_example: tagged_value := (Any, Secret).

Inductive cell: Type :=
  | AppMem (v: tagged_value)
  | UnusedMem (* may not need this! *)
  | EncMem (z: enc_mem_tag) (v: tagged_value)
.

Definition cell_example1: cell := AppMem tagged_value_example.

Definition cell_example2: cell := EncMem ZoneMem tagged_value_example.

(* Result, memory, mapping, and accessing *)

Inductive error: Type := 
  | Invalid
  | NoPriviledge
.

Definition errors: Type := list error.

Inductive result {X: Type} : Type :=
  | Ok (v: X)
  | Err (e: errors)
.

Definition memory: Type := location -> cell.

Definition empty_mem (l: location) : memory := 
  (fun _ => UnusedMem).

Definition eqb_string (x y : location) : bool :=
  if eq_location x y then true else false.

Definition update (s: location) (v: cell) (m: memory) : memory := 
  fun s' => if (eq_location s' s) then v else m s'.

(* raw_* is designed for security monitor, and should not be used in *)
Definition raw_access (me: memory) (s: location) : option tagged_value := 
  match me s with
  | AppMem v => Some v
  | EncMem _ v => Some v
  | UnusedMem => None
  end.

(* Normal access doens't have restriction on reading to the Zone *)
Definition access' (me: memory) (mo: mode) (s: location) : @result tagged_value := 
  let c := me s in
    match mo, c with
    | _, UnusedMem => Err([Invalid])
    | EnclaveMode, AppMem v
    | EnclaveMode, EncMem _ v => Ok(v)
    | NormalMode, EncMem _ _ => Err([NoPriviledge])
    | NormalMode, AppMem v => Ok(v)
    end.

Definition access (me: memory) (mo: mode) (s: location) : @result tagged_value := 
  let c := me s in
    match mo, c with
    | _, UnusedMem => Err([Invalid])
    | EnclaveMode, AppMem v
    | EnclaveMode, EncMem _ v => Ok(v)
    | NormalMode, EncMem _ _ => Err([NoPriviledge])
    | NormalMode, AppMem v => Ok(v)
    end.

(* Abstract Syntax: Expressions *)

(* Inductive oprand: Type :=
  | OpLoc (l: location) (* secret level dependet *)
  | OpVal (v: value)    (* secret level always normal *)
. *)

Inductive exp: Type :=
  | ExpLoc (l: location)
  | ExpVal (v: value)
  | ExpUnary (e: exp) (op: value -> value)
  | ExpBinary (e1 e2: exp) (op: value -> value -> value)
.

(* Expression evaluation *)


Fixpoint exp_prop_tag (me: memory) (mo: mode) (e: exp) : security_tag := 
  match e with
  | ExpLoc l => match access me mo l with
                | Ok v => (snd v)
                | Err e => Nonsense
                end
  | ExpVal v => Declassified
  | ExpUnary e _ => exp_prop_tag me mo e
  | ExpBinary e1 e2 _ =>  let t1 := exp_prop_tag me mo e1 in
                          let t2 := exp_prop_tag me mo e2 in
                          sum_two_tags t1 t2
  end.

(* bool evaluation *)

(* NOT use in interpretation! *)
Fixpoint raw_exp_eval (me: memory) (e: exp) : @result value := 
  match e with
  | ExpLoc l => match raw_access me l with
                | Some v => Ok(fst v)
                | None => Err([Invalid])
                end
  | ExpVal v => Ok(v)
  | ExpUnary e _ => match raw_exp_eval me e with
                    | Ok _ => Ok(Any)
                    | Err er => Err(er)
                    end
  | ExpBinary e1 e2 _ => let r1 := raw_exp_eval me e1 in
                         let r2 := raw_exp_eval me e2 in
                         match r1, r2 with
                         | Ok _, Ok _ => Ok(Any)
                         | Err er1, Err er2 => Err(er1 ++ er2)
                         | Err er1, Ok _ => Err(er1)
                         | Ok _, Err er2 => Err(er2)
                         end
  end.

Fixpoint exp_eval (me: memory) (mo: mode) (e: exp) : @result value := 
  match e with
  | ExpLoc l => match access me mo l with
                | Ok v => Ok (fst v)
                | Err e => Err e
                end
  | ExpVal v => Ok(v)
  | ExpUnary e _ => match exp_eval me mo e with
                    | Ok _ => Ok(Any)
                    | e => e
                    end
  | ExpBinary e1 e2 _ => let r1 := exp_eval me mo e1 in
                         let r2 := exp_eval me mo e2 in
                         match r1, r2 with
                         | Ok _, Ok _ => Ok(Any)
                         | Err er1, Err er2 => Err(er1 ++ er2)
                         | Err er1, Ok _ => Err(er1)
                         | Ok _, Err er2 => Err(er2)
                         end
  end.

Definition exp_tagged_val (me: memory) (mo: mode) (e: exp) : @result tagged_value := 
  match (exp_eval me mo e), (exp_prop_tag me mo e) with
  | Ok v, t => Ok (v, t)
  | Err ev, _ => Err ev
  end.


(* bool evaluation *)

Definition value_as_bool (v: value) : bool := 
  match v with
  | ConcreteN n => match n with
                  | 0 => true
                  | S _ => false
                  end
  | ConcreteB b => b
  | Any => false
  end.

Definition exp_as_bool (me: memory) (mo: mode) (e: exp) : @result bool := 
  match exp_eval me mo e with
  | Ok v => Ok (value_as_bool v)
  | Err e => Err e
  end.


(* NOT use in interpretation!
Fixpoint raw_exp_as_bool (me: memory) (e: exp) : @result bool := 
  match e with
  | ExpLoc l => match raw_access me l with
                | Some v => Ok(value_as_bool v)
                | None => Err([Invalid])
                end
  | ExpVal v => Ok(value_as_bool v)
  | ExpUnary e _ => match raw_exp_as_bool me e with
                    | Ok _ => Ok(false)
                    | Err er => Err(er)
                    end
  | ExpBinary e1 e2 _ => let r1 := raw_exp_as_bool me e1 in
                         let r2 := raw_exp_as_bool me e2 in
                         match r1, r2 with
                         | Ok _, Ok _ => Ok(false)
                         | Err er1, Err er2 => Err(er1 ++ er2)
                         | Err er1, Ok _ => Err(er1)
                         | Ok _, Err er2 => Err(er2)
                         end
  end.

Fixpoint exp_as_bool (me: memory) (mo: mode) (e: exp) : @result bool := 
  match e with
  | ExpLoc l => match access me mo l with
                | Ok v => Ok (value_as_bool (fst v))
                | Err e => Err e
                end
  | ExpVal v => Ok(value_as_bool v)
  | ExpUnary e _ => match exp_as_bool me mo e with
                    | Ok _ => Ok(false)
                    | e => e
                    end
  | ExpBinary e1 e2 _ => let r1 := exp_as_bool me mo e1 in
                         let r2 := exp_as_bool me mo e2 in
                         match r1, r2 with
                         | Ok _, Ok _ => Ok(false)
                         | Err er1, Err er2 => Err(er1 ++ er2)
                         | Err er1, Ok _ => Err(er1)
                         | Ok _, Err er2 => Err(er2)
                         end
  end. *)

(* Abstract Syntax: Statements (commands) *)

Inductive com : Type :=
  | CNop
  | CEenter
  | CEexit
  | CAsgn (l: location) (v: exp)
  | CSeq (c1 c2: com)
  | CIf (b: exp) (c1 c2: com)
  | CWhile (b: exp) (c: com)
  (* Declasification *)
.

(* State Machine
Record State := {
  mo: mode;
  me: memory;
  vars: list location;
  er: errors;
}.

About State. *)

Definition accessible: Type := list location.


Definition procedure: Type := com.


Fixpoint leaked (me: memory) (vars: accessible) : bool := 
  match vars with
  | [] => false
  | l::ls => match me l with
            (* secrets cannot stay on AppMem or nonzone EncMem *)
            | AppMem (_, Secret) => true
            | EncMem NonzoneMem (_, Secret) => true
            | _ => leaked me ls
            end
  end.

Lemma leaked_no_leak: forall (me: memory) (vars: accessible) (l: location) (tv: tagged_value),
  leaked me vars = false -> In l vars -> raw_access me l = Some tv -> 
  me l = AppMem tv \/ me l = EncMem NonzoneMem tv -> ~(snd tv = Secret).
Proof.
  intros. generalize dependent l. generalize dependent tv. induction vars.
  - intros. simpl in *. destruct H0.
  - unfold not in *. unfold raw_access in *. intros. apply IHvars with tv l.
    + simpl in *. destruct (me a) eqn: eqa. destruct v. destruct s eqn: eqs.
      * discriminate H.
      * assumption.
      * assumption.
      * assumption.
      * destruct H0.
        -- (* a=l*)
          destruct z. assumption. destruct v. destruct s. discriminate H. assumption. assumption.
        -- (* In l vars *)
          destruct z. assumption. destruct v. destruct s. discriminate H. assumption. assumption.
    + destruct H0.
      * subst. destruct H2; simpl in H; rewrite H0 in *; destruct tv; simpl in *; subst; discriminate H.
      * assumption.
    + assumption.
    + assumption.
    + assumption.
Qed.
  
Lemma leaked_update: forall (me: memory) (vars: accessible) (l: location) (tv: tagged_value),
  leaked me vars = false -> leaked (update l (EncMem ZoneMem tv) me) vars = false.
Proof.
  intros. generalize dependent l. generalize dependent tv. generalize dependent H. induction vars.
  - simpl. reflexivity.
  - destruct (me a) eqn:eqa. destruct v eqn:eqv. destruct s eqn:eqs.
    + simpl. rewrite eqa. intros. discriminate H.
    + simpl. rewrite eqa. intros. destruct (eq_location a l) eqn: eqal. apply eq_location_eq in eqal.
    (* can be simpler *)
      * subst. unfold update. rewrite eq_location_refl. apply IHvars with tv l in H. unfold update in H. assumption.
      * subst. unfold update. rewrite eqal. rewrite eqa. apply IHvars with tv l in H. unfold update in H. assumption.
    + simpl. rewrite eqa. intros. apply IHvars with tv l in H.  destruct (eq_location a l) eqn: eqal;
      unfold update; unfold update in H.
      * rewrite eqal. assumption.
      * rewrite eqal. rewrite eqa. assumption.
    + simpl. rewrite eqa. intros. apply IHvars with tv l in H.  destruct (eq_location a l) eqn: eqal;
      unfold update; unfold update in H.
      * rewrite eqal. assumption.
      * rewrite eqal. rewrite eqa. assumption.
    + simpl. rewrite eqa. destruct z eqn: eqz. intros. apply IHvars with tv l in H. destruct (eq_location a l) eqn: eqal; unfold update in *; rewrite eqal.
      * assumption.
      * rewrite eqa. assumption.
      * destruct v. destruct s eqn: eqs; intros; try discriminate H; apply IHvars with tv l in H; unfold update in *; destruct (eq_location a l) eqn: eqal; try rewrite eqa; try assumption; try assumption.
Qed.

Lemma leaked_update_l: forall (me: memory) (vars: accessible) (l: location) (tv: tagged_value),
  leaked me vars = false -> leaked (update l (EncMem ZoneMem tv) me) (l::vars) = false.
Proof.
  intros. generalize dependent l. generalize dependent tv. generalize dependent H. induction vars.
  - simpl. intros. unfold update. rewrite eq_location_refl. reflexivity.
  - intros H. simpl in H. destruct (me a) eqn:eqa; try destruct v; try destruct s eqn:eqs; try discriminate H;
    intros tv l; try destruct z eqn: eqz; try apply IHvars with tv l in H; simpl in H; unfold update in H; try rewrite eq_location_refl in H;
    repeat try (unfold update; simpl; rewrite eq_location_refl; destruct (eq_location a l) eqn: eqal;
      unfold update; try rewrite eqa; try assumption).
    discriminate H.
Qed.

(* We regard all the arguments to a procedure are passed through stack *)
(* should they also lie on the zoen? *)
Fixpoint is_critical' (me: memory) (vars: accessible) : bool :=
  match vars with
  | [] => false
  | h :: t => match h with
              | Stack n => match me h with
                          | EncMem ZoneMem (_, Secret) => true
                          | _ => is_critical' me t
                            end
              | _ => is_critical' me t
              end
  end.

Fixpoint is_critical (me: memory) (vars: accessible) : bool :=
  match vars with
  | [] => false
  | h :: t => match me h with
              (* cirtical only when secret is in the zone *)
              | EncMem ZoneMem (_, Secret) => true
              | _ => is_critical me t
              end
  end.

Lemma cirtical_propagate: forall (me: memory) (vars: accessible) (l: location) (tv: tagged_value),
(* should not update a location on stack *)
  is_critical me vars = true -> 
  is_critical (update l (EncMem ZoneMem tv) me) (l::vars) = true.
Proof.
  intros. generalize dependent l. generalize dependent tv. generalize dependent H. induction vars.
  - simpl. intros. discriminate H.
  - intros. destruct tv eqn: eqtv; destruct s eqn: eqs; simpl in IHvars; simpl in H; destruct (me a) eqn: eqa; 
    unfold update; simpl; rewrite eq_location_refl; try reflexivity.
    +  assert (H' := H). apply IHvars with tv l in H'. unfold update in *. simpl. rewrite eq_location_refl in *.
      rewrite eqtv in H'. destruct (eq_location a l) eqn: eqal. assumption. rewrite eqa. assumption.
    + assert (H' := H). apply IHvars with tv l in H'. unfold update in *. simpl. rewrite eq_location_refl in *.
      rewrite eqtv in H'. destruct (eq_location a l) eqn: eqal. assumption. rewrite eqa. assumption.
    + assert (H' := H). destruct v0 eqn: eqv0. destruct z eqn: eqz. destruct s0 eqn: eqs0.
      simpl. unfold update. destruct (eq_location a l) eqn: eqal.
      apply IHvars with tv l in H'. unfold update in *. simpl. rewrite eq_location_refl in *.
    rewrite eqtv in H'. destruct (eq_location a l) eqn: eqal. assumption. rewrite eqa. assumption.

(* for critical procedures, secrects need to lay in the Zone *)

Definition state: Type := memory * mode * accessible * errors.

(* Semantics *)

Check (length).

(* interpreter for cirtcal procedures *)
Inductive com_eval_critical : com -> state -> state -> Prop :=
  (* | E_Err_ignore (me: memory) (mo: mode) (vars: accessible) (ers: errors) 
    (Herr: (length ers) >= 1) (c: com):
    com_eval_critical c (me, mo, vars, ers) (me, mo, vars, ers) *)
  | E_Nop (me: memory) (mo: mode) (vars: accessible) (ers: errors) (ers: errors): 
    com_eval_critical CNop (me, mo, vars, ers) (me, mo, vars, ers)
  | E_Eenter (me: memory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = []):
    com_eval_critical CEenter (me, mo, vars, ers) (me, EnclaveMode, vars, ers)
  | E_Eexit (me: memory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = []):
    com_eval_critical CEexit (me, mo, vars, ers) (me, NormalMode, vars, ers)
  | E_Asgn_Ok (me: memory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = [])
    (l: location) (v: exp) (r: tagged_value) (Hexp: exp_tagged_val me mo v = (Ok r)):
    (* Write restricted in the Zone! *)
    com_eval_critical (CAsgn l v) (me, mo, vars, ers) ((update l (EncMem ZoneMem r) me), mo, (l :: vars), ers)
  | E_Asgn_Err (me: memory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = [])
    (l: location) (v: exp) (er: errors) (Hexp: exp_tagged_val me mo v = (Err er)):
    com_eval_critical (CAsgn l v) (me, mo, vars, ers) (me, mo, vars, (er ++ ers))
  | E_Seq (st st' st'': state) (c1 c2: com)
    (Hc1: com_eval_critical c1 st st') (Hc2: com_eval_critical c2 st' st''):
    com_eval_critical (CSeq c1 c2) st st''
  | E_If_then (me: memory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c1 c2: com) (st': state):
    exp_as_bool me mo b = Ok true -> 
    com_eval_critical c1 (me, mo, vars, ers) st' -> 
    com_eval_critical (CIf b c1 c2) (me, mo, vars, ers) st'
  | E_If_else (me: memory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c1 c2: com) (st': state):
    exp_as_bool me mo b = Ok false -> 
    com_eval_critical c2 (me, mo, vars, ers) st' -> 
    com_eval_critical (CIf b c1 c2) (me, mo, vars, ers) st'
  | E_If_err (me: memory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c1 c2: com) (st': state) (er: errors):
    exp_as_bool me mo b = Err er -> 
    com_eval_critical (CIf b c1 c2) (me, mo, vars, ers) (me, mo, vars, er ++ ers)
  | E_while_true (me: memory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c: com) (st': state):
    exp_as_bool me mo b = Ok true -> 
    com_eval_critical c (me, mo, vars, ers) st' -> 
    com_eval_critical (CWhile b c) (me, mo, vars, ers) st'
  | E_while_false (me: memory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c: com) (st': state):
    exp_as_bool me mo b = Ok false -> 
    com_eval_critical (CWhile b c) (me, mo, vars, ers) (me, mo, vars, ers)
  | E_while_err (me: memory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c: com) (st': state) (er: errors):
    exp_as_bool me mo b = Err er -> 
    com_eval_critical (CWhile b c) (me, mo, vars, ers) (me, mo, vars, er ++ ers)
.

(* Lemma error_ignore : forall (me: memory) (mo: mode) (vars: accessible) (ers: errors) (c: com),
  ((length ers) >= 1) -> com_eval_critical c (me, mo, vars, ers) (me, mo, vars, ers).
Proof.
  intros. constructor. assumption.
Qed. *)

Theorem CNop_refl: forall (me me': memory) (mo mo': mode) (vars vars': accessible) (ers ers': errors),
  com_eval_critical CNop (me, mo, vars, ers) (me', mo', vars', ers') -> me = me' /\ mo = mo' /\ vars = vars' /\ ers = ers'.
Proof.
  intros. repeat split; inversion H; subst; reflexivity.
Qed.


Theorem restricted_no_leakage_proc: forall (c: com) (me me': memory) (mo mo': mode) (vars vars': accessible) (ers ers': errors),
  leaked me vars = false -> is_critical me vars = true ->
  com_eval_critical c (me, mo, vars, ers) (me', mo', vars', ers') ->
  leaked me' vars' = false.
Proof.
  intros c. induction c; intros; try (inversion H1; rewrite <- H7; rewrite <- H9; assumption).
  - (* CAsgn *)
    inversion H1. apply leaked_update_l. assumption. rewrite <- H9. rewrite <- H11. assumption.
  - (* CSeq *)
    inversion H1. destruct st' as [[[me'' mo''] vars''] ers'']. 
    assert (H' := H). apply IHc2 with me'' mo'' mo' vars'' ers'' ers';
    try apply IHc1 with me mo mo'' vars ers ers''; try assumption. 
    inversion Hc1; inversion Hc2; subst; try apply leaked_update_l; try assumption. unfold update

  me', mo, mo', vars', ers, ers'.
  (* inversion cannot get far enough *)
  inversion H1; subst; try assumption. 
  - 
  - apply leaked_update_l. assumption.
  (* inversion stucked at the Seq case *)
  - assert (Hr: com_eval_critical c (me, mo, vars, ers) (me', mo', vars', ers')). constructor.
  apply leaked_update. simpl. 
    + destruct (me l) eqn: eql. destruct v0. destruct s eqn: eqs. subst.
Qed.


(* Procedure(functionn) and task *)

Definition procedure := list com.


(* Fixpoint deref (m: mem_layout) (l: location) : tag_value :=
  match m with
  | nil => (UnusedMem, Any)
  | (h :: t) => if l =? fst h then snd h else deref t l
  end.

Definition deref_val (m: mem_layout) (l: location) : value := 
  snd (deref m l).

Check pair.

Definition mode_deref (mo: mode) (ml: mem_layout) (l: location) : value := 
  let tv := deref ml l in
    match (fst tv), mo with
    | EncMem(_), NormalMode => Error
    | _, _ => snd tv
    end.

Notation "m ':' x '!->' v" := (m, (x, v))
                              (at level 100, v at next level, right associativity).

Definition test_memory_layout = []. *)

(* Modeling Instructions *)

(* We model the instructions in a more abstract way *)

(* TODO: jumps, branches, ref, [loops] *)


(* How to say a procedure is critical? *)

(* Virtual Stack? *)

(* How to make a function PID? *)

(* Need a secret tag for propagation, i.e., mimicing taint analysis *)

Definition function := list instr.

Definition task := list function.

Inductive function' : Type -> Prop :=
  | ConstantF  : function' y
  | UnaryF (f: X -> Y) : function' X Y
  | HigherOrderF (Z: Type) (H) (f:  -> Y ) : function' X Y
.


