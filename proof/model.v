Require Import Bool Arith List Lia List String Logic.
Require Import Logic.FunctionalExtensionality.
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
  | Notsecret
  | Nonsense
.

Definition sum_two_tags (t1 t2: security_tag) : security_tag := 
  match t1 with
  | Nonsense => Nonsense
  | Secret => match t2 with
              | Nonsense => Nonsense
              | _ => Secret
              end
  
  | Notsecret => match t2 with
              | Nonsense => Nonsense
              | Secret => Secret
              | Notsecret => Notsecret
              end
  end.

Inductive value : Type :=
  | ConcreteN (v: nat) (* This may not be a nat here? *)
  | ConcreteB (v: bool)
  | Any
  | Cleared
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

Definition loc_in_enclave (me: memory) (l: location) : Prop := 
  exists (z: enc_mem_tag) (v: tagged_value), me l = EncMem z v.

Definition loc_unused (me: memory) (l: location) : Prop :=
  me l = UnusedMem.

Definition loc_in_app (me: memory) (l: location) : Prop :=
  exists (v: tagged_value), me l = AppMem v.

(* Definition empty_mem' (l: location) : memory := 
  (fun _ => UnusedMem). *)

Definition empty_mem : memory := 
  (fun _ => UnusedMem).

Definition eqb_string (x y : location) : bool :=
  if eq_location x y then true else false.

Definition update (s: location) (v: cell) (m: memory) : memory := 
  fun s' => if (eq_location s' s) then v else m s'.

(* update a location different from X desn't affect X's value *)
Lemma update_invariant: forall (l1 l2: location) (v: cell) (m: memory),
  eq_location l1 l2 = false -> update l2 v m l1 = m l1.
Proof.
  intros. unfold update. rewrite H. reflexivity.
Qed.

Lemma update_comm: forall l1 l2 c1 c2 me,
  l1 <> l2 -> update l1 c1 (update l2 c2 me) = update l2 c2 (update l1 c1 me).
Proof.
  intros. extensionality l. unfold update. 
  destruct (eq_location l l1) eqn: eqll1; destruct (eq_location l l2) eqn: eqll2.
  - apply eq_location_eq in eqll1. apply eq_location_eq in eqll2. subst. unfold not in H. destruct H. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


Lemma update_shadow: forall (me: memory) (l: location) (c1 c2: cell),
  update l c1 (update l c2 me) = update l c1 me.
Proof.
  intros. unfold update. extensionality s.
  destruct (eq_location s l) eqn: eqsl.
  reflexivity. reflexivity.
Qed.


(* raw_* is designed for security monitor, and should not be used in *)
Definition raw_access (me: memory) (s: location) : option tagged_value := 
  match me s with
  | AppMem v => Some v
  | EncMem _ v => Some v
  | UnusedMem => None
  end.

(* Normal access doens't have restriction on reading to the Zone *)
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
  | ExpVal v => Notsecret
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
  | Any => true
  | Cleared => false
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

Definition accessible: Type := list location.

(* State Machine
Record State := {
  mo: mode;
  me: memory;
  vars: accessible;
  er: errors;
}.

About State. *)

Definition procedure: Type := com.


(* secrets find on places other than the zone *)
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

Lemma leaked_update': forall (me: memory) (vars: accessible) (l: location) (tv: tagged_value),
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

(* writing new var in the Zone doesn't leak secret *)
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
(* Fixpoint is_critical' (me: memory) (vars: accessible) : bool :=
  match vars with
  | [] => false
  | h :: t => match h with
              | Stack n => match me h with
                          | EncMem ZoneMem (_, Secret) => true
                          | _ => is_critical' me t
                            end
              | _ => is_critical' me t
              end
  end. *)

(* accessible vars contain secrets in the zone *)
(* Critical Should ONLY describe procedure(s) *)
Fixpoint is_critical (me: memory) (vars: accessible) : bool :=
  match vars with
  | [] => false
  | h :: t => match me h with
              (* cirtical only when secret is in the zone *)
              | EncMem ZoneMem (_, Secret) => true
              | _ => is_critical me t
              end
  end.

Definition is_critical_loc (me: memory) (l: location) : bool :=
  match me l with
  | UnusedMem => false
  | AppMem tv
  | EncMem _ tv => match tv with
                  | (_, Secret) => true
                  | _ => false
                  end
  end.

(* critical expression? *)
Fixpoint is_critical_exp (me: memory) (e: exp) : bool :=
  match e with
  | ExpLoc l => is_critical_loc me l
  | ExpVal _ => false
  | ExpUnary e _ => is_critical_exp me e
  | ExpBinary e1 e2 _ => is_critical_exp me e1 || is_critical_exp me e2
  end.

(* critical procedure? *)
Fixpoint is_critical_com (me: memory) (c: com) : bool :=
  match c with
  | CNop
  | CEenter
  | CEexit => false
  (* what if assigning to a critical location? *)
  | CAsgn _ exp => is_critical_exp me exp
  | CSeq c1 c2 => is_critical_com me c1 || is_critical_com me c2
  | CIf b c1 c2 => is_critical_exp me b || is_critical_com me c1 || is_critical_com me c2
  | CWhile b c => is_critical_exp me b || is_critical_com me c
  end.

Lemma critical_CSeq: forall (me: memory) (c1 c2: com),
  is_critical_com me (CSeq c1 c2) = true -> is_critical_com me c1 = true \/ is_critical_com me c2 = true.
Proof.
  intros. inversion H. assert (H1' := H1). apply orb_true_iff in H1. rewrite H1'. assumption.
Qed.

Lemma cirtical_propagate_sec_zone: forall (me: memory) (vars: accessible) (l: location) (tv: tagged_value),
(* should not update a location on stack *)
  is_critical me vars = true -> snd(tv) = Secret ->
  is_critical (update l (EncMem ZoneMem tv) me) (l::vars) = true.
Proof.
  intros. generalize dependent l. generalize dependent tv. generalize dependent H. induction vars.
  - simpl. intros. discriminate H.
  - intros. destruct tv eqn: eqtv. simpl in *. unfold update in *. rewrite eq_location_refl in *.
    destruct (me a) eqn: eqa.
    + apply IHvars with tv l in H. rewrite eq_location_refl in H. subst. reflexivity. rewrite eqtv. subst. reflexivity.
    + apply IHvars with tv l in H. rewrite eq_location_refl in H. subst. reflexivity. rewrite eqtv. subst. reflexivity.
    + rewrite H0. reflexivity.
Qed.  

(* updating the state may result in declassification of a secret variable in the Zone, which may lead to declassification!!!! *)

(* Lemma cirtical_propagate: forall (me: memory) (vars: accessible) (l: location) (tv: tagged_value),
(* should not update a location on stack *)
  is_critical me vars = true -> 
  is_critical (update l (EncMem ZoneMem tv) me) (l::vars) = true. *)
(* Proof. *)
  (* intros. generalize dependent l. generalize dependent tv. generalize dependent H. induction vars.
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
    rewrite eqtv in H'. destruct (eq_location a l) eqn: eqal. assumption. rewrite eqa. assumption. *)

(* for critical procedures, secrects need to lay in the Zone *)

Inductive valid_asgn: mode -> memory -> accessible -> Prop :=
  | VA_Normal_Empty (l: location) (tv: tagged_value):
    valid_asgn NormalMode (update l (AppMem tv) empty_mem) [l]
  | VA_Normal_Claim (me: memory) (vars: accessible) (l: location) (tv: tagged_value)
    (Hm: loc_unused me l) (HI: valid_asgn NormalMode me vars):
    valid_asgn NormalMode (update l (AppMem tv) me) (l::vars)
  | VA_Normal_Update (me: memory) (vars: accessible) (l: location) (tv: tagged_value)
    (Hm: loc_in_app me l) (HI: valid_asgn NormalMode me vars):
    valid_asgn NormalMode (update l (AppMem tv) me) (l::vars)
  
.

Definition state: Type := memory * mode * accessible * errors.

(* Semantics *)

Check (length).

(* interpreter for cirtcal procedures *)
Inductive com_eval_critical : com -> state -> state -> Prop :=
  | E_Nop (me: memory) (mo: mode) (vars: accessible) (ers: errors) (ers: errors): 
    com_eval_critical CNop (me, mo, vars, ers) (me, mo, vars, ers)
  | E_Eenter (me: memory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = []):
    com_eval_critical CEenter (me, mo, vars, ers) (me, EnclaveMode, vars, ers)
  | E_Eexit (me: memory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = []):
    com_eval_critical CEexit (me, mo, vars, ers) (me, NormalMode, vars, ers)
  | E_Asgn_Ok_enc (me: memory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = [])
    (l: location) (v: exp) (r: tagged_value) (Hexp: exp_tagged_val me mo v = (Ok r))
    (Henc: mo = EnclaveMode):
    (* What if not in the enclave mode? *)
    (* Write restricted in the Zone! *)
    com_eval_critical (CAsgn l v) (me, mo, vars, ers) ((update l (EncMem ZoneMem r) me), mo, (l :: vars), ers)
  | E_Asgn_Err_access (me: memory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = [])
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
    (b: exp) (c1 c2: com) (er: errors):
    exp_as_bool me mo b = Err er -> 
    com_eval_critical (CIf b c1 c2) (me, mo, vars, ers) (me, mo, vars, er ++ ers)
  | E_while_true (me: memory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c: com) (st': state):
    exp_as_bool me mo b = Ok true -> 
    com_eval_critical c (me, mo, vars, ers) st' -> 
    com_eval_critical (CWhile b c) (me, mo, vars, ers) st'
  | E_while_false (me: memory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c: com):
    exp_as_bool me mo b = Ok false -> 
    com_eval_critical (CWhile b c) (me, mo, vars, ers) (me, mo, vars, ers)
  | E_while_err (me: memory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c: com) (er: errors):
    exp_as_bool me mo b = Err er -> 
    com_eval_critical (CWhile b c) (me, mo, vars, ers) (me, mo, vars, er ++ ers)
  | E_Err_ignore (me: memory) (mo: mode) (vars: accessible) (ers: errors) 
    (Herr: (length ers) >= 1) (c: com):
    com_eval_critical c (me, mo, vars, ers) (me, mo, vars, ers)
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

(* Assume that executing a critical procedure doesn't change its criticalness *)
(* This should ONLY be used in single-threaded scenerios! *)
Lemma criticanlness_not_change: forall (c: com) (me me': memory) (mo mo': mode) (vars vars': accessible) (ers ers': errors),
  is_critical me vars = true -> com_eval_critical c (me, mo, vars, ers) (me', mo', vars', ers') -> 
  is_critical me' vars' = true.
Proof.
Admitted.

(* Restricted *)
(* for a critical procedure, executing in the critical mode never leads to leakage *)
Theorem restricted_no_leakage_proc: forall (c: com) (me me': memory) (mo mo': mode) (vars vars': accessible) (ers ers': errors),
  com_eval_critical c (me, mo, vars, ers) (me', mo', vars', ers') ->
  (* no leakage at the beginning, criticalness doesn't change *)
  leaked me vars = false -> is_critical me vars = true ->
  leaked me' vars' = false.
Proof.
  intros c. induction c; intros; try (inversion H1; rewrite <- H7; rewrite <- H9; assumption);
  inversion H; subst; try assumption.
  - (* CAsgn *)
    apply leaked_update_l. assumption.
  - (* CSeq *)
    destruct st' as [[[me'' mo''] vars''] ers''].
    apply IHc2 with me'' mo'' mo' vars'' ers'' ers';
    try apply IHc1 with me mo mo'' vars ers ers''; try assumption; 
    apply criticanlness_not_change with c1 me mo mo'' vars ers ers''; assumption. 
  - (* CIf_then *)
    apply IHc1 with me mo mo' vars [] ers'; assumption.
  - (* CIf_else *)
    apply IHc2 with me mo mo' vars [] ers'; assumption.
  - (* CIf_err *)
    apply IHc with me mo mo' vars [] ers'; assumption.
Qed.

Theorem restricted_no_leakage_proc': forall (c: com) (me me': memory) (mo mo': mode) (vars vars': accessible) (ers ers': errors),
  com_eval_critical c (me, mo, vars, ers) (me', mo', vars', ers') ->
  (* no leakage at the beginning *)
  leaked me vars = false -> 
  leaked me' vars' = false.
Proof.
  intros c. induction c; intros; try (inversion H1; rewrite <- H7; rewrite <- H9; assumption);
  inversion H; subst; try assumption.
  - (* CAsgn *)
    apply leaked_update_l. assumption.
  - (* CSeq *)
    destruct st' as [[[me'' mo''] vars''] ers''].
    apply IHc2 with me'' mo'' mo' vars'' ers'' ers';
    try apply IHc1 with me mo mo'' vars ers ers''; try assumption. 
  - (* CIf_then *)
    apply IHc1 with me mo mo' vars [] ers'; assumption.
  - (* CIf_else *)
    apply IHc2 with me mo mo' vars [] ers'; assumption.
  - (* CIf_err *)
    apply IHc with me mo mo' vars [] ers'; assumption.
Qed.

(* Procedure(functionn) and task *)

Definition task := list procedure.

(* And leftover will be considered residue *)

(* Residue handling *)

(* Fixpoints with prime(') denote that the whole memory is considered, including RV *)
Fixpoint residue_secret' (me: memory) (vars: accessible): bool := 
  match vars with
  | [] => false
  | h :: t => match me h with
              | EncMem _ (_, Secret) => true
              | AppMem (_, Secret) => true
              | _ => residue_secret' me t
              end
  end.

Fixpoint residue_secret (me: memory) (vars: accessible): bool := 
  match vars with
  | [] => false
  | h :: t => match h with
              | RV => residue_secret me t
              | _ => match me h with
                      | EncMem _ (_, Secret) => true
                      | AppMem (_, Secret) => true
                      | _ => residue_secret me t
                      end
              end
  end.

Fixpoint zeroize' (me: memory) (vars: accessible): memory := 
  match vars with
  | [] => me
  | h :: t => match me h with
              | EncMem ZoneMem _ => 
                (* zerorize the zone *)
                zeroize' (update h (EncMem ZoneMem (Cleared, Notsecret)) me) t
              | _ => zeroize' me t
              end
  end.

(* zerorize all memory locations other than the return value *)
Fixpoint zeroize (me: memory) (vars: accessible): memory := 
  match vars with
  | [] => me
  | h :: t => match h with
              (* exclude return value *)
              | RV => zeroize me t
              | _ => match me h with
                    (* zerorize the zone *)
                    | EncMem ZoneMem _ => 
                      zeroize (update h (EncMem ZoneMem (Cleared, Notsecret)) me) t
                    | _ => zeroize me t
                    end
              end
  end.

Lemma zeroize_not_effect_nonezone: forall (vars: accessible) (me: memory) (l: location),
  (forall (tv: tagged_value), ~(me l = EncMem ZoneMem tv)) -> zeroize me vars l = me l.
Proof.
  intros vars. induction vars.
  - intros. simpl. reflexivity.
  - intros me l Htv. simpl. assert (H' := Htv). 
    destruct a eqn: eqa; destruct (me a) eqn: eqma; try destruct z eqn: eqz; rewrite eqa in eqma; try rewrite eqma; try apply IHvars; try apply H'.

    (* the following proof can be more consise *)
    destruct (eq_location l (Stack n)) eqn: eqln. apply eq_location_eq in eqln.
    rewrite <- eqln in eqma. apply H' in eqma. destruct eqma.
    assert (Ha: (update (Stack n) (EncMem ZoneMem (Cleared, Notsecret)) me) l = me l).
    apply update_invariant. assumption. rewrite <- Ha. apply IHvars. intros. rewrite Ha. apply H'.

    destruct (eq_location l (Ident s)) eqn: eqln. apply eq_location_eq in eqln.
    rewrite <- eqln in eqma. apply H' in eqma. destruct eqma.
    assert (Ha: (update (Ident s) (EncMem ZoneMem (Cleared, Notsecret)) me) l = me l).
    apply update_invariant. assumption. rewrite <- Ha. apply IHvars. intros. rewrite Ha. apply H'.
Qed.

Lemma zeroize_update_invariant: forall (vars: accessible) (me: memory) (l1 l2: location) (c: cell),
  l1 <> l2 -> zeroize (update l2 c me) vars l1 = zeroize me vars l1.
Proof.
  intros vars. induction vars.
  - intros. simpl. unfold update. apply eq_location_ne in H. rewrite H. reflexivity.
  - intros. simpl. destruct a eqn: eqa.
    + destruct (eq_location a l2) eqn: eql2a.
      * unfold update in *. rewrite eqa in eql2a. rewrite eql2a.
        destruct (me (Stack n)) eqn: eqma;
        destruct c eqn: eqc; try destruct z eqn: eqz; try (apply IHvars; assumption);
        apply eq_location_eq in eql2a; subst.
        -- assert (Hup:  update (Stack n) (EncMem ZoneMem (Cleared, Notsecret)) (update (Stack n) (EncMem ZoneMem v0) me) = update (Stack n) (EncMem ZoneMem (Cleared, Notsecret)) me).
        apply update_shadow. unfold update in Hup. rewrite Hup. apply IHvars. assumption.
        -- assert (Hup:  update (Stack n) (EncMem ZoneMem (Cleared, Notsecret)) (update (Stack n) (EncMem ZoneMem v) me) = update (Stack n) (EncMem ZoneMem (Cleared, Notsecret)) me).
        apply update_shadow. unfold update in Hup. rewrite Hup. apply IHvars. assumption.
        -- assert (H' := H). apply IHvars with (me:= me) (c:= AppMem v0) in H. rewrite H. symmetry. 
        apply IHvars. assumption.
        -- assert (H' := H). apply IHvars with (me:= me) (c:= UnusedMem) in H. rewrite H. symmetry. 
        apply IHvars. assumption.
        -- destruct z0 eqn: eqz. 
          assert (Hup:  update (Stack n) (EncMem ZoneMem (Cleared, Notsecret)) (update (Stack n) (EncMem ZoneMem v0) me) = update (Stack n) (EncMem ZoneMem (Cleared, Notsecret)) me). apply update_shadow. unfold update in Hup. rewrite Hup. reflexivity.
          assert (H' := H). apply IHvars with (me:= me) (c:= EncMem NonzoneMem v0) in H. rewrite H. 
          symmetry. apply IHvars. assumption.
        -- destruct z0 eqn: eqz. 
          assert (Hup:  update (Stack n) (EncMem ZoneMem (Cleared, Notsecret)) (update (Stack n) (EncMem ZoneMem v0) me) = update (Stack n) (EncMem ZoneMem (Cleared, Notsecret)) me). apply update_shadow. unfold update in Hup. rewrite Hup.  apply IHvars. assumption.
          apply IHvars. assumption.
      * unfold update in *. rewrite eqa in eql2a. rewrite eql2a.
        destruct (me (Stack n)) eqn: eqma; try apply IHvars; try assumption.
        destruct z eqn: eqz. 
        assert (Ha: update (Stack n) (EncMem ZoneMem (Cleared, Notsecret)) (update l2 c me) = update l2 c (update (Stack n) (EncMem ZoneMem (Cleared, Notsecret)) me)). apply update_comm. apply eq_location_ne in eql2a. assumption. unfold update in Ha. rewrite Ha.
        apply IHvars. assumption.
        apply IHvars. assumption.
    + destruct (eq_location a l2) eqn: eql2a.
      * unfold update in *. rewrite eqa in eql2a. rewrite eql2a.
        destruct (me (Ident s)) eqn: eqma;
        destruct c eqn: eqc; try destruct z eqn: eqz; try (apply IHvars; assumption);
        apply eq_location_eq in eql2a; subst.
        -- assert (Hup:  update (Ident s) (EncMem ZoneMem (Cleared, Notsecret)) (update (Ident s) (EncMem ZoneMem v0) me) = update (Ident s) (EncMem ZoneMem (Cleared, Notsecret)) me).
        apply update_shadow. unfold update in Hup. rewrite Hup. apply IHvars. assumption.
        -- assert (Hup:  update (Ident s) (EncMem ZoneMem (Cleared, Notsecret)) (update (Ident s) (EncMem ZoneMem v) me) = update (Ident s) (EncMem ZoneMem (Cleared, Notsecret)) me).
        apply update_shadow. unfold update in Hup. rewrite Hup. apply IHvars. assumption.
        -- assert (H' := H). apply IHvars with (me:= me) (c:= AppMem v0) in H. rewrite H. symmetry. 
        apply IHvars. assumption.
        -- assert (H' := H). apply IHvars with (me:= me) (c:= UnusedMem) in H. rewrite H. symmetry. 
        apply IHvars. assumption.
        -- destruct z0 eqn: eqz. 
          assert (Hup:  update (Ident s) (EncMem ZoneMem (Cleared, Notsecret)) (update (Ident s) (EncMem ZoneMem v0) me) = update (Ident s) (EncMem ZoneMem (Cleared, Notsecret)) me). apply update_shadow. unfold update in Hup. rewrite Hup. reflexivity.
          assert (H' := H). apply IHvars with (me:= me) (c:= EncMem NonzoneMem v0) in H. rewrite H. 
          symmetry. apply IHvars. assumption.
        -- destruct z0 eqn: eqz. 
          assert (Hup:  update (Ident s) (EncMem ZoneMem (Cleared, Notsecret)) (update (Ident s) (EncMem ZoneMem v0) me) = update (Ident s) (EncMem ZoneMem (Cleared, Notsecret)) me). apply update_shadow. unfold update in Hup. rewrite Hup.  apply IHvars. assumption.
          apply IHvars. assumption.
      * unfold update in *. rewrite eqa in eql2a. rewrite eql2a.
        destruct (me (Ident s)) eqn: eqma; try apply IHvars; try assumption.
        destruct z eqn: eqz. 
        assert (Ha: update (Ident s) (EncMem ZoneMem (Cleared, Notsecret)) (update l2 c me) = update l2 c (update (Ident s) (EncMem ZoneMem (Cleared, Notsecret)) me)). apply update_comm. apply eq_location_ne in eql2a. assumption. unfold update in Ha. rewrite Ha.
        apply IHvars. assumption.
        apply IHvars. assumption.
    + apply IHvars. assumption.
Qed.

Lemma zeroize_zeroize_zone: forall (vars: accessible) (me: memory) (l: location),
  l <> RV ->  zeroize (update l (EncMem ZoneMem (Cleared, Notsecret)) me) vars l = EncMem ZoneMem (Cleared, Notsecret).
Proof.
  intros vars. induction vars.
  - intros. simpl. unfold update. rewrite eq_location_refl. reflexivity.
  - intros me l H. destruct a eqn: eqa; simpl.
    + destruct (eq_location a l) eqn: eqal. 
      (* eq_location a l = true *)
      apply eq_location_eq in eqal. subst.
      unfold update. rewrite eq_location_refl. 
      assert (Hup:  update (Stack n) (EncMem ZoneMem (Cleared, Notsecret)) (update (Stack n) (EncMem ZoneMem (Cleared, Notsecret)) me) = update (Stack n) (EncMem ZoneMem (Cleared, Notsecret)) me).
      apply update_shadow. unfold update in *. rewrite Hup. 
      apply IHvars. auto. unfold update. rewrite eqa in eqal. rewrite eqal. destruct (me (Stack n)) eqn: eqma; unfold update in IHvars; try apply IHvars; try assumption.
      (* eq_location a l = false *)
      destruct z eqn: eqz.
      (* Zonemem *)
      apply eq_location_ne in eqal. assert (Hn: Stack n <> RV). unfold not. intros. inversion H0. 
      assert (Hln : l <> Stack n). auto.
      apply zeroize_update_invariant with (vars:=vars) (me:=(update l (EncMem ZoneMem (Cleared, Notsecret)) me)) (c:=EncMem ZoneMem (Cleared, Notsecret)) in Hln. unfold update in Hln. rewrite Hln. apply IHvars. assumption.
      (* Nonzonemem *)
      apply IHvars. assumption.
    + destruct (eq_location a l) eqn: eqal. 
      (* eq_location a l = true *)
      apply eq_location_eq in eqal. subst.
      unfold update. rewrite eq_location_refl. 
      assert (Hup: update (Ident s) (EncMem ZoneMem (Cleared, Notsecret)) (update (Ident s) (EncMem ZoneMem (Cleared, Notsecret)) me) = update (Ident s) (EncMem ZoneMem (Cleared, Notsecret)) me).
      apply update_shadow. unfold update in *. rewrite Hup. 
      apply IHvars. auto. unfold update. rewrite eqa in eqal. rewrite eqal. destruct (me (Ident s)) eqn: eqma; unfold update in IHvars; try apply IHvars; try assumption.
      (* eq_location a l = false *)
      destruct z eqn: eqz.
      (* Zonemem *)
      apply eq_location_ne in eqal. assert (Hn: Ident s <> RV). unfold not. intros. inversion H0. 
      assert (Hln : l <> Ident s). auto.
      apply zeroize_update_invariant with (vars:=vars) (me:=(update l (EncMem ZoneMem (Cleared, Notsecret)) me)) (c:=EncMem ZoneMem (Cleared, Notsecret)) in Hln. unfold update in Hln. rewrite Hln. apply IHvars. assumption.
      (* Nonzonemem *)
      apply IHvars. assumption.
    + apply IHvars. assumption.
Qed.

Theorem zeroize_sound: forall (vars: accessible) (me: memory),
  leaked me vars = false -> residue_secret (zeroize me vars) vars = false.
Proof.
  intros vars. induction vars.
  - intros. simpl. reflexivity.
  - intros. destruct (me a) eqn: eqma.
    + destruct a eqn: eqa; simpl; try rewrite eqma;
      simpl in H; rewrite eqma in H.
      * assert (Ha: forall tv, me a <> EncMem ZoneMem tv). unfold not; intros tv Ha'. subst.
        rewrite eqma in Ha'. inversion Ha'. apply zeroize_not_effect_nonezone with vars me a in Ha.
        subst. rewrite Ha. rewrite eqma. destruct v. destruct s eqn: eqs. discriminate H.
        apply IHvars. assumption. apply IHvars. assumption.
      * assert (Ha: forall tv, me a <> EncMem ZoneMem tv). unfold not; intros tv Ha'. subst.
        rewrite eqma in Ha'. inversion Ha'. apply zeroize_not_effect_nonezone with vars me a in Ha.
        subst. rewrite Ha. rewrite eqma. destruct v. destruct s0 eqn: eqs0. discriminate H.
        apply IHvars. assumption. apply IHvars. assumption.
      * apply IHvars. destruct v. destruct s eqn: eqs. discriminate H.
        assumption. assumption.
    + destruct a eqn: eqa; simpl; try rewrite eqma;
      simpl in H; rewrite eqma in H.
      * assert (Ha: forall tv, me a <> EncMem ZoneMem tv). unfold not; intros tv Ha'. subst.
        rewrite eqma in Ha'. inversion Ha'. apply zeroize_not_effect_nonezone with vars me a in Ha.
        subst. rewrite Ha. rewrite eqma. apply IHvars. assumption.
      * assert (Ha: forall tv, me a <> EncMem ZoneMem tv). unfold not; intros tv Ha'. subst.
        rewrite eqma in Ha'. inversion Ha'. apply zeroize_not_effect_nonezone with vars me a in Ha.
        subst. rewrite Ha. rewrite eqma. apply IHvars. assumption.
      * apply IHvars. assumption.
    + destruct a eqn: eqa; simpl; try rewrite eqma.
      * destruct z eqn: eqz; simpl in H; rewrite eqma in H.
        assert (Ha: zeroize (update (Stack n) (EncMem ZoneMem (Cleared, Notsecret)) me) vars
        (Stack n) =(EncMem ZoneMem (Cleared, Notsecret))).
        apply zeroize_zeroize_zone. unfold not. intros. inversion H0.
        rewrite Ha. apply IHvars. apply leaked_update'. simpl in H. assumption.
        (* nonzone *)
        assert (Ha: forall tv, me a <> EncMem ZoneMem tv). unfold not; intros tv Ha'. subst.
        rewrite eqma in Ha'. inversion Ha'. apply zeroize_not_effect_nonezone with vars me a in Ha.
        subst. rewrite Ha. rewrite eqma. destruct v. destruct s eqn: eqs. discriminate H.
        apply IHvars. assumption. apply IHvars. assumption.
      * destruct z eqn: eqz; simpl in H; rewrite eqma in H.
        assert (Ha: zeroize (update (Ident s) (EncMem ZoneMem (Cleared, Notsecret)) me) vars
        (Ident s) =(EncMem ZoneMem (Cleared, Notsecret))).
        apply zeroize_zeroize_zone. unfold not. intros. inversion H0.
        rewrite Ha. apply IHvars. apply leaked_update'. simpl in H. assumption.
        (* nonzone *)
        assert (Ha: forall tv, me a <> EncMem ZoneMem tv). unfold not; intros tv Ha'. subst.
        rewrite eqma in Ha'. inversion Ha'. apply zeroize_not_effect_nonezone with vars me a in Ha.
        subst. rewrite Ha. rewrite eqma. destruct v. destruct s0 eqn: eqs0. discriminate H.
        apply IHvars. assumption. apply IHvars. assumption.
      * apply IHvars. simpl in H. rewrite eqma in H. destruct z eqn: eqz. assumption.
        destruct v. destruct s eqn: eqs. discriminate H. assumption. assumption.
Qed.

