Require Import Bool Arith List Lia List String Logic.
Require Import Logic.FunctionalExtensionality.
Require Import Lists.List.
Import ListNotations.

(** ** TEE Execution modes *)
Inductive mode : Type := 
  | NormalMode
  | EnclaveMode (* maybe we should have another critical mode! *)
.

(** * Abstract Memory model *)

(** ** Tags *)
Inductive enclave_tag : Type :=
  | ZoneMem
  | NonzoneMem
.

Inductive security_tag : Type :=
  | Secret
  | Notsecret
  | Nonsense
.

(** *** security_tag Propagation *)
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

(** *** Abstract value v' *)
Inductive value : Type :=
  | ConcreteN (v: nat) (* This may not be a nat here? *)
  | ConcreteB (v: bool)
  | Any
  | Cleared
.

(** *** Location l  *)
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

Theorem eq_location_comm: forall (l1 l2: location), eq_location l1 l2 = eq_location l2 l1.
Proof.
  intros.
  destruct l1 eqn: eql1; destruct l2 eqn: eql2; simpl; try reflexivity.
  - eauto. Search ( _ =? _). apply Nat.eqb_sym.
  - destruct (string_dec s s0) eqn:ss0; destruct (string_dec s0 s) eqn:s0s;
      try reflexivity; subst; destruct n; reflexivity.
Qed.  

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

(** *** TagValue v *)
Definition tag_value: Type := prod value security_tag.

Definition tag_value_example: tag_value := (Any, Secret).

(** *** Cell c *)
Inductive cell: Type :=
  | AppMem (v: tag_value)
  | DummyMem
  | UnusedMem (* may not need this! *)
  | EncMem (z: enclave_tag) (v: tag_value)
.

Definition In_zone (c: cell) : Prop :=
  exists v, c = EncMem ZoneMem v.

Definition cell_example1: cell := AppMem tag_value_example.

Definition cell_example2: cell := EncMem ZoneMem tag_value_example.

(* Result, memory, mapping, and accessing *)

Inductive error: Type := 
  | Invalid
  | NoPriviledge
.

Definition errors: Type := list error.

Inductive option {X: Type} : Type :=
| Some (v: X)
| None
.

Inductive result {X: Type} : Type :=
  | Ok (v: X)
  | Err (e: errors)
.

(* maybe we should use a Mapping here? *)
Definition memory : Type := list (location * cell).

Definition empty_memory : memory := nil.

Fixpoint raw_read (me: memory) (l: location) : @option cell :=
  match me with
  | nil => None
  | hd :: tl => if eq_location (fst hd) l then Some (snd hd) else raw_read tl l
  end.

(* read with priviledge and validity checks *)
Definition read (mo: mode) (me: memory) (l: location) : @result tag_value :=
  match raw_read me l with
  | None => Err([Invalid])
  | Some c => match c with
             | AppMem v => Ok(v)
             | DummyMem | UnusedMem => Err([Invalid])
             | EncMem _ v => match mo with
                            | EnclaveMode => Ok(v)
                            | NormalMode => Err([NoPriviledge])
                            end
             end
  end.

Definition memory_eq (me1 me2: memory) : Prop :=
  forall l, raw_read me1 l = raw_read me2 l.

Fixpoint update_countinue (me: memory) (mc: memory) (l: location) (c:cell) : memory :=
  match me with
  | nil => (l, c) :: mc
  | hd :: tl => if eq_location (fst hd) l then (mc ++ (l, c) :: tl) else update_countinue tl (mc ++ [hd]) l c 
  end.

Definition update (me: memory) (l: location) (c: cell) : memory :=
  update_countinue me nil l c.

Example mem_eg1: memory := update empty_memory (Ident "rax") (AppMem ((ConcreteN 6), Secret)).

Print mem_eg1.

(* Lemma update_comm: forall l1 l2 c1 c2 me, *)
(*   memory_eq (update (update me l2 c2) l1 c1) (update (update me l1 c1) l2 c2). *)
(* Proof. *)
(*   induction me. *)
(*   - unfold update, update_countinue. simpl. *)
(*     destruct (eq_location l1 l2) eqn: eql1l2. rewrite eq_location_comm; *)
(*     rewrite eql1l2     *)


(** * Abstract Syntax *)

(* Inductive oprand: Type :=
  | OpLoc (l: location) (* secret level dependet *)
  | OpVal (v: value)    (* secret level always normal *)
. *)

(** ** Expression *)
Inductive exp: Type :=
  | ExpLoc (l: location)
  | ExpVal (v: value)
  | ExpUnary (e: exp) (op: value -> value)
  | ExpBinary (e1 e2: exp) (op: value -> value -> value)
.   

(** *** Expression: tag propagation *)
Fixpoint exp_prop_tag (mo: mode) (me: memory) (e: exp) : security_tag := 
  match e with
  | ExpLoc l => match read mo me l with
                | Ok v => (snd v)
                | Err e => Nonsense
                end
  | ExpVal v => Notsecret
  | ExpUnary e _ => exp_prop_tag mo me e
  | ExpBinary e1 e2 _ =>  let t1 := exp_prop_tag mo me e1 in
                          let t2 := exp_prop_tag mo me e2 in
                          sum_two_tags t1 t2
  end.

Fixpoint exp_eval (mo: mode) (me: memory) (e: exp) : @result value := 
  match e with
  | ExpLoc l => match read mo me l with
                | Ok v => Ok (fst v)
                | Err e => Err e
                end
  | ExpVal v => Ok(v)
  | ExpUnary e _ => match exp_eval mo me e with
                    | Ok _ => Ok(Any)
                    | e => e
                    end
  | ExpBinary e1 e2 _ => let r1 := exp_eval mo me e1 in
                         let r2 := exp_eval mo me e2 in
                         match r1, r2 with
                         | Ok _, Ok _ => Ok(Any)
                         | Err er1, Err er2 => Err(er1 ++ er2)
                         | Err er1, Ok _ => Err(er1)
                         | Ok _, Err er2 => Err(er2)
                         end
  end.

Definition exp_tagged_val (mo: mode) (me: memory) (e: exp) : @result tag_value := 
  match (exp_eval mo me e), (exp_prop_tag mo me e) with
  | Ok v, t => Ok (v, t)
  | Err ev, _ => Err ev
  end.

(** *** Expression: bool evaluation  *)
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

Definition exp_as_bool (mo: mode) (me: memory) (e: exp) : @result bool := 
  match exp_eval mo me e with
  | Ok v => Ok (value_as_bool v)
  | Err e => Err e
  end.

(** ** Abstract Syntax: Statements (commands) *)
Inductive com : Type :=
  | CNop
  | CEenter                     (* Enclave specific *)
  | CEexit                      (* Enclave specific *)
  | CAsgn (l: location) (v: exp)
  | CSeq (c1 c2: com)
  | CIf (b: exp) (c1 c2: com)
  | CWhile (b: exp) (c: com)
  (* Declasification *)
.

(* a list tracking all accessible vars *)
Definition accessible: Type := list location.

Fixpoint get_accessible (me: memory) : accessible :=
  match me with
  | nil => nil
  | hd :: tl => (fst hd) :: get_accessible tl
  end.

(* State Machine
Record State := {
  mo: mode;
  me: memory;
  er: errors;
}.

About State. *)

(* procedure is semantically equivalent to com *)
Definition procedure: Type := com.

(** * PoBF: leaked *)
(* secrets find on places other than the zone *)

Definition leaked_cell (c: cell) : bool :=
  match c with
    | AppMem (_, Secret) => true
    | DummyMem | UnusedMem | AppMem _ => false
    | EncMem NonzoneMem (_, Secret) => true
    | EncMem _ _ => false
  end.
                     
Fixpoint leaked (me: memory) : bool :=
  match me with
  | [] => false
  | hd :: tl => if leaked_cell (snd hd) then true else leaked tl
  end.


(* How to express this theorem? *)
(* Lemma leaked_false_no_leak: forall (me: memory) (l: location) (c: cell), *)
(*   leaked me = false -> In l (get_accessible me) -> raw_read me l = Some c ->  *)

Lemma no_leak: forall me l c tv,
    leaked me = false -> raw_read me l = Some c ->
    c = AppMem tv \/ c = EncMem NonzoneMem tv -> ~(snd tv = Secret).
Proof.
  intros. generalize dependent l. generalize dependent tv. induction me.
  - intros. inversion H0.
  - simpl. intros. destruct a eqn: eqa. subst. simpl in *.
    destruct (eq_location l0 l) eqn: eql0l. 
    + apply eq_location_eq in eql0l. inversion H0. subst. destruct H0.
      destruct c eqn: eqc.
      * destruct H1. inversion H0. subst. destruct tv eqn:eqtv;
          destruct s; simpl; eauto; try inversion H; intros Ha; discriminate Ha.
        discriminate H0.
      * inversion H1; inversion H0.
      * inversion H1; inversion H0.
      * inversion H1; inversion H0. subst.
        destruct tv eqn: eqtv; destruct s eqn: eqs. inversion H.
        simpl. intros Ha. inversion Ha.
        simpl. intros Ha. inversion Ha.
    + eapply IHme. destruct c0 eqn: eqc0; try assumption.
      * destruct v eqn: eqv. destruct s. inversion H. assumption. assumption.
      * destruct z. assumption. destruct v. destruct s.
        inversion H. assumption. assumption.
      * assumption.
      * exact H0.
Qed.

Lemma concat_no_leak :
  forall me mc, leaked me = false -> leaked mc = false ->
           leaked (me ++ mc) = false.
Proof.
  induction me; intros.
  - simpl. assumption.
  - Search (_::_ ++ _). rewrite <- app_comm_cons. simpl.
    inversion H. destruct (leaked_cell (snd a)) eqn: eqla.
    inversion H2. rewrite H2. apply IHme.
    assumption. assumption.
Qed.

Lemma update_countinue_no_leak :
  forall me mc l c, leaked me = false -> leaked mc = false -> leaked_cell c = false ->
               leaked (update_countinue me mc l c) = false.
Proof.
  induction me; intros.
  - simpl. rewrite H1. assumption.
  - simpl. inversion H.
    destruct (leaked_cell (snd a)) eqn: eqsa. discriminate H3. rewrite H3.
    destruct (eq_location (fst a) l) eqn: eqal.
    apply concat_no_leak. assumption. simpl. rewrite H1. assumption.
    apply IHme; try assumption. apply concat_no_leak. assumption.
    simpl. rewrite eqsa. auto.
Qed.

Hint Immediate update_countinue_no_leak: core.

Lemma update_zone_no_leak: forall me l tv,
    leaked me = false -> leaked (update me l (EncMem ZoneMem tv)) = false.
Proof with eauto.
  intros. unfold update. apply update_countinue_no_leak...
Qed.

Definition state := memory * mode * errors.

(** ** Definition: Critical State *)
(* Definition:  Current memory contains secrets in the zone *)
Fixpoint is_critical (me: memory) : bool :=
  match me with
  | [] => false
  | hd :: tl => match snd hd with
              | EncMem ZoneMem (_, Secret) => is_critical tl
              | _ => false
              end
  end.

(** * Semantics of the Statements *)
(* interpreter for critical state *)
Inductive com_eval_critical : com -> state -> state -> Prop :=
  | E_Nop (me: memory) (mo: mode) (vars: accessible) (ers: errors) (ers: errors): 
    com_eval_critical CNop (me, mo, ers) (me, mo, ers)
  | E_Eenter (me: memory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = []):
    com_eval_critical CEenter (me, mo, ers) (me, EnclaveMode, ers)
  | E_Eexit (me: memory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = []):
    com_eval_critical CEexit (me, mo, ers) (me, NormalMode, ers)
  | E_Asgn_Ok_enc (me: memory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = [])
    (l: location) (v: exp) (r: tag_value) (Hexp: exp_tagged_val mo me v = (Ok r))
    (Henc: mo = EnclaveMode):
    (* What if not in the enclave mode? *)
    (* Write restricted in the Zone! *)
    com_eval_critical (CAsgn l v) (me, mo, ers) ((update me l (EncMem ZoneMem r) ), mo, ers)
  | E_Asgn_Err_access (me: memory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = [])
    (l: location) (v: exp) (er: errors) (Hexp: exp_tagged_val mo me v = (Err er)):
    com_eval_critical (CAsgn l v) (me, mo, ers) (me, mo, (er ++ ers))
  | E_Seq (st st' st'': state) (c1 c2: com)
    (Hc1: com_eval_critical c1 st st') (Hc2: com_eval_critical c2 st' st''):
    com_eval_critical (CSeq c1 c2) st st''
  | E_If_then (me: memory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c1 c2: com) (st': state):
    exp_as_bool mo me b = Ok true -> 
    com_eval_critical c1 (me, mo, ers) st' -> 
    com_eval_critical (CIf b c1 c2) (me, mo, ers) st'
  | E_If_else (me: memory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c1 c2: com) (st': state):
    exp_as_bool mo me b = Ok false -> 
    com_eval_critical c2 (me, mo, ers) st' -> 
    com_eval_critical (CIf b c1 c2) (me, mo, ers) st'
  | E_If_err (me: memory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c1 c2: com) (er: errors):
    exp_as_bool mo me b = Err er -> 
    com_eval_critical (CIf b c1 c2) (me, mo, ers) (me, mo, er ++ ers)
  | E_while_true (me: memory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c: com) (st': state):
    exp_as_bool mo me b = Ok true -> 
    com_eval_critical c (me, mo, ers) st' -> 
    com_eval_critical (CWhile b c) (me, mo, ers) st'
  | E_while_false (me: memory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c: com):
    exp_as_bool mo me b = Ok false -> 
    com_eval_critical (CWhile b c) (me, mo, ers) (me, mo, ers)
  | E_while_err (me: memory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c: com) (er: errors):
    exp_as_bool mo me b = Err er -> 
    com_eval_critical (CWhile b c) (me, mo, ers) (me, mo, er ++ ers)
  | E_Err_ignore (me: memory) (mo: mode) (vars: accessible) (ers: errors) 
    (Herr: (length ers) >= 1) (c: com):
    com_eval_critical c (me, mo, ers) (me, mo, ers)
.


(* No criticalness required here! *)
Theorem restricted_no_leakage_proc: forall (c: com) (me me': memory) (mo mo': mode) (ers ers': errors),
      com_eval_critical c (me, mo, ers) (me', mo', ers') ->
  (* no leakage at the beginning, criticalness doesn't change *)
  leaked me = false ->
  leaked me' = false.
Proof with eauto.
  intros c. induction c; intros; inversion H; subst; try assumption...
  - (* CAsgn *)
    apply update_zone_no_leak...
  - (* CSeq *)
    destruct  st'. destruct p. eapply IHc2. exact Hc2.
    eapply IHc1. exact Hc1... assumption.
Qed.
    
Fixpoint residue_secret' (me: memory): bool :=
  match me with
  | [] => false
  | (l, c)::tl => match c with
                | EncMem _ (_, Secret) => true
                | AppMem (_, Secret) => true
                | _ => residue_secret' tl
                end
  end.

Fixpoint zeroize' (me: memory) : memory :=
  match me with
  | [] => me
  | (l, c)::tl => match c with
                | EncMem ZoneMem _ =>
                    (* Zeroize the entire Zone *)
                    (l, EncMem ZoneMem (Cleared, Notsecret))::(zeroize' tl)
                | _ => (l, c)::(zeroize' tl)
                end
  end.

Fixpoint residue_secret (me: memory) : bool :=
  match me with
  | [] => false
  | (l, c)::tl => match l with
                | RV => residue_secret tl
                | _ => match c with
                      | EncMem _ (_, Secret) => true
                      | AppMem (_, Secret) => true
                      | _ => residue_secret tl
                      end
                end
  end.

Fixpoint zeroize (me: memory) : memory :=
  match me with
  | [] => me
  | (l, c)::tl => match l with
                | RV => (l, c)::(zeroize tl)
                | _ => match c with
                      | EncMem ZoneMem _ =>
                          (l, EncMem ZoneMem (Cleared, Notsecret))::(zeroize tl)
                      | _ => zeroize tl
                      end
                end
  end.

(* Zeroized memory contains no secret residue if not leaked *)
Theorem zeroize_sound: forall me,
    leaked me = false -> residue_secret (zeroize me) = false.
Proof.
  induction me; intros.
  - reflexivity.
  - simpl. destruct a. inversion H. destruct (leaked_cell c). inversion H1.
    destruct l eqn: eql; destruct c eqn: eqc;
      rewrite H1; try destruct z; try apply IHme; try auto.
Qed.
    
