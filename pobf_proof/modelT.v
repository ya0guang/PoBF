Require Import Bool Arith List Lia List String Logic.
Require Import Logic.FunctionalExtensionality.
Require Import Lists.List.
Require Import POBF.model.
Import ListNotations.

Definition ThreadId := nat.

(* The location is bound *)
(* TODO: add global *)
(* Definition Tlocation : Type := prod ThreadId location. *)

(* Definition Taccessible: Type := list Tlocation. *)

(* Definition eq_Tlocation (i1 i2: Tlocation) : bool :=  *)
(*   match i1, i2 with *)
(*   | (tid1, l1), (tid2, l2) => if tid1 =? tid2 then eq_location l1 l2 else false *)
(*   end. *)

(* Theorem eq_Tlocation_eq: forall i1 i2, eq_Tlocation i1 i2 = true <-> i1 = i2. *)
(* Proof. *)
(*   split. *)
(*   - destruct i1 eqn:eqi1; destruct i2 eqn:eqi2; unfold eq_Tlocation;  *)
(*     intros; try discriminate H; apply pair_equal_spec; split; *)
(*     destruct (t =? t0) eqn: eqtt0; try apply Nat.eqb_eq; try assumption; try discriminate H. apply eq_location_eq. assumption. *)
(*   - destruct i1 eqn:eqi1; destruct i2 eqn:eqi2; unfold eq_location;  *)
(*     intros; inversion H. unfold eq_Tlocation. rewrite Nat.eqb_refl. *)
(*     apply eq_location_eq. reflexivity. *)
(* Qed. *)

(* Lemma eq_Tlocation_refl: forall (l: Tlocation), eq_Tlocation l l = true. *)
(* Proof. *)
(*   intros l. assert (H: l = l). reflexivity. *)
(*   apply eq_Tlocation_eq. reflexivity. *)
(* Qed. *)

(* ThreadId, as the owner of the cell, is stored in Tcell *)
Inductive Tcell: Type :=
  | TAppMem (v: tag_value) (* note that thread isolation doesn't work on insecure memory! *)
  | TDummyMem
  | TUnusedMem
  | TEncMem (t: ThreadId) (z: enclave_tag) (v: tag_value)
.

Definition Tmemory: Type := location -> Tcell.

Definition empty_Tmem : Tmemory := 
  (fun _ => TUnusedMem).

(* This update is secure! *)
Definition Tupdate (t: ThreadId) (l: location) (v: Tcell) (m: Tmemory) : Tmemory := 
  match v with
  | TDummyMem => m
  | TAppMem _ 
  | TUnusedMem => fun s' => if (eq_location s' l) then v else m s'
  | TEncMem t' _ _ => if (t' =? t) (*Checking if the updating is allowed! *)
                        then fun s' => if (eq_location s' l) then v else m s'
                        else m  (* update failed *)
  end.

Definition unsafe_update (t: ThreadId) (s: location) (v: Tcell) (m: Tmemory) : Tmemory := 
  fun s' => if (eq_location s' s) then v else m s'.

(* safe memory access *)
Definition Taccess (t: ThreadId) (me: Tmemory) (mo: mode) (s: location) : @result tag_value := 
  let c := me s in
    match mo, c with
    | _, TDummyMem
    | _, TUnusedMem => Err([Invalid])
    | EnclaveMode, TAppMem v => Ok v
    (* Checking if enclave memory of another thread is accessed *)
    | EnclaveMode, TEncMem t' _ v => if t' =? t then Ok v else Err([NoPriviledge])
    | NormalMode, TEncMem _ _ _ => Err([NoPriviledge])
    | NormalMode, TAppMem v => Ok(v)
    end.

(* We assume that only the enclave memory is thread-specific *)
Theorem Taccess_App_shared: forall (me: Tmemory) mo (t t': ThreadId) l v,
  me l = TAppMem v -> Taccess t' me mo l = Ok v.
Proof.
  intros. unfold Taccess.
  destruct mo eqn: eqmo; destruct (me l) eqn: eql; inversion H; try reflexivity.
Qed.

Theorem Taccess_Unused_shared: forall (me: Tmemory) mo (t t': ThreadId) l,
  me l = TUnusedMem -> Taccess t' me mo l = Err([Invalid]).
Proof.
  intros. unfold Taccess.
  destruct mo eqn: eqmo; destruct (me l) eqn: eql; inversion H; try reflexivity.
Qed.

(* secrets find on places other than the zone *)
Fixpoint Tleaked (me: Tmemory) (vars: accessible) : bool := 
  match vars with
  | [] => false
  | l::ls => match me l with
            (* secrets cannot stay on AppMem or nonzone EncMem *)
            | TAppMem (_, Secret) => true
            | TEncMem _ NonzoneMem (_, Secret) => true
            | _ => Tleaked me ls
            end
  end.

(* Inductive Texp: Type := *)
(*   | TExpLoc (l: Tlocation) *)
(*   | TExpVal (v: value) *)
(*   | TExpUnary (e: Texp) (op: value -> value) *)
(*   | TExpBinary (e1 e2: Texp) (op: value -> value -> value) *)
(* . *)

Fixpoint Texp_eval (t: ThreadId) (me: Tmemory) (mo: mode) (e: exp) : @result value := 
  match e with
  | ExpLoc l => match Taccess t me mo l with
                | Ok v => Ok (fst v)
                | Err e => Err e
                end
  | ExpVal v => Ok(v)
  | ExpUnary e _ => match Texp_eval t me mo e with
                    | Ok _ => Ok(Any)
                    | e => e
                    end
  | ExpBinary e1 e2 _ => let r1 := Texp_eval t me mo e1 in
                         let r2 := Texp_eval t me mo e2 in
                         match r1, r2 with
                         | Ok _, Ok _ => Ok(Any)
                         | Err er1, Err er2 => Err(er1 ++ er2)
                         | Err er1, Ok _ => Err(er1)
                         | Ok _, Err er2 => Err(er2)
                         end
  end.

Definition Texp_as_bool (t: ThreadId) (me: Tmemory) (mo: mode) (e: exp) : @result bool := 
  match Texp_eval t me mo e with
  | Ok v => Ok (value_as_bool v)
  | Err e => Err e
  end.


Fixpoint Texp_prop_tag (t: ThreadId) (me: Tmemory) (mo: mode) (e: exp) : security_tag := 
  match e with
  | ExpLoc l => match Taccess t me mo l with
                | Ok v => (snd v)
                | Err e => Nonsense
                end
  | ExpVal v => Notsecret
  | ExpUnary e _ => Texp_prop_tag t me mo e
  | ExpBinary e1 e2 _ =>  let t1 := Texp_prop_tag t me mo e1 in
                          let t2 := Texp_prop_tag t me mo e2 in
                          sum_two_tags t1 t2
  end.

Definition Texp_tagged_val (t: ThreadId) (me: Tmemory) (mo: mode) (e: exp) : @result tag_value := 
  match (Texp_eval t me mo e), (Texp_prop_tag t me mo e) with
  | Ok v, t => Ok (v, t)
  | Err ev, _ => Err ev
  end.

(* Inductive Tcom : Type := *)
(*   | TCNop *)
(*   | TCEenter *)
(*   | TCEexit *)
(*   | TCAsgn (l: Tlocation) (v: Texp) *)
(*   | TCSeq (c1 c2: Tcom) *)
(*   | TCIf (b: Texp) (c1 c2: Tcom) *)
(*   | TCWhile (b: Texp) (c: Tcom) *)
(*   (* Declasification *) *)
(* . *)

Definition Tstate: Type := Tmemory * mode * accessible * errors.

(* Add tid here *)
Inductive Tcom_eval_critical : ThreadId -> com -> Tstate -> Tstate -> Prop :=
  | TE_Nop (tid: ThreadId) (me: Tmemory) (mo: mode) (vars: accessible) (ers: errors) (ers: errors): 
    Tcom_eval_critical tid CNop (me, mo, vars, ers) (me, mo, vars, ers)
  | TE_Eenter (tid: ThreadId) (me: Tmemory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = []):
    Tcom_eval_critical tid CEenter (me, mo, vars, ers) (me, EnclaveMode, vars, ers)
  | TE_Eexit (tid: ThreadId) (me: Tmemory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = []):
    Tcom_eval_critical tid CEexit (me, mo, vars, ers) (me, NormalMode, vars, ers)
  | TE_Asgn_Ok_enc (tid: ThreadId) (me: Tmemory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = [])
    (l: location) (v: exp) (r: tag_value) 
    (Hexp: Texp_tagged_val tid me mo v = (Ok r)) (Henc: mo = EnclaveMode) 
    (* only assign correct tid! *):
    (* What if not in the enclave mode? *)
    (* Write restricted in the Zone! *)
    Tcom_eval_critical tid (CAsgn l v) (me, mo, vars, ers) ((Tupdate tid l (TEncMem tid ZoneMem r) me), mo, (l :: vars), ers)
  | TE_Asgn_Err_access (tid: ThreadId) (me: Tmemory) (mo: mode) (vars: accessible) (ers: errors) (Her: ers = [])
    (l: location) (v: exp) (er: errors) (Hexp: Texp_tagged_val tid me mo v = (Err er)):
    Tcom_eval_critical tid (CAsgn l v) (me, mo, vars, ers) (me, mo, vars, (er ++ ers))
  | TE_Seq (tid: ThreadId) (st st' st'': Tstate) (c1 c2: com)
    (Hc1: Tcom_eval_critical tid c1 st st') (Hc2: Tcom_eval_critical tid c2 st' st''):
    Tcom_eval_critical tid (CSeq c1 c2) st st''
  | TE_If_then (tid: ThreadId) (me: Tmemory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c1 c2: com) (st': Tstate):
    Texp_as_bool tid me mo b = Ok true -> 
    Tcom_eval_critical tid c1 (me, mo, vars, ers) st' -> 
    Tcom_eval_critical tid (CIf b c1 c2) (me, mo, vars, ers) st'
  | TE_If_else (tid: ThreadId) (me: Tmemory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c1 c2: com) (st': Tstate):
    Texp_as_bool tid me mo b = Ok false -> 
    Tcom_eval_critical tid c2 (me, mo, vars, ers) st' -> 
    Tcom_eval_critical tid (CIf b c1 c2) (me, mo, vars, ers) st'
  | TE_If_err (tid: ThreadId) (me: Tmemory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c1 c2: com) (st': Tstate) (er: errors):
    Texp_as_bool tid me mo b = Err er -> 
    Tcom_eval_critical tid (CIf b c1 c2) (me, mo, vars, ers) (me, mo, vars, er ++ ers)
  | TE_while_true (tid: ThreadId) (me: Tmemory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c: com) (st': Tstate):
    Texp_as_bool tid me mo b = Ok true -> 
    Tcom_eval_critical tid c (me, mo, vars, ers) st' -> 
    Tcom_eval_critical tid (CWhile b c) (me, mo, vars, ers) st'
  | TE_while_false (tid: ThreadId) (me: Tmemory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c: com) (st': state):
    Texp_as_bool tid  me mo b = Ok false -> 
    Tcom_eval_critical tid (CWhile b c) (me, mo, vars, ers) (me, mo, vars, ers)
  | TE_while_err (tid: ThreadId) (me: Tmemory) (mo: mode) (vars: list location) (ers: errors) (Her: ers = [])
    (b: exp) (c: com) (st': state) (er: errors):
    Texp_as_bool tid me mo b = Err er -> 
    Tcom_eval_critical tid (CWhile b c) (me, mo, vars, ers) (me, mo, vars, er ++ ers)
  | TE_Err_ignore (tid: ThreadId) (me: Tmemory) (mo: mode) (vars: accessible) (ers: errors) 
    (Herr: (length ers) >= 1) (c: com):
    Tcom_eval_critical tid c (me, mo, vars, ers) (me, mo, vars, ers)
.

(* Singlize the multi-threading state-related data structures *)
Definition singlize_Tcell (tid: ThreadId) (c: Tcell) : cell := 
  match c with
  | TDummyMem => DummyMem
  | TAppMem v => AppMem v
  | TUnusedMem => UnusedMem
  | TEncMem t z v
    => if (t =? tid) then EncMem z v else DummyMem
  end.

(* Fixpoint singlize_accessible (tid: ThreadId) (vars: accessible) : accessible :=  *)
(*   match vars with *)
(*   | [] => [] *)
(*   | h :: t => if (fst h =? tid) then (snd h) :: (singlize_accessible tid t) else (singlize_accessible tid t) *)
(*   end. *)

Fixpoint singlize_Tmemory (tid: ThreadId) (me: Tmemory) (vars: accessible) : memory := 
  match vars with
  | [] => empty_mem
  | h :: t => update h (singlize_Tcell tid (me h)) (singlize_Tmemory tid me t)
  end.

Lemma singlize_Tapp_app: forall me tid l v vars,
  In l vars ->
  me l = TAppMem v -> (singlize_Tmemory tid me vars) l = AppMem v.
Proof.
  intros. induction vars.
  - inversion H.
  - inversion H.
    + subst. unfold singlize_Tmemory. rewrite H0. simpl.
      rewrite eq_location_refl. reflexivity.
    + simpl. apply IHvars in H1.
      unfold update. unfold singlize_Tcell.
      destruct (me a) eqn: eqa; try destruct (eq_location l a) eqn: eqla;
        try assumption.
      * apply eq_location_eq in eqla. subst.
        assert (Ha: TAppMem v = TAppMem v0).
        { rewrite <- eqa. rewrite <- H0. reflexivity. }
        inversion Ha. reflexivity.
      * apply eq_location_eq in eqla. subst.
        rewrite H0 in eqa. inversion eqa.
      * apply eq_location_eq in eqla. subst.
        rewrite H0 in eqa. inversion eqa.
      * destruct (t =? tid) eqn: eqt.
        rewrite eqla. assumption. assumption.
Qed.

Lemma singlize_Tunused_unused: forall me tid l vars,
  In l vars ->
  me l = TUnusedMem -> (singlize_Tmemory tid me vars) l = UnusedMem.
Proof.
  intros. induction vars.
  - inversion H.
  - inversion H.
    + subst. unfold singlize_Tmemory. rewrite H0. simpl.
      rewrite eq_location_refl. reflexivity.
    + simpl. apply IHvars in H1.
      unfold update. unfold singlize_Tcell.
      destruct (me a) eqn: eqa; try destruct (eq_location l a) eqn: eqla;
        try assumption.
      * apply eq_location_eq in eqla. subst.
        rewrite H0 in eqa. inversion eqa.
      * reflexivity.
      * apply eq_location_eq in eqla. subst.
        rewrite H0 in eqa. inversion eqa.
      * destruct (t =? tid) eqn: eqt.
        rewrite eqla. assumption. assumption.
Qed.

Definition singlize_Tstate (tid: ThreadId) (st: Tstate) : state := 
  match st with
  | (me, mo, vars, ers) => ((singlize_Tmemory tid me vars), mo, vars, ers)
  end.

(* Fixpoint singlize_Texp (te: exp) : exp := *)
(*   match te with *)
(*   | TExpLoc l => ExpLoc (snd l) *)
(*   | TExpVal v => ExpVal v *)
(*   | TExpUnary e op => ExpUnary (singlize_Texp e) op *)
(*   | TExpBinary e1 e2 op => ExpBinary (singlize_Texp e1) (singlize_Texp e2) op *)
(*   end *)
(* . *)

(* Fixpoint singlize_Tcom (tc: Tcom) : com :=  *)
(*   match tc with *)
(*   | TCNop => CNop *)
(*   | TCEenter => CEenter *)
(*   | TCEexit => CEexit *)
(*   | TCAsgn l v => CAsgn (snd l) (singlize_Texp v) *)
(*   | TCSeq c1 c2 => CSeq (singlize_Tcom c1) (singlize_Tcom c2) *)
(*   | TCIf b c1 c2 => CIf (singlize_Texp b) (singlize_Tcom c1) (singlize_Tcom c2) *)
(*   | TCWhile b c => CWhile (singlize_Texp b) (singlize_Tcom c) *)
(*   end. *)

(* Lemma Texp_eval_singlize_err_prop: forall tid me mo vars v er, *)
(*   Texp_tagged_val tid me mo v = Err er ->  *)
(*   (exists er', exp_tagged_val (singlize_Tmemory tid me vars) mo v = Err er'). *)
(* Proof. *)
(*   intros. induction v; simpl. *)
(*   - destruct l. simpl in *.  *)
(*     unfold Texp_tagged_val in *. unfold Texp_eval in *. unfold Taccess in *. *)
(*     unfold exp_tagged_val. unfold exp_eval. unfold access. *)
(*     destruct mo eqn: mode. *)
(*     + destruct (me (t, l)) eqn: Hl; try inversion H. *)
(*     (* Need a lemma here! *) *)
(*       destruct (singlize_Tmemory tid me vars l) eqn: eql. admit. *)
(*       exists [Invalid]. reflexivity. exists [NoPriviledge]. reflexivity.  *)
(*       destruct (singlize_Tmemory tid me vars l) eqn: eql. admit. exists [Invalid]. reflexivity. *)
(*     exists [NoPriviledge]. reflexivity. *)
(*     + destruct (me (t, l)) eqn:eqt. inversion H. *)
(*       inversion H. assert (Ha: In (tid, l) vars). admit. *)
(*       apply singlize_Tunused_unused with (me:=me) in Ha. rewrite Ha. *)
(*       eauto. apply T_access_Unused_shared with (tid':= tid) in eqt. assumption. *)
(*       destruct (t0 =? t) eqn : eqtt0; simpl in *.  *)
(*       rewrite eqtt0 in H. rewrite eqt in H. inversion H. *)
(*       rewrite eqtt0 in H. admit. *)
(*   - unfold exp_tagged_val. admit. *)
(*   - admit. *)
(*   - admit. *)
(* Admitted. *)

(* TODO: bool exp transition! *)

Lemma singlized_update_inv: forall tid me l vars r,
    singlize_Tmemory tid (Tupdate tid l (TEncMem tid ZoneMem r) me) (l :: vars) =
    (update l (EncMem ZoneMem r) (singlize_Tmemory tid me  vars)).
Proof.
  intros.

Admitted.

Lemma eval_inv: forall tid me vars mo v r,
    Texp_tagged_val tid me mo v = Ok r ->
    exp_tagged_val (singlize_Tmemory tid me vars) mo v = Ok r.
Proof.
  intros. induction v; induction vars.
  - simpl in *. unfold Texp_tagged_val in H. unfold exp_tagged_val.
    unfold Texp_eval in H. unfold  exp_eval.
    unfold Taccess in H. unfold access.
    destruct mo eqn: eqmo. destruct (me l) eqn: eql.
    simpl in H. rewrite eql in H. simpl.
    induction v.
    + simpl. unfold Texp_tagged_val, exp_tagged_val.
      destruct ( exp_eval empty_mem mo (ExpLoc l)) eqn: eql;
      destruct ( Texp_eval tid me mo (ExpLoc l)) eqn: eqsl.
    
  induction v.

  Admitted.
  

Theorem singlize_exec: forall tid com st st', 
  Tcom_eval_critical tid com st st' -> com_eval_critical com (singlize_Tstate tid st) (singlize_Tstate tid st').
Proof.
  intros. induction H.
  (* Nop *)
  - simpl. apply E_Nop. assumption.
  (* Eenter *)
  - simpl. apply E_Eenter. assumption.
  (* Eexit *)
  - simpl. apply E_Eexit. assumption.
  (* Asgn *)
  - unfold singlize_Tstate. rewrite singlized_update_inv. apply E_Asgn_Ok_enc.
    assumption.
    inversion Hexp.
    unfold Texp_tagged_val. unfold exp_tagged_val.
    simpl. rewrite <- beq_nat_refl. rewrite eq_location_refl. simpl.
    rewrite <- beq_nat_refl. 
    
    * simpl in *. subst.
      rewrite <- beq_nat_refl with tid in *. rewrite eq_location_refl.
      simpl. rewrite <- beq_nat_refl with tid.
      remember (fun s' : location => if eq_location s' (Stack n) then TEncMem tid ZoneMem r else me s') as me'.
      assert (Ha: update (Stack n) (EncMem ZoneMem r) (singlize_Tmemory tid me' vars) = update (Stack n) (EncMem ZoneMem r) (singlize_Tmemory tid me vars)).
      { rewrite Heqme'. unfold update. induction vars.
        apply functional_extensionality. intros x.
        destruct (eq_location x (Stack n)) eqn: eqxn. reflexivity.
        simpl. reflexivity.
        apply functional_extensionality. intros.
        destruct (eq_location x (Stack n)) eqn: eqxn. reflexivity.
        simpl in *. unfold update. simpl.
        unfold singlize_Tcell.
        destruct (eq_location a (Stack n)) eqn: eqan.
        rewrite <- beq_nat_refl.
        apply eq_location_eq in eqan.
        rewrite <- eqan in eqxn.
        rewrite eqxn. destruct (me a) eqn: eqma.
        rewrite eqxn. apply functional_extensionality in IHvars.
        rewrite <- IHvars. assert (Ha': (singlize_Tmemory tid
    (fun s' : location => if eq_location s' (Stack n) then TEncMem tid ZoneMem r else me s')
    vars) =  singlize_Tmemory tid me vars).
        apply functional_extensionality. intros.  apply IHvars
        
        destruct (eq_location a (Stack n)) eqn: eqan.
        
          
      apply E_Asgn_Ok_enc.
      
  - apply E_Asgn_Err_access. assumption. 
  apply Texp_eval_singlize_err_prop in Hexp. admit.
  (* Seq *)
  - simpl. apply E_Seq with (st':= (singlize_Tstate tid st')). assumption. assumption.
  (* If *)
  - simpl. apply E_If_then. assumption. admit. assumption.
  - simpl. apply E_If_else. assumption. admit. assumption.
  - simpl. apply E_If_err. assumption. admit.
  (* While *)
  - simpl. apply E_while_true. assumption. admit. assumption.
  - simpl. apply E_while_false. assumption. admit.
  - simpl. apply E_while_err. assumption. admit.
  (* Err_ignore *)
  - simpl. apply E_Err_ignore. assumption.
Admitted.


