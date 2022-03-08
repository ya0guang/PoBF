Require Import Bool Arith List Lia List.

(* Execution mode *)
Inductive mode : Type := 
  | NormalMode
  | EnclaveMode 
.

(* Different types of memory regions *)

Inductive enc_mem_tag : Type :=
  | ZoneMem
  | NonzoneMem
.

Inductive value : Type :=
  | Concrete (v: nat) (* This may not be a nat here? *)
  | Any
.

Inductive accessible : Type :=
  | Some (v: value)
  | Uninit  (* uninitialized memory *)
  | Error (* priviledge error *)
.

Inductive mem: Type :=
  | AppMem (v: value)
  | UnusedMem
  | EncMem (z: enc_mem_tag) (v: value)
.

(* Memory and mappings *)

(* Do we really need locations? Maybe we just need variable names (identifiers)? *)
Definition location : Type := nat.

(* Convention: location 0 ~ 15 are for registers *)
Definition memory_mapping := location -> mem.

Definition empty_mem (l: location) : memory_mapping := 
  (fun _ => UnusedMem).

Definition take_mem (me: mem) (mo: mode) : accessible :=
  match me, mo with
  | UnusedMem, _ => Uninit
  | (EncMem _ _), NormalMode => Error
  | (EncMem _ v), EnclaveMode => Some v
  | AppMem v, _ => Some v
  end.

Definition update_mem (mm: memory_mapping) (l: location) (m: mem) : memory_mapping := 
  fun l' => if l =? l' then m else mm l.


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
Inductive instr : Type :=
  | nop
  | copy (ld: location) (ls: location) (* actually copy value ld <- ls *)
  | wirtev (l: location) (v: value)
  | unaryop (l: location) (op: nat -> nat)
  | binaryop (l1: location) (l2: location) (op: nat -> nat -> nat)
  | eexit
  | eenter
.

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


