Require Import lib.Integers.
Require Import Rustre.Common.
Require Import common.Smallstep.
Require Import common.Events.
Require Import common.Globalenvs.
Require Import common.Memory.
Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Minimp.Semantics.

(* Interface avec CompCert *)
Inductive val'' : Type :=
| Vundef : val''
| Vint : Int.int -> val''.

Inductive unary_op' : Type :=
| Opposite : unary_op'
| Negation : unary_op'.

Inductive binary_op' : Type :=
| Add : binary_op'
| Sub : binary_op'
| Mul : binary_op'.

Definition zero := Int.zero.
Definition one := Int.one.
Definition Vzero := Vint Int.zero.

Module Op <: OPERATORS.
  Definition val' := val''.
              
  Inductive val: Type :=
  | Vbool: bool -> val
  | Val: val' -> val.

  Definition typ := nat.
  
  Definition unary_op := unary_op'.
  Definition binary_op := binary_op'.

  Definition of_bool (b: bool) := Vint (if b then one else zero).

  Definition sem_val_unary (sem: val' -> option val) (v: val) :=
    match v with
    | Vbool b => sem (of_bool b)   
    | Val v => sem v
    end.

  Definition sem_val_binary (sem: val' -> val' -> option val) (v1 v2: val) :=
    match v1, v2 with
    | Vbool b1, Vbool b2 => sem (of_bool b1) (of_bool b2)
    | Val v1, Vbool b2 => sem v1 (of_bool b2)
    | Vbool b1, Val v2 => sem (of_bool b1) v2
    | Val v1, Val v2 => sem v1 v2
    end.
  
  Definition sem_opposite: val -> option val :=
    let sem v :=
        match v with
        | Vundef => None
        | Vint n => Some (Val (Vint (Int.neg n)))
        end
    in sem_val_unary sem.
  
  Definition sem_negation: val -> option val :=
    let sem v :=
        match v with
        | Vundef => None
        | Vint n => Some (Val (Vint (if (Int.eq n zero) then one else zero)))
        end
    in sem_val_unary sem.
    
  Definition sem_unary (op : unary_op): val -> option val :=
    match op with
    | Opposite => sem_opposite 
    | Negation => sem_negation 
    end.

  Definition sem_plus: val -> val -> option val :=
    let sem v1 v2 :=
        match v1, v2 with
        | Vint n1, Vint n2 => Some (Val (Vint (Int.add n1 n2)))
        | _, _ => None
        end
    in sem_val_binary sem.

  Definition sem_minus: val -> val -> option val :=
    let sem v1 v2 :=
        match v1, v2 with
        | Vint n1, Vint n2 => Some (Val (Vint (Int.sub n1 n2)))
        | _, _ => None
        end
    in sem_val_binary sem.

  Definition sem_mult: val -> val -> option val :=
    let sem v1 v2 :=
        match v1, v2 with
        | Vint n1, Vint n2 => Some (Val (Vint (Int.mul n1 n2)))
        | _, _ => None
        end
    in sem_val_binary sem.
  
  Definition sem_binary (op : binary_op): val -> val -> option val :=
    match op with
    | Add => sem_plus
    | Sub => sem_minus
    | Mul => sem_mult
    end.
    
  Lemma val_dec : forall v1 v2 : val, {v1 = v2} + {v1 <> v2}.
  Proof. decide equality; [apply Bool.bool_dec | decide equality; apply Int.eq_dec]. Qed.
  Definition val_eqb (v1 v2 : val) : bool :=
    match v1, v2 with
    | Vbool b1, Vbool b2 => Bool.eqb b1 b2
    | Val v1, Val v2 =>
      match v1, v2 with
      | Vundef, Vundef => true
      | Vint n1, Vint n2 => Int.eq n1 n2
      | _, _ => false
      end
    | _, _ => false
    end.

  Lemma unop_dec : forall op1 op2 : unary_op, {op1 = op2} + {op1 <> op2}.
  Proof. decide equality. Qed.
  Definition unop_eqb (op1 op2 : unary_op) := if unop_dec op1 op2 then true else false.

  Lemma binop_dec : forall op1 op2 : binary_op, {op1 = op2} + {op1 <> op2}.
  Proof. decide equality. Qed.
  Definition binop_eqb (op1 op2 : binary_op) := if binop_dec op1 op2 then true else false.
  
  Theorem val_eqb_true_iff : forall v1 v2, val_eqb v1 v2 = true <-> v1 = v2.
  Proof.
    intros v1 v2; unfold val_eqb; destruct v1 as [b1|v1], v2 as [b2|v2];
    try destruct b1, b2; try destruct v1 as [|n1], v2 as [|n2]; try intuition discriminate.
    split; intro H.
    - pose proof (Int.eq_spec n1 n2) as Heq; rewrite H in Heq; now do 2 f_equal.
    - inversion H; apply Int.eq_true.
  Qed.

  Theorem val_eqb_false_iff : forall v1 v2, val_eqb v1 v2 = false <-> v1 <> v2.
  Proof.
    intros v1 v2; unfold val_eqb; destruct v1 as [b1|v1], v2 as [b2|v2];
    try destruct b1, b2; try destruct v1 as [|n1], v2 as [|n2]; try intuition discriminate.
    split; intros H.
    - intro Hf; pose proof (Int.eq_spec n1 n2) as Hneq; rewrite H in Hneq; inversion Hf as [Heq]; contradiction. 
    - apply Int.eq_false; intro Heq; apply H; now do 2 f_equal.
  Qed.

  Theorem unop_eqb_true_iff : forall op1 op2, unop_eqb op1 op2 = true <-> op1 = op2.
  Proof. intros op1 op2; unfold unop_eqb; destruct (unop_dec op1 op2); intuition discriminate. Qed.
  
  Theorem unop_eqb_false_iff : forall op1 op2, unop_eqb op1 op2 = false <-> op1 <> op2.
  Proof. intros op1 op2; unfold unop_eqb; destruct (unop_dec op1 op2); intuition. Qed.

  Theorem binop_eqb_true_iff : forall op1 op2, binop_eqb op1 op2 = true <-> op1 = op2. 
  Proof. intros op1 op2; unfold binop_eqb; destruct (binop_dec op1 op2); intuition discriminate. Qed.
  
  Theorem binop_eqb_false_iff : forall op1 op2, binop_eqb op1 op2 = false <-> op1 <> op2. 
  Proof. intros op1 op2; unfold binop_eqb; destruct (binop_dec op1 op2); intuition. Qed.

End Op.

Module Import Syn := SyntaxFun Op.
Module Import Sem := SemanticsFun Op Syn.

Record fundeft := Fundeft {name: ident; body: stmt}.
Parameter vart: Type.
Parameter pub: program -> list ident.
Parameter def: program -> list (ident * AST.globdef fundeft vart).

Definition genv := Genv.t fundeft vart.
Inductive state :=
| State (H: heap) (S: stack) (s: stmt)
| StopState.
Parameter convert_prog: program -> AST.program fundeft vart.

Inductive step: genv -> state -> trace -> state -> Prop :=
| DoStep: forall prog ge H S s H' S' t,
    stmt_eval prog H S s (H', S') ->
    step ge (State H S s) t (State H' S' Skip)
| Stop: forall ge H S t,
    step ge (State H S Skip) t StopState.

Parameter convert_mem: mem -> heap * stack.
Inductive initial_state (ge : genv) (p: program): state -> Prop :=
  IniState: forall b f m0 H0 S0,
    let p' := convert_prog p in
    Genv.init_mem p' = Some m0 ->
    Genv.find_symbol ge p'.(AST.prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    convert_mem m0 = (H0, S0) ->
    initial_state ge p (State H0 S0 f.(body)).

Inductive final_state: state -> int -> Prop :=
  FinalState: final_state StopState zero.

Definition globalenv (p: program) :=
  Genv.globalenv (convert_prog p).

Definition semantics (p: program) :=
  let ge := globalenv p in
  Semantics_gen step (initial_state ge p) final_state ge ge.