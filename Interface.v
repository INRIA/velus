Require Import lib.Integers.
Require Import lib.Floats.
Require Import Rustre.Common.

(* Interface avec CompCert *)
Inductive val'': Type :=
(* | Vundef: val'' *)
| Vint: Int.int -> val''
| Vfloat: float32 -> val''.

Inductive typ': Type :=
| Tbool
| Tvoid
| Tint
| Tfloat.

Inductive unary_op': Type :=
| Opposite
| Negation.

Inductive binary_op': Type :=
| Add
| Sub
| Mul
| Div.

Definition zero := Int.zero.
Definition one := Int.one.

Module Export Op <: OPERATORS.
  Definition val': Type := val''.
              
  Inductive val: Type :=
  | Vbool: bool -> val
  | Val: val' -> val.

  Definition Vzero := Val (Vint Int.zero).

  Definition typ := typ'.

  Definition typ_of_val (v: val): typ :=
    match v with
    | Vbool _ => Tbool
    | Val v =>
      match v with
      (* | Vundef => Tvoid *)
      | Vint _ => Tint
      | Vfloat _ => Tfloat
      end
    end.
    
  Definition unary_op := unary_op'.
  Definition binary_op := binary_op'.

  Definition opt (v: val'): option val := Some (Val v).
  
  Definition of_bool (b: bool): val' := Vint (if b then one else zero).

  Definition sem_val_unary (sem: val' -> typ -> option val) (v: val): typ -> option val :=
    match v with
    | Vbool b => sem (of_bool b)   
    | Val v => sem v
    end.
  
  Definition sem_opposite: val -> typ -> option val :=
    let sem v ty :=
        match v, ty with
        | Vint n, (Tint | Tbool) => opt (Vint (Int.neg n))
        | Vfloat f, Tfloat => opt (Vfloat (Float32.neg f))
        | _, _ => None
        end
    in sem_val_unary sem.
  
  Definition sem_negation: val -> typ -> option val :=
    let sem v ty :=
        match v, ty with
        | Vint n, (Tint | Tbool) => opt (of_bool (Int.eq n zero))
        | Vfloat f, Tfloat => opt (of_bool (Float32.cmp Ceq f Float32.zero))
        | _, _ => None
        end
    in sem_val_unary sem.
    
  Definition sem_unary (op: unary_op): val -> typ -> option val :=
    match op with
    | Opposite => sem_opposite 
    | Negation => sem_negation 
    end.

  Inductive classify_cast_cases :=
  | cast_case_neutral
  | cast_case_f2bool
  | cast_case_i2bool
  | cast_case_f2i
  | cast_case_f2f
  | cast_case_i2f
  | cast_case_void
  | cast_case_default.
  
  Definition classify_cast (tfrom tto: typ) : classify_cast_cases :=
    match tto, tfrom with
    | Tint, (Tint | Tbool) => cast_case_neutral
    | Tbool, Tfloat => cast_case_f2bool
    | Tbool, Tint => cast_case_i2bool
    | Tint, Tfloat => cast_case_f2i
    | Tfloat, Tfloat => cast_case_f2f
    | Tfloat, (Tint | Tbool) => cast_case_i2f 
    | Tvoid, _ => cast_case_void
    | _, _ => cast_case_default
    end.

  Definition sem_cast (v: val') (ty1 ty2: typ) : option val' :=
    match classify_cast ty1 ty2 with
    | cast_case_neutral =>
      match v with
      | Vint _ => Some v
      | _ => None
      end
    | cast_case_f2bool =>
      match v with
      | Vfloat f => Some (of_bool (Float32.cmp Ceq f Float32.zero))
      | _ => None
      end
    | cast_case_i2bool =>
      match v with
      | Vint i => Some (of_bool (Int.eq i Int.zero))
      | _ => None
      end
    | cast_case_f2i =>
      match v with
      | Vfloat f =>
        match Float32.to_int f with
        | Some i => Some (Vint i)
        | None => None
        end
      | _ => None
      end
    | cast_case_f2f =>
      match v with
      | Vfloat f => Some (Vfloat f)
      | _ => None
      end
    | cast_case_i2f =>
      match v with
      | Vint i => Some (Vfloat (Float32.of_int i))
      | _ => None
      end
    | cast_case_void => Some v
    | cast_case_default => None
    end.

  Definition binarith_type (ty1 ty2: typ) : typ :=
    match ty1, ty2 with
    | (Tint | Tbool), (Tint | Tbool) => Tint
    | Tfloat, Tfloat
    | (Tint | Tbool), Tfloat
    | Tfloat, (Tint | Tbool) => Tfloat
    | _, _ => Tvoid
    end.

  Definition sem_binarith
    (sem_int: int -> int -> option val)
    (sem_float: float32 -> float32 -> option val)
    (v1 v2: val') (ty1 ty2: typ): option val :=
    let ty := binarith_type ty1 ty2 in
    match sem_cast v1 ty1 ty with
    | None => None
    | Some v1' =>
      match sem_cast v2 ty2 ty with
      | None => None
      | Some v2' =>
        match ty with
        | Tint =>
          match v1', v2' with
          | Vint n1, Vint n2 => sem_int n1 n2
          | _, _ => None
          end
        | Tfloat =>
          match v1', v2' with
          | Vfloat f1, Vfloat f2 => sem_float f1 f2
          | _, _ => None
          end
        | bin_default => None
        end
      end
    end.
  
  Definition sem_val_binary (sem: val' -> val' -> typ -> typ -> option val) (v1 v2: val)
    : typ -> typ -> option val :=
    match v1, v2 with
    | Vbool b1, Vbool b2 => sem (of_bool b1) (of_bool b2)
    | Val v1, Vbool b2 => sem v1 (of_bool b2)
    | Vbool b1, Val v2 => sem (of_bool b1) v2
    | Val v1, Val v2 => sem v1 v2
    end.
  
  Definition sem_add: val -> val -> typ -> typ -> option val :=
    let sem_int n1 n2 := opt (Vint (Int.add n1 n2)) in
    let sem_float f1 f2 := opt (Vfloat (Float32.add f1 f2)) in
    sem_val_binary (sem_binarith sem_int sem_float).

  Definition sem_sub: val -> val -> typ -> typ -> option val :=
    let sem_int n1 n2 := opt (Vint (Int.sub n1 n2)) in
    let sem_float f1 f2 := opt (Vfloat (Float32.sub f1 f2)) in
    sem_val_binary (sem_binarith sem_int sem_float).

  Definition sem_mul: val -> val -> typ -> typ -> option val :=
    let sem_int n1 n2 := opt (Vint (Int.mul n1 n2)) in
    let sem_float f1 f2 := opt (Vfloat (Float32.mul f1 f2)) in
    sem_val_binary (sem_binarith sem_int sem_float).

  Definition sem_div: val -> val -> typ -> typ -> option val :=
    let sem_int n1 n2 :=
        if Int.eq n2 Int.zero
           || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
        then None else opt (Vint (Int.divs n1 n2))
    in
    let sem_float f1 f2 := opt (Vfloat (Float32.div f1 f2)) in
    sem_val_binary (sem_binarith sem_int sem_float).
  
  Definition sem_binary (op: binary_op) (v1: val) (ty1: typ) (v2: val) (ty2: typ): option val :=
    (match op with
    | Add => sem_add
    | Sub => sem_sub
    | Mul => sem_mul
    | Div => sem_div
    end) v1 v2 ty1 ty2.
    
  (* Lemma val_dec: forall v1 v2: val, {v1 = v2} + {v1 <> v2}. *)
  (* Proof. *)
  (*   decide equality. *)
  (*   apply Bool.bool_dec. *)
  (*   decide equality. *)
  (*   apply Int.eq_dec. *)
  (*   apply Float.eq_dec. *)
  (* Qed. *)

  Definition val_eqb (v1 v2: val): bool :=
    match v1, v2 with
    | Vbool b1, Vbool b2 => Bool.eqb b1 b2
    | Val v1, Val v2 =>
      match v1, v2 with
      (* | Vundef, Vundef => true *)
      | Vint n1, Vint n2 => Int.eq n1 n2
      | Vfloat f1, Vfloat f2 => if Float32.eq_dec f1 f2 then true else false
      | _, _ => false
      end
    | _, _ => false
    end.

  Definition typ_eqb (ty1 ty2: typ): bool :=
    match ty1, ty2 with
    | Tbool, Tbool
    | Tvoid, Tvoid
    | Tint, Tint
    | Tfloat, Tfloat => true
    | _, _ => false
    end.
  
  Lemma unop_dec: forall op1 op2: unary_op, {op1 = op2} + {op1 <> op2}.
  Proof. decide equality. Qed.
  Definition unop_eqb (op1 op2: unary_op) := if unop_dec op1 op2 then true else false.

  Lemma binop_dec: forall op1 op2: binary_op, {op1 = op2} + {op1 <> op2}.
  Proof. decide equality. Qed.
  Definition binop_eqb (op1 op2: binary_op) := if binop_dec op1 op2 then true else false.
  
  Theorem val_eqb_iff: forall v1 v2, val_eqb v1 v2 = true <-> v1 = v2.
  Proof.
    intros v1 v2; unfold val_eqb; destruct v1 as [b1|v1], v2 as [b2|v2];
    try destruct b1, b2; try destruct v1 as [n1|f1], v2 as [n2|f2];
    try intuition discriminate.
    - split; intro H.
      + pose proof (Int.eq_spec n1 n2) as Heq; rewrite H in Heq; now do 2 f_equal.
      + inversion H; apply Int.eq_true.
    - split; intro H.
      + destruct (Float32.eq_dec f1 f2).
        * now inversion e.
        * discriminate.
      + destruct (Float32.eq_dec f1 f2); auto.
        exfalso; apply n; now inversion H.
  Qed.

  Theorem typ_eqb_iff : forall t1 t2, typ_eqb t1 t2 = true <-> t1 = t2.
  Proof. intros ty1 ty2; destruct ty1, ty2; intuition discriminate. Qed.

  Theorem unop_eqb_iff: forall op1 op2, unop_eqb op1 op2 = true <-> op1 = op2.
  Proof. intros op1 op2; unfold unop_eqb; destruct (unop_dec op1 op2); intuition discriminate. Qed.
  
  Theorem binop_eqb_iff: forall op1 op2, binop_eqb op1 op2 = true <-> op1 = op2. 
  Proof. intros op1 op2; unfold binop_eqb; destruct (binop_dec op1 op2); intuition discriminate. Qed.
  
End Op.