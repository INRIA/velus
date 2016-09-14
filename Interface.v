Require Import lib.Integers.
Require Import lib.Floats.
Require Import Rustre.Common.

Require compcert.common.Values.
Require compcert.cfrontend.Cop.
Require compcert.cfrontend.Ctypes.
Require compcert.cfrontend.Ctyping.
Require compcert.common.Memory.
Require compcert.lib.Maps.

(* Interface avec CompCert *)

Definition empty_composite_env : Ctypes.composite_env := (Maps.PTree.empty _).

Module Export Op <: OPERATORS.
  Definition val: Type := Values.val.

  Inductive type' : Type :=
  | Tbool:  type'
  | Tint:   Ctypes.intsize -> Ctypes.signedness -> type'
  | Tlong:  Ctypes.signedness -> type'
  | Tfloat: Ctypes.floatsize -> type'.

  Definition type := type'.

  Definition cltype (ty: type) : Ctypes.type :=
    match ty with
    | Tbool      => Ctypes.type_bool
    | Tint sz sg => Ctypes.Tint sz sg Ctypes.noattr
    | Tlong sg   => Ctypes.Tlong sg Ctypes.noattr
    | Tfloat sz  => Ctypes.Tfloat sz Ctypes.noattr
    end.

  Definition typecl (ty: Ctypes.type) : option type :=
    match ty with
    | Ctypes.Tint sz sg (Ctypes.mk_attr false None) => Some (Tint sz sg)
    | Ctypes.Tlong sg   (Ctypes.mk_attr false None) => Some (Tlong sg)
    | Ctypes.Tfloat sz  (Ctypes.mk_attr false None) => Some (Tfloat sz)
    | _ => None
    end.
  
  Definition true_val := Values.Vtrue.
  Definition false_val := Values.Vfalse.

  Lemma true_not_false_val: true_val <> false_val.
  Proof. discriminate. Qed.

  Definition bool_type : type := Tbool.

  Inductive constant : Type :=
  | Cint: Integers.int -> Ctypes.intsize -> Ctypes.signedness -> constant
  | Clong: Integers.int64 -> Ctypes.signedness -> constant
  | Cfloat: Floats.float -> constant
  | Csingle: Floats.float32 -> constant.

  Definition const := constant.

  Definition type_const (c: const) : type :=
    match c with
    | Cint _ sz sg => Tint sz sg
    | Clong _ sg   => Tlong sg
    | Cfloat _     => Tfloat Ctypes.F64
    | Csingle _    => Tfloat Ctypes.F32
    end.

  Definition sem_const (c: const) : val :=
    match c with
    | Cint i _ _ => Values.Vint i
    | Clong i _  => Values.Vlong i
    | Cfloat f   => Values.Vfloat f
    | Csingle f  => Values.Vsingle f
    end.

  Inductive unary_op' : Type :=
  | UnaryOp: Cop.unary_operation -> unary_op'
  | CastOp:  type -> unary_op'.

  Definition unary_op := unary_op'.
  Definition binary_op := Cop.binary_operation.

  Definition sem_unary (uop: unary_op) (v: val) (ty: type) : option val :=
    match uop with
    | UnaryOp op => Cop.sem_unary_operation op v (cltype ty) Memory.Mem.empty
    | CastOp ty' => Cop.sem_cast v (cltype ty) (cltype ty') Memory.Mem.empty
    end.

  Definition sem_binary (op: binary_op)
             (v1: val) (ty1: type)
             (v2: val) (ty2: type) : option val :=
    Cop.sem_binary_operation
      empty_composite_env op v1 (cltype ty1) v2 (cltype ty2) Memory.Mem.empty.

  Definition type_unary (uop: unary_op) (ty: type) : option type :=
    match uop with
    | UnaryOp op => match Ctyping.type_unop op (cltype ty) with
                    | Errors.OK ty' => typecl ty'
                    | Errors.Error _ => None
                    end
    | CastOp ty' => match Ctyping.check_cast (cltype ty) (cltype ty') with
                    | Errors.OK _ => Some ty'
                    | Errors.Error _ => None
                    end
    end.

  Definition type_binary (op: binary_op) (ty1 ty2: type) : option type :=
    match Ctyping.type_binop op (cltype ty1) (cltype ty2) with
    | Errors.OK ty' => typecl ty'
    | Errors.Error _ => None
    end.

  Lemma val_dec   : forall v1 v2 : val, {v1 = v2} + {v1 <> v2}.
  Proof Values.Val.eq.

  Lemma type_dec   : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
  Proof.
    decide equality; (apply Ctyping.signedness_eq
                      || apply Ctyping.intsize_eq
                      || apply Ctyping.floatsize_eq).
  Qed.
  
  Lemma const_dec : forall c1 c2 : const, {c1 = c2} + {c1 <> c2}.
  Proof.
    decide equality; (apply Ctyping.signedness_eq
                      || apply Ctyping.intsize_eq
                      || apply Int.eq_dec
                      || apply Int64.eq_dec
                      || apply Float.eq_dec
                      || apply Float32.eq_dec).
  Qed.

  Lemma unop_dec  : forall op1 op2 : unary_op, {op1 = op2} + {op1 <> op2}.
  Proof.
    assert (forall (x y: Cop.unary_operation), {x=y} + {x<>y})
      by decide equality.
    decide equality.
    apply type_dec.
  Qed.

  Lemma binop_dec : forall op1 op2 : binary_op, {op1 = op2} + {op1 <> op2}.
  Proof.
    decide equality.
  Qed.
    
End Op.

