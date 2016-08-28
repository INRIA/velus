Require Import lib.Integers.
Require Import lib.Floats.
Require Import Rustre.Common.

Require compcert.common.Values.
Require compcert.cfrontend.Cop.
Require compcert.cfrontend.Ctypes.
Require compcert.common.Memory.
Require compcert.lib.Maps.

(* Interface avec CompCert *)

Definition empty_composite_env : Ctypes.composite_env := (Maps.PTree.empty _).

Module Export Op <: OPERATORS.
  Definition val: Type := Values.val.

  (* TODO: wrong! Fix. *)
  Definition typ := Ctypes.type.

  Definition true_val := Values.Vtrue.
  Definition false_val := Values.Vfalse.

  Lemma true_not_false_val: true_val <> false_val.
  Proof. discriminate. Qed.

  Definition bool_typ := Ctypes.type_bool.

  Inductive constant : Type :=
  | Cint: Integers.int -> Ctypes.intsize -> Ctypes.signedness -> constant
  | Clong: Integers.int64 -> Ctypes.signedness -> constant
  | Cfloat: Floats.float -> constant
  | Csingle: Floats.float32 -> constant.

  Definition const := constant.

  Definition typ_const (c: const) : typ :=
    match c with
    | Cint _ sz sg => Ctypes.Tint sz sg Ctypes.noattr
    | Clong _ sg   => Ctypes.Tlong sg Ctypes.noattr
    | Cfloat _     => Ctypes.Tfloat Ctypes.F64 Ctypes.noattr
    | Csingle _    => Ctypes.Tfloat Ctypes.F32 Ctypes.noattr
    end.

  Definition sem_const (c: const) : val :=
    match c with
    | Cint i _ _ => Values.Vint i
    | Clong i _  => Values.Vlong i
    | Cfloat f   => Values.Vfloat f
    | Csingle f  => Values.Vsingle f
    end.

  Definition unary_op := Cop.unary_operation.
  Definition binary_op := Cop.binary_operation.

  Definition sem_unary (op: unary_op) (v: val) (ty: typ) : option val :=
    Cop.sem_unary_operation op v ty Memory.Mem.empty.

  Definition sem_binary (op: binary_op)
             (v1: val) (ty1: typ)
             (v2: val) (ty2: typ) : option val :=
    Cop.sem_binary_operation
      empty_composite_env op v1 ty1 v2 ty2 Memory.Mem.empty.

  Lemma val_dec   : forall v1 v2 : val, {v1 = v2} + {v1 <> v2}.
  Proof Values.Val.eq.

  Lemma typ_dec   : forall t1 t2 : typ, {t1 = t2} + {t1 <> t2}.
  Proof Ctypes.type_eq.
  
  Lemma const_dec : forall c1 c2 : const, {c1 = c2} + {c1 <> c2}.
  Proof.
    assert (forall (x y: Ctypes.intsize), {x=y} + {x<>y}) by decide equality.
    assert (forall (x y: Ctypes.signedness), {x=y} + {x<>y}) by decide equality.
    decide equality.
    apply Int.eq_dec.
    apply Int64.eq_dec.
    apply Float.eq_dec.
    apply Float32.eq_dec.
  Qed.
      
  Lemma unop_dec  : forall op1 op2 : unary_op, {op1 = op2} + {op1 <> op2}.
  Proof.
    decide equality.
  Qed.

  Lemma binop_dec : forall op1 op2 : binary_op, {op1 = op2} + {op1 <> op2}.
  Proof.
    decide equality.
  Qed.
    
End Op.