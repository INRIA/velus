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

  (* Wrong. TODO: Fix this. *)
  Definition typ_of_val (v: val): typ :=
    match v with
    (* | Vundef => Tvoid *)
    | Values.Vint _ => Ctypes.Tvoid
    | Values.Vfloat _ => Ctypes.Tvoid
    | _ => Ctypes.Tvoid
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
      
  Lemma unop_dec  : forall op1 op2 : unary_op, {op1 = op2} + {op1 <> op2}.
  Proof.
    decide equality.
  Qed.

  Lemma binop_dec : forall op1 op2 : binary_op, {op1 = op2} + {op1 <> op2}.
  Proof.
    decide equality.
  Qed.
    
End Op.