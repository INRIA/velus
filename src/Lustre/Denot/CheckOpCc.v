From Velus Require Import Common.CommonTactics.
From Velus Require Import ObcToClight.Interface.

(** TEST : définitions de check_* avec les valeurs de CompCert *)

Lemma equiv_decb_spec :
  forall x y,
    EquivDec.equiv_decb x y = true -> x = y.
Proof.
  intros * He.
  cbv in He.
  cases.
Qed.


(* Définition concrète de check_unop *)

Definition check_unop (op : unop) (ty : type) : bool :=
  match op, ty with
  | UnaryOp Cop.Onotbool, Tprimitive _ => true
  | UnaryOp Cop.Onotint, (Tprimitive (Tint _ _ | Tlong _)) => true
  | UnaryOp Cop.Oneg, Tprimitive _ => true
  | UnaryOp Cop.Oabsfloat, Tprimitive _ => true
  | _, _ => false
  end.

Theorem check_unop_correct :
  forall op ty,
    check_unop op ty = true ->
    forall v, wt_value v ty ->
         sem_unop op v ty <> None.
Proof.
  unfold check_unop, sem_unop, option_map.
  unfold Cop.sem_unary_operation.
  intros * Hck v Hwt.
  destruct op as [[]|]; try congruence.
  - (* Onotbool *)
    unfold Cop.sem_notbool, Cop.bool_val, Cop.classify_bool; simpl.
    cases_eqn HH; subst; try congruence; inv Hwt.
    all: inv H1; simpl in *; try congruence; cases.
  - (* Onotint *)
    unfold Cop.sem_notint.
    cases_eqn HH; subst; try congruence; inv Hwt.
    all: inv H1; simpl in *; try congruence; cases.
  - (* Oneg *)
    unfold Cop.sem_neg.
    cases_eqn HH; subst; try congruence; inv Hwt.
    all: inv H1; simpl in *; try congruence; cases.
  - (* Oabsfloat *)
    unfold Cop.sem_absfloat.
    cases_eqn HH; subst; try congruence; inv Hwt.
    all: inv H1; simpl in *; try congruence; cases.
Qed.
