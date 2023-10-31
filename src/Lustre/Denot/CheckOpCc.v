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

Module TEST1CC.

(* Définition concrète de check_unop *)

Definition check_unop (op : unop) (ty : type) : bool :=
  match op, ty with
  | UnaryOp Cop.Onotbool, Tprimitive _ => true
  (* | UnaryOp Cop.Onotint, (Tprimitive (Tint _ _ | Tlong _)) => true *)
  | UnaryOp Cop.Onotint, Tprimitive ty =>
      match Cop.classify_notint (cltype ty) with Cop.notint_default => false | _ => true end
  | UnaryOp Cop.Oneg, Tprimitive _ => true
  (* | UnaryOp Cop.Oneg, Tenum t _ => EquivDec.equiv_decb  t  Ident.Ids.bool_id *)
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


(* Définition concrète de check_binop *)
Definition check_binop (op : binop) (ty1 ty2 : type) : bool :=
  match op, ty1, ty2 with
  | Cop.Oadd, Tprimitive ty1, Tprimitive ty2 =>
      match Cop.classify_add (cltype ty1) (cltype ty2) with Cop.add_default => false | _ => true end
  | Cop.Osub, Tprimitive ty1, Tprimitive ty2 =>
      match Cop.classify_sub (cltype ty1) (cltype ty2) with Cop.sub_default => false | _ => true end
  (* (* mul général semble impossible ? à cause d'un cast_float_int qui peut échouer selon une valeur *) *)
  | Cop.Omul, Tprimitive (Tint _ _ | Tlong  _), Tprimitive (Tint _ _ | Tlong _) =>
      true
  | Cop.Omul, Tprimitive (Tfloat _), Tprimitive (Tfloat _) =>
      true
  | Cop.Odiv, Tprimitive (Tfloat _), Tprimitive (Tfloat _) =>
      true
  (* idem : impossible *)
  | Cop.Odiv, _, _ =>
      false
  (* idem : impossible *)
  | Cop.Omod, Tprimitive ty1, Tprimitive ty2 =>
      false
  (* | Oand : binary_operation             (**r bitwise and ([&]) *) *)
  (* | Oor : binary_operation              (**r bitwise or ([|]) *) *)
  (* | Oxor : binary_operation             (**r bitwise xor ([^]) *) *)
  (* | Oshl : binary_operation             (**r left shift ([<<]) *) *)
  (* | Oshr : binary_operation             (**r right shift ([>>]) *) *)
  | Cop.Oeq, Tprimitive ty1, Tprimitive ty2 =>
      match Cop.classify_cmp (cltype ty1) (cltype ty2) with Cop.cmp_default => false | _ => true end
  | Cop.One, Tprimitive ty1, Tprimitive ty2 =>
      match Cop.classify_cmp (cltype ty1) (cltype ty2) with Cop.cmp_default => false | _ => true end
  | Cop.Olt, Tprimitive ty1, Tprimitive ty2 =>
      match Cop.classify_cmp (cltype ty1) (cltype ty2) with Cop.cmp_default => false | _ => true end
  | Cop.Ogt, Tprimitive ty1, Tprimitive ty2 =>
      match Cop.classify_cmp (cltype ty1) (cltype ty2) with Cop.cmp_default => false | _ => true end
  | Cop.Ole, Tprimitive ty1, Tprimitive ty2 =>
      match Cop.classify_cmp (cltype ty1) (cltype ty2) with Cop.cmp_default => false | _ => true end
  | Cop.Oge, Tprimitive ty1, Tprimitive ty2 =>
      match Cop.classify_cmp (cltype ty1) (cltype ty2) with Cop.cmp_default => false | _ => true end
  | _, _, _ => false
  end.

Theorem check_binop_correct :
  forall op ty1 ty2,
    check_binop op ty1 ty2 = true ->
    forall v1 v2, wt_value v1 ty1 ->
             wt_value v2 ty2 ->
             sem_binop op v1 ty1 v2 ty2 <> None.
Proof.
  unfold check_binop, sem_binop, option_map.
  unfold Cop.sem_binary_operation.
  intros * Hck v1 v2 Hwt1 Hwt2.
  destruct op; try congruence.
  - (* Oadd *)
    revert Hck.
    unfold Cop.classify_add; intros.
    cases_eqn HH; subst; try congruence; inv Hwt1; inv Hwt2.
    all: simpl in *; try congruence.
    all: inv H1; inv H2; simpl in *; try congruence; cases.
  - (* Osub *)
    revert Hck.
    unfold Cop.classify_sub; intros.
    cases_eqn HH; subst; try congruence; inv Hwt1; inv Hwt2.
    all: simpl in *; try congruence.
    all: inv H1; inv H2; simpl in *; try congruence; cases.
  - (* Omul *)
    cases_eqn HH; subst; simpl in *; try congruence; inv Hwt1; inv Hwt2.
    { inv H1; inv H2.
      revert HH6.
      unfold Cop.sem_mul, Cop.sem_binarith, Cop.sem_cast, Cop.classify_cast.
      simpl; cases_eqn HH; subst; congruence. }
    { inv H1; inv H2.
      revert HH6.
      unfold Cop.sem_mul, Cop.sem_binarith, Cop.sem_cast, Cop.classify_cast.
      simpl; cases_eqn HH; subst; congruence. }
    { inv H1; inv H2.
      revert HH6.
      unfold Cop.sem_mul, Cop.sem_binarith, Cop.sem_cast, Cop.classify_cast.
      simpl; cases_eqn HH; subst; congruence. }
    { inv H1; inv H2.
      revert HH6.
      unfold Cop.sem_mul, Cop.sem_binarith, Cop.sem_cast, Cop.classify_cast.
      simpl; cases_eqn HH; subst; congruence. }
    { inv H1; inv H2.
      all: revert HH6.
      all: unfold Cop.sem_mul, Cop.sem_binarith, Cop.sem_cast, Cop.classify_cast.
      all: simpl; cases_eqn HH; subst; congruence. }
  - (* Odiv flottants *)
    cases_eqn HH; subst; simpl in *; try congruence; inv Hwt1; inv Hwt2.
    { inv H1; inv H2.
      all: revert HH6.
      all: unfold Cop.sem_div, Cop.sem_binarith, Cop.sem_cast, Cop.classify_cast.
      all: simpl; cases_eqn HH; subst; congruence. }
  - (* Omod *)
    cases.
  - (* Oeq *)
    revert Hck.
    unfold Cop.classify_cmp; intros.
    cases_eqn HH; subst; try congruence; inv Hwt1; inv Hwt2.
    all: simpl in *; try congruence.
    all: inv H1; inv H2; simpl in *; try congruence; cases.
  - (* One *)
    revert Hck.
    unfold Cop.classify_cmp; intros.
    cases_eqn HH; subst; try congruence; inv Hwt1; inv Hwt2.
    all: simpl in *; try congruence.
    all: inv H1; inv H2; simpl in *; try congruence; cases.
  - (* Olt *)
    revert Hck.
    unfold Cop.classify_cmp; intros.
    cases_eqn HH; subst; try congruence; inv Hwt1; inv Hwt2.
    all: simpl in *; try congruence.
    all: inv H1; inv H2; simpl in *; try congruence; cases.
  - (* Ogt *)
    revert Hck.
    unfold Cop.classify_cmp; intros.
    cases_eqn HH; subst; try congruence; inv Hwt1; inv Hwt2.
    all: simpl in *; try congruence.
    all: inv H1; inv H2; simpl in *; try congruence; cases.
  - (* Ole *)
    revert Hck.
    unfold Cop.classify_cmp; intros.
    cases_eqn HH; subst; try congruence; inv Hwt1; inv Hwt2.
    all: simpl in *; try congruence.
    all: inv H1; inv H2; simpl in *; try congruence; cases.
  - (* Oge *)
    revert Hck.
    unfold Cop.classify_cmp; intros.
    cases_eqn HH; subst; try congruence; inv Hwt1; inv Hwt2.
    all: simpl in *; try congruence.
    all: inv H1; inv H2; simpl in *; try congruence; cases.
Qed.

End TEST1CC.
