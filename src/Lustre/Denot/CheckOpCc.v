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

(* Import BinInt. *)
(* Check (Values.Vint (Integers.Int.repr (5%Z))). *)


Import String.

Inductive okty : Ctypes.type -> Prop :=
| OkInt : forall sz sg attr, okty (Ctypes.Tint sz sg attr)
| OkLong : forall sg attr, okty (Ctypes.Tlong sg attr)
| OkLFloat : forall sz attr, okty (Ctypes.Tfloat sz attr)
.

Lemma typecl_okty : forall ty, okty ty <-> typecl ty <> None.
Proof.
  split; intro H.
  inv H; simpl; congruence.
  destruct ty; simpl in *; try congruence; constructor.
Qed.

Lemma classify_binarith_ok :
  forall t1 t2 op t3,
    okty t1 ->
    okty t2 ->
    (* okty t3 -> *)
    Ctyping.type_binop op t1 t2 = Errors.OK t3 ->
    Cop.classify_binarith t1 t2 <> Cop.bin_default.
Proof.
  unfold Cop.classify_binarith.
  intros * Ht1 Ht2 (* Ht3 *) Hop Hcl.
  inv Ht1; inv Ht2; (* inv Ht3; *) simpl in *; cases.
Qed.

Definition okval (v : Values.val) :=
  match v with
  | Values.Vundef
  | Values.Vptr _ _ => False
  | _ => True
  end.

Lemma sem_cast1_ok :
  forall v1 t1 t2 m op t3,
    okty t1 ->
    okty t2 ->
    (* okty t3 -> *)
    Ctyping.type_binop op t1 t2 = Errors.OK t3 ->
    okval v1 ->
    Ctyping.wt_val v1 t1 ->
    Cop.sem_cast v1 t1 (Cop.binarith_type (Cop.classify_binarith t1 t2)) m <> None.
Proof.
  unfold Cop.sem_cast, Cop.classify_binarith.
  intros * Ht1 Ht2 (* Ht3 *) Hop Hokv1 Hv1.
  inv Ht1; inv Ht2; inv Hv1.
  all: cases_eqn HH; subst.
  all: try congruence.
  all: simpl in *; cases_eqn HH; subst; try congruence.
Qed.

Lemma sem_cast2_ok :
  forall v2 t1 t2 m op t3,
    okty t1 ->
    okty t2 ->
    (* okty t3 -> *)
    Ctyping.type_binop op t1 t2 = Errors.OK t3 ->
    okval v2 ->
    Ctyping.wt_val v2 t2 ->
    Cop.sem_cast v2 t2 (Cop.binarith_type (Cop.classify_binarith t1 t2)) m <> None.
Proof.
  unfold Cop.sem_cast, Cop.classify_binarith.
  intros * Ht1 Ht2 (* Ht3 *) Hop Hokv2 Hv2.
  inv Ht1; inv Ht2; inv Hv2.
  all: cases_eqn HH; subst.
  all: try congruence.
  all: simpl in *; cases_eqn HH; subst; try congruence.
Qed.

Lemma sem_cast_ok :
  forall v1 v2 t1 t2 m,
    Cop.sem_cast v1 t1 t2 m = Some v2 ->
    okval v1 ->
    okval v2.
Proof.
  unfold Cop.sem_cast, okval.
  intros * Hc Hv.
  destruct t1, t2; simpl in *; inv Hc; auto.
  all: cases.
  
Qed.


Lemma sem_binarith_ok :
  forall sem_int sem_long sem_float sem_single v1 t1 v2 t2 m,
  (forall sg n1 n2, sem_int sg n1 n2 <> None) ->
  (forall sg n1 n2, sem_long sg n1 n2 <> None) ->
  (forall n1 n2, sem_float n1 n2 <> None) ->
  (forall n1 n2, sem_single n1 n2 <> None) ->
  okty t1 ->
  okty t2 ->
  Ctyping.wt_val v1 t1 ->
  Ctyping.wt_val v2 t2 ->
  okval v1 ->
  okval v2 ->
  (exists op t3, Ctyping.type_binop op t1 t2 = Errors.OK t3) ->
  Cop.sem_binarith sem_int sem_long sem_float sem_single v1 t1 v2 t2 m <> None.
Proof.
  intros * Hint Hlong Hfloat Hsingle Ht1 Ht2 Hv1 Hv2 Ok1 Ok2 (op & t3 & Hty).
  unfold Cop.sem_binarith.
  destruct (Cop.sem_cast v1 t1 (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:Hc1.
  2:{ eapply sem_cast1_ok in Hc1; eauto. }
  destruct (Cop.sem_cast v2 t2 (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:Hc2.
  2:{ eapply sem_cast2_ok in Hc2; eauto. }
  destruct (Cop.classify_binarith t1 t2) eqn:Hcb.
  5:{ eapply classify_binarith_ok in Hcb; eauto. }
  all: apply Ctyping.pres_sem_cast in Hc1 as Hv, Hc2 as Hv0; auto.
  all: simpl in Hv, Hv0.
  inv Hv, Hv0.

  
  all: inv Hv; inv Hv0; auto.
  all: destruct v1, v2; simpl in *; try congruence.
  all: inv Hv1; inv Hv2.
  all: destruct v, v0; eauto.
  Search  Cop.sem_cast.
Qed.


Definition check_binop_any (op : binop) : bool :=
  match op with
  | Cop.Odiv => false
  | Cop.Omod => false
  (* | Cop.Oshl => false *)
  (* | Cop.Oshr => false *)
  | _ => true
  end.

Theorem check_binop_any_correct :
  forall op,
    check_binop_any op = true ->
  forall ty1 ty2,
    type_binop op ty1 ty2 <> None ->
  forall v1 v2,
    wt_value v1 ty1 ->
    wt_value v2 ty2 ->
    sem_binop op v1 ty1 v2 ty2 <> None.
Proof.
  intros ? Hop ?? Hty ?? Hv1 Hv2.
  
Qed.

(* Définition concrète de check_binop_any *)
Definition check_binop_any (op : binop) (ty1 ty2 : type) : bool :=
  match op, ty1, ty2 with
  | Cop.Oadd, Tprimitive ty1, Tprimitive ty2 =>
      match Cop.classify_add (cltype ty1) (cltype ty2) with
      | Cop.add_default => 
      | _ => true
      end
      (* | Cop.Oadd, Tprimitive ty1, Tprimitive ty2 => *)
  (*     match Cop.classify_add (cltype ty1) (cltype ty2) with Cop.add_default => false | _ => true end *)
  (* | Cop.Osub, Tprimitive ty1, Tprimitive ty2 => *)
  (*     match Cop.classify_sub (cltype ty1) (cltype ty2) with Cop.sub_default => false | _ => true end *)
  (* (* (* mul général semble impossible ? à cause d'un cast_float_int qui peut échouer selon une valeur *) *) *)
  (* | Cop.Omul, Tprimitive (Tint _ _ | Tlong  _), Tprimitive (Tint _ _ | Tlong _) => *)
  (*     true *)
  (* | Cop.Omul, Tprimitive (Tfloat _), Tprimitive (Tfloat _) => *)
  (*     true *)
  (* | Cop.Odiv, Tprimitive (Tfloat _), Tprimitive (Tfloat _) => *)
  (*     true *)
  (* (* idem : impossible *) *)
  (* | Cop.Odiv, _, _ => *)
  (*     false *)
  (* (* idem : impossible *) *)
  (* | Cop.Omod, Tprimitive ty1, Tprimitive ty2 => *)
  (*     false *)
  (* (* | Oand : binary_operation             (**r bitwise and ([&]) *) *) *)
  (* (* | Oor : binary_operation              (**r bitwise or ([|]) *) *) *)
  (* (* | Oxor : binary_operation             (**r bitwise xor ([^]) *) *) *)
  (* (* | Oshl : binary_operation             (**r left shift ([<<]) *) *) *)
  (* (* | Oshr : binary_operation             (**r right shift ([>>]) *) *) *)
  (* | Cop.Oeq, Tprimitive ty1, Tprimitive ty2 => *)
  (*     match Cop.classify_cmp (cltype ty1) (cltype ty2) with Cop.cmp_default => false | _ => true end *)
  (* | Cop.One, Tprimitive ty1, Tprimitive ty2 => *)
  (*     match Cop.classify_cmp (cltype ty1) (cltype ty2) with Cop.cmp_default => false | _ => true end *)
  (* | Cop.Olt, Tprimitive ty1, Tprimitive ty2 => *)
  (*     match Cop.classify_cmp (cltype ty1) (cltype ty2) with Cop.cmp_default => false | _ => true end *)
  (* | Cop.Ogt, Tprimitive ty1, Tprimitive ty2 => *)
  (*     match Cop.classify_cmp (cltype ty1) (cltype ty2) with Cop.cmp_default => false | _ => true end *)
  (* | Cop.Ole, Tprimitive ty1, Tprimitive ty2 => *)
  (*     match Cop.classify_cmp (cltype ty1) (cltype ty2) with Cop.cmp_default => false | _ => true end *)
  (* | Cop.Oge, Tprimitive ty1, Tprimitive ty2 => *)
  (*     match Cop.classify_cmp (cltype ty1) (cltype ty2) with Cop.cmp_default => false | _ => true end *)
  | _, _, _ => false
  end.

Theorem check_binop_any_correct :
  forall op ty1 ty2,
    type_binop op ty1 ty2 <> None ->
    check_binop_any op ty1 ty2 = true ->
    forall v1 v2, wt_value v1 ty1 ->
             wt_value v2 ty2 ->
             sem_binop op v1 ty1 v2 ty2 <> None.
Proof.
  unfold check_binop_any, sem_binop, option_map.
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


(* Définition concrète de check_binop_val (v2 = valeur du membre droit) *)
Definition check_binop_val (op : binop) (ty1 : type) (v2 : value) (ty2 : type) : bool :=
  match op, ty1, v2, ty2 with
  | Cop.Odiv, Tprimitive (Tint Ctypes.I32 _), Vscalar (Values.Vint n), Tprimitive (Tint Ctypes.I32 _) =>
      negb (Integers.Int.eq n Integers.Int.zero)
      && negb (Integers.Int.eq n Integers.Int.mone)
  | _, _, _, _ => false
  end.

(* Require Import String. (* pour type_binop *) *)

Theorem check_binop_val_correct :
  forall op ty1 v2 ty2,
    (* type_binop op ty1 ty2 <> None -> (* si besoin, l'ajouter à op_correct ?? *) *)
    check_binop_val op ty1 v2 ty2 = true ->
    forall v1, wt_value v1 ty1 ->
          wt_value v2 ty2 ->
          sem_binop op v1 ty1 v2 ty2 <> None.
Proof.
  unfold type_binop, check_binop_val, sem_binop, option_map.
  unfold Cop.sem_binary_operation.
  intros * Hck (* Hwt *) v1 Hwt1 Hwt2.
  destruct op; try congruence.
  - (* Odiv *)
    cases_eqn HH; subst; simpl in *; try congruence; inv Hwt1; inv Hwt2.
    inv H1; inv H2.
    rewrite Bool.andb_true_iff, 2 Bool.negb_true_iff in Hck.
    destruct Hck.
    revert HH9.
    unfold Cop.sem_div, Cop.sem_binarith, Cop.sem_cast, Cop.classify_cast.
    simpl; cases_eqn HH; subst; try congruence.
    all: inv HH; inv HH0; simpl in *; try congruence.
    rewrite Bool.orb_true_iff, Bool.andb_true_iff in *.
    firstorder; congruence.
Qed.
