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
(* FIXME: devrait toujours fonctionner !! *)

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

(* une autre définition des type de Vélus *)
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

(* valeurs problématiques dans Vélus *)
Definition okval (v : Values.val) :=
  match v with
  | Values.Vundef
  | Values.Vptr _ _ => False
  | _ => True
  end.

Lemma classify_binarith_ok :
  forall t1 t2,
    okty t1 ->
    okty t2 ->
    Cop.classify_binarith t1 t2 <> Cop.bin_default.
Proof.
  unfold Cop.classify_binarith.
  intros * Ht1 Ht2 Hcl.
  inv Ht1; inv Ht2; simpl in *; cases.
Qed.

Lemma sem_cast1_ok :
  forall v1 t1 t2 m,
    okty t1 ->
    okty t2 ->
    okval v1 ->
    Ctyping.wt_val v1 t1 ->
    Cop.sem_cast v1 t1 (Cop.binarith_type (Cop.classify_binarith t1 t2)) m <> None.
Proof.
  unfold Cop.sem_cast, Cop.classify_binarith.
  intros * Ht1 Ht2 Hokv1 Hv1.
  inv Ht1; inv Ht2; inv Hv1.
  all: cases_eqn HH; subst.
  all: try congruence.
  all: simpl in *; cases_eqn HH; subst; try congruence.
Qed.

Lemma sem_cast2_ok :
  forall v2 t1 t2 m,
    okty t1 ->
    okty t2 ->
    okval v2 ->
    Ctyping.wt_val v2 t2 ->
    Cop.sem_cast v2 t2 (Cop.binarith_type (Cop.classify_binarith t1 t2)) m <> None.
Proof.
  unfold Cop.sem_cast, Cop.classify_binarith.
  intros * Ht1 Ht2 Hokv2 Hv2.
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
  intros * Hc Hv1.
  destruct t1, t2; simpl in *; inv Hc; auto.
  all: destruct v1, v2; auto; cases; congruence.
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
  Cop.sem_binarith sem_int sem_long sem_float sem_single v1 t1 v2 t2 m <> None.
Proof.
  intros * Hint Hlong Hfloat Hsingle Ht1 Ht2 Hv1 Hv2 Ok1 Ok2.
  (* (op & t3 & Hty). *)
  unfold Cop.sem_binarith.
  destruct (Cop.sem_cast v1 t1 (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:Hc1.
  2:{ eapply sem_cast1_ok in Hc1; eauto. }
  destruct (Cop.sem_cast v2 t2 (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:Hc2.
  2:{ eapply sem_cast2_ok in Hc2; eauto. }
  destruct (Cop.classify_binarith t1 t2) eqn:Hcb.
  5:{ eapply classify_binarith_ok in Hcb; eauto. }
  all: apply Ctyping.pres_sem_cast in Hc1 as Hv, Hc2 as Hv0; auto.
  all: simpl in Hv, Hv0.
  all: apply sem_cast_ok in Hc1 as Hok, Hc2 as Hok0.
  all: inv Hv; inv Hv0; simpl in *; auto.
Qed.

(* pour les opérations qui ne fonctionnent que sur les entiers *)
Lemma sem_binarith_ok' :
  forall sem_int sem_long sem_float sem_single v1 t1 v2 t2 m,
  (* (forall sg n1 n2, sem_int sg n1 n2 <> None) -> *)
  (* (forall sg n1 n2, sem_long sg n1 n2 <> None) -> *)
  (* (forall n1 n2, sem_float n1 n2 <> None) -> *)
  (* (forall n1 n2, sem_single n1 n2 <> None) -> *)
  (* okty t1 -> *)
  (* okty t2 -> *)
  Ctyping.wt_val v1 t1 ->
  Ctyping.wt_val v2 t2 ->
  okval v1 ->
  okval v2 ->
  match Cop.classify_binarith t1 t2 with
  | Cop.bin_case_i _ | Cop.bin_case_l _ =>
                         (forall sg n1 n2, sem_int sg n1 n2 <> None)
                         /\ (forall sg n1 n2, sem_long sg n1 n2 <> None)

  | Cop.bin_case_f | Cop.bin_case_s =>
                       (forall n1 n2, sem_float n1 n2 <> None)
                       /\ (forall n1 n2, sem_single n1 n2 <> None)
  | _ => False
  end ->
  Cop.sem_binarith sem_int sem_long sem_float sem_single v1 t1 v2 t2 m <> None.
Proof.
  intros * (* Hint Hlong *) (* Hfloat Hsingle *) (* Ht1 Ht2 *) Hv1 Hv2 Ok1 Ok2 Hop.
  (* (op & t3 & Hty). *)
  unfold Cop.sem_binarith.
  destruct (Cop.sem_cast v1 t1 (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:Hc1.
  2:{ eapply sem_cast1_ok in Hc1; eauto.
      destruct t1, t2; simpl in Hop; cases; try tauto; constructor.
      clear - Hop. destruct t1, t2; simpl in Hop; cases_eqn HH; subst; try tauto.
      all: constructor.
  }
  destruct (Cop.sem_cast v2 t2 (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:Hc2.
  2:{ eapply sem_cast2_ok in Hc2; eauto.
      destruct t1, t2; simpl in Hop; cases; try tauto; constructor.
      clear - Hop. destruct t1, t2; simpl in Hop; cases_eqn HH; subst; try tauto.
      all: constructor.
  }
  destruct (Cop.classify_binarith t1 t2) eqn:Hcb; try tauto; destruct Hop.
  all: apply Ctyping.pres_sem_cast in Hc1 as Hv, Hc2 as Hv0; auto.
  all: simpl in Hv, Hv0.
  all: apply sem_cast_ok in Hc1 as Hok, Hc2 as Hok0.
  all: inv Hv; inv Hv0; simpl in *; auto.
Qed.

(* FIXME: changer la signature de cette fonction car elle se fout des types *)
Definition check_binop_any (op : binop) (ty1 ty2 : type) : bool :=
  match op with
  | Cop.Odiv => false
  | Cop.Omod => false
  | Cop.Oshl => false
  | Cop.Oshr => false
  | _ => true
  end.

Lemma sem_binary_operation_ok :
  forall env op v1 t1 v2 t2 t3 m tyy,
    check_binop_any op tyy tyy = true ->
    Ctyping.type_binop op t1 t2 = Errors.OK t3 ->
    okty t1 ->
    okty t2 ->
    Ctyping.wt_val v1 t1 ->
    Ctyping.wt_val v2 t2 ->
    okval v1 ->
    okval v2 ->
    Cop.sem_binary_operation env op v1 t1 v2 t2 m <> None.

Proof.
  intros * Hcheck Hop Ht1 Ht2 Hv1 Hv2 Ok1 Ok2.
  unfold Cop.sem_binary_operation.
  destruct op; simpl in *; try congruence.
  { (* Oadd *)
    unfold Cop.sem_add.
    inv Ht1; inv Ht2; simpl.
    all: unfold Cop.classify_add, Ctypes.typeconv.
    all: cases_eqn HH; subst; try congruence.
    all: try apply sem_binarith_ok'; auto.
    simpl; split; intros; congruence.
    all: try (simpl; split; intros; congruence).
    all: simpl; cases_eqn HH.
    all: try (simpl; split; intros; congruence).
    all: simpl in *; congruence. }
  { (* Osub *)
    unfold Cop.sem_sub.
    inv Ht1; inv Ht2; simpl.
    all: unfold Cop.classify_sub, Ctypes.typeconv.
    all: cases_eqn HH; subst; try congruence.
    all: try apply sem_binarith_ok'; auto.
    all: try (simpl; split; intros; congruence).
    all: simpl; cases_eqn HH.
    all: try (simpl; split; intros; congruence).
  }
  { (* Omul *)
    unfold Cop.sem_mul.
    inv Ht1; inv Ht2; simpl.
    all: apply sem_binarith_ok'; auto.
    all: simpl; cases_eqn HH.
    all: try (simpl; split; intros; congruence).
  }
  3:{ (* Oxor *)
    apply sem_binarith_ok'; auto.
    inv Ht1; inv Ht2; simpl in *.
    all: cases_eqn HH; subst.
    all: cbn in Hop; try congruence.
    all: split; intros; congruence.
  }
(*   3:{ unfold Cop.sem_mul. *)
(*       eapply sem_binarith_ok; intros; eauto; try congruence. *)
(*       exists Cop.Omul. *)
(*       exists t3. *)
(*       now simpl. } *)
(*   - unfold Cop.sem_add. *)
(*     cases. *)
(*     5:{ eapply sem_binarith_ok; intros; eauto; try congruence. *)
(*         exists Cop.Oadd, t3. simpl. inv H0.  cases.  *)
(*   all: cases_eqn HH; subst. inv H0. *)
(*   destruct op eqn:Hop; simpl in *; try congruence. *)
(*   - unfold Cop.sem_add. *)
(*     cases. *)
(*     5:{ eapply sem_binarith_ok; intros; eauto; try congruence. *)
(*         exists op.   *)
(* Qed.int *)
Admitted.

(*   forall sem_int sem_long sem_float sem_single v1 t1 v2 t2 m, *)
(*   (forall sg n1 n2, sem_int sg n1 n2 <> None) -> *)
(*   (forall sg n1 n2, sem_long sg n1 n2 <> None) -> *)
(*   (forall n1 n2, sem_float n1 n2 <> None) -> *)
(*   (forall n1 n2, sem_single n1 n2 <> None) -> *)
(*   okty t1 -> *)
(*   okty t2 -> *)
(*   Ctyping.wt_val v1 t1 -> *)
(*   Ctyping.wt_val v2 t2 -> *)
(*   okval v1 -> *)
(*   okval v2 -> *)
(*   (exists op t3, Ctyping.type_binop op t1 t2 = Errors.OK t3) -> *)
(*   Cop.sem_binarith sem_int sem_long sem_float sem_single v1 t1 v2 t2 m <> None. *)
(* Proof. *)
(*   intros * Hint Hlong Hfloat Hsingle Ht1 Ht2 Hv1 Hv2 Ok1 Ok2 (op & t3 & Hty). *)
(*   unfold Cop.sem_binarith. *)


Definition okvalue (v : value) : Prop :=
  match v with
  | Vscalar v => okval v
  | Venum _ => True
  end.

(* Theorem check_binop_any_correct : *)
(*   forall op, *)
(*     check_binop_any op = true -> *)
(*   forall ty1 ty2, *)
(*     type_binop op ty1 ty2 <> None -> *)
(*   forall v1 v2, *)
(*     wt_value v1 ty1 -> *)
(*     wt_value v2 ty2 -> *)
(*     okvalue v1 -> *)
(*     okvalue v2 -> *)
(*     sem_binop op v1 ty1 v2 ty2 <> None. *)
(* Proof. *)
(*   intros ? Hop ?? Hty ?? Hv1 Hv2 Ok1 Ok2. *)
(*   unfold sem_binop. *)
(*   cases_eqn HH; subst; simpl in *; try congruence. *)
(*   all: cases_eqn HH; subst; try congruence. *)
(*   all: inv Hv1; inv Hv2. *)
(*   6-17: repeat rewrite ?Bool.andb_true_iff, ?Bool.andb_false_iff in *. *)
(*   6-17: (firstorder; congruence). *)
(*   2: admit. *)
(*   all: unfold option_map; cases_eqn HH; try congruence. *)
(* Qed. *)

Module OLDCHECK.

  (* Définition concrète de check_binop_any *)
Definition check_binop_any (op : binop) (ty1 ty2 : type) : bool :=
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
  intros * hty Hck v1 v2 Hwt1 Hwt2.
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

End OLDCHECK.

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
