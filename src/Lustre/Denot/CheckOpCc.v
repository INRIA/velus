Require Import Lia.
From Velus Require Import Common.CommonTactics.
From Velus Require Import ObcToClight.Interface.

Import String.

(** * Concrete definitions of [check_unop], [check_binop_any]
 * and [check_binop_val], instantiated with CompCert's operators *)

(** * /!\ this file is no longer in use !
 * the definitions moved to [ObcToClight/Interface.v] *)

(** Concrete definition of [check_unop].
 * We only prohibit cast operations from floats to integers, which can fail
 * on some values. More precisely, all of
 *      Float.to_int, Float.to_intu, Float.to_long, Float.to_longu
 * triggers the operation [ZofB_range f zmin zmax] that can return None if either
 * - f is infinite or NaN
 * - ZofB f < zmin
 * - ZofB f > zmax
 *)
Definition check_unop (op : unop) (ty : type) : bool :=
  match op, ty with
  | CastOp t2, Tprimitive t1 =>
      match Cop.classify_cast (cltype t1) (cltype t2) with
      | Cop.cast_case_f2i _ _
      | Cop.cast_case_s2i _ _
      | Cop.cast_case_f2l _
      | Cop.cast_case_s2l _ => false
      | _ => true
      end
  | _, _ => true
  end.

Lemma sem_cast_ok :
  forall v t1 t2 r m,
    wt_cvalue v t1 ->
    check_unop (CastOp t2) (Tprimitive t1) = true ->
    Ctyping.check_cast (cltype t1) (cltype t2) = Errors.OK r ->
    Cop.sem_cast v (cltype t1) (cltype t2) m <> None.
Proof.
  intros * Hwt Hck Ht.
  unfold Cop.sem_cast, Ctyping.check_cast in *.
  destruct t1,t2; inv Hwt.
  all: simpl in *; try congruence.
  all: cases_eqn HH; congruence.
Qed.

Lemma unary_operation_ok :
  forall op ty ty' v m,
    Ctyping.type_unop op (cltype ty) = Errors.OK ty' ->
    wt_cvalue v ty ->
    Cop.sem_unary_operation op v (cltype ty) m <> None.
Proof.
  intros * Hok Hwt.
  destruct op; simpl in *; cases_eqn HH; subst; simpl in *.
  all: inv Hwt; simpl in *; cbn; try congruence.
  all: cases_eqn HH; subst; cbn; try congruence.
  (* reste les cas booléens *)
  all: unfold Cop.sem_notbool, Cop.bool_val, Cop.classify_bool in *.
  all: repeat (cases_eqn HH; subst; simpl in *; try congruence).
Qed.

Theorem check_unop_correct :
  forall op ty ty',
    check_unop op ty = true ->
    type_unop op ty = Some ty' -> (* ok with wt_exp *)
    forall v, wt_value v ty ->
         sem_unop op v ty <> None.
Proof.
  unfold sem_unop, type_unop.
  intros * Hck Hty v Hwt.
  destruct ty as [ty|tx tn].
  - (* Tprimitive *)
    inv Hwt.
    destruct op.
    + (* UnaryOp *)
      unfold option_map.
      cases_eqn Hok; try congruence.
      eapply unary_operation_ok in Hok; eauto.
    + (* CastOp *)
      unfold option_map.
      cases_eqn Hok; try congruence.
      eapply sem_cast_ok in Hok; eauto.
  - (* Tenum *)
    destruct
      (EquivDec.equiv_decb tx Ident.Ids.bool_id) eqn:Heq,
      (PeanoNat.Nat.eqb (Datatypes.length tn) 2) eqn:Hl;
      simpl in Hty; try congruence.
    rewrite PeanoNat.Nat.eqb_eq in Hl.
    destruct op as [[]|]; try congruence.
    inv Hwt; rewrite Hl in *.
    simpl; cases; simpl; try congruence; lia.
Qed.


(** Binary operations that always work with types ty1 and ty2 *)
Definition check_binop_any (op : binop) (ty1 ty2 : type) : bool :=
  match op with
  | Cop.Odiv =>
      match ty1, ty2 with
      | Tprimitive t1, Tprimitive t2 =>
          match Cop.classify_binarith (cltype t1) (cltype t2) with
          (* floating point division is always defined *)
          | Cop.bin_case_f | Cop.bin_case_s => true
          | _ => false
          end
      | _,_ => false
      end
  | Cop.Omod => false
  | Cop.Oshl => false
  | Cop.Oshr => false
  | _ => true
  end.

(* TODO: plus rapide. TODO: c'est plus fort que sem_cast ??? sans doute pas *)
Lemma sem_cast1_ok :
  forall v1 t1 t2 m,
    wt_cvalue v1 t1 ->
    Cop.sem_cast v1 (cltype t1) (Cop.binarith_type (Cop.classify_binarith (cltype t1) (cltype t2))) m <> None.
Proof.
  unfold Cop.sem_cast, Cop.classify_binarith.
  intros * Hwt1.
  inv Hwt1; simpl.
  all: cases_eqn HH; subst.
  all: try congruence.
  all: simpl in *; cases_eqn HH; subst; congruence.
Qed.


(* TODO: plus rapide. TODO: c'est plus fort que sem_cast ??? sans doute pas *)
Lemma sem_cast2_ok :
  forall v2 t1 t2 m,
    wt_cvalue v2 t2 ->
    Cop.sem_cast v2 (cltype t2) (Cop.binarith_type (Cop.classify_binarith (cltype t1) (cltype t2))) m <> None.
Proof.
  unfold Cop.sem_cast, Cop.classify_binarith.
  intros * Hwt.
  inv Hwt; simpl.
  all: cases_eqn HH; subst.
  all: try congruence.
  all: simpl in *; cases_eqn HH; subst; congruence.
Qed.

(* useless ? *)
Lemma classify_binarith_ok :
  forall t1 t2,
    Cop.classify_binarith (cltype t1) (cltype t2) <> Cop.bin_default.
Proof.
  intros t1 t2.
  unfold Cop.classify_binarith.
  destruct t1, t2; simpl; cases; congruence.
Qed.

Lemma sem_binarith_ok1 :
  forall sem_int sem_long sem_float sem_single v1 t1 v2 t2 m,
  (forall sg n1 n2, sem_int sg n1 n2 <> None) ->
  (forall sg n1 n2, sem_long sg n1 n2 <> None) ->
  (forall n1 n2, sem_float n1 n2 <> None) ->
  (forall n1 n2, sem_single n1 n2 <> None) ->
  wt_cvalue v1 t1 ->
  wt_cvalue v2 t2 ->
  Cop.sem_binarith sem_int sem_long sem_float sem_single v1 (cltype t1) v2 (cltype t2) m <> None.
Proof.
  intros * Hint Hlong Hfloat Hsingle Hwt1 Hwt2.

  unfold Cop.sem_binarith.
  destruct (Cop.sem_cast v1 _ _ _) eqn:Hc1.
  2:{ apply sem_cast1_ok in Hc1; auto. }
  destruct (Cop.sem_cast v2 _ _ _) eqn:Hc2.
  2:{ apply sem_cast2_ok in Hc2; auto. }

  destruct t1, t2; simpl.
  all: inv Hwt1; inv Hwt2.
  all: repeat (simpl in *; cases_eqn HH; subst).
  all: inv Hc1; inv Hc2.
Qed.

Lemma sem_binarith_ok2 :
  forall sem_int sem_long sem_float sem_single v1 t1 v2 t2 m,
  match Cop.classify_binarith (cltype t1) (cltype t2) with
  | Cop.bin_case_i _ | Cop.bin_case_l _ =>
     (forall sg n1 n2, sem_int sg n1 n2 <> None)
   /\ (forall sg n1 n2, sem_long sg n1 n2 <> None)
  | Cop.bin_case_f | Cop.bin_case_s =>
     (forall n1 n2, sem_float n1 n2 <> None)
     /\ (forall n1 n2, sem_single n1 n2 <> None)
  | _ => False
  end ->
  wt_cvalue v1 t1 ->
  wt_cvalue v2 t2 ->
  Cop.sem_binarith sem_int sem_long sem_float sem_single v1 (cltype t1) v2 (cltype t2) m <> None.
Proof.
  intros * Hcl Hwt1 Hwt2.
  unfold Cop.sem_binarith.
  destruct (Cop.sem_cast v1 _ _ _) eqn:Hc1.
  2:{ apply sem_cast1_ok in Hc1; auto. }
  destruct (Cop.sem_cast v2 _ _ _) eqn:Hc2.
  2:{ apply sem_cast2_ok in Hc2; auto. }

  destruct t1, t2; simpl.
  all: inv Hwt1; inv Hwt2.
  all: repeat (simpl in *; cases_eqn HH; subst).
  all: inv Hc1; inv Hc2.
  all: destruct Hcl; congruence.
Qed.

Theorem check_binop_any_correct :
  forall op ty1 ty2 ty',
    check_binop_any op ty1 ty2 = true ->
    type_binop op ty1 ty2 = Some ty' -> (* ok with wt_exp *)
    forall v1 v2, wt_value v1 ty1 ->
             wt_value v2 ty2 ->
             sem_binop op v1 ty1 v2 ty2 <> None.
Proof.
  unfold sem_binop, type_binop.
  intros * Hck Hty v1 v2 Hwt1 Hwt2.
  destruct ty1, ty2; try congruence.
  - (* Tprimitive *)
    inv Hwt1; inv Hwt2.
    destruct op; simpl in *; try congruence.
    + (* Oadd *)
      unfold option_map, Cop.sem_add.
      rewrite classify_add_cltypes.
      destruct (Cop.sem_binarith _ _ _ _ _) eqn:Hop; try congruence.
      apply sem_binarith_ok1 in Hop; congruence.
    + (* Osub *)
      unfold option_map, Cop.sem_sub.
      rewrite classify_sub_cltypes.
      destruct (Cop.sem_binarith _ _ _ _ _) eqn:Hop; try congruence.
      apply sem_binarith_ok1 in Hop; congruence.
    + (* Omul *)
      unfold option_map, Cop.sem_mul; cases_eqn Hop; try congruence.
      apply sem_binarith_ok1 in Hop0; congruence.
    + (* Odiv *)
      unfold option_map, Cop.sem_div.
      destruct (Cop.sem_binarith _ _ _ _ _) eqn:Hop; try congruence.
      apply sem_binarith_ok2 in Hop; try congruence.
      cases; split; congruence.
    + (* Oand *)
      unfold option_map; cases_eqn Hop; try congruence.
      apply sem_binarith_ok2 in Hop0; try congruence.
      unfold Ctyping.binarith_int_type in Hop.
      cases; split; congruence.
    + (* Oor *)
      unfold option_map; cases_eqn Hop; try congruence.
      apply sem_binarith_ok2 in Hop0; try congruence.
      unfold Ctyping.binarith_int_type in Hop.
      cases; split; congruence.
    + (* Oxor *)
      unfold option_map; cases_eqn Hop; try congruence.
      apply sem_binarith_ok2 in Hop0; try congruence.
      unfold Ctyping.binarith_int_type in Hop.
      cases; split; congruence.
    + (* Oeq *)
      unfold option_map, Cop.sem_cmp.
      rewrite classify_cmp_cltypes.
      cases_eqn Hop; try congruence.
      apply sem_binarith_ok1 in Hop0; congruence.
    + (* One *)
      unfold option_map, Cop.sem_cmp.
      rewrite classify_cmp_cltypes.
      cases_eqn Hop; try congruence.
      apply sem_binarith_ok1 in Hop0; congruence.
    + (* Olt *)
      unfold option_map, Cop.sem_cmp.
      rewrite classify_cmp_cltypes.
      cases_eqn Hop; try congruence.
      apply sem_binarith_ok1 in Hop0; congruence.
    + (* Ogt *)
      unfold option_map, Cop.sem_cmp.
      rewrite classify_cmp_cltypes.
      cases_eqn Hop; try congruence.
      apply sem_binarith_ok1 in Hop0; congruence.
    + (* Ole *)
      unfold option_map, Cop.sem_cmp.
      rewrite classify_cmp_cltypes.
      cases_eqn Hop; try congruence.
      apply sem_binarith_ok1 in Hop0; congruence.
    + (* Oge *)
      unfold option_map, Cop.sem_cmp.
      rewrite classify_cmp_cltypes.
      cases_eqn Hop; try congruence.
      apply sem_binarith_ok1 in Hop0; congruence.
  - (* Tenum *)
    inv Hwt1; inv Hwt2.
    destruct (EquivDec.equiv_decb i Ident.Ids.bool_id && EquivDec.equiv_decb i0 Ident.Ids.bool_id)
      eqn:Heq1.
    2: cases_eqn HH; simpl in *; congruence.
    repeat (cases_eqn Hl; simpl in *; try congruence).
    apply andb_prop in Hl0 as [ Hl1 Hl2 ].
    apply PeanoNat.Nat.eqb_eq in Hl1, Hl2.
    unfold option_map, sem_binop_bool, truth_table.
    destruct op; simpl in Hck; try congruence.
    all: cases_eqn HH; subst; simpl in *; try congruence; lia.
Qed.


(** Concrete definition of check_binop_val (v2 = valeur du membre droit) *)
(* TODO: étendre un peu ?? *)
Definition check_binop_val (op : binop) (ty1 : type) (v2 : value) (ty2 : type) : bool :=
  match op, ty1, v2, ty2 with
  | Cop.Odiv, Tprimitive (Tint Ctypes.I32 _), Vscalar (Values.Vint n), Tprimitive (Tint Ctypes.I32 _) =>
      negb (Integers.Int.eq n Integers.Int.zero)
      && negb (Integers.Int.eq n Integers.Int.mone)
  | _, _, _, _ => false
  end.

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
