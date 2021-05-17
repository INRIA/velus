From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Clocks.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCISRESET
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX Ids Op OpAux Cks CESyn).

  Lemma not_Is_reset_in_cons:
    forall x ck tc tcs,
      ~ Is_reset_in x ck (tc :: tcs) <-> ~ Is_reset_in_tc x ck tc /\ ~ Is_reset_in x ck tcs.
  Proof.
    split; intros HH.
    - split; intro; apply HH; unfold Is_reset_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma not_Is_reset_in_cons':
    forall x tc tcs,
      ~ (exists ck, Is_reset_in x ck (tc :: tcs)) <-> ~ (exists ck, Is_reset_in_tc x ck tc) /\ ~ (exists ck, Is_reset_in x ck tcs).
  Proof.
    split; intros HH.
    - split; intros (?&H); apply HH; unfold Is_reset_in; eauto.
    - destruct HH; intros (?&HH); inversion_clear HH; eauto.
  Qed.

  Lemma reset_of_In:
    forall x tc,
      (exists ck, Is_reset_in_tc x ck tc) <-> In x (resets_of [tc]).
  Proof.
    destruct tc; simpl; (split; [intros (?&H)|intro H]); inv H; eauto using Is_reset_in_tc.
    inv H0.
  Qed.

  Lemma resets_of_In:
    forall tcs x,
      (exists ck, Is_reset_in x ck tcs) <-> In x (resets_of tcs).
  Proof.
    induction tcs as [|[]]; simpl; intros.
    - setoid_rewrite Exists_nil.
      split; [intros (?&?)|intros ?]; eauto using Cbase.
    - setoid_rewrite <-IHtcs.
      split; intros (ck&?); exists ck; try right; eauto.
      inversion_clear H as [?? Reset|]; try inv Reset; auto.
    - setoid_rewrite <-IHtcs; split.
      + intros (?&H). inversion_clear H as [?? Reset|]; try inv Reset; eauto.
      + intros [E|(ck&?)]; subst.
        * exists c; left; constructor.
        * exists ck; right; auto.
    - setoid_rewrite <-IHtcs; split; intros (ck&?); exists ck; try right; eauto.
      inversion_clear H as [?? Reset|]; try inv Reset; auto.
    - setoid_rewrite <-IHtcs; split; intros (ck&?); exists ck; try right; eauto.
      inversion_clear H as [?? Reset|]; try inv Reset; auto.
    - setoid_rewrite <-IHtcs; split; intros (ck&?); exists ck; try right; eauto.
      inversion_clear H as [?? Reset|]; try inv Reset; auto.
  Qed.

  Definition is_reset_in_tc_b (x: ident) (ck: clock) (tc: trconstr) : bool :=
    match tc with
    | TcReset y ck' _ _ => ident_eqb x y && clock_eq ck ck'
    | _ => false
    end.

  Definition is_reset_in_b (x: ident) (ck: clock) (tcs: list trconstr) : bool :=
    existsb (is_reset_in_tc_b x ck) tcs.

  Fact Is_reset_in_tc_reflect:
    forall x ck tc,
      Is_reset_in_tc x ck tc <-> is_reset_in_tc_b x ck tc = true.
  Proof.
    destruct tc; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1.
      rewrite Bool.andb_true_iff; split.
      apply ident_eqb_refl.
      rewrite clock_eq_spec; auto.
    - rewrite Bool.andb_true_iff, ident_eqb_eq, clock_eq_spec.
      intros (?&?); subst; constructor.
  Qed.

  Corollary Is_reset_in_reflect:
    forall x ck tcs,
      Is_reset_in x ck tcs <-> is_reset_in_b x ck tcs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Reset); apply Is_reset_in_tc_reflect in Reset; eauto.
  Qed.

  Lemma Is_reset_in_dec:
    forall x ck tcs,
      { Is_reset_in x ck tcs } + { ~ Is_reset_in x ck tcs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_reset_in_reflect.
  Qed.

  Lemma not_Is_reset_in_tc_TcReset:
    forall y x ck ty ro,
      ~ (exists ck', Is_reset_in_tc y ck' (TcReset x ck ty ro)) -> x <> y.
  Proof.
    intros * NIsReset E; subst; apply NIsReset; eauto using Is_reset_in_tc.
  Qed.

  Lemma s_ins_not_reset:
    forall s x ck,
      InMembers x s.(s_in) ->
      ~ Is_reset_in x ck s.(s_tcs).
  Proof.
    intros * Hin Hreset.
    pose proof (s_nodup s) as Nodup.
    eapply (NoDup_app_In x) in Nodup.
    - assert (In x (resets_of (s_tcs s))) as Hreset' by (apply resets_of_In; eauto).
      apply s_reset_incl in Hreset'.
      rewrite <-s_nexts_in_tcs_fst in Hreset'.
      apply Nodup; rewrite app_assoc, in_app; auto.
    - apply fst_InMembers; auto.
  Qed.

End STCISRESET.

Module StcIsResetFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Syn   : STCSYNTAX Ids Op OpAux Cks CESyn)
<: STCISRESET Ids Op OpAux Cks CESyn Syn.
  Include STCISRESET Ids Op OpAux Cks CESyn Syn.
End StcIsResetFun.
