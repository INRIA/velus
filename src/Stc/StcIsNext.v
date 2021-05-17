From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Clocks.

From Velus Require Export CoreExpr.CEIsFree.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCISNEXT
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX      Op)
       (Import Syn   : STCSYNTAX Ids Op CESyn).

  Inductive Is_next_in_tc: ident -> trconstr -> Prop :=
  | NextTcNext:
      forall x ck ckrs e,
        Is_next_in_tc x (TcNext x ck ckrs e).

  Definition Is_next_in (x : ident) (tcs : list trconstr) :=
    Exists (Is_next_in_tc x) tcs.

  Lemma not_Is_next_in_cons:
    forall x tc tcs,
      ~ Is_next_in x (tc :: tcs) <-> ~ Is_next_in_tc x tc /\ ~ Is_next_in x tcs.
  Proof.
    split; intros HH.
    - split; intro; apply HH; unfold Is_next_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma next_of_In:
    forall x tc,
      Is_next_in_tc x tc <-> In x (nexts_of [tc]).
  Proof.
    destruct tc; simpl; split; intros H; inv H; auto using Is_next_in_tc.
    inv H0.
  Qed.

  Lemma nexts_of_In:
    forall x tcs,
      Is_next_in x tcs <-> In x (nexts_of tcs).
  Proof.
    induction tcs as [|[]]; simpl.
    - now setoid_rewrite Exists_nil.
    - setoid_rewrite <-IHtcs; split; try right; auto.
      inversion_clear 1 as [?? Next|]; try inv Next; auto.
    - setoid_rewrite <-IHtcs; split; try right; auto.
      inversion_clear 1 as [?? Next|]; try inv Next; auto.
    - setoid_rewrite <-IHtcs; split.
      + inversion_clear 1 as [?? Next|]; try inv Next; auto.
      + intros [E|?].
        * subst; left; constructor.
        * right; auto.
    - setoid_rewrite <-IHtcs; split; try right; auto.
      inversion_clear 1 as [?? Next|]; try inv Next; auto.
    - setoid_rewrite <-IHtcs; split; try right; auto.
      inversion_clear 1 as [?? Next|]; try inv Next; auto.
  Qed.

  Definition is_next_in_tc_b (x: ident) (tc: trconstr) : bool :=
    match tc with
    | TcNext y _ _ _ => ident_eqb x y
    | _ => false
    end.

  Definition is_next_in_b (x: ident) (tcs: list trconstr) : bool :=
    existsb (is_next_in_tc_b x) tcs.

  Fact Is_next_in_tc_reflect:
    forall x tc,
      Is_next_in_tc x tc <-> is_next_in_tc_b x tc = true.
  Proof.
    destruct tc; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intro; subst; constructor.
  Qed.

  Corollary Is_next_in_reflect:
    forall x tcs,
      Is_next_in x tcs <-> is_next_in_b x tcs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Next); apply Is_next_in_tc_reflect in Next; eauto.
  Qed.

  Lemma Is_next_in_dec:
    forall x tcs,
      { Is_next_in x tcs } + { ~ Is_next_in x tcs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_next_in_reflect.
  Qed.

  Lemma not_Is_next_in_tc_TcNext:
    forall y x ck ckrs le,
      ~ Is_next_in_tc y (TcNext x ck ckrs le) -> x <> y.
  Proof.
    intros * NIsNext E; subst; apply NIsNext ; auto using Is_next_in_tc.
  Qed.

  Lemma s_ins_not_next:
    forall s x,
      InMembers x s.(s_in) ->
      ~ Is_next_in x s.(s_tcs).
  Proof.
    intros * Hin Hnext.
    pose proof (s_nodup s) as Nodup.
    eapply (NoDup_app_In x) in Nodup.
    - apply nexts_of_In in Hnext.
      rewrite <-s_nexts_in_tcs in Hnext.
      apply Nodup; rewrite app_assoc, in_app; auto.
    - apply fst_InMembers; auto.
  Qed.

  Lemma Next_with_reset_in_Is_next_in:
    forall tcs s rst,
      Next_with_reset_in s rst tcs ->
      Is_next_in s tcs.
  Proof.
    induction 1 as [?? Next|].
    - inv Next; left; constructor.
    - right; auto.
  Qed.

End STCISNEXT.

Module StcIsNextFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX          Op)
       (Syn   : STCSYNTAX     Ids Op CESyn)
<: STCISNEXT Ids Op CESyn Syn.
  Include STCISNEXT Ids Op CESyn Syn.
End StcIsNextFun.
