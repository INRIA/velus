From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Clocks.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCISLAST
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX      Op)
       (Import Syn   : STCSYNTAX Ids Op CESyn).

  Inductive Is_last_in_tc: ident -> trconstr -> Prop :=
    LastTcNext:
      forall x ck e,
        Is_last_in_tc x (TcNext x ck e).

  Definition Is_last_in (x: ident) (tcs: list trconstr) : Prop :=
    Exists (Is_last_in_tc x) tcs.

  Lemma not_Is_last_in_cons:
    forall x tc tcs,
      ~ Is_last_in x (tc :: tcs) <-> ~ Is_last_in_tc x tc /\ ~ Is_last_in x tcs.
  Proof.
    split; intros HH.
    - split; intro; apply HH; unfold Is_last_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma lasts_of_In:
    forall tcs x,
      Is_last_in x tcs <-> In x (lasts_of tcs).
  Proof.
    induction tcs as [|[]]; simpl.
    - now setoid_rewrite Exists_nil.
    - setoid_rewrite <-IHtcs; split; try right; auto.
      inversion_clear 1 as [?? Last|]; try inv Last; auto.
    - setoid_rewrite <-IHtcs; split.
      + inversion_clear 1 as [?? Last|]; try inv Last; auto.
      + intros [E|?].
        * subst; left; constructor.
        * right; auto.
    - setoid_rewrite <-IHtcs; split; try right; auto.
      inversion_clear 1 as [?? Last|]; try inv Last; auto.
    - setoid_rewrite <-IHtcs; split; try right; auto.
      inversion_clear 1 as [?? Last|]; try inv Last; auto.
  Qed.

  Definition is_last_in_tc_b (x: ident) (tc: trconstr) : bool :=
    match tc with
    | TcNext y ck e => ident_eqb x y
    | _ => false
    end.

  Definition is_last_in_b (x: ident) (tcs: list trconstr) : bool :=
    existsb (is_last_in_tc_b x) tcs.

  Fact Is_last_in_tc_reflect:
    forall x tc,
      Is_last_in_tc x tc <-> is_last_in_tc_b x tc = true.
  Proof.
    destruct tc; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intro; subst; constructor.
  Qed.

  Corollary Is_last_in_reflect:
    forall x tcs,
      Is_last_in x tcs <-> is_last_in_b x tcs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Last); apply Is_last_in_tc_reflect in Last; eauto.
  Qed.

  Lemma Is_last_in_dec:
    forall x tcs,
      { Is_last_in x tcs } + { ~ Is_last_in x tcs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_last_in_reflect.
  Qed.

End STCISLAST.

Module StcIsLastFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX      Op)
       (Syn   : STCSYNTAX Ids Op CESyn)
<: STCISLAST Ids Op CESyn Syn.
  Include STCISLAST Ids Op CESyn Syn.
End StcIsLastFun.
