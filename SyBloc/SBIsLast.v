Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.Clocks.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type SBISLAST
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import Clks    : CLOCKS       Ids)
       (Import ExprSyn : NLEXPRSYNTAX     Op)
       (Import Syn     : SBSYNTAX     Ids Op Clks ExprSyn).

  Inductive Is_last_in_eq: ident -> equation -> Prop :=
    LastEqNext:
      forall x ck e,
        Is_last_in_eq x (EqNext x ck e).

  Definition Is_last_in (x: ident) (eqs: list equation) : Prop :=
    Exists (Is_last_in_eq x) eqs.

  Lemma not_Is_last_in_cons:
    forall x eq eqs,
      ~ Is_last_in x (eq :: eqs) <-> ~ Is_last_in_eq x eq /\ ~ Is_last_in x eqs.
  Proof.
    split; intros HH.
    - split; intro; apply HH; unfold Is_last_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma lasts_of_In:
    forall eqs x,
      Is_last_in x eqs <-> In x (lasts_of eqs).
  Proof.
    induction eqs as [|[]]; simpl.
    - now setoid_rewrite Exists_nil.
    - setoid_rewrite <-IHeqs; split; try right; auto.
      inversion_clear 1 as [?? Last|]; try inv Last; auto.
    - setoid_rewrite <-IHeqs; split.
      + inversion_clear 1 as [?? Last|]; try inv Last; auto.
      + intros [E|?].
        * subst; left; constructor.
        * right; auto.
    - setoid_rewrite <-IHeqs; split; try right; auto.
      inversion_clear 1 as [?? Last|]; try inv Last; auto.
    - setoid_rewrite <-IHeqs; split; try right; auto.
      inversion_clear 1 as [?? Last|]; try inv Last; auto.
  Qed.

  Definition is_last_in_eq_b (x: ident) (eq: equation) : bool :=
    match eq with
    | EqNext y ck e => ident_eqb x y
    | _ => false
    end.

  Definition is_last_in_b (x: ident) (eqs: list equation) : bool :=
    existsb (is_last_in_eq_b x) eqs.

  Fact Is_last_in_eq_reflect:
    forall x eq,
      Is_last_in_eq x eq <-> is_last_in_eq_b x eq = true.
  Proof.
    destruct eq; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intro; subst; constructor.
  Qed.

  Corollary Is_last_in_reflect:
    forall x eqs,
      Is_last_in x eqs <-> is_last_in_b x eqs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Last); apply Is_last_in_eq_reflect in Last; eauto.
  Qed.

  Lemma Is_last_in_dec:
    forall x eqs,
      { Is_last_in x eqs } + { ~ Is_last_in x eqs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_last_in_reflect.
  Qed.

End SBISLAST.
