From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import SyBloc.SBSyntax.
From Velus Require Import Clocks.

From Velus Require Export CoreExpr.CEIsFree.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type SBISFREE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX     Op)
       (Import Syn   : SBSYNTAX Ids Op CESyn)
       (Import CEIsF : CEISFREE Ids Op CESyn).

  Inductive Is_free_in_eq: ident -> equation -> Prop :=
  | FreeEqDef:
      forall x ck e y,
        Is_free_in_caexp y ck e ->
        Is_free_in_eq y (EqDef x ck e)
  | FreeEqNext:
      forall x ck e y,
        Is_free_in_aexp y ck e ->
        Is_free_in_eq y (EqNext x ck e)
  | FreeEqReset:
      forall s ck b x,
        Is_free_in_clock x ck ->
        Is_free_in_eq x (EqReset s ck b)
  | FreeEqCall:
      forall s x ck rst b es y,
        Is_free_in_aexps y ck es ->
        Is_free_in_eq y (EqCall s x ck rst b es).

  Definition Is_free_in (x: ident) (eqs: list equation) : Prop :=
    Exists (Is_free_in_eq x) eqs.

  Definition free_in_eq (eq: equation) (fvs: PS.t) : PS.t :=
    match eq with
    | EqDef _ ck e => free_in_caexp ck e fvs
    | EqNext _ ck e => free_in_aexp ck e fvs
    | EqReset _ ck _ => free_in_clock ck fvs
    | EqCall _ _ ck _ _ es => free_in_aexps ck es fvs
    end.

  Hint Constructors Is_free_in_clock Is_free_in_exp
       Is_free_in_aexp Is_free_in_aexps Is_free_in_cexp
       Is_free_in_caexp Is_free_in_eq.

  Lemma free_in_eq_spec:
    forall x eq m,
      PS.In x (free_in_eq eq m)
      <-> (Is_free_in_eq x eq \/ PS.In x m).
  Proof.
    Local Ltac aux :=
      repeat (match goal with
              | H:Is_free_in_eq _ _ |- _ => inversion_clear H
              | H:PS.In _ (free_in_eq _ _) |- _ =>
                apply free_in_clock_spec in H
                || apply free_in_caexp_spec in H
                || apply free_in_aexp_spec in H
                || apply free_in_aexps_spec in H
              | |- PS.In _ (free_in_eq _ _) =>
                apply free_in_clock_spec
                || apply free_in_caexp_spec
                || apply free_in_aexp_spec
                || apply free_in_aexps_spec
              | _ => intuition; eauto
              end).
    destruct eq; split; intro H; aux.
  Qed.

  Corollary free_in_eq_spec':
    forall x eq,
      PS.In x (free_in_eq eq PS.empty)
      <-> Is_free_in_eq x eq.
  Proof.
    intros; rewrite free_in_eq_spec. intuition.
  Qed.


End SBISFREE.

Module SBIsFreeFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX     Op)
       (Syn   : SBSYNTAX Ids Op CESyn)
       (CEIsF : CEISFREE Ids Op CESyn)
<: SBISFREE Ids Op CESyn Syn CEIsF.
  Include SBISFREE Ids Op CESyn Syn CEIsF.
End SBIsFreeFun.
