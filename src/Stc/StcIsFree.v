From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Clocks.

From Velus Require Export CoreExpr.CEIsFree.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCISFREE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX      Op)
       (Import Syn   : STCSYNTAX Ids Op CESyn)
       (Import CEIsF : CEISFREE  Ids Op CESyn).

  Inductive Is_free_in_tc: ident -> trconstr -> Prop :=
  | FreeTcDef:
      forall x ck e y,
        Is_free_in_caexp y ck e ->
        Is_free_in_tc y (TcDef x ck e)
  | FreeTcNext:
      forall x ck e y,
        Is_free_in_aexp y ck e ->
        Is_free_in_tc y (TcNext x ck e)
  | FreeTcReset:
      forall s ck b x,
        Is_free_in_clock x ck ->
        Is_free_in_tc x (TcReset s ck b)
  | FreeTcCall:
      forall s x ck rst b es y,
        Is_free_in_aexps y ck es ->
        Is_free_in_tc y (TcCall s x ck rst b es).

  Definition Is_free_in (x: ident) (tcs: list trconstr) : Prop :=
    Exists (Is_free_in_tc x) tcs.

  Definition free_in_tc (tc: trconstr) (fvs: PS.t) : PS.t :=
    match tc with
    | TcDef _ ck e => free_in_caexp ck e fvs
    | TcNext _ ck e => free_in_aexp ck e fvs
    | TcReset _ ck _ => free_in_clock ck fvs
    | TcCall _ _ ck _ _ es => free_in_aexps ck es fvs
    end.

  Hint Constructors Is_free_in_clock Is_free_in_exp
       Is_free_in_aexp Is_free_in_aexps Is_free_in_cexp
       Is_free_in_caexp Is_free_in_tc.

  Lemma free_in_tc_spec:
    forall x tc m,
      PS.In x (free_in_tc tc m)
      <-> (Is_free_in_tc x tc \/ PS.In x m).
  Proof.
    Local Ltac aux :=
      repeat (match goal with
              | H:Is_free_in_tc _ _ |- _ => inversion_clear H
              | H:PS.In _ (free_in_tc _ _) |- _ =>
                apply free_in_clock_spec in H
                || apply free_in_caexp_spec in H
                || apply free_in_aexp_spec in H
                || apply free_in_aexps_spec in H
              | |- PS.In _ (free_in_tc _ _) =>
                apply free_in_clock_spec
                || apply free_in_caexp_spec
                || apply free_in_aexp_spec
                || apply free_in_aexps_spec
              | _ => intuition; eauto
              end).
    destruct tc; split; intro H; aux.
  Qed.

  Corollary free_in_tc_spec':
    forall x tc,
      PS.In x (free_in_tc tc PS.empty)
      <-> Is_free_in_tc x tc.
  Proof.
    intros; rewrite free_in_tc_spec. intuition.
  Qed.


End STCISFREE.

Module StcIsFreeFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX     Op)
       (Syn   : STCSYNTAX Ids Op CESyn)
       (CEIsF : CEISFREE Ids Op CESyn)
<: STCISFREE Ids Op CESyn Syn CEIsF.
  Include STCISFREE Ids Op CESyn Syn CEIsF.
End StcIsFreeFun.
