Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.Clocks.

Require Import Velus.NLustre.NLSyntax.
Require Export Velus.NLustre.IsFree.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type SBISFREE
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import Clks    : CLOCKS       Ids)
       (Import ExprSyn : NLEXPRSYNTAX     Op)
       (Import Syn     : SBSYNTAX     Ids Op Clks ExprSyn)
       (SynNL          : NLSYNTAX     Ids Op Clks ExprSyn)
       (Import IsF     : ISFREE       Ids Op Clks ExprSyn SynNL).

  Inductive Is_free_in_eq: ident -> equation -> Prop :=
  | FreeEqDef:
      forall x ck e y,
        Is_free_in_caexp y ck e ->
        Is_free_in_eq y (EqDef x ck e)
  | FreeEqNext:
      forall x ck e y,
        Is_free_in_laexp y ck e ->
        Is_free_in_eq y (EqNext x ck e)
  | FreeEqReset:
      forall s ck b x,
        Is_free_in_clock x ck ->
        Is_free_in_eq x (EqReset s ck b)
  | FreeEqCall:
      forall s x ck rst b es y,
        Is_free_in_laexps y ck es ->
        Is_free_in_eq y (EqCall s x ck rst b es).

  Definition Is_free_in (x: ident) (eqs: list equation) : Prop :=
    Exists (Is_free_in_eq x) eqs.

End SBISFREE.
