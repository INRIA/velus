Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.Clocks.

Require Import Velus.SyBloc.SBIsVariable.
Require Import Velus.SyBloc.SBIsLast.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type SBISDEFINED
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import Clks    : CLOCKS       Ids)
       (Import ExprSyn : NLEXPRSYNTAX     Op)
       (Import Syn     : SBSYNTAX     Ids Op Clks ExprSyn)
       (Import Var     : SBISVARIABLE Ids Op Clks ExprSyn Syn)
       (Import Last    : SBISLAST     Ids Op Clks ExprSyn Syn).

  Inductive Is_defined_in_eq: ident -> equation -> Prop :=
  | DefEqDef:
      forall x ck e,
        Is_defined_in_eq x (EqDef x ck e)
  | DefEqNext:
      forall x ck e,
        Is_defined_in_eq x (EqNext x ck e)
  | DefEqCall:
      forall x s xs ck rst b es,
        In x xs ->
        Is_defined_in_eq x (EqCall s xs ck rst b es).

  Definition Is_defined_in (x: ident) (eqs: list equation) : Prop :=
    Exists (Is_defined_in_eq x) eqs.

  Lemma Is_defined_Is_variable_Is_last_in:
    forall eqs x,
      Is_defined_in x eqs ->
      Is_variable_in x eqs \/ Is_last_in x eqs.
  Proof.
    induction eqs; inversion_clear 1 as [?? Def|?? Defs].
    - inv Def.
      + left; left; constructor; auto.
      + right; left; constructor; auto.
      + left; left; constructor; auto.
    - apply IHeqs in Defs as [].
      + left; right; auto.
      + right; right; auto.
  Qed.

  Lemma b_ins_not_def:
    forall b x,
      InMembers x b.(b_in) ->
      ~ Is_defined_in x b.(b_eqs).
  Proof.
    intros ** Hin Hdef.
    pose proof (b_nodup b) as Nodup.
    eapply (NoDup_app_In x) in Nodup.
    - apply Is_defined_Is_variable_Is_last_in in Hdef as [Var|Last];
        apply Nodup, in_app.
      + apply Is_variable_in_variables in Var; rewrite <-b_vars_out_in_eqs in Var;
          auto.
      + apply lasts_of_In in Last; rewrite <-b_lasts_in_eqs in Last; auto.
    - apply fst_InMembers; auto.
  Qed.

  Lemma not_Is_defined_in_eq_EqDef:
    forall y x ck e,
      ~ Is_defined_in_eq y (EqDef x ck e) -> x <> y.
  Proof.
    intros ** NIsDef E; subst; apply NIsDef; auto using Is_defined_in_eq.
  Qed.

  Lemma not_Is_defined_in_eq_EqNext:
    forall y x ck e,
      ~ Is_defined_in_eq y (EqNext x ck e) -> x <> y.
  Proof.
    intros ** NIsDef E; subst; apply NIsDef; auto using Is_defined_in_eq.
  Qed.

  Lemma not_Is_defined_in_cons:
    forall x eq eqs,
      ~ Is_defined_in x (eq :: eqs)
      <-> ~ Is_defined_in_eq x eq /\ ~ Is_defined_in x eqs.
  Proof.
    split.
    - intro Hndef; split; intro His_def;
        eapply Hndef; constructor (assumption).
    - intros [Hdef_eq Hdef_eqs] Hdef_all.
      inv Hdef_all; eauto.
  Qed.

  Definition defined_eq (eq: equation): idents :=
    match eq with
    | EqNext x _ _
    | EqDef x _ _ => [x]
    | EqCall _ xs _ _ _ _ => xs
    | EqReset _ _ _ => []
    end.

  Lemma Is_defined_in_defined_eq:
    forall x eq,
      Is_defined_in_eq x eq <-> In x (defined_eq eq).
  Proof.
    destruct eq; split; try inversion_clear 1; subst;
      simpl; auto using Is_defined_in_eq; try contradiction.
  Qed.

End SBISDEFINED.

Module SBIsDefinedFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (Clks    : CLOCKS       Ids)
       (ExprSyn : NLEXPRSYNTAX     Op)
       (Syn     : SBSYNTAX     Ids Op Clks ExprSyn)
       (Var     : SBISVARIABLE Ids Op Clks ExprSyn Syn)
       (Last    : SBISLAST     Ids Op Clks ExprSyn Syn)
<: SBISDEFINED Ids Op Clks ExprSyn Syn Var Last.
  Include SBISDEFINED Ids Op Clks ExprSyn Syn Var Last.
End SBIsDefinedFun.
