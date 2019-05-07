Require Import Velus.Common.Common.
Require Import Velus.Operators.
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.Clocks.

Require Import Velus.SyBloc.SBIsVariable.
Require Import Velus.SyBloc.SBIsLast.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type SBISDEFINED
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX         Op)
       (Import Syn   : SBSYNTAX     Ids Op CESyn)
       (Import Var   : SBISVARIABLE Ids Op CESyn Syn)
       (Import Last  : SBISLAST     Ids Op CESyn Syn).

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
      Is_defined_in x eqs <->
      Is_variable_in x eqs \/ Is_last_in x eqs.
  Proof.
    induction eqs; split.
    - inversion 1.
    - intros [E|E]; inversion E.
    - inversion_clear 1 as [?? Def|?? Defs].
      + inv Def.
        * left; left; constructor; auto.
        * right; left; constructor; auto.
        * left; left; constructor; auto.
      + apply IHeqs in Defs as [].
        * left; right; auto.
        * right; right; auto.
    - intros [E|E]; inversion_clear E as [?? E'|].
      + inv E'.
        * left; constructor.
        * left; constructor; auto.
      + right; apply IHeqs; auto.
      + inv E'; left; constructor.
      + right; apply IHeqs; auto.
  Qed.

  Lemma Is_variable_in_eq_Is_defined_in_eq:
    forall x eq,
      Is_variable_in_eq x eq ->
      Is_defined_in_eq x eq.
  Proof.
    destruct eq; inversion_clear 1; auto using Is_defined_in_eq.
  Qed.

  Lemma Is_variable_in_Is_defined_in:
    forall x eqs,
      Is_variable_in x eqs ->
      Is_defined_in x eqs.
  Proof.
    induction eqs; inversion_clear 1 as [?? Var|].
    - inv Var; left; constructor; auto.
    - right; auto; apply IHeqs; auto.
  Qed.

  Lemma b_ins_not_def:
    forall b x,
      InMembers x b.(b_in) ->
      ~ Is_defined_in x b.(b_eqs).
  Proof.
    intros * Hin Hdef.
    pose proof (b_nodup b) as Nodup.
    eapply (NoDup_app_In x) in Nodup.
    - apply Is_defined_Is_variable_Is_last_in in Hdef as [Var|Last];
        apply Nodup; rewrite app_assoc, in_app.
      + apply Is_variable_in_variables in Var; rewrite <-b_vars_out_in_eqs in Var;
          auto.
      + apply lasts_of_In in Last; rewrite <-b_lasts_in_eqs in Last; auto.
    - apply fst_InMembers; auto.
  Qed.

  Lemma not_Is_defined_in_eq_EqDef:
    forall y x ck e,
      ~ Is_defined_in_eq y (EqDef x ck e) -> x <> y.
  Proof.
    intros * NIsDef E; subst; apply NIsDef; auto using Is_defined_in_eq.
  Qed.

  Lemma not_Is_defined_in_eq_EqNext:
    forall y x ck e,
      ~ Is_defined_in_eq y (EqNext x ck e) -> x <> y.
  Proof.
    intros * NIsDef E; subst; apply NIsDef; auto using Is_defined_in_eq.
  Qed.

  Lemma not_Is_defined_in_cons:
    forall x eq eqs,
      ~ Is_defined_in x (eq :: eqs)
      <-> ~ Is_defined_in_eq x eq /\ ~ Is_defined_in x eqs.
  Proof.
    split.
    - intro Hndef; split; intro His_def;
        eapply Hndef; now constructor.
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

  Definition defined := flat_map defined_eq.

  Lemma Is_defined_in_defined_eq:
    forall x eq,
      Is_defined_in_eq x eq <-> In x (defined_eq eq).
  Proof.
    destruct eq; split; try inversion_clear 1; subst;
      simpl; auto using Is_defined_in_eq; try contradiction.
  Qed.

  Lemma Is_defined_in_defined:
    forall x eqs,
      Is_defined_in x eqs <-> In x (defined eqs).
  Proof.
    unfold defined.
    induction eqs; simpl.
    - split; inversion 1.
    - split; rewrite in_app.
      + inversion_clear 1.
        * left; apply Is_defined_in_defined_eq; auto.
        * right; apply IHeqs; auto.
      + intros [?|?].
        * left; apply Is_defined_in_defined_eq; auto.
        * right; apply IHeqs; auto.
  Qed.

  Lemma block_output_defined_in_eqs:
    forall b x,
      In x (map fst b.(b_out)) ->
      Is_defined_in x b.(b_eqs).
  Proof.
    intros * Ho.
    cut (In x (map fst b.(b_vars) ++ map fst b.(b_out))).
    - intro Hvo; apply Is_variable_in_Is_defined_in, Is_variable_in_variables.
      now rewrite <-b_vars_out_in_eqs.
    - apply in_or_app; auto.
  Qed.

  Lemma Is_defined_in_In:
    forall x eqs,
      Is_defined_in x eqs ->
      exists eq, In eq eqs /\ Is_defined_in_eq x eq.
  Proof.
    induction eqs as [|eq]. now inversion 1.
    inversion_clear 1 as [? ? Hdef|? ? Hex].
    - exists eq; split; auto with datatypes.
    - apply Exists_exists in Hex as (eq' & Hin & Hdef).
      exists eq'; split; auto with datatypes.
  Qed.

  Lemma b_defined:
    forall b,
      Permutation.Permutation (defined (b_eqs b)) (variables (b_eqs b) ++ lasts_of (b_eqs b)).
  Proof.
    unfold defined, variables; intro;
      induction (b_eqs b) as [|[]]; simpl; auto.
    - now apply Permutation.Permutation_cons_app.
    - now rewrite <-app_assoc; apply Permutation.Permutation_app_head.
  Qed.

End SBISDEFINED.

Module SBIsDefinedFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX         Op)
       (Syn   : SBSYNTAX     Ids Op CESyn)
       (Var   : SBISVARIABLE Ids Op CESyn Syn)
       (Last  : SBISLAST     Ids Op CESyn Syn)
<: SBISDEFINED Ids Op CESyn Syn Var Last.
  Include SBISDEFINED Ids Op CESyn Syn Var Last.
End SBIsDefinedFun.
