From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Clocks.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCISVARIABLE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS    Ids Op OpAux)
       (Import CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX Ids Op OpAux Cks CESyn).

  Inductive Is_variable_in_tc: ident -> trconstr -> Prop :=
  | VarTcDef:
      forall x ck e,
        Is_variable_in_tc x (TcDef x ck e)
  | VarTcStep:
      forall x i xs ck rst f es,
        In x xs ->
        Is_variable_in_tc x (TcStep i xs ck rst f es).

  Global Hint Constructors Is_variable_in_tc : stcdef.

  Definition Is_variable_in (x: ident) (tcs: list trconstr) : Prop :=
    Exists (Is_variable_in_tc x) tcs.

  Lemma Is_variable_in_tc_variables_tc:
    forall tc x,
      Is_variable_in_tc x tc <-> In x (variables_tc tc).
  Proof.
    unfold variables.
    intros *; destruct tc; simpl; split; intro H; try inv H; auto.
    - constructor.
    - inv H0.
    - constructor; auto.
  Qed.

  Corollary Is_variable_in_variables:
    forall tcs x,
      Is_variable_in x tcs <-> In x (variables tcs).
  Proof.
    unfold variables.
    induction tcs; simpl.
    - split; try contradiction; inversion 1.
    - intro; setoid_rewrite Exists_cons.
      rewrite in_app, Is_variable_in_tc_variables_tc, <-IHtcs.
      tauto.
  Qed.

  Definition is_variable_in_tc_b (x: ident) (tc: trconstr) : bool :=
    match tc with
    | TcDef x' _ _ => ident_eqb x x'
    | TcStep _ xs _ _ _ _ => existsb (ident_eqb x) xs
    | _ => false
    end.

  Fact Is_variable_in_tc_reflect:
    forall x tc,
      Is_variable_in_tc x tc <-> is_variable_in_tc_b x tc = true.
  Proof.
    destruct tc; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intro; subst; constructor.
    - inversion_clear 1.
      apply existsb_exists; eexists; split; eauto.
      apply ident_eqb_refl.
    - rewrite existsb_exists; intros (?&?& E).
      apply ident_eqb_eq in E; subst.
      constructor; auto.
  Qed.

  Lemma Is_variable_in_tc_dec:
    forall x tc,
      { Is_variable_in_tc x tc } + { ~ Is_variable_in_tc x tc }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_variable_in_tc_reflect.
  Qed.

  Lemma not_Is_variable_in_cons:
    forall x tc tcs,
      ~ Is_variable_in x (tc :: tcs)
      <-> ~ Is_variable_in_tc x tc /\ ~ Is_variable_in x tcs.
  Proof.
    split.
    - intro Hndef; split; intro His_def;
        eapply Hndef; now constructor.
    - intros [Hdef_tc Hdef_tcs] Hdef_all.
      inv Hdef_all; eauto.
  Qed.

  Lemma s_ins_not_var:
    forall s x,
      InMembers x s.(s_in) ->
      ~ Is_variable_in x s.(s_tcs).
  Proof.
    intros * Hin Hvar.
    rewrite Is_variable_in_variables, <- s_vars_out_in_tcs in Hvar.
    pose proof (s_nodup s) as Nodup.
    eapply (NoDup_app_In x) in Nodup.
    - apply Nodup; rewrite app_assoc, in_app.
      repeat rewrite in_app_iff in *.
      destruct Hvar; auto.
    - apply fst_InMembers; auto.
  Qed.

End STCISVARIABLE.

Module StcIsVariableFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS    Ids Op OpAux)
       (CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Syn   : STCSYNTAX Ids Op OpAux Cks CESyn)
<: STCISVARIABLE Ids Op OpAux Cks CESyn Syn.
  Include STCISVARIABLE Ids Op OpAux Cks CESyn Syn.
End StcIsVariableFun.
