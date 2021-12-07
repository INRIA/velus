From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Clocks.

From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsNext.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCISDEFINED
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX     Ids Op OpAux Cks CESyn)
       (Import Var   : STCISVARIABLE Ids Op OpAux Cks CESyn Syn)
       (Import Next  : STCISNEXT     Ids Op OpAux Cks CESyn Syn).

  Inductive Is_defined_in_tc: ident -> trconstr -> Prop :=
  | DefTcDef:
      forall x ck e,
        Is_defined_in_tc x (TcDef x ck e)
  | DefTcNext:
      forall x ck ckrs e,
        Is_defined_in_tc x (TcNext x ck ckrs e)
  | DefTcStep:
      forall x i xs ck rst f es,
        In x xs ->
        Is_defined_in_tc x (TcStep i xs ck rst f es).

  Global Hint Constructors Is_defined_in_tc : stcdef.

  Definition Is_defined_in (x: ident) (tcs: list trconstr) : Prop :=
    Exists (Is_defined_in_tc x) tcs.

  Lemma Is_defined_Is_variable_Is_next_in:
    forall tcs x,
      Is_defined_in x tcs <->
      Is_variable_in x tcs \/ Is_next_in x tcs.
  Proof.
    induction tcs; split.
    - inversion 1.
    - intros [E|E]; inversion E.
    - inversion_clear 1 as [?? Def|?? Defs].
      + inv Def.
        * left; left; constructor; auto.
        * right; left; constructor; auto.
        * left; left; constructor; auto.
      + apply IHtcs in Defs as [].
        * left; right; auto.
        * right; right; auto.
    - intros [E|E]; inversion_clear E as [?? E'|].
      + inv E'.
        * left; constructor.
        * left; constructor; auto.
      + right; apply IHtcs; auto.
      + inv E'; left; constructor.
      + right; apply IHtcs; auto.
  Qed.

  Corollary Is_variable_in_Is_defined_in:
    forall x tcs,
      Is_variable_in x tcs ->
      Is_defined_in x tcs.
  Proof.
    intros * Hvar.
    rewrite Is_defined_Is_variable_Is_next_in; auto.
  Qed.

  Corollary Is_next_in_Is_defined_in:
    forall x tcs,
      Is_next_in x tcs ->
      Is_defined_in x tcs.
  Proof.
    intros * Hvar.
    rewrite Is_defined_Is_variable_Is_next_in; auto.
  Qed.

  Lemma Is_variable_in_tc_Is_defined_in_tc:
    forall x tc,
      Is_variable_in_tc x tc ->
      Is_defined_in_tc x tc.
  Proof.
    destruct tc; inversion_clear 1; auto with stcdef.
  Qed.

  Global Hint Resolve Is_variable_in_Is_defined_in Is_next_in_Is_defined_in Is_variable_in_tc_Is_defined_in_tc : stcdef.

  Lemma s_ins_not_def:
    forall s x,
      InMembers x s.(s_in) ->
      ~ Is_defined_in x s.(s_tcs).
  Proof.
    intros * Hin Hdef.
    pose proof (s_nodup s) as Nodup.
    eapply (NoDup_app_In x) in Nodup.
    - apply Is_defined_Is_variable_Is_next_in in Hdef as [Var|Next];
        apply Nodup; rewrite app_assoc, in_app.
      + apply Is_variable_in_variables in Var; rewrite <-s_vars_out_in_tcs in Var;
          auto.
      + apply nexts_of_In in Next; rewrite <-s_nexts_in_tcs_fst in Next; auto.
    - apply fst_InMembers; auto.
  Qed.

  Lemma not_Is_defined_in_tc_TcDef:
    forall y x ck e,
      ~ Is_defined_in_tc y (TcDef x ck e) -> x <> y.
  Proof.
    intros * NIsDef E; subst; apply NIsDef; auto using Is_defined_in_tc.
  Qed.

  (* Lemma not_Is_defined_in_tc_TcNext: *)
  (*   forall y x ck ro, *)
  (*     ~ Is_defined_in_tc y (TcNext x ck ro) -> x <> y. *)
  (* Proof. *)
  (*   intros * NIsDef E; subst; apply NIsDef; auto using Is_defined_in_tc. *)
  (* Qed. *)

  Lemma not_Is_defined_in_cons:
    forall x tc tcs,
      ~ Is_defined_in x (tc :: tcs)
      <-> ~ Is_defined_in_tc x tc /\ ~ Is_defined_in x tcs.
  Proof.
    split.
    - intro Hndef; split; intro His_def;
        eapply Hndef; now constructor.
    - intros [Hdef_tc Hdef_tcs] Hdef_all.
      inv Hdef_all; eauto.
  Qed.

  Definition defined_tc (tc: trconstr): list ident :=
    match tc with
    | TcNext x _ _ _
    | TcDef x _ _ => [x]
    | TcStep _ xs _ _ _ _ => xs
    | TcReset _ _ _ _
    | TcInstReset _ _ _ => []
    end.

  Definition defined := flat_map defined_tc.

  Lemma Is_defined_in_defined_tc:
    forall x tc,
      Is_defined_in_tc x tc <-> In x (defined_tc tc).
  Proof.
    destruct tc; split; try inversion_clear 1; subst;
      simpl; auto using Is_defined_in_tc; try contradiction.
  Qed.

  Lemma Is_defined_in_defined:
    forall x tcs,
      Is_defined_in x tcs <-> In x (defined tcs).
  Proof.
    unfold defined.
    induction tcs; simpl.
    - split; inversion 1.
    - split; rewrite in_app.
      + inversion_clear 1.
        * left; apply Is_defined_in_defined_tc; auto.
        * right; apply IHtcs; auto.
      + intros [?|?].
        * left; apply Is_defined_in_defined_tc; auto.
        * right; apply IHtcs; auto.
  Qed.

  Lemma system_output_defined_in_tcs:
    forall s x,
      In x (map fst s.(s_out)) ->
      Is_defined_in x s.(s_tcs).
  Proof.
    intros * Ho.
    cut (In x (map fst s.(s_vars) ++ map fst s.(s_out))).
    - intro Hvo; apply Is_variable_in_Is_defined_in, Is_variable_in_variables.
      now rewrite <-s_vars_out_in_tcs.
    - apply in_or_app; auto.
  Qed.

  Lemma Is_defined_in_In:
    forall x tcs,
      Is_defined_in x tcs ->
      exists tc, In tc tcs /\ Is_defined_in_tc x tc.
  Proof.
    induction tcs as [|tc]. now inversion 1.
    inversion_clear 1 as [? ? Hdef|? ? Hex].
    - exists tc; split; auto with datatypes.
    - apply Exists_exists in Hex as (tc' & Hin & Hdef).
      exists tc'; split; auto with datatypes.
  Qed.

  Lemma s_defined:
    forall s,
      Permutation.Permutation (defined (s_tcs s)) (variables (s_tcs s) ++ map fst (nexts_of (s_tcs s))).
  Proof.
    unfold defined, variables; intro;
      induction (s_tcs s) as [|[]]; simpl; auto.
    - now apply Permutation.Permutation_cons_app.
    - now rewrite <-app_assoc; apply Permutation.Permutation_app_head.
  Qed.

  Lemma s_nodup_defined:
    forall s, NoDup (defined (s_tcs s)).
  Proof.
    intros; eapply Permutation.Permutation_NoDup.
    - apply Permutation.Permutation_sym, s_defined.
    - rewrite <-s_nexts_in_tcs_fst, <-s_vars_out_in_tcs.
      rewrite <-app_assoc.
      eapply NoDup_app_weaken.
      rewrite Permutation.Permutation_app_comm.
      apply s_nodup.
  Qed.

  Lemma incl_defined_nexts:
    forall tcs, incl (map fst (nexts_of tcs)) (defined tcs).
  Proof.
    induction tcs; intros ? Hin; simpl in *; [inv Hin|].
    apply in_app.
    destruct a; simpl in *; auto.
    destruct Hin; auto.
  Qed.

  Lemma nodup_defined_nodup_nexts:
    forall tcs, NoDup (defined tcs) -> NoDup (nexts_of tcs).
  Proof.
    induction tcs; intros; simpl in *. constructor.
    destruct a; simpl in *; auto.
    - inv H; auto.
    - inv H; constructor; auto.
      intro Hin. apply H2, incl_defined_nexts; auto.
      eapply in_map_iff. exists (i, typeof e); eauto.
    - apply NoDup_app_r in H; auto.
  Qed.

  Lemma defined_app:
    forall tcs tcs',
      defined (tcs ++ tcs') = defined tcs ++ defined tcs'.
  Proof.
    unfold defined.
    induction tcs as [|[]]; simpl; intros; auto with datatypes.
    - rewrite <-app_assoc; f_equal; auto.
  Qed.

End STCISDEFINED.

Module StcIsDefinedFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Syn   : STCSYNTAX     Ids Op OpAux Cks CESyn)
       (Var   : STCISVARIABLE Ids Op OpAux Cks CESyn Syn)
       (Next  : STCISNEXT     Ids Op OpAux Cks CESyn Syn)
<: STCISDEFINED Ids Op OpAux Cks CESyn Syn Var Next.
  Include STCISDEFINED Ids Op OpAux Cks CESyn Syn Var Next.
End StcIsDefinedFun.
