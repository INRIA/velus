(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Clocks.

From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsLast.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCISDEFINED
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX          Op)
       (Import Syn   : STCSYNTAX     Ids Op CESyn)
       (Import Var   : STCISVARIABLE Ids Op CESyn Syn)
       (Import Last  : STCISLAST     Ids Op CESyn Syn).

  Inductive Is_defined_in_tc: ident -> trconstr -> Prop :=
  | DefTcDef:
      forall x ck e,
        Is_defined_in_tc x (TcDef x ck e)
  | DefTcNext:
      forall x ck e,
        Is_defined_in_tc x (TcNext x ck e)
  | DefTcCall:
      forall x i xs ck rst f es,
        In x xs ->
        Is_defined_in_tc x (TcCall i xs ck rst f es).

  Definition Is_defined_in (x: ident) (tcs: list trconstr) : Prop :=
    Exists (Is_defined_in_tc x) tcs.

  Lemma Is_defined_Is_variable_Is_last_in:
    forall tcs x,
      Is_defined_in x tcs <->
      Is_variable_in x tcs \/ Is_last_in x tcs.
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

  Lemma Is_variable_in_tc_Is_defined_in_tc:
    forall x tc,
      Is_variable_in_tc x tc ->
      Is_defined_in_tc x tc.
  Proof.
    destruct tc; inversion_clear 1; auto using Is_defined_in_tc.
  Qed.

  Lemma Is_variable_in_Is_defined_in:
    forall x tcs,
      Is_variable_in x tcs ->
      Is_defined_in x tcs.
  Proof.
    induction tcs; inversion_clear 1 as [?? Var|].
    - inv Var; left; constructor; auto.
    - right; auto; apply IHtcs; auto.
  Qed.

  Lemma s_ins_not_def:
    forall s x,
      InMembers x s.(s_in) ->
      ~ Is_defined_in x s.(s_tcs).
  Proof.
    intros * Hin Hdef.
    pose proof (s_nodup s) as Nodup.
    eapply (NoDup_app_In x) in Nodup.
    - apply Is_defined_Is_variable_Is_last_in in Hdef as [Var|Last];
        apply Nodup; rewrite app_assoc, in_app.
      + apply Is_variable_in_variables in Var; rewrite <-s_vars_out_in_tcs in Var;
          auto.
      + apply lasts_of_In in Last; rewrite <-s_lasts_in_tcs in Last; auto.
    - apply fst_InMembers; auto.
  Qed.

  Lemma not_Is_defined_in_tc_TcDef:
    forall y x ck e,
      ~ Is_defined_in_tc y (TcDef x ck e) -> x <> y.
  Proof.
    intros * NIsDef E; subst; apply NIsDef; auto using Is_defined_in_tc.
  Qed.

  Lemma not_Is_defined_in_tc_TcNext:
    forall y x ck e,
      ~ Is_defined_in_tc y (TcNext x ck e) -> x <> y.
  Proof.
    intros * NIsDef E; subst; apply NIsDef; auto using Is_defined_in_tc.
  Qed.

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
    | TcNext x _ _
    | TcDef x _ _ => [x]
    | TcCall _ xs _ _ _ _ => xs
    | TcReset _ _ _ => []
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
      Permutation.Permutation (defined (s_tcs s)) (variables (s_tcs s) ++ lasts_of (s_tcs s)).
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
    - rewrite <-s_lasts_in_tcs, <-s_vars_out_in_tcs.
      rewrite <-app_assoc.
      eapply NoDup_app_weaken.
      rewrite Permutation.Permutation_app_comm.
      apply s_nodup.
  Qed.

  Lemma Is_last_in_not_Is_variable_in:
    forall tcs x,
      NoDup (defined tcs) ->
      Is_last_in x tcs ->
      ~ Is_variable_in x tcs.
  Proof.
    induction tcs; intros * Nodup Last Var;
      inversion_clear Last as [?? IsLast|];
      inversion_clear Var as [?? IsVar|?? IsVar_in].
    - inv IsLast; inv IsVar.
    - apply Is_variable_in_Is_defined_in in IsVar_in.
      inv IsLast.
      simpl in Nodup; inv Nodup.
      now apply Is_defined_in_defined in IsVar_in.
    - apply Is_variable_in_tc_Is_defined_in_tc in IsVar.
      assert (Is_defined_in x tcs) as Hins by (apply Is_defined_Is_variable_Is_last_in; auto).
      apply Is_defined_in_defined in Hins; apply Is_defined_in_defined_tc in IsVar.
      simpl in Nodup; eapply NoDup_app_In in Nodup; eauto.
    - simpl in Nodup; rewrite Permutation.Permutation_app_comm in Nodup;
        apply NoDup_app_weaken in Nodup.
      eapply IHtcs; eauto.
  Qed.

  Lemma defined_app:
    forall tcs tcs',
      defined (tcs ++ tcs') = defined tcs ++ defined tcs'.
  Proof.
    unfold defined.
    induction tcs as [|[]]; simpl; intros; auto.
    - f_equal; auto.
    - f_equal; auto.
    - rewrite <-app_assoc; f_equal; auto.
  Qed.

End STCISDEFINED.

Module StcIsDefinedFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX          Op)
       (Syn   : STCSYNTAX     Ids Op CESyn)
       (Var   : STCISVARIABLE Ids Op CESyn Syn)
       (Last  : STCISLAST     Ids Op CESyn Syn)
<: STCISDEFINED Ids Op CESyn Syn Var Last.
  Include STCISDEFINED Ids Op CESyn Syn Var Last.
End StcIsDefinedFun.
