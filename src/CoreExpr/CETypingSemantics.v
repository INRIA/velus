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
From Velus Require Import Environment.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import CoreExpr.CESemantics.

From Coq Require Import List.

Module Type CETYPINGSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import ComTyp: COMMONTYPING    Ids Op OpAux)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Import CEFree: CEISFREE        Ids Op OpAux Cks CESyn)
       (Import Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (Import CESem : CESEMANTICS Ids Op OpAux Cks CESyn     Str)
       (Import CETyp : CETYPING    Ids Op OpAux Cks CESyn).

  Definition wt_env_svalue (R: env) '((x, ty): ident * type) :=
    match Env.find x R with
    | Some v => wt_svalue v ty
    | _ => True
    end.

  Definition wt_synchronous_env (R: env) :=
    Forall (wt_env_svalue R).

  Hint Constructors wt_value.

  Lemma sem_exp_instant_wt:
    forall base R e v enums Γ,
      sem_exp_instant base R e v ->
      wt_exp enums Γ e ->
      wt_synchronous_env R (filter (fun xt => PS.mem (fst xt) (free_in_exp e PS.empty)) Γ) ->
      wt_svalue v (typeof e).
  Proof.
    induction 1; inversion_clear 1; intros WT; simpl in *; auto; try congruence.
    - subst; cases; simpl; auto.
      constructor.
      apply wt_cvalue_cconst.
    - subst; cases; simpl; auto.
    - eapply Forall_forall in WT; eauto.
      + instantiate (1 := (x, ty)) in WT.
        unfold wt_env_svalue, sem_var_instant in *.
        take (Env.find _ _ = _) and rewrite it in WT; auto.
      + apply filter_In; split; auto.
        apply PSE.add_mem_1.
    - apply IHsem_exp_instant; auto.
      apply Forall_filter; apply Forall_filter in WT.
      apply Forall_forall; intros; eapply Forall_forall in WT; eauto.
      apply WT, free_in_exp_spec; rewrite <-free_in_exp_spec'; auto.
    - eapply pres_sem_unop; eauto.
    - eapply pres_sem_binop; eauto.
      + take (wt_exp _ _ le1) and apply IHsem_exp_instant1 in it; auto; try now inv it.
        apply Forall_filter; apply Forall_filter in WT.
        apply Forall_forall; intros; eapply Forall_forall in WT; eauto.
        apply WT, free_in_exp_spec; auto.
      + take (wt_exp _ _ le2) and apply IHsem_exp_instant2 in it; auto; try now inv it; auto.
        apply Forall_filter; apply Forall_filter in WT.
        apply Forall_forall; intros; eapply Forall_forall in WT; eauto.
        apply WT, free_in_exp_spec; rewrite <-free_in_exp_spec'; auto.
  Qed.
  Hint Resolve sem_exp_instant_wt.

  Corollary sem_aexp_instant_wt:
    forall base R e ck v enums Γ,
      sem_aexp_instant base R ck e v ->
      wt_exp enums Γ e ->
      wt_synchronous_env R (filter (fun xt => PS.mem (fst xt) (free_in_exp e PS.empty)) Γ) ->
      wt_svalue v (typeof e).
  Proof.
    inversion_clear 1; intros; eauto.
  Qed.

  Lemma sem_cexp_instant_wt:
    forall base R e v enums Γ,
      sem_cexp_instant base R e v ->
      wt_cexp enums Γ e ->
      wt_synchronous_env R (filter (fun xt => PS.mem (fst xt) (free_in_cexp e PS.empty)) Γ) ->
      wt_svalue v (typeofc e).
  Proof.
    induction 1 using sem_cexp_instant_ind_2; inversion_clear 1; intros WT; simpl in *; eauto.
    - subst.
      do 2 (take (Forall _ (_ ++ _)) and apply Forall_app_weaken in it; inv it); auto.
      apply IHsem_cexp_instant; auto.
      apply Forall_filter; apply Forall_filter in WT.
      apply Forall_forall; intros; eapply Forall_forall in WT; eauto.
      apply WT.
      rewrite fold_left_app; simpl.
      apply In_fold_left_free_in_cexp; rewrite free_in_cexp_spec, <-free_in_cexp_spec'; auto.
    - take (nth_error _ _ = _) and apply nth_error_In in it.
      take (Forall2 _ _ _) and eapply Forall2_in_right in it as (oe & Hin & IH); eauto.
      assert (typeofc (or_default d oe) = typeofc d) as <-
          by (destruct oe; simpl in *; auto).
      assert (wt_cexp enums Γ (or_default d oe)) by (destruct oe; simpl in *; auto).
      apply in_split in Hin as (?&?&?); subst.
      apply IH; auto.
      apply Forall_filter; apply Forall_filter in WT.
      apply Forall_forall; intros; eapply Forall_forall in WT; eauto.
      apply WT.
      rewrite fold_left_app; simpl.
      apply In_fold_left_or_default_free_in_cexp; rewrite free_in_cexp_spec, <-free_in_cexp_spec'; auto.
  Qed.
  Hint Resolve sem_cexp_instant_wt.

  Corollary sem_caexp_instant_wt:
    forall base R e ck v enums Γ,
      sem_caexp_instant base R ck e v ->
      wt_cexp enums Γ e ->
      wt_synchronous_env R (filter (fun xt => PS.mem (fst xt) (free_in_cexp e PS.empty)) Γ) ->
      wt_svalue v (typeofc e).
  Proof.
    inversion_clear 1; intros; eauto.
  Qed.

End CETYPINGSEMANTICS.

Module CETypingSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (ComTyp: COMMONTYPING    Ids Op OpAux)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CESyn : CESYNTAX        Ids Op OpAux Cks)
       (CEFree: CEISFREE    Ids Op OpAux Cks CESyn)
       (Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (CESem : CESEMANTICS Ids Op OpAux Cks CESyn     Str)
       (CETyp : CETYPING    Ids Op OpAux Cks CESyn)
       <: CETYPINGSEMANTICS Ids Op OpAux ComTyp Cks CESyn CEFree Str CESem CETyp.
  Include CETYPINGSEMANTICS Ids Op OpAux ComTyp Cks CESyn CEFree Str CESem CETyp.
End CETypingSemanticsFun.
