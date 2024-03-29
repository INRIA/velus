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
    match R x with
    | Some v => wt_svalue v ty
    | _ => True
    end.

  Definition wt_synchronous_env (R: env) :=
    Forall (wt_env_svalue R).

  Global Hint Constructors wt_value : typing.

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
    - subst; cases; simpl; auto with typing.
    - eapply Forall_forall in WT; eauto.
      + instantiate (1 := (x, ty)) in WT.
        unfold wt_env_svalue, sem_var_instant in *.
        take (R _ = _) and rewrite it in WT; auto.
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
  Global Hint Resolve sem_exp_instant_wt : nltyping stctyping nlsem stcsem.

  Corollary sem_aexp_instant_wt:
    forall base R e ck v enums Γ,
      sem_aexp_instant base R ck e v ->
      wt_exp enums Γ e ->
      wt_synchronous_env R (filter (fun xt => PS.mem (fst xt) (free_in_exp e PS.empty)) Γ) ->
      wt_svalue v (typeof e).
  Proof.
    inversion_clear 1; intros; eauto with nltyping.
  Qed.

  Lemma sem_cexp_instant_wt:
    forall base R e v enums Γ,
      sem_cexp_instant base R e v ->
      wt_cexp enums Γ e ->
      wt_synchronous_env R (filter (fun xt => PS.mem (fst xt) (free_in_cexp e PS.empty)) Γ) ->
      wt_svalue v (typeofc e).
  Proof.
    induction 1 using sem_cexp_instant_ind_2; inversion_clear 1; intros WT; simpl in *; eauto with nltyping.
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
      apply In_free_in_cexp in H3. rewrite free_in_cexp_spec in H3. destruct H3 as [[Hfree|]|].
      2,3:exfalso; eapply not_In_empty; eauto.
      apply In_free_in_cexp; rewrite In_fold_left_or_default_free_in_cexp, free_in_cexp_spec.
      destruct oe; simpl in *; auto. right; right. rewrite free_in_cexp_spec; auto with nltyping.
  Qed.
  Global Hint Resolve sem_cexp_instant_wt : nltyping stctyping nlsem stcsem.

  Lemma sem_rhs_instant_wt:
    forall base R e v enums externs Γ,
      sem_rhs_instant base R e v ->
      wt_rhs enums externs Γ e ->
      wt_synchronous_env R (filter (fun xt => PS.mem (fst xt) (free_in_rhs e PS.empty)) Γ) ->
      wt_svalue v (typeofr e).
  Proof.
    intros * Sem WT Env; inv Sem; inv WT; simpl; eauto using sem_cexp_instant_wt.
    constructor.
    eapply pres_sem_extern; [|eauto].
    apply Forall2_swap_args in H0. eapply Forall2_trans_ex in H; eauto.
    simpl_Forall.
    take (sem_exp_instant _ _ _ _) and eapply sem_exp_instant_wt in it; eauto.
    2:{ unfold wt_synchronous_env in *. rewrite Forall_filter in *. simpl_Forall.
        apply Env.
        apply free_in_fold_left_exp_spec. apply free_in_exp_spec in H10 as [|]; auto.
        left. solve_Exists. }
    inv it; congruence.
  Qed.
  Global Hint Resolve sem_rhs_instant_wt : nltyping stctyping nlsem stcsem.

  Corollary sem_arhs_instant_wt:
    forall base R e ck v enums externs Γ,
      sem_arhs_instant base R ck e v ->
      wt_rhs enums externs Γ e ->
      wt_synchronous_env R (filter (fun xt => PS.mem (fst xt) (free_in_rhs e PS.empty)) Γ) ->
      wt_svalue v (typeofr e).
  Proof.
    inversion_clear 1; intros; eauto with nltyping.
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
