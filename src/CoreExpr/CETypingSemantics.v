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
From Velus Require Import FunctionalEnvironment.
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

  Definition wt_env_svalue (R: env) (x : var_last) (ty: type) :=
    match R x with Some v => wt_svalue v ty | _ => True end.

  Definition wt_synchronous_env (R: env) :=
    Forall (fun '(x, (ty, islast)) =>
              wt_env_svalue R (Var x) ty
              /\ if islast : bool then wt_env_svalue R (Last x) ty else True).

  Global Hint Constructors wt_value : typing.

  Lemma sem_exp_instant_wt:
    forall base R e v enums Γ,
      sem_exp_instant base R e v ->
      wt_exp enums Γ e ->
      (forall x ty islast, In (x, (ty, islast)) Γ -> Is_free_in_exp (Var x) e -> wt_env_svalue R (Var x) ty) ->
      (forall x ty, In (x, (ty, true)) Γ -> Is_free_in_exp (Last x) e -> wt_env_svalue R (Last x) ty) ->
      wt_svalue v (typeof e).
  Proof.
    induction 1; inversion_clear 1; intros WTV WTL; simpl in *; auto; try congruence.
    - subst; cases; simpl; auto.
      constructor.
      apply wt_cvalue_cconst.
    - subst; cases; simpl; auto with typing.
    - take (In _ _) and eapply WTV in it as WT; auto with nlfree.
      unfold wt_env_svalue, sem_var_instant in *.
      take (R _ = _) and rewrite it in WT; auto.
    - take (In _ _) and eapply WTL in it as WT; auto with nlfree.
      unfold wt_env_svalue, sem_var_instant in *.
      take (R _ = _) and rewrite it in WT; auto.
    - apply IHsem_exp_instant; eauto with nlfree.
    - eapply pres_sem_unop; eauto.
      eapply IHsem_exp_instant; eauto with nlfree.
    - eapply pres_sem_binop; eauto with nlfree.
      + apply IHsem_exp_instant1; eauto with nlfree.
      + apply IHsem_exp_instant2; eauto with nlfree.
  Qed.
  Global Hint Resolve sem_exp_instant_wt : nltyping stctyping nlsem stcsem.

  Corollary sem_aexp_instant_wt:
    forall base R e ck v enums Γ,
      sem_aexp_instant base R ck e v ->
      wt_exp enums Γ e ->
      (forall x ty islast, In (x, (ty, islast)) Γ -> Is_free_in_exp (Var x) e -> wt_env_svalue R (Var x) ty) ->
      (forall x ty, In (x, (ty, true)) Γ -> Is_free_in_exp (Last x) e -> wt_env_svalue R (Last x) ty) ->
      wt_svalue v (typeof e).
  Proof.
    inversion_clear 1; intros; eauto with nltyping.
  Qed.

  Lemma sem_cexp_instant_wt:
    forall base R e v enums Γ,
      sem_cexp_instant base R e v ->
      wt_cexp enums Γ e ->
      (forall x ty islast, In (x, (ty, islast)) Γ -> Is_free_in_cexp (Var x) e -> wt_env_svalue R (Var x) ty) ->
      (forall x ty, In (x, (ty, true)) Γ -> Is_free_in_cexp (Last x) e -> wt_env_svalue R (Last x) ty) ->
      wt_svalue v (typeofc e).
  Proof.
    induction 1 using sem_cexp_instant_ind_2; inversion_clear 1; intros WTV WTL; simpl in *; eauto.
    - subst.
      do 2 (take (Forall _ (_ ++ _)) and apply Forall_app_weaken in it; inv it); auto.
      apply IHsem_cexp_instant; auto; intros; [eapply WTV|eapply WTL]; eauto.
      1,2:constructor; apply Exists_app; eauto.
    - take (nth_error _ _ = _) and apply nth_error_In in it.
      take (Forall2 _ _ _) and eapply Forall2_in_right in it as (oe & Hin & IH); eauto.
      assert (typeofc (or_default d oe) = typeofc d) as <-
          by (destruct oe; simpl in *; auto).
      assert (wt_cexp enums Γ (or_default d oe)) by (destruct oe; simpl in *; auto).
      apply in_split in Hin as (?&?&?); subst.
      apply IH; auto; intros; [eapply WTV|eapply WTL]; eauto.
      1,2:(destruct oe; [constructor; apply Exists_app; eauto|auto with nlfree]).
    - eapply sem_exp_instant_wt; eauto with nlfree.
  Qed.
  Global Hint Resolve sem_cexp_instant_wt : nltyping stctyping nlsem stcsem.

  Corollary sem_caexp_instant_wt:
    forall base R e ck v enums Γ,
      sem_caexp_instant base R ck e v ->
      wt_cexp enums Γ e ->
      (forall x ty islast, In (x, (ty, islast)) Γ -> Is_free_in_cexp (Var x) e -> wt_env_svalue R (Var x) ty) ->
      (forall x ty, In (x, (ty, true)) Γ -> Is_free_in_cexp (Last x) e -> wt_env_svalue R (Last x) ty) ->
      wt_svalue v (typeofc e).
  Proof.
    inversion_clear 1; intros; eauto with nltyping.
  Qed.

  Lemma sem_rhs_instant_wt:
    forall base R e v enums externs Γ,
      sem_rhs_instant base R e v ->
      wt_rhs enums externs Γ e ->
      (forall x ty islast, In (x, (ty, islast)) Γ -> Is_free_in_rhs (Var x) e -> wt_env_svalue R (Var x) ty) ->
      (forall x ty, In (x, (ty, true)) Γ -> Is_free_in_rhs (Last x) e -> wt_env_svalue R (Last x) ty) ->
      wt_svalue v (typeofr e).
  Proof.
    intros * Sem WT WTV WTL; inv Sem; inv WT; simpl; auto.
    - constructor.
      eapply pres_sem_extern; [|eauto].
      apply Forall2_swap_args in H0. eapply Forall2_trans_ex in H; eauto.
      simpl_Forall.
      take (sem_exp_instant _ _ _ _) and eapply sem_exp_instant_wt in it; eauto;
        intros; [|eapply WTV|eapply WTL]; eauto.
      + inv it. congruence.
      + constructor. solve_Exists.
      + constructor. solve_Exists.
    - eapply sem_cexp_instant_wt; eauto with nlfree.
  Qed.
  Global Hint Resolve sem_rhs_instant_wt : nltyping stctyping nlsem stcsem.

  Corollary sem_arhs_instant_wt:
    forall base R e ck v enums externs Γ,
      sem_arhs_instant base R ck e v ->
      wt_rhs enums externs Γ e ->
      (forall x ty islast, In (x, (ty, islast)) Γ -> Is_free_in_rhs (Var x) e -> wt_env_svalue R (Var x) ty) ->
      (forall x ty, In (x, (ty, true)) Γ -> Is_free_in_rhs (Last x) e -> wt_env_svalue R (Last x) ty) ->
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
