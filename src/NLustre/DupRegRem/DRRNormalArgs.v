From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Recdef.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Environment.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLTyping.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLNormalArgs.
From Velus Require Import NLustre.DupRegRem.DRR.

(** Remove duplicate registers in an NLustre program *)

Module Type DRRNORMALARGS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Import CETyp : CETYPING        Ids Op OpAux Cks CESyn)
       (Import Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Import Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Import Typ   : NLTYPING        Ids Op OpAux Cks CESyn Syn Ord CETyp)
       (Import Norm  : NLNORMALARGS    Ids Op OpAux Cks CESyn CETyp Syn Ord Typ)
       (Import DRR   : DRR             Ids Op OpAux Cks CESyn Syn).

  Lemma rename_in_exp_noops_exp : forall sub e ck,
    noops_exp ck e ->
    noops_exp ck (rename_in_exp sub e).
  Proof.
    induction e; intros * Hnormed; simpl; auto.
    1-4:destruct ck; simpl in *; auto.
  Qed.

  Lemma rename_in_equation_normal_args : forall G sub equ,
    normal_args_eq G equ ->
    normal_args_eq G (rename_in_equation sub equ).
  Proof.
    intros * Hnorm; inv Hnorm; simpl;
      econstructor; eauto.
    rewrite Forall2_map_2. eapply Forall2_impl_In; [|eauto]; intros.
    apply rename_in_exp_noops_exp; auto.
  Qed.

  Lemma remove_dup_regs_normal_args_eqs : forall G sub eqs,
      Forall (normal_args_eq G) eqs ->
      Forall (normal_args_eq G) (snd (remove_dup_regs_eqs sub eqs)).
  Proof.
    intros * Hnormed.
    functional induction (remove_dup_regs_eqs sub eqs); auto.
    apply IHp.
    inv e. unfold subst_and_filter_equations.
    rewrite Forall_map, Forall_filter.
    eapply Forall_impl; eauto; intros * Hn _.
    eapply rename_in_equation_normal_args; eauto.
  Qed.

  Lemma remove_dup_regs_normal_args_node : forall G n,
      normal_args_node G n ->
      normal_args_node (remove_dup_regs G) (remove_dup_regs_node n).
  Proof.
    unfold normal_args_node.
    intros * Hnormed; simpl.
    apply remove_dup_regs_normal_args_eqs; auto.
    eapply Forall_impl; [|eauto]. intros.
    eapply global_iface_eq_normal_args_eq; eauto.
    apply remove_dup_regs_iface_eq.
  Qed.

  Theorem remove_dup_regs_normal_args : forall G,
      normal_args G ->
      normal_args (remove_dup_regs G).
  Proof.
    unfold normal_args; simpl.
    induction 1 as [|?? NAS]; simpl; constructor; auto.
    apply remove_dup_regs_normal_args_node in NAS; auto.
  Qed.

End DRRNORMALARGS.

Module DrrNormalArgsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CESyn : CESYNTAX        Ids Op OpAux Cks)
       (CETyp : CETYPING        Ids Op OpAux Cks CESyn)
       (Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Typ   : NLTYPING        Ids Op OpAux Cks CESyn Syn Ord CETyp)
       (Norm  : NLNORMALARGS    Ids Op OpAux Cks CESyn CETyp Syn Ord Typ)
       (DRR   : DRR             Ids Op OpAux Cks CESyn Syn)
  <: DRRNORMALARGS Ids Op OpAux Cks CESyn CETyp Syn Ord Typ Norm DRR.
  Include DRRNORMALARGS Ids Op OpAux Cks CESyn CETyp Syn Ord Typ Norm DRR.
End DrrNormalArgsFun.
