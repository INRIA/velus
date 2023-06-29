From Coq Require Import List Permutation.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CommonProgram.
From Velus Require Import Fresh.

From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import Stc.StcIsFree.
From Velus Require Import Stc.StcWellDefined.
From Velus Require Import Stc.CutCycles.CC.

Module Type CCNORMALARGS
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX   Ids Op)
  (Import Cks   : CLOCKS          Ids Op OpAux)
  (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
  (Import Syn   : STCSYNTAX       Ids Op OpAux Cks CESyn)
  (Import Ord   : STCORDERED      Ids Op OpAux Cks CESyn Syn)
  (Import CEF   : CEISFREE        Ids Op OpAux Cks CESyn)
  (Import Free  : STCISFREE       Ids Op OpAux Cks CESyn Syn CEF)
  (Import Wdef  : STCWELLDEFINED  Ids Op OpAux Cks CESyn Syn Ord CEF Free)
  (Import ECC   : EXT_CC          Ids Op OpAux Cks CESyn Syn)
  (Import CC    : CC              Ids Op OpAux Cks CESyn Syn ECC).

  Lemma rename_exp_noops subl subn : forall ck e,
      noops_exp ck e ->
      noops_exp ck (rename_exp subl subn e).
  Proof.
    induction ck; intros * Noops; simpl in *; auto.
    destruct e; simpl in *; auto.
    - now inv Noops.
    - destruct_conjs; auto.
  Qed.

  Lemma cut_cycles_system_normal_args G : forall n,
    normal_args_system G n ->
    normal_args_system (cut_cycles G) (cut_cycles_system n).
  Proof.
    unfold normal_args_system.
    intros * Hn. simpl.
    destruct (cut_cycles_tcs _ _ _ _) as (tcs'&st') eqn:Htcs.
    unfold cut_cycles_tcs in *. repeat Fresh.Tactics.inv_bind.
    rewrite ? Forall_app. repeat split; simpl_Forall.
    1,2:constructor.
    inv Hn; simpl; try constructor.
    take (find_system _ _ = _) and eapply cut_cycles_find_system in it.
    econstructor; eauto.
    simpl_Forall; auto using rename_exp_noops.
  Qed.

  Theorem cut_cycles_normal_args : forall G,
    normal_args G ->
    normal_args (cut_cycles G).
  Proof.
    unfold normal_args.
    intros [] Hnorm; simpl in *.
    induction Hnorm; simpl; constructor; auto.
    eapply cut_cycles_system_normal_args in H; eauto.
  Qed.

End CCNORMALARGS.


Module CCNormalArgsFun
  (Ids   : IDS)
  (Op    : OPERATORS)
  (OpAux : OPERATORS_AUX   Ids Op)
  (Cks   : CLOCKS          Ids Op OpAux)
  (CESyn : CESYNTAX        Ids Op OpAux Cks)
  (Syn   : STCSYNTAX       Ids Op OpAux Cks CESyn)
  (Ord   : STCORDERED      Ids Op OpAux Cks CESyn Syn)
  (CEF   : CEISFREE        Ids Op OpAux Cks CESyn)
  (Free  : STCISFREE       Ids Op OpAux Cks CESyn Syn CEF)
  (Wdef  : STCWELLDEFINED  Ids Op OpAux Cks CESyn Syn Ord CEF Free)
  (ECC   : EXT_CC          Ids Op OpAux Cks CESyn Syn)
  (CC    : CC              Ids Op OpAux Cks CESyn Syn ECC)
<: CCNORMALARGS Ids Op OpAux Cks CESyn Syn Ord CEF Free Wdef ECC CC.
  Include CCNORMALARGS Ids Op OpAux Cks CESyn Syn Ord CEF Free Wdef ECC CC.
End CCNormalArgsFun.
