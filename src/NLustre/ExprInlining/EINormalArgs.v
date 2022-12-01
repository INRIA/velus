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
From Velus Require Import NLustre.ExprInlining.EI.

(** Remove duplicate registers in an NLustre program *)

Module Type EINORMALARGS
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
       (Import EI   : EI             Ids Op OpAux Cks CESyn Syn).

  Lemma exp_inlining_normal_args_node : forall G n,
      normal_args_node G n ->
      normal_args_node (exp_inlining G) (exp_inlining_node n).
  Proof.
    unfold normal_args_node.
    intros * Hnormed; simpl. unfold inline_all_possible.
    rewrite <-fold_left_rev_right.
    induction (rev _) as [|(?&?)]; simpl; auto.
    - simpl_Forall.
      inv Hnormed; econstructor.
      eapply find_node_exp_inlining_forward; eauto. simpl; auto.
    - unfold inline_in_equations. simpl_Forall.
      take equation and destruct it; simpl; auto.
      destruct r; constructor.
  Qed.

  Theorem exp_inlining_normal_args : forall G,
      normal_args G ->
      normal_args (exp_inlining G).
  Proof.
    unfold normal_args; simpl.
    induction 1 as [|?? NAS]; simpl; constructor; auto.
    apply exp_inlining_normal_args_node in NAS; auto.
  Qed.

End EINORMALARGS.

Module EINormalArgsFun
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
       (EI   : EI             Ids Op OpAux Cks CESyn Syn)
  <: EINORMALARGS Ids Op OpAux Cks CESyn CETyp Syn Ord Typ Norm EI.
  Include EINORMALARGS Ids Op OpAux Cks CESyn CETyp Syn Ord Typ Norm EI.
End EINormalArgsFun.
