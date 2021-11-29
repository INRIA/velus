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
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLTyping.
From Velus Require Import NLustre.NLNormalArgs.
From Velus Require Import NLustre.DeadCodeElim.DCE.

Module Type DCENORMALARGS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Import CEF   : CEISFREE        Ids Op OpAux Cks CESyn)
       (Import CETyp : CETYPING        Ids Op OpAux Cks CESyn)
       (Import Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Import Free  : ISFREE          Ids Op OpAux Cks CESyn Syn CEF)
       (Import Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (Import Def   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Import Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Import Typ   : NLTYPING        Ids Op OpAux Cks CESyn Syn Ord CETyp)
       (Import Norm  : NLNORMALARGS    Ids Op OpAux Cks CESyn CETyp Syn Ord Typ)
       (Import DCE   : DCE             Ids Op OpAux Cks CESyn CEF Syn Free Mem Def).

  Lemma dce_node_normal_args G1 G2 : forall n,
    global_iface_eq G1 G2 ->
    normal_args_node G1 n ->
    normal_args_node G2 (dce_node n).
  Proof.
    unfold normal_args_node.
    intros * Heq Hn. simpl.
    eapply Forall_filter, Forall_impl; [|eauto].
    intros ? Hnorm _; eauto using global_iface_eq_normal_args_eq.
  Qed.

  Theorem dce_normal_args : forall G,
    normal_args G ->
    normal_args (dce_global G).
  Proof.
    unfold normal_args.
    intros (?&?) Hnorm; simpl in *.
    induction Hnorm; simpl; constructor; auto.
    eapply dce_node_normal_args; eauto. apply dce_global_iface_eq.
  Qed.

End DCENORMALARGS.

Module DCENormalArgsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CESyn : CESYNTAX        Ids Op OpAux Cks)
       (CEF   : CEISFREE        Ids Op OpAux Cks CESyn)
       (CETyp : CETYPING        Ids Op OpAux Cks CESyn)
       (Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Free  : ISFREE          Ids Op OpAux Cks CESyn Syn CEF)
       (Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (Def   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Typ   : NLTYPING        Ids Op OpAux Cks CESyn Syn Ord CETyp)
       (Norm  : NLNORMALARGS    Ids Op OpAux Cks CESyn CETyp Syn Ord Typ)
       (DCE   : DCE             Ids Op OpAux Cks CESyn CEF Syn Free Mem Def)
<: DCENORMALARGS Ids Op OpAux Cks CESyn CEF CETyp Syn Free Mem Def Ord Typ Norm DCE.
  Include DCENORMALARGS Ids Op OpAux Cks CESyn CEF CETyp Syn Free Mem Def Ord Typ Norm DCE.
End DCENormalArgsFun.
