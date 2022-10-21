From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Recdef.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Environment.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLIndexedSemantics.
From Velus Require Import NLustre.DeadCodeElim.DCE.

Module Type DCECORRECTNESS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Import CEF   : CEISFREE        Ids Op OpAux Cks CESyn)
       (Import CESem : CESEMANTICS     Ids Op OpAux Cks CESyn Str)
       (Import Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Import Free  : ISFREE          Ids Op OpAux Cks CESyn Syn CEF)
       (Import Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (Import Def   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Import Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Import Sem   : NLINDEXEDSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem)
       (Import DCE   : DCE             Ids Op OpAux Cks CESyn CEF Syn Free Mem Def).

  (** ** Preservation of Ordered_nodes *)

  Lemma dce_eqs_Is_node_in : forall f outs vars eqs,
    Is_node_in f (snd (dce_eqs outs vars eqs)) ->
    Is_node_in f eqs.
  Proof.
    unfold dce_eqs; simpl.
    intros * Hin.
    apply Exists_exists in Hin as (?&Hin&Hdef). apply filter_In in Hin as (Hin&_).
    apply Exists_exists; eauto.
  Qed.

  Lemma dce_global_Ordered : forall G,
    Ordered_nodes G ->
    Ordered_nodes (dce_global G).
  Proof.
    intros * Hord.
    eapply transform_units_Ordered_program; eauto.
    intros * Hin; simpl in *.
    eapply dce_eqs_Is_node_in in Hin; eauto.
  Qed.

  Theorem dce_global_sem : forall G f ins outs,
      Ordered_nodes G ->
      sem_node G f ins outs ->
      sem_node (dce_global G) f ins outs.
  Proof.
    intros [].
    unfold dce_global.
    induction nodes0; intros * Hord Hsem; simpl; auto.
    destruct (ident_eq_dec (n_name a) f).
    - inv Hsem. rewrite find_node_now in H1; inv H1; auto.
      econstructor; simpl; auto. rewrite find_node_now; eauto.
      1-3:simpl; eauto.
      eapply Forall_sem_equation_global_tl in H5; eauto.
      2:{ eapply not_Is_called_in_self in Hord; eauto.
          setoid_rewrite find_unit_now; eauto. simpl; eauto. }
      eapply Forall_sem_equation_global_tl'; eauto.
      1,2:eapply dce_global_Ordered in Hord; eauto.
      { eapply not_Is_called_in_self in Hord; eauto.
        setoid_rewrite find_unit_now; eauto. simpl; eauto. }
      simpl. eapply Forall_filter, Forall_impl; [|eauto].
      intros ? Hsem _. inv Hsem; econstructor; eauto.
      inv Hord; eauto.
    - eapply sem_node_cons in Hsem; eauto.
      eapply sem_node_cons'; eauto.
      + eapply dce_global_Ordered in Hord; eauto.
      + inv Hord; eauto.
  Qed.

End DCECORRECTNESS.

Module DCECorrectnessFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS          Ids Op OpAux)
       (Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (CESyn : CESYNTAX        Ids Op OpAux Cks)
       (CEF   : CEISFREE        Ids Op OpAux Cks CESyn)
       (CESem : CESEMANTICS     Ids Op OpAux Cks CESyn Str)
       (Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Free  : ISFREE          Ids Op OpAux Cks CESyn Syn CEF)
       (Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (Def   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Sem   : NLINDEXEDSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem)
       (DCE   : DCE             Ids Op OpAux Cks CESyn CEF Syn Free Mem Def)
<: DCECORRECTNESS Ids Op OpAux Cks Str CESyn CEF CESem Syn Free Mem Def Ord Sem DCE.
  Include DCECORRECTNESS Ids Op OpAux Cks Str CESyn CEF CESem Syn Free Mem Def Ord Sem DCE.
End DCECorrectnessFun.
