From Coq Require Import List.

From compcert Require Import common.Errors.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.

From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LCausality.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import Lustre.Normalization.Normalization.

From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax NLustre.NLNormalArgs NLustre.NLOrdered.
From Velus Require Import Transcription.Tr Transcription.TrOrdered.

Module Type TRNORMALARGS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import LSyn  : LSYNTAX Ids Op)
       (LOrd         : LORDERED Ids Op LSyn)
       (Import LCau  : LCAUSALITY Ids Op LSyn)
       (Import Norm  : NORMALIZATION Ids Op OpAux LSyn LCau)
       (Import CE    : CESYNTAX Op)
       (NL           : NLSYNTAX Ids Op CE)
       (Ord          : NLORDERED Ids Op CE NL)
       (Import NLNA  : NLNORMALARGS Ids Op CE NL)
       (Import TR    : TR Ids Op OpAux LSyn CE NL).

  (** *** Some lemmas about order and normal args (very boring) *)

  Module Import TrOrdered := TrOrderedFun Ids Op OpAux LSyn LOrd CE NL Ord TR.

  Lemma normal_args_cons : forall n G,
      ~Ord.Is_node_in (NL.n_name n) (NL.n_eqs n) ->
      normal_args_node G n ->
      normal_args_node (n :: G) n.
  Proof.
    unfold normal_args_node.
    intros * Hnin Hnorm.
    eapply Forall_impl_In; [|eauto].
    intros ? Hin Heq.
    inv Heq; econstructor; eauto.
    rewrite Ord.find_node_tl; auto.
    contradict Hnin; subst.
    apply Exists_exists. eexists; split; eauto.
    constructor.
  Qed.

  (** *** The actual result *)

  Lemma to_lexp_noops_exp : forall ck e e',
    normalized_lexp e ->
    Unnesting.noops_exp ck e ->
    to_lexp e = OK e' ->
    noops_exp ck e'.
  Proof.
    induction ck; intros * Hnormed Hnoops Htole; simpl in *; auto.
    inv Hnormed; monadInv Htole; eauto.
  Qed.

  Corollary to_lexps_noops_exps : forall cks es es',
    Forall normalized_lexp es ->
    Forall2 Unnesting.noops_exp cks es ->
    mmap to_lexp es = OK es' ->
    Forall2 noops_exp cks es'.
  Proof.
    intros * Hnormed Hnoops. revert es'.
    induction Hnoops; intros es' Htole; inv Hnormed; simpl in *; monadInv Htole; auto.
    constructor; auto.
    eapply to_lexp_noops_exp; eauto.
  Qed.

  Lemma to_equation_normal_args : forall G G' Hprefs to_cut env envo eq eq',
    to_global G Hprefs = OK G' ->
    normalized_equation G to_cut eq ->
    to_equation env envo eq = OK eq' ->
    normal_args_eq G' eq'.
  Proof.
    intros * Htog Hnormed Htoeq.
    inv Hnormed; simpl in *.
    - (* app *)
      destruct (vars_of _); monadInv Htoeq.
      eapply find_node_global in H0 as (n'&?&Hfind'&Htonode); eauto.
      econstructor; eauto.
      erewrite <- to_node_in; eauto.
      eapply to_lexps_noops_exps; eauto.
    - (* fby *)
      destruct (vars_of _); monadInv Htoeq.
      constructor.
    - (* cexp *)
      inv H. 3:inv H0.
      1-7:monadInv Htoeq; constructor.
  Qed.

  Lemma to_node_normal_args : forall G G' n n' Hprefs Hpref,
    to_global G Hprefs = OK G' ->
    normalized_node G n ->
    to_node n Hpref = OK n' ->
    normal_args_node G' n'.
  Proof.
    unfold normal_args_node, to_node.
    intros * Htog Hnormed Hton.
    destruct mmap_to_equation as [(?&?)|]; try congruence.
    inv Hton; simpl.
    unfold normalized_node in Hnormed.
    revert x e Hnormed.
    induction (n_eqs n); intros x Htoeq Hnormed; simpl in *; monadInv Htoeq; auto.
    inv Hnormed. constructor; auto.
    eapply to_equation_normal_args; eauto.
  Qed.

  Theorem to_global_normal_args : forall G G' Hprefs,
      LOrd.Ordered_nodes G ->
      normalized_global G ->
      to_global G Hprefs = OK G' ->
      normal_args G'.
  Proof.
    unfold to_global.
    induction G; intros G' Hprefs Hord Hnormed Htog; inv Hord; inv Hnormed; simpl in *;
      monadInv Htog; constructor; auto.
    apply normal_args_cons; auto.
    - eapply ninin_l_nl; eauto.
      erewrite <- to_node_name; eauto.
      intro contra. apply H2 in contra as (?&?); congruence.
    - eapply to_node_normal_args in EQ; eauto.
    - eapply IHG; eauto.
  Qed.

End TRNORMALARGS.

Module TrNormalArgsFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (LSyn : LSYNTAX Ids Op)
       (LOrd : LORDERED Ids Op LSyn)
       (LCau  : LCAUSALITY Ids Op LSyn)
       (Norm  : NORMALIZATION Ids Op OpAux LSyn LCau)
       (CE : CESYNTAX Op)
       (NL : NLSYNTAX Ids Op CE)
       (Ord : NLORDERED Ids Op CE NL)
       (NLNA : NLNORMALARGS Ids Op CE NL)
       (TR : TR Ids Op OpAux LSyn CE NL)
       <: TRNORMALARGS Ids Op OpAux LSyn LOrd LCau Norm CE NL Ord NLNA TR.
  Include TRNORMALARGS Ids Op OpAux LSyn LOrd LCau Norm CE NL Ord NLNA TR.
End TrNormalArgsFun.
