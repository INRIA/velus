From Coq Require Import List.

From compcert Require Import common.Errors.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.

From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LOrdered.

From Velus Require Import CoreExpr.CESyntax CoreExpr.CETyping.
From Velus Require Import NLustre.NLSyntax NLustre.NLNormalArgs NLustre.NLOrdered NLustre.NLTyping.
From Velus Require Import Transcription.Tr Transcription.TrOrdered.

Module Type TRNORMALARGS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS Ids Op OpAux)
       (Import Senv  : STATICENV Ids Op OpAux Cks)
       (Import LSyn  : LSYNTAX Ids Op OpAux Cks Senv)
       (LOrd         : LORDERED Ids Op OpAux Cks Senv LSyn)
       (Import CE    : CESYNTAX Ids Op OpAux Cks)
       (CETyp        : CETYPING Ids Op OpAux Cks CE)
       (NL           : NLSYNTAX Ids Op OpAux Cks CE)
       (Ord          : NLORDERED Ids Op OpAux Cks CE NL)
       (Typ          : NLTYPING Ids Op OpAux Cks CE NL Ord CETyp)
       (Import NLNA  : NLNORMALARGS Ids Op OpAux Cks CE CETyp NL Ord Typ)
       (Import TR    : TR Ids Op OpAux Cks Senv LSyn CE NL).

  (** *** The actual result *)

  Lemma to_lexp_noops_exp : forall ck e e',
    normalized_lexp e ->
    LSyn.noops_exp ck e ->
    to_lexp e = OK e' ->
    noops_exp ck e'.
  Proof.
    induction ck; intros * Hnormed Hnoops Htole; simpl in *; auto.
    inv Hnormed; monadInv Htole; eauto.
  Qed.

  Corollary to_lexps_noops_exps : forall cks es es',
    Forall normalized_lexp es ->
    Forall2 LSyn.noops_exp cks es ->
    Errors.mmap to_lexp es = OK es' ->
    Forall2 noops_exp cks es'.
  Proof.
    intros * Hnormed Hnoops. revert es'.
    induction Hnoops; intros es' Htole; inv Hnormed; simpl in *; monadInv Htole; auto.
    constructor; auto.
    eapply to_lexp_noops_exp; eauto.
  Qed.

  Lemma to_equation_normal_args : forall G G' outs lasts env envo xr eq eq',
    to_global G = OK G' ->
    normalized_equation outs lasts eq ->
    LSyn.normal_args_eq G eq ->
    to_equation env envo xr eq = OK eq' ->
    normal_args_eq G' eq'.
  Proof.
    intros * Htog Hnormed Hnorma Htoeq.
    inv Hnormed; simpl in *.
    - (* app *)
      destruct (vars_of _); monadInv Htoeq.
      inv Hnorma; [|inv H3; inv H2].
      eapply find_node_global in H4 as (n'&Hfind'&Htonode); eauto.
      econstructor; eauto.
      erewrite <- to_node_in; eauto.
      eapply to_lexps_noops_exps; eauto.
      unfold Common.idfst; erewrite map_map, map_ext; eauto. intros (?&((?&?)&?)); auto.
    - (* fby *)
      monadInv Htoeq.
      constructor.
    - (* extcall *)
      destruct_conjs; monadInv Htoeq.
      constructor.
    - (* cexp *)
      inv H. 3:inv H0.
      all:monadInv Htoeq; constructor.
  Qed.

  Lemma block_to_equation_normal_args outs lasts : forall G G' env envo d xr eq',
      to_global G = OK G' ->
      normalized_block outs lasts d ->
      LSyn.normal_args_blk G d ->
      block_to_equation env envo xr d = OK eq' ->
      normal_args_eq G' eq'.
  Proof.
    intros * Htog Hnormed Hnorma Htoeq. revert dependent xr.
    induction Hnormed; inv Hnorma; intros; simpl in *.
    - (* eq *)
      eapply to_equation_normal_args in Htoeq; eauto.
    - (* last *)
      monadInv Htoeq. constructor.
    - (* reset *)
      simpl_Forall.
      cases; eauto.
  Qed.

  Lemma to_node_normal_args : forall G G' n n',
    to_global G = OK G' ->
    LSyn.normal_args_node G n ->
    to_node n = OK n' ->
    normal_args_node G' n'.
  Proof.
    unfold normal_args_node, LSyn.normal_args_node.
    intros * Htog Hnormed Hton.
    pose proof (LSyn.n_syn n) as Syn. inversion Syn as [??? _ Blk _].
    tonodeInv Hton; simpl in *. rewrite <-H0 in *. monadInv Hmmap.
    eapply mmap_inversion in EQ.
    inv Hnormed. clear - Htog Blk H1 EQ.
    induction EQ; inv H1; inv Blk; constructor; auto.
    eapply block_to_equation_normal_args; eauto.
  Qed.

  Theorem to_global_normal_args : forall G G',
      LSyn.normal_args G ->
      to_global G = OK G' ->
      normal_args G'.
  Proof.
    intros [] ? Hnormed Htog. monadInv Htog.
    revert dependent x.
    induction nodes0; intros * Htog; simpl in *; monadInv Htog; inv Hnormed;
      constructor; simpl; auto.
    - eapply to_node_normal_args; eauto.
      unfold to_global; simpl. rewrite EQ1; auto.
    - eapply IHnodes0; eauto.
  Qed.

End TRNORMALARGS.

Module TrNormalArgsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS Ids Op OpAux)
       (Senv  : STATICENV Ids Op OpAux Cks)
       (LSyn  : LSYNTAX Ids Op OpAux Cks Senv)
       (LOrd  : LORDERED Ids Op OpAux Cks Senv LSyn)
       (CE    : CESYNTAX Ids Op OpAux Cks)
       (CETyp : CETYPING Ids Op OpAux Cks CE)
       (NL    : NLSYNTAX Ids Op OpAux Cks CE)
       (Ord   : NLORDERED Ids Op OpAux Cks CE NL)
       (Typ   : NLTYPING Ids Op OpAux Cks CE NL Ord CETyp)
       (NLNA  : NLNORMALARGS Ids Op OpAux Cks CE CETyp NL Ord Typ)
       (TR    : TR Ids Op OpAux Cks Senv LSyn CE NL)
       <: TRNORMALARGS Ids Op OpAux Cks Senv LSyn LOrd CE CETyp NL Ord Typ NLNA TR.
  Include TRNORMALARGS Ids Op OpAux Cks Senv LSyn LOrd CE CETyp NL Ord Typ NLNA TR.
End TrNormalArgsFun.
