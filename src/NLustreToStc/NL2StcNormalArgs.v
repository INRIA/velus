From Velus Require Import NLustre.
From Velus Require Import Stc.

From Velus Require Import NLustreToStc.Translation.

From Velus Require Import VelusMemory.
From Velus Require Import Common.
From Velus Require Import CoindToIndexed.
From Velus Require Import CommonProgram.
From Velus Require Import CommonTyping.

From Coq Require Import List.
Import List.ListNotations.

Module Type NL2STCNORMALARGS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import ComTyp: COMMONTYPING    Ids Op OpAux)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import CStr  : COINDSTREAMS    Ids Op OpAux Cks)
       (Import IStr  : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (Import CIStr : COINDTOINDEXED  Ids Op OpAux        Cks CStr IStr)
       (Import CE    : COREEXPR        Ids Op OpAux ComTyp Cks      IStr)
       (Import NL    : NLUSTRE         Ids Op OpAux ComTyp Cks CStr IStr CIStr CE)
       (Import Stc   : STC             Ids Op OpAux ComTyp Cks      IStr       CE)
       (Import Trans : TRANSLATION     Ids Op OpAux        Cks              CE.Syn NL.Syn Stc.Syn NL.Mem).

  Lemma translate_eqn_normal_args:
    forall G env eq,
      Norm.normal_args_eq G eq ->
      Forall (normal_args_tc (translate G)) (translate_eqn env eq).
  Proof.
    induction 1 as [| |?????? Find|]; simpl; cases.
    all:try constructor; simpl_Forall; eauto with stcsyn.
    apply option_map_inv in Find as ((?&?)& Find &?); simpl in *; subst.
    apply find_unit_transform_units_forward in Find.
    econstructor; eauto. simpl_Forall; auto.
  Qed.

  Lemma translate_node_normal_args:
    forall G n,
      normal_args_node G n ->
      normal_args_system (translate G) (translate_node n).
  Proof.
    intros.
    unfold normal_args_node, normal_args_system in *. simpl in *.
    simpl_Forall. unfold translate_eqns in *. simpl_In. simpl_Forall.
    eapply translate_eqn_normal_args, Forall_forall in H; eauto.
  Qed.

  Lemma translate_normal_args:
    forall G,
      NL.Norm.normal_args G ->
      normal_args (translate G).
  Proof.
    unfold NL.Norm.normal_args, normal_args; simpl.
    induction 1 as [|?? NAS]; simpl; constructor; auto.
    apply translate_node_normal_args in NAS; auto.
  Qed.

End NL2STCNORMALARGS.

Module NL2StcNormalArgsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (ComTyp: COMMONTYPING    Ids Op OpAux)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CStr  : COINDSTREAMS    Ids Op OpAux Cks)
       (IStr  : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (CIStr : COINDTOINDEXED  Ids Op OpAux        Cks CStr IStr)
       (CE    : COREEXPR        Ids Op OpAux ComTyp Cks      IStr)
       (NL    : NLUSTRE         Ids Op OpAux ComTyp Cks CStr IStr CIStr CE)
       (Stc   : STC             Ids Op OpAux ComTyp Cks      IStr       CE)
       (Trans : TRANSLATION     Ids Op OpAux Cks           CE.Syn NL.Syn Stc.Syn NL.Mem)
<: NL2STCNORMALARGS Ids Op OpAux ComTyp Cks CStr IStr CIStr CE NL Stc Trans.
  Include NL2STCNORMALARGS Ids Op OpAux ComTyp Cks CStr IStr CIStr CE NL Stc Trans.
End NL2StcNormalArgsFun.
