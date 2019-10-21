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

From Velus Require Import NLustre.
From Velus Require Import Stc.

From Velus Require Import NLustreToStc.Translation.

From Velus Require Import VelusMemory.
From Velus Require Import Common.

From Coq Require Import List.
Import List.ListNotations.

Module Type NL2STCNORMALARGS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import CStr  : COINDSTREAMS    Op OpAux)
       (Import IStr  : INDEXEDSTREAMS  Op OpAux)
       (Import CE    : COREEXPR    Ids Op OpAux      IStr)
       (Import NL    : NLUSTRE     Ids Op OpAux CStr IStr CE)
       (Import Stc   : STC         Ids Op OpAux      IStr CE)
       (Import Trans : TRANSLATION Ids Op                 CE.Syn NL.Syn Stc.Syn NL.Mem).

  Lemma translate_eqn_normal_args:
    forall G eq,
      Norm.normal_args_eq G eq ->
      Forall (normal_args_tc (translate G)) (translate_eqn eq).
  Proof.
    induction 1 as [|?????? Find|]; simpl; eauto using Forall_cons, normal_args_tc.
    apply find_node_translate in Find as (?&?&?&?); subst.
    cases; eauto using Forall_cons, normal_args_tc.
  Qed.

  Lemma translate_node_normal_args:
    forall G n,
      normal_args_node G n ->
      normal_args_system (translate G) (translate_node n).
  Proof.
    unfold normal_args_node, normal_args_system.
    simpl; unfold translate_eqns; induction 1; simpl; auto.
    apply Forall_app; split; auto.
    apply translate_eqn_normal_args; auto.
  Qed.

  Lemma translate_normal_args:
    forall G,
      NL.Norm.normal_args G ->
      normal_args (translate G).
  Proof.
    induction G as [|n]; simpl; auto.
    intros (?&?); split; auto.
    change (translate_node n :: translate G) with (translate (n :: G)).
    apply translate_node_normal_args; auto.
  Qed.

End NL2STCNORMALARGS.

Module NL2StcNormalArgsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Op)
       (CStr  : COINDSTREAMS    Op OpAux)
       (IStr  : INDEXEDSTREAMS  Op OpAux)
       (CE    : COREEXPR    Ids Op OpAux      IStr)
       (NL    : NLUSTRE     Ids Op OpAux CStr IStr CE)
       (Stc   : STC         Ids Op OpAux      IStr CE)
       (Trans : TRANSLATION Ids Op                 CE.Syn NL.Syn Stc.Syn NL.Mem)
<: NL2STCNORMALARGS Ids Op OpAux CStr IStr CE NL Stc Trans.
  Include NL2STCNORMALARGS Ids Op OpAux CStr IStr CE NL Stc Trans.
End NL2StcNormalArgsFun.
