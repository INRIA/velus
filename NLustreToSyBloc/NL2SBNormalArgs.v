Require Import Velus.NLustre.
Require Import Velus.SyBloc.

Require Import Velus.NLustreToSyBloc.Translation.

Require Import Velus.RMemory.
Require Import Velus.Common.

Require Import List.
Import List.ListNotations.

Module Type NL2SBNORMALARGS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import Str   : STREAM          Op OpAux)
       (Import CE    : COREEXPR    Ids Op OpAux Str)
       (Import NL    : NLUSTRE     Ids Op OpAux Str CE)
       (Import SB    : SYBLOC      Ids Op OpAux Str CE)
       (Import Trans : TRANSLATION Ids Op       CE.Syn NL.Syn SB.Syn NL.Mem).

  Lemma translate_eqn_normal_args:
    forall G eq,
      Norm.normal_args_eq G eq ->
      Forall (normal_args_eq (translate G)) (translate_eqn eq).
  Proof.
    induction 1 as [|?????? Find|]; simpl; eauto using Forall_cons, normal_args_eq.
    apply find_node_translate in Find as (?&?&?&?); subst.
    cases; eauto using Forall_cons, normal_args_eq.
  Qed.

  Lemma translate_node_normal_args:
    forall G n,
      normal_args_node G n ->
      normal_args_block (translate G) (translate_node n).
  Proof.
    unfold normal_args_node, normal_args_block.
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

End NL2SBNORMALARGS.

Module NL2SBNormalArgsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Op)
       (Str   : STREAM          Op OpAux)
       (CE    : COREEXPR    Ids Op OpAux Str)
       (NL    : NLUSTRE     Ids Op OpAux Str CE)
       (SB    : SYBLOC      Ids Op OpAux Str CE)
       (Trans : TRANSLATION Ids Op       CE.Syn NL.Syn SB.Syn NL.Mem)
<: NL2SBNORMALARGS Ids Op OpAux Str CE NL SB Trans.
  Include NL2SBNORMALARGS Ids Op OpAux Str CE NL SB Trans.
End NL2SBNormalArgsFun.
