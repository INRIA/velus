From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking.
From Velus Require Import Lustre.LCausality Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics LClockSemantics.
From Velus Require Import Lustre.Normalization.Normalization.
From Velus Require Import Lustre.Normalization.Correctness.
From Velus Require Import Lustre.Normalization.Idempotence.

Local Set Warnings "-masking-absolute-name".
Module Type LNORMALIZATION
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str : COINDSTREAMS Op OpAux)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn)
       (Clo : LCLOCKING Ids Op Syn)
       (Cau : LCAUSALITY Ids Op Syn)
       (Ord : LORDERED Ids Op Syn)
       (Sem : LSEMANTICS Ids Op OpAux Syn Ord Str)
       (ClSem : LCLOCKSEMANTICS Ids Op OpAux Syn Typ Clo Cau Ord Str Sem).
  Declare Module Norm : NORMALIZATION Ids Op OpAux Syn.
  Declare Module Export Correct : CORRECTNESS Ids Op OpAux Str Syn Typ Clo Cau Ord Sem ClSem Norm.
  Declare Module Idempotence : IDEMPOTENCE Ids Op OpAux Syn Norm.
End LNORMALIZATION.

Module LNormalizationFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str : COINDSTREAMS Op OpAux)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn)
       (Clo : LCLOCKING Ids Op Syn)
       (Cau : LCAUSALITY Ids Op Syn)
       (Ord : LORDERED Ids Op Syn)
       (Sem : LSEMANTICS Ids Op OpAux Syn Ord Str)
       (ClSem : LCLOCKSEMANTICS Ids Op OpAux Syn Typ Clo Cau Ord Str Sem)
       <: LNORMALIZATION Ids Op OpAux Str Syn Typ Clo Cau Ord Sem ClSem.
  Module Norm := NormalizationFun Ids Op OpAux Syn.
  Module Export Correct := CorrectnessFun Ids Op OpAux Str Syn Typ Clo Cau Ord Sem ClSem Norm.
  Module Idempotence := IdempotenceFun Ids Op OpAux Syn Norm.
End LNormalizationFun.
