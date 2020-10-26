From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams IndexedStreams.
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
       (CStr : COINDSTREAMS Op OpAux)
       (IStr : INDEXEDSTREAMS Op OpAux)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn)
       (Clo : LCLOCKING Ids Op Syn)
       (Cau : LCAUSALITY Ids Op Syn)
       (Ord : LORDERED Ids Op Syn)
       (Sem : LSEMANTICS Ids Op OpAux Syn Ord CStr)
       (ClSem : LCLOCKSEMANTICS Ids Op OpAux Syn Typ Clo Cau Ord CStr IStr Sem).
  Declare Module Export Norm : NORMALIZATION Ids Op OpAux Syn Cau.
  Declare Module Export Correct : CORRECTNESS Ids Op OpAux CStr IStr Syn Cau Typ Clo Ord Sem ClSem Norm.
  Declare Module Export Idempotence : IDEMPOTENCE Ids Op OpAux Syn Cau Norm.
End LNORMALIZATION.

Module LNormalizationFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (CStr : COINDSTREAMS Op OpAux)
       (IStr : INDEXEDSTREAMS Op OpAux)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn)
       (Clo : LCLOCKING Ids Op Syn)
       (Cau : LCAUSALITY Ids Op Syn)
       (Ord : LORDERED Ids Op Syn)
       (Sem : LSEMANTICS Ids Op OpAux Syn Ord CStr)
       (ClSem : LCLOCKSEMANTICS Ids Op OpAux Syn Typ Clo Cau Ord CStr IStr Sem)
       <: LNORMALIZATION Ids Op OpAux CStr IStr Syn Typ Clo Cau Ord Sem ClSem.
  Module Export Norm := NormalizationFun Ids Op OpAux Syn Cau.
  Module Export Correct := CorrectnessFun Ids Op OpAux CStr IStr Syn Cau Typ Clo Ord Sem ClSem Norm.
  Module Export Idempotence := IdempotenceFun Ids Op OpAux Syn Cau Norm.
End LNormalizationFun.
