From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking.
From Velus Require Import Lustre.LCausality Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics LClockSemantics.
From Velus Require Import Lustre.Normalization.Normalization.
From Velus Require Import Lustre.Normalization.Correctness.
(* From Velus Require Import Lustre.Normalization.Idempotence. *)

Module Type LNORMALIZATION
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (Typ : LTYPING Ids Op OpAux Cks Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (Cau : LCAUSALITY Ids Op OpAux Cks Syn)
       (Ord : LORDERED Ids Op OpAux Cks Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Syn Ord CStr)
       (ClSem : LCLOCKSEMANTICS Ids Op OpAux Cks Syn Clo Cau Ord CStr Sem).
  Declare Module Export Norm : NORMALIZATION Ids Op OpAux Cks Syn Cau.
  Declare Module Export Correct : CORRECTNESS Ids Op OpAux Cks CStr Syn Cau Typ Clo Ord Sem ClSem Norm.
  (* Declare Module Export Idempotence : IDEMPOTENCE Ids Op OpAux Syn Cau Norm. *)
End LNORMALIZATION.

Module LNormalizationFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (Typ : LTYPING Ids Op OpAux Cks Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (Cau : LCAUSALITY Ids Op OpAux Cks Syn)
       (Ord : LORDERED Ids Op OpAux Cks Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Syn Ord CStr)
       (ClSem : LCLOCKSEMANTICS Ids Op OpAux Cks Syn Clo Cau Ord CStr Sem)
       <: LNORMALIZATION Ids Op OpAux Cks CStr Syn Typ Clo Cau Ord Sem ClSem.
  Module Export Norm := NormalizationFun Ids Op OpAux Cks Syn Cau.
  Module Export Correct := CorrectnessFun Ids Op OpAux Cks CStr Syn Cau Typ Clo Ord Sem ClSem Norm.
  (* Module Export Idempotence := IdempotenceFun Ids Op OpAux Syn Cau Norm. *)
End LNormalizationFun.
