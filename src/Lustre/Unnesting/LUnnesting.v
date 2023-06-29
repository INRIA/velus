From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics LClockedSemantics.
From Velus Require Import Lustre.Unnesting.Unnesting.
From Velus Require Import Lustre.Unnesting.UTyping.
From Velus Require Import Lustre.Unnesting.UClocking.
From Velus Require Import Lustre.Unnesting.UCorrectness.
(* From Velus Require Import Lustre.Unnesting.Idempotence. *)

Module Type LUNNESTING
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Ord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (ClSem : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Clo Ord CStr Sem).
  Declare Module Export Un : UNNESTING Ids Op OpAux Cks Senv Syn.
  Declare Module Export Typing : UTYPING Ids Op OpAux Cks Senv Syn Typ Un.
  Declare Module Export Clocking : UCLOCKING Ids Op OpAux Cks Senv Syn Clo Un.
  Declare Module Export Correct : UCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem ClSem Un.
  (* Declare Module Export Idempotence : IDEMPOTENCE Ids Op OpAux Syn Cau Norm. *)
End LUNNESTING.

Module LUnnestingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Ord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (ClSem : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Clo Ord CStr Sem)
       <: LUNNESTING Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem ClSem.
  Module Export Un := UnnestingFun Ids Op OpAux Cks Senv Syn.
  Module Export Typing := UTypingFun Ids Op OpAux Cks Senv Syn Typ Un.
  Module Export Clocking := UClockingFun Ids Op OpAux Cks Senv Syn Clo Un.
  Module Export Correct := UCorrectnessFun Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem ClSem Un.
  (* Module Export Idempotence := IdempotenceFun Ids Op OpAux Syn Cau Norm. *)
End LUnnestingFun.
