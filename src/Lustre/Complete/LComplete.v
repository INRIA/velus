From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics.
From Velus Require Import Lustre.Complete.Complete.
From Velus Require Import Lustre.Complete.CompTyping.
From Velus Require Import Lustre.Complete.CompClocking.
From Velus Require Import Lustre.Complete.CompCorrectness.

Module Type LCOMPLETE
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
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr).
  Declare Module Export Complete : COMPLETE Ids Op OpAux Cks Senv Syn.
  Declare Module Export Typing : COMPTYPING Ids Op OpAux Cks Senv Syn Typ Complete.
  Declare Module Export Clocking : COMPCLOCKING Ids Op OpAux Cks Senv Syn Clo Complete.
  Declare Module Export Correct : COMPCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Clo Ord Sem Complete.
End LCOMPLETE.

Module LCompleteFun
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
       <: LCOMPLETE Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem.
  Module Export Complete := CompleteFun Ids Op OpAux Cks Senv Syn.
  Module Export Typing := CompTypingFun Ids Op OpAux Cks Senv Syn Typ Complete.
  Module Export Clocking := CompClockingFun Ids Op OpAux Cks Senv Syn Clo Complete.
  Module Export Correct := CompCorrectnessFun Ids Op OpAux Cks CStr Senv Syn Clo Ord Sem Complete.
End LCompleteFun.
