From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking.
From Velus Require Import Lustre.LCausality Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics LClockSemantics.
From Velus Require Import Lustre.DeLast.DeLast.
From Velus Require Import Lustre.DeLast.DLTyping.
From Velus Require Import Lustre.DeLast.DLClocking.
From Velus Require Import Lustre.DeLast.DLCorrectness.

Module Type LDELAST
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Cau : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Ord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (ClSem : LCLOCKSEMANTICS Ids Op OpAux Cks Senv Syn Typ Clo Cau Ord CStr Sem).
  Declare Module Export DL : DELAST Ids Op OpAux Cks Senv Syn.
  Declare Module Export Typing : DLTYPING Ids Op OpAux Cks Senv Syn Typ DL.
  Declare Module Export Clocking : DLCLOCKING Ids Op OpAux Cks Senv Syn Clo DL.
  Declare Module Export Correct : DLCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Cau Typ Clo Ord Sem ClSem DL.
End LDELAST.

Module LDeLastFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Cau : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Ord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (ClSem : LCLOCKSEMANTICS Ids Op OpAux Cks Senv Syn Typ Clo Cau Ord CStr Sem)
       <: LDELAST Ids Op OpAux Cks CStr Senv Syn Typ Clo Cau Ord Sem ClSem.
  Module Export DL := DeLastFun Ids Op OpAux Cks Senv Syn.
  Module Export Typing := DLTypingFun Ids Op OpAux Cks Senv Syn Typ DL.
  Module Export Clocking := DLClockingFun Ids Op OpAux Cks Senv Syn Clo DL.
  Module Export Correct := DLCorrectnessFun Ids Op OpAux Cks CStr Senv Syn Cau Typ Clo Ord Sem ClSem DL.
End LDeLastFun.
