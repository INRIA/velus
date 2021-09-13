From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking.
From Velus Require Import Lustre.LCausality Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics LClockSemantics.
From Velus Require Import Lustre.InlineLocal.InlineLocal.
From Velus Require Import Lustre.InlineLocal.ILTyping.
From Velus Require Import Lustre.InlineLocal.ILClocking.
From Velus Require Import Lustre.InlineLocal.ILCorrectness.

Module Type LINLINELOCAL
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
  Declare Module Export IL : INLINELOCAL Ids Op OpAux Cks Syn.
  Declare Module Export Typing : ILTYPING Ids Op OpAux Cks Syn Typ IL.
  Declare Module Export Clocking : ILCLOCKING Ids Op OpAux Cks Syn Clo IL.
  Declare Module Export Correct : ILCORRECTNESS Ids Op OpAux Cks CStr Syn Cau Typ Clo Ord Sem ClSem IL.
End LINLINELOCAL.

Module LInlineLocalFun
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
       <: LINLINELOCAL Ids Op OpAux Cks CStr Syn Typ Clo Cau Ord Sem ClSem.
  Module Export IL := InlineLocalFun Ids Op OpAux Cks Syn.
  Module Export Typing := ILTypingFun Ids Op OpAux Cks Syn Typ IL.
  Module Export Clocking := ILClockingFun Ids Op OpAux Cks Syn Clo IL.
  Module Export Correct := ILCorrectnessFun Ids Op OpAux Cks CStr Syn Cau Typ Clo Ord Sem ClSem IL.
End LInlineLocalFun.
