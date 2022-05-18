From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics LClockedSemantics.
From Velus Require Import Lustre.CompAuto.CompAuto.
From Velus Require Import Lustre.CompAuto.CATyping.
From Velus Require Import Lustre.CompAuto.CAClocking.
From Velus Require Import Lustre.CompAuto.CACorrectness.

Module Type LCOMPAUTO
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
  Declare Module Export CA : COMPAUTO Ids Op OpAux Cks Senv Syn.
  Declare Module Export Typing : CATYPING Ids Op OpAux Cks Senv Syn Typ CA.
  Declare Module Export Clocking : CACLOCKING Ids Op OpAux Cks Senv Syn Clo CA.
  Declare Module Export Correct : CACORRECTNESS Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem ClSem CA.
End LCOMPAUTO.

Module LCompAutoFun
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
       <: LCOMPAUTO Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem ClSem.
  Module Export CA := CompAutoFun Ids Op OpAux Cks Senv Syn.
  Module Export Typing := CATypingFun Ids Op OpAux Cks Senv Syn Typ CA.
  Module Export Clocking := CAClockingFun Ids Op OpAux Cks Senv Syn Clo CA.
  Module Export Correct := CACorrectnessFun Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem ClSem CA.
End LCompAutoFun.
