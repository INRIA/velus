From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics LClockedSemantics.
From Velus Require Import Lustre.NormFby.NormFby.
From Velus Require Import Lustre.NormFby.NFTyping.
From Velus Require Import Lustre.NormFby.NFClocking.
From Velus Require Import Lustre.NormFby.NFCorrectness.

Module Type LNORMFBY
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
  Declare Module Export NF : NORMFBY Ids Op OpAux Cks Senv Syn.
  Declare Module Export Typing : NFTYPING Ids Op OpAux Cks Senv Syn Typ NF.
  Declare Module Export Clocking : NFCLOCKING Ids Op OpAux Cks Senv Syn Clo NF.
  Declare Module Export Correct : NFCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Clo Ord Sem ClSem NF.
End LNORMFBY.

Module LNormFbyFun
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
       <: LNORMFBY Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem ClSem.
  Module Export NF := NormFbyFun Ids Op OpAux Cks Senv Syn.
  Module Export Typing := NFTypingFun Ids Op OpAux Cks Senv Syn Typ NF.
  Module Export Clocking := NFClockingFun Ids Op OpAux Cks Senv Syn Clo NF.
  Module Export Correct := NFCorrectnessFun Ids Op OpAux Cks CStr Senv Syn Clo Ord Sem ClSem NF.
End LNormFbyFun.
