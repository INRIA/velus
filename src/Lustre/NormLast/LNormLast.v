From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics LClockedSemantics.
From Velus Require Import Lustre.NormLast.NormLast.
From Velus Require Import Lustre.NormLast.NLTyping.
From Velus Require Import Lustre.NormLast.NLClocking.
From Velus Require Import Lustre.NormLast.NLCorrectness.

Module Type LNORMLAST
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
  Declare Module Export NL : NORMLAST Ids Op OpAux Cks Senv Syn.
  Declare Module Export Typing : NLTYPING Ids Op OpAux Cks Senv Syn Typ NL.
  Declare Module Export Clocking : NLCLOCKING Ids Op OpAux Cks Senv Syn Clo NL.
  Declare Module Export Correct : NLCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Clo Ord Sem ClSem NL.
End LNORMLAST.

Module LNormLastFun
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
       <: LNORMLAST Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem ClSem.
  Module Export NL := NormLastFun Ids Op OpAux Cks Senv Syn.
  Module Export Typing := NLTypingFun Ids Op OpAux Cks Senv Syn Typ NL.
  Module Export Clocking := NLClockingFun Ids Op OpAux Cks Senv Syn Clo NL.
  Module Export Correct := NLCorrectnessFun Ids Op OpAux Cks CStr Senv Syn Clo Ord Sem ClSem NL.
End LNormLastFun.
