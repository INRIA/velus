From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Export Lustre.LSyntax.
From Velus Require Export Lustre.LClocking.
From Velus Require Export Lustre.LTyping.
From Velus Require Export Lustre.LOrdered.
From Velus Require Export Lustre.LCausality.
From Velus Require Export Lustre.LSemantics.
From Velus Require Export Lustre.LSemDeterminism.
From Velus Require Export Lustre.LClockSemantics.
From Velus Require Export Lustre.Normalization.LNormalization.

From Velus Require Import Common.

Module Type LUSTRE
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (Cks   : CLOCKS         Ids Op OpAux)
       (CStr  : COINDSTREAMS   Ids Op OpAux Cks).
  Declare Module Export Syn: LSYNTAX    Ids Op OpAux Cks.
  Declare Module Export Typ: LTYPING    Ids Op OpAux Cks Syn.
  Declare Module Export Clo: LCLOCKING  Ids Op OpAux Cks Syn.
  Declare Module Export Ord: LORDERED   Ids Op OpAux Cks Syn.
  Declare Module Export Cau: LCAUSALITY Ids Op OpAux Cks Syn.
  Declare Module Export Sem: LSEMANTICS Ids Op OpAux Cks Syn Ord CStr.
  Declare Module Export SemDet : LSEMDETERMINISM Ids Op OpAux Cks Syn Clo Cau Ord CStr Sem.
  Declare Module Export CkSem: LCLOCKSEMANTICS Ids Op OpAux Cks Syn Clo Cau Ord CStr Sem.
  Declare Module Export Norm: LNORMALIZATION Ids Op OpAux Cks CStr Syn Typ Clo Cau Ord Sem CkSem.
End LUSTRE.

Module LustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (Cks   : CLOCKS         Ids Op OpAux)
       (CStr  : COINDSTREAMS   Ids Op OpAux Cks)
       <: LUSTRE Ids Op OpAux Cks CStr.
  Module Export Syn := LSyntaxFun     Ids Op OpAux Cks.
  Module Export Typ := LTypingFun     Ids Op OpAux Cks Syn.
  Module Export Clo := LClockingFun   Ids Op OpAux Cks Syn.
  Module Export Ord:= LOrderedFun     Ids Op OpAux Cks Syn.
  Module Export Cau:= LCausalityFun   Ids Op OpAux Cks Syn.
  Module Export Sem := LSemanticsFun  Ids Op OpAux Cks Syn Ord CStr.
  Module Export SemDet := LSemDeterminismFun Ids Op OpAux Cks Syn Clo Cau Ord CStr Sem.
  Module Export CkSem := LClockSemanticsFun Ids Op OpAux Cks Syn Clo Cau Ord CStr Sem.
  Module Export Norm := LNormalizationFun Ids Op OpAux Cks CStr Syn Typ Clo Cau Ord Sem CkSem.
End LustreFun.
