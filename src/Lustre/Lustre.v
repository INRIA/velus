From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Export Lustre.LSyntax.
From Velus Require Export Lustre.LClocking.
From Velus Require Export Lustre.LTyping.
From Velus Require Export Lustre.LOrdered.
From Velus Require Export Lustre.LCausality.
From Velus Require Export Lustre.LSemantics.
From Velus Require Export Lustre.LClockSemantics.
From Velus Require Export Lustre.Normalization.LNormalization.

From Velus Require Import Common.

Module Type LUSTRE
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (CStr  : COINDSTREAMS  Op OpAux)
       (IStr  : INDEXEDSTREAMS Op OpAux).
  Declare Module Export Syn: LSYNTAX    Ids Op.
  Declare Module Export Typ: LTYPING    Ids Op       Syn.
  Declare Module Export Clo: LCLOCKING  Ids Op       Syn.
  Declare Module Export Ord: LORDERED   Ids Op       Syn.
  Declare Module Export Cau: LCAUSALITY Ids Op       Syn.
  Declare Module Export Sem: LSEMANTICS Ids Op OpAux Syn Ord CStr.
  Declare Module Export ClSem: LCLOCKSEMANTICS Ids Op OpAux Syn Clo Cau Ord CStr IStr Sem.
  Declare Module Export Norm: LNORMALIZATION Ids Op OpAux CStr IStr Syn Typ Clo Cau Ord Sem ClSem.
End LUSTRE.

Module LustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (CStr  : COINDSTREAMS  Op OpAux)
       (IStr  : INDEXEDSTREAMS Op OpAux)
       <: LUSTRE Ids Op OpAux CStr IStr.
  Module Export Syn := LSyntaxFun     Ids Op.
  Module Export Typ := LTypingFun     Ids Op       Syn.
  Module Export Clo := LClockingFun   Ids Op       Syn.
  Module Export Ord:= LOrderedFun     Ids Op       Syn.
  Module Export Cau:= LCausalityFun      Ids Op       Syn.
  Module Export Sem := LSemanticsFun  Ids Op OpAux Syn Ord CStr.
  Module Export ClSem := LClockSemanticsFun Ids Op OpAux Syn Clo Cau Ord CStr IStr Sem.
  Module Export Norm := LNormalizationFun Ids Op OpAux CStr IStr Syn Typ Clo Cau Ord Sem ClSem.
End LustreFun.
