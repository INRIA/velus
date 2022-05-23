From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Export Lustre.LSyntax.
From Velus Require Export Lustre.LClocking.
From Velus Require Export Lustre.LTyping.
From Velus Require Export Lustre.LOrdered.
From Velus Require Export Lustre.LCausality.
From Velus Require Export Lustre.LSemantics.
From Velus Require Export Lustre.LClockedSemantics.
From Velus Require Export Lustre.LSemDeterminism.
From Velus Require Export Lustre.LClockCorrectness.
From Velus Require Export Lustre.DeLast.LDeLast.
From Velus Require Export Lustre.CompAuto.LCompAuto.
From Velus Require Export Lustre.ClockSwitch.LClockSwitch.
From Velus Require Export Lustre.InlineLocal.LInlineLocal.
From Velus Require Export Lustre.Normalization.LNormalization.

From Velus Require Import Common.

Module Type LUSTRE
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (Cks   : CLOCKS         Ids Op OpAux)
       (CStr  : COINDSTREAMS   Ids Op OpAux Cks).
  Declare Module Export Senv: STATICENV Ids Op OpAux Cks.
  Declare Module Export Syn: LSYNTAX    Ids Op OpAux Cks Senv.
  Declare Module Export Typ: LTYPING    Ids Op OpAux Cks Senv Syn.
  Declare Module Export Clo: LCLOCKING  Ids Op OpAux Cks Senv Syn.
  Declare Module Export Ord: LORDERED   Ids Op OpAux Cks Senv Syn.
  Declare Module Export Cau: LCAUSALITY Ids Op OpAux Cks Senv Syn.
  Declare Module Export Sem: LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr.
  Declare Module Export CkSem: LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Clo Ord CStr Sem.

  Declare Module Export SemDet: LSEMDETERMINISM Ids Op OpAux Cks Senv Syn Typ Cau Ord CStr Sem.
  Declare Module Export CkCor: LCLOCKCORRECTNESS Ids Op OpAux Cks Senv Syn Typ Clo Cau Ord CStr Sem CkSem.

  Declare Module Export DeLast: LDELAST           Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem CkSem.
  Declare Module Export CompAuto: LCOMPAUTO       Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem CkSem.
  Declare Module Export ClockSwitch: LCLOCKSWITCH Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem CkSem.
  Declare Module Export InlineLocal: LINLINELOCAL Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem CkSem.
  Declare Module Export Norm: LNORMALIZATION Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem CkSem.
End LUSTRE.

Module LustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (Cks   : CLOCKS         Ids Op OpAux)
       (CStr  : COINDSTREAMS   Ids Op OpAux Cks)
<: LUSTRE Ids Op OpAux Cks CStr.
  Module Export Senv := StaticEnvFun Ids Op OpAux Cks.
  Module Export Syn := LSyntaxFun     Ids Op OpAux Cks Senv.
  Module Export Typ := LTypingFun     Ids Op OpAux Cks Senv Syn.
  Module Export Clo := LClockingFun   Ids Op OpAux Cks Senv Syn.
  Module Export Ord := LOrderedFun    Ids Op OpAux Cks Senv Syn.
  Module Export Cau := LCausalityFun  Ids Op OpAux Cks Senv Syn.
  Module Export Sem := LSemanticsFun  Ids Op OpAux Cks Senv Syn Ord CStr.
  Module Export CkSem := LClockedSemanticsFun Ids Op OpAux Cks Senv Syn Clo Ord CStr Sem.

  Module Export SemDet := LSemDeterminismFun Ids Op OpAux Cks Senv Syn Typ Cau Ord CStr Sem.
  Module Export CkCor:= LClockCorrectnessFun Ids Op OpAux Cks Senv Syn Typ Clo Cau Ord CStr Sem CkSem.


  Module Export DeLast := LDeLastFun           Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem CkSem.
  Module Export CompAuto := LCompAutoFun       Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem CkSem.
  Module Export ClockSwitch := LClockSwitchFun Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem CkSem.
  Module Export InlineLocal := LInlineLocalFun Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem CkSem.
  Module Export Norm := LNormalizationFun Ids Op OpAux Cks CStr Senv Syn Typ Clo Ord Sem CkSem.
End LustreFun.
