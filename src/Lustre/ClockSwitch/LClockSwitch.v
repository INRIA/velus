From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking.
From Velus Require Import Lustre.LCausality Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics LClockSemantics.
From Velus Require Import Lustre.ClockSwitch.ClockSwitch.
From Velus Require Import Lustre.ClockSwitch.CSTyping.
From Velus Require Import Lustre.ClockSwitch.CSClocking.
From Velus Require Import Lustre.ClockSwitch.CSCorrectness.

Module Type LCLOCKSWITCH
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
  Declare Module Export CS      : CLOCKSWITCH Ids Op OpAux Cks Senv Syn.
  Declare Module Export CSTyp   : CSTYPING Ids Op OpAux Cks Senv Syn Typ CS.
  Declare Module Export CSClo   : CSCLOCKING Ids Op OpAux Cks Senv Syn Clo CS.
  Declare Module Export Correct : CSCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Typ Clo Cau Ord Sem ClSem CS.
End LCLOCKSWITCH.

Module LClockSwitchFun
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
       <: LCLOCKSWITCH Ids Op OpAux Cks CStr Senv Syn Typ Clo Cau Ord Sem ClSem.
  Module Export CS := ClockSwitchFun Ids Op OpAux Cks Senv Syn.
  Module Export CSTyp := CSTypingFun Ids Op OpAux Cks Senv Syn Typ CS.
  Module Export CSClo := CSClockingFun Ids Op OpAux Cks Senv Syn Clo CS.
  Module Export Correct := CSCorrectnessFun Ids Op OpAux Cks CStr Senv Syn Typ Clo Cau Ord Sem ClSem CS.
End LClockSwitchFun.
