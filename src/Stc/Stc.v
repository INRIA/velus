(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Velus Require Export CoreExpr.
From Velus Require Export Stc.StcSyntax.
From Velus Require Export Stc.StcIsSystem.
From Velus Require Export Stc.StcOrdered.
From Velus Require Export Stc.StcSemantics.
From Velus Require Export Stc.StcIsLast.
From Velus Require Export Stc.StcIsVariable.
From Velus Require Export Stc.StcIsDefined.
From Velus Require Export Stc.StcIsFree.
From Velus Require Export Stc.StcWellDefined.
From Velus Require Export Stc.StcSchedulingValidator.
From Velus Require Export Stc.StcSchedule.
From Velus Require Export Stc.StcTyping.
From Velus Require Export Stc.StcClocking.
From Velus Require Export Stc.StcClockingSemantics.

From Velus Require Import Common.

Module Type STC
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Op)
       (Str   : INDEXEDSTREAMS Op OpAux)
       (CE    : COREEXPR Ids   Op OpAux Str).

  Declare Module Export Syn  : STCSYNTAX      Ids Op       CE.Syn.
  Declare Module Export Syst : STCISSYSTEM    Ids Op       CE.Syn Syn.
  Declare Module Export Ord  : STCORDERED     Ids Op       CE.Syn Syn Syst.
  Declare Module Export Sem  : STCSEMANTICS   Ids Op OpAux CE.Syn Syn Syst Ord Str CE.Sem.
  Declare Module Export Last : STCISLAST      Ids Op       CE.Syn Syn.
  Declare Module Export Var  : STCISVARIABLE  Ids Op       CE.Syn Syn.
  Declare Module Export Def  : STCISDEFINED   Ids Op       CE.Syn Syn Var Last.
  Declare Module Export Free : STCISFREE      Ids Op       CE.Syn Syn CE.IsF.
  Declare Module Export Wdef : STCWELLDEFINED Ids Op       CE.Syn Syn Syst Ord Var Last Def CE.IsF Free.
  Declare Module Export SchV : STCSCHEDULINGVALIDATOR
                                              Ids Op       CE.Syn Syn Syst Ord Var Last Def CE.IsF Free Wdef.
  Declare Module Export Typ  : STCTYPING      Ids Op       CE.Syn Syn CE.Typ.
  Declare Module Export Clo  : STCCLOCKING    Ids Op       CE.Syn Syn Last Var Def Syst Ord CE.Clo.
  Declare Module Export CloSem : STCCLOCKINGSEMANTICS Ids Op OpAux CE.Syn Syn Str Last Var Def Syst Ord
                                                     CE.Sem Sem CE.Clo Clo CE.CloSem.

  Declare Module Scheduler   : STCSCHEDULE    Ids Op OpAux Str CE Syn Syst Ord Sem Typ Var Last Def Clo Free Wdef.

End STC.

Module StcFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Op)
       (Str   : INDEXEDSTREAMS Op OpAux)
       (CE    : COREEXPR Ids   Op OpAux Str)
<: STC Ids Op OpAux Str CE.

  Module Export Syn   := StcSyntaxFun      Ids Op       CE.Syn.
  Module Export Syst  := StcIsSystemFun    Ids Op       CE.Syn Syn.
  Module Export Ord   := StcOrderedFun     Ids Op       CE.Syn Syn Syst.
  Module Export Sem   := StcSemanticsFun   Ids Op OpAux CE.Syn Syn Syst Ord Str CE.Sem.
  Module Export Last  := StcIsLastFun      Ids Op       CE.Syn Syn.
  Module Export Var   := StcIsVariableFun  Ids Op       CE.Syn Syn.
  Module Export Def   := StcIsDefinedFun   Ids Op       CE.Syn Syn Var Last.
  Module Export Free  := StcIsFreeFun      Ids Op       CE.Syn Syn CE.IsF.
  Module Export Wdef  := StcWellDefinedFun Ids Op       CE.Syn Syn Syst Ord Var Last Def CE.IsF Free.
  Module Export SchV  := StcSchedulingValidatorFun
                                           Ids Op       CE.Syn Syn Syst Ord Var Last Def CE.IsF Free Wdef.
  Module Export Typ   := StcTypingFun      Ids Op       CE.Syn Syn CE.Typ.
  Module Export Clo   := StcClockingFun    Ids Op       CE.Syn Syn Last Var Def Syst Ord CE.Clo.
  Module Export CloSem := StcClockingSemanticsFun Ids Op OpAux CE.Syn Syn Str Last Var Def Syst Ord
                                                     CE.Sem Sem CE.Clo Clo CE.CloSem.

  Module Scheduler    := StcScheduleFun    Ids Op OpAux Str CE Syn Syst Ord Sem Typ Var Last Def Clo Free Wdef.
End StcFun.
