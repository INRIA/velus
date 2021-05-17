From Velus Require Export CoreExpr.
From Velus Require Export Stc.StcSyntax.
From Velus Require Export Stc.StcIsSystem.
From Velus Require Export Stc.StcOrdered.
From Velus Require Export Stc.StcSemantics.
From Velus Require Export Stc.StcIsReset.
From Velus Require Export Stc.StcIsVariable.
From Velus Require Export Stc.StcIsDefined.
From Velus Require Export Stc.StcIsNext.
From Velus Require Export Stc.StcIsFree.
From Velus Require Export Stc.StcWellDefined.
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
  Declare Module Export Reset: STCISRESET      Ids Op       CE.Syn Syn.
  Declare Module Export Next : STCISNEXT      Ids Op       CE.Syn Syn.
  Declare Module Export Var  : STCISVARIABLE  Ids Op       CE.Syn Syn.
  Declare Module Export Def  : STCISDEFINED   Ids Op       CE.Syn Syn Var Next.
  Declare Module Export Free : STCISFREE      Ids Op       CE.Syn Syn CE.IsF.
  Declare Module Export Wdef : STCWELLDEFINED Ids Op       CE.Syn Syn Syst Ord Var Reset Next CE.IsF Free.
  Declare Module Export Typ  : STCTYPING      Ids Op       CE.Syn Syn CE.Typ.
  Declare Module Export Clo  : STCCLOCKING    Ids Op       CE.Syn Syn Reset Var Syst Ord CE.Clo.
  Declare Module Export CloSem : STCCLOCKINGSEMANTICS Ids Op OpAux CE.Syn Syn Str Reset Next Var Def Syst Ord
                                                      CE.Sem Sem CE.Clo Clo CE.CloSem.

  Declare Module Scheduler   : STCSCHEDULE    Ids Op OpAux Str CE Syn Syst Ord Sem Typ Var Reset Next Clo Free Wdef.

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
  Module Export Reset := StcIsResetFun      Ids Op       CE.Syn Syn.
  Module Export Next  := StcIsNextFun      Ids Op       CE.Syn Syn.
  Module Export Var   := StcIsVariableFun  Ids Op       CE.Syn Syn.
  Module Export Def   := StcIsDefinedFun   Ids Op       CE.Syn Syn Var Next.
  Module Export Free  := StcIsFreeFun      Ids Op       CE.Syn Syn CE.IsF.
  Module Export Wdef  := StcWellDefinedFun Ids Op       CE.Syn Syn Syst Ord Var Reset Next CE.IsF Free.
  Module Export Typ   := StcTypingFun      Ids Op       CE.Syn Syn CE.Typ.
  Module Export Clo   := StcClockingFun    Ids Op       CE.Syn Syn Reset Var Syst Ord CE.Clo.
  Module Export CloSem := StcClockingSemanticsFun Ids Op OpAux CE.Syn Syn Str Reset Next Var Def Syst Ord
                                                     CE.Sem Sem CE.Clo Clo CE.CloSem.

  Module Scheduler    := StcScheduleFun    Ids Op OpAux Str CE Syn Syst Ord Sem Typ Var Reset Next Clo Free Wdef.
End StcFun.
