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
From Velus Require Export Stc.StcSchedulingValidator.
From Velus Require Export Stc.StcSchedule.
From Velus Require Export Stc.StcTyping.
From Velus Require Export Stc.StcClocking.
From Velus Require Export Stc.StcClockingSemantics.
From Velus Require Export Stc.StcMemoryCorres.
From Velus Require Export Stc.StcTypingSemantics.

From Velus Require Import Common.

Module Type STC
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (ComTyp: COMMONTYPING   Ids Op OpAux)
       (Cks   : CLOCKS         Ids Op OpAux)
       (Str   : INDEXEDSTREAMS Ids Op OpAux Cks)
       (CE    : COREEXPR       Ids Op OpAux ComTyp Cks Str).

  Declare Module Export Syn  : STCSYNTAX      Ids Op OpAux Cks CE.Syn.
  Declare Module Export Syst : STCISSYSTEM    Ids Op OpAux Cks CE.Syn Syn.
  Declare Module Export Ord  : STCORDERED     Ids Op OpAux Cks CE.Syn Syn Syst.
  Declare Module Export Sem  : STCSEMANTICS   Ids Op OpAux Cks CE.Syn Syn Syst Ord Str CE.Sem.
  Declare Module Export Reset: STCISRESET     Ids Op OpAux Cks CE.Syn Syn.
  Declare Module Export Next : STCISNEXT      Ids Op OpAux Cks CE.Syn Syn.
  Declare Module Export Var  : STCISVARIABLE  Ids Op OpAux Cks CE.Syn Syn.
  Declare Module Export Def  : STCISDEFINED   Ids Op OpAux Cks CE.Syn Syn Var Next.
  Declare Module Export Free : STCISFREE      Ids Op OpAux Cks CE.Syn Syn CE.IsF.
  Declare Module Export Wdef : STCWELLDEFINED Ids Op OpAux Cks CE.Syn Syn Syst Ord Var Reset Next CE.IsF Free.
  Declare Module Export SchV : STCSCHEDULINGVALIDATOR
                                              Ids Op OpAux Cks CE.Syn Syn Syst Ord Var Reset Next CE.IsF Free Wdef.
  Declare Module Export Typ  : STCTYPING      Ids Op OpAux Cks CE.Syn Syn CE.Typ.
  Declare Module Export Clo  : STCCLOCKING    Ids Op OpAux Cks CE.Syn Syn Reset Var Syst Ord CE.Clo.
  Declare Module Export CloSem : STCCLOCKINGSEMANTICS Ids Op OpAux Cks CE.Syn Syn Str Reset Next Var Def Syst Ord
                                                      CE.Sem Sem CE.Clo Clo CE.CloSem.

  Declare Module Export Corres : STCMEMORYCORRES    Ids Op OpAux Cks Str CE.Syn Syn Reset Next Syst Ord CE.Sem Sem.
  Declare Module Export TypSem : STCTYPINGSEMANTICS Ids Op OpAux ComTyp Cks CE.Syn Syn CE.Typ Typ Str Next Reset Syst Var Def CE.IsF Free Ord CE.Sem CE.TypSem Sem Wdef Corres.
  Declare Module Scheduler   : STCSCHEDULE    Ids Op OpAux ComTyp Cks Str CE Syn Syst Ord Sem Typ Var Reset Next Clo Free Wdef.

End STC.

Module StcFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (ComTyp: COMMONTYPING   Ids Op OpAux)
       (Cks   : CLOCKS         Ids Op OpAux)
       (Str   : INDEXEDSTREAMS Ids Op OpAux Cks)
       (CE    : COREEXPR       Ids Op OpAux ComTyp Cks Str)
<: STC Ids Op OpAux ComTyp Cks Str CE.

  Module Export Syn   := StcSyntaxFun      Ids Op OpAux Cks CE.Syn.
  Module Export Syst  := StcIsSystemFun    Ids Op OpAux Cks CE.Syn Syn.
  Module Export Ord   := StcOrderedFun     Ids Op OpAux Cks CE.Syn Syn Syst.
  Module Export Sem   := StcSemanticsFun   Ids Op OpAux Cks CE.Syn Syn Syst Ord Str CE.Sem.
  Module Export Reset := StcIsResetFun     Ids Op OpAux Cks CE.Syn Syn.
  Module Export Next  := StcIsNextFun      Ids Op OpAux Cks CE.Syn Syn.
  Module Export Var   := StcIsVariableFun  Ids Op OpAux Cks CE.Syn Syn.
  Module Export Def   := StcIsDefinedFun   Ids Op OpAux Cks CE.Syn Syn Var Next.
  Module Export Free  := StcIsFreeFun      Ids Op OpAux Cks CE.Syn Syn CE.IsF.
  Module Export Wdef  := StcWellDefinedFun Ids Op OpAux Cks CE.Syn Syn Syst Ord Var Reset Next CE.IsF Free.
  Module Export SchV  := StcSchedulingValidatorFun
                                           Ids Op OpAux Cks CE.Syn Syn Syst Ord Var Reset Next CE.IsF Free Wdef.
  Module Export Typ   := StcTypingFun      Ids Op OpAux Cks CE.Syn Syn CE.Typ.
  Module Export Clo   := StcClockingFun    Ids Op OpAux Cks CE.Syn Syn Reset Var Syst Ord CE.Clo.
  Module Export CloSem := StcClockingSemanticsFun Ids Op OpAux Cks CE.Syn Syn Str Reset Next Var Def Syst Ord
                                                     CE.Sem Sem CE.Clo Clo CE.CloSem.
  Module Export Corres := StcMemoryCorresFun    Ids Op OpAux Cks Str CE.Syn Syn Reset Next Syst Ord CE.Sem Sem.
  Module Export TypSem := StcTypingSemanticsFun Ids Op OpAux ComTyp Cks CE.Syn Syn CE.Typ Typ Str Next Reset Syst Var Def CE.IsF Free Ord CE.Sem CE.TypSem Sem Wdef Corres.
  Module Scheduler    := StcScheduleFun    Ids Op OpAux ComTyp Cks Str CE Syn Syst Ord Sem Typ Var Reset Next Clo Free Wdef.
End StcFun.
