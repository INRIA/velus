Require Export Velus.CoreExpr.
Require Export Velus.SyBloc.SBSyntax.
Require Export Velus.SyBloc.SBIsBlock.
Require Export Velus.SyBloc.SBOrdered.
Require Export Velus.SyBloc.SBSemantics.
Require Export Velus.SyBloc.SBIsLast.
Require Export Velus.SyBloc.SBIsVariable.
Require Export Velus.SyBloc.SBIsDefined.
Require Export Velus.SyBloc.SBIsFree.
Require Export Velus.SyBloc.SBWellDefined.
Require Export Velus.SyBloc.SBSchedule.
Require Export Velus.SyBloc.SBTyping.
Require Export Velus.SyBloc.SBClocking.

Require Import Velus.Common.

Module Type SYBLOC
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Clks  : CLOCKS   Ids)
       (Str   : STREAM        Op OpAux)
       (CE    : COREEXPR Ids  Op OpAux Clks Str).

  Declare Module Export Syn  : SBSYNTAX      Ids Op       Clks CE.Syn.
  Declare Module Export Block: SBISBLOCK     Ids Op       Clks CE.Syn Syn.
  Declare Module Export Ord  : SBORDERED     Ids Op       Clks CE.Syn Syn Block.
  Declare Module Export Sem  : SBSEMANTICS   Ids Op OpAux Clks CE.Syn Syn Block Ord Str CE.Sem.
  Declare Module Export Last : SBISLAST      Ids Op       Clks CE.Syn Syn.
  Declare Module Export Var  : SBISVARIABLE  Ids Op       Clks CE.Syn Syn.
  Declare Module Export Def  : SBISDEFINED   Ids Op       Clks CE.Syn Syn Var Last.
  Declare Module Export Free : SBISFREE      Ids Op       Clks CE.Syn Syn CE.IsF.
  Declare Module Export Wdef : SBWELLDEFINED Ids Op       Clks CE.Syn Syn Block Ord Var Last Def CE.IsF Free.
  Declare Module Export Typ  : SBTYPING      Ids Op       Clks CE.Syn Syn CE.Typ.
  Declare Module Export Clo  : SBCLOCKING    Ids Op       Clks CE.Syn Syn Last Var Def CE.Clo.

  Declare Module Scheduler   : SBSCHEDULE    Ids Op OpAux Clks CE.Syn Syn Block Ord Str CE.Sem Sem CE.Typ Typ.

End SYBLOC.

Module SyBlocFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Clks  : CLOCKS   Ids)
       (Str   : STREAM        Op OpAux)
       (CE    : COREEXPR Ids  Op OpAux Clks Str)
<: SYBLOC Ids Op OpAux Clks Str CE.

  Module Export Syn   := SBSyntaxFun      Ids Op       Clks CE.Syn.
  Module Export Block := SBIsBlockFun     Ids Op       Clks CE.Syn Syn.
  Module Export Ord   := SBOrderedFun     Ids Op       Clks CE.Syn Syn Block.
  Module Export Sem   := SBSemanticsFun   Ids Op OpAux Clks CE.Syn Syn Block Ord Str CE.Sem.
  Module Export Last  := SBIsLastFun      Ids Op       Clks CE.Syn Syn.
  Module Export Var   := SBIsVariableFun  Ids Op       Clks CE.Syn Syn.
  Module Export Def   := SBIsDefinedFun   Ids Op       Clks CE.Syn Syn Var Last.
  Module Export Free  := SBIsFreeFun      Ids Op       Clks CE.Syn Syn CE.IsF.
  Module Export Wdef  := SBWellDefinedFun Ids Op       Clks CE.Syn Syn Block Ord Var Last Def CE.IsF Free.
  Module Export Typ   := SBTypingFun      Ids Op       Clks CE.Syn Syn CE.Typ.
  Module Export Clo   := SBClockingFun    Ids Op       Clks CE.Syn Syn Last Var Def CE.Clo.

  Module Scheduler    := SBScheduleFun    Ids Op OpAux Clks CE.Syn Syn Block Ord Str CE.Sem Sem CE.Typ Typ.
End SyBlocFun.
