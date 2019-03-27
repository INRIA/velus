Require Export Velus.Common.
Require Export Velus.Operators.
Require Export Velus.Clocks.
Require Export Velus.NLustre.Stream.
Require Export Velus.NLustre.NLExprSyntax.
Require Export Velus.SyBloc.SBSyntax.
Require Export Velus.SyBloc.SBIsBlock.
Require Export Velus.SyBloc.SBOrdered.
Require Export Velus.NLustre.NLExprSemantics.
Require Export Velus.SyBloc.SBSemantics.
Require Export Velus.SyBloc.SBIsLast.
Require Export Velus.SyBloc.SBIsVariable.
Require Export Velus.SyBloc.SBIsDefined.
Require Export Velus.NLustre.IsFreeExpr.
Require Export Velus.SyBloc.SBIsFree.
Require Export Velus.SyBloc.SBWellDefined.
Require Export Velus.SyBloc.SBSchedule.
Require Export Velus.NLustre.NLClockingExpr.
Require Export Velus.SyBloc.SBClocking.

Module Type SYBLOC
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX       Op)
       (Clks   : CLOCKS          Ids)
       (ExprSyn: NLEXPRSYNTAX        Op)
       (Str    : STREAM              Op OpAux)
       (ExprSem: NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn Str)
       (IsFExpr: ISFREEEXPR      Ids Op       Clks ExprSyn)
       (CloExpr: NLCLOCKINGEXPR  Ids Op       Clks ExprSyn).

  Declare Module Export Syn  : SBSYNTAX      Ids Op       Clks ExprSyn.
  Declare Module Export Block: SBISBLOCK     Ids Op       Clks ExprSyn Syn.
  Declare Module Export Ord  : SBORDERED     Ids Op       Clks ExprSyn Syn Block.
  Declare Module Export Sem  : SBSEMANTICS   Ids Op OpAux Clks ExprSyn Syn Block Ord Str ExprSem.
  Declare Module Export Last : SBISLAST      Ids Op       Clks ExprSyn Syn.
  Declare Module Export Var  : SBISVARIABLE  Ids Op       Clks ExprSyn Syn.
  Declare Module Export Def  : SBISDEFINED   Ids Op       Clks ExprSyn Syn Var Last.
  Declare Module Export Free : SBISFREE      Ids Op       Clks ExprSyn Syn IsFExpr.
  Declare Module Export Wdef : SBWELLDEFINED Ids Op       Clks ExprSyn Syn Block Ord Var Last Def IsFExpr Free.
  Declare Module Export Clo  : SBCLOCKING    Ids Op       Clks ExprSyn Syn Last Var Def CloExpr.

  Declare Module Scheduler   : SBSCHEDULE    Ids Op OpAux Clks ExprSyn Syn Block Ord Str ExprSem Sem.

End SYBLOC.

Module SyBlocFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX       Op)
       (Clks   : CLOCKS          Ids)
       (ExprSyn: NLEXPRSYNTAX        Op)
       (Str    : STREAM              Op OpAux)
       (ExprSem: NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn Str)
       (IsFExpr: ISFREEEXPR      Ids Op       Clks ExprSyn)
       (CloExpr: NLCLOCKINGEXPR  Ids Op       Clks ExprSyn)
<: SYBLOC Ids Op OpAux Clks ExprSyn Str ExprSem IsFExpr CloExpr.

  Module Export Syn   := SBSyntaxFun      Ids Op       Clks ExprSyn.
  Module Export Block := SBIsBlockFun     Ids Op       Clks ExprSyn Syn.
  Module Export Ord   := SBOrderedFun     Ids Op       Clks ExprSyn Syn Block.
  Module Export Sem   := SBSemanticsFun   Ids Op OpAux Clks ExprSyn Syn Block Ord Str ExprSem.
  Module Export Last  := SBIsLastFun      Ids Op       Clks ExprSyn Syn.
  Module Export Var   := SBIsVariableFun  Ids Op       Clks ExprSyn Syn.
  Module Export Def   := SBIsDefinedFun   Ids Op       Clks ExprSyn Syn Var Last.
  Module Export Free  := SBIsFreeFun      Ids Op       Clks ExprSyn Syn IsFExpr.
  Module Export Wdef  := SBWellDefinedFun Ids Op       Clks ExprSyn Syn Block Ord Var Last Def IsFExpr Free.
  Module Export Clo   := SBClockingFun    Ids Op       Clks ExprSyn Syn Last Var Def CloExpr.

  Module Scheduler    := SBScheduleFun    Ids Op OpAux Clks ExprSyn Syn Block Ord Str ExprSem Sem.
End SyBlocFun.
