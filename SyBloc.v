Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Export Velus.NLustre.Stream.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.SyBloc.SBIsBlock.
Require Import Velus.SyBloc.SBOrdered.
Require Import Velus.NLustre.NLExprSemantics.
Require Import Velus.SyBloc.SBSemantics.
Require Import Velus.SyBloc.SBIsLast.
Require Import Velus.SyBloc.SBIsVariable.
Require Import Velus.SyBloc.SBIsDefined.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.IsFree.
Require Import Velus.SyBloc.SBIsFree.
Require Import Velus.SyBloc.SBWellDefined.
Require Import Velus.SyBloc.SBSchedule.

Module Type SYBLOC
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX       Op)
       (Clks   : CLOCKS          Ids)
       (ExprSyn: NLEXPRSYNTAX        Op)
       (Str    : STREAM              Op OpAux)
       (ExprSem: NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn Str)
       (SynNL  : NLSYNTAX        Ids Op       Clks ExprSyn)
       (FreeNL : ISFREE          Ids Op       Clks ExprSyn     SynNL).

  Declare Module Export Syn  : SBSYNTAX      Ids Op       Clks ExprSyn.
  Declare Module Export Block: SBISBLOCK     Ids Op       Clks ExprSyn Syn.
  Declare Module Export Ord  : SBORDERED     Ids Op       Clks ExprSyn Syn Block.
  Declare Module Export Sem  : SBSEMANTICS   Ids Op OpAux Clks ExprSyn Syn Block Ord Str ExprSem.
  Declare Module Export Last : SBISLAST      Ids Op       Clks ExprSyn Syn.
  Declare Module Export Var  : SBISVARIABLE  Ids Op       Clks ExprSyn Syn.
  Declare Module Export Def  : SBISDEFINED   Ids Op       Clks ExprSyn Syn Var Last.
  Declare Module Export Free : SBISFREE      Ids Op       Clks ExprSyn Syn SynNL FreeNL.
  Declare Module Export Wdef : SBWELLDEFINED Ids Op       Clks ExprSyn Syn Block Ord Var Last Def SynNL FreeNL Free.

  Declare Module Scheduler   : SBSCHEDULE    Ids Op OpAux Clks ExprSyn Syn Block Ord Str ExprSem Sem.

End SYBLOC.

Module SyBlocFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX Op)
       (Clks   : CLOCKS    Ids)
       (ExprSyn: NLEXPRSYNTAX  Op)
       (Str    : STREAM              Op OpAux)
       (ExprSem: NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn Str)
       (SynNL  : NLSYNTAX  Ids Op Clks ExprSyn)
       (FreeNL : ISFREE    Ids Op Clks ExprSyn SynNL)
<: SYBLOC Ids Op OpAux Clks ExprSyn Str ExprSem SynNL FreeNL.

  Module Export Syn   := SBSyntaxFun      Ids Op       Clks ExprSyn.
  Module Export Block := SBIsBlockFun     Ids Op       Clks ExprSyn Syn.
  Module Export Ord   := SBOrderedFun     Ids Op       Clks ExprSyn Syn Block.
  Module Export Sem   := SBSemanticsFun   Ids Op OpAux Clks ExprSyn Syn Block Ord Str ExprSem.
  Module Export Last  := SBIsLastFun      Ids Op       Clks ExprSyn Syn.
  Module Export Var   := SBIsVariableFun  Ids Op       Clks ExprSyn Syn.
  Module Export Def   := SBIsDefinedFun   Ids Op       Clks ExprSyn Syn Var Last.
  Module Export Free  := SBIsFreeFun      Ids Op       Clks ExprSyn Syn SynNL FreeNL.
  Module Export Wdef  := SBWellDefinedFun Ids Op       Clks ExprSyn Syn Block Ord Var Last Def SynNL FreeNL Free.

  Module Scheduler    := SBScheduleFun    Ids Op OpAux Clks ExprSyn Syn Block Ord Str ExprSem Sem.
End SyBlocFun.
