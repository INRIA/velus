Require Export Operators.
Require Export Clocks.
Require Export NLustre.Stream.
Require Export NLustre.NLExprSyntax.
Require Export NLustre.NLSyntax.
Require Export NLustre.IsFreeExpr.
Require Export NLustre.IsFree.
Require Export NLustre.IsVariable.
Require Export NLustre.IsDefined.
Require Export NLustre.Memories.
Require Export NLustre.NLExprSemantics.
Require Export NLustre.NLSemantics.
Require Export NLustre.MemSemantics.
Require Export NLustre.Ordered.
Require Export NLustre.NoDup.
Require Export NLustre.NLClockingExpr.
Require Export NLustre.NLClocking.
Require Export NLustre.NLClockingSemantics.
Require Export NLustre.NLTyping.

Require Import Velus.Common.

Module Type NLUSTRE
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX       Op)
       (Clks   : CLOCKS         Ids)
       (ExprSyn: NLEXPRSYNTAX        Op)
       (Str    : STREAM              Op OpAux)
       (ExprSem: NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn Str)
       (IsFExpr: ISFREEEXPR      Ids Op       Clks ExprSyn)
       (CloExpr: NLCLOCKINGEXPR  Ids Op       Clks ExprSyn).

  Declare Module Export Syn    : NLSYNTAX        Ids Op       Clks ExprSyn.
  Declare Module Export Ord    : ORDERED         Ids Op       Clks ExprSyn Syn.
  Declare Module Export IsF    : ISFREE          Ids Op       Clks ExprSyn Syn IsFExpr.
  Declare Module Export Sem    : NLSEMANTICS     Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem.
  Declare Module Export Typ    : NLTYPING        Ids Op       Clks ExprSyn Syn.
  Declare Module Export Mem    : MEMORIES        Ids Op       Clks ExprSyn Syn.
  Declare Module Export IsD    : ISDEFINED       Ids Op       Clks ExprSyn Syn                     Mem.
  Declare Module Export IsV    : ISVARIABLE      Ids Op       Clks ExprSyn Syn                     Mem IsD.
  Declare Module Export NoD    : NODUP           Ids Op       Clks ExprSyn Syn                     Mem IsD IsV.
  Declare Module Export Clo    : NLCLOCKING      Ids Op       Clks ExprSyn Syn     Ord             Mem IsD IsFExpr IsF CloExpr.
  Declare Module Export CloSem : NLCLOCKINGSEMANTICS Ids Op OpAux Clks ExprSyn Syn
                                                     Str Ord ExprSem Sem Mem IsD IsFExpr IsF CloExpr Clo.
  Declare Module Export MemSem : MEMSEMANTICS    Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem Sem Mem IsD IsV IsFExpr IsF NoD CloExpr Clo CloSem.

End NLUSTRE.

Module NLustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Clks  : CLOCKS Ids)
       (ExprSyn: NLEXPRSYNTAX  Op)
       (Str    : STREAM              Op OpAux)
       (ExprSem: NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn Str)
       (IsFExpr: ISFREEEXPR      Ids Op       Clks ExprSyn)
       (CloExpr: NLCLOCKINGEXPR  Ids Op       Clks ExprSyn)
<: NLUSTRE Ids Op OpAux Clks ExprSyn Str ExprSem IsFExpr CloExpr.
  Module Export Syn     := NLSyntaxFun        Ids Op       Clks ExprSyn.
  Module Export Ord     := OrderedFun         Ids Op       Clks ExprSyn Syn.
  Module Export IsF     := IsFreeFun          Ids Op       Clks ExprSyn Syn IsFExpr.
  Module Export Sem     := NLSemanticsFun     Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem.
  Module Export Typ     := NLTypingFun        Ids Op       Clks ExprSyn Syn.
  Module Export Mem     := MemoriesFun        Ids Op       Clks ExprSyn Syn.
  Module Export IsD     := IsDefinedFun       Ids Op       Clks ExprSyn Syn                     Mem.
  Module Export IsV     := IsVariableFun      Ids Op       Clks ExprSyn Syn                     Mem IsD.
  Module Export NoD     := NoDupFun           Ids Op       Clks ExprSyn Syn                     Mem IsD IsV.
  Module Export Clo     := NLClockingFun      Ids Op       Clks ExprSyn Syn     Ord             Mem IsD IsFExpr IsF CloExpr.
  Module Export CloSem  := NLClockingSemanticsFun Ids Op OpAux Clks ExprSyn Syn
                                                     Str Ord ExprSem Sem Mem IsD IsFExpr IsF CloExpr Clo.
  Module Export MemSem  := MemSemanticsFun    Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem Sem Mem IsD IsV IsFExpr IsF NoD CloExpr Clo CloSem.

End NLustreFun.
