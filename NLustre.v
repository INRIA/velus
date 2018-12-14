Require Import Operators.
Require Import Clocks.
Require Export NLustre.Stream.
Require Import NLustre.NLExprSyntax.
Require Export NLustre.NLSyntax.
Require Export NLustre.IsFree.
Require Export NLustre.IsVariable.
Require Export NLustre.IsDefined.
Require Export NLustre.Memories.
Require Import NLustre.NLExprSemantics.
Require Export NLustre.NLSemantics.
Require Export NLustre.MemSemantics.
Require Export NLustre.WellFormed.
Require Export NLustre.Ordered.
Require Export NLustre.NoDup.
Require Export NLustre.NLClocking.
Require Export NLustre.NLTyping.
Require Export NLustre.NLSchedule.

Require Import Velus.Common.

Module Type NLUSTRE
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Clks  : CLOCKS Ids).
  Declare Module Export ExprSyn: NLEXPRSYNTAX        Op.
  Declare Module Export Syn    : NLSYNTAX        Ids Op       Clks ExprSyn.
  Declare Module Export Str    : STREAM              Op OpAux.
  Declare Module Export Ord    : ORDERED         Ids Op       Clks ExprSyn Syn.
  Declare Module Export IsF    : ISFREE          Ids Op       Clks ExprSyn Syn.
  Declare Module Export ExprSem: NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn     Str.
  Declare Module Export Sem    : NLSEMANTICS     Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem.
  Declare Module Export Typ    : NLTYPING        Ids Op       Clks ExprSyn Syn.
  Declare Module Export Mem    : MEMORIES        Ids Op       Clks ExprSyn Syn.
  Declare Module Export IsD    : ISDEFINED       Ids Op       Clks ExprSyn Syn                     Mem.
  Declare Module Export IsV    : ISVARIABLE      Ids Op       Clks ExprSyn Syn                     Mem IsD.
  Declare Module Export NoD    : NODUP           Ids Op       Clks ExprSyn Syn                     Mem IsD IsV.
  Declare Module Export WeF    : WELLFORMED      Ids Op       Clks ExprSyn Syn     Ord             Mem IsD IsV IsF NoD.
  Declare Module Export MemSem : MEMSEMANTICS    Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem Sem Mem IsD IsV IsF NoD WeF.
  Declare Module Export Clo    : NLCLOCKING      Ids Op       Clks ExprSyn Syn                     Mem IsD     IsF.

  Declare Module Scheduler     : NLSCHEDULE      Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem Sem Mem IsD     IsF          Typ Clo.

End NLUSTRE.

Module NLustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Clks  : CLOCKS Ids)
       <: NLUSTRE Ids Op OpAux Clks.
  Module Export ExprSyn := NLExprSyntaxFun        Op.
  Module Export Syn     := NLSyntaxFun        Ids Op       Clks ExprSyn.
  Module Export Str     := StreamFun              Op OpAux.
  Module Export Ord     := OrderedFun         Ids Op       Clks ExprSyn Syn.
  Module Export IsF     := IsFreeFun          Ids Op       Clks ExprSyn Syn.
  Module Export ExprSem := NLExprSemanticsFun Ids Op OpAux Clks ExprSyn     Str.
  Module Export Sem     := NLSemanticsFun     Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem.
  Module Export Typ     := NLTypingFun        Ids Op       Clks ExprSyn Syn.
  Module Export Mem     := MemoriesFun        Ids Op       Clks ExprSyn Syn.
  Module Export IsD     := IsDefinedFun       Ids Op       Clks ExprSyn Syn                     Mem.
  Module Export IsV     := IsVariableFun      Ids Op       Clks ExprSyn Syn                     Mem IsD.
  Module Export NoD     := NoDupFun           Ids Op       Clks ExprSyn Syn                     Mem IsD IsV.
  Module Export WeF     := WellFormedFun      Ids Op       Clks ExprSyn Syn     Ord             Mem IsD IsV IsF NoD.
  Module Export MemSem  := MemSemanticsFun    Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem Sem Mem IsD IsV IsF NoD WeF.
  Module Export Clo     := NLClockingFun      Ids Op       Clks ExprSyn Syn                     Mem IsD     IsF.

  Module Scheduler      := NLScheduleFun      Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem Sem Mem IsD IsF              Typ Clo.

End NLustreFun.
