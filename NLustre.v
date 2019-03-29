Require Export Velus.CoreExpr.
Require Export NLustre.NLSyntax.
Require Export NLustre.IsFree.
Require Export NLustre.IsVariable.
Require Export NLustre.IsDefined.
Require Export NLustre.Memories.
Require Export NLustre.NLSemantics.
Require Export NLustre.MemSemantics.
Require Export NLustre.Ordered.
Require Export NLustre.NoDup.
Require Export NLustre.NLClocking.
Require Export NLustre.NLClockingSemantics.
Require Export NLustre.NLTyping.

Require Import Velus.Common.

Module Type NLUSTRE
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Clks  : CLOCKS   Ids)
       (Str   : STREAM        Op OpAux)
       (CE    : COREEXPR Ids  Op OpAux Clks Str).
  Declare Module Export Syn    : NLSYNTAX        Ids Op       Clks CE.Syn.
  Declare Module Export Ord    : ORDERED         Ids Op       Clks CE.Syn Syn.
  Declare Module Export IsF    : ISFREE          Ids Op       Clks CE.Syn Syn CE.IsF.
  Declare Module Export Sem    : NLSEMANTICS     Ids Op OpAux Clks CE.Syn Syn Str Ord CE.Sem.
  Declare Module Export Typ    : NLTYPING        Ids Op       Clks CE.Syn Syn     Ord CE.Typ.
  Declare Module Export Mem    : MEMORIES        Ids Op       Clks CE.Syn Syn.
  Declare Module Export IsD    : ISDEFINED       Ids Op       Clks CE.Syn Syn                     Mem.
  Declare Module Export IsV    : ISVARIABLE      Ids Op       Clks CE.Syn Syn                     Mem IsD.
  Declare Module Export NoD    : NODUP           Ids Op       Clks CE.Syn Syn                     Mem IsD IsV.
  Declare Module Export Clo    : NLCLOCKING      Ids Op       Clks CE.Syn Syn     Ord             Mem IsD CE.IsF IsF CE.Clo.
  Declare Module Export CloSem : NLCLOCKINGSEMANTICS Ids Op OpAux Clks CE.Syn Syn
                                                     Str Ord CE.Sem Sem Mem IsD CE.IsF IsF CE.Clo Clo.
  Declare Module Export MemSem : MEMSEMANTICS    Ids Op OpAux Clks CE.Syn Syn Str Ord CE.Sem Sem Mem IsD IsV CE.IsF IsF NoD CE.Clo Clo CloSem.

End NLUSTRE.

Module NLustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Clks  : CLOCKS   Ids)
       (Str   : STREAM        Op OpAux)
       (CE    : COREEXPR Ids  Op OpAux Clks Str)
<: NLUSTRE Ids Op OpAux Clks Str CE.
  Module Export Syn     := NLSyntaxFun        Ids Op       Clks CE.Syn.
  Module Export Ord     := OrderedFun         Ids Op       Clks CE.Syn Syn.
  Module Export IsF     := IsFreeFun          Ids Op       Clks CE.Syn Syn CE.IsF.
  Module Export Sem     := NLSemanticsFun     Ids Op OpAux Clks CE.Syn Syn Str Ord CE.Sem.
  Module Export Typ     := NLTypingFun        Ids Op       Clks CE.Syn Syn     Ord CE.Typ.
  Module Export Mem     := MemoriesFun        Ids Op       Clks CE.Syn Syn.
  Module Export IsD     := IsDefinedFun       Ids Op       Clks CE.Syn Syn                     Mem.
  Module Export IsV     := IsVariableFun      Ids Op       Clks CE.Syn Syn                     Mem IsD.
  Module Export NoD     := NoDupFun           Ids Op       Clks CE.Syn Syn                     Mem IsD IsV.
  Module Export Clo     := NLClockingFun      Ids Op       Clks CE.Syn Syn     Ord             Mem IsD CE.IsF IsF CE.Clo.
  Module Export CloSem  := NLClockingSemanticsFun Ids Op OpAux Clks CE.Syn Syn
                                                     Str Ord CE.Sem Sem Mem IsD CE.IsF IsF CE.Clo Clo.
  Module Export MemSem  := MemSemanticsFun    Ids Op OpAux Clks CE.Syn Syn Str Ord CE.Sem Sem Mem IsD IsV CE.IsF IsF NoD CE.Clo Clo CloSem.

End NLustreFun.
