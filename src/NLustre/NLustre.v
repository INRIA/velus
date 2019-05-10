From Velus Require Export CoreExpr.
From Velus Require Export NLustre.NLSyntax.
From Velus Require Export NLustre.IsFree.
From Velus Require Export NLustre.IsVariable.
From Velus Require Export NLustre.IsDefined.
From Velus Require Export NLustre.Memories.
From Velus Require Export NLustre.NLSemantics.
From Velus Require Export NLustre.MemSemantics.
From Velus Require Export NLustre.NLOrdered.
From Velus Require Export NLustre.NoDup.
From Velus Require Export NLustre.NLClocking.
From Velus Require Export NLustre.NLClockingSemantics.
From Velus Require Export NLustre.NLTyping.
From Velus Require Export NLustre.NLNormalArgs.

From Velus Require Import Common.

Module Type NLUSTRE
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str   : STREAM        Op OpAux)
       (CE    : COREEXPR Ids  Op OpAux Str).
  Declare Module Export Syn    : NLSYNTAX        Ids Op       CE.Syn.
  Declare Module Export Ord    : NLORDERED       Ids Op       CE.Syn Syn.
  Declare Module Export Norm   : NLNORMALARGS    Ids Op       CE.Syn Syn.
  Declare Module Export IsF    : ISFREE          Ids Op       CE.Syn Syn CE.IsF.
  Declare Module Export Sem    : NLSEMANTICS     Ids Op OpAux CE.Syn Syn Str Ord CE.Sem.
  Declare Module Export Typ    : NLTYPING        Ids Op       CE.Syn Syn     Ord CE.Typ.
  Declare Module Export Mem    : MEMORIES        Ids Op       CE.Syn Syn.
  Declare Module Export IsD    : ISDEFINED       Ids Op       CE.Syn Syn                     Mem.
  Declare Module Export IsV    : ISVARIABLE      Ids Op       CE.Syn Syn                     Mem IsD.
  Declare Module Export NoD    : NODUP           Ids Op       CE.Syn Syn                     Mem IsD IsV.
  Declare Module Export Clo    : NLCLOCKING      Ids Op       CE.Syn Syn     Ord             Mem IsD CE.IsF IsF CE.Clo.
  Declare Module Export CloSem : NLCLOCKINGSEMANTICS Ids Op OpAux CE.Syn Syn Str Ord CE.Sem
                                                     Sem Mem IsD CE.IsF IsF CE.Clo Clo CE.CloSem.
  Declare Module Export MemSem : MEMSEMANTICS    Ids Op OpAux CE.Syn Syn Str Ord CE.Sem Sem Mem IsD IsV CE.IsF IsF NoD CE.Clo Clo CE.CloSem CloSem.
End NLUSTRE.

Module NLustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str   : STREAM        Op OpAux)
       (CE    : COREEXPR Ids  Op OpAux Str)
<: NLUSTRE Ids Op OpAux Str CE.
  Module Export Syn    := NLSyntaxFun        Ids Op       CE.Syn.
  Module Export Ord    := NLOrderedFun       Ids Op       CE.Syn Syn.
  Module Export Norm   := NLNormalArgsFun    Ids Op       CE.Syn Syn.
  Module Export IsF    := IsFreeFun          Ids Op       CE.Syn Syn CE.IsF.
  Module Export Sem    := NLSemanticsFun     Ids Op OpAux CE.Syn Syn Str Ord CE.Sem.
  Module Export Typ    := NLTypingFun        Ids Op       CE.Syn Syn     Ord CE.Typ.
  Module Export Mem    := MemoriesFun        Ids Op       CE.Syn Syn.
  Module Export IsD    := IsDefinedFun       Ids Op       CE.Syn Syn                     Mem.
  Module Export IsV    := IsVariableFun      Ids Op       CE.Syn Syn                     Mem IsD.
  Module Export NoD    := NoDupFun           Ids Op       CE.Syn Syn                     Mem IsD IsV.
  Module Export Clo    := NLClockingFun      Ids Op       CE.Syn Syn     Ord             Mem IsD CE.IsF IsF CE.Clo.
  Module Export CloSem := NLClockingSemanticsFun Ids Op OpAux CE.Syn Syn Str Ord CE.Sem
                                                 Sem Mem IsD CE.IsF IsF CE.Clo Clo CE.CloSem.
  Module Export MemSem := MemSemanticsFun    Ids Op OpAux CE.Syn Syn Str Ord CE.Sem Sem Mem IsD IsV CE.IsF IsF NoD CE.Clo Clo CE.CloSem CloSem.
End NLustreFun.
