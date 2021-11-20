From Velus Require Export CoreExpr.
From Velus Require Export NLustre.NLSyntax.
From Velus Require Export NLustre.IsFree.
From Velus Require Export NLustre.IsVariable.
From Velus Require Export NLustre.IsDefined.
From Velus Require Export NLustre.Memories.
From Velus Require Export NLustre.NLIndexedSemantics.
From Velus Require Export NLustre.NLCoindSemantics.
From Velus Require Export NLustre.NLCoindToIndexed.
From Velus Require Export NLustre.NLMemSemantics.
From Velus Require Export NLustre.NLOrdered.
From Velus Require Export NLustre.NoDup.
From Velus Require Export NLustre.NLClocking.
From Velus Require Export NLustre.NLClockingSemantics.
From Velus Require Export NLustre.NLTyping.
From Velus Require Export NLustre.NLNormalArgs.
From Velus Require Export NLustre.DupRegRem.DupRegRem.
From Velus Require Export CoindStreams.
From Velus Require Import CoindToIndexed.

From Velus Require Import Common.

Module Type NLUSTRE
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (ComTyp: COMMONTYPING   Ids Op OpAux)
       (Cks   : CLOCKS         Ids Op OpAux)
       (CStr  : COINDSTREAMS   Ids Op OpAux Cks)
       (IStr  : INDEXEDSTREAMS Ids Op OpAux Cks)
       (CIStr : COINDTOINDEXED Ids Op OpAux Cks CStr IStr)
       (CE    : COREEXPR       Ids Op OpAux ComTyp Cks IStr).
  Declare Module Export Syn        : NLSYNTAX             Ids Op OpAux Cks CE.Syn.
  Declare Module Export Ord        : NLORDERED            Ids Op OpAux Cks CE.Syn Syn.
  Declare Module Export IsF        : ISFREE               Ids Op OpAux Cks CE.Syn Syn CE.IsF.
  Declare Module Export CoindSem   : NLCOINDSEMANTICS     Ids Op OpAux Cks CE.Syn Syn CStr Ord.
  Declare Module Export Sem        : NLINDEXEDSEMANTICS   Ids Op OpAux Cks CE.Syn Syn IStr Ord CE.Sem.
  Declare Module Export CoindToIdx : NLCOINDTOINDEXED     Ids Op OpAux Cks CE.Syn Syn IStr CStr CIStr Ord CE.Sem Sem CoindSem.
  Declare Module Export Typ        : NLTYPING             Ids Op OpAux Cks CE.Syn Syn      Ord CE.Typ.
  Declare Module Export Norm       : NLNORMALARGS         Ids Op OpAux Cks CE.Syn CE.Typ Syn Ord Typ.
  Declare Module Export Mem        : MEMORIES             Ids Op OpAux Cks CE.Syn Syn.
  Declare Module Export IsD        : ISDEFINED            Ids Op OpAux Cks CE.Syn Syn                     Mem.
  Declare Module Export IsV        : ISVARIABLE           Ids Op OpAux Cks CE.Syn Syn                     Mem IsD.
  Declare Module Export NoD        : NODUP                Ids Op OpAux Cks CE.Syn Syn                     Mem IsD IsV.
  Declare Module Export Clo        : NLCLOCKING           Ids Op OpAux Cks CE.Syn Syn     Ord             Mem IsD CE.Clo.
  Declare Module Export CloSem     : NLCLOCKINGSEMANTICS  Ids Op OpAux Cks CE.Syn Syn IStr Ord CE.Sem Sem Mem IsD CE.Clo Clo CE.CloSem.
  Declare Module Export MemSem     : NLMEMSEMANTICS       Ids Op OpAux Cks CE.Syn Syn IStr Ord CE.Sem Sem Mem IsD IsV NoD CE.Clo Clo CE.CloSem CloSem.

  Declare Module Export DRR        : DUPREGREM            Ids Op OpAux ComTyp Cks IStr CE Syn Ord Typ Norm Mem IsD Clo Sem.
End NLUSTRE.

Module NLustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (ComTyp: COMMONTYPING   Ids Op OpAux)
       (Cks   : CLOCKS         Ids Op OpAux)
       (CStr  : COINDSTREAMS   Ids Op OpAux Cks)
       (IStr  : INDEXEDSTREAMS Ids Op OpAux Cks)
       (CIStr : COINDTOINDEXED Ids Op OpAux Cks CStr IStr)
       (CE    : COREEXPR       Ids Op OpAux ComTyp Cks IStr)
<: NLUSTRE Ids Op OpAux ComTyp Cks CStr IStr CIStr CE.
  Module Export Syn        := NLSyntaxFun             Ids Op OpAux Cks CE.Syn.
  Module Export Ord        := NLOrderedFun            Ids Op OpAux Cks CE.Syn Syn.
  Module Export IsF        := IsFreeFun               Ids Op OpAux Cks CE.Syn Syn CE.IsF.
  Module Export CoindSem   := NLCoindSemanticsFun     Ids Op OpAux Cks CE.Syn Syn CStr Ord.
  Module Export Sem        := NLIndexedSemanticsFun   Ids Op OpAux Cks CE.Syn Syn IStr Ord CE.Sem.
  Module Export CoindToIdx := NLCoindToIndexedFun     Ids Op OpAux Cks CE.Syn Syn IStr CStr CIStr Ord CE.Sem Sem CoindSem.
  Module Export Typ        := NLTypingFun             Ids Op OpAux Cks CE.Syn Syn     Ord CE.Typ.
  Module Export Norm       := NLNormalArgsFun         Ids Op OpAux Cks CE.Syn CE.Typ Syn Ord Typ.
  Module Export Mem        := MemoriesFun             Ids Op OpAux Cks CE.Syn Syn.
  Module Export IsD        := IsDefinedFun            Ids Op OpAux Cks CE.Syn Syn                     Mem.
  Module Export IsV        := IsVariableFun           Ids Op OpAux Cks CE.Syn Syn                     Mem IsD.
  Module Export NoD        := NoDupFun                Ids Op OpAux Cks CE.Syn Syn                     Mem IsD IsV.
  Module Export Clo        := NLClockingFun           Ids Op OpAux Cks CE.Syn Syn     Ord             Mem IsD CE.Clo.
  Module Export CloSem     := NLClockingSemanticsFun  Ids Op OpAux Cks CE.Syn Syn IStr Ord CE.Sem Sem Mem IsD CE.Clo Clo CE.CloSem.
  Module Export MemSem     := NLMemSemanticsFun       Ids Op OpAux Cks CE.Syn Syn IStr Ord CE.Sem Sem Mem IsD IsV NoD CE.Clo Clo CE.CloSem CloSem.

  Module Export DRR        := DupRegRemFun            Ids Op OpAux ComTyp Cks IStr CE Syn Ord Typ Norm Mem IsD Clo Sem.
End NLustreFun.
