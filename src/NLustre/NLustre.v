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
From Velus Require Export CoindStreams.
From Velus Require Import CoindToIndexed.

From Velus Require Import Common.

Module Type NLUSTRE
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Op)
       (CStr  : COINDSTREAMS   Op OpAux)
       (IStr  : INDEXEDSTREAMS Op OpAux)
       (CIStr : COINDTOINDEXED Op OpAux CStr IStr)
       (CE    : COREEXPR Ids   Op OpAux IStr).
  Declare Module Export Syn        : NLSYNTAX             Ids Op       CE.Syn.
  Declare Module Export Ord        : NLORDERED            Ids Op       CE.Syn Syn.
  Declare Module Export Norm       : NLNORMALARGS         Ids Op       CE.Syn Syn.
  Declare Module Export IsF        : ISFREE               Ids Op       CE.Syn Syn CE.IsF.
  Declare Module Export CoindSem   : NLCOINDSEMANTICS     Ids Op OpAux CE.Syn Syn CStr Ord.
  Declare Module Export Sem        : NLINDEXEDSEMANTICS   Ids Op OpAux CE.Syn Syn IStr Ord CE.Sem.
  Declare Module Export CoindToIdx : NLCOINDTOINDEXED     Ids Op OpAux CE.Syn Syn IStr CStr CIStr Ord CE.Sem Sem CoindSem.
  Declare Module Export Typ        : NLTYPING             Ids Op       CE.Syn Syn     Ord CE.Typ.
  Declare Module Export Mem        : MEMORIES             Ids Op       CE.Syn Syn.
  Declare Module Export IsD        : ISDEFINED            Ids Op       CE.Syn Syn                     Mem.
  Declare Module Export IsV        : ISVARIABLE           Ids Op       CE.Syn Syn                     Mem IsD.
  Declare Module Export NoD        : NODUP                Ids Op       CE.Syn Syn                     Mem IsD IsV.
  Declare Module Export Clo        : NLCLOCKING           Ids Op       CE.Syn Syn     Ord             Mem IsD CE.Clo.
  Declare Module Export CloSem     : NLCLOCKINGSEMANTICS  Ids Op OpAux CE.Syn Syn IStr Ord CE.Sem Sem Mem IsD CE.Clo Clo CE.CloSem.
  Declare Module Export MemSem     : NLMEMSEMANTICS       Ids Op OpAux CE.Syn Syn IStr Ord CE.Sem Sem Mem IsD IsV NoD CE.Clo Clo CE.CloSem CloSem.
End NLUSTRE.

Module NLustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Op)
       (CStr  : COINDSTREAMS   Op OpAux)
       (IStr  : INDEXEDSTREAMS Op OpAux)
       (CIStr : COINDTOINDEXED Op OpAux CStr IStr)
       (CE    : COREEXPR Ids   Op OpAux IStr)
<: NLUSTRE Ids Op OpAux CStr IStr CIStr CE.
  Module Export Syn        := NLSyntaxFun             Ids Op       CE.Syn.
  Module Export Ord        := NLOrderedFun            Ids Op       CE.Syn Syn.
  Module Export Norm       := NLNormalArgsFun         Ids Op       CE.Syn Syn.
  Module Export IsF        := IsFreeFun               Ids Op       CE.Syn Syn CE.IsF.
  Module Export CoindSem   := NLCoindSemanticsFun     Ids Op OpAux CE.Syn Syn CStr Ord.
  Module Export Sem        := NLIndexedSemanticsFun   Ids Op OpAux CE.Syn Syn IStr Ord CE.Sem.
  Module Export CoindToIdx := NLCoindToIndexedFun     Ids Op OpAux CE.Syn Syn IStr CStr CIStr Ord CE.Sem Sem CoindSem.
  Module Export Typ        := NLTypingFun             Ids Op       CE.Syn Syn     Ord CE.Typ.
  Module Export Mem        := MemoriesFun             Ids Op       CE.Syn Syn.
  Module Export IsD        := IsDefinedFun            Ids Op       CE.Syn Syn                     Mem.
  Module Export IsV        := IsVariableFun           Ids Op       CE.Syn Syn                     Mem IsD.
  Module Export NoD        := NoDupFun                Ids Op       CE.Syn Syn                     Mem IsD IsV.
  Module Export Clo        := NLClockingFun           Ids Op       CE.Syn Syn     Ord             Mem IsD CE.Clo.
  Module Export CloSem     := NLClockingSemanticsFun  Ids Op OpAux CE.Syn Syn IStr Ord CE.Sem Sem Mem IsD CE.Clo Clo CE.CloSem.
  Module Export MemSem     := NLMemSemanticsFun       Ids Op OpAux CE.Syn Syn IStr Ord CE.Sem Sem Mem IsD IsV NoD CE.Clo Clo CE.CloSem CloSem.
End NLustreFun.
