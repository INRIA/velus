From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import IndexedStreams.
From Velus Require Import CommonTyping.

From Velus Require Import CoreExpr.CoreExpr.
From Velus Require Export NLustre.NLSyntax.
From Velus Require Export NLustre.IsDefined.
From Velus Require Export NLustre.Memories.
From Velus Require Export NLustre.NLIndexedSemantics.
From Velus Require Export NLustre.NLOrdered.
From Velus Require Export NLustre.NLClocking.
From Velus Require Export NLustre.NLTyping.
From Velus Require Export NLustre.NLNormalArgs.
From Velus Require Export NLustre.DupRegRem.DRR.
From Velus Require Export NLustre.DupRegRem.DRRTyping.
From Velus Require Export NLustre.DupRegRem.DRRClocking.
From Velus Require Export NLustre.DupRegRem.DRRNormalArgs.
From Velus Require Export NLustre.DupRegRem.DRRCorrectness.

Module Type DUPREGREM
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (ComTyp: COMMONTYPING Ids Op OpAux)
       (Cks   : CLOCKS Ids Op OpAux)
       (IStr  : INDEXEDSTREAMS Ids Op OpAux Cks)
       (CE    : COREEXPR Ids Op OpAux ComTyp Cks IStr)
       (Syn   : NLSYNTAX Ids Op OpAux Cks CE.Syn)
       (Ord   : NLORDERED Ids Op OpAux Cks CE.Syn Syn)
       (Typ   : NLTYPING Ids Op OpAux Cks CE.Syn Syn Ord CE.Typ)
       (Norm  : NLNORMALARGS Ids Op OpAux Cks CE.Syn CE.Typ Syn Ord Typ)
       (Mem   : MEMORIES Ids Op OpAux Cks CE.Syn Syn)
       (IsD   : ISDEFINED Ids Op OpAux Cks CE.Syn Syn Mem)
       (Clo   : NLCLOCKING Ids Op OpAux Cks CE.Syn Syn Ord Mem IsD CE.Clo)
       (Sem   : NLINDEXEDSEMANTICS Ids Op OpAux Cks CE.Syn Syn IStr Ord CE.Sem).
  Declare Module Export DRR        : DRR                  Ids Op OpAux Cks CE.Syn Syn.
  Declare Module Export DRRTyp     : DRRTYPING            Ids Op OpAux Cks CE.Syn CE.Typ Syn Ord Typ DRR.
  Declare Module Export DRRClo     : DRRCLOCKING          Ids Op OpAux Cks CE.Syn CE.Clo Syn Ord Mem IsD Clo DRR.
  Declare Module Export DRRNorm    : DRRNORMALARGS        Ids Op OpAux Cks CE.Syn CE.Typ Syn Ord Typ Norm DRR.
  Declare Module Export DRRCor     : DRRCORRECTNESS       Ids Op OpAux Cks IStr CE.Syn CE.Sem Syn Ord Sem DRR.
End DUPREGREM.

Module DupRegRemFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (ComTyp: COMMONTYPING Ids Op OpAux)
       (Cks   : CLOCKS Ids Op OpAux)
       (IStr  : INDEXEDSTREAMS Ids Op OpAux Cks)
       (CE    : COREEXPR Ids Op OpAux ComTyp Cks IStr)
       (Syn   : NLSYNTAX Ids Op OpAux Cks CE.Syn)
       (Ord   : NLORDERED Ids Op OpAux Cks CE.Syn Syn)
       (Typ   : NLTYPING Ids Op OpAux Cks CE.Syn Syn Ord CE.Typ)
       (Norm  : NLNORMALARGS Ids Op OpAux Cks CE.Syn CE.Typ Syn Ord Typ)
       (Mem   : MEMORIES Ids Op OpAux Cks CE.Syn Syn)
       (IsD   : ISDEFINED Ids Op OpAux Cks CE.Syn Syn Mem)
       (Clo   : NLCLOCKING Ids Op OpAux Cks CE.Syn Syn Ord Mem IsD CE.Clo)
       (Sem   : NLINDEXEDSEMANTICS Ids Op OpAux Cks CE.Syn Syn IStr Ord CE.Sem)
       <: DUPREGREM Ids Op OpAux ComTyp Cks IStr CE Syn Ord Typ Norm Mem IsD Clo Sem.
  Module Export DRR        := DRRFun                  Ids Op OpAux Cks CE.Syn Syn.
  Module Export DRRTyp     := DrrTypingFun            Ids Op OpAux Cks CE.Syn CE.Typ Syn Ord Typ DRR.
  Module Export DRRClo     := DrrClockingFun          Ids Op OpAux Cks CE.Syn CE.Clo Syn Ord Mem IsD Clo DRR.
  Module Export DRRNorm    := DrrNormalArgsFun        Ids Op OpAux Cks CE.Syn CE.Typ Syn Ord Typ Norm DRR.
  Module Export DRRCor     := DrrCorrectnessFun       Ids Op OpAux Cks IStr CE.Syn CE.Sem Syn Ord Sem DRR.
End DupRegRemFun.
