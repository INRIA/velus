From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import IndexedStreams.
From Velus Require Import CommonTyping.

From Velus Require Import CoreExpr.CoreExpr.
From Velus Require Export NLustre.NLSyntax.
From Velus Require Export NLustre.IsFree.
From Velus Require Export NLustre.IsDefined.
From Velus Require Export NLustre.Memories.
From Velus Require Export NLustre.NLIndexedSemantics.
From Velus Require Export NLustre.NLOrdered.
From Velus Require Export NLustre.NLClocking.
From Velus Require Export NLustre.NLTyping.
From Velus Require Export NLustre.NLNormalArgs.
From Velus Require Export NLustre.DeadCodeElim.DCE.
From Velus Require Export NLustre.DeadCodeElim.DCETyping.
From Velus Require Export NLustre.DeadCodeElim.DCEClocking.
From Velus Require Export NLustre.DeadCodeElim.DCENormalArgs.
From Velus Require Export NLustre.DeadCodeElim.DCECorrectness.


Module Type DEADCODEELIM
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
       (IsF   : ISFREE Ids Op OpAux Cks CE.Syn Syn CE.IsF)
       (Mem   : MEMORIES Ids Op OpAux Cks CE.Syn Syn)
       (IsD   : ISDEFINED Ids Op OpAux Cks CE.Syn Syn Mem)
       (Clo   : NLCLOCKING Ids Op OpAux Cks CE.Syn Syn Ord Mem IsD CE.Clo)
       (Sem   : NLINDEXEDSEMANTICS Ids Op OpAux Cks CE.Syn Syn IStr Ord CE.Sem).
  Declare Module Export DCE        : DCE                  Ids Op OpAux Cks CE.Syn CE.IsF Syn IsF Mem IsD.
  Declare Module Export DCETyp     : DCETYPING            Ids Op OpAux Cks CE.Syn CE.IsF CE.Typ Syn IsF Mem IsD Ord Typ DCE.
  Declare Module Export DCEClo     : DCECLOCKING          Ids Op OpAux Cks CE.Syn CE.IsF CE.Clo Syn IsF Mem IsD Ord Clo DCE.
  Declare Module Export DCENorm    : DCENORMALARGS        Ids Op OpAux Cks CE.Syn CE.IsF CE.Typ Syn IsF Mem IsD Ord Typ Norm DCE.
  Declare Module Export DCECor     : DCECORRECTNESS       Ids Op OpAux Cks IStr CE.Syn CE.IsF CE.Sem Syn IsF Mem IsD Ord Sem DCE.
End DEADCODEELIM.

Module DeadCodeElimFun
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
       (IsF   : ISFREE Ids Op OpAux Cks CE.Syn Syn CE.IsF)
       (Mem   : MEMORIES Ids Op OpAux Cks CE.Syn Syn)
       (IsD   : ISDEFINED Ids Op OpAux Cks CE.Syn Syn Mem)
       (Clo   : NLCLOCKING Ids Op OpAux Cks CE.Syn Syn Ord Mem IsD CE.Clo)
       (Sem   : NLINDEXEDSEMANTICS Ids Op OpAux Cks CE.Syn Syn IStr Ord CE.Sem)
       <: DEADCODEELIM Ids Op OpAux ComTyp Cks IStr CE Syn Ord Typ Norm IsF Mem IsD Clo Sem.
  Module Export DCE        := DCEFun                  Ids Op OpAux Cks CE.Syn CE.IsF Syn IsF Mem IsD.
  Module Export DCETyp     := DCETypingFun            Ids Op OpAux Cks CE.Syn CE.IsF CE.Typ Syn IsF Mem IsD Ord Typ DCE.
  Module Export DCEClo     := DCEClockingFun          Ids Op OpAux Cks CE.Syn CE.IsF CE.Clo Syn IsF Mem IsD Ord Clo DCE.
  Module Export DCENorm    := DCENormalArgsFun        Ids Op OpAux Cks CE.Syn CE.IsF CE.Typ Syn IsF Mem IsD Ord Typ Norm DCE.
  Module Export DCECor     := DCECorrectnessFun       Ids Op OpAux Cks IStr CE.Syn CE.IsF CE.Sem Syn IsF Mem IsD Ord Sem DCE.
End DeadCodeElimFun.
