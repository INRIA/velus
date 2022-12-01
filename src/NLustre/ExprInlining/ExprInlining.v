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
From Velus Require Export NLustre.ExprInlining.EI.
From Velus Require Export NLustre.ExprInlining.EITyping.
From Velus Require Export NLustre.ExprInlining.EIClocking.
From Velus Require Export NLustre.ExprInlining.EINormalArgs.
From Velus Require Export NLustre.ExprInlining.EICorrectness.

Module Type EXPRINLINING
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
  Declare Module Export EI        : EI                  Ids Op OpAux Cks CE.Syn Syn.
  Declare Module Export EITyp     : EITYPING            Ids Op OpAux Cks CE.Syn CE.Typ Syn Ord Typ EI.
  Declare Module Export EIClo     : EICLOCKING          Ids Op OpAux Cks CE.Syn CE.Clo Syn Ord Mem IsD Clo EI.
  Declare Module Export EINorm    : EINORMALARGS        Ids Op OpAux Cks CE.Syn CE.Typ Syn Ord Typ Norm EI.
  Declare Module Export EICor     : EICORRECTNESS       Ids Op OpAux Cks IStr CE.Syn CE.Typ CE.Sem Syn Ord Typ Sem EI EITyp.
End EXPRINLINING.

Module ExprInliningFun
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
       <: EXPRINLINING Ids Op OpAux ComTyp Cks IStr CE Syn Ord Typ Norm Mem IsD Clo Sem.
  Module Export EI        := EIFun                  Ids Op OpAux Cks CE.Syn Syn.
  Module Export EITyp     := EITypingFun            Ids Op OpAux Cks CE.Syn CE.Typ Syn Ord Typ EI.
  Module Export EIClo     := EIClockingFun          Ids Op OpAux Cks CE.Syn CE.Clo Syn Ord Mem IsD Clo EI.
  Module Export EINorm    := EINormalArgsFun        Ids Op OpAux Cks CE.Syn CE.Typ Syn Ord Typ Norm EI.
  Module Export EICor     := EICorrectnessFun       Ids Op OpAux Cks IStr CE.Syn CE.Typ CE.Sem Syn Ord Typ Sem EI EITyp.
End ExprInliningFun.
