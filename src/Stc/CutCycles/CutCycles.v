From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import IndexedStreams.
From Velus Require Import CommonTyping.

From Velus Require Import CoreExpr.CoreExpr.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import Stc.StcIsFree.
From Velus Require Import Stc.StcWellDefined.
From Velus Require Import Stc.StcTyping.
From Velus Require Import Stc.StcClocking.
From Velus Require Import Stc.StcSemantics.

From Velus Require Import Stc.CutCycles.CC.
From Velus Require Import Stc.CutCycles.CCTyping.
From Velus Require Import Stc.CutCycles.CCClocking.
From Velus Require Import Stc.CutCycles.CCNormalArgs.
From Velus Require Import Stc.CutCycles.CCCorrectness.

Module Type CUTCYCLES
  (Ids   : IDS)
  (Op    : OPERATORS)
  (OpAux : OPERATORS_AUX Ids Op)
  (ComTyp: COMMONTYPING Ids Op OpAux)
  (Cks   : CLOCKS Ids Op OpAux)
  (IStr  : INDEXEDSTREAMS Ids Op OpAux Cks)
  (CE    : COREEXPR Ids Op OpAux ComTyp Cks IStr)
  (Syn   : STCSYNTAX Ids Op OpAux Cks CE.Syn)
  (Ord   : STCORDERED Ids Op OpAux Cks CE.Syn Syn)
  (IsF   : STCISFREE Ids Op OpAux Cks CE.Syn Syn CE.IsF)
  (Wdef  : STCWELLDEFINED Ids Op OpAux Cks CE.Syn Syn Ord CE.IsF IsF)
  (Typ   : STCTYPING Ids Op OpAux Cks CE.Syn Syn CE.Typ)
  (Clo   : STCCLOCKING Ids Op OpAux Cks CE.Syn Syn Ord CE.Clo)
  (Sem   : STCSEMANTICS Ids Op OpAux Cks CE.Syn Syn Ord IStr CE.Sem)
  (ECC   : EXT_CC Ids Op OpAux Cks CE.Syn Syn).
  Declare Module Export CC      : CC                  Ids Op OpAux Cks CE.Syn Syn ECC.
  Declare Module Export CCTyp   : CCTYPING            Ids Op OpAux Cks CE.Syn Syn Ord CE.Typ Typ CE.Clo Clo ECC CC.
  Declare Module Export CCClo   : CCCLOCKING          Ids Op OpAux Cks CE.Syn Syn Ord CE.Clo Clo ECC CC.
  Declare Module Export CCNorm  : CCNORMALARGS        Ids Op OpAux Cks CE.Syn Syn Ord CE.IsF IsF Wdef ECC CC.
  Declare Module Export CCCor   : CCCORRECTNESS       Ids Op OpAux ComTyp Cks IStr CE Syn Ord Typ Clo Sem ECC CC.
End CUTCYCLES.

Module CutCyclesFun
  (Ids   : IDS)
  (Op    : OPERATORS)
  (OpAux : OPERATORS_AUX Ids Op)
  (ComTyp: COMMONTYPING Ids Op OpAux)
  (Cks   : CLOCKS Ids Op OpAux)
  (IStr  : INDEXEDSTREAMS Ids Op OpAux Cks)
  (CE    : COREEXPR Ids Op OpAux ComTyp Cks IStr)
  (Syn   : STCSYNTAX Ids Op OpAux Cks CE.Syn)
  (Ord   : STCORDERED Ids Op OpAux Cks CE.Syn Syn)
  (IsF   : STCISFREE Ids Op OpAux Cks CE.Syn Syn CE.IsF)
  (Wdef  : STCWELLDEFINED Ids Op OpAux Cks CE.Syn Syn Ord CE.IsF IsF)
  (Typ   : STCTYPING Ids Op OpAux Cks CE.Syn Syn CE.Typ)
  (Clo   : STCCLOCKING Ids Op OpAux Cks CE.Syn Syn Ord CE.Clo)
  (Sem   : STCSEMANTICS Ids Op OpAux Cks CE.Syn Syn Ord IStr CE.Sem)
  (ECC   : EXT_CC Ids Op OpAux Cks CE.Syn Syn)
<: CUTCYCLES Ids Op OpAux ComTyp Cks IStr CE Syn Ord IsF Wdef Typ Clo Sem ECC.
  Module Export CC        := CCFun            Ids Op OpAux Cks CE.Syn Syn ECC.
  Module Export CCTyp     := CCTypingFun      Ids Op OpAux Cks CE.Syn Syn Ord CE.Typ Typ CE.Clo Clo ECC CC.
  Module Export CCClo     := CCClockingFun    Ids Op OpAux Cks CE.Syn Syn Ord CE.Clo Clo ECC CC.
  Module Export CCNorm    := CCNormalArgsFun  Ids Op OpAux Cks CE.Syn Syn Ord CE.IsF IsF Wdef ECC CC.
  Module Export CCCor     := CCCorrectnessFun Ids Op OpAux ComTyp Cks IStr CE Syn Ord Typ Clo Sem ECC CC.
End CutCyclesFun.
