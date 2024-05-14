From Velus Require Import ObcToClight.Interface.
From Velus Require Import Ident.
From Velus Require Import Operators.
From Velus Require Import Clocks.

From Velus Require Import CoindToIndexed IndexedToCoind.

Module CIStr := CoindToIndexedFun Ids Op OpAux Cks CStr IStr.
Module ICStr := IndexedToCoindFun Ids Op OpAux Cks IStr CStr.

From Velus Require Import CoreExpr.

Module CE := CoreExprFun Ids Op OpAux ComTyp Cks IStr.

From Velus Require Import Lustre.

Module L := LustreFun Ids Op OpAux Cks CStr.

From Velus Require Import NLustre.

Module NL := NLustreFun Ids Op OpAux ComTyp Cks CStr IStr CIStr CE.

From Velus Require Import Transcription.

Module TR := TranscriptionFun Ids Op OpAux ComTyp Cks CStr IStr CIStr L CE NL.

From Velus Require Import Stc.

Module Stc := StcFun Ids Op OpAux ComTyp Cks IStr CE.

From Coq Require Import ZArith.BinInt.
From Velus Require Import NLustreToStc.Translation.
From Velus Require Import NLustreToStc.Correctness.
From Velus Require Import NLustreToStc.NL2StcTyping.
From Velus Require Import NLustreToStc.NL2StcClocking.
From Velus Require Import NLustreToStc.NL2StcNormalArgs.

Module NL2Stc           := TranslationFun      Ids Op OpAux        Cks           CE.Syn NL.Syn Stc.Syn NL.Mem.
Module NL2StcCorr       := CorrectnessFun      Ids Op OpAux ComTyp Cks CStr IStr CIStr CE NL Stc NL2Stc.
Module NL2StcTyping     := NL2StcTypingFun     Ids Op OpAux ComTyp Cks CStr IStr CIStr CE NL Stc NL2Stc.
Module NL2StcClocking   := NL2StcClockingFun   Ids Op OpAux ComTyp Cks CStr IStr CIStr CE NL Stc NL2Stc.
Module NL2StcNormalArgs := NL2StcNormalArgsFun Ids Op OpAux ComTyp Cks CStr IStr CIStr CE NL Stc NL2Stc.

From Velus Require Import StcToObc.Translation.
From Velus Require Import StcToObc.Correctness.
From Velus Require Import StcToObc.Stc2ObcInvariants.
From Velus Require Import StcToObc.Stc2ObcTyping.

Module Stc2Obc     := TranslationFun     Ids Op OpAux        Cks     CE.Syn Stc.Syn Obc.Syn.
Module Stc2ObcInvariants := Stc2ObcInvariantsFun Ids Op OpAux ComTyp Cks IStr CE Stc Obc Stc2Obc.
Module Stc2ObcTyping     := Stc2ObcTypingFun     Ids Op OpAux ComTyp Cks IStr CE Stc Obc Stc2Obc.
Module Stc2ObcCorr := CorrectnessFun     Ids Op OpAux ComTyp Cks IStr CE Stc Obc Stc2Obc Stc2ObcTyping.


(** instantiate Restr & Rt-Op checks separately *)

From Velus Require Import Lustre.Denot.Restr.
From Velus Require Import Lustre.Denot.CheckOp.

Module Restr := RestrFun  Ids Op OpAux Cks L.Senv L.Syn.
Module CheckOp := CheckOpFun Ids Op OpAux Cks L.Senv L.Syn.

Definition check_restr := @Restr.check_global.
Definition check_op := @CheckOp.check_global.

(** the denotational semantics *)

From Velus Require Import Lustre.Denot.Denot.

Module Den := LdenotFun Ids Op OpAux Cks L.Senv L.Syn L.Typ L.Clo L.Cau L.Ord CStr L.Sem Restr CheckOp.
