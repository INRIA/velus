From Velus Require Import ObcToClight.Interface.
From Velus Require Import Ident.
From Velus Require Import Operators.
From Velus Require Import Clocks.

From Velus Require Import CoreExpr.

Module CE := CoreExprFun Ids Op OpAux IStr.

(* From Velus Require Import Lustre. *)
From Velus Require Import NLustre.

(* Module L := LustreFun Ids Op OpAux CStr. *)
Module NL := NLustreFun Ids Op OpAux CStr IStr CE.

(* From Velus Require Import Transcription. *)

(* Module TR := TranscriptionFun Ids Op OpAux L.Syn CE.Syn NL.Syn. *)

From Velus Require Import Stc.

Module Stc := StcFun Ids Op OpAux IStr CE.

From Coq Require Import ZArith.BinInt.
From Velus Require Import NLustreToStc.Translation.
From Velus Require Import NLustreToStc.Correctness.
From Velus Require Import NLustreToStc.NL2StcTyping.
From Velus Require Import NLustreToStc.NL2StcClocking.
From Velus Require Import NLustreToStc.NL2StcNormalArgs.

Module NL2Stc           := TranslationFun      Ids Op           CE.Syn NL.Syn Stc.Syn NL.Mem.
Module NL2StcCorr       := CorrectnessFun      Ids Op OpAux CStr IStr CE NL Stc NL2Stc.
Module NL2StcTyping     := NL2StcTypingFun     Ids Op OpAux CStr IStr CE NL Stc NL2Stc.
Module NL2StcClocking   := NL2StcClockingFun   Ids Op OpAux CStr IStr CE NL Stc NL2Stc.
Module NL2StcNormalArgs := NL2StcNormalArgsFun Ids Op OpAux CStr IStr CE NL Stc NL2Stc.

From Velus Require Import StcToObc.Translation.
From Velus Require Import StcToObc.StcMemoryCorres.
From Velus Require Import StcToObc.Correctness.
From Velus Require Import StcToObc.Stc2ObcInvariants.
From Velus Require Import StcToObc.Stc2ObcTyping.

Module Stc2Obc     := TranslationFun     Ids Op OpAux CE.Syn Stc.Syn Obc.Syn.
Module MemCorres   := StcMemoryCorresFun Ids Op       CE.Syn Stc.Syn Stc.Last.
Module Stc2ObcCorr := CorrectnessFun     Ids Op OpAux IStr CE Stc Obc Stc2Obc MemCorres.

Module Stc2ObcInvariants := Stc2ObcInvariantsFun Ids Op OpAux IStr CE Stc Obc Stc2Obc.
Module Stc2ObcTyping     := Stc2ObcTypingFun     Ids Op OpAux IStr CE Stc Obc Stc2Obc.
