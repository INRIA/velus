From Velus Require Import ObcToClight.Interface.
From Velus Require Import Ident.
From Velus Require Import Operators.
From Velus Require Import Clocks.

From Velus Require Import CoreExpr.

Module CE := CoreExprFun Ids Op OpAux Str.

From Velus Require Import Lustre.
From Velus Require Import NLustre.

Module L := LustreFun Ids Op OpAux Strs.
Module NL := NLustreFun Ids Op OpAux Strs Str CE.

From Velus Require Import Transcription.

Module TR := TranscriptionFun Ids Op OpAux L.Syn CE.Syn NL.Syn.

From Velus Require Import Stc.

Module Stc := StcFun Ids Op OpAux Str CE.

From Coq Require Import ZArith.BinInt.
From Velus Require Import NLustreToStc.Translation.
From Velus Require Import NLustreToStc.Correctness.
From Velus Require Import NLustreToStc.NL2StcTyping.
From Velus Require Import NLustreToStc.NL2StcClocking.
From Velus Require Import NLustreToStc.NL2StcNormalArgs.

Module NL2Stc           := TranslationFun      Ids Op           CE.Syn NL.Syn Stc.Syn NL.Mem.
Module NL2StcCorr       := CorrectnessFun      Ids Op OpAux Strs Str CE NL Stc NL2Stc.
Module NL2StcTyping     := NL2StcTypingFun     Ids Op OpAux Strs Str CE NL Stc NL2Stc.
Module NL2StcClocking   := NL2StcClockingFun   Ids Op OpAux Strs Str CE NL Stc NL2Stc.
Module NL2StcNormalArgs := NL2StcNormalArgsFun Ids Op OpAux Strs Str CE NL Stc NL2Stc.

From Velus Require Import StcToObc.Translation.
From Velus Require Import StcToObc.StcMemoryCorres.
From Velus Require Import StcToObc.Correctness.
From Velus Require Import StcToObc.Stc2ObcInvariants.
From Velus Require Import StcToObc.Stc2ObcTyping.

Module Stc2Obc     := TranslationFun     Ids Op OpAux CE.Syn Stc.Syn Obc.Syn.
Module MemCorres   := StcVelusMemoryCorresFun Ids Op       CE.Syn Stc.Syn Stc.Last.
Module Stc2ObcCorr := CorrectnessFun     Ids Op OpAux Str CE Stc Obc Stc2Obc MemCorres.

Module Stc2ObcInvariants := Stc2ObcInvariantsFun Ids Op OpAux Str CE Stc Obc Stc2Obc.
Module Stc2ObcTyping     := Stc2ObcTypingFun     Ids Op OpAux Str CE Stc Obc Stc2Obc.
