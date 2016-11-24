Require Import ObcToClight.Interface.
Require Import Ident.
Require Import Operators.

Module OpAux := OperatorsAux Op.

Require Import Coq.ZArith.BinInt.
Require Import NLustreToObc.Correctness.
Require Import NLustreToObc.Correctness.IsPresent.
Require Import NLustreToObc.Correctness.MemoryCorres.
Require Import NLustre.
Require Import Obc.
Require Import NLustreToObc.Translation.
Require Import NLustreToObc.Fusible.
Require Import NLustre.Memories.
Require Import NLustre.IsFree.Decide.
Require Import NLustre.WellFormed.Decide.
Require Import NLustre.Typing.

Module NL := NLustreFun Ids Op OpAux.
Module Obc := ObcFun Ids Op OpAux.
Module Mem := MemoriesFun Ids Op NL.Syn.
Module Trans := TranslationFun Ids Op OpAux NL.Syn Obc.Syn Mem.
Module IsP := IsPresentFun Ids Op OpAux NL.Syn Obc.Syn Obc.Sem Mem Trans.
Module MemCor := MemoryCorresFun Ids Op OpAux NL Obc.
Module Typ := NLustreToObc.Typing.TypingFun Ids Op OpAux NL Obc Mem Trans.
Module Corr := NLustreToObc.Correctness.CorrectnessFun Ids Op OpAux NL Obc Mem Trans IsP MemCor Typ.
Module Fusible := NLustreToObc.Fusible.FusibleFun Ids Op OpAux NL Obc Trans.

Module WeFDec := WellFormed.Decide.Decide Ids Op NL.Syn NL.IsF NL.IsFDec NL.Ord NL.Mem NL.IsD NL.IsV NL.IsDDec NL.IsVDec NL.NoD NL.WeF.

