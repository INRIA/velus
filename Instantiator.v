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
Require Import NLustre.Memories.
Require Import Obc.FuseIfte.
Require Import NLustre.IsFree.Decide.
Require Import NLustre.WellFormed.Decide.
Require Import NLustre.Typing.

Module DF := NLustreFun Ids Op OpAux.
Module Obc := ObcFun Ids Op OpAux.
Module Mem := MemoriesFun Ids Op DF.Syn.
Module Trans := TranslationFun Ids Op OpAux DF.Syn Obc.Syn Mem.
Module IsP := IsPresentFun Ids Op OpAux DF.Syn Obc.Syn Obc.Sem Mem Trans.
Module MemCor := MemoryCorresFun Ids Op OpAux DF Obc.
Module Fus := FuseIfteFun Ids Op OpAux DF.Syn Obc.Syn Obc.Sem Obc.Equ.
Module Typ := NLustreToObc.Typing.TypingFun Ids Op OpAux DF Obc Mem Trans Fus.
Module Corr := NLustreToObc.Correctness.CorrectnessFun Ids Op OpAux DF Obc Mem Trans IsP MemCor Fus Typ.

  
Module WeFDec := WellFormed.Decide.Decide Ids Op DF.Syn DF.IsF DF.IsFDec DF.Ord DF.Mem DF.IsD DF.IsV DF.IsDDec DF.IsVDec DF.NoD DF.WeF.
