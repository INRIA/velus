Require Import ObcToClight.Interface.
Require Import Ident.
Require Import Operators.

Module OpAux := OperatorsAux Op.

Require Import Coq.ZArith.BinInt.
Require Import DataflowToObc.Correctness.
Require Import DataflowToObc.Correctness.IsPresent.
Require Import DataflowToObc.Correctness.MemoryCorres.
Require Import Dataflow.
Require Import Obc.
Require Import DataflowToObc.Translation.
Require Import Dataflow.Memories.
Require Import Obc.FuseIfte.
Require Import Dataflow.IsFree.Decide.
Require Import Dataflow.WellFormed.Decide.

Module DF := DataflowFun Ids Op OpAux.
Module Obc := ObcFun Ids Op OpAux.
Module Mem := MemoriesFun Ids Op DF.Syn.
Module Trans := TranslationFun Ids Op OpAux DF.Syn Obc.Syn Mem.
Module IsP := IsPresentFun Ids Op OpAux DF.Syn Obc.Syn Obc.Sem Mem Trans.
Module MemCor := MemoryCorresFun Ids Op OpAux DF Obc.
Module Fus := FuseIfteFun Ids Op OpAux DF.Syn Obc.Syn Obc.Sem Obc.Equ.
Module Corr := DataflowToObc.Correctness.CorrectnessFun Ids Op OpAux DF Obc Mem Trans IsP MemCor Fus.

Module WeFDec := WellFormed.Decide.Decide Ids Op DF.Syn DF.IsF DF.IsFDec DF.Ord DF.Mem DF.IsD DF.IsV DF.IsDDec DF.IsVDec DF.NoD DF.WeF.
