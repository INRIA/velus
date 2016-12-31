Require Import ObcToClight.Interface.
Require Import Ident.
Require Import Operators.
Require Import Clocks.

Module OpAux := OperatorsAux Op.
Module Clks := ClocksFun Ids. 

Require Import Coq.ZArith.BinInt.

Require Import NLustre.
Require Import Obc.
Require Import NLustreToObc.Translation.
Require Import NLustreToObc.Correctness.
Require Import NLustreToObc.Fusible.

Module NL := NLustreFun Ids Op OpAux Clks.
Module Obc := ObcFun Ids Op OpAux.
Module Mem := MemoriesFun Ids Op Clks NL.Syn.
Module Trans := TranslationFun Ids Op OpAux Clks NL.Syn Obc.Syn Mem.
Module Typ := NLustreToObc.NLObcTyping.NLObcTypingFun Ids Op OpAux Clks NL Obc Mem Trans.
Module Corr := NLustreToObc.Correctness.CorrectnessFun Ids Op OpAux Clks NL Obc Mem Trans Typ.
Module Fusible := NLustreToObc.Fusible.FusibleFun Ids Op OpAux Clks NL Obc Trans.

