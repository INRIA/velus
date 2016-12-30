Require Import ObcToClight.Interface.
Require Import Ident.
Require Import Operators.

Module OpAux := OperatorsAux Op.

Require Import Coq.ZArith.BinInt.

Require Import NLustre.
Require Import Obc.
Require Import NLustreToObc.Translation.
Require Import NLustreToObc.Correctness.
Require Import NLustreToObc.Fusible.

Module NL := NLustreFun Ids Op OpAux.
Module Obc := ObcFun Ids Op OpAux.
Module Mem := MemoriesFun Ids Op NL.Syn.
Module Trans := TranslationFun Ids Op OpAux NL.Syn Obc.Syn Mem.
Module Typ := NLustreToObc.NLObcTyping.NLObcTypingFun Ids Op OpAux NL Obc Mem Trans.
Module Corr := NLustreToObc.Correctness.CorrectnessFun Ids Op OpAux NL Obc Mem Trans Typ.
Module Fusible := NLustreToObc.Fusible.FusibleFun Ids Op OpAux NL Obc Trans.

