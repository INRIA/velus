Require Import ObcToClight.Interface.
Require Import Ident.
Require Import Operators.
Require Import Clocks.
Require Import Stream.

Module OpAux := OperatorsAux Op.
Module Clks  := ClocksFun Ids.
Module Str   := StreamFun Op OpAux.

Require Import CoreExpr.

Module CE := CoreExprFun Ids Op OpAux Clks Str.

Require Import NLustre.
Require Import SyBloc.

Module NL := NLustreFun Ids Op OpAux Clks Str CE.
Module SB := SyBlocFun  Ids Op OpAux Clks Str CE.

Require Import Coq.ZArith.BinInt.
Require Import NLustreToSyBloc.Translation.
Require Import NLustreToSyBloc.Correctness.
Require Import NLustreToSyBloc.NL2SBTyping.
Require Import NLustreToSyBloc.NL2SBClocking.

Module NL2SB         := TranslationFun   Ids Op       Clks     CE.Syn NL.Syn SB.Syn NL.Mem.
Module NL2SBCorr     := CorrectnessFun   Ids Op OpAux Clks Str CE NL SB NL2SB.
Module NL2SBTyping   := NL2SBTypingFun   Ids Op OpAux Clks Str CE NL SB NL2SB.
Module NL2SBClocking := NL2SBClockingFun Ids Op OpAux Clks Str CE NL SB NL2SB.

Require Import Obc.

Module Obc := ObcFun Ids Op OpAux.

Require Import SyBlocToObc.Translation.
Require Import SyBlocToObc.SBMemoryCorres.
Require Import SyBlocToObc.Correctness.
Require Import SyBlocToObc.SB2ObcInvariants.
Require Import SyBlocToObc.SB2ObcTyping.

Module SB2Obc     := TranslationFun    Ids Op OpAux Clks CE.Syn SB.Syn Obc.Syn.
Module MemCorres  := SBMemoryCorresFun Ids Op       Clks CE.Syn SB.Syn SB.Last.
Module SB2ObcCorr := CorrectnessFun    Ids Op OpAux Clks Str CE SB Obc SB2Obc MemCorres.

Module SB2ObcInvariants := SB2ObcInvariantsFun Ids Op OpAux Clks Str CE SB Obc SB2Obc.
Module SB2ObcTyping     := SB2ObcTypingFun     Ids Op OpAux Clks Str CE SB Obc SB2Obc.