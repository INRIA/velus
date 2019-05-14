From Velus Require Import ObcToClight.Interface.
From Velus Require Import Ident.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Stream.

Module OpAux := OperatorsAux Op.
Module Str   := StreamFun Op OpAux.

From Velus Require Import CoreExpr.

Module CE := CoreExprFun Ids Op OpAux Str.

From Velus Require Import Lustre.
From Velus Require Import NLustre.

Module L := LustreFun Ids Op OpAux.
Module NL := NLustreFun Ids Op OpAux Str CE.

From Velus Require Import LustreToNLustre.

Module L2NL := LustreToNLustreFun Ids Op OpAux L.Syn CE.Syn NL.Syn.

From Velus Require Import SyBloc.

Module SB := SyBlocFun  Ids Op OpAux Str CE.

From Coq Require Import ZArith.BinInt.
From Velus Require Import NLustreToSyBloc.Translation.
From Velus Require Import NLustreToSyBloc.Correctness.
From Velus Require Import NLustreToSyBloc.NL2SBTyping.
From Velus Require Import NLustreToSyBloc.NL2SBClocking.
From Velus Require Import NLustreToSyBloc.NL2SBNormalArgs.

Module NL2SB           := TranslationFun     Ids Op           CE.Syn NL.Syn SB.Syn NL.Mem.
Module NL2SBCorr       := CorrectnessFun     Ids Op OpAux Str CE NL SB NL2SB.
Module NL2SBTyping     := NL2SBTypingFun     Ids Op OpAux Str CE NL SB NL2SB.
Module NL2SBClocking   := NL2SBClockingFun   Ids Op OpAux Str CE NL SB NL2SB.
Module NL2SBNormalArgs := NL2SBNormalArgsFun Ids Op OpAux Str CE NL SB NL2SB.

From Velus Require Import Obc.

Module Obc := ObcFun Ids Op OpAux.

From Velus Require Import SyBlocToObc.Translation.
From Velus Require Import SyBlocToObc.SBMemoryCorres.
From Velus Require Import SyBlocToObc.Correctness.
From Velus Require Import SyBlocToObc.SB2ObcInvariants.
From Velus Require Import SyBlocToObc.SB2ObcTyping.

Module SB2Obc     := TranslationFun    Ids Op OpAux CE.Syn SB.Syn Obc.Syn.
Module MemCorres  := SBMemoryCorresFun Ids Op       CE.Syn SB.Syn SB.Last.
Module SB2ObcCorr := CorrectnessFun    Ids Op OpAux Str CE SB Obc SB2Obc MemCorres.

Module SB2ObcInvariants := SB2ObcInvariantsFun Ids Op OpAux Str CE SB Obc SB2Obc.
Module SB2ObcTyping     := SB2ObcTypingFun     Ids Op OpAux Str CE SB Obc SB2Obc.
