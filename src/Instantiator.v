Require Import ObcToClight.Interface.
Require Import Ident.
Require Import Operators.
Require Import Clocks.
Require Import Stream.

Module OpAux := OperatorsAux Op.
Module Str   := StreamFun Op OpAux.

Require Import CoreExpr.

Module CE := CoreExprFun Ids Op OpAux Str.

Require Import Lustre.
Require Import NLustre.

Module L := LustreFun Ids Op OpAux.
Module NL := NLustreFun Ids Op OpAux Str CE.

Require Import LustreToNLustre.

Module L2NL := LustreToNLustreFun Ids Op L.Syn CE.Syn NL.Syn.

Require Import SyBloc.

Module SB := SyBlocFun  Ids Op OpAux Str CE.

Require Import Coq.ZArith.BinInt.
Require Import NLustreToSyBloc.Translation.
Require Import NLustreToSyBloc.Correctness.
Require Import NLustreToSyBloc.NL2SBTyping.
Require Import NLustreToSyBloc.NL2SBClocking.
Require Import NLustreToSyBloc.NL2SBNormalArgs.

Module NL2SB           := TranslationFun     Ids Op           CE.Syn NL.Syn SB.Syn NL.Mem.
Module NL2SBCorr       := CorrectnessFun     Ids Op OpAux Str CE NL SB NL2SB.
Module NL2SBTyping     := NL2SBTypingFun     Ids Op OpAux Str CE NL SB NL2SB.
Module NL2SBClocking   := NL2SBClockingFun   Ids Op OpAux Str CE NL SB NL2SB.
Module NL2SBNormalArgs := NL2SBNormalArgsFun Ids Op OpAux Str CE NL SB NL2SB.

Require Import Obc.

Module Obc := ObcFun Ids Op OpAux.

Require Import SyBlocToObc.Translation.
Require Import SyBlocToObc.SBMemoryCorres.
Require Import SyBlocToObc.Correctness.
Require Import SyBlocToObc.SB2ObcInvariants.
Require Import SyBlocToObc.SB2ObcTyping.

Module SB2Obc     := TranslationFun    Ids Op OpAux CE.Syn SB.Syn Obc.Syn.
Module MemCorres  := SBMemoryCorresFun Ids Op       CE.Syn SB.Syn SB.Last.
Module SB2ObcCorr := CorrectnessFun    Ids Op OpAux Str CE SB Obc SB2Obc MemCorres.

Module SB2ObcInvariants := SB2ObcInvariantsFun Ids Op OpAux Str CE SB Obc SB2Obc.
Module SB2ObcTyping     := SB2ObcTypingFun     Ids Op OpAux Str CE SB Obc SB2Obc.
