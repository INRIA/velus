Require Import ObcToClight.Interface.
Require Import Ident.
Require Import Operators.
Require Import Clocks.
Require Import Stream.

Module OpAux := OperatorsAux Op.
Module Clks := ClocksFun Ids.
Module Str := StreamFun Op OpAux.

Require Import NLustre.NLExprSyntax.
Require Import NLustre.NLExprSemantics.

Module ExprSyn := NLExprSyntaxFun Op.
Module ExprSem := NLExprSemanticsFun Ids Op OpAux Clks ExprSyn Str.

Require Import NLustre.
Require Import SyBloc.

Module NL := NLustreFun Ids Op OpAux Clks ExprSyn Str ExprSem.
Module SB := SyBlocFun Ids Op OpAux Clks ExprSyn Str ExprSem NL.Syn NL.IsF.

Require Import Coq.ZArith.BinInt.
Require Import NLustreToSyBloc.Translation.
Require Import NLustreToSyBloc.Correctness.

Module NL2SB := TranslationFun Ids Op Clks ExprSyn NL.Syn SB.Syn NL.Mem.
Module NL2SBCorr := CorrectnessFun Ids Op OpAux Clks ExprSyn Str ExprSem NL SB NL2SB.

Require Import Obc.

Module Obc := ObcFun Ids Op OpAux.

Require Import SyBlocToObc.Translation.
Require Import SyBlocToObc.SBMemoryCorres.
Require Import SyBlocToObc.Correctness.
(* Require Import NLustreToObc.Fusible. *)

Module SB2Obc := TranslationFun Ids Op OpAux Clks ExprSyn SB.Syn Obc.Syn.
Module MemCorres := SBMemoryCorresFun Ids Op Clks ExprSyn SB.Syn SB.Last.
Module SB2ObcCorr := CorrectnessFun Ids Op OpAux Clks ExprSyn Str ExprSem NL.Syn NL.IsF SB Obc SB2Obc MemCorres.

(* Module Fusible := NLustreToObc.Fusible.FusibleFun Ids Op OpAux Clks NL Obc Trans. *)
