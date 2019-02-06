Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.

Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLExprSemantics.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.SyBloc.SBSemantics.

Require Import Velus.Obc.ObcSyntax.
Require Import Velus.Obc.ObcSemantics.

Require Import Velus.SyBlocToObc.Translation.

Require Import List.
Import List.ListNotations.

Open Scope positive.
Open Scope list.

Module Type CORRECTNESS
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX       Op)
       (Import Clks    : CLOCKS          Ids)
       (Import ExprSyn : NLEXPRSYNTAX        Op)
       (Import SynSB   : SBSYNTAX        Ids Op       Clks ExprSyn)
       (Import Str     : STREAM              Op OpAux)
       (Import ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn              Str)
       (Import SemSB   : SBSEMANTICS     Ids Op OpAux Clks ExprSyn SynSB        Str ExprSem)
       (Import SynObc  : OBCSYNTAX       Ids Op OpAux)
       (Import SemObc  : OBCSEMANTICS    Ids Op OpAux                    SynObc)
       (Import Trans   : TRANSLATION     Ids Op OpAux Clks ExprSyn SynSB SynObc).


End CORRECTNESS.
