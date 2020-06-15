From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams.
From Velus Require Export Lustre.LSyntax.
From Velus Require Export Lustre.LClocking.
From Velus Require Export Lustre.LTyping.
From Velus Require Export Lustre.LSemantics.
From Velus Require Export Lustre.LOrdered.
From Velus Require Export Lustre.LClockSemantics.
From Velus Require Export Lustre.Normalization.LNormalization.

From Velus Require Import Common.

Local Set Warnings "-masking-absolute-name".
Module Type LUSTRE
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str   : COINDSTREAMS  Op OpAux).
  Declare Module Export Syn: LSYNTAX    Ids Op.
  Declare Module Export Typ: LTYPING    Ids Op       Syn.
  Declare Module Export Clo: LCLOCKING  Ids Op       Syn.
  Declare Module Export Lord: LORDERED  Ids Op       Syn.
  Declare Module Export Sem: LSEMANTICS Ids Op OpAux Syn Lord Str.
  Declare Module Export ClockSem : LCLOCKSEMANTICS Ids Op OpAux Syn Typ Clo Lord Str Sem.
  Declare Module Export Norm: LNORMALIZATION Ids Op OpAux Str Syn Typ Clo Lord Sem.
End LUSTRE.

Module LustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str   : COINDSTREAMS  Op OpAux)
       <: LUSTRE Ids Op OpAux Str.
  Module Export Syn := LSyntaxFun     Ids Op.
  Module Export Typ := LTypingFun     Ids Op       Syn.
  Module Export Clo := LClockingFun   Ids Op       Syn.
  Module Export Lord:= LOrderedFun    Ids Op       Syn.
  Module Export Sem := LSemanticsFun  Ids Op OpAux Syn Lord Str.
  Module Export ClockSem := LClockSemanticsFun Ids Op OpAux Syn Typ Clo Lord Str Sem.
  Module Export Norm := LNormalizationFun Ids Op OpAux Str Syn Typ Clo Lord Sem.
End LustreFun.
