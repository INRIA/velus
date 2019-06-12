From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Streams.
From Velus Require Export Lustre.LSyntax.
From Velus Require Export Lustre.LClocking.
From Velus Require Export Lustre.LTyping.
From Velus Require Export Lustre.LSemantics.

From Velus Require Import Common.

Module Type LUSTRE
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str   : STREAMS       Op OpAux).
  Declare Module Export Syn: LSYNTAX    Ids Op.
  Declare Module Export Typ: LTYPING    Ids Op           Syn.
  Declare Module Export Clo: LCLOCKING  Ids Op           Syn.
  Declare Module Export Sem: LSEMANTICS Ids Op OpAux Str Syn.
End LUSTRE.

Module LustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str   : STREAMS       Op OpAux)
       <: LUSTRE Ids Op OpAux Str.
  Module Export Syn := LSyntaxFun     Ids Op.
  Module Export Typ := LTypingFun     Ids Op           Syn.
  Module Export Clo := LClockingFun   Ids Op           Syn.
  Module Export Sem := LSemanticsFun  Ids Op OpAux Str Syn.
End LustreFun.
