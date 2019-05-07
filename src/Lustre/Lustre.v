Require Import Operators.
Require Import Clocks.
Require Export Lustre.LSyntax.
Require Export Lustre.LClocking.
Require Export Lustre.LTyping.
Require Export Lustre.LSemantics.

Require Import Velus.Common.Common.

Module Type LUSTRE
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op).
  Declare Module Export Syn: LSYNTAX    Ids Op.
  Declare Module Export Typ: LTYPING    Ids Op       Syn.
  Declare Module Export Clo: LCLOCKING  Ids Op       Syn.
  Declare Module Export Sem: LSEMANTICS Ids Op OpAux Syn.
End LUSTRE.

Module LustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       <: LUSTRE Ids Op OpAux.
  Module Export Syn := LSyntaxFun     Ids Op.
  Module Export Typ := LTypingFun     Ids Op       Syn.
  Module Export Clo := LClockingFun   Ids Op       Syn.
  Module Export Sem := LSemanticsFun  Ids Op OpAux Syn.
End LustreFun.

