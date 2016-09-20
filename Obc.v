Require Import Operators.
Require Export Obc.Syntax.
Require Export Obc.Semantics.
Require Export Obc.Equiv.

Require Import Rustre.Common.

Module Type OBC (Ids: IDS) (Op: OPERATORS) (OpAux: OPERATORS_AUX Op).
  Declare Module Export Syn: SYNTAX Ids Op OpAux.
  Declare Module Export Sem: SEMANTICS Ids Op OpAux Syn.
  Declare Module Export Equ: EQUIV Ids Op OpAux Syn Sem.
End OBC.

