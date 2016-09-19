Require Import Operators.
Require Export Minimp.Syntax.
Require Export Minimp.Semantics.
Require Export Minimp.Equiv.

Require Import Rustre.Common.

Module Type MINIMP (Ids: IDS) (Op: OPERATORS) (OpAux: OPERATORS_AUX Op).
  Declare Module Export Syn: SYNTAX Ids Op OpAux.
  Declare Module Export Sem: SEMANTICS Ids Op OpAux Syn.
  Declare Module Export Equ: EQUIV Ids Op OpAux Syn Sem.
End MINIMP.

