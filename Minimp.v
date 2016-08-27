Require Export Minimp.Syntax.
Require Export Minimp.Semantics.
Require Export Minimp.Equiv.

Require Import Rustre.Common.

Module Type MINIMP (Op: OPERATORS) (OpAux: OPERATORS_AUX Op).
  Declare Module Export Syn: SYNTAX Op OpAux.
  Declare Module Export Sem: SEMANTICS Op OpAux Syn.
  Declare Module Export Equ: EQUIV Op OpAux Syn Sem.
End MINIMP.