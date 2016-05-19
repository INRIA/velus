Require Export Minimp.Syntax.
Require Export Minimp.Semantics.
Require Export Minimp.Equiv.

Require Import Rustre.Common.

Module Type MINIMP (Op: OPERATORS).
  Declare Module Export Syn: SYNTAX Op.
  Declare Module Export Sem: SEMANTICS Op Syn.
  Declare Module Export Equ: EQUIV Op Syn Sem.
End MINIMP.