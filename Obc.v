Require Import Operators.
Require Export Obc.Syntax.
Require Export Obc.Semantics.
Require Export Obc.Typing.
Require Export Obc.Equiv.

Require Import Velus.Common.

Module Type OBC (Ids: IDS) (Op: OPERATORS) (OpAux: OPERATORS_AUX Op).
  Declare Module Export Syn: SYNTAX Ids Op OpAux.
  Declare Module Export Sem: SEMANTICS Ids Op OpAux Syn.
  Declare Module Export Equ: EQUIV Ids Op OpAux Syn Sem.
  Declare Module Export Typ: TYPING Ids Op OpAux Syn Sem.
End OBC.

Module ObcFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       <: OBC Ids Op OpAux.
  Module Export Syn := SyntaxFun Ids Op OpAux.
  Module Export Sem := SemanticsFun Ids Op OpAux Syn.
  Module Export Equ := EquivFun Ids Op OpAux Syn Sem.
  Module Export Typ := TypingFun Ids Op OpAux Syn Sem.
End ObcFun.
