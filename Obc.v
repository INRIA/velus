Require Import Operators.
Require Export Obc.ObcSyntax.
Require Export Obc.ObcSemantics.
Require Export Obc.ObcTyping.
Require Export Obc.Equiv.
Require Export Obc.Fusion.

Require Import Velus.Common.

Module Type OBC (Ids: IDS) (Op: OPERATORS) (OpAux: OPERATORS_AUX Op).
  Declare Module Export Syn: OBCSYNTAX Ids Op OpAux.
  Declare Module Export Sem: OBCSEMANTICS Ids Op OpAux Syn.
  Declare Module Export Equ: EQUIV Ids Op OpAux Syn Sem.
  Declare Module Export Typ: OBCTYPING Ids Op OpAux Syn Sem.
  Declare Module Export Fus: FUSION Ids Op OpAux Syn Sem Typ Equ.
End OBC.

Module ObcFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       <: OBC Ids Op OpAux.
  Module Export Syn := ObcSyntaxFun Ids Op OpAux.
  Module Export Sem := ObcSemanticsFun Ids Op OpAux Syn.
  Module Export Equ := EquivFun Ids Op OpAux Syn Sem.
  Module Export Typ := ObcTypingFun Ids Op OpAux Syn Sem.
  Module Export Fus := FusionFun Ids Op OpAux Syn Sem Typ Equ.
End ObcFun.
