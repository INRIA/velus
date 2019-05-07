Require Import Operators.
Require Export Obc.ObcSyntax.
Require Export Obc.ObcSemantics.
Require Export Obc.ObcInvariants.
Require Export Obc.ObcTyping.
Require Export Obc.Equiv.
Require Export Obc.ObcAddDefaults.
Require Export Obc.Fusion.

Require Import Velus.Common.Common.

Module Type OBC (Ids: IDS) (Op: OPERATORS) (OpAux: OPERATORS_AUX Op).
  Declare Module Export Syn: OBCSYNTAX      Ids Op OpAux.
  Declare Module Export Sem: OBCSEMANTICS   Ids Op OpAux Syn.
  Declare Module Export Inv: OBCINVARIANTS  Ids Op OpAux Syn Sem.
  Declare Module Export Typ: OBCTYPING      Ids Op OpAux Syn Sem.
  Declare Module Export Equ: EQUIV          Ids Op OpAux Syn Sem     Typ.
  Declare Module Export Fus: FUSION         Ids Op OpAux Syn Sem Inv Typ Equ.
  Declare Module Export Def: OBCADDDEFAULTS Ids Op OpAux Syn Sem Inv Typ Equ.
End OBC.

Module ObcFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       <: OBC Ids Op OpAux.
  Module Export Syn := ObcSyntaxFun      Ids Op OpAux.
  Module Export Sem := ObcSemanticsFun   Ids Op OpAux Syn.
  Module Export Inv := ObcInvariantsFun  Ids Op OpAux Syn Sem.
  Module Export Typ := ObcTypingFun      Ids Op OpAux Syn Sem.
  Module Export Equ := EquivFun          Ids Op OpAux Syn Sem     Typ.
  Module Export Fus := FusionFun         Ids Op OpAux Syn Sem Inv Typ Equ.
  Module Export Def := ObcAddDefaultsFun Ids Op OpAux Syn Sem Inv Typ Equ.
End ObcFun.
