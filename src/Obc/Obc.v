From Velus Require Import Operators.
From Velus Require Export Obc.ObcSyntax.
From Velus Require Export Obc.ObcSemantics.
From Velus Require Export Obc.ObcInvariants.
From Velus Require Export Obc.ObcTyping.
From Velus Require Export Obc.Equiv.
From Velus Require Export Obc.ObcAddDefaults.
From Velus Require Export Obc.Fusion.
From Velus Require Export Obc.ObcSwitchesNormalization.
From Velus Require Export Obc.ObcDeadCode.
From Velus Require Export Obc.ObcInterpreter.

From Velus Require Import Common.
From Velus Require Import CommonTyping.

Module Type OBC
       (Ids: IDS)
       (Op: OPERATORS)
       (OpAux: OPERATORS_AUX Ids Op)
       (ComTyp: COMMONTYPING Ids Op OpAux).
  Declare Module Export Syn: OBCSYNTAX      Ids Op OpAux.
  Declare Module Export Sem: OBCSEMANTICS   Ids Op OpAux Syn.
  Declare Module Export Inv: OBCINVARIANTS  Ids Op OpAux Syn        Sem.
  Declare Module Export Typ: OBCTYPING      Ids Op OpAux Syn ComTyp Sem.
  Declare Module Export Equ: EQUIV          Ids Op OpAux Syn ComTyp Sem     Typ.
  Declare Module Export Fus: FUSION         Ids Op OpAux Syn ComTyp Sem Inv Typ Equ.
  Declare Module Export SwN: OBCSWITCHESNORMALIZATION Ids Op OpAux Syn ComTyp Sem Inv Typ Equ.
  Declare Module Export DCE: OBCDEADCODE    Ids Op OpAux Syn ComTyp Sem Inv Typ.
  Declare Module Export Def: OBCADDDEFAULTS Ids Op OpAux Syn ComTyp Sem Inv Typ Equ.
  Declare Module Export Int: OBCINTERPRETER Ids Op OpAux Syn Sem.
End OBC.

Module ObcFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX Ids Op)
       (ComTyp : COMMONTYPING  Ids Op OpAux)
       <: OBC Ids Op OpAux ComTyp.
  Module Export Syn := ObcSyntaxFun                Ids Op OpAux.
  Module Export Sem := ObcSemanticsFun             Ids Op OpAux Syn.
  Module Export Inv := ObcInvariantsFun            Ids Op OpAux Syn Sem.
  Module Export Typ := ObcTypingFun                Ids Op OpAux Syn ComTyp Sem.
  Module Export Equ := EquivFun                    Ids Op OpAux Syn ComTyp Sem     Typ.
  Module Export Fus := FusionFun                   Ids Op OpAux Syn ComTyp Sem Inv Typ Equ.
  Module Export SwN := ObcSwitchesNormalizationFun Ids Op OpAux Syn ComTyp Sem Inv Typ Equ.
  Module Export DCE := ObcDeadCodeFun              Ids Op OpAux Syn ComTyp Sem Inv Typ.
  Module Export Def := ObcAddDefaultsFun           Ids Op OpAux Syn ComTyp Sem Inv Typ Equ.
  Module Export Int := ObcInterpreterFun           Ids Op OpAux Syn Sem.
End ObcFun.
