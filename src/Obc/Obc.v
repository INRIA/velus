(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Velus Require Import Operators.
From Velus Require Export Obc.ObcSyntax.
From Velus Require Export Obc.ObcSemantics.
From Velus Require Export Obc.ObcInvariants.
From Velus Require Export Obc.ObcTyping.
From Velus Require Export Obc.Equiv.
From Velus Require Export Obc.ObcAddDefaults.
From Velus Require Export Obc.Fusion.

From Velus Require Import Common.

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
