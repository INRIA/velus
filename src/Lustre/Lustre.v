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
From Velus Require Import Clocks.
From Velus Require Import CoindStreams.
From Velus Require Export Lustre.LSyntax.
From Velus Require Export Lustre.LClocking.
From Velus Require Export Lustre.LTyping.
From Velus Require Export Lustre.LSemantics.
From Velus Require Export Lustre.LOrdered.

From Velus Require Import Common.

Module Type LUSTRE
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str   : COINDSTREAMS  Op OpAux).
  Declare Module Export Syn: LSYNTAX    Ids Op.
  Declare Module Export Typ: LTYPING    Ids Op       Syn.
  Declare Module Export Clo: LCLOCKING  Ids Op       Syn.
  Declare Module Export Lord: LORDERED  Ids Op       Syn.
  Declare Module Export Sem: LSEMANTICS Ids Op OpAux Syn Lord Str.
End LUSTRE.

Module LustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str   : COINDSTREAMS  Op OpAux)
       <: LUSTRE Ids Op OpAux Str.
  Module Export Syn := LSyntaxFun     Ids Op.
  Module Export Typ := LTypingFun     Ids Op       Syn.
  Module Export Clo := LClockingFun   Ids Op       Syn.
  Module Export Lord:= LOrderedFun    Ids Op       Syn.
  Module Export Sem := LSemanticsFun  Ids Op OpAux Syn Lord Str.
End LustreFun.
