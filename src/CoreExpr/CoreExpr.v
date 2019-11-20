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

From Velus Require Export Operators.
From Velus Require Export Clocks.
From Velus Require Export IndexedStreams.
From Velus Require Export CoreExpr.CESyntax.
From Velus Require Export CoreExpr.CEIsFree.
From Velus Require Export CoreExpr.CESemantics.
From Velus Require Export CoreExpr.CEClocking.
From Velus Require Export CoreExpr.CEClockingSemantics.
From Velus Require Export CoreExpr.CETyping.
From Velus Require Export CoreExpr.CEProperties.
From Velus Require Export CoreExpr.CEInterpreter.

From Velus Require Import Common.

Module Type COREEXPR
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX  Op)
       (Str    : INDEXEDSTREAMS Op OpAux).
  Declare Module Export Syn    : CESYNTAX                Op.
  Declare Module Export IsF    : CEISFREE            Ids Op       Syn.
  Declare Module Export Sem    : CESEMANTICS         Ids Op OpAux Syn Str.
  Declare Module Export Typ    : CETYPING            Ids Op       Syn.
  Declare Module Export Clo    : CECLOCKING          Ids Op       Syn.
  Declare Module Export CloSem : CECLOCKINGSEMANTICS Ids Op OpAux Syn Str Sem     Clo.
  Declare Module Export Props  : CEPROPERTIES        Ids Op OpAux Syn Str Sem Typ        IsF.
  Declare Module Export Interp : CEINTERPRETER       Ids Op OpAux Syn Str Sem.
End COREEXPR.

Module CoreExprFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX  Op)
       (Str    : INDEXEDSTREAMS Op OpAux)
<: COREEXPR Ids Op OpAux Str.
  Module Export Syn    := CESyntaxFun                Op.
  Module Export IsF    := CEIsFreeFun            Ids Op       Syn.
  Module Export Sem    := CESemanticsFun         Ids Op OpAux Syn Str.
  Module Export Typ    := CETypingFun            Ids Op       Syn.
  Module Export Clo    := CEClockingFun          Ids Op       Syn.
  Module Export CloSem := CEClockingSemanticsFun Ids Op OpAux Syn Str Sem     Clo.
  Module Export Props  := CEProperties           Ids Op OpAux Syn Str Sem Typ     IsF.
  Module Export Interp := CEInterpreterFun       Ids Op OpAux Syn Str Sem.
End CoreExprFun.
