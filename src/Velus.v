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

From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import NLustre.NLElaboration.
From Velus Require Import Interface.
From Velus Require Import Instantiator.
From Velus Require Import ObcToClight.Generation.
From Velus Require Import ClightToAsm.
Import Stc.

From compcert Require Import common.Errors.
From compcert Require Import driver.Compiler.

From Coq Require Import String.
From Coq Require Import List.

Open Scope error_monad_scope.

Parameter schedule      : ident -> list trconstr -> list positive.
Parameter print_nlustre : NL.Syn.global -> unit.
Parameter print_stc     : Stc.Syn.program -> unit.
Parameter print_sch     : Stc.Syn.program -> unit.
Parameter print_obc     : Obc.Syn.program -> unit.
Parameter do_fusion     : unit -> bool.
Parameter do_sync       : unit -> bool.
Parameter do_expose     : unit -> bool.

Module ExternalSchedule.
  Definition schedule := schedule.
End ExternalSchedule.

Module Scheduler := Stc.Scheduler ExternalSchedule.

Definition is_well_sch_system (r: res unit) (s: system) : res unit :=
  do _ <- r;
  let args := map fst s.(s_in) in
  let mems := ps_from_list (map fst s.(s_lasts)) in
  if Stc.Wdef.is_well_sch_tcs mems args s.(s_tcs)
  then OK tt
  else Error (Errors.msg ("system " ++ pos_to_str s.(s_name) ++ " is not well scheduled.")).

Definition is_well_sch (P: Stc.Syn.program) : res Stc.Syn.program :=
  do _ <- fold_left is_well_sch_system P (OK tt);
  OK P.

Definition nl_to_cl (main_node: ident) (G: NL.Syn.global) : res Clight.program :=
  OK G
  @@  print print_nlustre
  @@  NL2Stc.translate
  @@  print print_stc
  @@  Scheduler.schedule
  @@@ is_well_sch
  @@  print print_sch
  @@  Stc2Obc.translate
  @@  total_if do_fusion (map Obc.Fus.fuse_class)
  @@  Obc.Def.add_defaults
  @@  print print_obc
  @@@ Generation.translate (do_sync tt) (do_expose tt) main_node.

Axiom add_builtins: Clight.program -> Clight.program.

Definition nl_to_asm (main_node: ident) (G: NL.Syn.global) : res Asm.program :=
  nl_to_cl main_node G
  @@  print print_Clight
  @@  add_builtins
  @@@ transf_clight2_program.

Definition compile (D: list LustreAst.declaration) (main_node: ident)
  : res (NL.Syn.global * Asm.program) :=
  do G <- elab_declarations D @@ @proj1_sig _ _;
  do P <- nl_to_asm main_node G;
  OK (G, P).
