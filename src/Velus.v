From compcert Require Import common.Errors.
From compcert Require Import common.Behaviors.
From compcert Require Import driver.Compiler.
From compcert Require Import cfrontend.Clight.
From compcert Require Import cfrontend.ClightBigstep.

From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import CoindStreams.
From Velus Require Import ObcToClight.Generation.
From Velus Require Import Traces.
From Velus Require Import ClightToAsm.
From Velus Require Import Interface.
From Velus Require Import Instantiator.
From Velus Require Import Lustre.LustreElab.
Import NL.
Import L.
Import Stc.Syn.
Import Obc.Syn.
Import Obc.Def.
Import Fusion.
Import OpAux.
Import Op.

From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.

Open Scope error_monad_scope.
Open Scope stream_scope.

Parameter schedule      : ident -> list trconstr -> list positive.
Parameter print_lustre  : @global elab_prefs -> unit.
Parameter print_nlustre : NL.Syn.global -> unit.
Parameter print_stc     : Stc.Syn.program -> unit.
Parameter print_sch     : Stc.Syn.program -> unit.
Parameter print_obc     : Obc.Syn.program -> unit.
Parameter do_dupregrem  : unit -> bool.
Parameter do_fusion     : unit -> bool.
Parameter do_norm_switches : unit -> bool.
Parameter do_sync       : unit -> bool.
Parameter do_expose     : unit -> bool.

Definition is_causal (G: @global elab_prefs) : res (@global elab_prefs) :=
  do _ <- check_causality G;
  OK G.

Module ExternalSchedule.
  Definition schedule := schedule.
End ExternalSchedule.

Module Scheduler := Stc.Scheduler ExternalSchedule.

Definition is_well_sch_system (r: res unit) (s: system) : res unit :=
  do _ <- r;
    let args := map fst s.(s_in) in
    let mems := ps_from_list (map fst s.(s_nexts)) in
    if Stc.SchV.well_sch mems args s.(s_tcs)
    then OK tt
    else Error (MSG "system " :: CTX s.(s_name) :: MSG " is not well scheduled." :: nil).

Definition is_well_sch (P: Stc.Syn.program) : res Stc.Syn.program :=
  do _ <- fold_left is_well_sch_system P.(systems) (OK tt);
  OK P.

Definition schedule_program (P: Stc.Syn.program) : res Stc.Syn.program :=
  is_well_sch (Scheduler.schedule P).

Definition l_to_nl (G : @global elab_prefs) : res NL.Syn.global :=
  OK G
     @@ print print_lustre
     @@@ is_causal
     @@ normalize_global
     @@@ TR.Tr.to_global.

Definition nl_to_cl (main_node: ident) (g: NL.Syn.global) : res Clight.program :=
  OK g
     @@ total_if do_dupregrem NL.DupRegRem.remove_dup_regs
     @@ print print_nlustre
     @@ NL2Stc.translate
     @@ print print_stc
     @@@ schedule_program
     @@ print print_sch
     @@ Stc2Obc.translate
     @@ total_if do_fusion Obc.Fus.fuse_program
     @@ total_if do_norm_switches Obc.SwN.normalize_switches
     @@ add_defaults
     @@ print print_obc
     @@@ Generation.translate (do_sync tt) (do_expose tt) main_node.

Axiom add_builtins: Clight.program -> Clight.program.
Axiom add_builtins_spec:
  forall B p,
    (forall t, B <> Goes_wrong t) ->
    program_behaves (semantics2 p) B -> program_behaves (semantics2 (add_builtins p)) B.

Definition nl_to_asm (main_node: ident) (g: NL.Syn.global) : res Asm.program :=
  OK g
     @@@ nl_to_cl main_node
     @@ print print_Clight
     @@ add_builtins
     @@@ transf_clight2_program.

Definition compile (D: list LustreAst.declaration) (main_node: ident) : res Asm.program :=
  elab_declarations D
                    @@ @proj1_sig _ _
                    @@@ l_to_nl
                    @@@ nl_to_asm main_node.
