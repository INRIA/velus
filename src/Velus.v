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
From Velus Require Import ObcToClight.Interface.
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

Parameter cutting_points: list ident -> list ident -> list trconstr -> list ident.
Parameter schedule      : ident -> list trconstr -> list positive.
Parameter print_lustre  : @global (fun _ _ => True) elab_prefs -> unit.
Parameter print_complete: @global complete elab_prefs -> unit.
Parameter print_noauto  : @global noauto auto_prefs -> unit.
Parameter print_noswitch: @global noswitch switch_prefs -> unit.
Parameter print_nolocal : @global nolocal local_prefs -> unit.
Parameter print_unnested: @global unnested norm1_prefs -> unit.
Parameter print_normlast: @global normlast last_prefs -> unit.
Parameter print_normfby : @global normalized fby_prefs -> unit.
Parameter print_nlustre : NL.Syn.global -> unit.
Parameter print_stc     : @Stc.Syn.program (PSP.of_list lustre_prefs) -> unit.
Parameter print_cut     : @Stc.Syn.program (PSP.of_list gensym_prefs) -> unit.
Parameter print_sch     : @Stc.Syn.program (PSP.of_list gensym_prefs) -> unit.
Parameter print_obc     : Obc.Syn.program -> unit.
Parameter print_header  : Clight.program -> unit.
Parameter do_exp_inlining : unit -> bool.
Parameter do_dce        : unit -> bool.
Parameter do_dupregrem  : unit -> bool.
Parameter do_fusion     : unit -> bool.
Parameter do_norm_switches : unit -> bool.
Parameter do_obc_dce    : unit -> bool.
Parameter do_sync       : unit -> bool.
Parameter do_expose     : unit -> bool.

Definition is_causal (G: @global complete elab_prefs) : res (@global _ elab_prefs) :=
  do _ <- check_causality G;
  OK G.

Module ExternalCutCycles.
  Definition cutting_points := cutting_points.
End ExternalCutCycles.

Module CutCycles := Stc.CC ExternalCutCycles.

Module ExternalSchedule.
  Definition schedule := schedule.
End ExternalSchedule.

Module Scheduler := Stc.Scheduler ExternalSchedule.

Definition is_well_sch_system (r: res unit) (s: @system (PSP.of_list gensym_prefs)) : res unit :=
  do _ <- r;
    let args := map fst s.(s_in) in
    let mems := map fst s.(s_nexts) in
    if Stc.SchV.well_sch args mems s.(s_tcs)
    then OK tt
    else Error (MSG "system " :: CTX s.(s_name) :: MSG " is not well scheduled." :: nil).

Definition is_well_sch (P: Stc.Syn.program) : res Stc.Syn.program :=
  do _ <- fold_left is_well_sch_system P.(systems) (OK tt);
  OK P.

Definition schedule_program (P: Stc.Syn.program) : res Stc.Syn.program :=
  is_well_sch (Scheduler.schedule P).

Definition l_to_nl (G : @global (fun _ _ => True) elab_prefs) : res NL.Syn.global :=
  OK G
     @@ print print_lustre
     @@ complete_global
     @@ print print_complete
     @@@ is_causal
     @@ auto_global
     @@ print print_noauto
     @@ switch_global
     @@ print print_noswitch
     @@ inlinelocal_global
     @@ print print_nolocal
     @@ unnest_global
     @@ print print_unnested
     @@ normlast_global
     @@ print print_normlast
     @@ normfby_global
     @@ print print_normfby
     @@@ TR.Tr.to_global.

Definition nl_to_cl (main_node: option ident) (g: NL.Syn.global) : res Clight.program :=
  OK g
     @@ total_if do_exp_inlining NL.EI.EI.exp_inlining
     @@ total_if do_dce NL.DCE.DCE.dce_global
     @@ total_if do_dupregrem NL.DRR.DRR.remove_dup_regs
     @@ print print_nlustre
     @@ NL2Stc.translate
     @@ print print_stc
     @@ CutCycles.CC.cut_cycles
     @@ print print_cut
     @@@ schedule_program
     @@ print print_sch
     @@ Stc2Obc.translate
     @@ total_if do_fusion Obc.Fus.fuse_program
     @@ total_if do_norm_switches Obc.SwN.normalize_switches
     @@ total_if do_obc_dce Obc.DCE.deadcode_program
     @@ add_defaults
     @@ print print_obc
     @@@ Generation.translate (do_sync tt) (do_expose tt) main_node.

Axiom add_builtins: Clight.program -> Clight.program.
Axiom add_builtins_spec:
  forall B p,
    (forall t, B <> Goes_wrong t) ->
    program_behaves (semantics2 p) B -> program_behaves (semantics2 (add_builtins p)) B.

Definition nl_to_asm (main_node: option ident) (g: NL.Syn.global) : res Asm.program :=
  OK g
     @@@ nl_to_cl main_node
     @@ print print_Clight
     @@ print print_header
     @@ add_builtins
     @@@ transf_clight2_program.

Definition lustre_to_asm (main_node: option ident) G : res Asm.program :=
  OK G
    @@@ l_to_nl
    @@@ nl_to_asm main_node.

Definition compile (D: list LustreAst.declaration) (main_node: option ident) : res Asm.program :=
  elab_declarations D
                    @@ @proj1_sig _ _
                    @@@ lustre_to_asm main_node.
