(** The old correctness lemma, starting from NLustre *)

From compcert Require Import common.Errors.
From compcert Require Import common.Events.
From compcert Require Import common.Behaviors.
From compcert Require Import cfrontend.Clight.
From compcert Require Import cfrontend.ClightBigstep.
From compcert Require Import lib.Integers.
From compcert Require Import driver.Compiler.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Ident.
From Velus Require Import CoindStreams.
From Velus Require Import ObcToClight.Generation.
From Velus Require Import Traces.
From Velus Require Import ClightToAsm.
From Velus Require Import ObcToClight.Correctness.
From Velus Require Import Interface.
From Velus Require Import Instantiator.
From Velus Require Import Velus.
Import Stc.Syn.
Import NL.
Import Obc.Syn.
Import Obc.Sem.
Import Obc.Typ.
Import Obc.Equ.
Import Obc.Def.
Import Obc.Fus.
Import Obc.SwN.
Import Fusion.
Import Stc2ObcInvariants.
Import IStr.
Import CStr.
Import CIStr.
Import OpAux.
Import Op.

From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.

Open Scope error_monad_scope.
Open Scope stream_scope.

Lemma is_well_sch_error:
  forall G e,
    fold_left is_well_sch_system G (Error e) = Error e.
Proof.
  induction G as [|n G]; simpl; auto.
Qed.

Lemma is_well_sch_program:
  forall P,
    fold_left is_well_sch_system P.(Stc.Syn.systems) (OK tt) = OK tt ->
    Stc.Wdef.Well_scheduled P.
Proof.
  unfold Stc.Wdef.Well_scheduled.
  intro; induction (Stc.Syn.systems P) as [|s]; simpl; auto.
  intro Fold.
  cases_eqn E.
  - apply Stc.SchV.Is_well_sch_by_refl in E.
    constructor; auto.
  - rewrite is_well_sch_error in Fold; discriminate.
Qed.

Definition wt_streams: list (Stream value) -> list (ident * type) -> Prop :=
  Forall2 (fun s xt => SForall (fun v => wt_value v (snd xt)) s).

Lemma wt_streams_spec:
  forall vss xts,
    wt_streams vss xts <->
    forall n, wt_values (tr_Streams vss n) xts.
Proof.
  unfold wt_values.
  split.
  - intros * WTs n; revert dependent vss; induction n; intros.
    + rewrite tr_Streams_hd.
      induction WTs as [|???? WT]; simpl; auto.
      constructor; auto.
      inv WT; auto.
    + rewrite <-tr_Streams_tl.
      apply IHn.
      clear - WTs; induction WTs as [|???? WT]; simpl;
        constructor; auto.
      inv WT; auto.
  - intros WTs.
    unfold wt_streams.
    revert dependent vss.
    induction xts, vss; intros; try now (specialize (WTs 0); simpl in WTs; inv WTs).
    constructor; auto.
    + rewrite SForall_forall; intro n; specialize (WTs n); inv WTs; auto.
    + apply IHxts; intro n; specialize (WTs n); inv WTs; auto.
Qed.

Section WtStream.

  Variable G: global.
  Variable main: ident.
  Variable ins: list (Stream value).
  Variable outs: list (Stream value).

  Definition wt_ins :=
    forall node,
      find_node main G = Some node ->
      wt_streams ins (idty node.(n_in)).

  Definition wt_outs :=
    forall node,
      find_node main G = Some node ->
      wt_streams outs (idty node.(n_out)).

End WtStream.

Lemma node_in_out_not_nil:
  forall n,
    n.(n_in) <> [] \/ n.(n_out) <> [].
Proof.
  intro; left; apply node_in_not_nil.
Qed.

Local Hint Resolve
     fuse_wt_program
     fuse_call
     normalize_switches_call
     fuse_wt_memory
     normalize_switches_wt_memory
     fuse_loop_call
     normalize_switches_loop_call
     wt_add_defaults_class
     normalize_switches_wt_program
     wt_memory_add_defaults
     stmt_call_eval_add_defaults
     loop_call_add_defaults
     ProgramFusible_translate
     Scheduler.scheduler_wc_program
     NL2StcClocking.translate_wc
     Scheduler.scheduler_wt_program
     NL2StcTyping.translate_wt
     Stc2ObcTyping.translate_wt
     No_Naked_Vars_add_defaults_class
     fuse_No_Overwrites
     normalize_switches_No_Overwrites
     translate_No_Overwrites
     fuse_cannot_write_inputs
     translate_cannot_write_inputs
     normalize_switches_cannot_write_inputs
     wt_add_defaults_class
     wt_memory_add_defaults
     stmt_call_eval_add_defaults
     loop_call_add_defaults
     ProgramFusible_translate
     Scheduler.scheduler_wc_program
     NL2StcClocking.translate_wc
     Scheduler.scheduler_wt_program
     NL2StcTyping.translate_wt
     Stc2ObcTyping.translate_wt
     No_Naked_Vars_add_defaults_class
     translate_No_Overwrites
     translate_cannot_write_inputs
     node_in_out_not_nil : core.

(** The trace of a NLustre node *)
Section NLTrace.

  Variable (node: node) (ins outs: list (Stream value)).

  Hypothesis Spec_in_out : node.(n_in) <> [] \/ node.(n_out) <> [].
  Hypothesis Len_ins     : Datatypes.length ins = Datatypes.length node.(n_in).
  Hypothesis Len_outs    : Datatypes.length outs = Datatypes.length node.(n_out).

  Program Definition trace_node (n: nat): traceinf :=
    mk_trace (tr_Streams ins) (tr_Streams outs)
             (idty node.(n_in)) (idty node.(n_out))
             _ _ _ n.
  Next Obligation.
    destruct Spec_in_out.
    - left; intro E; apply map_eq_nil in E; auto.
    - right; intro E; apply map_eq_nil in E; auto.
  Defined.
  Next Obligation.
    unfold tr_Streams, idty; rewrite 2 map_length; auto.
  Defined.
  Next Obligation.
    unfold tr_Streams, idty; rewrite 2 map_length; auto.
  Defined.

  (** Simply link the trace of a Lustre node with the trace of an Obc step method with the same parameters *)
  Lemma trace_inf_sim_step_node:
    forall n m Spec_in_out_m Len_ins_m Len_outs_m,
      m_in m = idty (n_in node) ->
      m_out m = idty (n_out node) ->
      traceinf_sim (trace_step m (tr_Streams ins) (tr_Streams outs) Spec_in_out_m Len_ins_m Len_outs_m n)
                   (trace_node n).
  Proof.
    intros; unfold trace_step, trace_node.
    apply traceinf_sim'_sim.
    revert n; cofix COFIX; intro.
    rewrite unfold_mk_trace.
    rewrite unfold_mk_trace with (xs := idty (n_in node)).
    simpl.
    replace (load_events (tr_Streams ins n) (idty (n_in node)) ** store_events (tr_Streams outs n) (idty (n_out node)))
      with (load_events (tr_Streams ins n) (m_in m) ** store_events (tr_Streams outs n) (m_out m)); try congruence.
    constructor.
    - intro E; eapply Eapp_E0_inv in E.
      pose proof (load_store_events_not_E0 _ _ _ _ Spec_in_out_m Len_ins_m Len_outs_m n).
      intuition.
    - apply COFIX.
  Qed.

End NLTrace.

(** A bisimulation relation between a declared node's trace and a given trace *)
Inductive bisim_IO (G: global) (f: ident) (ins outs: list (Stream value)): traceinf -> Prop :=
  IOStep:
    forall T node
      (Spec_in_out : node.(n_in) <> [] \/ node.(n_out) <> [])
      (Len_ins     : Datatypes.length ins = Datatypes.length node.(n_in))
      (Len_outs    : Datatypes.length outs = Datatypes.length node.(n_out)),
      find_node f G = Some node ->
      traceinf_sim T (trace_node node ins outs Spec_in_out Len_ins Len_outs 0) ->
      bisim_IO G f ins outs T.

(** streams of present values *)
Definition pstr (xss: stream (list value)) : stream (list svalue) :=
  fun n => map present (xss n).
Definition pStr: list (Stream value) -> list (Stream svalue) :=
  map (Streams.map present).

Lemma tr_Streams_pStr:
  forall xss,
    tr_Streams (pStr xss) ≈ pstr (tr_Streams xss).
Proof.
  intros ? n; unfold pstr, pStr.
  revert xss; induction n; intros.
  - rewrite 2 tr_Streams_hd, 2 map_map; induction xss; simpl; auto.
  - rewrite <-2 tr_Streams_tl.
    rewrite <-IHn, 2 map_map; auto.
Qed.

Lemma value_to_option_pstr:
  forall xs,
    (fun n => map Stc2ObcCorr.value_to_option (pstr xs n)) ≈ (fun n => map Some (xs n)).
Proof.
  intros; unfold Stc2ObcCorr.value_to_option, pstr; intro.
  rewrite map_map; auto.
Qed.

Lemma find_node_find_system:
  forall G f n,
    find_node f G = Some n ->
      exists P,
        Stc.Syn.find_system f (NL2Stc.translate G) = Some (NL2Stc.translate_node n, P).
Proof.
  intros * Find.
  unfold find_node in Find; apply option_map_inv in Find as ((node, ?)& Find & E).
  simpl in E; subst node.
  apply find_unit_transform_units_forward in Find; eauto.
Qed.

Lemma find_system_find_class:
  forall P f s P',
    Stc.Syn.find_system f P = Some (s, P') ->
    Obc.Syn.find_class f (Stc2Obc.translate P) = Some (Stc2Obc.translate_system s, Stc2Obc.translate P').
Proof.
  intros * Find; eapply find_unit_transform_units_forward in Find; auto.
Qed.

(** Correctness from NLustre to Clight *)
Lemma behavior_nl_to_cl:
  forall G P main ins outs,
    wc_global G ->
    wt_global G ->
    wt_ins G main ins ->
    normal_args G ->
    CoindSem.sem_node G main (pStr ins) (pStr outs) ->
    nl_to_cl (Some main) G = OK P ->
    exists T, program_behaves (semantics2 P) (Reacts T)
         /\ bisim_IO G main ins outs T.
Proof.
  intros * Hwc Hwt Hwti Hnorm Hsem COMP.
  unfold nl_to_cl, schedule_program in COMP.
  simpl in COMP; repeat rewrite print_identity in COMP.

  (* Coinductive NLustre to nat->values *)
  assert (Ordered_nodes G) as Hord by (eapply wt_global_Ordered_nodes; eauto).
  apply implies in Hsem.
  rewrite 2 tr_Streams_pStr in Hsem.

  (* dead code elimination optimization *)
  remember (total_if do_dce dce_global G) as G'.
  assert (wt_global G') as Hwt'.
  { subst; unfold total_if; destruct (do_dce tt); auto.
    apply dce_wt; auto. }
  assert (wt_ins G' main ins) as Hwti'.
  { subst; unfold total_if; destruct (do_dce tt); auto.
    clear - Hwti. unfold wt_ins in *; intros n Hnode.
    eapply find_node_dce_backward in Hnode as (?&Hfind&Hnode); subst.
    simpl. eapply Hwti; eauto. }
  assert (wc_global G') as Hwc'.
  { subst; unfold total_if; destruct (do_dce tt); auto.
    eapply dce_wc; eauto. }
  assert (normal_args G') as Hnorm'.
  { subst; unfold total_if. destruct (do_dce tt); auto.
    apply dce_normal_args; auto. }
  assert (sem_node G' main (pstr (tr_Streams ins)) (pstr (tr_Streams outs))) as Hsem'.
  { subst; unfold total_if. destruct (do_dce tt); auto.
    apply dce_global_sem; auto. }
  assert (forall T, bisim_IO G main ins outs T <-> bisim_IO G' main ins outs T) as Hbisim.
  { subst; unfold total_if; destruct (do_dce tt). 2:reflexivity.
    clear - G. split; intros * Hbis; inv Hbis.
    - eapply find_node_dce_forward in H.
      econstructor; eauto.
    - eapply find_node_dce_backward in H as (?&Hfind&?); subst.
      econstructor; eauto.
  }
  setoid_rewrite Hbisim.
  clear Hord Hwc Hwt Hwti Hnorm Hsem Hbisim HeqG' G.
  rename G' into G, Hwti' into Hwti, Hwt' into Hwt, Hwc' into Hwc, Hnorm' into Hnorm, Hsem' into Hsem.

  (* remove duplicate registers optimization *)
  remember (total_if do_dupregrem remove_dup_regs G) as G'.
  assert (wt_global G') as Hwt'.
  { subst; unfold total_if; destruct (do_dupregrem tt); auto.
    eapply remove_dup_regs_wt; eauto. }
  assert (wt_ins G' main ins) as Hwti'.
  { subst; unfold total_if; destruct (do_dupregrem tt); auto.
    clear - Hwti. unfold wt_ins in *; intros n Hnode.
    eapply find_node_remove_dup_regs_backward in Hnode as (?&Hfind&Hnode); subst.
    simpl. eapply Hwti; eauto. }
  assert (wc_global G') as Hwc'.
  { subst; unfold total_if; destruct (do_dupregrem tt); auto.
    eapply remove_dup_regs_wc; eauto. }
  assert (normal_args G') as Hnorm'.
  { subst; unfold total_if. destruct (do_dupregrem tt); auto.
    apply remove_dup_regs_normal_args; auto. }
  assert (sem_node G' main (pstr (tr_Streams ins)) (pstr (tr_Streams outs))) as Hsem'.
  { subst; unfold total_if. destruct (do_dupregrem tt); auto.
    apply remove_dup_regs_sem; auto using wt_global_Ordered_nodes. }
  assert (forall T, bisim_IO G main ins outs T <-> bisim_IO G' main ins outs T) as Hbisim.
  { subst; unfold total_if; destruct (do_dupregrem tt). 2:reflexivity.
    clear - G. split; intros * Hbis; inv Hbis.
    - eapply find_node_remove_dup_regs_forward in H.
      econstructor; eauto.
    - eapply find_node_remove_dup_regs_backward in H as (?&Hfind&?); subst.
      econstructor; eauto.
  }
  setoid_rewrite Hbisim.
  clear Hwc Hwt Hwti Hnorm Hsem Hbisim HeqG' G.
  rename G' into G, Hwti' into Hwti, Hsem' into Hsem.

  (* well-scheduled Stc program *)
  destruct (is_well_sch (Scheduler.schedule (NL2Stc.translate G))) eqn: Sch;
    simpl in COMP; try discriminate.
  unfold is_well_sch in Sch.
  destruct (fold_left is_well_sch_system (Stc.Syn.systems (Scheduler.schedule (NL2Stc.translate G)))
                      (OK tt)) eqn: Wsch; try discriminate; destruct u.
  inv Sch.
  apply is_well_sch_program in Wsch.

  (* a main Stc system exists *)
  repeat rewrite print_identity in COMP.
  (* pose proof COMP as COMP'. *)
  assert (exists n, find_node main G = Some n) as (main_node & Find)
      by (inv Hsem; eauto).
  pose proof Find as Find_node.
  apply find_node_find_system in Find as (P' & Find).
  apply Scheduler.scheduler_find_system in Find.
  pose proof Find as Find_system.

  (* a main Obc class exists *)
  apply find_system_find_class in Find.

  set (ins' := tr_Streams ins) in *;
    set (outs' := tr_Streams outs) in *.
  assert (forall n, 0 < length (ins' n)) as Length.
  { inversion_clear Hsem as [???????? Ins].
    intro k; specialize (Ins k); apply Forall2_length in Ins.
    unfold pstr in Ins; rewrite 2 map_length in Ins.
    rewrite <-Ins.
    apply n_ingt0.
  }

  (* NLustre to Nlustre with memory *)
  assert (Ordered_nodes G) as Hord by (eapply wt_global_Ordered_nodes; eauto).
  apply sem_msem_node in Hsem as (M & Hsem); auto.

  (* NLustre with memory to Stc loop *)
  assert (Stc.Wdef.Well_defined (Scheduler.schedule (NL2Stc.translate G))).
  { split; [|split]; auto.
    - apply Scheduler.scheduler_ordered, NL2StcCorr.Ordered_nodes_systems; auto.
    - apply Scheduler.scheduler_normal_args, NL2StcNormalArgs.translate_normal_args; auto.
  }
  apply NL2StcCorr.correctness_loop in Hsem as (?& Hsem); auto.
  apply Scheduler.scheduler_loop in Hsem; auto.

  assert (forall n, Forall2 Stc2ObcCorr.eq_if_present (pstr ins' n) (map Some (ins' n)))
    by (unfold pstr; intros; clear; induction (ins' n); constructor; simpl; auto with obcsem).
  assert (forall n, Exists (fun v => v <> absent) (pstr ins' n))
         by (unfold pstr; intros; specialize (Length n);
             destruct (ins' n); simpl in *; try lia;
             constructor; discriminate).

  assert (ComTyp.wt_memory (M 0) (Scheduler.schedule P')
                           (Stc.Syn.mems_of_nexts (Stc.Syn.s_nexts (Scheduler.schedule_system (NL2Stc.translate_node main_node))))
                           (Stc.Syn.s_subs (Scheduler.schedule_system (NL2Stc.translate_node main_node))))
    by (take (Stc.Sem.initial_state _ _ _) and apply Scheduler.scheduler_initial_state in it;
        eapply Stc.TypSem.initial_state_wt_memory with (2 := it); eauto).
  assert (forall n,
             Forall2
               (fun xt vo =>
                  wt_option_value vo (fst (snd xt)))
               (Stc.Syn.s_in (Scheduler.schedule_system (NL2Stc.translate_node main_node)))
               (map Some (ins' n))).
  { subst ins'; simpl.
    apply Hwti in Find_node; clear - Find_node.
    rewrite wt_streams_spec in Find_node.
    intro n; specialize (Find_node n).
    setoid_rewrite Forall2_map_2 in Find_node.
    induction Find_node; simpl; auto.
  }

  (* Stc loop to Obc loop *)
  eapply Stc2ObcCorr.correctness_loop_call with (ins := fun n => map Some (ins' n))
    in Hsem as (me0 & Rst & Hsem &?); eauto with stcsem.
  setoid_rewrite value_to_option_pstr in Hsem.

  (* aliases *)
  set (tr_G := NL2Stc.translate G) in *;
    set (sch_tr_G := Scheduler.schedule tr_G) in *;
    set (tr_sch_tr_G := Stc2Obc.translate sch_tr_G) in *;
    set (tr_main_node := NL2Stc.translate_node main_node) in *;
    set (sch_tr_main_node := Scheduler.schedule_system tr_main_node) in *;
    set (main_class := Stc2Obc.translate_system sch_tr_main_node) in *.

  (* Obc methods step and reset *)
  pose proof (Stc2Obc.exists_reset_method sch_tr_main_node) as Find_reset.
  pose proof (Stc2Obc.exists_step_method sch_tr_main_node) as Find_step.
  set (m_step := Stc2Obc.step_method sch_tr_main_node) in *;
    set (m_reset := Stc2Obc.reset_method sch_tr_main_node) in *.

  (* well-typing *)
  assert (Stc.Typ.wt_program sch_tr_G) by (subst sch_tr_G tr_G; auto).
  assert (wt_program tr_sch_tr_G) by (subst tr_sch_tr_G; auto).
  assert (ComTyp.wt_memory me0 (Stc2Obc.translate (Scheduler.schedule P'))
                           (c_mems main_class) (c_objs main_class))
    by (eapply pres_sem_stmt_call with (f := Ids.reset) in Find as (? & ?); eauto; simpl; auto with typing).
  assert (wt_outs G main outs) as Hwto.
  { unfold wt_outs.
    intros * Find_node'; rewrite Find_node' in Find_node; inv Find_node.
    apply wt_streams_spec.
    intro n.
    eapply pres_loop_call with (n := n) in Hsem; eauto.
    - rewrite Forall2_map_1 in Hsem; simpl in Hsem; auto.
    - apply Hwti in Find_node'.
      rewrite wt_streams_spec in Find_node'.
      setoid_rewrite Forall2_map_1; eauto.
  }

  (* IO specs *)
  (* and assert some equalities between classes and methods *)
  assert (forall n, wt_values (ins' n) (m_in m_step)) as Hwt_in
      by (erewrite Stc2Obc.find_method_stepm_in; eauto;
          apply wt_streams_spec, Hwti; auto).
  assert (forall n, wt_values (outs' n) (m_out m_step)) as Hwt_out
      by (erewrite Stc2Obc.find_method_stepm_out; eauto;
          apply wt_streams_spec, Hwto; auto).

  set (obc_p := add_defaults
                  (total_if do_norm_switches normalize_switches
                            (total_if do_fusion fuse_program tr_sch_tr_G))) in *.
  set (obc_p' := add_defaults
                   (total_if do_norm_switches normalize_switches
                             (total_if do_fusion fuse_program
                                       (Stc2Obc.translate (Scheduler.schedule P'))))) in *.
  set (main_class' := GenerationProperties.c_main main obc_p P (do_sync tt) (do_expose tt) COMP) in *.
  set (main_step' := GenerationProperties.main_step main obc_p P (do_sync tt) (do_expose tt) COMP) in *.

  assert (obc_p' =
          GenerationProperties.prog_main main
                                         (add_defaults (total_if do_norm_switches normalize_switches
                                                                 (total_if do_fusion fuse_program tr_sch_tr_G)))
                                         P (do_sync tt) (do_expose tt) COMP
          /\ main_class' =
            add_defaults_class
              (total_if do_norm_switches normalize_class
                        (total_if do_fusion fuse_class main_class))) as [Eq_prog Eq_main].
  { pose proof (GenerationProperties.find_main_class _ _ _ _ _ COMP) as Find'.
    subst obc_p main_class'; unfold total_if in *.
    destruct (do_fusion tt), (do_norm_switches tt).
    - apply fuse_find_class, normalize_switches_find_class, find_class_add_defaults_class in Find.
      rewrite Find' in Find; injection Find; intros -> ->; split; auto.
    - apply fuse_find_class, find_class_add_defaults_class in Find.
      rewrite Find' in Find; injection Find; intros -> ->; auto.
    - apply normalize_switches_find_class, find_class_add_defaults_class in Find.
      rewrite Find' in Find; injection Find; intros -> ->; auto.
    - apply find_class_add_defaults_class in Find.
      rewrite Find' in Find; injection Find; intros -> ->; auto.
  }
  assert (main_step' =
          add_defaults_method
            (total_if do_norm_switches normalize_method
                      (total_if do_fusion fuse_method m_step))) as Eq_step.
  { pose proof (GenerationProperties.find_main_step _ _ _ _ _ COMP) as Find_step'.
    subst obc_p main_class main_class' main_step'; unfold total_if in *.
    rewrite Eq_main, add_defaults_class_find_method in Find_step'.
    apply option_map_inv in Find_step' as (?& Find_step' &?).
    destruct (do_fusion tt), (do_norm_switches tt).
    - apply fuse_find_method', normalize_switches_find_method in Find_step.
      rewrite Find_step' in Find_step; inv Find_step; auto.
    - apply fuse_find_method' in Find_step.
      rewrite Find_step' in Find_step; inv Find_step; auto.
    - apply normalize_switches_find_method in Find_step.
      rewrite Find_step' in Find_step; inv Find_step; auto.
    - rewrite Find_step' in Find_step; inv Find_step; auto.
  }
  assert (forall n, wt_values (ins' n) (m_in main_step')) as WTins.
  { intro; specialize (Hwt_in n).
    subst main_step'.
    rewrite Eq_step; unfold total_if; cases.
  }
  assert (forall n, wt_values (outs' n) (m_out main_step')) as WTouts.
  { intro; specialize (Hwt_out n).
    subst main_step'.
    rewrite Eq_step; unfold total_if; cases.
  }
  assert (n_in main_node <> [] \/ n_out main_node <> []) as Node_in_out_spec by apply node_in_out_not_nil.
  assert (m_in main_step' <> nil \/ m_out main_step' <> nil) as Step_in_out_spec.
  { rewrite Eq_step.
    assert (idty (n_in main_node) <> [] \/ idty (n_out main_node) <> [])
      by (destruct Node_in_out_spec as [Neq|Neq];
          ((now left; intro; eapply Neq, map_eq_nil; eauto)
           || (right; intro; eapply Neq, map_eq_nil; eauto))).
    unfold total_if; cases; simpl.
  }
  assert (wt_program (total_if do_norm_switches normalize_switches
                               (total_if do_fusion fuse_program tr_sch_tr_G)))
    by (unfold total_if; cases).

  eexists; split.

  - eapply correctness with (TRANSL := COMP) (me0 := me0)
                            (WTins := WTins) (WTouts := WTouts)
                            (Step_in_out_spec := Step_in_out_spec);
      subst obc_p; eauto.
    + intros ??????? Call; eapply stmt_call_eval_add_defaults_class_not_None
                             with (3 := Call); eauto.
    + change [] with (map Some (@nil value)); eauto.
      apply stmt_call_eval_add_defaults; auto;
        subst tr_sch_tr_G sch_tr_G tr_G;
        unfold total_if; cases; eauto 6.
    + apply loop_call_add_defaults; auto;
        subst tr_sch_tr_G sch_tr_G tr_G;
        unfold total_if; cases; eauto 6.
    + subst main_class' obc_p'; rewrite Eq_main, <-Eq_prog.
      apply wt_memory_add_defaults;
        unfold total_if; cases; eauto.

  - assert (m_in m_step = idty main_node.(n_in)) as Ein by auto.
    assert (m_out m_step = idty main_node.(n_out)) as Eout by auto.
    assert (length ins = length (n_in main_node)) as Len_ins.
    { transitivity (length (idty main_node.(n_in))); try apply map_length.
      rewrite <-Ein.
      specialize (Hwt_in 0); unfold ins' in Hwt_in; setoid_rewrite Forall2_map_1 in Hwt_in.
      eapply Forall2_length; eauto.
    }
    assert (length outs = length (n_out main_node)) as Len_outs.
    { transitivity (length (idty main_node.(n_out))); try apply map_length.
      rewrite <-Eout.
      specialize (Hwt_out 0); unfold outs' in Hwt_out; setoid_rewrite Forall2_map_1 in Hwt_out.
      eapply Forall2_length; eauto.
    }

    eapply IOStep with (Len_ins := Len_ins) (Len_outs := Len_outs) (Spec_in_out := Node_in_out_spec); auto.
    apply trace_inf_sim_step_node; auto;
      subst main_step'; rewrite Eq_step; unfold total_if; cases.
Qed.

(** Correctness from NLustre to ASM  *)
Lemma behavior_nl_to_asm:
  forall G P main ins outs,
    wc_global G ->
    wt_global G ->
    wt_ins G main ins ->
    normal_args G ->
    CoindSem.sem_node G main (pStr ins) (pStr outs) ->
    nl_to_asm (Some main) G = OK P ->
    exists T, program_behaves (Asm.semantics P) (Reacts T)
         /\ bisim_IO G main ins outs T.
Proof.
  unfold nl_to_asm; simpl.
  intros * ????? Comp.
  destruct (nl_to_cl (Some main) G) as [p|] eqn: Comp'; simpl in Comp; try discriminate.
  eapply  behavior_nl_to_cl in Comp' as (T & Beh & Bisim); eauto.
  eapply reacts_trace_preservation in Comp; eauto.
  apply add_builtins_spec; auto.
  intros ? ?; discriminate.
Qed.
