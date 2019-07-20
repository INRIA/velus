From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import Streams.
From Velus Require Import ObcToClight.Generation.
From Velus Require Import Traces.
From Velus Require Import ClightToAsm.

From compcert Require Import common.Errors.
From compcert Require Import common.Events.
From compcert Require Import common.Behaviors.
From compcert Require Import cfrontend.Clight.
From compcert Require Import cfrontend.ClightBigstep.
From compcert Require Import lib.Integers.
From compcert Require Import driver.Compiler.

From Velus Require Import Instantiator.
Import Stc.Syn.
Import NL.
Import Obc.Syn.
Import Obc.Sem.
Import Obc.Typ.
Import Obc.Equ.
Import Obc.Def.
Import Fusion.
Import Stc2ObcInvariants.
Import Str.
Import Strs.
Import OpAux.
Import Interface.Op.
From Velus Require Import ObcToClight.Correctness.
From Velus Require Import Lustre.LustreElab.

From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Omega.

Open Scope error_monad_scope.
Open Scope stream_scope.

Parameter schedule      : ident -> list trconstr -> list positive.
Parameter print_nlustre : global -> unit.
Parameter print_stc     : Stc.Syn.program -> unit.
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
    if Stc.Wdef.well_sch mems args s.(s_tcs)
    then OK tt
    else Error (Errors.msg ("system " ++ pos_to_str s.(s_name) ++ " is not well scheduled.")).

Definition is_well_sch (P: Stc.Syn.program) : res Stc.Syn.program :=
  do _ <- fold_left is_well_sch_system P (OK tt);
    OK P.

Lemma is_well_sch_error:
  forall G e,
    fold_left is_well_sch_system G (Error e) = Error e.
Proof.
  induction G as [|n G]; simpl; auto.
Qed.

Lemma is_well_sch_program:
  forall P,
    fold_left is_well_sch_system P (OK tt) = OK tt ->
    Stc.Wdef.Well_scheduled P.
Proof.
  unfold Stc.Wdef.Well_scheduled.
  induction P as [|s]; simpl.
  - constructor.
  - intro Fold.
    destruct (Stc.Wdef.well_sch (ps_from_list (map fst (Stc.Syn.s_lasts s)))
                               (map fst (Stc.Syn.s_in s)) (Stc.Syn.s_tcs s)) eqn: E.
    + apply Stc.Wdef.Is_well_sch_by_refl in E.
      * constructor; auto.
      * apply Stc.Def.s_nodup_defined.
    + rewrite is_well_sch_error in Fold; discriminate.
Qed.

Definition schedule_program (P: Stc.Syn.program) : res Stc.Syn.program :=
  is_well_sch (Scheduler.schedule P).

Definition nl_to_cl (main_node: ident) (g: global) : res Clight.program :=
  OK g
     @@ print print_nlustre
     @@ NL2Stc.translate
     @@ print print_stc
     @@@ schedule_program
     @@ Stc2Obc.translate
     @@ total_if do_fusion (map Obc.Fus.fuse_class)
     @@ add_defaults
     @@ print print_obc
     @@@ Generation.translate (do_sync tt) (do_expose tt) main_node.

Axiom add_builtins: Clight.program -> Clight.program.
Axiom add_builtins_spec:
  forall B p,
    (forall t, B <> Goes_wrong t) ->
    program_behaves (semantics2 p) B -> program_behaves (semantics2 (add_builtins p)) B.

Definition nl_to_asm (main_node: ident) (g: global) : res Asm.program :=
  OK g
     @@@ nl_to_cl main_node
     @@ print print_Clight
     @@ add_builtins
     @@@ transf_clight2_program.

Definition compile (D: list LustreAst.declaration) (main_node: ident) : res Asm.program :=
  elab_declarations D
                    @@@ (fun G => L2NL.to_global (proj1_sig G))
                    @@@ nl_to_asm main_node.

(* Section WtStream. *)

(*   Variable G: global. *)
(*   Variable main: ident. *)
(*   Variable ins: stream (list val). *)
(*   Variable outs: stream (list val). *)

(*   Definition wt_ins := *)
(*     forall n node, *)
(*       find_node main G = Some node -> *)
(*       wt_vals (ins n) (idty node.(n_in)). *)

(*   Definition wt_outs := *)
(*     forall n node, *)
(*       find_node main G = Some node -> *)
(*       wt_vals (outs n) (idty node.(n_out)). *)

(* End WtStream. *)

Section ForallStr.
  Context {A: Type}.
  Variable P: A -> Prop.
  CoInductive Forall_Str: Stream A -> Prop :=
  Always:
    forall x xs,
      P x ->
      Forall_Str xs ->
      Forall_Str (x ::: xs).
End ForallStr.

Definition wt_streams: list (Stream val) -> list (ident * type) -> Prop :=
  Forall2 (fun s xt => Forall_Str (fun v => wt_val v (snd xt)) s).

Lemma wt_streams_spec:
  forall vss xts,
    wt_streams vss xts ->
    forall n, wt_vals (tr_Streams vss n) xts.
Proof.
  unfold wt_vals.
  intros * WTs n; revert dependent vss; induction n; intros.
  - rewrite tr_Streams_hd.
    induction WTs as [|???? WT]; simpl; auto.
    constructor; auto.
    inv WT; auto.
  - rewrite <-tr_Streams_tl.
    apply IHn.
    clear - WTs; induction WTs as [|???? WT]; simpl;
      constructor; auto.
    inv WT; auto.
Qed.

Section WtStream.

  Variable G: global.
  Variable main: ident.
  Variable ins: list (Stream val).
  Variable outs: list (Stream val).

  Definition wt_ins :=
    forall node,
      find_node main G = Some node ->
      Forall2 (fun s xt => Forall_Str (fun v => wt_val v (snd xt)) s) ins (idty node.(n_in)).

  Definition wt_outs :=
    forall node,
      find_node main G = Some node ->
      Forall2 (fun s xt => Forall_Str (fun v => wt_val v (snd xt)) s) outs (idty node.(n_out)).

End WtStream.

Section Bisim.

  Variable G: global.
  Variable main: ident.
  Variable ins: list (Stream val).
  Variable outs: list (Stream val).

  Inductive eventval_match: eventval -> AST.typ -> val -> Prop :=
  | ev_match_int: forall i,
      eventval_match (EVint i) AST.Tint (Values.Vint i)
  | ev_match_long: forall i,
      eventval_match (EVlong i) AST.Tlong (Values.Vlong i)
  | ev_match_float: forall f,
      eventval_match (EVfloat f) AST.Tfloat (Values.Vfloat f)
  | ev_match_single: forall f,
      eventval_match (EVsingle f) AST.Tsingle (Values.Vsingle f).

  (** All well-typed, dataflow values can be turned into event values. *)
  Lemma eventval_match_of_val:
    forall v t,
      wt_val v t ->
      eventval_match (eventval_of_val v)
                     (AST.type_of_chunk (type_chunk t))
                     v.
  Proof.
    intros v t Hwt.
    inversion Hwt; try constructor.
    destruct sz; destruct sg; try constructor.
  Qed.

  (** [eventval_match] is a stripped-down version of CompCert's [Events.eventval_match] *)
  Remark eventval_match_compat:
    forall ge ev t v,
      eventval_match ev t v -> Events.eventval_match ge ev t v.
  Proof. inversion 1; constructor. Qed.

  Inductive match_trace (f: eventval -> ident * type -> event):
    list val -> list (ident * type) -> trace -> Prop :=
  | MTNil:
      match_trace f [] [] []
  | MTCons:
      forall v vs x t xts ev evtval T,
        eventval_match evtval (AST.type_of_chunk (type_chunk t)) v ->
        f evtval (x, t) = ev ->
        match_trace f vs xts T ->
        match_trace f (v :: vs) ((x, t) :: xts) (ev :: T).

  (** Match a list of events loading values from the suitable, global
      volatile variables *)
  Definition match_trace_load: list val -> list (ident * type) -> trace -> Prop :=
    match_trace (fun ev xt => Event_vload (type_chunk (snd xt))
                                       (glob_id (fst xt))
                                       Ptrofs.zero ev).

  (** Match a list of events storing values to the suitable, global
      volatile variables *)
  Definition match_trace_store: list val -> list (ident * type) -> trace -> Prop :=
    match_trace (fun ev xt => Event_vstore (type_chunk (snd xt))
                                 (glob_id (fst xt))
                                 Ptrofs.zero ev).

  (** The trace generated by [mk_event] is characterized by [mask] *)
  Lemma mk_event_spec:
    forall (f: eventval -> ident * type -> event) vs xts,
      wt_vals vs xts ->
      match_trace f vs xts (mk_event (fun v => f (eventval_of_val v)) vs xts).
  Proof.
    intros * Hwt. generalize dependent xts.
    induction vs as [|v vs IHvs];
      intros xts Hwt; destruct xts as [|[x t] xts];
        inv Hwt; try constructor.
    rewrite Traces.mk_event_cons.
    apply MTCons with (evtval := eventval_of_val v);
      eauto using eventval_match_of_val.
  Qed.


  (** The trace of events induced by the execution of the Clight program
      corresponds to an infinite stream that alternates between loads and
      stores of the values passed and, respectively, retrieved from the
      dataflow node at each instant. *)
  CoInductive bisim_io': nat -> traceinf -> Prop :=
    Step:
      forall node n t t' T,
        find_node main G = Some node ->
        match_trace_load (map (Str_nth n) ins) (idty node.(n_in)) t ->
        match_trace_store (map (Str_nth n) outs) (idty node.(n_out)) t' ->
        bisim_io' (S n) T ->
        bisim_io' n (t *** t' *** T).

  Definition bisim_io := bisim_io' 0.

End Bisim.

Hint Resolve
     Obc.Fus.fuse_wt_program
     Obc.Fus.fuse_call
     Obc.Fus.fuse_wt_mem
     Obc.Fus.fuse_loop_call
(*      NL2StcTyping.translate_wt *)
(*      Scheduler.scheduler_wt_program *)
     (*      Stc2ObcTyping.translate_wt *)
     wt_add_defaults_class
     wt_mem_add_defaults
     stmt_call_eval_add_defaults
     loop_call_add_defaults
     ClassFusible_translate
     Scheduler.scheduler_wc_program
     NL2StcClocking.translate_wc
     No_Naked_Vars_add_defaults_class
     stmt_call_eval_add_defaults
     Obc.Fus.fuse_No_Overwrites
     translate_No_Overwrites
     Obc.Fus.fuse_cannot_write_inputs
     translate_cannot_write_inputs
.

Lemma find_node_trace_spec:
  forall G f node ins outs m
    (Step_in_spec : m_in m <> [])
    (Step_out_spec : m_out m <> [])
    (Hwt_in : forall n, wt_vals (tr_Streams ins n) (m_in m))
    (Hwt_out : forall n, wt_vals (tr_Streams outs n) (m_out m)),
    find_node f G = Some node ->
    m_in m = idty (n_in node) ->
    m_out m = idty (n_out node) ->
    bisim_io G f ins outs
             (traceinf_of_traceinf'
                (transl_trace m Step_in_spec Step_out_spec
                              (tr_Streams ins) (tr_Streams outs) Hwt_in Hwt_out 0)).
Proof.
  intros ??????????? Hstep_in Hstep_out.
  unfold bisim_io.
  generalize 0%nat.
  cofix COINDHYP; intro.
  unfold transl_trace, Traces.trace_step.
  rewrite Traces.unfold_mk_trace.
  rewrite E0_left, E0_left_inf.
  rewrite Eappinf_assoc.
  econstructor; eauto;
    rewrite Hstep_in || rewrite Hstep_out;
    apply mk_event_spec;
    rewrite <-Hstep_in || rewrite <-Hstep_out; auto.
Qed.

Definition pstr (xss: stream (list val)) : stream (list value) :=
  fun n => map present (xss n).
Definition pStr: list (Stream val) -> list (Stream value) := map (Streams.map present).

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

Lemma behavior_nl_to_cl:
  forall G P main ins outs,
    wc_global G ->
    wt_global G ->
    wt_ins G main ins ->
    wt_outs G main outs ->
    normal_args G ->
    CoindSem.sem_node G main (pStr ins) (pStr outs) ->
    nl_to_cl main G = OK P ->
    exists T, program_behaves (semantics2 P) (Reacts T)
         /\ bisim_io G main ins outs T.
Proof.
  intros * Hwc Hwt Hwti Hwto Hnorm Hsem COMP.
  unfold nl_to_cl in COMP.
  simpl in COMP; repeat rewrite print_identity in COMP.
  destruct (schedule_program (NL2Stc.translate G)) eqn: Sch;
    simpl in COMP; try discriminate.
  unfold schedule_program, is_well_sch in Sch; simpl in Sch.
  destruct (fold_left is_well_sch_system (Scheduler.schedule (NL2Stc.translate G))
                      (OK tt)) eqn: Wsch; simpl in *; try discriminate; destruct u.
  inv Sch.
  apply is_well_sch_program in Wsch.
  repeat rewrite print_identity in COMP.
  pose proof COMP as COMP'.
  assert (exists n, find_node main G = Some n) as (main_node & Find)
      by (inv Hsem; eauto).
  pose proof Find as Find_node.
  apply NL2Stc.find_node_translate in Find as (bl & P' & Find& ?); subst.
  apply Scheduler.scheduler_find_system in Find.
  apply Stc2Obc.find_system_translate in Find as (c_main &?& Find &?&?); subst.
  assert (Ordered_nodes G) by (eapply wt_global_Ordered_nodes; eauto).
  apply implies in Hsem.
  rewrite 2 tr_Streams_pStr in Hsem.
  set (ins' := tr_Streams ins) in *;
    set (outs' := tr_Streams outs) in *.
  assert (forall n, 0 < length (ins' n)) as Length.
  { inversion_clear Hsem as [???????? Ins].
    intro k; specialize (Ins k); apply Forall2_length in Ins.
    unfold pstr in Ins; rewrite 2 map_length in Ins.
    rewrite <-Ins.
    apply n_ingt0.
  }
  apply sem_msem_node in Hsem as (M & Hsem); auto.
  assert (Stc.Wdef.Well_defined (Scheduler.schedule (NL2Stc.translate G))).
  { split; [|split]; auto.
    - apply Scheduler.scheduler_ordered, NL2StcCorr.Ordered_nodes_systems; auto.
    - apply Scheduler.scheduler_normal_args, NL2StcNormalArgs.translate_normal_args; auto.
  }
  apply NL2StcCorr.correctness_loop in Hsem as (?& Hsem); auto.
  apply Scheduler.scheduler_loop in Hsem; auto.
  assert (forall n, Forall2 Stc2ObcCorr.eq_if_present (pstr ins' n) (map Some (ins' n)))
    by (unfold pstr; intros; clear; induction (ins' n); constructor; simpl; auto).
  assert (forall n, Exists (fun v => v <> absent) (pstr ins' n))
         by (unfold pstr; intros; specialize (Length n);
             destruct (ins' n); simpl in *; try omega;
             constructor; discriminate).
  apply Stc2ObcCorr.correctness_loop_call with (ins := fun n => map Some (ins' n))
    in Hsem as (me0 & Rst & Hsem &?); auto.
  setoid_rewrite value_to_option_pstr in Hsem.
  set (tr_G := NL2Stc.translate G) in *;
    set (sch_tr_G := Scheduler.schedule tr_G) in *;
    set (tr_sch_tr_G := Stc2Obc.translate sch_tr_G) in *;
    set (tr_main_node := NL2Stc.translate_node main_node) in *;
    set (sch_tr_main_node := Scheduler.schedule_system tr_main_node) in *.
  pose proof (Stc2Obc.exists_reset_method sch_tr_main_node) as Find_reset.
  pose proof (Stc2Obc.exists_step_method sch_tr_main_node) as Find_step.
  set (m_step := Stc2Obc.step_method sch_tr_main_node) in *;
    set (m_reset := Stc2Obc.reset_method sch_tr_main_node) in *.
  assert (wt_program tr_sch_tr_G)
    by (apply Stc2ObcTyping.translate_wt, Scheduler.scheduler_wt_program,
        NL2StcTyping.translate_wt; auto).
  assert (wt_mem me0 (Stc2Obc.translate (Scheduler.schedule P'))
                 (Stc2Obc.translate_system sch_tr_main_node))
    by (eapply pres_sem_stmt_call with (f := reset) in Find as (? & ?);
        eauto; simpl; constructor).
  assert (m_in m_step <> nil) as Step_in_spec.
  { apply Stc2Obc.find_method_stepm_in in Find_step.
    rewrite Find_step; simpl.
    pose proof (n_ingt0 main_node) as Hin.
    intro E; rewrite <-length_idty, E in Hin; simpl in Hin; omega.
  }
  assert (m_out m_step <> nil) as Step_out_spec.
  { apply Stc2Obc.find_method_stepm_out in Find_step.
    rewrite Find_step; simpl.
    pose proof (n_outgt0 main_node) as Hout.
    intro E; rewrite <-length_idty, E in Hout; simpl in Hout; omega.
  }
  assert (forall n, wt_vals (ins' n) (m_in m_step)) as Hwt_in
      by (erewrite Stc2Obc.find_method_stepm_in; eauto;
          apply wt_streams_spec, Hwti; auto).
  assert (forall n, wt_vals (outs' n) (m_out m_step)) as Hwt_out
      by (erewrite Stc2Obc.find_method_stepm_out; eauto;
          apply wt_streams_spec, Hwto; auto).
  pose proof (find_method_name _ _ _ Find_step) as Eq';
    pose proof (find_method_name _ _ _ Find_reset) as Eq'';
    rewrite <-Eq'' in Rst.
  unfold Generation.translate in COMP.
  unfold total_if in *.
  destruct (do_fusion tt).
  - pose proof Find as Find';
      pose proof Find_step as Find_step';
      pose proof Find_reset as Find_reset'.
    apply Obc.Fus.fuse_find_class in Find;
      apply Obc.Fus.fuse_find_method' in Find_step;
      apply Obc.Fus.fuse_find_method' in Find_reset.
    apply find_class_add_defaults_class in Find.
    apply find_method_add_defaults_method in Find_step;
      apply find_method_add_defaults_method in Find_reset;
      rewrite find_method_map_add_defaults_method in Find_step, Find_reset.
    rewrite Find, Find_step, Find_reset in *.
    pose proof (find_class_name _ _ _ _ Find) as Eq;
      rewrite <-Eq in Rst, Hsem.
    rewrite <-Obc.Fus.fuse_method_in in Step_in_spec, Hwt_in;
      rewrite <-Obc.Fus.fuse_method_out in Step_out_spec, Hwt_out.
    assert (Forall_methods (fun m => Obc.Inv.No_Overwrites (m_body m)) (map Obc.Fus.fuse_class tr_sch_tr_G))
           by (apply Obc.Fus.fuse_No_Overwrites, translate_No_Overwrites; auto).
    assert (Forall_methods
              (fun m => Forall (fun x => ~ Obc.Inv.Can_write_in x (m_body m)) (map fst (m_in m)))
              (map Obc.Fus.fuse_class tr_sch_tr_G))
      by (apply Obc.Fus.fuse_cannot_write_inputs, translate_cannot_write_inputs).
    econstructor; split; eauto.
    + assert (Forall Obc.Fus.ClassFusible tr_sch_tr_G)
        by (apply ClassFusible_translate; auto;
            apply Scheduler.scheduler_wc_program; eauto;
            apply NL2StcClocking.translate_wc; auto).
      eapply reacts'
        with (1:=COMP') (8:=Find) (9:=Find_reset) (10:=Find_step) (me0:=me0)
             (Step_in_spec:=Step_in_spec) (Step_out_spec:=Step_out_spec)
             (Hwt_in:=Hwt_in) (Hwt_out:=Hwt_out); eauto.
      * intros ??????? Call; eapply stmt_call_eval_add_defaults_class_not_None with (3 := Call); eauto.
      * change [] with (map Some (@nil val)); eauto.
    + eapply find_node_trace_spec; eauto.
  - apply find_class_add_defaults_class in Find.
    apply find_method_add_defaults_method in Find_step;
      apply find_method_add_defaults_method in Find_reset;
      rewrite find_method_map_add_defaults_method in Find_step, Find_reset.
    rewrite Find, Find_step, Find_reset in *.
    pose proof (find_class_name _ _ _ _ Find) as Eq;
      rewrite <-Eq in Rst, Hsem.
    assert (Forall_methods (fun m => Obc.Inv.No_Overwrites (m_body m)) tr_sch_tr_G)
      by (apply translate_No_Overwrites; auto).
    assert (Forall_methods
              (fun m => Forall (fun x => ~ Obc.Inv.Can_write_in x (m_body m)) (map fst (m_in m)))
              tr_sch_tr_G)
           by (apply translate_cannot_write_inputs).
    econstructor; split.
    + eapply reacts'
        with (1:=COMP') (8:=Find) (10:=Find_step) (me0:=me0)
             (Step_in_spec:=Step_in_spec) (Step_out_spec:=Step_out_spec)
             (Hwt_in:=Hwt_in) (Hwt_out:=Hwt_out);
        eauto.
      * intros ??????? Call; eapply stmt_call_eval_add_defaults_class_not_None with (3 := Call); eauto.
      * change [] with (map Some (@nil val)); eauto.
    + eapply find_node_trace_spec; eauto.
Qed.

Lemma behavior_nl_to_asm:
  forall G P main ins outs,
    wc_global G ->
    wt_global G ->
    wt_ins G main ins ->
    wt_outs G main outs ->
    normal_args G ->
    CoindSem.sem_node G main (pStr ins) (pStr outs) ->
    nl_to_asm main G = OK P ->
    exists T, program_behaves (Asm.semantics P) (Reacts T)
         /\ bisim_io G main ins outs T.
Proof.
  unfold nl_to_asm; simpl.
  intros * ?????? Comp.
  destruct (nl_to_cl main G) as [p|] eqn: Comp'; simpl in Comp; try discriminate.
  eapply  behavior_nl_to_cl in Comp' as (T & Beh & Bisim); eauto.
  eapply reacts_trace_preservation in Comp; eauto.
  apply add_builtins_spec; auto.
  intros ? ?; discriminate.
Qed.

(** The ultimate lemma states that, if
    - the parsed declarations [D] elaborate to a dataflow program [G] and
      a proof [Gp] that it satisfies [wt_global G] and [wc_global G],
    - the values on input streams [ins] are well-typed according to the
      interface of the [main] node,
    - similarly for output streams [outs],
    - the input and output streams are related by the dataflow semantics
      of the node [main] in [G], and
    - compilation succeeds in generating an assembler program [P],
    then the assembler program generates an infinite sequence of volatile
    reads and writes that correspond to the successive values on the
    input and output streams. *)

(* Theorem behavior_asm: *)
(*   forall D G Gp P main ins outs, *)
(*     elab_declarations D = OK (exist _ G Gp) -> *)
(*     wt_ins G main ins -> *)
(*     wt_outs G main outs -> *)
(*     sem_node G main (pstr ins) (pstr outs) -> *)
(*     compile D main = OK P -> *)
(*     exists T, program_behaves (Asm.semantics P) (Reacts T) *)
(*          /\ bisim_io G main ins outs T. *)
(* Proof. *)
(*   intros D G (WT & WC) P main ins outs Elab ** Comp. *)
(*   simpl in *. unfold compile, print in Comp. *)
(*   rewrite Elab in Comp; simpl in Comp. *)
(*   destruct (nl_to_cl main G) as [p|] eqn: Comp'; simpl in Comp; try discriminate. *)
(*   assert (normal_args G) by admit. *)
(*   edestruct behavior_clight as (T & Beh & Bisim); eauto. *)
(*   eapply reacts_trace_preservation in Comp; eauto. *)
(*   apply add_builtins_spec; auto. *)
(*   intros ? ?; discriminate. *)
(* Qed. *)
