Require Import Velus.Common.
Require Import Velus.Ident.
(* Require Import Velus.NLustreToObc.NLObcTyping. *)
Require Import Velus.ObcToClight.Generation.
Require Import Velus.Traces.
Require Import Velus.ClightToAsm.

Require Import common.Errors.
Require Import common.Events.
Require Import common.Behaviors.
Require Import cfrontend.Clight.
Require Import cfrontend.ClightBigstep.
Require Import lib.Integers.
Require Import driver.Compiler.

Require Import Velus.Instantiator.
Import SB.Syn.
Import NL.
(* Import NL.Syn. *)
(* Import NL.Sem. *)
(* Import NL.Mem. *)
(* Import NL.Typ. *)
Import Obc.Syn.
Import Obc.Sem.
Import Obc.Typ.
Import Obc.Equ.
Import Fusion.
(* Import Trans. *)
(* Import Corr. *)
Import Str.
Import OpAux.
Import Interface.Op.
Require Import ObcToClight.Correctness.
Require Import NLustreElab.

Require Import String.
Require Import List.
Import List.ListNotations.

Open Scope error_monad_scope.

Parameter schedule      : ident -> list SB.Syn.equation -> list positive.
Parameter print_snlustre: global -> unit.
Parameter print_obc     : Obc.Syn.program -> unit.
Parameter do_fusion     : unit -> bool.
Parameter do_sync       : unit -> bool.
Parameter do_expose     : unit -> bool.

Module ExternalSchedule.
  Definition schedule := schedule.
End ExternalSchedule.

Module Scheduler := SB.Scheduler ExternalSchedule.

Definition is_well_sch_block (r: res unit) (b: block) : res unit :=
  do _ <- r;
    let args := map fst b.(b_in) in
    let mems := ps_from_list (map fst b.(b_lasts)) in
    if SB.Wdef.well_sch mems args b.(b_eqs)
    then OK tt
    else Error (Errors.msg ("block " ++ pos_to_str b.(b_name) ++ " is not well scheduled.")).

Definition is_well_sch (P: SB.Syn.program) : res SB.Syn.program :=
  do _ <- fold_left is_well_sch_block P (OK tt);
    OK P.

Lemma is_well_sch_error:
  forall G e,
    fold_left is_well_sch_block G (Error e) = Error e.
Proof.
  induction G as [|n G]; simpl; auto.
Qed.

Lemma is_well_sch_program:
  forall P,
    fold_left is_well_sch_block P (OK tt) = OK tt ->
    SB.Wdef.Well_scheduled P.
Proof.
  induction P as [|bl]; simpl.
  - constructor.
  - intro Fold.
    destruct (SB.Wdef.well_sch (ps_from_list (map fst (SB.Syn.b_lasts bl)))
                               (map fst (SB.Syn.b_in bl)) (SB.Syn.b_eqs bl)) eqn: E.
    + apply SB.Wdef.Is_well_sch_by_refl in E; constructor; auto.
    + rewrite is_well_sch_error in Fold; discriminate.
Qed.

Definition schedule_program (P: SB.Syn.program) : res SB.Syn.program :=
  is_well_sch (Scheduler.schedule P).

Definition nl_to_cl (main_node: ident) (g: global): res Clight.program :=
  OK g
     @@ print print_snlustre
     @@ NL2SB.translate
     (* @@ print print_sb *)
     @@@ schedule_program
     @@ SB2Obc.translate
     @@ total_if do_fusion (map Obc.Fus.fuse_class)
     @@ print print_obc
     @@@ Generation.translate (do_sync tt) (do_expose tt) main_node.

Axiom add_builtins: Clight.program -> Clight.program.
Axiom add_builtins_spec:
  forall B p,
    (forall t, B <> Goes_wrong t) ->
    program_behaves (semantics2 p) B -> program_behaves (semantics2 (add_builtins p)) B.

Definition compile (D: list LustreAst.declaration) (main_node: ident) : res Asm.program :=
  elab_declarations D @@@ (fun g => nl_to_cl main_node (proj1_sig g))
                    @@ print print_Clight
                    @@ add_builtins
                    @@@ transf_clight2_program.

Section WtStream.

Variable G: global.
Variable main: ident.
Variable ins: stream (list const).
Variable outs: stream (list const).

Definition wt_ins :=
  forall n node,
    find_node main G = Some node ->
    wt_vals (map sem_const (ins n)) (idty node.(n_in)).

Definition wt_outs :=
  forall n node,
    find_node main G = Some node ->
    wt_vals (map sem_const (outs n)) (idty node.(n_out)).

End WtStream.

(* Lemma scheduler_wt_ins: *)
(*   forall G f ins, *)
(*     wt_ins G f ins -> *)
(*     wt_ins (Scheduler.schedule G) f ins. *)
(* Proof. *)
(*   unfold wt_ins. *)
(*   intros G f ins Hwt n node Hfind. *)
(*   apply Scheduler.scheduler_find_node' in Hfind. *)
(*   destruct Hfind as (node' & Hfind & Hnode). *)
(*   apply Hwt with (n:=n) in Hfind. *)
(*   subst. destruct node'; auto. *)
(* Qed. *)

(* Lemma scheduler_wt_outs: *)
(*   forall G f outs, *)
(*     wt_outs G f outs -> *)
(*     wt_outs (Scheduler.schedule G) f outs. *)
(* Proof. *)
(*   unfold wt_outs. *)
(*   intros G f ins Hwt n node Hfind. *)
(*   apply Scheduler.scheduler_find_node' in Hfind. *)
(*   destruct Hfind as (node' & Hfind & Hnode). *)
(*   apply Hwt with (n:=n) in Hfind. *)
(*   subst. destruct node'; auto. *)
(* Qed. *)

Section Bisim.

Variable G: global.
Variable main: ident.
Variable ins: stream (list const).
Variable outs: stream (list const).

Inductive eventval_match: eventval -> AST.typ -> Values.val -> Prop :=
  | ev_match_int: forall i,
      eventval_match (EVint i) AST.Tint (Values.Vint i)
  | ev_match_long: forall i,
      eventval_match (EVlong i) AST.Tlong (Values.Vlong i)
  | ev_match_float: forall f,
      eventval_match (EVfloat f) AST.Tfloat (Values.Vfloat f)
  | ev_match_single: forall f,
      eventval_match (EVsingle f) AST.Tsingle (Values.Vsingle f).


Lemma eventval_match_of_val:
  (** All well-typed, dataflow values can be turned into event values. *)
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

Remark eventval_match_compat:
  (** [eventval_match] is a stripped-down version of CompCert's [Events.eventval_match] *)
  forall ge ev t v,
    eventval_match ev t v -> Events.eventval_match ge ev t v.
Proof. inversion 1; constructor. Qed.


Inductive mask (f: eventval -> ident * type -> event):
  list Values.val -> list (ident * type) -> trace -> Prop :=
| MaskNil:

  (*---------------*)
    mask f [] [] []
| MaskCons: forall v vs x t xts ev evtval T,

    eventval_match evtval (AST.type_of_chunk (type_chunk t)) v ->
    f evtval (x, t) = ev ->
    mask f vs xts T ->
  (*------------------------------------------*)
    mask f (v :: vs) ((x, t) :: xts) (ev :: T).

Definition mask_load :=
  (** Match a list of events loading values from the suitable, global
  volatile variables *)
  mask (fun ev xt => Event_vload (type_chunk (snd xt))
                              (glob_id (fst xt))
                              Int.zero ev).

Definition mask_store :=
  (** Match a list of events storing values to the suitable, global
  volatile variables *)
  mask (fun ev xt => Event_vstore (type_chunk (snd xt))
                               (glob_id (fst xt))
                               Int.zero ev).

Lemma mk_event_spec:
  (** The trace generated by [mk_event] is characterized by [mask] *)
  forall (f: eventval -> ident * type -> event) vs xts,
    wt_vals vs xts ->
    mask f vs xts (mk_event (fun v => f (eventval_of_val v)) vs xts).
Proof.
intros ** Hwt. generalize dependent xts.
induction vs as [|v vs IHvs];
  intros xts Hwt; destruct xts as [|[x t] xts];
  inv Hwt; try constructor.
rewrite Traces.mk_event_cons.
apply MaskCons with (evtval := eventval_of_val v);
  eauto using eventval_match_of_val.
Qed.


(** The trace of events induced by the execution of the Clight program
corresponds to an infinite stream that alternates between loads and
stores of the values passed and, respectively, retrieved from the
dataflow node at each instant. *)

CoInductive bisim_io': nat -> traceinf -> Prop
  := Step: forall n node t t' T,
      find_node main G = Some node ->
      mask_load (map sem_const (ins n)) (idty node.(n_in)) t ->
      mask_store (map sem_const (outs n)) (idty node.(n_out)) t' ->
      bisim_io' (S n) T ->
      bisim_io' n (t *** t' *** T).

Definition bisim_io := bisim_io' 0.

End Bisim.

(* Lemma scheduler_bisim_io: *)
(*   forall G main ins outs T, *)
(*     bisim_io G main ins outs T <-> *)
(*     bisim_io (Scheduler.schedule G) main ins outs T. *)
(* Proof. *)
(*   intros G main ins outs T. *)
(*   split; unfold bisim_io; generalize 0%nat; revert T; cofix CH. *)
(*   - intros T n HH. *)
(*     destruct HH. *)
(*     match goal with H:find_node _ _ = _ |- _ => *)
(*       apply Scheduler.scheduler_find_node in H end. *)
(*     destruct node0; eauto using bisim_io'. *)
(*   - intros T n HH. *)
(*     destruct HH. *)
(*     match goal with H:find_node _ _ = _ |- _ => *)
(*       apply Scheduler.scheduler_find_node' in H; *)
(*       destruct H as (node & Hfind & Hnode0) end. *)
(*     subst. *)
(*     destruct node; eauto using bisim_io'. *)
(* Qed. *)

Lemma fuse_loop_call:
  forall f c ins outs G me,
    Forall Obc.Fus.ClassFusible (SB2Obc.translate G) ->
    Obc.Sem.loop_call (SB2Obc.translate G) c f ins outs 0 me ->
    Obc.Sem.loop_call (map Obc.Fus.fuse_class (SB2Obc.translate G)) c f ins outs 0 me.
Proof.
  intros f c ins outs G.
  generalize 0%nat.
  cofix COINDHYP.
  intros n ** Hdo.
  destruct Hdo.
  econstructor; eauto using Obc.Fus.fuse_call.
Qed.

(* Lemma Welldef_global_patch: *)
(*   forall G, *)
(*     Wellsch_global G -> *)
(*     wt_global G -> *)
(*     Welldef_global G. *)
(* Proof. *)
(*   induction G as [|n G]; intros; auto using Welldef_global. *)
(*   inv H. inv H0. *)
(*   specialize (IHG H4 H2). *)
(*   constructor; auto. *)
(*   - intro Hni. clear H3 H4. *)
(*     apply Forall_Exists with (1:=H5) in Hni. clear H5. *)
(*     apply Exists_exists in Hni. *)
(*     destruct Hni as (eq & Hin & WTeq & Hni). *)
(*     inv Hni. simpl in *. *)
(*     unfold wt_node in *. *)
(*     inv WTeq. *)
(*     assert (find_node n.(n_name) G <> None) as Hfind *)
(*         by (now apply not_None_is_Some; exists n0). *)
(*     apply find_node_Exists in Hfind. *)
(*     apply Forall_Exists with (1:=H6) in Hfind. *)
(*     apply Exists_exists in Hfind. *)
(*     destruct Hfind as (n' & Hin' & Hne & He). *)
(*     intuition. *)
(*   - intros f Hni. *)
(*     apply Forall_Exists with (1:=H5) in Hni. clear H5. *)
(*     apply Exists_exists in Hni. *)
(*     destruct Hni as (eq & Hin & WTeq & Hni). *)
(*     destruct eq; inv Hni. *)
(*     inv WTeq. rewrite H7. intuition. *)
(* Qed. *)

Hint Resolve Obc.Fus.fuse_wt_program
     Obc.Fus.fuse_call Obc.Fus.fuse_wt_mem
     fuse_loop_call
     (* Welldef_global_patch *)
     (* Fusible.ClassFusible_translate *)
.

Lemma scheduler_loop:
  forall P f xss yss S0,
    SB.Sem.loop P f xss yss S0 0 ->
    SB.Sem.loop (Scheduler.schedule P) f xss yss S0 0.
Proof.
  generalize 0%nat.
  cofix COFIX; inversion_clear 1.
  econstructor; eauto.
  apply Scheduler.scheduler_sem_block; eauto.
Qed.

Lemma behavior_clight:
  forall G P main ins outs,
    wc_global G ->
    wt_global G ->
    wt_ins G main ins ->
    wt_outs G main outs ->
    sem_node G main (vstr ins) (vstr outs) ->
    nl_to_cl main G = OK P ->
    exists T, program_behaves (semantics2 P) (Reacts T)
         /\ bisim_io G main ins outs T.
Proof.
  intros ** Hwc Hwt Hwti Hwto Hsem COMP.
  (* apply Scheduler.scheduler_wc_global in Hwc. *)
  (* apply Scheduler.scheduler_wt_global in Hwt. *)
  (* apply scheduler_wt_ins in Hwti. *)
  (* apply scheduler_wt_outs in Hwto. *)
  (* apply Scheduler.scheduler_sem_node in Hsem. *)
  (* setoid_rewrite scheduler_bisim_io. *)
  unfold nl_to_cl in COMP.
  simpl in COMP; repeat rewrite print_identity in COMP.
  destruct (schedule_program (NL2SB.translate G)) eqn: Sch;
    simpl in COMP; try discriminate.
  unfold schedule_program, is_well_sch in Sch; simpl in Sch.
  destruct (fold_left is_well_sch_block (Scheduler.schedule (NL2SB.translate G))
                      (OK tt)) eqn: Wsch; simpl in *; try discriminate; destruct u.
  inv Sch.
  apply is_well_sch_program in Wsch.
  repeat rewrite print_identity in COMP.
  pose proof COMP as COMP'.

  (* edestruct dostep'_correct *)
  (*   as (me0 & c_main & prog_main & Heval & Emain & Hwt_mem & Step); eauto. *)
  assert (Ordered_nodes G) by admit.
  assert (exists n, find_node main G = Some n) as (main_node & Find)
      by (inv Hsem; eauto).
  pose proof Find as Find_node.
  apply NL2SB.find_node_translate in Find as (bl & P' & Find& ?); subst.
  apply Scheduler.scheduler_find_block in Find.
  apply SB2Obc.find_block_translate in Find as (c_main &?& Find &?&?); subst.
  apply sem_msem_node in Hsem as (M & M' & Hsem); auto.
  assert (SB.Wdef.Well_defined (Scheduler.schedule (NL2SB.translate G)))
    by (split; auto; apply Scheduler.scheduler_ordered, NL2SBCorr.Ordered_nodes_blocks; auto).
  apply NL2SBCorr.correctness_loop, scheduler_loop in Hsem; auto.
  apply SB2ObcCorr.correctness_loop_call in Hsem as (me0 & Rst & Hsem &?); auto.
  unfold Generation.translate in COMP.
  unfold total_if in *.
  destruct (do_fusion tt).
  - pose proof Find as Find'.
    apply Obc.Fus.fuse_find_class in Find.
    rewrite Find in *.
    destruct (find_method Ids.step
                          (c_methods
                             (Obc.Fus.fuse_class (SB2Obc.translate_block
                                                    (Scheduler.schedule_block
                                                       (NL2SB.translate_node main_node))))))
      as [fuse_m_step|] eqn: Efusestep; try discriminate.
    destruct (find_method reset
                          (c_methods
                             (Obc.Fus.fuse_class (SB2Obc.translate_block
                                                    (Scheduler.schedule_block
                                                       (NL2SB.translate_node main_node))))))
      as [fuse_m_reset|] eqn: Efusereset; try discriminate.
    pose proof (find_class_name _ _ _ _ Find) as Eq;
      pose proof (find_method_name _ _ _ Efusestep) as Eq';
      pose proof (find_method_name _ _ _ Efusereset) as Eq'';
      rewrite <-Eq, <-Eq'' in Rst; rewrite <-Eq in Hsem.
    edestruct Obc.Fus.fuse_find_method with (1:=Efusereset)
      as (m_reset & Eq_r & Ereset); subst fuse_m_reset.
    edestruct Obc.Fus.fuse_find_method with (1:=Efusestep)
      as (m_step & Eq_s & Estep); subst fuse_m_step.
    rewrite SB2Obc.exists_reset_method in Ereset; inv Ereset.
    assert (m_in (Obc.Fus.fuse_method m_step) <> nil) as Step_in_spec.
    { rewrite Obc.Fus.fuse_method_in.
      apply SB2Obc.find_method_stepm_in in Estep.
      rewrite Estep; simpl.
      pose proof (n_ingt0 main_node) as Hin.
      intro E; rewrite <-length_idty, E in Hin; simpl in Hin; omega.
    }
    assert (m_out (Obc.Fus.fuse_method m_step) <> nil) as Step_out_spec.
    { rewrite Obc.Fus.fuse_method_out.
      apply SB2Obc.find_method_stepm_out in Estep.
      rewrite Estep; simpl.
      pose proof (n_outgt0 main_node) as Hout.
      intro E; rewrite <-length_idty, E in Hout; simpl in Hout; omega.
    }
    assert (forall n, wt_vals (map sem_const (ins n))
                         (m_in (Obc.Fus.fuse_method m_step))) as Hwt_in
        by (erewrite Obc.Fus.fuse_method_in, SB2Obc.find_method_stepm_in;
                    eauto; simpl; eauto).
    assert (forall n, wt_vals (map sem_const (outs n))
                         (m_out (Obc.Fus.fuse_method m_step))) as Hwt_out
        by (erewrite Obc.Fus.fuse_method_out, SB2Obc.find_method_stepm_out;
            eauto; simpl; eauto).
    econstructor; split.
    + eapply reacts'
        with (1:=COMP') (6:=Find) (8:=Efusestep) (me0:=me0)
             (Step_in_spec:=Step_in_spec) (Step_out_spec:=Step_out_spec)
             (Hwt_in:=Hwt_in) (Hwt_out:=Hwt_out); eauto.
       * apply Obc.Fus.fuse_wt_program; auto. admit.
       * apply Obc.Fus.fuse_call; auto. admit.
       * apply Obc.Fus.fuse_wt_mem. admit.
       * apply fuse_loop_call; eauto. admit.
    + assert (Hstep_in: (Obc.Fus.fuse_method m_step).(m_in) = idty main_node.(n_in))
        by (erewrite Obc.Fus.fuse_method_in, SB2Obc.find_method_stepm_in; eauto; reflexivity).
      assert (Hstep_out: (Obc.Fus.fuse_method m_step).(m_out) = idty main_node.(n_out))
        by (erewrite Obc.Fus.fuse_method_out, SB2Obc.find_method_stepm_out; eauto; reflexivity).
      clear - Find_node Hstep_in Hstep_out.
      unfold bisim_io.
      generalize 0%nat.
      cofix COINDHYP.
      intro n.
      unfold transl_trace.
      unfold Traces.trace_step.
      rewrite Traces.unfold_mk_trace.
      rewrite E0_left, E0_left_inf.
      rewrite Eappinf_assoc.
      econstructor; eauto;
        rewrite Hstep_in || rewrite Hstep_out;
        apply mk_event_spec;
        rewrite <-Hstep_in || rewrite <-Hstep_out; auto.

  - rewrite Find in *.
    destruct (find_method Ids.step (c_methods (SB2Obc.translate_block
                                                 (Scheduler.schedule_block
                                                    (NL2SB.translate_node main_node)))))
      as [m_step|] eqn: Estep; try discriminate.
    destruct (find_method Ids.reset (c_methods (SB2Obc.translate_block
                                                  (Scheduler.schedule_block
                                                     (NL2SB.translate_node main_node)))))
      as [m_reset|] eqn: Ereset; try discriminate.
    pose proof (find_class_name _ _ _ _ Find) as Eq;
      pose proof (find_method_name _ _ _ Estep) as Eq';
      pose proof (find_method_name _ _ _ Ereset) as Eq'';
      rewrite <-Eq, <-Eq'' in Rst; rewrite <-Eq in Hsem.
    pose proof Ereset;
      rewrite SB2Obc.exists_reset_method in Ereset; inv Ereset.
    assert (m_in m_step <> nil) as Step_in_spec.
    { apply SB2Obc.find_method_stepm_in in Estep.
      rewrite Estep; simpl.
      pose proof (n_ingt0 main_node) as Hin.
      intro E; rewrite <-length_idty, E in Hin; simpl in Hin; omega.
    }
    assert (m_out m_step <> nil) as Step_out_spec.
    { apply SB2Obc.find_method_stepm_out in Estep.
      rewrite Estep; simpl.
      pose proof (n_outgt0 main_node) as Hout.
      intro E; rewrite <-length_idty, E in Hout; simpl in Hout; omega.
    }
    assert (forall n, wt_vals (map sem_const (ins n)) (m_in m_step)) as Hwt_in
        by (erewrite SB2Obc.find_method_stepm_in; eauto; simpl; eauto).
    assert (forall n, wt_vals (map sem_const (outs n)) (m_out m_step)) as Hwt_out
        by (erewrite SB2Obc.find_method_stepm_out; eauto; simpl; eauto).
    econstructor; split.
    + eapply reacts'
        with (1:=COMP') (6:=Find) (8:=Estep) (me0:=me0)
             (Step_in_spec:=Step_in_spec) (Step_out_spec:=Step_out_spec)
             (Hwt_in:=Hwt_in) (Hwt_out:=Hwt_out);
        eauto.
      * admit.
      * admit.
    + assert (Hstep_in: m_step.(m_in) = idty main_node.(n_in))
        by (erewrite SB2Obc.find_method_stepm_in; eauto; reflexivity).
      assert (Hstep_out: m_step.(m_out) = idty main_node.(n_out))
        by (erewrite SB2Obc.find_method_stepm_out; eauto; reflexivity).
      clear - Find_node Hstep_in Hstep_out.
      unfold bisim_io.
      generalize 0%nat.
      cofix COINDHYP.
      intro n.
      unfold transl_trace.
      unfold Traces.trace_step.
      rewrite Traces.unfold_mk_trace.
      rewrite E0_left, E0_left_inf.
      rewrite Eappinf_assoc.
      econstructor; eauto;
        rewrite Hstep_in || rewrite Hstep_out;
        apply mk_event_spec;
        rewrite <-Hstep_in || rewrite <-Hstep_out; auto.
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
Theorem behavior_asm:
  forall D G Gp P main ins outs,
    elab_declarations D = OK (exist _ G Gp) ->
    wt_ins G main ins ->
    wt_outs G main outs ->
    sem_node G main (vstr ins) (vstr outs) ->
    compile D main = OK P ->
    exists T, program_behaves (Asm.semantics P) (Reacts T)
         /\ bisim_io G main ins outs T.
Proof.
  intros D G (WT & WC) P main ins outs Elab ** Comp.
  simpl in *. unfold compile, print in Comp.
  rewrite Elab in Comp; simpl in Comp.
  destruct (nl_to_cl main G) as [p|] eqn: Comp'; simpl in Comp; try discriminate.
  edestruct behavior_clight as (T & Beh & Bisim); eauto.
  eapply reacts_trace_preservation in Comp; eauto.
  apply add_builtins_spec; auto.
  intros ? ?; discriminate.
Qed.
