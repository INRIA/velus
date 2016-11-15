Require Import Rustre.Common.
Require Import Rustre.Ident.
Require Import Rustre.DataflowToObc.Typing.
Require Import Rustre.ObcToClight.Translation.
Require Import Rustre.Traces.
Require Import Rustre.ClightToAsm.

Require Import common.Errors.
Require Import common.Events.
Require Import common.Behaviors.
Require Import cfrontend.Clight.
Require Import cfrontend.ClightBigstep.
Require Import lib.Integers.
Require Import driver.Compiler.

Require Import Rustre.Instantiator.
Import DF.
Import WeFDec.
Import DF.Mem.
Import Obc.Syn.
Import Fus.
Import Trans.
Import Corr.
Import Typ.
Import OpAux.
Import Interface.Op.
Require Import ObcToClight.Correctness.

Require Import String.
Require Import List.
Import List.ListNotations.

Open Scope error_monad_scope.

Definition is_well_sch (res: res unit) (n: node) :=
  match res with
  | OK _ =>
    let eqs := n.(n_eqs) in
    let ni := map fst n.(n_in) in
    if well_sch (memories eqs) ni eqs then OK tt
    else Error (Errors.msg ("node " ++ pos_to_str n.(n_name) ++ " is not well scheduled."))
  | _ => res
  end.

Definition fuse_method (m: method): method :=
  match m with
    mk_method name ins vars out body nodup good =>
    mk_method name ins vars out (fuse body) nodup good
  end.

Lemma map_m_name_fuse_methods:
  forall methods,
    map m_name (map fuse_method methods) = map m_name methods.
Proof.
  intro ms; induction ms as [|m ms]; auto.
  simpl. rewrite IHms.
  now destruct m.
Qed.

Lemma NoDup_m_name_fuse_methods:
  forall methods,
    NoDup (map m_name methods) ->
    NoDup (map m_name (map fuse_method methods)).
Proof.
  intros; now rewrite map_m_name_fuse_methods.
Qed.

Definition fuse_class (c: class): class :=
  match c with
    mk_class name mems objs methods nodup nodupm =>
    mk_class name mems objs (List.map fuse_method methods) nodup
             (NoDup_m_name_fuse_methods _ nodupm)
  end.

Definition df_to_cl (g: global) (main_node: ident): res Clight.program :=
  do _ <- (fold_left is_well_sch g (OK tt));
  ObcToClight.Translation.translate ((* map fuse_class *) (Trans.translate g)) main_node.

Axiom add_builtins: Clight.program -> Clight.program.
Axiom add_builtins_spec:
  forall B p,
    (forall t, B <> Goes_wrong t) ->
    program_behaves (semantics2 p) B -> program_behaves (semantics2 (add_builtins p)) B.
Definition compile (g: global) (main_node: ident): res Asm.program :=
  let p := df_to_cl g main_node in
  p @@ print print_Clight
    @@ add_builtins
    @@@ transf_clight2_program.
  
Section WtStream.

Variable G: global.
Variable main: ident.
Variable ins: stream (list const).
Variable outs: stream (list const).

Definition wt_ins :=
  forall n node, find_node main G = Some node ->
            wt_vals (map sem_const (ins n)) node.(n_in).

Definition wt_outs :=
  forall n node, find_node main G = Some node ->
            wt_vals (map sem_const (outs n)) node.(n_out).

End WtStream.

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
      mask_load (map Interface.Op.sem_const (ins n)) node.(n_in) t ->
      mask_store (map Interface.Op.sem_const (outs n)) node.(n_out) t' ->
      bisim_io' (S n) T ->
      bisim_io' n (t *** t' *** T).

Definition bisim_io := bisim_io' 0.

End Bisim.


Lemma soundness_cl:
  forall G P main ins outs,
    Welldef_global G ->
    wt_global G ->
    wt_ins G main ins ->
    wt_outs G main outs ->
    let xss := fun n => map (fun c => present (sem_const c)) (ins n) in
    let yss := fun n => map (fun c => present (sem_const c)) (outs n) in
    sem_node G main xss yss ->
    df_to_cl G main = OK P ->
    exists T, bigstep_program_diverges function_entry2 P T
         /\ bisim_io G main ins outs T.
Proof.
  intros ** Comp.
  edestruct dostep'_correct as (me0 & c_main & prog_main & Heval & Emain & Hwt_mem & Step); eauto.
  unfold df_to_cl in Comp.
  destruct (fold_left is_well_sch G (OK tt)); try discriminate; simpl in Comp.
  pose proof Comp.
  unfold Translation.translate in Comp.
  rewrite Emain in *.
  destruct (find_method Ids.step (c_methods c_main)) as [m_step|] eqn: Estep; try discriminate.
  destruct (find_method Ids.reset (c_methods c_main)) as [m_reset|] eqn: Ereset; try discriminate.
  pose proof (find_class_name _ _ _ _ Emain) as Eq;
    pose proof (find_method_name _ _ _ Estep) as Eq';
    pose proof (find_method_name _ _ _ Ereset) as Eq'';
    rewrite <-Eq, <-Eq'' in Heval; rewrite <-Eq in Step.
  edestruct find_class_translate as (main_node & ? & Hmain); eauto.
  rewrite Hmain in Ereset, Estep.
  pose proof (exists_reset_method main_node) as Ereset'.
  rewrite Ereset in Ereset'.
  inv Ereset'.
  assert (m_in m_step <> nil) as Step_in_spec.
  { apply find_method_stepm_in in Estep.
    pose proof (n_ingt0 main_node) as Hin.
    rewrite Estep; intro E; rewrite E in Hin; simpl in Hin.
    eapply Lt.lt_irrefl; eauto.
  }
  assert (m_out m_step <> nil) as Step_out_spec.
  { apply find_method_stepm_out in Estep.
    pose proof (n_outgt0 main_node) as Hout.
    rewrite Estep; intro E; rewrite E in Hout; simpl in Hout.
    eapply Lt.lt_irrefl; eauto.
  }
  assert (forall n, OpAux.wt_vals (List.map Interface.Op.sem_const (ins n)) (m_in m_step))
    as Hwt_in
    by now erewrite find_method_stepm_in; eauto.
  assert (forall n, OpAux.wt_vals (List.map Interface.Op.sem_const (outs n)) (m_out m_step))
    as Hwt_out
    by now erewrite find_method_stepm_out; eauto.
  econstructor; split.
  - eapply diverges'
    with (prog_main := prog_main)
           (me0:=me0) (Step_in_spec:=Step_in_spec) (Step_out_spec:=Step_out_spec)
                    (Hwt_in:=Hwt_in) (Hwt_out:=Hwt_out); eauto.
    apply Typ.translate_wt; auto.
  - assert (Hstep_in: m_step.(m_in) = main_node.(n_in))
      by now apply find_method_stepm_in.
    assert (Hstep_out: m_step.(m_out) = main_node.(n_out))
      by now apply find_method_stepm_out.
    clear - H1 H2 H5 Hstep_in Hstep_out.
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
      apply mk_event_spec; auto.
Qed.

Lemma behavior_clight:
  forall G P main ins outs,
    Welldef_global G ->
    wt_global G ->
    wt_ins G main ins ->
    wt_outs G main outs ->
    let xss := fun n => map (fun c => present (sem_const c)) (ins n) in
    let yss := fun n => map (fun c => present (sem_const c)) (outs n) in
    sem_node G main xss yss ->
    df_to_cl G main = OK P ->
    (forall t, ~ program_behaves (semantics2 P) (Diverges t)) ->
    exists T, program_behaves (semantics2 P) (Reacts T)
         /\ bisim_io G main ins outs T.
Proof.
  intros ** Hbeh; edestruct soundness_cl as (? & ? & ?); eauto.
  eexists; split; eauto.
  assert (Smallstep.bigstep_diverges (bigstep_semantics_fe function_entry2 P) x)
    by match goal with
       | H: bigstep_program_diverges _ _ _ |- _ => 
         destruct H; econstructor; eauto
       end.
  edestruct behavior_bigstep_diverges as [|(? & ? & ?)]; eauto using bigstep_semantics_sound.
  exfalso. eapply Hbeh; eauto.
Qed.

Lemma behavior_asm:
  forall G P main ins outs,
    Welldef_global G ->
    wt_global G ->
    wt_ins G main ins ->
    wt_outs G main outs ->
    let xss := fun n => map (fun c => present (sem_const c)) (ins n) in
    let yss := fun n => map (fun c => present (sem_const c)) (outs n) in
    sem_node G main xss yss ->
    compile G main = OK P ->
    (forall t, ~ program_behaves (Asm.semantics P) (Diverges t)) ->
    exists T, program_behaves (Asm.semantics P) (Reacts T)
         /\ bisim_io G main ins outs T.
Proof.
  intros ** Comp Hbeh.
  unfold compile, print in Comp.
  destruct (df_to_cl G main) as [p|] eqn: Comp'; simpl in Comp; try discriminate.
  edestruct behavior_clight as (T & Beh & Bisim); eauto.
  - intros T1 Div.
    eapply (Hbeh T1).
    eapply diverges_trace_preservation; eauto.
    apply add_builtins_spec; auto.
    intros ? ?; discriminate.
  - eapply reacts_trace_preservation in Comp; eauto.
    apply add_builtins_spec; auto.
    intros ? ?; discriminate.  
Qed.
             