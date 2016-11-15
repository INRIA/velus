Require Import Rustre.Common.
Require Import Rustre.Ident.
Require Import Rustre.ObcToClight.Translation.

Require Import common.Errors.
Require Import common.Events.
Require Import cfrontend.Clight.
Require Import cfrontend.ClightBigstep.

Require Import Rustre.Instantiator.
Import DF.Syn.
Import WeFDec.
Import DF.Mem.
Import Obc.Syn.
Import Fus.
Import Trans.
Import Corr.
Import Typ.
Require Import ObcToClight.Correctness.

Require Import String.
Require Import List.
Import List.ListNotations.

Open Scope error_monad_scope.

Definition is_well_sch (res: res unit) (n: node) :=
  match res with
  | OK _ =>
    let eqs := n.(n_eqs) in
    let ni := List.map fst n.(n_in) in
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
    List.map m_name (List.map fuse_method methods) = List.map m_name methods.
Proof.
  intro ms; induction ms as [|m ms]; auto.
  simpl. rewrite IHms.
  now destruct m.
Qed.

Lemma NoDup_m_name_fuse_methods:
  forall methods,
    List.NoDup (List.map m_name methods) ->
    List.NoDup (List.map m_name (List.map fuse_method methods)).
Proof.
  intros; now rewrite map_m_name_fuse_methods.
Qed.

Definition fuse_class (c: class): class :=
  match c with
    mk_class name mems objs methods nodup nodupm =>
    mk_class name mems objs (List.map fuse_method methods) nodup
             (NoDup_m_name_fuse_methods _ nodupm)
  end.

Definition compile (g: global) (main_node: ident) :=
  do _ <- (List.fold_left is_well_sch g (OK tt));
  ObcToClight.Translation.translate ((* List.map fuse_class *) (Trans.translate g)) main_node.

Section WtStream.

Variable G: global.
Variable main: ident.
Variable ins: DF.Str.stream (list Interface.Op.const).
Variable outs: DF.Str.stream (list Interface.Op.const).

Definition wt_ins :=
  forall n node, find_node main G = Some node ->
            OpAux.wt_vals (List.map Interface.Op.sem_const (ins n)) node.(n_in).

Definition wt_outs :=
  forall n node, find_node main G = Some node ->
            OpAux.wt_vals (List.map Interface.Op.sem_const (outs n)) node.(n_out).

End WtStream.

Section Bisim.

Variable G: global.
Variable main: ident.
Variable ins: DF.Str.stream (list Interface.Op.const).
Variable outs: DF.Str.stream (list Interface.Op.const).

Inductive eventval_match: eventval -> AST.typ -> Values.val -> Prop :=
  | ev_match_int: forall i,
      eventval_match (EVint i) AST.Tint (Values.Vint i)
  | ev_match_long: forall i,
      eventval_match (EVlong i) AST.Tlong (Values.Vlong i)
  | ev_match_float: forall f,
      eventval_match (EVfloat f) AST.Tfloat (Values.Vfloat f)
  | ev_match_single: forall f,
      eventval_match (EVsingle f) AST.Tsingle (Values.Vsingle f).

Lemma eventval_match_compat:
  forall ge ev t v,
    eventval_match ev t v -> Events.eventval_match ge ev t v.
Proof. inversion 1; constructor. Qed.

Lemma eventval_match_of_val:
  forall v t,
    Interface.Op.wt_val v t ->
    eventval_match (Traces.eventval_of_val v)
                   (AST.type_of_chunk (Interface.Op.type_chunk t))
                   v.
Proof.
intros v t.
Admitted.



Inductive mask (f: eventval -> ident * Interface.Op.type -> event):
  list Values.val -> list (ident * Interface.Op.type) -> trace -> Prop :=
| MaskNil: mask f [] [] []
| MaskCons: forall v vs x t xts ev evtval T,
    eventval_match evtval (AST.type_of_chunk (Interface.Op.type_chunk t)) v ->
    f evtval (x, t) = ev ->
    mask f vs xts T ->
    mask f (v :: vs) ((x, t) :: xts) (ev :: T).

Lemma mk_event_spec:
  forall (f: eventval -> ident * Interface.Op.type -> event) vs xts,
    OpAux.wt_vals vs xts ->
    mask f vs xts (Traces.mk_event (fun v => f (Traces.eventval_of_val v)) vs xts).
Proof.
intros ** Hwt. generalize dependent xts.
induction vs as [|v vs IHvs];
  intros xts Hwt; destruct xts as [|[x t] xts];
  inv Hwt; try constructor.
rewrite Traces.mk_event_cons.
apply MaskCons with (evtval := Traces.eventval_of_val v); eauto.
admit.
Qed.

Definition mask_load :=
  mask (fun ev xt => Event_vload (Interface.Op.type_chunk (snd xt))
                               (glob_id (fst xt))
                               Integers.Int.zero ev).

Definition mask_store :=
  mask (fun ev xt => Event_vstore (Interface.Op.type_chunk (snd xt))
                                (glob_id (fst xt))
                                Integers.Int.zero ev).

CoInductive bisim_io': nat -> traceinf -> Prop
  := Step: forall n node t t' T,
      find_node main G = Some node ->
      mask_load (map Interface.Op.sem_const (ins n)) node.(n_in) t ->
      mask_store (map Interface.Op.sem_const (outs n)) node.(n_out) t' ->
      bisim_io' (S n) T ->
      bisim_io' n (t *** t' *** T).

Definition bisim_io := bisim_io' 0.

End Bisim.


Lemma soundness:
  forall G P main ins outs,
    DF.WeF.Welldef_global G ->
    DF.Typ.wt_global G ->
    wt_ins G main ins ->
    wt_outs G main outs ->
    let xss := fun n => List.map (fun c => DF.Str.present (Interface.Op.sem_const c)) (ins n) in
    let yss := fun n => List.map (fun c => DF.Str.present (Interface.Op.sem_const c)) (outs n) in
    DF.Sem.sem_node G main xss yss ->
    compile G main = OK P ->
    (* XXX: we may want to use determinacy to strengthen this
    conclusion: *all* traces are bisim_io *)
    exists T, bigstep_program_diverges function_entry2 P T
         /\ bisim_io G main ins outs T.
Proof.
  intros ** Comp.
  edestruct dostep'_correct as (me0 & Heval & Step); eauto.
  unfold compile in Comp.
  destruct (List.fold_left is_well_sch G (OK tt)); try discriminate; simpl in Comp.
  pose proof Comp.
  unfold Translation.translate in Comp.
  destruct (find_class main (translate G)) as [(c_main, prog_main)|] eqn: Emain; try discriminate.
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
    with (me0:=me0) (Step_in_spec:=Step_in_spec) (Step_out_spec:=Step_out_spec)
                    (Hwt_in:=Hwt_in) (Hwt_out:=Hwt_out); eauto.
    + apply translate_wt; auto.
    + admit.
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