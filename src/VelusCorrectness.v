From compcert Require Import common.Errors.
From compcert Require Import common.Events.
From compcert Require Import common.Behaviors.
From compcert Require Import cfrontend.Clight.
From compcert Require Import cfrontend.ClightBigstep.
From compcert Require Import lib.Integers.
From compcert Require Import driver.Compiler.

From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import CoindStreams.
From Velus Require Import ObcToClight.Generation.
From Velus Require Import Traces.
From Velus Require Import ClightToAsm.
From Velus Require Import ObcToClight.Correctness.
From Velus Require Import Interface.
From Velus Require Import Instantiator.
From Velus Require Import Lustre.LustreElab.
From Velus Require Import Velus.
From Velus Require Import NLCorrectness.
Import Stc.Syn.
Import NL.
Import L.
Import Obc.Syn.
Import Obc.Sem.
Import Obc.Typ.
Import Obc.Equ.
Import Obc.Def.
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

Section WtStream.
  Context {PSyn : block -> Prop} {prefs : PS.t}.

  Variable G: @global PSyn prefs.
  Variable main: ident.
  Variable ins: list (Stream value).
  Variable outs: list (Stream value).

  Definition wt_ins :=
    forall node,
      find_node main G = Some node ->
      NLCorrectness.wt_streams ins (idty (idty node.(n_in))).

  Definition wt_outs :=
    forall node,
      find_node main G = Some node ->
      NLCorrectness.wt_streams outs (idty (idty node.(n_out))).

End WtStream.

Definition wc_ins {PSyn prefs} (G: @global PSyn prefs) main ins := sem_clock_inputs G main ins.

(** The trace of a Lustre node *)
Section LTrace.
  Context {PSyn : block -> Prop} {prefs : PS.t}.

  Variable (node: @node PSyn prefs) (ins outs: list (Stream value)).

  Hypothesis Spec_in_out : node.(n_in) <> [] \/ node.(n_out) <> [].
  Hypothesis Len_ins     : Datatypes.length ins = Datatypes.length node.(n_in).
  Hypothesis Len_outs    : Datatypes.length outs = Datatypes.length node.(n_out).

  Program Definition trace_node (n: nat): traceinf :=
    mk_trace (tr_Streams ins) (tr_Streams outs)
             (idty (idty node.(n_in))) (idty (idty node.(n_out)))
             _ _ _ n.
  Next Obligation.
    destruct Spec_in_out.
    - left; intro E; apply map_eq_nil, map_eq_nil in E; auto.
    - right; intro E; apply map_eq_nil, map_eq_nil in E; auto.
  Qed.
  Next Obligation.
    unfold tr_Streams, idty; rewrite 3 map_length; auto.
  Qed.
  Next Obligation.
    unfold tr_Streams, idty; rewrite 3 map_length; auto.
  Qed.

  (** Simply link the trace of a Lustre node with the trace of an NLustre node with the same parameters *)
  Lemma trace_inf_sim_node:
    forall n n' Spec_in_out_n' Len_ins_n' Len_outs_n',
      idty (NL.Syn.n_in n') = idty (idty (n_in node)) ->
      idty (NL.Syn.n_out n') = idty (idty (n_out node)) ->
      traceinf_sim (NLCorrectness.trace_node n' ins outs Spec_in_out_n' Len_ins_n' Len_outs_n' n)
                   (trace_node n).
  Proof.
    intros; unfold NLCorrectness.trace_node, trace_node.
    apply traceinf_sim'_sim.
    revert n; cofix COFIX; intro.
    rewrite unfold_mk_trace.
    rewrite unfold_mk_trace with (xs := idty (idty (n_in node))).
    simpl.
    replace (load_events (tr_Streams ins n) (idty (idty (n_in node))) ** store_events (tr_Streams outs n) (idty (idty (n_out node))))
      with (load_events (tr_Streams ins n) (idty (NL.Syn.n_in n')) ** store_events (tr_Streams outs n) (idty (NL.Syn.n_out n')));
      try congruence.
    constructor.
    - intro E; eapply Eapp_E0_inv in E.
      assert (forall n, length (tr_Streams ins n) = length (idty (NL.Syn.n_in n'))) as Len_ins_2.
      { intros. unfold tr_Streams. rewrite map_length, length_idty; auto. }
      assert (forall n, length (tr_Streams outs n) = length (idty (NL.Syn.n_out n'))) as Len_outs_2.
      { intros. unfold tr_Streams. rewrite map_length, length_idty; auto. }
      assert (idty (NL.Syn.n_in n') <> [] \/ idty (NL.Syn.n_out n') <> []) as Spec_in_out_2.
      { clear - Spec_in_out_n'.
        destruct Spec_in_out_n'; [left|right].
        1,2:intro contra; eapply H, map_eq_nil; eauto. }
      pose proof (load_store_events_not_E0 _ _ _ _ Spec_in_out_2 Len_ins_2 Len_outs_2 n).
      intuition.
    - apply COFIX.
  Qed.

End LTrace.

(** A bisimulation relation between a declared node's trace and a given trace *)
Inductive bisim_IO {PSyn prefs} (G: @global PSyn prefs) (f: ident) (ins outs: list (Stream value)): traceinf -> Prop :=
  IOStep:
    forall T node
      (Spec_in_out : node.(n_in) <> [] \/ node.(n_out) <> [])
      (Len_ins     : Datatypes.length ins = Datatypes.length node.(n_in))
      (Len_outs    : Datatypes.length outs = Datatypes.length node.(n_out)),
      find_node f G = Some node ->
      traceinf_sim T (trace_node node ins outs Spec_in_out Len_ins Len_outs 0) ->
      bisim_IO G f ins outs T.

Local Hint Resolve
      wc_global_Ordered_nodes
      switch_global_wt switch_global_wc
      inlinelocal_global_wt inlinelocal_global_wc inlinelocal_global_sem
      normalize_global_normalized_global normalized_global_unnested_global
      Typing.normalize_global_wt
      Clocking.normalize_global_wc
      normalize_global_sem
      check_causality_correct : core.

Local Ltac unfold_l_to_nl Hltonl :=
  unfold l_to_nl in Hltonl; simpl in Hltonl;
  repeat rewrite print_identity in Hltonl;
  destruct (is_causal _) eqn:Hcaus; simpl in Hltonl; [|inv Hltonl];
  repeat rewrite print_identity in Hltonl;
  monadInv Hcaus.

(** Correctness from Lustre to NLustre *)
Lemma behavior_l_to_nl:
  forall G G' main ins outs,
    wt_global G ->
    wc_global G ->
    Sem.sem_node G main ins outs ->
    wc_ins G main ins ->
    l_to_nl G = OK G' ->
    CoindSem.sem_node G' main ins outs.
Proof.
  intros G * Hwt Hwc Hsem Hwcins Hltonl.
  unfold_l_to_nl Hltonl.
  eapply TR.Correctness.sem_l_nl in Hltonl; eauto with ltyping lclocking.
  eapply normalize_global_sem, inlinelocal_global_sem, switch_global_sem; eauto.
  eapply sem_node_sem_node_ck; eauto with ltyping.
Qed.

Fact l_to_nl_find_node : forall G G' f n,
    find_node f G = Some n ->
    l_to_nl G = OK G' ->
    exists n', NL.Syn.find_node f G' = Some n' /\
          NL.Syn.n_in n' = idty (n_in n) /\ NL.Syn.n_out n' = idty (n_out n).
Proof.
  intros g * Hfind Hltonl.
  unfold_l_to_nl Hltonl.
  eapply global_iface_eq_find in Hfind as (n'&Hfind&(_&_&Hin&Hout)); eauto.
  2:{ eapply global_iface_eq_trans, global_iface_eq_trans.
      eapply switch_global_iface_eq. eapply inlinelocal_global_iface_eq. eapply normalize_global_iface_eq. }
  eapply TR.Tr.find_node_global in Hfind as (n''&Hfind&Htonode); eauto.
  exists n''. repeat split; auto.
  - eapply TR.Tr.to_node_in in Htonode; eauto.
    congruence.
  - eapply TR.Tr.to_node_out in Htonode; eauto.
    congruence.
Qed.

Fact l_to_nl_find_node' : forall G G' f n',
    NL.Syn.find_node f G' = Some n' ->
    l_to_nl G = OK G' ->
    exists n, find_node f G = Some n /\
         NL.Syn.n_in n' = idty (n_in n) /\ NL.Syn.n_out n' = idty (n_out n).
Proof.
  intros G * Hfind Hltonl.
  unfold_l_to_nl Hltonl.
  eapply TR.Tr.find_node_global' in Hfind as (n''&Hfind&Htonode); eauto.
  eapply global_iface_eq_find in Hfind as (n&Hfind&(_&_&Hin&Hout)); eauto.
  2:{ eapply global_iface_eq_sym, global_iface_eq_trans, global_iface_eq_trans.
      eapply switch_global_iface_eq. eapply inlinelocal_global_iface_eq. eapply normalize_global_iface_eq. }
  exists n. repeat split; auto.
  - eapply TR.Tr.to_node_in in Htonode; eauto.
    congruence.
  - eapply TR.Tr.to_node_out in Htonode; eauto.
    congruence.
Qed.

(** The ultimate lemma states that, if
    - the parsed declarations [D] elaborate to a dataflow program [G] and
      a proof [Gp] that it satisfies [wt_global G] and [wc_global G],
    - the values on input streams [ins] are well-typed according to the
      interface of the [main] node,
    - the inputs of the [main] node are all on the base clock
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
    wc_ins G main (pStr ins) ->
    Sem.sem_node G main (pStr ins) (pStr outs) ->
    compile D main = OK P ->
    exists T, program_behaves (Asm.semantics P) (Reacts T)
         /\ bisim_IO G main ins outs T.
Proof.
  intros * Elab Hwti Hwci Hsem Comp.
  unfold compile, print in Comp.
  rewrite Elab in Comp. simpl in Comp.
  destruct (l_to_nl G) as [G'|] eqn: Comp'; simpl in Comp; try discriminate.
  destruct (nl_to_asm main G') as [p|] eqn: Comp''; inv Comp.
  destruct Gp as (Hwc&Hwt).
  eapply behavior_nl_to_asm with (ins:=ins) (outs:=outs) in Comp'' as (T&Hbeh&Hbisim).
  - exists T. split; auto.
    inv Hbisim.
    eapply l_to_nl_find_node' in Comp' as (?&Hfind'&Hin&Hout); eauto.
    assert (n_in x <> []) as Hnnul.
    { specialize (n_ingt0 x) as Hlt.
      intro contra. rewrite contra in Hlt; simpl in Hlt.
      eapply Lt.lt_irrefl; eauto. }
    assert (Datatypes.length ins = Datatypes.length (n_in x)) as Hlenin
        by (rewrite <-length_idty; congruence).
    assert (Datatypes.length outs = Datatypes.length (n_out x)) as Hlenout
        by (rewrite <-length_idty; congruence).
    eapply IOStep with (Spec_in_out0:=or_introl Hnnul)
                       (Len_ins0:=Hlenin) (Len_outs0:=Hlenout); eauto.
    eapply traceinf_sim_trans; eauto.
    eapply trace_inf_sim_node.
    1,2:f_equal; auto.
  - clear - Hwc Hwt Comp'. unfold_l_to_nl Comp'.
    eapply TR.Clocking.wc_transcription in Comp'; eauto.
  - clear - Hwc Hwt Comp'. unfold_l_to_nl Comp'.
    eapply TR.Typing.wt_transcription in Comp'; eauto.
  - clear - Hwti Comp'.
    intros ? Hfind.
    eapply l_to_nl_find_node' in Comp' as (?&Hfind'&Hin&_); eauto.
    eapply Hwti in Hfind'. rewrite Hin. eauto.
  - clear - Hwt Comp'. unfold_l_to_nl Comp'.
    eapply TR.NormalArgs.to_global_normal_args in Comp'; eauto with lclocking.
  - eapply behavior_l_to_nl in Comp'; eauto.
Qed.
