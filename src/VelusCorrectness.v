From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import CoindStreams.
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

From Velus Require Import Interface.
From Velus Require Import Instantiator.
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
From Velus Require Import NLCorrectness.
From Velus Require Import ObcToClight.Correctness.
From Velus Require Import Lustre.LustreElab.

From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Omega.

Open Scope error_monad_scope.
Open Scope stream_scope.

Parameter print_lustre  : global -> unit.

Definition l_to_nl (g : {G : global |
                          wt_global G /\ wc_global G /\
                          Forall (fun n => L.Syn.n_prefixes n = elab_prefs) G}) :
  res NL.Syn.global.
Proof.
  destruct g as (g&Hwt&_&Hprefs).
  eapply L.Typ.wt_global_wl_global in Hwt.
  specialize (Norm.Norm.normalize_global' (exist _ g (conj Hwt Hprefs))) as ([g'|err]&Hprefs'); simpl in *.
  - exact (TR.Tr.to_global g' Hprefs').
  - right. exact err.
Defined.

Definition compile (D: list LustreAst.declaration) (main_node: ident) : res Asm.program :=
  elab_declarations D
                    @@ print (fun g => print_lustre (proj1_sig g))
                    @@@ l_to_nl
                    @@@ nl_to_asm main_node.

Section WtStream.

  Variable G: global.
  Variable main: ident.
  Variable ins: list (Stream val).
  Variable outs: list (Stream val).

  Definition wt_ins :=
    forall node,
      find_node main G = Some node ->
      wt_streams ins (idty node.(n_in)).

  Definition wt_outs :=
    forall node,
      find_node main G = Some node ->
      wt_streams outs (idty node.(n_out)).

End WtStream.

Definition wc_ins G main ins := sem_clock_inputs G main ins.

(** The trace of a Lustre node *)
Section LTrace.

  Variable (node: node) (ins outs: list (Stream val)).

  Hypothesis Spec_in_out : node.(n_in) <> [] \/ node.(n_out) <> [].
  Hypothesis Len_ins     : Datatypes.length ins = Datatypes.length node.(n_in).
  Hypothesis Len_outs    : Datatypes.length outs = Datatypes.length node.(n_out).

  Program Definition trace_node (n: nat): traceinf :=
    traceinf_of_traceinf' (mk_trace (tr_Streams ins) (tr_Streams outs)
                                    (idty node.(n_in)) (idty node.(n_out))
                                    _ _ _ n).
  Next Obligation.
    destruct Spec_in_out.
    - left; intro E; apply map_eq_nil in E; auto.
    - right; intro E; apply map_eq_nil in E; auto.
  Qed.
  Next Obligation.
    unfold tr_Streams, idty; rewrite 2 map_length; auto.
  Qed.
  Next Obligation.
    unfold tr_Streams, idty; rewrite 2 map_length; auto.
  Qed.

  (** Simply link the trace of a Lustre node with the trace of an NLustre node with the same parameters *)
  Lemma trace_inf_sim_node:
    forall n n' Spec_in_out_n' Len_ins_n' Len_outs_n',
      idty (NL.Syn.n_in n') = idty (n_in node) ->
      idty (NL.Syn.n_out n') = idty (n_out node) ->
      traceinf_sim (NLCorrectness.trace_node n' ins outs Spec_in_out_n' Len_ins_n' Len_outs_n' n)
                   (trace_node n).
  Proof.
    intros; unfold NLCorrectness.trace_node, trace_node.
    apply traceinf_sim'_sim.
    revert n; cofix COFIX; intro.
    rewrite unfold_mk_trace.
    rewrite unfold_mk_trace with (xs := idty (n_in node)).
    simpl.
    replace (load_events (tr_Streams ins n) (idty (n_in node)) ** store_events (tr_Streams outs n) (idty (n_out node)))
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
Inductive bisim_IO (G: global) (f: ident) (ins outs: list (Stream val)): traceinf -> Prop :=
  IOStep:
    forall T node
      (Spec_in_out : node.(n_in) <> [] \/ node.(n_out) <> [])
      (Len_ins     : Datatypes.length ins = Datatypes.length node.(n_in))
      (Len_outs    : Datatypes.length outs = Datatypes.length node.(n_out)),
      find_node f G = Some node ->
      traceinf_sim T (trace_node node ins outs Spec_in_out Len_ins Len_outs 0) ->
      bisim_IO G f ins outs T.

Hint Resolve
     normalize_global_normalized_global normalized_global_unnested_global
     normalize_global_causal
     Typing.normalize_global_wt
     Clocking.normalize_global_wc
     normalize_global_sem
     normalize_global_sem_clock_inputs.

Local Ltac unfold_l_to_nl Hltonl :=
  unfold l_to_nl in Hltonl;
  destruct (normalize_global' _) as ([g'|?]&?) eqn:Hnorm; simpl in *; try congruence;
  unfold normalize_global' in Hnorm; inv Hnorm.

(** Correctness from Lustre to NLustre *)
Lemma behavior_l_to_nl:
  forall G G' main ins outs,
    sem_node (proj1_sig G) main ins outs ->
    wc_ins (proj1_sig G) main ins ->
    l_to_nl G = OK G' ->
    CoindSem.sem_node G' main ins outs.
Proof.
  intros (g&Hwt&Hwc&Hprefs) * Hsem Hwcins Hltonl.
  unfold_l_to_nl Hltonl.
  eapply TR.Correctness.sem_l_nl in Hltonl; eauto.
Qed.

Fact l_to_nl_find_node : forall G G' f n,
    find_node f (proj1_sig G) = Some n ->
    l_to_nl G = OK G' ->
    exists n', NL.Syn.find_node f G' = Some n' /\
          NL.Syn.n_in n' = n_in n /\ NL.Syn.n_out n' = n_out n.
Proof.
  intros (g&Hwt&Hwc&Hprefs) * Hfind Hltonl.
  unfold_l_to_nl Hltonl.
  eapply normalize_global_iface_eq in H0.
  eapply global_iface_eq_find in Hfind as (n'&Hfind&(_&_&Hin&Hout)); eauto.
  eapply TR.Tr.find_node_global in Hfind as (n''&?&Hfind&Htonode); eauto.
  exists n''. repeat split; auto.
  - eapply TR.Tr.to_node_in in Htonode; eauto.
    congruence.
  - eapply TR.Tr.to_node_out in Htonode; eauto.
    congruence.
Qed.

Fact l_to_nl_find_node' : forall G G' f n',
    NL.Syn.find_node f G' = Some n' ->
    l_to_nl G = OK G' ->
    exists n, find_node f (proj1_sig G) = Some n /\
         NL.Syn.n_in n' = n_in n /\ NL.Syn.n_out n' = n_out n.
Proof.
  intros (g&Hwt&Hwc&Hprefs) * Hfind Hltonl.
  unfold_l_to_nl Hltonl.
  eapply normalize_global_iface_eq in H0. symmetry in H0.
  eapply TR.Tr.find_node_global' in Hfind as (n''&?&Hfind&Htonode); eauto.
  eapply global_iface_eq_find in Hfind as (n&Hfind&(_&_&Hin&Hout)); eauto.
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
    sem_node G main (pStr ins) (pStr outs) ->
    compile D main = OK P ->
    exists T, program_behaves (Asm.semantics P) (Reacts T)
         /\ bisim_IO G main ins outs T.
Proof.
  intros * Elab Hwti Hwci Hsem Comp.
  unfold compile, print in Comp.
  rewrite Elab in Comp. simpl in Comp.
  replace (match Gp with | _ => _ end) with (l_to_nl (exist _ G Gp)) in Comp; auto.
  destruct (l_to_nl (exist _ G Gp)) as [G'|] eqn: Comp'; simpl in Comp; try discriminate.
  destruct (nl_to_asm main G') as [p|] eqn: Comp''; inv Comp.
  destruct Gp as (Hwc&Hwt&Hprefs).
  eapply behavior_nl_to_asm with (ins:=ins) (outs:=outs) in Comp'' as (T&Hbeh&Hbisim).
  - exists T. split; auto.
    inv Hbisim.
    eapply l_to_nl_find_node' in Comp' as (?&Hfind'&Hin&Hout); eauto.
    assert (n_in x <> []) as Hnnul.
    { specialize (n_ingt0 x) as Hlt.
      intro contra. rewrite contra in Hlt; simpl in Hlt.
      eapply Lt.lt_irrefl; eauto. }
    assert (Datatypes.length ins = Datatypes.length (n_in x)) as Hlenin by congruence.
    assert (Datatypes.length outs = Datatypes.length (n_out x)) as Hlenout by congruence.
    eapply IOStep with (Spec_in_out:=or_introl Hnnul)
                       (Len_ins:=Hlenin) (Len_outs:=Hlenout); eauto.
    eapply traceinf_sim_trans; eauto.
    eapply trace_inf_sim_node.
    1,2:f_equal; auto.
  - clear - Comp'. unfold_l_to_nl Comp'.
    eapply TR.Clocking.wc_transcription in Comp'; eauto.
  - clear - Comp'. unfold_l_to_nl Comp'.
    eapply TR.Typing.wt_transcription in Comp'; eauto.
  - clear - Hwti Comp'.
    intros ? Hfind.
    eapply l_to_nl_find_node' in Comp' as (?&Hfind'&Hin&_); eauto.
    eapply Hwti in Hfind'. rewrite Hin. eauto.
  - clear - Comp'. unfold_l_to_nl Comp'.
    eapply TR.NormalArgs.to_global_normal_args in Comp'; eauto.
  - eapply behavior_l_to_nl in Comp'; eauto.
Qed.
