From compcert Require Import common.Errors.
From compcert Require Import common.Events.
From compcert Require Import common.Behaviors.
From compcert Require Import common.Determinism.
From compcert Require Import cfrontend.Clight.
From compcert Require Import cfrontend.ClightBigstep.
From compcert Require Import lib.Integers.
From compcert Require Import driver.Compiler.

From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import CoindStreams.
From Velus Require Import ObcToClight.Generation.
From Velus Require Import ClightToAsm.
From Velus Require Import ObcToClight.Correctness.
From Velus Require Import ObcToClight.Interface.
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

From Velus Require Import Traces.
From Velus Require Import VelusWorld.

From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Permutation.

Open Scope error_monad_scope.
Open Scope stream_scope.

Import Common.

Section WtStream.
  Context {PSyn : list decl -> block -> Prop} {prefs : PS.t}.

  Variable G: @global PSyn prefs.
  Variable main: ident.
  Variable ins: list (Stream value).
  Variable outs: list (Stream value).

  Definition wt_ins :=
    forall node,
      find_node main G = Some node ->
      NLCorrectness.wt_streams ins (idfst (idfst node.(n_in))).

  Definition wt_outs :=
    forall node,
      find_node main G = Some node ->
      NLCorrectness.wt_streams outs (idfst (idfst (idfst node.(n_out)))).

End WtStream.

Definition wc_ins {PSyn prefs} (G: @global PSyn prefs) main ins := sem_clock_inputs G main ins.

(** A bisimulation relation between a declared node's trace and a given trace *)
Inductive bisim_IO {PSyn prefs} (G: @global PSyn prefs) (f: ident) (ins outs: list (Stream value)): traceinf -> Prop :=
  IOStep:
    forall T node
      (Len_ins     : Datatypes.length ins = Datatypes.length node.(n_in))
      (Len_outs    : Datatypes.length outs = Datatypes.length node.(n_out)),
      find_node f G = Some node ->
      traceinf_sim T (trace_node node ins outs Len_ins Len_outs 0) ->
      bisim_IO G f ins outs T.

Local Hint Resolve
      wc_global_Ordered_nodes
      complete_global_wt complete_global_wc
      auto_global_wt auto_global_wc
      switch_global_wt switch_global_wc
      inlinelocal_global_wt inlinelocal_global_wc inlinelocal_global_sem
      unnest_global_wt unnest_global_wc unnest_global_sem
      normlast_global_wt normlast_global_wc normlast_global_sem
      normfby_global_wt normfby_global_wc normfby_global_sem
      check_causality_correct : core.

Local Ltac unfold_l_to_nl Hltonl :=
  unfold l_to_nl in Hltonl; simpl in Hltonl;
  repeat rewrite print_identity in Hltonl;
  destruct (is_causal _) eqn:Hcaus; simpl in Hltonl; [|inv Hltonl];
  repeat rewrite print_identity in Hltonl;
  Errors.monadInv Hcaus.

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
  eapply TR.Correctness.sem_l_nl in Hltonl; eauto 14 with ltyping.
  eapply normfby_global_sem, normlast_global_sem, unnest_global_sem, inlinelocal_global_sem, switch_global_sem, auto_global_sem; eauto 7.
  eapply sem_node_sem_node_ck; eauto using complete_global_sem with ltyping.
  - eapply check_causality_correct; eauto using complete_global_wt with ltyping.
  - edestruct Hwcins as (?&?&Find&?&?).
    repeat esplit.
    + unfold find_node in *. inv_equalities.
      apply CommonProgram.find_unit_transform_units_forward in Hf.
      setoid_rewrite Hf. simpl. eauto.
    + simpl; eauto.
    + simpl; eauto.
Qed.

Fact l_to_nl_find_node' : forall G G' f n',
    NL.Syn.find_node f G' = Some n' ->
    l_to_nl G = OK G' ->
    exists n, find_node f G = Some n /\
         NL.Syn.n_in n' = idfst (n_in n) /\ NL.Syn.n_out n' = idfst (idfst (n_out n)).
Proof.
  intros G * Hfind Hltonl.
  unfold_l_to_nl Hltonl.
  eapply TR.Tr.find_node_global' in Hfind as (n''&Hfind&Htonode); eauto.
  eapply global_iface_eq_find in Hfind as (n&Hfind&(_&_&Hin&Hout)); eauto.
  2:{ eapply global_iface_eq_sym.
      eapply global_iface_eq_trans, normfby_global_eq.
      eapply global_iface_eq_trans, normlast_global_iface_eq.
      eapply global_iface_eq_trans, unnest_global_eq.
      eapply global_iface_eq_trans, inlinelocal_global_iface_eq.
      eapply global_iface_eq_trans, switch_global_iface_eq. apply global_iface_eq_refl. }
  apply auto_global_find_node' in Hfind as (?&Hfind&(_&_&Hin'&Hout')).
  eapply global_iface_eq_find in Hfind as (?&Hfind&(_&_&Hin''&Hout'')); eauto.
  2:{ apply global_iface_eq_sym.
      apply complete_global_iface_eq. }
  do 2 esplit; eauto; split.
  - eapply TR.Tr.to_node_in in Htonode; eauto.
    unfold idfst. erewrite map_ext, <-Hin'', <-Hin', <-Hin, map_ext. symmetry; apply Htonode.
    1,2:intros; destruct_conjs; auto.
  - eapply TR.Tr.to_node_out in Htonode; eauto.
    unfold idfst. erewrite map_map, map_ext, <-Hout'', <-Hout', <-Hout, map_ext, <-map_map. symmetry; apply Htonode.
    1,2:intros; destruct_conjs; auto.
Qed.

(** Simply link the trace of a Lustre node with the trace of an NLustre node with the same parameters *)
Lemma trace_inf_sim_node {PSyn} {prefs}:
  forall (node: @node PSyn prefs) ins outs
    (Len_ins: Datatypes.length ins = Datatypes.length node.(n_in))
    (Len_outs: Datatypes.length outs = Datatypes.length node.(n_out))
    n n' Spec_in_out_n' Len_ins_n' Len_outs_n',
    idfst (NL.Syn.n_in n') = idfst (idfst (n_in node)) ->
    idfst (NL.Syn.n_out n') = idfst (idfst (idfst (n_out node))) ->
    traceinf_sim (NLCorrectness.trace_node n' ins outs Spec_in_out_n' Len_ins_n' Len_outs_n' n)
      (trace_node node ins outs Len_ins Len_outs n).
Proof.
  intros; unfold NLCorrectness.trace_node, trace_node.
  rename node0 into node.
  apply traceinf_sim'_sim.
  revert n; cofix COFIX; intro.
  rewrite unfold_mk_trace.
  rewrite unfold_mk_trace with (xs := idfst (idfst (n_in node))).
  simpl.
  replace (load_events (tr_Streams ins n) (idfst (idfst (n_in node))) ** store_events (tr_Streams outs n) (idfst (idfst (idfst (n_out node)))))
    with (load_events (tr_Streams ins n) (idfst (NL.Syn.n_in n')) ** store_events (tr_Streams outs n) (idfst (NL.Syn.n_out n')));
    try congruence.
  constructor.
  - intro E; eapply Eapp_E0_inv in E.
    assert (forall n, length (tr_Streams ins n) = length (idfst (NL.Syn.n_in n'))) as Len_ins_2.
    { intros. unfold tr_Streams. rewrite map_length, length_idfst; auto. }
    assert (forall n, length (tr_Streams outs n) = length (idfst (NL.Syn.n_out n'))) as Len_outs_2.
    { intros. unfold tr_Streams. rewrite map_length, length_idfst; auto. }
    assert (idfst (NL.Syn.n_in n') <> [] \/ idfst (NL.Syn.n_out n') <> []) as Spec_in_out_2.
    { clear - Spec_in_out_n'.
      destruct Spec_in_out_n'; [left|right].
      1,2:intro contra; eapply H, map_eq_nil; eauto. }
    pose proof (load_store_events_not_E0 _ _ _ _ Spec_in_out_2 Len_ins_2 Len_outs_2 n).
    intuition.
  - apply COFIX.
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
    lustre_to_asm (Some main) G = OK P ->
    wt_ins G main ins ->
    wc_ins G main (pStr ins) ->
    Sem.sem_node G main (pStr ins) (pStr outs) ->
    exists T, program_behaves (Asm.semantics P) (Reacts T)
         /\ bisim_IO G main ins outs T.
Proof.
  intros * Elab Comp Hwti Hwci Hsem.
  unfold lustre_to_asm, print in Comp. simpl in Comp.
  destruct (l_to_nl G) as [G'|] eqn: Comp'; simpl in Comp; try discriminate.
  destruct Gp as (Hwc&Hwt).
  eapply behavior_nl_to_asm with (ins:=ins) (outs:=outs) in Comp as (T&Hbeh&Hbisim).
  - exists T. split; auto.
    inv Hbisim.
    eapply l_to_nl_find_node' in Comp' as (?&Hfind'&Hin&Hout); eauto.
    assert (n_in x <> []) as Hnnul.
    { specialize (n_ingt0 x) as Hlt.
      intro contra. rewrite contra in Hlt; simpl in Hlt. lia. }
    assert (Datatypes.length ins = Datatypes.length (n_in x)) as Hlenin
        by (rewrite <-length_idfst; congruence).
    assert (Datatypes.length outs = Datatypes.length (n_out x)) as Hlenout
        by (now rewrite Len_outs, Hout, 2 length_idfst).
    eapply IOStep with (Len_ins:=Hlenin) (Len_outs:=Hlenout); eauto.
    eapply traceinf_sim_trans; eauto.
    eapply trace_inf_sim_node.
    1,2:f_equal; auto.
  - clear - Hwc Hwt Comp'. unfold_l_to_nl Comp'.
    eapply TR.Clocking.wc_transcription in Comp'; eauto 8.
  - clear - Hwc Hwt Comp'. unfold_l_to_nl Comp'.
    eapply TR.Typing.wt_transcription in Comp'; eauto 8.
  - clear - Hwti Comp'.
    intros ? Hfind.
    eapply l_to_nl_find_node' in Comp' as (?&Hfind'&Hin&_); eauto.
    eapply Hwti in Hfind'. rewrite Hin. eauto.
  - clear - Hwt Comp'. unfold_l_to_nl Comp'.
    eapply TR.NormalArgs.to_global_normal_args in Comp'; eauto.
    eapply normfby_global_normal_args, normlast_global_normal_args, unnest_global_normal_args; eauto 7 with lclocking.
  - eapply behavior_l_to_nl in Comp'; eauto.
Qed.

Corollary behavior_asm_trace_node:
  forall D G Gp P main ins outs,
    elab_declarations D = OK (exist _ G Gp) ->
    lustre_to_asm (Some main) G = OK P ->
    wt_ins G main ins ->
    wc_ins G main (pStr ins) ->
    Sem.sem_node G main (pStr ins) (pStr outs) ->
    exists node Len_ins Len_outs,
      find_node main G = Some node
      /\ program_behaves (Asm.semantics P)
          (Reacts (trace_node node ins outs Len_ins Len_outs 0)).
Proof.
  intros * EL LA WT WC SEM.
  apply behavior_asm with (1:=EL) (2:=LA) (3:=WT) (4:=WC) in SEM as (T & SEM & BIS).
  inv BIS.
  exists node0; exists Len_ins; exists Len_outs.
  split; auto.
  eapply CompCertLib.traceinf_sim_program_behaves in SEM; eauto.
Qed.

Corollary behavior_asm_velus_world_trace_node_and_nothing_else:
  forall D G Gp P main ins outs,
    elab_declarations D = OK (exist _ G Gp) ->
    lustre_to_asm (Some main) G = OK P ->
    wt_ins G main ins ->
    wc_ins G main (pStr ins) ->
    Sem.sem_node G main (pStr ins) (pStr outs) ->
    exists node Len_ins Len_outs,
      find_node main G = Some node
      /\ program_behaves (world_sem (Asm.semantics P) (velus_world G main ins))
          (Reacts (trace_node node ins outs Len_ins Len_outs 0))
      /\ forall beh, program_behaves (world_sem (Asm.semantics P) (velus_world G main ins)) beh
               -> same_behaviors beh (Reacts (trace_node node ins outs Len_ins Len_outs 0)).
Proof.
  intros * EL LA WT WC SEM.
  apply behavior_asm_trace_node with (1:=EL) (2:=LA) (3:=WT) (4:=WC) in SEM
      as (node & Len_ins & Len_outs & FIND & BEH).
  exists node; exists Len_ins; exists Len_outs.
  match goal with |- _ /\ ?PB /\ _ => enough PB as BEH' end.
  repeat split; auto.
  - intros beh PB2.
    eapply asm_and_velus_world_deterministic with (1:=BEH') in PB2.
    destruct beh; inv PB2; auto.
    constructor.
    now apply traceinf_sim_sym.
  - apply velus_world_behaves; auto.
    apply Asm.semantics_determinate.
Qed.

