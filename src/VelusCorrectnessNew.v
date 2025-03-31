From compcert Require Import common.Errors.
From compcert Require Import common.Behaviors.
From compcert Require Import driver.Compiler.

From Velus Require Import Common.
From Velus Require Import Ident.
From Velus Require Import CoindStreams.
From Velus Require Import ObcToClight.Interface.
From Velus Require Import Instantiator.
From Velus Require Import Lustre.LustreElab.
From Velus Require Import Velus.
From Velus Require Import NLCorrectness.
From Velus Require Import Traces.
From Velus Require Import VelusWorld.
From Velus Require Import VelusCorrectness.
From Velus Require Import Cpo_def Nprod Cpo_streams_type CommonDS.

From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Permutation.

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

Open Scope error_monad_scope.
Open Scope stream_scope.

Import Common.
Import Restr Den.SdR Den.Sd SDfuns Den.Safe DS_ext.
Import DS_ext.
Import Den.OpErr.
Import Cpo.
Import Cpo_ext.Nprod.
Import Den.SdR.
Import Den.Inf.

(** * The new correctness statements thanks to the denotational semantics *)


(* TODO: move? *)
Lemma HasType_In :
  forall l x ty,
    HasType (senv_of_ins l) x ty ->
    In (x,ty) (idfst (idfst l)).
Proof.
  intros * HH; inv HH.
  unfold senv_of_ins, idfst in *.
  solve_In.
Qed.
(* TODO: move? *)
Lemma HasClock_In :
  forall l x ck,
    HasClock (senv_of_ins l) x ck ->
    In (x,ck) (List.map (fun '(x, (_, ck, _)) => (x, ck)) l).
Proof.
  intros * HH; inv HH.
  unfold senv_of_ins in *.
  solve_In.
Qed.

(* TODO: move? *)
Lemma SForall_map :
  forall A B P (f:A->B) xs,
    SForall (fun x => P (f x)) xs <-> SForall P (Streams.map f xs).
Proof.
  intros.
  rewrite 2 SForall_forall.
  setoid_rewrite Str_nth_map.
  tauto.
Qed.


(** conversion from Coq Stream to nprod DS *)
Section Streams_conversion.

Definition sampl_of_svalue :=
  fun (sv:svalue) => match sv with
         | present v => pres v
         | absent => abs
         end.

Lemma s_vs :
  forall s Inf, S_of_DSv (DS_of_S (Streams.map sampl_of_svalue s)) Inf ≡ s.
Proof.
  intros.
  remember_st (S_of_DSv (DS_of_S (Streams.map sampl_of_svalue s)) Inf) as t.
  revert_all.
  cofix Cof; intros.
  constructor; simpl.
  - rewrite <- Ht.
    destruct s.
    edestruct (S_of_DSv_eq _ Inf) as (Inf2 & ->).
    rewrite map_Cons; simpl.
    replace (DS_of_S _) with
      (cons (sampl_of_svalue s) (DS_of_S (Streams.map sampl_of_svalue s0))).
    2:{ rewrite DS_inv; auto. }
    reflexivity.
    unfold S_of_DSv.
    rewrite S_of_DS_cons. simpl.
    destruct s; auto.
  - destruct s; simpl.
    eapply Cof.
    Unshelve. 2: apply DS_of_S_inf.
    rewrite <- Ht.
    edestruct (S_of_DSv_eq _ Inf) as (Inf2 & ->).
    rewrite map_Cons; simpl.
    replace (DS_of_S _) with
      (cons (sampl_of_svalue s) (DS_of_S (Streams.map sampl_of_svalue s0))).
    2:{ rewrite DS_inv; auto. }
    reflexivity.
    unfold S_of_DSv.
    rewrite S_of_DS_cons. simpl.
    apply _S_of_DS_eq; auto.
Qed.

Fixpoint nprod_of_Ss (l : list (Stream svalue)) : @nprod (DS (sampl value)) (length l) :=
  match l with
  | [] => 0
  | s :: tl => nprod_cons (DS_of_S (Streams.map sampl_of_svalue s))
                (nprod_of_Ss tl)
  end.

Lemma nth_nprod_of_Ss :
  forall xs k d d',
    k < length xs ->
    get_nth k d (nprod_of_Ss xs) = DS_of_S (Streams.map sampl_of_svalue (nth k xs d')).
Proof.
  induction xs as [|? []]; intros * Hl. inv Hl.
  destruct k; simpl in *; try lia; auto.
  destruct k.
  - setoid_rewrite nprod_hd_cons; auto.
  - simpl in *.
    rewrite <- (IHxs _ d); auto with arith.
Qed.

Lemma Ss_of_nprod_of_Ss :
  forall xs Infxs,
    EqSts (Ss_of_nprod (nprod_of_Ss xs) Infxs) xs.
Proof.
  induction xs as [|? []]; intros.
  - constructor.
  - constructor; auto.
    cbn.
    now rewrite s_vs.
  - constructor. 2: apply IHxs.
    cbn.
    now rewrite s_vs.
Qed.

Lemma nprod_of_Ss_inf :
  forall xs, forall_nprod (@infinite _) (nprod_of_Ss xs).
Proof.
  induction xs as [|? []]; intros.
  - constructor.
  - apply DS_of_S_inf.
  - constructor.
    apply DS_of_S_inf.
    apply IHxs.
Qed.

Lemma DSForall_DS_of_S :
  forall A (P:A-> Prop) s,
    SForall P s ->
    DSForall P (DS_of_S s).
Proof.
  cofix Cof; intros.
  destruct s; inv H.
  rewrite DS_inv; constructor; eauto.
Qed.

End Streams_conversion.

(** Properties of streams with only present values *)
Section PSTR.

Lemma pStr_EqSts :
  forall ss1 ss2,
    EqSts (pStr ss1) (pStr ss2)->
    EqSts ss1 ss2.
Proof.
  unfold EqSts, pStr.
  intros * H.
  rewrite Forall2_map_1, Forall2_map_2 in H.
  eapply Forall2_impl_In, H; simpl; intros; eauto.
  apply ntheq_eqst; intro n.
  eapply (eqst_ntheq n) in H2.
  rewrite 2 Str_nth_map in H2.
  now injection H2.
Qed.

Definition all_pres : Stream svalue -> Prop :=
  SForall (fun v => match v with absent => False | present _ => True end).

Lemma all_pres_pStr :
  forall xs, Forall all_pres (pStr xs).
Proof.
  induction xs; constructor; auto.
  unfold all_pres.
  rewrite SForall_forall; intro.
  now rewrite Str_nth_map.
Qed.

Lemma clocks_of_pres :
  forall xs,
    xs <> [] ->
    Forall all_pres xs ->
    clocks_of xs ≡ Streams.const true.
Proof.
  destruct xs; simpl; try congruence.
  intros * ? Hf.
  inv Hf.
  simpl.
  rewrite clocks_of_cons.
  apply ntheq_eqst; intro.
  rewrite Str_nth_zipWith, const_nth, ac_nth.
  unfold all_pres, abstract_clock in *.
  rewrite SForall_forall in H2.
  specialize (H2 n).
  cases.
Qed.

Lemma ac_all_pres :
  forall x, abstract_clock x ≡ Streams.const true <-> all_pres x.
Proof.
  unfold all_pres.
  intro.
  rewrite SForall_forall.
  split.
  - intros H n.
    apply (eqst_ntheq n) in H.
    rewrite const_nth, ac_nth in H.
    cases.
  - intros H.
    apply ntheq_eqst; intro n.
    specialize (H n).
    rewrite const_nth, ac_nth.
    cases.
Qed.

Lemma all_pres_pStr1 :
  forall xs, all_pres xs -> exists ys, xs ≡ Streams.map present ys.
Proof.
  unfold all_pres.
  intros xs Hf.
  exists (Streams.map (fun v => match v with absent => Vscalar Values.Vundef | present v => v end) xs).
  rewrite SForall_forall in Hf.
  apply ntheq_eqst; intro n.
  specialize (Hf n).
  rewrite 2 Str_nth_map.
  unfold svalue.
  cases.
Qed.

Lemma pStr_all_pres :
  forall xs,
    Forall all_pres xs ->
    exists rs, EqSts xs (pStr rs).
Proof.
  induction xs; intros * Hf.
  exists []; constructor.
  inv Hf.
  destruct IHxs as (rs & Heq); auto.
  destruct (all_pres_pStr1 _ H1) as (ys & ?).
  exists (ys :: rs).
  constructor; auto.
Qed.

End PSTR.


(** Correspondance of definitions of valid inputs in the two models.
    It could probably work with sampled inputs too. *)
Lemma wt_wc_wf_inputs :
  forall {PSyn Prefs} (G : @global PSyn Prefs),
  forall main n ins,
    find_node main G = Some n ->
    Forall (fun '(_, (_, ck, _)) => ck = Cks.Cbase) (n_in n) ->
    wt_ins G main ins ->
    wc_ins G main (pStr ins) ->
    wf_inputs n (nprod_of_Ss (pStr ins)).
Proof.
  intros * Hfind Hbase Hwt Hwc.
  destruct Hwc as (H & n' &?& Hf1 & Hf2).
  rewrite Hfind in *.
  take (Some _ = Some _) and inv it.
  assert (Hl : length (pStr ins) = length (n_in n')).
  { apply Forall2_length in Hf2.
    unfold pStr in *.
    repeat rewrite length_map in *; auto. }
  split; auto.
  apply Hwt in Hfind as Hwti.
  unfold NLCorrectness.wt_streams in Hwti.
  intros x ty ck Hty Hck s; subst s.
  unfold denot_var.
  destruct (mem_ident x _) eqn:Hin.
  2:{  (* if x is not an input, it is ok *)
    repeat split; try apply DSForall_bot.
    unfold cl_DS. unfold AC. rewrite MAP_map, map_bot; auto. }
  apply mem_ident_spec in Hin.
  apply HasType_ins_app in Hty; auto using node_NoDupMembers.
  apply HasClock_ins_app in Hck; auto using node_NoDupMembers.
  (* pas génial *)
  assert (Hmap : forall l, List.map fst (idfst (idfst l)) = idents l).
    { intro; unfold idfst, idents.
      rewrite 2 map_map; apply List.map_ext; auto. }
  repeat split.
  - (* ty_DS *)
    apply HasType_In in Hty.
    eapply In_nth with (d := _) in Hty as (k & Hk & Hnth); subst.
    apply (f_equal fst) in Hnth as Hfnth.
    rewrite <- map_nth in Hfnth; simpl in Hfnth.
    rewrite <- Hfnth, Hmap.

    eapply CommonList2.Forall2_nth with (n := k) in Hwti.
    rewrite Hnth in Hwti; simpl in *.
    erewrite env_of_np_nth , nth_nprod_of_Ss with (k:=k); auto.
    unfold pStr. rewrite map_nth.
    apply DSForall_DS_of_S, SForall_map, SForall_map; eauto.
    all: unfold pStr, idents, idfst in *; repeat rewrite length_map in *; try congruence.
    unfold mem_nth.
    rewrite CommonList2.mem_nth_nth; auto using node_NoDup_in.
    rewrite length_map; auto.
  - (* cl_DS *)
    apply HasClock_In in Hck.
    unfold cl_DS.
    remember (env_of_np (idents (n_in n')) (nprod_of_Ss (pStr ins))) as env eqn:HH.
    assert (Henv : forall x, In x (idents (n_in n')) -> AC (env x) == DS_const true).
    { subst env.
      intros y Hiny.
      clear - Hiny Hl.
      eapply In_nth with (d := xH) in Hiny as (k & Hk & Hnth); subst.
      erewrite env_of_np_nth , nth_nprod_of_Ss with (k:=k); auto.
      unfold pStr.
      rewrite <- map_nth, map_map, <- 2 map_nth, 2 map_map.
      erewrite nth_indep, map_nth.
      { remember (nth k ins _) eqn:HH; clear HH.
        clear Hl Hk. clear n'.
        coind_Oeq Cof.
        destruct s.
        setoid_rewrite DS_inv in HU at 3.
        constructor; intros; split.
        rewrite HU, HV. simpl. rewrite AC_cons, DS_const_eq, 2 first_cons; auto.
        eapply Cof; auto.
        rewrite HU; simpl. rewrite AC_cons, rem_cons; auto.
        rewrite HV, DS_const_eq, rem_cons at 1; auto.
      }
      all: unfold idents, pStr in *; repeat rewrite length_map in *; try congruence.
    unfold mem_nth.
    rewrite CommonList2.mem_nth_nth; auto using node_NoDup_in.
    rewrite length_map; auto. }
    clear HH; rewrite Henv; auto.
    assert (bss (idents (n_in n')) env == DS_const true) as ->.
    { assert  ((idents (n_in n'))  <> []) as Hn0.
      { unfold idents.
        pose proof (n_ingt0 n').
        intro; subst; inv H1.
        apply map_eq_nil in H3.
        rewrite H3 in *; simpl in *; lia. }
        clear - Hn0 Henv.
      revert Hn0 Henv.
      generalize (idents (n_in n')).
      induction l as [|?[]]; intros; try congruence.
      simpl.
      setoid_rewrite Henv; auto. constructor; reflexivity.
      rewrite bss_cons, IHl; try congruence; auto.
      2: simpl in *; eauto.
      rewrite Henv. 2: constructor; auto.
      rewrite zip_const, MAP_map, map_DS_const; auto.
    }
    apply Oeq_le.
    assert (ck = Cks.Cbase); subst; auto.
    clear - Hbase Hck.
    apply in_map_iff in Hck as ((?&[]&?)&?&?). inv H.
    simpl_Forall; auto.
  - (* safe_DS *)
      eapply In_nth with (d := xH) in Hin as (k & Hk & Hnth); subst.
      erewrite env_of_np_nth , nth_nprod_of_Ss with (k:=k); auto.
      unfold pStr. rewrite map_nth.
      apply DSForall_DS_of_S, SForall_map, SForall_map; simpl; eauto.
      apply SForall_forall; auto.
      all: unfold idents, pStr in *; repeat rewrite length_map in *; try congruence.
    unfold mem_nth.
    rewrite CommonList2.mem_nth_nth; auto using node_NoDup_in.
    rewrite length_map; auto.
    Unshelve.
    all: eauto. all: try exact (Streams.const (Vscalar Values.Vundef)).
    exact (Streams.const absent).
Qed.

Lemma sem_node_outs :
  forall (HasCausInj : forall (Γ : static_env) (x cx : ident), HasCaus Γ x cx -> cx = x),
  forall {PSyn Prefs} (G : @global PSyn Prefs),
  forall f n ins outs,
    find_node f G = Some n ->
    Forall all_pres ins ->
    Forall (fun '(_, (_, ck, _, _)) => ck = Cks.Cbase) (n_out n) ->
    sem_node_ck G f ins outs ->
    Forall all_pres outs.
Proof.
  intros ? * Hfind Hin Hout Hsem.
  inv Hsem.
  subst bs.
  rewrite Hfind in *.
  take (Some _ = Some _) and inv it.
  apply clocks_of_pres in Hin; auto.
  2:{ pose proof (n_ingt0 n0).
      intro; subst; inv H1.
      apply symmetry, map_eq_nil in H6.
      rewrite H6 in *; simpl in *; lia. }
  rewrite Hin in *.
  take (clocked_node _ _ _) and destruct it as (Hdom&Hsc).
  simpl_Forall.
  apply Forall2_in_right with (y:=x) in H2 as (?&?&?); auto.
  simpl_Forall; subst.
  eapply sc_vars_sc_var_inv with (x:=i) in Hsc as [].
  unfold sc_var in H5.
  eapply H5 with (ck := Cks.Cbase) in H4.
  - inv H4; apply ac_all_pres, symmetry; auto.
  - eapply Den.Inf.HasCausRefl; auto.
    inv H4.
    eapply Hdom, FunctionalEnvironment.FEnv.find_In; eauto.
  - eapply HasClock_app_r, senv_HasClock'; eauto.
Qed.

Lemma find_node_complete :
  forall f G n,
    find_node f G = Some n ->
    find_node f (complete_global G) = Some (complete_node n).
Proof.
  unfold find_node, complete_global.
  intros * Hfind.
  eapply option_map_inv in Hfind as ([] & Hfind &?); subst.
  eapply CommonProgram.find_unit_transform_units_forward in Hfind; simpl in *.
  rewrite Hfind; auto.
Qed.

Lemma wc_ins_complete :
  forall G f ins,
    wc_ins G f (pStr ins) ->
    wc_ins (complete_global G) f (pStr ins).
Proof.
  unfold wc_ins.
  unfold sem_clock_inputs.
  intros * (H & n & Hfind & F1 & F2).
  apply find_node_complete in Hfind.
  eauto.
Qed.



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


Section Theorems.

  Variables
    (D : list LustreAst.declaration)
    (G : @global (fun _ _ => True) elab_prefs)
    (Gp : wt_global G /\ wc_global G)
    (P : Asm.program)
    (main : ident)
    (ins : list (Stream value))
    (n : @node (fun _ _ => True) elab_prefs).

  Hypothesis
    (Restr :  Restr.restr_global G) (** we restric to EMSOFT'21 syntax *)
    (HasCausInj : forall Γ x cx, HasCaus Γ x cx -> cx = x) (* related *)
    (Elab :   elab_declarations D = OK (exist _ G Gp))
    (Comp :   lustre_to_asm (Some main) G = OK P)     (* compilation succeeds *)
    (Hwti :   wt_ins G main ins)
    (Hwci :   wc_ins G main (pStr ins))
    (Hcau :   Forall node_causal (nodes G))
    (Hfind :  find_node main (G) = Some n)
    (Hckin :  Forall (fun '(_,(_,ck,_)) => ck = Cks.Cbase) (n_in n))
    (Hckout : Forall (fun '(_,(_,ck,_,_)) => ck = Cks.Cbase) (n_out n)).

  Theorem behavior_asm_exists :
    no_rte_global_main G main (env_of_np (List.map fst (n_in n)) (nprod_of_Ss (pStr ins))) ->
    exists outs,
      Sem.sem_node (G) main (pStr ins) (pStr outs)
      /\ exists T, program_behaves (Asm.semantics P) (Reacts T)
             /\ bisim_IO G main ins outs T.
  Proof.
    intros Norte.
    assert (Comp2 := Comp).
    unfold lustre_to_asm in Comp. simpl in Comp.
    destruct (l_to_nl G) as [G'|] eqn: Comp'; simpl in Comp; try discriminate.
    destruct Gp as (Hwc&Hwt).
    unfold_l_to_nl Comp'.
    eapply check_causality_correct in EQ; eauto with ltyping; simpl in EQ.
    pose (xs := nprod_of_Ss (pStr ins)).
    eapply ok_global_main with (xs := xs) (InfXs := nprod_of_Ss_inf _) in Norte as (outs & InfO & Hsem); eauto using wt_wc_wf_inputs.
    subst xs.
    rewrite Ss_of_nprod_of_Ss in Hsem.
    apply complete_global_sem in Hsem  as HsemC; auto.
    apply wc_ins_complete in Hwci as ?.
    eapply sem_node_sem_node_ck in HsemC as Hsemck; eauto.
    apply find_node_complete in Hfind.
    eapply sem_node_outs, pStr_all_pres in Hsemck as (?& Heqouts);
      eauto using all_pres_pStr.
    rewrite Heqouts in Hsem.
    eapply behavior_asm in Hsem as Ht; eauto.
  Qed.


  (** We introduce a local notion of streams unicity *)
  Definition unique_sts {A} (P : list (Stream A)->Prop) (x:list (Stream A)) : Prop :=
    P x /\ forall (x':list (Stream A)), P x' -> EqSts x x'.
  Local Notation "'exists' ! x , p" := (ex (unique_sts (fun x => p))) (at level 200).

  Corollary behavior_asm_new_uniq :
    no_rte_global_main G main (env_of_np (List.map fst (n_in n)) (nprod_of_Ss (pStr ins))) ->
    exists ! outs,
      Sem.sem_node (G) main (pStr ins) (pStr outs)
      /\ exists T, program_behaves (Asm.semantics P) (Reacts T)
             /\ bisim_IO G main ins outs T.
  Proof.
    intro Norte.
    eapply behavior_asm_exists in Norte as HH; eauto.
    destruct HH as (outs & Hsem & HsemOk).
    clear Hcau. (* this time we need causality on the complete node *)
    exists outs; split; auto.
    (* uniqueness *)
    intros outs' (Hsem' &  HsemOk').
    (* to obtain causality on (complete_global G) : *)
    unfold lustre_to_asm in Comp. simpl in Comp.
    destruct (l_to_nl G) as [G'|] eqn: Comp'; simpl in Comp; try discriminate.
    destruct Gp as (Hwc&Hwt).
    unfold_l_to_nl Comp'.
    eapply check_causality_correct in EQ; eauto with ltyping; simpl in EQ.
    apply complete_global_sem in Hsem, Hsem'; auto.
    eapply det_global
      with (ins := pStr ins) (outs1 := pStr outs)  (outs2 := pStr outs')
      in Hsem'; auto.
    apply pStr_EqSts, Hsem'.
  Qed.


  (** Correction with no-run-time-errors check *)
  Corollary behavior_asm_new_check :
    CheckOp.check_global G = true -> (** check for run-time errors *)
    exists outs,
      Sem.sem_node (G) main (pStr ins) (pStr outs)
      /\ exists T, program_behaves (Asm.semantics P) (Reacts T)
             /\ bisim_IO G main ins outs T.
  Proof.
    intros Hchk.
    eapply behavior_asm_exists; eauto.
    destruct Gp.
    apply no_rte_global_main_global, check_global_ok; auto.
  Qed.

End Theorems.
