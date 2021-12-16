From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.LSyntax Lustre.LClocking.
From Velus Require Import Lustre.Normalization.Normalization.

(** * Preservation of Typing through Normalization *)

Module Type NCLOCKING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (Import Norm : NORMALIZATION Ids Op OpAux Cks Syn).
  Import Fresh Fresh.Facts Fresh.Tactics.

  (** ** Rest of clockof preservation (started in Normalization.v) *)

  Fact unnest_reset_clockof : forall G vars e e' eqs' st st',
      wc_exp G vars e ->
      numstreams e = 1 ->
      unnest_reset (unnest_exp G true) e st = (e', eqs', st') ->
      clockof e' = clockof e.
  Proof.
    intros * Hwc Hnum Hunn.
    unnest_reset_spec; simpl in *; auto.
    1,2:assert (length l = 1) by
        (eapply unnest_exp_length in Hk0; eauto with lclocking; congruence);
      singleton_length.
    - eapply unnest_exp_clockof in Hk0; eauto with lclocking.
    - eapply unnest_exp_annot in Hk0; eauto with lclocking.
      simpl in Hk0. rewrite app_nil_r in Hk0.
      rewrite <- length_annot_numstreams in Hnum.
      rewrite clockof_annot, <- Hk0.
      singleton_length. rewrite Hk0 in *; simpl in Hhd; subst.
      reflexivity.
  Qed.

  Corollary mmap2_unnest_exp_clocksof' :
    forall G vars is_control es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => clocksof es' = clockof e) es' es.
  Proof with eauto with lclocking.
    intros G vars is_control es es' eqs' st st' Hwt Hmap.
    eapply mmap2_unnest_exp_annots' in Hmap...
    clear Hwt.
    induction Hmap; constructor; eauto.
    rewrite clocksof_annots, H, <- clockof_annot...
  Qed.

  Corollary mmap2_unnest_exp_clocksof'' : forall G vars is_control es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      Forall2 (fun e ck => clockof e = [ck]) (concat es') (clocksof es).
  Proof.
    intros * Hwl Hmap.
    eapply mmap2_unnest_exp_annots'' in Hmap; eauto with lclocking.
    rewrite clocksof_annots, Forall2_map_2.
    eapply Forall2_impl_In; eauto. intros; simpl in *.
    rewrite clockof_annot, H1; auto.
  Qed.

  Corollary mmap2_unnest_exp_clocksof''' : forall G vars is_control ck es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      Forall (eq ck) (clocksof es) ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      Forall (fun e => clockof e = [ck]) (concat es').
  Proof.
    intros * Hwl Hck Hmap.
    assert (Hmap':=Hmap). eapply mmap2_unnest_exp_numstreams in Hmap.
    eapply mmap2_unnest_exp_annots'' in Hmap'; eauto with lclocking.
    rewrite clocksof_annots in Hck.
    assert (length (concat es') = length (annots es)) by (apply Forall2_length in Hmap'; auto).
    assert (Forall (fun e => exists y, In y (annots es) /\ (clockof e = [ck])) (concat es')) as Hf'.
    { eapply Forall2_ignore2. solve_forall.
      rewrite clockof_annot, H2; simpl in *. congruence. }
    solve_forall.
  Qed.

  Corollary mmap2_mmap2_unnest_exp_clocksof1 : forall G vars is_control ck x tx es es' eqs' st st',
      Forall (fun es => Forall (wc_exp G vars) (snd es)) es ->
      Forall (fun '(i, es) => Forall (eq (Con ck x (tx, i))) (clocksof es)) es ->
      mmap2 (fun '(i, es) => bind2 (mmap2 (unnest_exp G is_control) es) (fun es' eqs' => ret (i, concat es', concat eqs'))) es st = (es', eqs', st') ->
      Forall (fun '(i, es) => Forall (fun e => clockof e = [Con ck x (tx, i)]) es) es'.
  Proof.
    intros * Hwl Htys Hmap.
    eapply mmap2_values in Hmap.
    eapply Forall3_ignore3, Forall2_ignore1 in Hmap.
    eapply Forall_impl; [|eauto]; intros (?&?) ((?&?)&Hin1&?&?&?&Hbind); clear Hmap; repeat inv_bind.
    rewrite Forall_forall in *.
    eapply mmap2_unnest_exp_clocksof'' in H. 2:eapply Hwl in Hin1; eauto.
    intros ? Hin.
    eapply Forall2_ignore2, Forall_forall in H as (?&?&Heq); eauto.
    rewrite Heq. f_equal.
    eapply Htys, Forall_forall in Hin1; eauto.
  Qed.

  Corollary mmap2_mmap2_unnest_exp_clocksof2 : forall G vars is_control ck (es : list (enumtag * _))  es' eqs' st st',
      Forall (fun es => Forall (wc_exp G vars) (snd es)) es ->
      Forall (fun es => Forall (eq ck) (clocksof (snd es))) es ->
      mmap2 (fun '(i, es) => bind2 (mmap2 (unnest_exp G is_control) es) (fun es' eqs' => ret (i, concat es', concat eqs'))) es st = (es', eqs', st') ->
      Forall (fun es => Forall (fun e => clockof e = [ck]) (snd es)) es'.
  Proof.
    intros * Hwl Htys Hmap.
    eapply mmap2_values in Hmap.
    eapply Forall3_ignore3, Forall2_ignore1 in Hmap.
    eapply Forall_impl; [|eauto]; intros (?&?) ((?&?)&Hin1&?&?&?&Hbind); clear Hmap; repeat inv_bind.
    rewrite Forall_forall in *.
    eapply mmap2_unnest_exp_clocksof'' in H. 2:eapply Hwl in Hin1; eauto.
    intros ? Hin.
    eapply Forall2_ignore2, Forall_forall in H as (?&?&Heq); eauto.
    rewrite Heq. f_equal.
    eapply Htys, Forall_forall in Hin1; eauto.
  Qed.

  Corollary mmap2_unnest_exp_clocksof :
    forall G vars is_control es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      clocksof (concat es') = clocksof es.
  Proof.
    intros.
    eapply mmap2_unnest_exp_annots in H0; eauto with lclocking.
    rewrite clocksof_annots, H0, <- clocksof_annots; eauto.
  Qed.
  Local Hint Resolve mmap2_unnest_exp_clocksof : norm.

  Corollary unnest_exps_clocksof : forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      unnest_exps G es st = (es', eqs', st') ->
      clocksof es' = clocksof es.
  Proof.
    intros.
    eapply unnest_exps_annots in H0; eauto with lclocking.
    repeat rewrite clocksof_annots.
    congruence.
  Qed.

  Fact fby_iteexp_clockof : forall e0 e ann es' eqs' st st',
      fby_iteexp e0 e ann st = (es', eqs', st') ->
      clockof es' = [(snd ann)].
  Proof.
    intros ?? [ty cl] es' eqs' st st' Hfby; simpl in *.
    destruct (is_constant e0); repeat inv_bind; reflexivity.
  Qed.

  Fact unnest_fby_clocksof : forall anns e0s es,
      length e0s = length anns ->
      length es = length anns ->
      clocksof (unnest_fby e0s es anns) = List.map snd anns.
  Proof.
    intros * Hlen1 Hlen2.
    rewrite clocksof_annots, unnest_fby_annot; auto.
  Qed.

  Fact unnest_merge_clocksof : forall tys x tx es nck,
      clocksof (unnest_merge (x, tx) es tys nck) = List.map (fun _ => nck) tys.
  Proof.
    induction tys; intros *; simpl in *; f_equal; eauto.
  Qed.

  Fact unnest_case_clocksof : forall tys c es d nck,
      clocksof (unnest_case c es d tys nck) = List.map (fun _ => nck) tys.
  Proof.
    induction tys; intros *; simpl in *; f_equal; eauto.
  Qed.

  Fact unnest_rhs_clockof: forall G vars e es' eqs' st st',
      wc_exp G vars e ->
      unnest_rhs G e st = (es', eqs', st') ->
      clocksof es' = clockof e.
  Proof.
    intros * Hwc Hnorm.
    eapply unnest_rhs_annot in Hnorm; eauto with lclocking.
    rewrite clocksof_annots, Hnorm, <- clockof_annot. reflexivity.
  Qed.

  Corollary unnest_rhss_clocksof: forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      unnest_rhss G es st = (es', eqs', st') ->
      clocksof es' = clocksof es.
  Proof.
    intros.
    eapply unnest_rhss_annots in H0; eauto with lclocking.
    repeat rewrite clocksof_annots. congruence.
  Qed.

  (** ** nclockof is also preserved by unnest_exp *)

  Fact unnest_merge_clockof : forall ckid es tys ck,
      Forall (fun e => clockof e = [ck]) (unnest_merge ckid es tys ck).
  Proof.
    intros *.
    setoid_rewrite clockof_annot.
    specialize (unnest_merge_annot ckid es tys ck) as Hannot.
    eapply Forall2_ignore1 in Hannot.
    eapply Forall_impl; [|eauto]. intros ? (?&?&Hann).
    now rewrite Hann.
  Qed.

  Fact unnest_case_clockof : forall e es d tys ck,
      Forall (fun e => clockof e = [ck]) (unnest_case e es d tys ck).
  Proof.
    intros *.
    setoid_rewrite clockof_annot.
    specialize (unnest_case_annot e es tys d ck) as Hannot.
    eapply Forall2_ignore1 in Hannot.
    eapply Forall_impl; [|eauto]. intros ? (?&?&Hann).
    now rewrite Hann.
  Qed.

  Fact unnest_when_nclocksof : forall ckid k es tys ck,
      length es = length tys ->
      nclocksof (unnest_when ckid k es tys ck) = map (fun _ => (ck, None)) tys.
  Proof.
    unfold unnest_when.
    induction es; intros * Hl; destruct tys; simpl in *; try congruence; auto.
  Qed.

  Fact unnest_merge_nclocksof : forall tx tys es ck,
      nclocksof (unnest_merge tx es tys ck) = map (fun _ => (ck, None)) tys.
  Proof.
    unfold unnest_merge.
    induction tys; intros; simpl in *; auto.
  Qed.

  Fact unnest_case_nclocksof : forall e tys es d ck,
      nclocksof (unnest_case e es d tys ck) = map (fun _ => (ck, None)) tys.
  Proof.
    unfold unnest_case.
    induction tys; intros; simpl in *; auto.
  Qed.

  Lemma idents_for_anns_nclocksof : forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      nclocksof (map (fun '(x, ann0) => Evar x ann0) ids) = map (fun '(x, (_, ck)) => (ck, Some x)) ids.
  Proof.
    induction anns as [|(?&?)]; intros * Hids; repeat inv_bind; simpl in *; auto.
    f_equal; eauto.
  Qed.

  Fact unnest_exp_nclocksof : forall G vars e is_control es' eqs' st st',
      wc_exp G vars e ->
      unnest_exp G is_control e st = (es', eqs', st') ->
      Forall2 (fun '(ck1, o1) '(ck2, o2) => ck1 = ck2 /\ LiftO True (fun x1 => o2 = Some x1) o1) (nclockof e) (nclocksof es').
  Proof with eauto.
    intros * Hwc Hun.
    assert (length (nclockof e) = length (nclocksof es')) as Hlen.
    { rewrite length_nclockof_numstreams, length_nclocksof_annots, <-length_annot_numstreams.
      apply unnest_exp_annot_length in Hun; eauto with lclocking. }
    inv Hwc; repeat inv_bind; simpl; repeat rewrite map_length in Hlen.
    - (* const *)
      repeat constructor.
    - (* enum *)
      repeat constructor.
    - (* var *)
      repeat constructor.
    - (* unop *)
      repeat constructor.
    - (* binop *)
      repeat constructor.
    - (* fby *)
      erewrite idents_for_anns_nclocksof, Forall2_map_2; eauto.
      eapply idents_for_anns_values in H5. rewrite <-H5, 2 Forall2_map_1.
      apply Forall2_same, Forall_forall; intros (?&?&?) _; simpl; auto.
    - (* arrow *)
      erewrite idents_for_anns_nclocksof, Forall2_map_2; eauto.
      eapply idents_for_anns_values in H5. rewrite <-H5, 2 Forall2_map_1.
      apply Forall2_same, Forall_forall; intros (?&?&?) _; simpl; auto.
    - (* when *)
      rewrite unnest_when_nclocksof.
      2:{ rewrite H2. apply mmap2_unnest_exp_length in H3; eauto with lclocking.
          rewrite H3, length_clocksof_annots; eauto. }
      apply Forall2_same, Forall_map, Forall_forall. intros ? _; simpl; auto.
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + rewrite unnest_merge_nclocksof.
        apply Forall2_same, Forall_map, Forall_forall. intros ? _; simpl; auto.
      + erewrite idents_for_anns_nclocksof, Forall2_map_2; eauto.
        eapply idents_for_anns_values in H5. erewrite map_ext, <-map_map, <-H5, 2 Forall2_map_1.
        2:instantiate (1:=fun '(_, ck) => (ck, None)); auto.
        apply Forall2_same, Forall_forall; intros (?&?&?) _; simpl; auto.
    - (* case *)
      destruct is_control; repeat inv_bind.
      + rewrite unnest_case_nclocksof.
        apply Forall2_same, Forall_map, Forall_forall. intros ? _; simpl; auto.
      + erewrite idents_for_anns_nclocksof, Forall2_map_2; eauto.
        eapply idents_for_anns_values in H11. erewrite map_ext, <-map_map, <-H11, 2 Forall2_map_1.
        2:instantiate (1:=fun '(_, ck) => (ck, None)); auto.
        apply Forall2_same, Forall_forall; intros (?&?&?) _; simpl; auto.
    - (* app *)
      erewrite idents_for_anns_nclocksof, Forall2_map_2; eauto.
      eapply idents_for_anns_values in H8. rewrite <-H8, 2 Forall2_map_1.
      apply Forall2_same, Forall_forall; intros (?&?&?) _; simpl; auto.
  Qed.

  Corollary mmap2_unnest_exp_nclocksof : forall G vars es is_control es' eqs' st st',
      Forall (wc_exp G vars) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      Forall2 (fun '(ck1, o1) '(ck2, o2) => ck1 = ck2 /\ LiftO True (fun x1 => o2 = Some x1) o1) (nclocksof es) (nclocksof (concat es')).
  Proof with eauto.
    induction es; intros * Hf Hun; inv Hf; repeat inv_bind; simpl in *; auto.
    unfold nclocksof. rewrite <-flat_map_app.
    apply Forall2_app; eauto using unnest_exp_nclocksof.
  Qed.

  Lemma unnest_noops_exp_nclocksof : forall ck e e' eqs' st st',
      normalized_lexp e ->
      unnest_noops_exp ck e st = (e', eqs', st') ->
      Forall2 (fun '(ck1, o1) '(ck2, o2) => ck1 = ck2 /\ LiftO True (fun x1 => o2 = Some x1) o1) (nclockof e) (nclockof e').
  Proof.
    unfold unnest_noops_exp.
    intros * Hnormed Hun. cases_eqn Heq; repeat inv_bind; simpl.
    - apply Forall2_same, Forall_forall. intros (?&?) _.
      split; auto. destruct o; simpl in *; auto.
    - inv Hnormed; simpl in *; inv Heq.
      1-6:repeat constructor.
      destruct ck; simpl in *; try congruence.
  Qed.

  Fact unnest_noops_exps_nclocksof : forall cks es es' eqs' st st',
      Forall normalized_lexp es ->
      length cks = length es ->
      unnest_noops_exps cks es st = (es', eqs', st') ->
      Forall2 (fun '(ck1, o1) '(ck2, o2) => ck1 = ck2 /\ LiftO True (fun x1 => o2 = Some x1) o1) (nclocksof es) (nclocksof es').
  Proof.
    unfold unnest_noops_exps.
    induction cks; intros * Hn Hlen Hun; destruct es; simpl in *; try congruence;
      inv Hn; repeat inv_bind; simpl in *; auto.
    apply Forall2_app; eauto using unnest_noops_exp_nclocksof.
    eapply IHcks; eauto.
    repeat inv_bind; eauto.
  Qed.

  Fact unnest_noops_exps_nclocksof2 : forall G vars cks es es2 es' eqs2 eqs' st st2 st3 st',
      Forall (wc_exp G vars) es ->
      length cks = length (annots es) ->
      mmap2 (unnest_exp G false) es st = (es2, eqs2, st2) ->
      unnest_noops_exps cks (concat es2) st3 = (es', eqs', st') ->
      Forall2 (fun '(ck1, o1) '(ck2, o2) => ck1 = ck2 /\ LiftO True (fun x1 => o2 = Some x1) o1) (nclocksof es) (nclocksof es').
  Proof.
    intros.
    eapply unnest_noops_exps_nclocksof in H2; eauto with norm lclocking.
    2:{ apply mmap2_unnest_exp_length in H1; eauto with lclocking. congruence. }
    eapply mmap2_unnest_exp_nclocksof in H1; eauto.
    eapply Forall2_trans_ex in H2; eauto.
    eapply Forall2_impl_In; [|eauto]; intros (?&?) (?&?) _ _ ((?&?)&_&(?&?)&?&?); subst.
    split; auto.
    destruct o; simpl in *; auto. subst; simpl in *; auto.
  Qed.

  (** ** A few additional things *)

  Definition st_clocks (st : fresh_st (Op.type * clock)) :=
    idck (st_anns st).

  Global Hint Unfold st_clocks : list.

  Fact idents_for_anns_incl_clocks : forall anns ids st st',
    idents_for_anns anns st = (ids, st') ->
    incl (List.map (fun '(id, (_, cl)) => (id, cl)) ids) (st_clocks st').
  Proof.
    intros anns ids st st' Hids.
    apply idents_for_anns_incl in Hids.
    intros [id cl] Hin.
    solve_In.
  Qed.

  Fact st_follows_clocks_incl : forall st st',
      st_follows st st' ->
      incl (st_clocks st) (st_clocks st').
  Proof.
    intros st st' Hfollows.
    apply st_follows_incl in Hfollows.
    unfold st_clocks.
    repeat apply incl_map.
    assumption.
  Qed.

  Ltac solve_incl :=
    match goal with
    | H : wc_clock ?l1 ?cl |- wc_clock ?l2 ?cl =>
      eapply wc_clock_incl; [| eauto]
    | H : wc_exp ?G ?l1 ?e |- wc_exp ?G ?l2 ?e =>
      eapply wc_exp_incl; [| eauto]
    | H : wc_equation ?G ?l1 ?eq |- wc_equation ?G ?l2 ?eq =>
      eapply wc_equation_incl; [| eauto]
    | H : wc_block ?G ?l1 ?eq |- wc_block ?G ?l2 ?eq =>
      eapply wc_block_incl; [| eauto]
    | H : In ?i ?l1 |- In ?i ?l2 =>
      assert (incl l1 l2) by repeat solve_incl; eauto
    | |- incl ?l1 ?l1 => reflexivity
    | |- incl ?l1 (?l1 ++ ?l2) =>
      eapply incl_appl; reflexivity
    | |- incl (?l1 ++ ?l2) (?l1 ++ ?l3) =>
      eapply incl_app
    | |- incl ?l1 (?l2 ++ ?l3) =>
      eapply incl_appr
    | |- incl ?l1 (?a::?l2) =>
      eapply incl_tl
    | |- incl (st_clocks ?st1) (st_clocks _) =>
      eapply st_follows_clocks_incl; repeat solve_st_follows
    | H : incl ?l1 ?l2 |- incl (idty ?l1) (idty ?l2) =>
      eapply incl_map; eauto
    end; auto.

  (** ** Preservation of clocking through first pass *)

  Import Permutation.

  Fact fresh_ident_wc_env : forall pref hint vars ty ck id st st',
      wc_env (vars++st_clocks st) ->
      wc_clock (vars++st_clocks st) ck ->
      fresh_ident pref hint (ty, ck) st = (id, st') ->
      wc_env (vars++st_clocks st').
  Proof.
    intros * Hwenv Hwc Hfresh.
    apply fresh_ident_anns in Hfresh.
    unfold st_clocks in *. rewrite Hfresh; simpl.
    rewrite <- Permutation_middle.
    constructor; simpl.
    - repeat solve_incl.
    - eapply Forall_impl; [|eauto].
      intros; simpl in *. repeat solve_incl.
  Qed.

  Fact idents_for_anns_wc_env : forall vars anns ids st st',
      wc_env (vars++st_clocks st) ->
      Forall (wc_clock (vars++st_clocks st)) (map snd anns) ->
      idents_for_anns anns st = (ids, st') ->
      wc_env (vars++st_clocks st').
  Proof with eauto.
    induction anns as [|[ty ck]]; intros ids st st' Hwenv Hwc Hids;
      repeat inv_bind...
    inv Hwc.
    eapply IHanns in H0... 2:(solve_forall; repeat solve_incl).
    eapply fresh_ident_wc_env...
  Qed.

  Fact hd_default_wc_exp {PSyn prefs} : forall (G : @global PSyn prefs) vars es,
      Forall (wc_exp G vars) es ->
      wc_exp G vars (hd_default es).
  Proof.
    intros G vars es Hf.
    destruct es; simpl.
    - constructor.
    - inv Hf; auto.
  Qed.
  Local Hint Resolve hd_default_wc_exp : norm.

  Section unnest_node_wc.
    Variable G1 : @global nolocal_top_block local_prefs.
    Variable G2 : @global nolocal_top_block norm1_prefs.

    Fact idents_for_anns_wc : forall vars anns ids st st',
        idents_for_anns anns st = (ids, st') ->
        Forall (wc_exp G2 (vars++st_clocks st')) (List.map (fun '(x, ann) => Evar x ann) ids).
    Proof.
      induction anns; intros ids st st' Hident;
        repeat inv_bind; simpl; auto.
      destruct a as [? ?]. repeat inv_bind.
      constructor; eauto.
      constructor.
      eapply fresh_ident_In in H.
      eapply idents_for_anns_st_follows in H0.
      eapply st_follows_incl in H; eauto.
      eapply in_or_app. right. solve_In.
    Qed.

    Fact mmap2_wc {A B} :
      forall vars (k : A -> Fresh (list exp * list equation) B) a es' eqs' st st',
        mmap2 k a st = (es', eqs', st') ->
        (forall st st' a es eqs', k a st = (es, eqs', st') -> st_follows st st') ->
        Forall (fun a => forall es' eqs' st0 st0',
                    k a st0 = (es', eqs', st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    Forall (wc_exp G2 vars) es' /\
                    Forall (wc_equation G2 vars) eqs') a ->
        Forall (wc_exp G2 vars) (concat es') /\
        Forall (wc_equation G2 vars) (concat eqs').
    Proof with eauto.
      intros vars k a.
      induction a; intros * Hmap Hfollows Hforall;
        repeat inv_bind; simpl.
      - repeat constructor.
      - inv Hforall.
        assert (H':=H). eapply H3 in H' as [Hwc1 Hwc1']... 2,3:repeat solve_st_follows.
        eapply IHa in H0 as [Hwc2 Hwc2']...
        2:{ solve_forall. eapply H2 in H4... etransitivity... }
        repeat rewrite Forall_app. repeat split; eauto.
    Qed.

    Fact mmap2_wc' {A B} :
      forall vars (k : A -> Fresh (enumtag * list exp * list equation) B) a es' eqs' st st',
        mmap2 k a st = (es', eqs', st') ->
        (forall st st' a es eqs', k a st = (es, eqs', st') -> st_follows st st') ->
        Forall (fun a => forall n es' eqs' st0 st0',
                    k a st0 = (n, es', eqs', st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    Forall (wc_exp G2 vars) es' /\
                    Forall (wc_equation G2 vars) eqs') a ->
        Forall (wc_exp G2 vars) (concat (map snd es')) /\
        Forall (wc_equation G2 vars) (concat eqs').
    Proof with eauto.
      intros vars k a.
      induction a; intros * Hmap Hfollows Hforall;
        repeat inv_bind; simpl.
      - repeat constructor.
      - inv Hforall.
        assert (H':=H). destruct x. eapply H3 in H' as [Hwc1 Hwc1']... 2,3:repeat solve_st_follows.
        eapply IHa in H0 as [Hwc2 Hwc2']...
        2:{ solve_forall. eapply H2 in H4... etransitivity... }
        repeat rewrite Forall_app. repeat split; eauto.
    Qed.

    Fact unnest_fby_wc_exp : forall vars e0s es anns,
        Forall (wc_exp G2 vars) e0s ->
        Forall (wc_exp G2 vars) es ->
        Forall2 (fun e0 a => clockof e0 = [a]) e0s (map snd anns) ->
        Forall2 (fun e a => clockof e = [a]) es (map snd anns) ->
        Forall (wc_exp G2 vars) (unnest_fby e0s es anns).
    Proof.
      intros * Hwc1 Hwc2 Hck1 Hck2.
      unfold unnest_fby.
      assert (length e0s = length anns) as Hlen1 by (eapply Forall2_length in Hck1; solve_length).
      assert (length es = length anns) as Hlen2 by (eapply Forall2_length in Hck2; solve_length).
      solve_forall.
      constructor; simpl in *; eauto; try rewrite app_nil_r; eauto.
    Qed.

    Fact unnest_arrow_wc_exp : forall vars e0s es anns,
        Forall (wc_exp G2 vars) e0s ->
        Forall (wc_exp G2 vars) es ->
        Forall2 (fun e0 a => clockof e0 = [a]) e0s (map snd anns) ->
        Forall2 (fun e a => clockof e = [a]) es (map snd anns) ->
        Forall (wc_exp G2 vars) (unnest_arrow e0s es anns).
    Proof.
      intros * Hwc1 Hwc2 Hck1 Hck2.
      unfold unnest_arrow.
      assert (length e0s = length anns) as Hlen1 by (eapply Forall2_length in Hck1; solve_length).
      assert (length es = length anns) as Hlen2 by (eapply Forall2_length in Hck2; solve_length).
      solve_forall.
      constructor; simpl in *; eauto; try rewrite app_nil_r; eauto.
    Qed.

    Fact unnest_when_wc_exp : forall vars ckid ck b ty es tys,
        length es = length tys ->
        In (ckid, ck) vars ->
        Forall (wc_exp G2 vars) es ->
        Forall (fun e => clockof e = [ck]) es ->
        Forall (wc_exp G2 vars) (unnest_when ckid b es tys (Con ck ckid (ty, b))).
    Proof.
      intros * Hlen Hin Hwc Hck. unfold unnest_when.
      solve_forall.
      repeat constructor; auto;
        simpl; rewrite app_nil_r, H1; auto.
    Qed.

    Fact unnest_merge_wc_exp : forall vars ckid tx ck es tys,
        In (ckid, ck) vars ->
        es <> [] ->
        Forall (fun es => length (snd es) = length tys) es ->
        Forall (fun es => Forall (wc_exp G2 vars) (snd es)) es ->
        Forall (fun '(i, es) => Forall (fun e => clockof e = [Con ck ckid (tx, i)]) es) es ->
        Forall (wc_exp G2 vars) (unnest_merge (ckid, tx) es tys ck).
    Proof.
      intros *; revert es. induction tys; intros * InV Hnnil Hlen Hwc Hcks; simpl; constructor.
      - constructor; auto; try rewrite Forall_map.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + clear - Hwc.
          eapply Forall_impl; [|eauto]; intros (?&?) Hf; simpl in *.
          inv Hf; auto with norm.
        + clear - Hcks Hlen.
          rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite app_nil_r.
          specialize (Hlen _ Hin). specialize (Hcks _ Hin); simpl in *.
          inv Hcks; simpl in *; try congruence.
          rewrite H. auto.
        + clear - Hcks Hlen.
          rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite app_nil_r.
          specialize (Hlen _ Hin). specialize (Hcks _ Hin); simpl in *.
          inv Hcks; simpl in *; try congruence.
          rewrite H. auto.
      - eapply IHtys; eauto; try rewrite Forall_map.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + clear - Hlen. eapply Forall_impl; [|eauto]; intros.
          destruct a0, l; simpl; inv H; auto.
        + clear - Hwc. eapply Forall_impl; [|eauto]; intros.
          destruct a; simpl in *. inv H; simpl; auto.
        + clear - Hcks. eapply Forall_impl; [|eauto]; intros.
          destruct a; simpl in *. inv H; simpl; auto.
    Qed.

    Fact unnest_case_wc_exp : forall vars e ck es d tys,
        wc_exp G2 vars e ->
        clockof e = [ck] ->
        es <> [] ->
        Forall (fun es => length (snd es) = length tys) es ->
        Forall (fun es => Forall (wc_exp G2 vars) (snd es)) es ->
        Forall (fun es => Forall (fun e => clockof e = [ck]) (snd es)) es ->
        LiftO True (fun d => length (clocksof d) = length tys) d ->
        LiftO True (Forall (wc_exp G2 vars)) d ->
        LiftO True (Forall (fun e => clockof e = [ck])) d ->
        Forall (wc_exp G2 vars) (unnest_case e es d tys ck).
    Proof.
      intros *; revert es d.
      induction tys; intros * Hwce Hck Hnnil Hlen Hwc Hcks Hlend Hwcd Hckd; simpl; constructor.
      - constructor; auto; try rewrite Forall_map.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + clear - Hwc.
          eapply Forall_impl; [|eauto]; intros (?&?) Hf; simpl in *.
          inv Hf; auto with norm.
        + clear - Hcks Hlen.
          rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite app_nil_r.
          specialize (Hlen _ Hin). specialize (Hcks _ Hin); simpl in *.
          inv Hcks; simpl in *; try congruence.
          rewrite H. auto.
        + clear - Hcks Hlen.
          rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite app_nil_r.
          specialize (Hlen _ Hin). specialize (Hcks _ Hin); simpl in *.
          inv Hcks; simpl in *; try congruence.
          rewrite H. auto.
        + intros ? Hopt. destruct d; simpl in *; inv Hopt.
          inv Hwcd; auto with norm.
        + intros ? Hopt. destruct d; simpl in *; inv Hopt.
          inv Hckd; simpl in *; try congruence.
          rewrite app_nil_r, H. auto.
        + intros ? Hopt. destruct d; simpl in *; inv Hopt.
          inv Hckd; simpl in *; try congruence.
          rewrite app_nil_r, H. auto.
      - eapply IHtys; eauto; try rewrite Forall_map.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + clear - Hlen. eapply Forall_impl; [|eauto]; intros.
          destruct a0; simpl; inv H; auto.
          destruct l; inv H1; auto.
        + clear - Hwc. eapply Forall_impl; [|eauto]; intros.
          destruct a; simpl in *; inv H; simpl; auto.
        + clear - Hcks. eapply Forall_impl; [|eauto]; intros.
          destruct a; simpl in *; inv H; simpl; auto.
        + destruct d; simpl in *; try congruence.
          inv Hckd; simpl in *; try congruence.
          rewrite H in Hlend; simpl in *; inv Hlend; auto.
        + destruct d; simpl in *; auto. inv Hwcd; simpl; auto.
        + destruct d; simpl in *; auto. inv Hckd; simpl; auto.
    Qed.

    Fact unnest_reset_wc : forall vars e e' eqs' st st' ck,
        (forall es' eqs' st0',
            st_follows st0' st' ->
            unnest_exp G1 true e st = (es', eqs', st0') ->
            Forall (wc_exp G2 (vars++st_clocks st0')) es' /\
            Forall (wc_equation G2 (vars++st_clocks st0')) eqs') ->
        wc_exp G1 (vars++st_clocks st) e ->
        clockof e = [ck] ->
        unnest_reset (unnest_exp G1 true) e st = (e', eqs', st') ->
        clockof e' = [ck] /\
        wc_exp G2 (vars++st_clocks st') e' /\
        Forall (wc_equation G2 (vars++st_clocks st')) eqs'.
    Proof.
      intros * Hkwc Hwc Hck Hunn.
      repeat split.
      - eapply unnest_reset_clockof in Hunn; eauto; try congruence.
        rewrite <-length_clockof_numstreams, Hck; eauto.
      - unnest_reset_spec; simpl in *; auto.
        + specialize (Hkwc _ _ _ (st_follows_refl _) eq_refl) as (Hwc1&_).
          destruct l; simpl in H; [inv H|]; subst.
          inv Hwc1; auto.
        + constructor.
          eapply fresh_ident_In in Hfresh.
          apply in_or_app; right.
          unfold st_clocks, idck. simpl_In.
          repeat eexists; eauto. split; auto.
      - unfold unnest_reset in Hunn. simpl in *; repeat inv_bind; auto.
        assert (length x = 1).
        { eapply unnest_exp_length in H; eauto with lclocking.
          rewrite <- length_clockof_numstreams, Hck in H; auto. }
        singleton_length.
        assert (Hk:=H). apply unnest_exp_normalized_cexp, Forall_singl in H.
        assert (st_follows x1 st') as Hfollows.
        { inv H; [| | inv H1]; try destruct cl; simpl in *;
            repeat inv_bind; repeat solve_st_follows. }
        eapply Hkwc in Hk as [Hwc1 Hwc2]; auto.
        inv H; [| | inv H1]; simpl in *.
        1-8:repeat inv_bind.
        1-4,6-8:constructor.
        2,4,6,8,10,12,14,15:solve_forall; repeat solve_incl.
        1-7:inv Hwc1.
        1-7:repeat (constructor; eauto; repeat solve_incl); simpl in *.
        1-7:(take (fresh_ident _ _ _ _ = (_, _)) and eapply fresh_ident_In in it;
             apply in_or_app, or_intror;
             unfold st_clocks, idck; simpl_In;
             repeat eexists; eauto; auto).
    Qed.

    Fact unnest_resets_wc : forall vars es es' eqs' st st',
        Forall (fun e => forall es' eqs' st0 st0',
                    unnest_exp G1 true e st0 = (es', eqs', st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    Forall (wc_exp G2 (vars++st_clocks st0')) es' /\
                    Forall (wc_equation G2 (vars++st_clocks st0')) eqs') es ->
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        Forall (fun e => exists ck, clockof e = [ck]) es ->
        mmap2 (unnest_reset (unnest_exp G1 true)) es st = (es', eqs', st') ->
        Forall (fun e => exists ck, clockof e = [ck]) es' /\
        Forall (wc_exp G2 (vars++st_clocks st')) es' /\
        Forall (wc_equation G2 (vars++st_clocks st')) (concat eqs').
    Proof.
      induction es; intros * F Wt Cks Map; inv F; inv Wt; inv Cks;
        repeat inv_bind; simpl in *; auto.
      assert (Map:=H0). eapply IHes in H0 as (Cks1&Wt1&Wt2); eauto.
      3:solve_forall; repeat solve_incl.
      2:{ eapply Forall_impl; [|eapply H2].
          intros. eapply H7 in H10; eauto.
          repeat solve_st_follows. }
      destruct H5 as (?&?).
      eapply unnest_reset_wc in H as (Cks2&Wt3&Wt4); eauto.
      repeat split; try constructor; eauto.
      - repeat solve_incl.
      - apply Forall_app; split; auto.
        solve_forall; repeat solve_incl.
      - intros * Follows Un. eapply H1 in Un; eauto. 1,2:repeat solve_st_follows.
    Qed.

    Lemma unnest_noops_exps_wc : forall vars cks es es' eqs' st st' ,
        length es = length cks ->
        Forall normalized_lexp es ->
        Forall (fun e => numstreams e = 1) es ->
        Forall (wc_exp G2 (vars++st_clocks st)) es ->
        unnest_noops_exps cks es st = (es', eqs', st') ->
        Forall (wc_exp G2 (vars++st_clocks st')) es' /\
        Forall (wc_equation G2 (vars++st_clocks st')) eqs'.
    Proof.
      unfold unnest_noops_exps.
      induction cks; intros * Hlen Hnormed Hnums Hwt Hunt; repeat inv_bind; simpl; auto.
      destruct es; simpl in *; inv Hlen; repeat inv_bind.
      inv Hwt. inv Hnums. inv Hnormed.
      assert (Forall (wc_exp G2 (vars ++ st_clocks x2)) es) as Hes.
      { solve_forall. repeat solve_incl; eauto with norm. }
      eapply IHcks in Hes as (Hes'&Heqs'). 2-4:eauto.
      2:repeat inv_bind; repeat eexists; eauto; inv_bind; eauto.
      unfold unnest_noops_exp in H.
      rewrite <-length_annot_numstreams in H6. singleton_length.
      destruct p as (?&?).
      split; simpl; try constructor; try (rewrite Forall_app; split); auto.
      1,2:destruct (is_noops_exp) eqn:Hnoops; repeat inv_bind; auto.
      + repeat solve_incl.
      + constructor. eapply fresh_ident_In in H.
        eapply in_or_app. right. unfold st_clocks, idck. simpl_In. exists (x0, (t, c)).
        split; auto.
        eapply st_follows_incl in H; eauto. repeat solve_st_follows.
      + repeat constructor; auto; simpl; try rewrite app_nil_r.
        * repeat solve_incl.
        * rewrite clockof_annot, Hsingl; simpl.
          constructor; auto.
          eapply fresh_ident_In in H.
          eapply in_or_app. right. solve_In.
          2:eapply st_follows_incl in H; eauto; repeat solve_st_follows.
          reflexivity.
    Qed.

    Hypothesis Hiface : global_iface_eq G1 G2.

    Lemma instck_refines : forall bck sub1 sub2 ck ck',
        (forall x y, sub1 x = Some y -> sub2 x = Some y) ->
        instck bck sub1 ck = Some ck' ->
        instck bck sub2 ck = Some ck'.
    Proof.
      intros * Hsub. revert ck'.
      induction ck; intros * Hinst; simpl in *; auto.
      cases_eqn Heq.
      - inv Hinst.
        specialize (IHck _ eq_refl). inv IHck.
        apply Hsub in Heq0. rewrite Heq0 in Heq2. inv Heq2; auto.
      - apply Hsub in Heq0. rewrite Heq0 in Heq2. inv Heq2.
      - specialize (IHck _ eq_refl). inv IHck.
    Qed.

    Lemma WellInstantiated_refines1 : forall bck sub1 sub2 x ck1 ck2,
        (forall x y, sub1 x = Some y -> sub2 x = Some y) ->
        sub2 x = None ->
        WellInstantiated bck sub1 (x, ck1) (ck2, None) ->
        WellInstantiated bck sub2 (x, ck1) (ck2, None).
    Proof.
      intros * Hsub1 Hsub2 (Hs&Hinst); simpl in *.
      split; eauto using instck_refines; simpl.
    Qed.

    Lemma WellInstantiated_refines2 : forall bck sub1 sub2 x ck1 ck2 y,
        (forall x y, sub1 x = Some y -> sub2 x = Some y) ->
        WellInstantiated bck sub1 (x, ck1) (ck2, Some y) ->
        WellInstantiated bck sub2 (x, ck1) (ck2, Some y).
    Proof.
      intros * Hsub1 (Hs&Hinst); simpl in *.
      split; eauto using instck_refines; simpl.
    Qed.

    Lemma WellInstantiated_refines3 : forall bck sub1 sub2 x ck1 ck2 y,
        (forall x y, sub1 x = Some y -> sub2 x = Some y) ->
        sub2 x = Some y ->
        WellInstantiated bck sub1 (x, ck1) (ck2, None) ->
        WellInstantiated bck sub2 (x, ck1) (ck2, Some y).
    Proof.
      intros * Hsub1 Hsub2 (Hs&Hinst); simpl in *.
      split; eauto using instck_refines; simpl.
    Qed.

    Fact unnest_exp_wc : forall vars e is_control es' eqs' st st',
        wc_exp G1 (vars++st_clocks st) e ->
        unnest_exp G1 is_control e st = (es', eqs', st') ->
        Forall (wc_exp G2 (vars++st_clocks st')) es' /\
        Forall (wc_equation G2 (vars++st_clocks st')) eqs'.
    Proof with eauto with norm lclocking.
      Local Ltac solve_mmap2 :=
        solve_forall;
        match goal with
        | Hnorm : unnest_exp _ _ _ _ = _, H : context [unnest_exp _ _ _ _ = _ -> _] |- _ =>
          eapply H in Hnorm as [? ?]; eauto;
          try split; try solve_forall; repeat solve_incl
        end.
      induction e using exp_ind2; intros is_control es' eqs' st st' Hwc Hnorm;
        repeat inv_bind. 11:inv Hwc.
      - (* const *) repeat constructor.
      - (* enum *) repeat constructor.
      - (* var *)
        repeat constructor...
        inv Hwc; econstructor; eauto.
      - (* unop *)
        inv Hwc.
        assert (length x = numstreams e) as Hlen by eauto with norm lclocking.
        rewrite <- length_clockof_numstreams, H4 in Hlen; simpl in Hlen.
        singleton_length.
        assert (Hnorm:=H); eapply IHe in H as [Hwc1 Hwc1']; eauto.
        repeat econstructor...
        + inv Hwc1; eauto.
        + eapply unnest_exp_clockof in Hnorm; simpl in Hnorm; eauto with lclocking.
          rewrite app_nil_r, H4 in Hnorm...
      - (* binop *)
        inv Hwc. repeat inv_bind.
        assert (length x = numstreams e1) as Hlen1 by eauto with norm lclocking.
        rewrite <- length_clockof_numstreams, H7 in Hlen1; simpl in Hlen1.
        assert (length x2 = numstreams e2) as Hlen2 by eauto with norm lclocking.
        rewrite <- length_clockof_numstreams, H8 in Hlen2; simpl in Hlen2. repeat singleton_length.
        assert (Hnorm1:=H); eapply IHe1 in H as [Hwc1 Hwc1']; eauto.
        assert (Hnorm2:=H0); eapply IHe2 in H0 as [Hwc2 Hwc2']; eauto. 2:repeat solve_incl.
        repeat econstructor...
        + inv Hwc1. repeat solve_incl.
        + inv Hwc2...
        + eapply unnest_exp_clockof in Hnorm1; simpl in Hnorm1; eauto with lclocking.
          rewrite app_nil_r, H7 in Hnorm1...
        + eapply unnest_exp_clockof in Hnorm2; simpl in Hnorm2; eauto with lclocking.
          rewrite app_nil_r, H8 in Hnorm2...
        + apply Forall_app; split; auto.
          solve_forall. repeat solve_incl.
      - (* fby *)
        repeat inv_bind.
        inv Hwc.
        assert (Hnorm1:=H1). eapply mmap2_wc with (vars0:=vars++st_clocks x1) in H1 as [Hwt1 Hwt1']...
        assert (Hnorm2:=H2). eapply mmap2_wc with (vars0:=vars++st_clocks x4) in H2 as [Hwt2 Hwt2']...
        2,3:solve_mmap2.
        repeat rewrite Forall_app. repeat split.
        3-4:solve_forall; repeat solve_incl.
        + eapply idents_for_anns_wc in H3...
        + assert (Forall (wc_exp G2 (vars++st_clocks st')) (unnest_fby (concat x2) (concat x6) a)) as Hwcfby.
          { rewrite Forall2_eq in H9, H10.
            eapply unnest_fby_wc_exp...
            1-2:solve_forall; repeat solve_incl.
            + eapply mmap2_unnest_exp_clocksof'' in Hnorm1... congruence.
            + eapply mmap2_unnest_exp_clocksof'' in Hnorm2... congruence. }
          remember (unnest_fby _ _ _) as fby.
          assert (length (concat x2) = length a) as Hlen1.
          { eapply mmap2_unnest_exp_length in Hnorm1...
            apply Forall2_length in H9.
            repeat simpl_length; erewrite <- map_length, <- typesof_annots; solve_length. }
          assert (length (concat x6) = length a) as Hlen2.
          { eapply mmap2_unnest_exp_length in Hnorm2...
            apply Forall2_length in H10.
            repeat simpl_length. erewrite <- map_length, <- typesof_annots; solve_length. }
          assert (length fby = length x5).
          { rewrite Heqfby, unnest_fby_length...
            eapply idents_for_anns_length in H3... }
          assert (Forall2 (fun '(_, ck) e => clockof e = [ck]) (map snd x5) fby) as Htys.
          { eapply idents_for_anns_values in H3; subst.
            specialize (unnest_fby_annot' _ _ _ Hlen1 Hlen2) as Hanns; eauto. clear - Hanns.
            eapply Forall2_swap_args. solve_forall.
            rewrite clockof_annot, H1; auto. }
          eapply mk_equations_Forall. solve_forall.
          repeat constructor; eauto; simpl; rewrite app_nil_r.
          * rewrite H5. repeat constructor.
            eapply idents_for_anns_incl_clocks in H3.
            apply in_or_app, or_intror, H3. simpl_In. eexists; split; eauto. reflexivity.
      - (* arrow *)
        repeat inv_bind.
        inv Hwc.
        assert (Hnorm1:=H1). eapply mmap2_wc with (vars0:=vars++st_clocks x1) in H1 as [Hwt1 Hwt1']...
        assert (Hnorm2:=H2). eapply mmap2_wc with (vars0:=vars++st_clocks x4) in H2 as [Hwt2 Hwt2']...
        2,3:solve_mmap2.
        repeat rewrite Forall_app. repeat split.
        3-4:solve_forall; repeat solve_incl.
        + eapply idents_for_anns_wc in H3...
        + assert (Forall (wc_exp G2 (vars++st_clocks st')) (unnest_arrow (concat x2) (concat x6) a)) as Hwcarrow.
          { rewrite Forall2_eq in H9, H10.
            eapply unnest_arrow_wc_exp...
            1-2:solve_forall; repeat solve_incl.
            + eapply mmap2_unnest_exp_clocksof'' in Hnorm1... congruence.
            + eapply mmap2_unnest_exp_clocksof'' in Hnorm2... congruence. }
          remember (unnest_arrow _ _ _) as arrow.
          assert (length (concat x2) = length a) as Hlen1.
          { eapply mmap2_unnest_exp_length in Hnorm1...
            apply Forall2_length in H9.
            repeat simpl_length; erewrite <- map_length, <- typesof_annots; solve_length. }
          assert (length (concat x6) = length a) as Hlen2.
          { eapply mmap2_unnest_exp_length in Hnorm2...
            apply Forall2_length in H10.
            repeat simpl_length. erewrite <- map_length, <- typesof_annots; solve_length. }
          assert (length arrow = length x5).
          { rewrite Heqarrow, unnest_arrow_length...
            eapply idents_for_anns_length in H3... }
          assert (Forall2 (fun '(_, ck) e => clockof e = [ck]) (map snd x5) arrow) as Htys.
          { eapply idents_for_anns_values in H3; subst.
            specialize (unnest_arrow_annot' _ _ _ Hlen1 Hlen2) as Hanns; eauto. clear - Hanns.
            eapply Forall2_swap_args. solve_forall.
            rewrite clockof_annot, H1; auto. }
          eapply mk_equations_Forall. solve_forall.
          repeat constructor; eauto; simpl; rewrite app_nil_r.
          rewrite H5. repeat constructor.
          eapply idents_for_anns_incl_clocks in H3.
          apply in_or_app, or_intror, H3. simpl_In. eexists; split; eauto. reflexivity.
      - (* when *)
        inv Hwc; repeat inv_bind.
        assert (H0':=H0). eapply mmap2_wc with (vars0:=vars++st_clocks st') in H0' as [Hwc1 Hwc1']...
        2:solve_mmap2.
        split; auto.
        apply unnest_when_wc_exp...
        + eapply mmap2_unnest_exp_length in H0...
          solve_length.
        + repeat solve_incl.
        + eapply mmap2_unnest_exp_clocksof''' in H0...
      - (* merge *)
        inv Hwc; repeat inv_bind.
        assert (Hnorm1:=H0). eapply mmap2_wc' in H0 as (?&?).
        2:(intros; repeat inv_bind; destruct a; repeat solve_st_follows).
        2:{ solve_forall; repeat inv_bind.
            eapply mmap2_wc with (vars0:=vars++st_clocks x2) in H5... solve_mmap2. }
        assert (Forall (wc_exp G2 (vars++st_clocks st')) (unnest_merge (x0, tx) x tys ck)) as Hwcexp.
        { eapply unnest_merge_wc_exp...
          + destruct is_control; repeat solve_incl.
          + eapply mmap2_length_1 in Hnorm1.
            intro contra; subst. destruct es; simpl in *; try congruence.
          + apply mmap2_mmap2_unnest_exp_length in Hnorm1. 2:solve_forall...
            clear - Hnorm1 H7.
            induction Hnorm1; inv H7; constructor; auto.
            destruct y; simpl in *. now rewrite H2, H, length_clocksof_annots.
          + eapply Forall_concat in H0. rewrite Forall_map in H0.
            solve_forall. solve_forall. destruct is_control; repeat solve_incl.
          + eapply mmap2_mmap2_unnest_exp_clocksof1; eauto. }
        destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split; eauto.
        3:solve_forall; repeat solve_incl.
        + eapply idents_for_anns_wc in H1...
        + assert (Forall (fun e : exp => clockof e = [ck]) (unnest_merge (x0, tx) x tys ck)) as Hnck.
          { eapply unnest_merge_clockof; solve_length. }
          eapply mk_equations_Forall. solve_forall.
          2:(rewrite unnest_merge_length; eapply idents_for_anns_length in H1; solve_length).
          repeat constructor; simpl. 2:rewrite app_nil_r.
          * repeat constructor...
          * rewrite H7; simpl. repeat constructor.
            assert (H':=H1). apply idents_for_anns_values in H'.
            apply idents_for_anns_incl_clocks in H1.
            apply in_or_app; right. apply H1.
            simpl_In. exists (i, (t, ck)). split; auto.
            assert (In (t, c) (map snd x3)) by solve_In.
            setoid_rewrite H' in H9. simpl_In; auto.
      - (* case *)
        inv Hwc; repeat inv_bind.
        assert (st_follows x1 x4) as Hfollows by repeat solve_st_follows.
        assert (st_follows x7 st') as Hfollows2 by (destruct is_control; repeat solve_st_follows).
        assert (st_follows x4 st') as Hfollows3 by (destruct d; repeat solve_st_follows).
        assert (Hnorm0:=H1). eapply IHe in H1 as (Hwc0&?)...
        assert (Hnorm1:=H2). eapply mmap2_wc' in H2 as (?&?).
        2:(intros; repeat inv_bind; destruct a; repeat solve_st_follows).
        2:{ solve_forall; repeat inv_bind.
            eapply mmap2_wc with (vars0:=vars++st_clocks x4) in H9... solve_mmap2. }
        assert (length x = 1); try singleton_length.
        { eapply unnest_exp_length in Hnorm0...
          now rewrite Hnorm0, <-length_clockof_numstreams, H6. }
        apply Forall_singl in Hwc0.
        assert (Forall (wc_exp G2 (vars++st_clocks st')) (unnest_case e0 x2 x5 tys ck)) as Hwcexp.
        { eapply unnest_case_wc_exp...
          + repeat solve_incl.
          + apply unnest_exp_clockof in Hnorm0; simpl in *...
            rewrite app_nil_r in Hnorm0. congruence.
          + eapply mmap2_length_1 in Hnorm1.
            intro contra; subst. destruct es; simpl in *; try congruence.
          + apply mmap2_mmap2_unnest_exp_length in Hnorm1. 2:solve_forall...
            clear - Hnorm1 H10.
            induction Hnorm1; constructor; inv H10; eauto with datatypes.
            destruct y; simpl in *; auto.
            now rewrite H, H2, length_clocksof_annots.
          + eapply Forall_concat in H2. rewrite Forall_map in H2.
            solve_forall. solve_forall. destruct is_control; repeat solve_incl.
          + eapply mmap2_mmap2_unnest_exp_clocksof2 in Hnorm1; eauto.
          + destruct d; repeat inv_bind; simpl; auto.
            rewrite length_clocksof_annots. eapply mmap2_unnest_exp_annots_length in H3...
            rewrite H3, <-length_clocksof_annots, <-H13; auto.
          + destruct d; repeat inv_bind; simpl; auto.
            eapply mmap2_wc in H3 as (?&?)... solve_forall.
            eapply H8 in H9 as (?&?); eauto. 2:eapply Forall_forall in H11; eauto.
            split; (eapply Forall_impl; [|eauto]; intros). 1-3:repeat solve_incl.
          + destruct d; repeat inv_bind; simpl; auto.
            eapply mmap2_unnest_exp_clocksof''' in H3; eauto.
        }
        assert (Forall (wc_equation G2 (vars ++ st_clocks st')) x6) as Hwcd'.
        {  destruct d; repeat inv_bind; simpl; auto.
          eapply mmap2_wc in H3 as (?&?)... solve_forall.
          eapply H8 in H9 as (?&?); eauto. 2:eapply Forall_forall in H11; eauto.
          split; (eapply Forall_impl; [|eauto]; intros). 1-3:repeat solve_incl. }
        destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split; eauto.
        1,2,5,6:solve_forall; repeat solve_incl.
        + eapply idents_for_anns_wc in H4...
        + assert (Forall (fun e : exp => clockof e = [ck]) (unnest_case e0 x2 x5 tys ck)) as Hnck.
          { eapply unnest_case_clockof; solve_length. }
          eapply mk_equations_Forall. solve_forall.
          2:(rewrite unnest_case_length; eapply idents_for_anns_length in H4; solve_length).
          repeat constructor; simpl. 2:rewrite app_nil_r.
          * repeat constructor...
          * rewrite H10; simpl. repeat constructor.
            assert (H':=H4). apply idents_for_anns_values in H'.
            apply idents_for_anns_incl_clocks in H4.
            apply in_or_app; right. apply H4.
            simpl_In. exists (i, (t, c)). split; auto.
            assert (In (t, c) (map snd x)) as Hin' by solve_In.
            setoid_rewrite H' in Hin'. simpl_In; auto.
      - (* app *)
        assert (st_follows x4 x7) as Hfollows by repeat solve_st_follows.
        eapply unnest_resets_wc in H3 as (Hck2&Hwt2&Hwt2'); eauto.
        2:solve_mmap2. 2:solve_forall; repeat solve_incl.
        assert (Hnorm:=H1). eapply mmap2_wc with (vars0:=vars++st_clocks x1) in H1 as [Hwc1 Hwc1']...
        2:solve_mmap2.

        assert (length (find_node_incks G1 f) = length (concat x6)) as Hlen1.
        { unfold find_node_incks. rewrite H11.
          eapply Forall2_length in H12. rewrite map_length.
          eapply mmap2_unnest_exp_length in Hnorm... rewrite length_nclocksof_annots in H12.
          rewrite length_idck, length_idty in H12. congruence. }
        assert (Forall (fun e : exp => numstreams e = 1) (concat x6)) as Hnum.
        { eapply mmap2_unnest_exp_numstreams; eauto. }

        destruct Hiface as (_&Hiface').
        specialize (Hiface' f). rewrite H11 in Hiface'. inv Hiface'.
        destruct H5 as (?&?&Hin&Hout).

        assert (length (n_in n) = length (nclocksof x2)) as Hlen2.
        { apply Forall2_length in H12. repeat setoid_rewrite map_length in H12. rewrite H12.
          eapply unnest_noops_exps_nclocksof2 with (es:=es), Forall2_length in H2; eauto.
          rewrite Hlen1... }

        remember (Env.from_list (map_filter (fun '(x, (_, ox)) => option_map (fun xc => (x, xc)) ox)
                                            (combine (map fst (n_in n)) (nclocksof x2)))) as sub2.
        assert (Forall2 (fun '(x, _) '(ck, ox) => LiftO (Env.find x sub2 = None) (fun x' => Env.MapsTo x x' sub2) ox) (idck (idty (n_in n))) (nclocksof x2)) as Hsub2.
        { apply Forall2_forall; split. 2:repeat setoid_rewrite map_length; auto.
          intros (?&?) (?&?) Hin'.
          assert (In (k, (c0, o)) (combine (map fst (n_in n)) (nclocksof x2))) as Hin2.
          { repeat setoid_rewrite combine_map_fst in Hin'. rewrite map_map in Hin'.
            eapply in_map_iff in Hin' as (((?&(?&?)&?)&?&?)&Heq&?); inv Heq.
            rewrite combine_map_fst. eapply in_map_iff. do 2 esplit; eauto. simpl; auto. }
          assert (NoDupMembers (combine (map fst (n_in n)) (nclocksof x2))) as Hnd1.
          { rewrite fst_NoDupMembers, combine_map_fst', <-fst_NoDupMembers. 2:now rewrite map_length.
            pose proof (n_nodup n) as (Hnd1&_). apply NoDupMembers_app_l in Hnd1; auto. }
          destruct o; simpl; subst.
          - eapply Env.find_In_from_list.
            2:{ clear - Hnd1. remember (combine _ _) as comb. clear - Hnd1.
                induction comb as [|(?&?&?)]; simpl in *; inv Hnd1. constructor.
                destruct (option_map _ _) as [(?&?)|] eqn:Hopt; simpl; auto.
                eapply option_map_inv in Hopt as (?&?&Heq); inv Heq.
                econstructor; auto. intro contra. apply H1.
                apply fst_InMembers, in_map_iff in contra as ((?&?)&?&Hin); subst.
                apply map_filter_In' in Hin as ((?&?&?)&Hin&Hopt). apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
                apply In_InMembers in Hin; auto.
            }
            eapply map_filter_In; eauto.
          - destruct (Env.find _ _) eqn:Hfind; auto. exfalso.
            eapply Env.from_list_find_In, map_filter_In' in Hfind as ((?&?&?)&Hin3&Hopt).
            apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
            eapply NoDupMembers_det in Hin2; eauto. inv Hin2.
        }

        repeat constructor; simpl in *... 2:econstructor...
        + eapply idents_for_anns_wc...
        + eapply unnest_noops_exps_wc with (vars:=vars) in H2 as (?&?)...
          solve_forall; repeat solve_incl.
        + solve_forall; repeat solve_incl.
        + instantiate (1:=fun x => match (sub x) with
                                | Some y => Some y
                                | _ => Env.find x sub2
                      end).
          eapply unnest_noops_exps_nclocksof2 with (es:=es) in H2; eauto.
          2:{ rewrite Hlen1; eauto... }
          eapply Forall2_trans_ex in H2; eauto. eapply Forall2_Forall2 in Hsub2; eauto. clear H2. rewrite <-Hin.
          eapply Forall2_impl_In; [|eauto]; intros (?&?) (?&?) ?? (((?&?)&?&Hwi&?&?)&?); subst.
          destruct o0; simpl in *; subst. eapply WellInstantiated_refines2; eauto.
          2:destruct o; [eapply WellInstantiated_refines3|eapply WellInstantiated_refines1]; eauto.
          1,2,4:intros ?? Hsub; rewrite Hsub; auto.
          1,2:destruct Hwi as (Hwi1&_); simpl in *; rewrite Hwi1; simpl; eauto.
        + erewrite <-Hout, idents_for_anns_values...
          rewrite Forall2_map_2 in *.
          eapply Forall2_impl_In; [|eauto]; intros (?&?) (?&?) ?? Hwi.
          eapply WellInstantiated_refines1; eauto.
          * intros ?? Hsub. rewrite Hsub; auto.
          * destruct Hwi as (Hwi1&_); simpl in *. rewrite Hwi1. subst.
            destruct (Env.find i _) eqn:Hfind; auto. exfalso.
            eapply Env.from_list_find_In, map_filter_In' in Hfind as ((?&?&?)&?&Hopt).
            apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
            pose proof (n_nodup n) as (Hnd&_). eapply NoDupMembers_app_InMembers in Hnd. eapply Hnd.
            rewrite fst_InMembers, <-map_fst_idty, <-map_fst_idck. eapply in_map_iff; do 2 esplit; eauto.
            apply In_InMembers, fst_InMembers in H8. erewrite combine_map_fst', <-fst_InMembers in H8; eauto.
            now rewrite map_length.
        + rewrite app_nil_r, map_map, Forall2_map_1, Forall2_map_2, <- Forall2_same.
          eapply idents_for_anns_incl_clocks in H4.
          apply Forall_forall; intros.
          apply in_or_app; right. apply H4.
          rewrite in_map_iff. exists x; split; auto. destruct x as [? [? ?]]; auto.
        + repeat rewrite Forall_app; repeat split.
          2:eapply unnest_noops_exps_wc in H2 as (?&?)...
          1-3:solve_forall; repeat solve_incl.
    Qed.

    Corollary mmap2_unnest_exp_wc : forall vars is_control es es' eqs' st st',
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        mmap2 (unnest_exp G1 is_control) es st = (es', eqs', st') ->
        Forall (wc_exp G2 (vars++st_clocks st')) (concat es') /\
        Forall (wc_equation G2 (vars++st_clocks st')) (concat eqs').
    Proof.
      intros * Hwt Hmap.
      eapply mmap2_wc in Hmap; eauto with norm.
      solve_forall. eapply unnest_exp_wc with (vars:=vars) in H1 as [? ?]; eauto.
      split. 1,2:solve_forall. 1,2,3:repeat solve_incl.
    Qed.

    Corollary unnest_exps_wc : forall vars es es' eqs' st st',
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        unnest_exps G1 es st = (es', eqs', st') ->
        Forall (wc_exp G2 (vars++st_clocks st')) es' /\
        Forall (wc_equation G2 (vars++st_clocks st')) eqs'.
    Proof.
      intros * Hwt Hmap.
      unfold unnest_exps in Hmap; repeat inv_bind.
      eapply mmap2_unnest_exp_wc in H; eauto.
    Qed.

    Corollary mmap2_mmap2_unnest_exp_wc : forall vars is_control (es: list (enumtag * _)) es' eqs' st st',
        Forall (fun es => Forall (wc_exp G1 (vars++st_clocks st)) (snd es)) es ->
        mmap2 (fun '(i, es) => bind2 (mmap2 (unnest_exp G1 is_control) es) (fun es' eqs' => ret (i, concat es', concat eqs'))) es st = (es', eqs', st') ->
        Forall (fun es => Forall (wc_exp G2 (vars++st_clocks st')) (snd es)) es' /\
        Forall (wc_equation G2 (vars++st_clocks st')) (concat eqs').
    Proof.
      intros * Hwt Hmap.
      eapply mmap2_wc' with (vars0:=vars++st_clocks st') in Hmap as (Hwc1&Hwc2); eauto.
      - split; auto.
        rewrite <-Forall_concat, Forall_map in Hwc1. eauto.
      - intros ?? (?&?) (?&?) ??. repeat solve_st_follows.
      - eapply Forall_forall; intros (?&?) Hin * ???.
        repeat inv_bind.
        eapply mmap2_unnest_exp_wc with (vars:=vars) in H as (Hwc1&Hwc2); eauto. split.
        3:eapply Forall_forall in Hwt; eauto.
        1-3:eapply Forall_impl; [|eauto]; intros; repeat solve_incl.
    Qed.

    Fact unnest_rhs_wc : forall vars e es' eqs' st st',
        wc_exp G1 (vars++st_clocks st) e ->
        unnest_rhs G1 e st = (es', eqs', st') ->
        Forall (wc_exp G2 (vars++st_clocks st')) es' /\
        Forall (wc_equation G2 (vars++st_clocks st')) eqs'.
    Proof with eauto with norm lclocking.
      intros * Hwc Hnorm.
      destruct e; unfold unnest_rhs in Hnorm;
        try (solve [eapply unnest_exp_wc in Hnorm; eauto]); repeat inv_bind. 3:inv Hwc.
      - (* fby *)
        inv Hwc.
        rewrite Forall2_eq in H6, H7.
        repeat inv_bind.
        assert (H':=H). eapply unnest_exps_wc in H' as [Hwc1 Hwc1']...
        assert (H0':=H0). eapply unnest_exps_wc with (vars:=vars) in H0' as [Hwc2 Hwc2']...
        2:solve_forall; repeat solve_incl.
        repeat rewrite Forall_app; repeat split.
        2-3:solve_forall; repeat solve_incl.
        eapply unnest_fby_wc_exp...
        + solve_forall; repeat solve_incl.
        + unfold unnest_exps in H; repeat inv_bind.
          eapply mmap2_unnest_exp_clocksof'' in H... congruence.
        + unfold unnest_exps in H0; repeat inv_bind.
          eapply mmap2_unnest_exp_clocksof'' in H0... congruence.
      - (* arrow *)
        inv Hwc.
        rewrite Forall2_eq in H6, H7.
        repeat inv_bind.
        assert (H':=H). eapply unnest_exps_wc in H' as [Hwc1 Hwc1']...
        assert (H0':=H0). eapply unnest_exps_wc with (vars:=vars) in H0' as [Hwc2 Hwc2']...
        2:solve_forall; repeat solve_incl.
        repeat rewrite Forall_app; repeat split.
        2-3:solve_forall; repeat solve_incl.
        eapply unnest_arrow_wc_exp...
        + solve_forall; repeat solve_incl.
        + unfold unnest_exps in H; repeat inv_bind.
          eapply mmap2_unnest_exp_clocksof'' in H... congruence.
        + unfold unnest_exps in H0; repeat inv_bind.
          eapply mmap2_unnest_exp_clocksof'' in H0... congruence.
      - (* app *)
        assert (Hnorm:=H). eapply unnest_exps_wc in H as [Hwc1 Hwc1']...
        assert (st_follows x4 st') as Hfollows by repeat solve_st_follows.
        eapply unnest_resets_wc with (vars:=vars) in H1 as [Hwc2 [Hwc2' Hwc2'']]...
        2,3:solve_forall. 2:eapply unnest_exp_wc in H3; eauto. 2,3:repeat solve_incl.

        assert (length (find_node_incks G1 i) = length x) as Hlen1.
        { unfold find_node_incks. rewrite H8.
          eapply Forall2_length in H9. rewrite map_length.
          eapply unnest_exps_length in Hnorm; eauto...
          rewrite length_nclocksof_annots, length_idck, length_idty in H9.
          congruence. }
        assert (Forall (fun e : exp => numstreams e = 1) x) as Hnum.
        { eapply unnest_exps_numstreams; eauto. }

        destruct Hiface as (_&Hiface').
        specialize (Hiface' i). rewrite H8 in Hiface'. inv Hiface'.
        destruct H2 as (?&?&Hin&Hout).

        assert (length (n_in n) = length (nclocksof x2)) as Hlen2.
        { apply Forall2_length in H9. repeat setoid_rewrite map_length in H9. rewrite H9.
          unfold unnest_exps in Hnorm; repeat inv_bind.
          eapply unnest_noops_exps_nclocksof2, Forall2_length in H0; eauto.
          rewrite Hlen1; eauto... }

        unfold unnest_exps in *. repeat inv_bind.
        remember (Env.from_list (map_filter (fun '(x, (_, ox)) => option_map (fun xc => (x, xc)) ox)
                                            (combine (map fst (n_in n)) (nclocksof x2)))) as sub2.
        assert (Forall2 (fun '(x, _) '(ck, ox) => LiftO (Env.find x sub2 = None) (fun x' => Env.MapsTo x x' sub2) ox) (idck (idty (n_in n))) (nclocksof x2)) as Hsub2.
        { apply Forall2_forall; split. 2:repeat setoid_rewrite map_length; auto.
          intros (?&?) (?&?) Hin'.
          assert (In (k, (c0, o)) (combine (map fst (n_in n)) (nclocksof x2))) as Hin2.
          { repeat setoid_rewrite combine_map_fst in Hin'. rewrite map_map in Hin'.
            eapply in_map_iff in Hin' as (((?&(?&?)&?)&?&?)&Heq&?); inv Heq.
            rewrite combine_map_fst. eapply in_map_iff. do 2 esplit; eauto. simpl; auto. }
          assert (NoDupMembers (combine (map fst (n_in n)) (nclocksof x2))) as Hnd1.
          { rewrite fst_NoDupMembers, combine_map_fst', <-fst_NoDupMembers. 2:now rewrite map_length.
            pose proof (n_nodup n) as (Hnd1&_). apply NoDupMembers_app_l in Hnd1; auto. }
          destruct o; simpl; subst.
          - eapply Env.find_In_from_list.
            2:{ clear - Hnd1. remember (combine _ _) as comb. clear - Hnd1.
                induction comb as [|(?&?&?)]; simpl in *; inv Hnd1. constructor.
                destruct (option_map _ _) as [(?&?)|] eqn:Hopt; simpl; auto.
                eapply option_map_inv in Hopt as (?&?&Heq); inv Heq.
                econstructor; auto. intro contra. apply H1.
                apply fst_InMembers, in_map_iff in contra as ((?&?)&?&Hin); subst.
                apply map_filter_In' in Hin as ((?&?&?)&Hin&Hopt). apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
                apply In_InMembers in Hin; auto.
            }
            eapply map_filter_In; eauto.
          - destruct (Env.find _ _) eqn:Hfind; auto. exfalso.
            eapply Env.from_list_find_In, map_filter_In' in Hfind as ((?&?&?)&Hin3&Hopt).
            apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
            eapply NoDupMembers_det in Hin2; eauto. inv Hin2.
        }

        repeat constructor; simpl in *... econstructor...
        + eapply unnest_noops_exps_wc with (vars:=vars) in H0 as (?&?)...
          solve_forall; repeat solve_incl.
        + instantiate (1:=fun x => match (sub x) with
                                | Some y => Some y
                                | _ => Env.find x sub2
                      end).
          eapply unnest_noops_exps_nclocksof2 with (es:=l) in H0; eauto.
          2:{ rewrite Hlen1; eauto... }
          eapply Forall2_trans_ex in H0; eauto. eapply Forall2_Forall2 in Hsub2; eauto. clear H0. rewrite <-Hin.
          eapply Forall2_impl_In; [|eauto]; intros (?&?) (?&?) ?? (((?&?)&?&Hwi&?&?)&?); subst.
          destruct o0; simpl in *; subst. eapply WellInstantiated_refines2; eauto.
          2:destruct o; [eapply WellInstantiated_refines3|eapply WellInstantiated_refines1]; eauto.
          1,2,4:intros ?? Hsub; rewrite Hsub; auto.
          1,2:destruct Hwi as (Hwi1&_); simpl in *; rewrite Hwi1; simpl; eauto.
        + rewrite Forall2_map_2 in *. rewrite <-Hout.
          eapply Forall2_impl_In; [|eauto]; intros (?&?) (?&?) ?? Hwi.
          eapply WellInstantiated_refines1; eauto.
          * intros ?? Hsub. rewrite Hsub; auto.
          * destruct Hwi as (Hwi1&_); simpl in *. rewrite Hwi1. subst.
            destruct (Env.find i0 _) eqn:Hfind; auto. exfalso.
            eapply Env.from_list_find_In, map_filter_In' in Hfind as ((?&?&?)&?&Hopt).
            apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
            pose proof (n_nodup n) as (Hnd&_). eapply NoDupMembers_app_InMembers in Hnd. eapply Hnd.
            rewrite fst_InMembers, <-map_fst_idty, <-map_fst_idck. eapply in_map_iff; do 2 esplit; eauto.
            apply In_InMembers, fst_InMembers in H12. erewrite combine_map_fst', <-fst_InMembers in H12; eauto.
            now rewrite map_length.
        + repeat rewrite Forall_app; repeat split.
          2:eapply unnest_noops_exps_wc in H0 as (?&?)...
          1-3:solve_forall; repeat solve_incl.
    Qed.

    Corollary unnest_rhss_wc : forall vars es es' eqs' st st',
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        unnest_rhss G1 es st = (es', eqs', st') ->
        Forall (wc_exp G2 (vars++st_clocks st')) es' /\
        Forall (wc_equation G2 (vars++st_clocks st')) eqs'.
    Proof.
      intros * Hwc Hnorm.
      unfold unnest_rhss in Hnorm; repeat inv_bind.
      eapply mmap2_wc in H; eauto with norm lclocking.
      solve_forall.
      eapply unnest_rhs_wc with (vars:=vars) in H2 as [? ?]; eauto.
      split. 1,2:solve_forall. 1,2,3:repeat solve_incl.
    Qed.

    Fact unnest_equation_wc_eq : forall vars e eqs' st st',
        wc_equation G1 (vars++st_clocks st) e ->
        unnest_equation G1 e st = (eqs', st') ->
        Forall (wc_equation G2 (vars++st_clocks st')) eqs'.
    Proof with eauto with norm lclocking.
      intros vars [xs es] eqs' st st' Hwc Hnorm.
      unfold unnest_equation in Hnorm. repeat inv_bind.
      inv Hwc.
      - (* app *)
        assert (length xs = length anns) as Hlen.
        { eapply Forall3_length in H6 as (_&Hlen). rewrite map_length in Hlen; auto. }

        unfold unnest_rhss in H; repeat inv_bind.
        rewrite firstn_all2, skipn_all2. 2,3:setoid_rewrite Hlen; reflexivity.

        assert (Hnorm:=H). eapply unnest_exps_wc in H as [Hwc1 Hwc1']...
        assert (st_follows st x6) as Hfollows by repeat solve_st_follows.
        assert (Hnr:=H1). eapply unnest_resets_wc with (vars:=vars) in H1 as [Hwc2 [Hwc2' Hwc2'']]...
        2,3:solve_forall. 2:eapply unnest_exp_wc in H7; eauto. 2,3:repeat solve_incl.

        assert (length (find_node_incks G1 f) = length x1) as Hlen1.
        { unfold find_node_incks. rewrite H4.
          eapply Forall2_length in H5. rewrite map_length.
          eapply unnest_exps_length in Hnorm...
          rewrite length_nclocksof_annots, length_idck, length_idty in H5.
          congruence. }
        assert (Forall (fun e : exp => numstreams e = 1) x1) as Hnum.
        { eapply unnest_exps_numstreams; eauto. }

        destruct Hiface as (_&Hiface').
        specialize (Hiface' f). rewrite H4 in Hiface'. inv Hiface'.
        destruct H9 as (?&?&Hin&Hout).

        assert (length (n_in n) = length (nclocksof x4)) as Hlen2.
        { apply Forall2_length in H5. repeat setoid_rewrite map_length in H5. rewrite H5.
          unfold unnest_exps in Hnorm; repeat inv_bind.
          eapply unnest_noops_exps_nclocksof2, Forall2_length in H0; eauto.
          rewrite Hlen1... }

        unfold unnest_exps in *. repeat inv_bind.
        remember (Env.from_list (map_filter (fun '(x, (_, ox)) => option_map (fun xc => (x, xc)) ox)
                                            (combine (map fst (n_in n)) (nclocksof x4)))) as sub2.
        assert (Forall2 (fun '(x, _) '(ck, ox) => LiftO (Env.find x sub2 = None) (fun x' => Env.MapsTo x x' sub2) ox) (idck (idty (n_in n))) (nclocksof x4)) as Hsub2.
        { apply Forall2_forall; split. 2:repeat setoid_rewrite map_length; auto.
          intros (?&?) (?&?) Hin'.
          assert (In (k, (c0, o)) (combine (map fst (n_in n)) (nclocksof x4))) as Hin2.
          { repeat setoid_rewrite combine_map_fst in Hin'. rewrite map_map in Hin'.
            eapply in_map_iff in Hin' as (((?&(?&?)&?)&?&?)&Heq&?); inv Heq.
            rewrite combine_map_fst. eapply in_map_iff. do 2 esplit; eauto. simpl; auto. }
          assert (NoDupMembers (combine (map fst (n_in n)) (nclocksof x4))) as Hnd1.
          { rewrite fst_NoDupMembers, combine_map_fst', <-fst_NoDupMembers. 2:now rewrite map_length.
            pose proof (n_nodup n) as (Hnd1&_). apply NoDupMembers_app_l in Hnd1; auto. }
          destruct o; simpl; subst.
          - eapply Env.find_In_from_list.
            2:{ clear - Hnd1. remember (combine _ _) as comb. clear - Hnd1.
                induction comb as [|(?&?&?)]; simpl in *; inv Hnd1. constructor.
                destruct (option_map _ _) as [(?&?)|] eqn:Hopt; simpl; auto.
                eapply option_map_inv in Hopt as (?&?&Heq); inv Heq.
                econstructor; auto. intro contra. apply H1.
                apply fst_InMembers, in_map_iff in contra as ((?&?)&?&Hin); subst.
                apply map_filter_In' in Hin as ((?&?&?)&Hin&Hopt). apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
                apply In_InMembers in Hin; auto.
            }
            eapply map_filter_In; eauto.
          - destruct (Env.find _ _) eqn:Hfind; auto. exfalso.
            eapply Env.from_list_find_In, map_filter_In' in Hfind as ((?&?&?)&Hin3&Hopt).
            apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
            eapply NoDupMembers_det in Hin2; eauto. inv Hin2.
        }

        repeat econstructor; simpl in *...
        + eapply unnest_noops_exps_wc with (vars:=vars) in H0 as (?&?)...
          solve_forall; repeat solve_incl.
        + instantiate (1:=fun x => match (sub x) with
                                | Some y => Some y
                                | _ => Env.find x sub2
                                end).
          eapply unnest_noops_exps_nclocksof2 with (es:=es0) in H0; eauto.
          2:{ rewrite Hlen1; eauto... }
          eapply Forall2_trans_ex in H0; eauto. eapply Forall2_Forall2 in Hsub2; eauto. clear H0. rewrite <-Hin.
          eapply Forall2_impl_In; [|eauto]; intros (?&?) (?&?) ?? (((?&?)&?&Hwi&?&?)&?); subst.
          destruct o0; simpl in *; subst. eapply WellInstantiated_refines2; eauto.
          2:destruct o; [eapply WellInstantiated_refines3|eapply WellInstantiated_refines1]; eauto.
          1,2,4:intros ?? Hsub; rewrite Hsub; auto.
          1,2:destruct Hwi as (Hwi1&_); simpl in *; rewrite Hwi1; simpl; eauto.
        + rewrite <-Hout.
          eapply Forall3_impl_In; [|eauto]; intros (?&?) ?? ??? Hwi.
          eapply WellInstantiated_refines2; eauto.
          intros ?? Hsub. rewrite Hsub; auto.
        + eapply Forall2_impl_In; [|eauto]; intros; simpl in *.
          repeat solve_incl.
        + rewrite app_nil_r. repeat rewrite Forall_app; repeat split.
          2:eapply unnest_noops_exps_wc in H0 as (?&?); eauto...
          1-3:solve_forall; repeat solve_incl.
      - (* general case *)
        assert (st_follows st st') as Hfollows by eauto with norm.
        assert (H':=H). eapply unnest_rhss_wc in H' as [Hwc1' Hwc1'']...
        apply Forall_app; split...
        rename H3 into Hwc2.
        replace (clocksof es) with (clocksof x) in Hwc2.
        2: { eapply unnest_rhss_clocksof in H... }
        clear - H2 Hwc2 Hwc1' Hfollows.
        revert es xs H2 Hwc2 Hwc1'.
        induction x; intros; simpl in *; try constructor.
        + inv Hwc2; simpl; auto.
        + inv Hwc1'.
          assert (length (firstn (numstreams a) xs) = length (clockof a)) as Hlen1.
          { apply Forall2_length in Hwc2. rewrite app_length in Hwc2.
            rewrite firstn_length, Hwc2, length_clockof_numstreams.
            apply Nat.min_l. lia. }
          rewrite <- (firstn_skipn (numstreams a) xs) in Hwc2.
          apply Forall2_app_split in Hwc2 as [Hwc2 _]...
          repeat constructor...
          simpl. rewrite app_nil_r.
          eapply Forall2_impl_In... intros; simpl in *. repeat solve_incl.
        + inv Hwc1'. eapply IHx...
          assert (length (firstn (numstreams a) xs) = length (clockof a)) as Hlen1.
          { apply Forall2_length in Hwc2. rewrite app_length in Hwc2.
            rewrite firstn_length, Hwc2, length_clockof_numstreams.
            apply Nat.min_l. lia. }
          rewrite <- (firstn_skipn (numstreams a) xs) in Hwc2.
          apply Forall2_app_split in Hwc2 as [_ Hwc2]...
    Qed.

    Lemma unnest_block_wc : forall vars d blocks' st st',
        wc_block G1 (vars++st_clocks st) d ->
        unnest_block G1 d st = (blocks', st') ->
        Forall (wc_block G2 (vars++st_clocks st')) blocks'.
    Proof.
      induction d using block_ind2; intros * Hwc Hun; inv Hwc;
        repeat inv_bind.
      - (* equation *)
        eapply unnest_equation_wc_eq in H; eauto.
        rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
        constructor; auto.
      - (* reset *)
        assert (st_follows x0 st') as Hfollows by (repeat solve_st_follows).
        eapply unnest_reset_wc with (vars:=vars) in H1 as (Hck1&Hwc1&Hwc1'); eauto.
        2:{ intros. eapply unnest_exp_wc in H6; eauto; repeat solve_incl. }
        2:repeat solve_incl.
        apply Forall_app; split.
        + clear - H H2 H0 H4 Hck1 Hwc1 Hfollows.
          revert st x x0 Hfollows H H0 H2 H4.
          induction blocks; intros * Hfollows Hf Hmap Hwc Hwc2; repeat inv_bind; simpl; auto;
            inv Hf; inv Hwc.
          rewrite map_app, Forall_app; split.
          * eapply H3 in H; eauto.
            rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
            econstructor; eauto.
            constructor; auto. repeat solve_incl.
          * eapply IHblocks; eauto.
            clear - H6 H. solve_forall. 1,2:repeat solve_incl.
        + rewrite Forall_map.
          eapply Forall_impl; [|eauto]; intros; constructor; auto.
      - (* switch *)
        constructor; auto.
        eapply iface_eq_wc_block; eauto. econstructor; eauto.
      - (* locals *)
        constructor; eauto.
        eapply iface_eq_wc_block; eauto. econstructor; eauto.
    Qed.

    Corollary unnest_blocks_wc : forall vars blocks blocks' st st',
        Forall (wc_block G1 (vars++st_clocks st)) blocks ->
        unnest_blocks G1 blocks st = (blocks', st') ->
        Forall (wc_block G2 (vars++st_clocks st')) blocks'.
    Proof with eauto.
      induction blocks; intros * Hwc Hnorm;
        unfold unnest_blocks in *; simpl in *; repeat inv_bind; simpl...
      assert (st_follows st x1) as Hfollows1 by repeat solve_st_follows.
      assert (st_follows x1 st') as Hfollows2 by repeat solve_st_follows.
      inv Hwc. eapply unnest_block_wc in H...
      assert (unnest_blocks G1 blocks x1 = (concat x2, st')) as Hnorm.
      { unfold unnest_blocks; repeat inv_bind; eauto. }
      apply IHblocks in Hnorm... 2:solve_forall; repeat solve_incl.
      apply Forall_app; split...
      solve_forall; repeat solve_incl.
    Qed.

    (** *** The produced environment is also well-clocked *)

    Hypothesis HwcG1 : wc_global G1.
    Hypothesis HwcG2 : wc_global G2.

    Fact unnest_reset_wc_env : forall vars e e' eqs' st st',
        wc_env (vars++st_clocks st) ->
        (forall es' eqs' st0',
            unnest_exp G1 true e st = (es', eqs', st0') ->
            st_follows st0' st' ->
            wc_env (vars++st_clocks st0')) ->
        wc_exp G1 (vars ++ st_clocks st) e ->
        unnest_reset (unnest_exp G1 true) e st = (e', eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof with eauto.
      intros * Hwenv Hun Hwc Hnorm.
      unnest_reset_spec; simpl in *; eauto.
      - eapply Hun; eauto; repeat solve_st_follows.
      - eapply fresh_ident_wc_env in Hfresh; eauto with fresh.
        assert (Hwc' := Hk0). eapply unnest_exp_wc in Hwc' as [Hwc' _]; eauto.
        eapply wc_exp_clocksof in Hwc'; eauto with fresh.
        destruct l; simpl in *; inv Hhd. constructor.
        apply Forall_app in Hwc' as [Hwc' _].
        rewrite clockof_annot in Hwc'.
        destruct (annot e0); simpl in *. inv H0; constructor.
        inv Hwc'; auto.
    Qed.

    Fact mmap2_wc_env {A A1 A2 : Type} :
      forall vars (k : A -> Unnesting.FreshAnn (A1 * A2)) a a1s a2s st st',
        wc_env (vars++st_clocks st) ->
        mmap2 k a st = (a1s, a2s, st') ->
        (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
        Forall (fun a => forall a1s a2s st0 st0',
                    wc_env (vars++st_clocks st0) ->
                    k a st0 = (a1s, a2s, st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    wc_env (vars++st_clocks st0')) a ->
        wc_env (vars++st_clocks st').
    Proof with eauto.
      induction a; intros a1s a2s st st' Hclocks Hmap Hfollows Hf;
        simpl in Hmap; repeat inv_bind...
      inv Hf.
      specialize (H3 _ _ _ _ Hclocks H).
      eapply IHa in H3...
      - reflexivity.
      - eapply mmap2_st_follows...
        solve_forall...
      - solve_forall.
        eapply H2 in H5...
        etransitivity...
    Qed.

    Corollary unnest_resets_wc_env : forall vars es es' eqs' st st',
        wc_env (vars++st_clocks st) ->
        Forall (fun e => forall es' eqs' st0 st0',
                    wc_env (vars++st_clocks st0) ->
                    unnest_exp G1 true e st0 = (es', eqs', st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    wc_env (vars++st_clocks st0')) es ->
        Forall (wc_exp G1 (vars ++ st_clocks st)) es ->
        mmap2 (unnest_reset (unnest_exp G1 true)) es st = (es', eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof with eauto.
      induction es; intros * HwcE F Wc Map; simpl in *;
        inv F; inv Wc; repeat inv_bind; eauto.
      assert (Map:=H0). eapply IHes in H0; eauto. 3:solve_forall; repeat solve_incl.
      2:solve_forall; eapply H9; eauto; repeat solve_st_follows.
      eapply unnest_reset_wc_env in H; eauto.
      intros * Un Follows. eapply H1 in Un; eauto. 1,2:repeat solve_st_follows.
    Qed.

    Lemma unnest_noops_exps_wc_env : forall vars cks es es' eqs' st st' ,
        length es = length cks ->
        Forall normalized_lexp es ->
        Forall (fun e => numstreams e = 1) es ->
        Forall (wc_exp G2 (vars++st_clocks st)) es ->
        wc_env (vars++st_clocks st) ->
        unnest_noops_exps cks es st = (es', eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof.
      unfold unnest_noops_exps.
      intros * Hl Hnormed Hnum Hwc Henv Hunt. repeat inv_bind.
      eapply mmap2_wc_env in H; eauto.
      1:intros ? ? (?&?) ? ? Hun; eauto with norm.
      eapply Forall2_combine'. eapply Forall2_forall2. split; auto.
      intros * Hn Hnth1 Hnth2 * Henv' Hunt Hf1 Hf2; subst.
      unfold unnest_noops_exp in Hunt.
      assert (In (nth n es b) es) as Hin by (eapply nth_In; congruence).
      eapply Forall_forall in Hnormed; eauto.
      eapply Forall_forall in Hnum; eauto.
      eapply Forall_forall in Hwc; eauto.
      rewrite <- length_annot_numstreams in Hnum. singleton_length.
      destruct p as (?&?).
      destruct (is_noops_exp _ _); repeat inv_bind; eauto.
      eapply fresh_ident_wc_env in H0; eauto.
      eapply wc_exp_clockof in Hwc; eauto.
      rewrite clockof_annot, Hsingl in Hwc; simpl in Hwc. inv Hwc.
      repeat solve_incl.
    Qed.

    Fact unnest_exp_wc_env : forall vars e is_control es' eqs' st st',
        wc_env (vars++st_clocks st) ->
        wc_exp G1 (vars++st_clocks st) e ->
        unnest_exp G1 is_control e st = (es', eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof with eauto with norm.
      Local Ltac solve_mmap2' :=
        solve_forall;
        match goal with
        | Hnorm : unnest_exp _ _ _ _ = _, H : context [unnest_exp _ _ _ _ = _ -> _] |- _ =>
          eapply H in Hnorm; eauto; repeat solve_incl
        end.
      induction e using exp_ind2; intros is_control es' eqs' st st' Hwenv Hwc Hnorm;
          simpl in *; repeat inv_bind...
      - (* unop *)
        inv Hwc; eauto.
      - (* binop *)
        inv Hwc.
        assert (st_follows st x1) as Hfollows by eauto with norm.
        eapply IHe1 in H...
        eapply IHe2 in H0...
        repeat solve_incl.
      - (* fby *)
        inv Hwc.
        rewrite Forall2_eq in H9, H10.
        assert (Hwenv1:=H1). eapply mmap2_wc_env in Hwenv1... 2:solve_mmap2'.
        assert (Hwenv2:=H2). eapply mmap2_wc_env in Hwenv2... 2:solve_mmap2'.
        eapply idents_for_anns_wc_env in H3...
        assert (Forall (wc_clock ((vars ++ st_clocks x1))) (map snd a)).
        { rewrite H9.
          eapply wc_exp_clocksof in H7... eapply Forall_impl; [|eauto]. intros.
          repeat solve_incl. }
        solve_forall; repeat solve_incl.
      - (* arrow *)
        inv Hwc.
        rewrite Forall2_eq in H9, H10.
        assert (Hwenv1:=H1). eapply mmap2_wc_env in Hwenv1... 2:solve_mmap2'.
        assert (Hwenv2:=H2). eapply mmap2_wc_env in Hwenv2... 2:solve_mmap2'.
        eapply idents_for_anns_wc_env in H3...
        assert (Forall (wc_clock ((vars ++ st_clocks x1))) (map snd a)).
        { rewrite H9.
          eapply wc_exp_clocksof in H7... eapply Forall_impl; [|eauto]. intros.
          repeat solve_incl. }
        solve_forall; repeat solve_incl.
      - (* when *)
        inv Hwc; repeat inv_bind.
        eapply mmap2_wc_env in H0... solve_mmap2'.
      - (* merge *)
        inv Hwc; repeat inv_bind.
        assert (Hwenv1:=H0). eapply mmap2_wc_env in Hwenv1...
        2:(intros; repeat inv_bind; destruct a; repeat solve_st_follows).
        2:{ solve_forall; repeat inv_bind. eapply mmap2_wc_env in H6...
            solve_mmap2'. }
        destruct is_control; repeat inv_bind...
        eapply idents_for_anns_wc_env in H1...
        repeat rewrite Forall_map.
        rewrite Forall_forall. intros ty _; simpl.
        unfold wc_env in Hwenv; rewrite Forall_forall in Hwenv; eapply Hwenv in H3; simpl in H3.
        repeat solve_incl.
      - (* case *)
        inv Hwc; repeat inv_bind.
        assert (st_follows x1 x4) by (repeat solve_st_follows; destruct a; repeat solve_st_follows).
        assert (Hwenv1:=H1). eapply IHe in Hwenv1...
        assert (Hwenv2:=H2). eapply mmap2_wc_env in Hwenv2...
        2:(intros; repeat inv_bind; destruct a; repeat solve_st_follows).
        2:{ solve_forall; repeat inv_bind.
            eapply mmap2_wc_env in H10... solve_mmap2'. }
        assert (wc_env (vars ++ st_clocks x7)) as Hwenv3.
        { destruct d; repeat inv_bind; auto.
          eapply mmap2_wc_env in H3... solve_mmap2'.
          eapply Forall_forall in H11; eauto. repeat solve_incl. }
        destruct is_control; repeat inv_bind...
        eapply idents_for_anns_wc_env in H4...
        repeat rewrite Forall_map.
        rewrite Forall_forall. intros ty _; simpl.
        eapply wc_exp_clockof in H5... rewrite H6 in H5. inv H5.
        assert (st_follows x4 x7) as Hfollows.
        { destruct d; repeat solve_st_follows. }
        repeat solve_incl.
      - (* app *)
        assert (Hwc':=Hwc). inv Hwc'.
        assert (Hwenv1:=H1). eapply mmap2_wc_env in Hwenv1... 2:solve_mmap2'.
        assert (Hwenv2:=H2). eapply unnest_noops_exps_wc_env in Hwenv2...
        2:{ unfold find_node_incks. rewrite H11.
            eapply Forall2_length in H12. rewrite map_length.
            eapply mmap2_unnest_exp_length in H1; eauto with lclocking.
            rewrite length_nclocksof_annots, length_idck, length_idty in H12.
            congruence. }
        2:{ eapply mmap2_unnest_exp_numstreams; eauto. }
        2:{ eapply mmap2_unnest_exp_wc in H1 as (?&?); eauto. }
        assert (Hnr:=H3). eapply unnest_resets_wc_env in H3... 2:solve_mmap2'.
        2:solve_forall; repeat solve_incl.
        eapply idents_for_anns_wc_env...
        apply wc_exp_clockof in Hwc... simpl in Hwc.
        eapply Forall_impl; [|eauto]; intros. repeat solve_incl.
    Qed.

    Corollary mmap2_unnest_exp_wc_env : forall vars es is_control es' eqs' st st',
        wc_env (vars++st_clocks st) ->
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        mmap2 (unnest_exp G1 is_control) es st = (es', eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof.
      intros.
      eapply mmap2_wc_env in H1; eauto with norm.
      rewrite Forall_forall in *; intros.
      eapply unnest_exp_wc_env in H4; eauto.
      eapply H0 in H2. repeat solve_incl.
    Qed.

    Corollary unnest_exps_wc_env : forall vars es es' eqs' st st',
        wc_env (vars++st_clocks st) ->
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        unnest_exps G1 es st = (es', eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof with eauto with norm.
      intros * Hwenv Hwc Hnorm.
      unfold unnest_exps in Hnorm; repeat inv_bind.
      eapply mmap2_wc_env in H...
      solve_forall.
      eapply unnest_exp_wc_env in H3...
      repeat solve_incl.
    Qed.

    Fact unnest_rhs_wc_env : forall vars e es' eqs' st st',
        wc_env (vars++st_clocks st) ->
        wc_exp G1 (vars++st_clocks st) e ->
        unnest_rhs G1 e st = (es', eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof with eauto with norm.
      intros * Hwenv Hwc Hnorm.
      destruct e; unfold unnest_rhs in Hnorm;
        try (solve [eapply unnest_exp_wc_env in Hnorm; eauto]);
        repeat inv_bind.
      - (* fby *)
        inv Hwc.
        assert (Hwenv1:=H). eapply unnest_exps_wc_env in Hwenv1...
        assert (Hwenv2:=H0). eapply unnest_exps_wc_env in Hwenv2...
        solve_forall; repeat solve_incl.
      - (* arrow *)
        inv Hwc.
        assert (Hwenv1:=H). eapply unnest_exps_wc_env in Hwenv1...
        assert (Hwenv2:=H0). eapply unnest_exps_wc_env in Hwenv2...
        solve_forall; repeat solve_incl.
      - (* app *)
        inv Hwc.
        assert (Hnorm:=H). eapply unnest_exps_wc_env in H...
        assert (Hnorm2:=H0). eapply unnest_noops_exps_wc_env in H0...
        + eapply unnest_resets_wc_env in H1... 2:solve_forall; repeat solve_incl.
          eapply Forall_forall; intros.
          eapply unnest_exp_wc_env in H4; eauto.
          eapply Forall_forall in H7; eauto. repeat solve_incl.
        + unfold find_node_incks. rewrite H8.
          eapply Forall2_length in H9. rewrite map_length.
          eapply unnest_exps_length in Hnorm; eauto with lclocking.
          rewrite length_nclocksof_annots, length_idck, length_idty in H9.
          congruence.
        + eapply unnest_exps_numstreams; eauto.
        + eapply unnest_exps_wc in Hnorm as (?&?); eauto.
    Qed.

    Corollary unnest_rhss_wc_env : forall vars es es' eqs' st st',
        wc_env (vars++st_clocks st) ->
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        unnest_rhss G1 es st = (es', eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof with eauto with norm.
      intros * Hwenv Hwc Hnorm.
      unfold unnest_rhss in Hnorm; repeat inv_bind.
      eapply mmap2_wc_env in H...
      solve_forall.
      eapply unnest_rhs_wc_env in H3...
      repeat solve_incl.
    Qed.

    Fact unnest_equation_wc_env : forall vars e eqs' st st',
        wc_env (vars++st_clocks st) ->
        wc_equation G1 (vars++st_clocks st) e ->
        unnest_equation G1 e st = (eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof with eauto with norm.
      intros vars [xs es] * Hwenv Hwc Hnorm.
      unfold unnest_equation in Hnorm.
      inv Hwc; repeat inv_bind.
      - (* app *)
        unfold unnest_rhss in *; repeat inv_bind.
        assert (Hnorm:=H). eapply unnest_exps_wc_env in H...
        assert (Hnorm2:=H0). eapply unnest_noops_exps_wc_env in H0...
        + eapply unnest_resets_wc_env in H8... 2:solve_forall; repeat solve_incl.
          eapply Forall_forall; intros.
          eapply unnest_exp_wc_env in H11; eauto.
          eapply Forall_forall in H2; eauto. repeat solve_incl.
        + unfold find_node_incks. rewrite H3.
          eapply Forall2_length in H4. rewrite map_length.
          eapply unnest_exps_length in Hnorm; eauto with lclocking.
          rewrite length_nclocksof_annots, length_idck, length_idty in H4.
          congruence.
        + eapply unnest_exps_numstreams; eauto.
        + eapply unnest_exps_wc in Hnorm as (?&?); eauto.
      - (* general case *)
        eapply unnest_rhss_wc_env in H...
    Qed.

    Lemma unnest_block_wc_env : forall vars d blocks' st st' ,
        wc_env (vars++st_clocks st) ->
        wc_block G1 (vars++st_clocks st) d ->
        unnest_block G1 d st = (blocks', st') ->
        wc_env (vars++st_clocks st').
    Proof.
      induction d using block_ind2; intros * Hwenv Hwc Hnorm;
        inv Hwc; repeat inv_bind; auto.
      - (* equation *)
        eapply unnest_equation_wc_env in H; eauto.
      - (* reset *)
        assert (wc_env (vars ++ st_clocks x0)) as Hwenv'.
        { clear - H H0 H2 Hwenv.
          revert st x0 x H2 Hwenv H0.
          induction H; intros * Hwc Hwenv Hmap; inv Hwc; repeat inv_bind; auto.
          eapply IHForall in H2; eauto.
          solve_forall; repeat solve_incl. }
        eapply unnest_reset_wc_env in H1; eauto.
        intros. eapply unnest_exp_wc_env in H3; eauto.
        1,2:repeat solve_incl.
    Qed.

    Corollary unnest_blocks_wc_env : forall vars blocks blocks' st st' ,
        wc_env (vars++st_clocks st) ->
        Forall (wc_block G1 (vars++st_clocks st)) blocks ->
        unnest_blocks G1 blocks st = (blocks', st') ->
        wc_env (vars++st_clocks st').
    Proof with eauto.
      induction blocks; intros * Hwenv Hwc Hnorm;
        unfold unnest_blocks in *; simpl in *; repeat inv_bind...
      assert (st_follows st x1) as Hfollows1 by repeat solve_st_follows.
      inv Hwc. eapply unnest_block_wc_env in H...
      assert (unnest_blocks G1 blocks x1 = (concat x2, st')) as Hnorm.
      { unfold unnest_blocks; repeat inv_bind; eauto. }
      apply IHblocks in Hnorm as Hwenv2... solve_forall; repeat solve_incl.
    Qed.

    Lemma unnest_node_wc : forall n,
        wc_node G1 n ->
        wc_node G2 (unnest_node G1 n).
    Proof with eauto.
      intros * [Hin [Hout Hblk]].
      unfold unnest_node.
      repeat constructor; simpl; auto.
      destruct (n_block n); eauto using iface_eq_wc_block. inv Hblk.
      constructor; auto.
      - destruct (unnest_blocks _ _ _) as (eqs'&st') eqn:Heqres.
        unfold idck. repeat rewrite map_app.
        eapply unnest_blocks_wc in Heqres as Hwc'...
        2:unfold st_clocks; rewrite init_st_anns, app_nil_r...
        unfold st_clocks, idty, idck in *.
        repeat rewrite map_app in *; repeat rewrite map_map in *; repeat rewrite <- app_assoc in *.
        solve_forall; solve_incl.
      - destruct (unnest_blocks _ _ _) as (eqs'&st') eqn:Heqres.
        unfold idck. repeat rewrite map_app.
        eapply unnest_blocks_wc_env in Heqres as Henv'...
        2,3:unfold st_clocks; rewrite init_st_anns, app_nil_r. 3:eauto.
        + unfold st_clocks, idty, idck in *.
          repeat rewrite map_app in *; repeat rewrite map_map in *; repeat rewrite <- app_assoc in *.
          simpl in *...
          unfold wc_env in Henv'.
          repeat rewrite Forall_app in Henv'. destruct Henv' as (_&_&_&Henv').
          eapply Forall_app. split; auto.
          1,2:solve_forall; repeat solve_incl.
        + unfold wc_env in Hout.
          eapply Forall_app. split; auto.
          1,2:solve_forall; repeat solve_incl.
    Qed.

  End unnest_node_wc.

  Lemma unnest_global_wc : forall G,
      wc_global G ->
      wc_global (unnest_global G).
  Proof.
    intros (enums&nds). unfold wc_global, CommonTyping.wt_program; simpl.
    induction nds; intros * Hwc; simpl; inv Hwc; auto with datatypes.
    destruct H1.
    constructor; [constructor|].
    - eapply unnest_node_wc; eauto.
      2: eapply IHnds; eauto.
      eapply unnest_nodes_eq.
    - eapply unnest_nodes_names; eauto.
    - eapply IHnds; eauto.
  Qed.

  (** ** Preservation of clocking through second pass *)

  Section normfby_node_wc.
    Variable G1 : @global nolocal_top_block norm1_prefs.
    Variable G2 : @global nolocal_top_block norm2_prefs.

    Hypothesis Hiface : global_iface_eq G1 G2.
    Local Hint Resolve iface_eq_wc_exp : norm.

    Fact add_whens_clockof : forall e ty ck,
      clockof e = [Cbase] ->
      clockof (add_whens e ty ck) = [ck].
    Proof. induction ck; try destruct p; intros Hlen; auto. Qed.

    Fact add_whens_wc_exp : forall vars e ty ck,
        clockof e = [Cbase] ->
        wc_exp G1 vars e ->
        wc_clock vars ck ->
        wc_exp G2 vars (add_whens e ty ck).
    Proof with eauto with norm.
      induction ck; try destruct p; intros Hclof Hwc Hwc2; inv Hwc2; simpl...
      repeat constructor; simpl... 1,2:rewrite app_nil_r.
      + rewrite add_whens_clockof...
      + rewrite add_whens_clockof...
    Qed.

    Fact fby_iteexp_wc_exp : forall vars e0 e ty ck e' eqs' st st' ,
        wc_exp G1 (vars++st_clocks st) e0 ->
        wc_exp G1 (vars++st_clocks st) e ->
        clockof e0 = [ck] ->
        clockof e = [ck] ->
        fby_iteexp e0 e (ty, ck) st = (e', eqs', st') ->
        wc_exp G2 (vars++st_clocks st') e'.
    Proof with eauto with fresh.
      intros * Hwc1 Hwc2 Hck1 Hck2 Hfby.
      unfold fby_iteexp in Hfby; simpl in *.
      assert (st_follows st st') as Hfollows.
      { eapply (fby_iteexp_st_follows _ _ (ty, ck)) in Hfby; eauto. }
      repeat inv_bind; repeat econstructor; simpl; try congruence...
      1-5:try rewrite app_nil_r.
      - apply in_or_app, or_intror; unfold st_clocks, idty, idck.
        apply init_var_for_clock_In in H; simpl in *.
        eapply st_follows_incl in H...
        simpl_In; eexists; split; eauto...
      - eapply iface_eq_wc_exp; eauto. repeat solve_incl.
      - apply in_or_app, or_intror; unfold st_clocks, idty, idck.
        simpl_In; exists (x2, (ty, ck)); simpl; split...
        eapply fresh_ident_In in H0...
      - rewrite Hck1; auto.
      - now rewrite Hck1.
    Qed.

    Fact arrow_iteexp_wc_exp : forall vars e0 e ty ck e' eqs' st st' ,
        wc_exp G1 (vars++st_clocks st) e0 ->
        wc_exp G1 (vars++st_clocks st) e ->
        clockof e0 = [ck] ->
        clockof e = [ck] ->
        arrow_iteexp e0 e (ty, ck) st = (e', eqs', st') ->
        wc_exp G2 (vars++st_clocks st') e'.
    Proof with eauto.
      intros * Hwc1 Hwc2 Hck1 Hck2 Hfby.
      unfold arrow_iteexp in Hfby; simpl in *; repeat inv_bind.
      assert (st_follows st st') as Hfollows by (eapply init_var_for_clock_st_follows; eauto).
      repeat econstructor; simpl; try congruence...
      1-7:try rewrite app_nil_r.
      4-7:try rewrite Hck1; try rewrite Hck2; auto.
      - apply in_or_app, or_intror; unfold st_clocks, idty, idck.
        apply init_var_for_clock_In in H; simpl in *.
        simpl_In; eexists; split; eauto...
      - eapply iface_eq_wc_exp; eauto. repeat solve_incl.
      - eapply iface_eq_wc_exp; eauto. repeat solve_incl.
    Qed.

    Fact init_var_for_clock_wc_env : forall vars ck id eqs' st st' ,
        wc_env (vars++st_clocks st) ->
        wc_clock (vars++st_clocks st) ck ->
        init_var_for_clock ck st = (id, eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof with eauto.
      intros * Hwenv Hwc Hinit.
      unfold init_var_for_clock in Hinit.
      destruct fresh_ident eqn:Hfresh. inv Hinit.
      eapply fresh_ident_wc_env in Hfresh...
    Qed.

    Fact fby_iteexp_wc_env : forall vars e0 e ty ck es' eqs' st st' ,
        wc_env (vars++st_clocks st) ->
        wc_clock (vars++st_clocks st) ck ->
        fby_iteexp e0 e (ty, ck) st = (es', eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof with eauto.
      intros ???? ck es' eqs' st st' Hwenv Hwc Hfby.
      unfold fby_iteexp in Hfby; repeat inv_bind...
      eapply fresh_ident_wc_env in H0... 2:repeat solve_incl.
      eapply init_var_for_clock_wc_env in H... eapply init_var_for_clock_st_follows in H...
    Qed.

    Fact init_var_for_clock_wc_eq : forall vars ck id eqs' st st' ,
        wc_clock (vars++st_clocks st) ck ->
        init_var_for_clock ck st = (id, eqs', st') ->
        Forall (wc_equation G2 (vars++st_clocks st')) eqs'.
    Proof with eauto with norm lclocking.
      intros * Hwc Hinit.
      unfold init_var_for_clock in Hinit.
      destruct fresh_ident eqn:Hfresh; repeat inv_bind.
      simpl in *; repeat econstructor; simpl...
      1,2:apply add_whens_wc_exp... 1-2:repeat solve_incl.
      1,2:rewrite app_nil_r, add_whens_clockof...
      apply fresh_ident_In in Hfresh.
      apply in_or_app; right.
      unfold st_clocks, idck, idty;
        simpl_In; eexists; split; eauto; eauto.
    Qed.

    Fact normalized_lexp_wc_exp_clockof : forall vars e,
        normalized_lexp e ->
        wc_env vars ->
        wc_exp G2 vars e ->
        Forall (wc_clock vars) (clockof e).
    Proof with eauto.
      intros vars e Hnormed Hwenv Hwc.
      induction Hnormed; inv Hwc; simpl; repeat constructor...
      - eapply Forall_forall in Hwenv; eauto. eauto.
      - eapply IHHnormed in H1. rewrite H4 in H1. inv H1...
      - eapply IHHnormed1 in H3. rewrite H6 in H3. inv H3...
      - apply Forall_singl in H5.
        eapply IHHnormed in H5.
        simpl in H7. rewrite app_nil_r in H7. symmetry in H7.
        singleton_length.
        inv H6. inv H5...
    Qed.

    Fact fby_iteexp_wc_eq : forall vars e0 e ty ck e' eqs' st st' ,
        normalized_lexp e0 ->
        wc_env (vars++st_clocks st) ->
        wc_exp G1 (vars++st_clocks st) e0 ->
        wc_exp G1 (vars++st_clocks st) e ->
        clockof e0 = [ck] ->
        clockof e = [ck] ->
        fby_iteexp e0 e (ty, ck) st = (e', eqs', st') ->
        Forall (wc_equation G2 (vars++st_clocks st')) eqs'.
    Proof with eauto with norm lclocking.
      intros * Hnormed Henv Hwc1 Hwc2 Hcl1 Hcl2 Hfby.
      assert (wc_clock (vars++st_clocks st) ck) as Hwck.
      { eapply iface_eq_wc_exp, normalized_lexp_wc_exp_clockof in Hwc1...
        rewrite Hcl1 in Hwc1; inv Hwc1; auto. }
      unfold fby_iteexp in Hfby; simpl in *.
      repeat inv_bind; repeat constructor; simpl...
      - eapply add_whens_wc_exp...
        1,2:destruct ty; simpl...
        eapply init_var_for_clock_st_follows in H. repeat solve_incl.
      - eapply init_var_for_clock_st_follows in H.
        eapply iface_eq_wc_exp; eauto. repeat solve_incl.
      - rewrite app_nil_r, add_whens_clockof...
        destruct ty; simpl...
      - rewrite app_nil_r. rewrite Hcl2...
      - eapply fresh_ident_In in H0.
        apply in_or_app; right.
        unfold st_clocks, idck.
        simpl_In. exists (x2, (ty, ck)); auto.
      - eapply init_var_for_clock_wc_eq in H...
        solve_forall; repeat solve_incl.
    Qed.

    Fact normfby_equation_wc : forall vars to_cut eq eqs' st st' ,
        unnested_equation G1 eq ->
        wc_env (vars++st_clocks st) ->
        wc_equation G1 (vars++st_clocks st) eq ->
        normfby_equation to_cut eq st = (eqs', st') ->
        (Forall (wc_equation G2 (vars++st_clocks st')) eqs' /\ wc_env (vars++st_clocks st')).
    Proof with eauto.
      intros * Hunt Hwenv Hwc Hfby.
      inv_normfby_equation Hfby to_cut eq; try destruct x2 as [ty ck].
      - (* fby (constant) *)
        destruct PS.mem; repeat inv_bind; auto.
        2:{ split; auto. inv Hwc.
            do 2 constructor; auto.
            solve_forall. }
        inv Hwc. rename H2 into Hwc. rename H3 into Hins.
        apply Forall_singl in Hwc. apply Forall2_singl in Hins.
        assert (Hwc':=Hwc). inv Hwc'.
        apply Forall_singl in H3; apply Forall_singl in H4.
        assert (wc_clock (vars ++ st_clocks st) ck).
        { eapply wc_env_var; eauto. }
        repeat (econstructor; eauto).
        + eapply fresh_ident_In in H.
          eapply in_or_app, or_intror. unfold st_clocks, idck, idty.
          simpl_In. exists (x2, (ty, ck)); split; auto.
        + repeat solve_incl.
        + eapply iface_eq_wc_exp... repeat solve_incl.
        + eapply iface_eq_wc_exp... repeat solve_incl.
        + eapply fresh_ident_In in H.
          eapply in_or_app, or_intror. unfold st_clocks, idck, idty.
          simpl_In. exists (x2, (ty, ck)); split; auto.
        + eapply fresh_ident_wc_env in H; eauto.
      - (* fby *)
        assert (st_follows st st') as Hfollows by (eapply fby_iteexp_st_follows with (ann:=(ty, ck)) in H; eauto).
        inv Hwc. rename H2 into Hwc. rename H3 into Hins.
        apply Forall_singl in Hwc. apply Forall2_singl in Hins.
        inv Hwc.
        simpl in *; rewrite app_nil_r in *.
        apply Forall_singl in H3; apply Forall_singl in H4.
        rewrite Forall2_eq in H5, H6.
        assert (Hwce:=H). eapply fby_iteexp_wc_exp in Hwce; eauto.
        assert (Hck:=H). eapply (fby_iteexp_clockof _ _ (ty, ck)) in Hck; eauto.
        assert (Hwceq:=H). eapply fby_iteexp_wc_eq in Hwceq; eauto.
        2:(clear - Hunt; inv Hunt; eauto; inv H0; inv H).
        assert (wc_clock (vars ++ st_clocks st) ck).
        { eapply wc_env_var; eauto. }
        eapply (fby_iteexp_wc_env _ _ _ ty ck) in H...
        repeat constructor; auto; simpl; rewrite app_nil_r.
        rewrite Hck. repeat constructor.
        repeat solve_incl.
      - (* arrow *)
        inv Hwc. rename H2 into Hwc. rename H3 into Hins.
        apply Forall_singl in Hwc. apply Forall2_singl in Hins.
        inv Hwc.
        simpl in *; rewrite app_nil_r in *.
        apply Forall_singl in H3; apply Forall_singl in H4.
        rewrite Forall2_eq in H5, H6.
        assert (Hwce:=H). eapply arrow_iteexp_wc_exp in Hwce; eauto.
        assert (wc_clock (vars ++ st_clocks st) ck).
        { eapply wc_env_var; eauto. }
        repeat inv_bind.
        assert (Hwce':=H). eapply init_var_for_clock_wc_env in Hwce'; eauto.
        split; eauto.
        assert (st_follows st st') as Hfollows.
        { eapply init_var_for_clock_st_follows; eauto. }
        repeat (econstructor; auto); try congruence.
        + repeat solve_incl.
        + eapply init_var_for_clock_wc_eq in H...
      - (* others *)
        split; auto. constructor; auto.
        eapply iface_eq_wc_equation; eauto.
    Qed.

    Fact normfby_block_wc : forall vars to_cut d blocks' st st' ,
        unnested_block G1 d ->
        wc_env (vars++st_clocks st) ->
        wc_block G1 (vars++st_clocks st) d ->
        normfby_block to_cut d st = (blocks', st') ->
        (Forall (wc_block G2 (vars++st_clocks st')) blocks' /\ wc_env (vars++st_clocks st')).
    Proof.
      induction d using block_ind2; intros * Hunt Henv Hwc Hfby;
        unfold normfby_blocks in *; repeat inv_bind; simpl; auto.
      - (* equation *)
        inv Hunt. inv Hwc.
        eapply normfby_equation_wc in H as (?&?); eauto.
        split; auto.
        rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
        constructor; auto.
      - (* reset *)
        simpl in Hfby.
        inv Hunt. inv Hwc.
        cases; repeat inv_bind.
        apply Forall_singl in H3. inv H6. apply Forall_singl in H.
        assert (Hnorm1:=H0). eapply H in H0 as (?&?); eauto.
        split; auto.
        rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
        econstructor; simpl; eauto.
        eapply iface_eq_wc_exp; eauto. repeat solve_incl.
        eapply normfby_block_st_follows; eauto.
      - split; auto. constructor; eauto using iface_eq_wc_block.
      - split; auto. constructor; eauto using iface_eq_wc_block.
    Qed.

    Corollary normfby_blocks_wc : forall vars to_cut blocks blocks' st st' ,
        Forall (unnested_block G1) blocks ->
        wc_env (vars++st_clocks st) ->
        Forall (wc_block G1 (vars++st_clocks st)) blocks ->
        normfby_blocks to_cut blocks st = (blocks', st') ->
        (Forall (wc_block G2 (vars++st_clocks st')) blocks' /\ wc_env (vars++st_clocks st')).
    Proof.
      induction blocks; intros * Hunt Henv Hwc Hfby;
        unfold normfby_blocks in *; repeat inv_bind; simpl; auto.
      inv Hunt. inv Hwc.
      assert (normfby_blocks to_cut blocks x1 = (concat x2, st')) as Hnorm.
      { unfold normfby_blocks. repeat inv_bind; eauto. }
      assert (H':=H). eapply normfby_block_wc in H as [Hwc' Henv']; auto. 2,3:eauto.
      apply IHblocks in Hnorm as [Hwc'' Henv'']; auto.
      2:solve_forall; repeat solve_incl; eapply normfby_block_st_follows in H'; eauto.
      rewrite Forall_app; repeat split; eauto.
      solve_forall; repeat solve_incl.
    Qed.

    Lemma normfby_node_wc : forall n,
        unnested_node G1 n ->
        wc_node G1 n ->
        wc_node G2 (normfby_node n).
    Proof.
      intros * Hunn [Hclin [Hclout Hblk]].
      unfold normfby_node.
      repeat constructor; simpl; auto.
      inv Hunn. rewrite H in Hblk; inv Hblk. rewrite H.
      constructor; auto.
      - destruct (normfby_blocks _ _ _) as (eqs'&st') eqn:Heqres.
        eapply normfby_blocks_wc in Heqres as [? _]; eauto.
        2,3:unfold st_clocks; rewrite init_st_anns, app_nil_r.
        3:eauto.
        + unfold st_clocks, idck, idty in *.
          repeat rewrite map_app in *; repeat rewrite map_map in *; repeat rewrite <- app_assoc in *.
          solve_forall; repeat solve_incl.
        + unfold wc_env in *.
          apply Forall_app; split; auto.
          1,2:solve_forall; repeat solve_incl.
      - destruct (normfby_blocks _ _ _) as (eqs'&st') eqn:Heqres.
        eapply normfby_blocks_wc in Heqres as [_ Henv']; eauto.
        1-3:unfold st_clocks in *; try rewrite init_st_anns, app_nil_r. 3:eauto.
        + unfold wc_env, st_clocks, idck, idty in *.
          repeat rewrite map_app in *; repeat rewrite map_map in *; repeat rewrite <- app_assoc in *; simpl in *.
          repeat rewrite Forall_app in Henv'. destruct Henv' as (_&_&_&Henv').
          apply Forall_app; split.
          1,2:solve_forall; repeat solve_incl.
        + unfold wc_env in *.
          apply Forall_app; split; auto.
          1,2:solve_forall; repeat solve_incl.
    Qed.

  End normfby_node_wc.

  Lemma normfby_global_wc : forall G,
      unnested_global G ->
      wc_global G ->
      wc_global (normfby_global G).
  Proof.
    intros (enums&nds). unfold wc_global, unnested_global, CommonTyping.wt_program; simpl.
    induction nds; intros * Hun Hwc; simpl;
      inversion_clear Hun as [|?? (?&?)];
      inversion_clear Hwc as [|?? (?&?)]; auto with datatypes.
    constructor; [constructor|].
    - eapply normfby_node_wc; eauto.
      eapply normfby_global_eq.
    - simpl. eapply normfby_nodes_names; eauto.
    - eapply IHnds; eauto.
  Qed.

  (** ** Conclusion *)

  Lemma normalize_global_wc : forall G,
      wc_global G ->
      wc_global (normalize_global G).
  Proof.
    intros * Hwc.
    eapply normfby_global_wc, unnest_global_wc, Hwc.
    eapply unnest_global_unnested_global; eauto with lclocking.
  Qed.

End NCLOCKING.

Module NClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (Norm : NORMALIZATION Ids Op OpAux Cks Syn)
       <: NCLOCKING Ids Op OpAux Cks Syn Clo Norm.
  Include NCLOCKING Ids Op OpAux Cks Syn Clo Norm.
End NClockingFun.
