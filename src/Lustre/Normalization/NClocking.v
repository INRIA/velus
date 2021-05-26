From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Omega.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax Lustre.LCausality Lustre.LClocking.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

(** * Preservation of Typing through Normalization *)

Module Type NCLOCKING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (Caus : LCAUSALITY Ids Op OpAux Cks Syn)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (Import Norm : NORMALIZATION Ids Op OpAux Cks Syn Caus).
  Import Fresh Fresh.Facts Fresh.Tactics.

  (** ** Rest of clockof preservation (started in Normalization.v) *)

  Fact unnest_noops_exps_nclocksof : forall cks es es' eqs' st st',
      length cks = length es ->
      Forall (fun e => numstreams e = 1) es ->
      unnest_noops_exps cks es st = (es', eqs', st') ->
      nclocksof es' = nclocksof es.
  Proof.
    intros.
    repeat rewrite nclocksof_annots.
    erewrite unnest_noops_exps_annots; eauto.
  Qed.

  Fact unnest_reset_clockof : forall G vars e e' eqs' st st',
      wc_exp G vars e ->
      numstreams e = 1 ->
      unnest_reset (unnest_exp G true) e st = (e', eqs', st') ->
      clockof e' = clockof e.
  Proof.
    intros * Hwc Hnum Hunn.
    unnest_reset_spec; simpl in *; auto.
    1,2:assert (length l = 1) by
        (eapply unnest_exp_length in Hk0; eauto; congruence);
      singleton_length.
    - eapply unnest_exp_clockof in Hk0; eauto.
    - eapply unnest_exp_annot in Hk0; eauto.
      simpl in Hk0. rewrite app_nil_r in Hk0.
      rewrite <- length_annot_numstreams in Hnum.
      rewrite clockof_annot, <- Hk0.
      singleton_length. rewrite Hk0 in *; simpl in Hhd; subst.
      reflexivity.
  Qed.

  Hint Resolve nth_In.
  Corollary mmap2_unnest_exp_clocksof' :
    forall G vars is_control es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => clocksof es' = clockof e) es' es.
  Proof with eauto.
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
    eapply mmap2_unnest_exp_annots'' in Hmap; eauto.
    rewrite clocksof_annots, Forall2_map_2, Forall2_map_2.
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
    eapply mmap2_unnest_exp_annots'' in Hmap'; eauto.
    rewrite clocksof_annots in Hck.
    assert (length (concat es') = length (annots es)) by (apply Forall2_length in Hmap'; auto).
    assert (Forall (fun e => exists y, In y (annots es) /\ (clockof e = [ck])) (concat es')) as Hf'.
    { eapply Forall2_ignore2. solve_forall.
      rewrite clockof_annot, H2; simpl in *. congruence. }
    solve_forall. destruct H1 as [_ [_ ?]]; auto.
  Qed.

  Corollary mmap2_mmap2_unnest_exp_clocksof1 : forall G vars is_control ck x tx es es' eqs' st st',
      Forall (Forall (wc_exp G vars)) es ->
      Forall2 (fun i es => Forall (eq (Con ck x (tx, i))) (clocksof es)) (seq 0 (length es)) es ->
      mmap2 (fun es => bind2 (mmap2 (unnest_exp G is_control) es) (fun es' eqs' => ret (concat es', concat eqs'))) es st = (es', eqs', st') ->
      Forall2 (fun i es => Forall (fun e => clockof e = [Con ck x (tx, i)]) es) (seq 0 (length es')) es'.
  Proof.
    intros * Hwl Htys Hmap.
    eapply mmap2_values in Hmap.
    eapply Forall2_forall2 in Htys as (?&Htys). setoid_rewrite seq_length in Htys.
    eapply Forall3_forall3 in Hmap as (?&?&Hmap).
    eapply Forall2_forall2; split; try congruence.
    intros ????? Hn Hnth1 Hnth2.
    rewrite seq_length, <-H0 in Hn. rewrite <- H0 in Hnth1.
    specialize (Htys _ b _ _ _ Hn Hnth1 eq_refl).
    specialize (Hmap b _ [] _ _ _ _ Hn eq_refl Hnth2 eq_refl) as (?&?&Hbind); repeat inv_bind.
    eapply mmap2_unnest_exp_clocksof''' in H2; eauto.
    eapply Forall_forall in Hwl; eauto.
  Qed.

  Corollary mmap2_mmap2_unnest_exp_clocksof2 : forall G vars is_control ck es es' eqs' st st',
      Forall (Forall (wc_exp G vars)) es ->
      Forall (fun es => Forall (eq ck) (clocksof es)) es ->
      mmap2 (fun es => bind2 (mmap2 (unnest_exp G is_control) es) (fun es' eqs' => ret (concat es', concat eqs'))) es st = (es', eqs', st') ->
      Forall (fun es => Forall (fun e => clockof e = [ck]) es) es'.
  Proof.
    intros * Hwl Htys Hmap.
    eapply mmap2_values in Hmap.
    eapply Forall3_ignore3 in Hmap.
    induction Hmap; inv Hwl; inv Htys; constructor; auto.
    destruct H as (?&?&?&?). repeat inv_bind.
    eapply mmap2_unnest_exp_clocksof''' in H; eauto.
  Qed.

  Corollary mmap2_mmap2_unnest_exp_clocksof3 : forall G vars is_control ck es es' eqs' st st',
      Forall (LiftO True (Forall (wc_exp G vars))) es ->
      Forall (LiftO True (fun es => Forall (eq ck) (clocksof es))) es ->
      mmap2
        (or_default_with
           (ret (None, []))
           (fun es => bind2
                     (bind2 (mmap2 (unnest_exp G is_control) es) (fun es0 eqs => ret (concat es0, concat eqs)))
                     (fun es' eqs'  => ret (Some es', eqs')))) es st = (es', eqs', st') ->
      Forall (LiftO True (fun es => Forall (fun e => clockof e = [ck]) es)) es'.
  Proof.
    intros * Hwl Htys Hmap.
    eapply mmap2_values in Hmap.
    eapply Forall3_ignore3 in Hmap.
    induction Hmap; inv Hwl; inv Htys; constructor; auto.
    destruct H as (?&?&?&?). repeat inv_bind.
    destruct x; repeat inv_bind; simpl; auto.
    eapply mmap2_unnest_exp_clocksof''' in H; eauto.
  Qed.

  Corollary mmap2_unnest_exp_clocksof :
    forall G vars is_control es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      clocksof (concat es') = clocksof es.
  Proof.
    intros.
    eapply mmap2_unnest_exp_annots in H0; eauto.
    rewrite clocksof_annots, H0, <- clocksof_annots; eauto.
  Qed.
  Hint Resolve mmap2_unnest_exp_clocksof.

  Corollary unnest_exps_clocksof : forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      unnest_exps G es st = (es', eqs', st') ->
      clocksof es' = clocksof es.
  Proof.
    intros.
    eapply unnest_exps_annots in H0; eauto.
    repeat rewrite clocksof_annots.
    congruence.
  Qed.

  Fact fby_iteexp_clockof : forall e0 e er ann es' eqs' st st',
      fby_iteexp e0 e er ann st = (es', eqs', st') ->
      clockof es' = [fst (snd ann)].
  Proof.
    intros e0 e er [ty [cl name]] es' eqs' st st' Hfby; simpl in *.
    destruct (is_constant e0); repeat inv_bind; reflexivity.
  Qed.

  Fact unnest_fby_clockof : forall anns e0s es er,
      length e0s = length anns ->
      length es = length anns ->
      clocksof (unnest_fby e0s es er anns) = List.map clock_of_nclock anns.
  Proof.
    intros * Hlen1 Hlen2.
    rewrite clocksof_annots, unnest_fby_annot, map_map; auto.
  Qed.

  Fact unnest_rhs_clockof: forall G vars e es' eqs' st st',
      wc_exp G vars e ->
      unnest_rhs G e st = (es', eqs', st') ->
      clocksof es' = clockof e.
  Proof.
    intros * Hwc Hnorm.
    eapply unnest_rhs_annot in Hnorm; eauto.
    rewrite clocksof_annots, Hnorm, <- clockof_annot. reflexivity.
  Qed.

  Corollary unnest_rhss_clocksof: forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      unnest_rhss G es st = (es', eqs', st') ->
      clocksof es' = clocksof es.
  Proof.
    intros.
    eapply unnest_rhss_annots in H0; eauto.
    repeat rewrite clocksof_annots. congruence.
  Qed.

  (** ** nclockof is also preserved by unnest_exp *)

  Fact fby_iteexp_nclockof : forall e0 e er ann es' eqs' st st',
      fby_iteexp e0 e er ann st = (es', eqs', st') ->
      nclockof es' = [snd ann].
  Proof.
    intros e0 e er [ty [cl name]] es' eqs' st st' Hfby; simpl in *.
    destruct (is_constant e0); repeat inv_bind; reflexivity.
  Qed.

  Fact unnest_merge_nclockof : forall ckid es tys ck,
      Forall (fun e => nclockof e = [ck]) (unnest_merge ckid es tys ck).
  Proof.
    intros *.
    setoid_rewrite nclockof_annot.
    specialize (unnest_merge_annot ckid es tys ck) as Hannot.
    eapply Forall2_ignore1 in Hannot.
    eapply Forall_impl; [|eauto]. intros ? (?&?&Hann).
    now rewrite Hann.
  Qed.

  Fact unnest_case_nclockof : forall e es d tys ck,
      Forall (fun e => nclockof e = [ck]) (unnest_case e es d tys ck).
  Proof.
    intros *.
    setoid_rewrite nclockof_annot.
    specialize (unnest_case_annot e es tys d ck) as Hannot.
    eapply Forall2_ignore1 in Hannot.
    eapply Forall_impl; [|eauto]. intros ? (?&?&Hann).
    now rewrite Hann.
  Qed.

  Fact unnest_exp_nclockof : forall G vars e is_control es' eqs' st st',
      wc_exp G vars e ->
      unnest_exp G is_control e st = (es', eqs', st') ->
      nclocksof es' = nclockof e.
  Proof with eauto.
    intros.
    eapply unnest_exp_annot in H0; eauto.
    rewrite nclocksof_annots, H0, <- nclockof_annot. reflexivity.
  Qed.

  Fact mmap2_unnest_exp_nclocksof : forall G vars es is_control es' eqs' st st',
      Forall (wc_exp G vars) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      nclocksof (concat es') = nclocksof es.
  Proof with eauto.
    intros.
    eapply mmap2_unnest_exp_annots in H0; eauto.
    repeat rewrite nclocksof_annots. congruence.
  Qed.

  Fact unnest_exps_nclocksof : forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      unnest_exps G es st = (es', eqs', st') ->
      nclocksof es' = nclocksof es.
  Proof with eauto.
    intros.
    eapply unnest_exps_annots in H0; eauto.
    repeat rewrite nclocksof_annots. congruence.
  Qed.

  Fact unnest_rhs_nclockof : forall G vars e es' eqs' st st',
      wc_exp G vars e ->
      unnest_rhs G e st = (es', eqs', st') ->
      nclocksof es' = nclockof e.
  Proof with eauto.
    intros.
    eapply unnest_rhs_annot in H0; eauto.
    rewrite nclocksof_annots, H0, <- nclockof_annot. reflexivity.
  Qed.

  Fact unnest_rhss_nclocksof : forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      unnest_rhss G es st = (es', eqs', st') ->
      nclocksof es' = nclocksof es.
  Proof with eauto.
    intros.
    eapply unnest_rhss_annots in H0; eauto.
    rewrite nclocksof_annots, H0, <- nclocksof_annots. reflexivity.
  Qed.

  (** ** A few additional things *)

  Definition st_clocks (st : fresh_st (Op.type * clock)) :=
    idck (st_anns st).
  Definition st_clocks' (st : fresh_st ((Op.type * clock) * option PS.t)) :=
    idck (idty (st_anns st)).

  Local Ltac In_st_clocks id t cl b :=
    unfold st_clocks, idck, idty in *;
    repeat simpl_In; exists (id, (t, cl)); split; auto;
    simpl_In; exists (id, (t, cl, b)); eauto.

  Fact idents_for_anns_incl_clocks : forall anns ids st st',
    idents_for_anns anns st = (ids, st') ->
    incl (List.map (fun '(id, (_, (cl, _))) => (id, cl)) ids) (st_clocks st').
  Proof.
    intros anns ids st st' Hids.
    apply idents_for_anns_incl in Hids.
    intros [id cl] Hin.
    repeat simpl_In. inv H.
    specialize (Hids (id, (t, cl))).
    assert (In (id, (t, cl)) (st_anns st')).
    { eapply Hids. repeat simpl_In. exists (id, (t, (cl, o))); auto. }
    In_st_clocks id t cl b.
  Qed.

  Fact idents_for_anns'_incl_clocks : forall anns ids st st',
    idents_for_anns' anns st = (ids, st') ->
    incl (List.map (fun '(id, (_, (cl, _))) => (id, cl)) ids) (st_clocks st').
  Proof.
    intros anns ids st st' Hids.
    apply idents_for_anns'_incl in Hids.
    intros [id cl] Hin.
    repeat simpl_In. inv H.
    specialize (Hids (id, (t, cl))).
    assert (In (id, (t, cl)) (st_anns st')).
    { eapply Hids. repeat simpl_In. exists (id, (t, (cl, o))); auto. }
    In_st_clocks id t cl b.
  Qed.

  Fact idents_for_anns'_clocknames : forall anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      Forall (fun x => LiftO True (eq (fst x)) (snd (snd (snd x)))) ids.
  Proof with eauto.
    induction anns; intros ids st st' Hids; repeat inv_bind...
    destruct a as [ty [cl [name|]]]; repeat inv_bind; constructor; simpl...
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
    | |- incl (st_clocks' ?st1) (st_clocks' _) =>
      unfold st_clocks', idty, idck; do 2 eapply incl_map; eapply st_follows_incl; repeat solve_st_follows
    | H : incl ?l1 ?l2 |- incl (idty ?l1) (idty ?l2) =>
      eapply incl_map; eauto
    end; auto.

  (** ** Preservation of clocking through first pass *)

  Import Permutation.

  Fact fresh_ident_wc_env : forall pref vars ty ck id st st',
      wc_env (vars++st_clocks st) ->
      wc_clock (vars++st_clocks st) ck ->
      fresh_ident pref (ty, ck) st = (id, st') ->
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
      Forall (wc_clock (vars++st_clocks st)) (map fst (map snd anns)) ->
      idents_for_anns anns st = (ids, st') ->
      wc_env (vars++st_clocks st').
  Proof with eauto.
    induction anns as [|[ty [ck id]]]; intros ids st st' Hwenv Hwc Hids;
      repeat inv_bind...
    inv Hwc.
    eapply IHanns in H0... 2:(solve_forall; repeat solve_incl).
    eapply fresh_ident_wc_env...
  Qed.

  Fact reuse_ident_wc_env : forall vars ty ck id st st',
      wc_env (vars++st_clocks st) ->
      wc_clock (vars++st_clocks st') ck ->
      reuse_ident id (ty, ck) st = (tt, st') ->
      wc_env (vars++st_clocks st').
  Proof.
    intros * Hwenv Hwc Hfresh.
    apply reuse_ident_anns in Hfresh.
    unfold st_clocks in *. rewrite Hfresh; simpl.
    rewrite <- Permutation_middle.
    constructor; simpl.
    - solve_incl. rewrite Hfresh; simpl.
      rewrite Permutation_middle. apply incl_refl.
    - eapply Forall_impl; [|eauto].
      intros; simpl in *. repeat solve_incl.
  Qed.

  Fact idents_for_anns'_st_anns : forall anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      Permutation (st_anns st') (map (fun '(id, (ty, (cl, _))) => (id, (ty, cl))) ids++(st_anns st)).
  Proof with eauto.
    induction anns; intros ids st st' Hids;
      repeat inv_bind; simpl in *...
    destruct a as [ty [cl [name|]]]; repeat inv_bind; simpl in *.
    - rewrite IHanns...
      rewrite Permutation_middle. apply Permutation_app_head.
      destruct x. apply reuse_ident_anns in H.
      rewrite H. reflexivity.
    - rewrite IHanns...
      rewrite Permutation_middle. apply Permutation_app_head.
      apply fresh_ident_anns in H.
      rewrite H. reflexivity.
  Qed.

  Fact idents_for_anns'_wc_env : forall vars anns ids st st',
      wc_env (vars++st_clocks st) ->
      Forall (wc_clock (vars++st_clocks st')) (map fst (map snd anns)) ->
      idents_for_anns' anns st = (ids, st') ->
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros vars anns ids st st' Hwenv Hwc Hids.
    specialize (idents_for_anns'_values _ _ _ _ Hids) as Hids'.
    apply idents_for_anns'_st_anns in Hids.
    unfold st_clocks. rewrite Hids.
    unfold st_clocks, idck, idty in *; repeat simpl_list.
    unfold wc_env in *. repeat rewrite Forall_app in *.
    destruct Hwenv as [Hwenv1 Hwenv2]. repeat split.
    - eapply Forall_impl... intros; simpl in *. repeat solve_incl.
    - clear Hwenv1 Hwenv2.
      rewrite <- Hids' in Hwc.
      repeat rewrite Forall_map. repeat rewrite Forall_map in Hwc.
      eapply Forall_impl...
      intros [id [ty [cl name]]] ?; simpl in *.
      intros; simpl in *.
      solve_incl. apply incl_appr'.
      rewrite Hids. unfold idck. rewrite map_app, map_map.
      eapply incl_appr', incl_refl.
    - eapply Forall_impl... intros; simpl in *. repeat solve_incl.
  Qed.

  Hint Constructors wc_exp.

  Fact hd_default_wc_exp {prefs} : forall (G : @global prefs) vars es,
      Forall (wc_exp G vars) es ->
      wc_exp G vars (hd_default es).
  Proof.
    intros G vars es Hf.
    destruct es; simpl.
    - constructor.
    - inv Hf; auto.
  Qed.
  Hint Resolve hd_default_wc_exp.

  Section unnest_node_wc.
    Variable G1 : @global elab_prefs.
    Variable G2 : @global norm1_prefs.

    Fact idents_for_anns_wc : forall vars anns ids st st',
        Forall unnamed_stream anns ->
        idents_for_anns anns st = (ids, st') ->
        Forall (wc_exp G2 (vars++st_clocks st')) (List.map (fun '(x, ann) => Evar x ann) ids).
    Proof.
      induction anns; intros ids st st' Hunnamed Hident;
        repeat inv_bind; simpl; auto.
      destruct a as [? [? ?]]. repeat inv_bind.
      inv Hunnamed. constructor; eauto.
      unfold unnamed_stream in H3; simpl in H3; subst.
      constructor.
      eapply fresh_ident_In in H.
      eapply idents_for_anns_st_follows in H0.
      eapply st_follows_incl in H; eauto.
      eapply in_or_app. right.
      In_st_clocks x t c false.
    Qed.

    Fact idents_for_anns'_wc : forall vars anns ids st st',
        idents_for_anns' anns st = (ids, st') ->
        Forall (wc_exp G2 (vars++st_clocks st')) (List.map (fun '(x, ann) => Evar x ann) ids).
    Proof.
      induction anns; intros ids st st' Hident;
        repeat inv_bind; simpl; auto.
      destruct a as [? [? ?]].
      destruct o; repeat inv_bind; constructor; eauto.
      - constructor.
        destruct x. eapply reuse_ident_In in H.
        eapply idents_for_anns'_st_follows in H0.
        eapply st_follows_incl in H; eauto.
        eapply in_or_app. right.
        In_st_clocks i t c false.
      - constructor.
        eapply fresh_ident_In in H.
        eapply idents_for_anns'_st_follows in H0.
        eapply st_follows_incl in H; eauto.
        eapply in_or_app. right.
        In_st_clocks x t c false.
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
      forall vars (k : A -> Fresh (option (list exp) * list equation) B) a es' eqs' st st',
        mmap2 k a st = (es', eqs', st') ->
        (forall st st' a es eqs', k a st = (es, eqs', st') -> st_follows st st') ->
        Forall (fun a => forall es' eqs' st0 st0',
                    k a st0 = (es', eqs', st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    LiftO True (Forall (wc_exp G2 vars)) es' /\
                    Forall (wc_equation G2 vars) eqs') a ->
        Forall (LiftO True (Forall (wc_exp G2 vars))) es' /\
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

    Fact unnest_fby_wc_exp : forall vars e0s es er anns,
        Forall (wc_exp G2 vars) e0s ->
        Forall (wc_exp G2 vars) es ->
        Forall (wc_exp G2 vars) er ->
        Forall unnamed_stream anns ->
        Forall2 (fun e0 a => clockof e0 = [a]) e0s (map clock_of_nclock anns) ->
        Forall2 (fun e a => clockof e = [a]) es (map clock_of_nclock anns) ->
        Forall (fun e => exists ckr, clockof e = [ckr]) er ->
        Forall (wc_exp G2 vars) (unnest_fby e0s es er anns).
    Proof.
      intros * Hwc1 Hwc2 Hwc3 Hunnamed Hck1 Hck2 Hck3.
      unfold unnest_fby.
      assert (length e0s = length anns) as Hlen1 by (eapply Forall2_length in Hck1; solve_length).
      assert (length es = length anns) as Hlen2 by (eapply Forall2_length in Hck2; solve_length).
      solve_forall.
      constructor; simpl in *; eauto; try rewrite app_nil_r; eauto.
      1,2:eapply Forall_impl; [|eauto]; intros ? (?&?); eauto.
    Qed.

    Fact unnest_arrow_wc_exp : forall vars e0s es er anns,
        Forall (wc_exp G2 vars) e0s ->
        Forall (wc_exp G2 vars) es ->
        Forall (wc_exp G2 vars) er ->
        Forall unnamed_stream anns ->
        Forall2 (fun e0 a => clockof e0 = [a]) e0s (map clock_of_nclock anns) ->
        Forall2 (fun e a => clockof e = [a]) es (map clock_of_nclock anns) ->
        Forall (fun e => exists ckr, clockof e = [ckr]) er ->
        Forall (wc_exp G2 vars) (unnest_arrow e0s es er anns).
    Proof.
      intros * Hwc1 Hwc2 Hwc3 Hunnamed Hck1 Hck2 Hck3.
      unfold unnest_arrow.
      assert (length e0s = length anns) as Hlen1 by (eapply Forall2_length in Hck1; solve_length).
      assert (length es = length anns) as Hlen2 by (eapply Forall2_length in Hck2; solve_length).
      solve_forall.
      constructor; simpl in *; eauto; try rewrite app_nil_r; eauto.
      1,2:eapply Forall_impl; [|eauto]; intros ? (?&?); eauto.
    Qed.

    Fact unnest_when_wc_exp : forall vars ckid ck b ty es tys,
        length es = length tys ->
        In (ckid, ck) vars ->
        Forall (wc_exp G2 vars) es ->
        Forall (fun e => clockof e = [ck]) es ->
        Forall (wc_exp G2 vars) (unnest_when ckid b es tys (Con ck ckid (ty, b), None)).
    Proof.
      intros * Hlen Hin Hwc Hck. unfold unnest_when.
      solve_forall.
      repeat constructor; auto;
        simpl; rewrite app_nil_r, H1; auto.
    Qed.

    Fact unnest_merge_wc_exp : forall vars ckid tx ck es tys,
        In (ckid, ck) vars ->
        es <> [] ->
        Forall (fun es => length es = length tys) es ->
        Forall (Forall (wc_exp G2 vars)) es ->
        Forall2 (fun i es => Forall (fun e => clockof e = [Con ck ckid (tx, i)]) es) (seq 0 (length es)) es ->
        Forall (wc_exp G2 vars) (unnest_merge (ckid, tx) es tys (ck, None)).
    Proof.
      intros *; revert es. induction tys; intros * InV Hnnil Hlen Hwc Hcks; simpl; constructor.
      - constructor; auto; try rewrite Forall_map.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + clear - Hwc.
          eapply Forall_impl; [|eauto]; intros.
          destruct a; simpl; inv H; auto.
        + rewrite Forall2_map_2, map_length.
          eapply Forall2_impl_In; [|eauto]. intros ?? _ Hin Hck; simpl in Hck.
          eapply Forall_forall in Hlen; eauto.
          destruct b; simpl in *; try congruence.
          rewrite app_nil_r. inv Hck. rewrite H1; auto.
        + eapply Forall2_ignore1 in Hcks.
          rewrite Forall_forall in *. intros ? Hin.
          specialize (Hlen _ Hin). specialize (Hcks _ Hin) as (?&?&?).
          destruct x; simpl in *; try congruence.
          rewrite app_nil_r. inv H0. rewrite H3; auto.
      - eapply IHtys; eauto; try rewrite Forall_map.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + clear - Hlen. eapply Forall_impl; [|eauto]; intros.
          destruct a0; simpl; inv H; auto.
        + clear - Hwc. eapply Forall_impl; [|eauto]; intros.
          destruct a; simpl; inv H; auto.
        + clear - Hcks. rewrite Forall2_map_2, map_length.
          eapply Forall2_impl_In; [|eauto]. intros ?? _ _ Hck; simpl in Hck.
          destruct b; simpl; inv Hck; auto.
    Qed.

    Fact unnest_case_wc_exp : forall vars e ck es d tys,
        wc_exp G2 vars e ->
        clockof e = [ck] ->
        es <> [] ->
        Forall (LiftO True (fun es => length es = length tys)) es ->
        Forall (LiftO True (Forall (wc_exp G2 vars))) es ->
        Forall (LiftO True (fun es => Forall (fun e => clockof e = [ck]) es)) es ->
        length (clocksof d) = length tys ->
        Forall (wc_exp G2 vars) d ->
        Forall (fun e => clockof e = [ck]) d ->
        Forall (wc_exp G2 vars) (unnest_case e es d tys (ck, None)).
    Proof.
      intros *; revert es d.
      induction tys; intros * Hwce Hck Hnnil Hlen Hwc Hcks Hlend Hwcd Hckd; simpl; constructor.
      - constructor; auto; try rewrite Forall_map.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + intros ? Hin. eapply in_map_iff in Hin as (?&Hopt&Hin).
          eapply option_map_inv in Hopt as (?&?&Hhd); subst.
          eapply Forall_forall in Hwc; eauto; simpl in *.
          inv Hwc; auto.
        + intros ? Hin. eapply in_map_iff in Hin as (?&Hopt&Hin).
          eapply option_map_inv in Hopt as (?&?&Hhd); subst.
          eapply Forall_forall in Hlen; eauto.
          eapply Forall_forall in Hcks; eauto. simpl in *.
          inv Hcks; simpl in *; try congruence.
          rewrite app_nil_r, H; auto.
        + intros ? Hin. eapply in_map_iff in Hin as (?&Hopt&Hin).
          eapply option_map_inv in Hopt as (?&?&Hhd); subst.
          eapply Forall_forall in Hlen; eauto.
          eapply Forall_forall in Hcks; eauto. simpl in *.
          inv Hcks; simpl in *; try congruence.
          rewrite app_nil_r, H; auto.
        + destruct d; simpl in *; try congruence.
          inv Hckd.
          rewrite app_nil_r, H1; auto.
        + destruct d; simpl in *; try congruence.
          inv Hckd.
          rewrite app_nil_r, H1; auto.
      - eapply IHtys; eauto; try rewrite Forall_map.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + clear - Hlen. eapply Forall_impl; [|eauto]; intros.
          destruct a0; simpl; inv H; auto.
          destruct l; inv H1; auto.
        + clear - Hwc. eapply Forall_impl; [|eauto]; intros.
          destruct a; simpl; inv H; simpl; auto.
        + clear - Hcks. eapply Forall_impl; [|eauto]; intros.
          destruct a; simpl; inv H; simpl; auto.
        + destruct d; simpl in *; try congruence.
          inv Hckd. rewrite H1 in Hlend; simpl in *; inv Hlend; auto.
        + inv Hwcd; simpl; auto.
        + inv Hckd; simpl; auto.
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
        { eapply unnest_exp_length in H; eauto.
          rewrite <- length_clockof_numstreams, Hck in H; auto. }
        singleton_length.
        assert (Hk:=H). apply unnest_exp_normalized_cexp, Forall_singl in H.
        assert (st_follows x1 st') as Hfollows.
        { inv H; [| | inv H1]; try destruct cl; simpl in *;
            repeat inv_bind; repeat solve_st_follows. }
        eapply Hkwc in Hk as [Hwc1 Hwc2]; auto.
        inv H; [| | inv H1]; simpl in *.
        1-8:try destruct cl as [ck' ?]; repeat inv_bind.
        1-4,6-8:constructor.
        2,4,6,8,10,12,14,15:solve_forall; repeat solve_incl.
        1-7:inv Hwc1.
        1-7:repeat split; [constructor;[|constructor]| |]; repeat solve_incl.
        1-14:simpl; repeat constructor.
        2,4,5,6,8,10,12:
          (unfold clock_of_nclock, stripname; simpl;
           match goal with
           | H : fresh_ident _ _ _ = _ |- _ =>
             apply fresh_ident_In in H
           end;
           apply in_or_app, or_intror;
           unfold st_clocks, idck; simpl_In;
           repeat eexists; eauto; auto).
        + inv H3; simpl; auto.
        + simpl_In. repeat eexists; eauto; auto.
        + inv H5; simpl; auto.
        + inv H3; simpl; auto.
        + inv H4; simpl; auto.
        + inv H3; simpl; auto.
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

    Lemma not_is_noops_exp_anon : forall vars ck e,
        normalized_lexp e ->
        wc_exp G2 vars e ->
        is_noops_exp ck e = false ->
        Forall unnamed_stream (annot e).
    Proof.
      intros * Hnormed Hwc Hnoops.
      destruct ck; simpl in *. try congruence.
      induction Hnormed; simpl in *; try congruence.
      - inv Hwc. repeat constructor.
      - inv Hwc. repeat constructor.
      - inv Hwc. repeat constructor.
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
      { solve_forall. repeat solve_incl; eauto. }
      eapply IHcks in Hes as (Hes'&Heqs'). 2-4:eauto.
      2:repeat inv_bind; repeat eexists; eauto; inv_bind; eauto.
      unfold unnest_noops_exp in H.
      rewrite <-length_annot_numstreams in H6. singleton_length.
      destruct p as (?&?&?).
      split; simpl; try constructor; try (rewrite Forall_app; split); auto.
      1,2:destruct (is_noops_exp) eqn:Hnoops; repeat inv_bind; auto.
      + repeat solve_incl.
      + eapply not_is_noops_exp_anon in Hnoops; eauto.
        rewrite Hsingl in Hnoops. eapply Forall_singl in Hnoops. inv Hnoops; simpl in *; subst.
        constructor. eapply fresh_ident_In in H.
        eapply in_or_app. right. unfold st_clocks, idck. simpl_In. exists (x0, (t, c)).
        split; auto.
        eapply st_follows_incl in H; eauto. repeat solve_st_follows.
      + repeat constructor; auto; simpl; try rewrite app_nil_r.
        * repeat solve_incl.
        * eapply not_is_noops_exp_anon in Hnoops; eauto.
          rewrite Hsingl in Hnoops. eapply Forall_singl in Hnoops. inv Hnoops; simpl in *; subst.
          rewrite nclockof_annot, Hsingl; simpl.
          do 2 constructor; auto.
        * rewrite clockof_annot, Hsingl; simpl.
          constructor; auto.
          eapply fresh_ident_In in H.
          eapply in_or_app. right. unfold st_clocks, idck. simpl_In. exists (x0, (t, c)).
          split; auto.
          eapply st_follows_incl in H; eauto. repeat solve_st_follows.
    Qed.

    Hypothesis Hiface : global_iface_eq G1 G2.

    Hint Resolve nth_In.
    Fact unnest_exp_wc : forall vars e is_control es' eqs' st st',
        wc_exp G1 (vars++st_clocks st) e ->
        unnest_exp G1 is_control e st = (es', eqs', st') ->
        Forall (wc_exp G2 (vars++st_clocks st')) es' /\
        Forall (wc_equation G2 (vars++st_clocks st')) eqs'.
    Proof with eauto.
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
        assert (length x = numstreams e) as Hlen by eauto.
        rewrite <- length_clockof_numstreams, H4 in Hlen; simpl in Hlen.
        singleton_length.
        assert (Hnorm:=H); eapply IHe in H as [Hwc1 Hwc1']; eauto.
        repeat econstructor...
        + inv Hwc1; eauto.
        + eapply unnest_exp_clockof in Hnorm; simpl in Hnorm; eauto.
          rewrite app_nil_r, H4 in Hnorm...
      - (* binop *)
        inv Hwc. repeat inv_bind.
        assert (length x = numstreams e1) as Hlen1 by eauto.
        rewrite <- length_clockof_numstreams, H7 in Hlen1; simpl in Hlen1.
        assert (length x2 = numstreams e2) as Hlen2 by eauto.
        rewrite <- length_clockof_numstreams, H8 in Hlen2; simpl in Hlen2. repeat singleton_length.
        assert (Hnorm1:=H); eapply IHe1 in H as [Hwc1 Hwc1']; eauto.
        assert (Hnorm2:=H0); eapply IHe2 in H0 as [Hwc2 Hwc2']; eauto. 2:repeat solve_incl.
        repeat econstructor...
        + inv Hwc1. repeat solve_incl.
        + inv Hwc2...
        + eapply unnest_exp_clockof in Hnorm1; simpl in Hnorm1; eauto.
          rewrite app_nil_r, H7 in Hnorm1...
        + eapply unnest_exp_clockof in Hnorm2; simpl in Hnorm2; eauto.
          rewrite app_nil_r, H8 in Hnorm2...
        + apply Forall_app; split; auto.
          solve_forall. repeat solve_incl.
      - (* fby *)
        repeat inv_bind.
        inv Hwc.
        assert (st_follows x4 x7) as Hfollows by repeat solve_st_follows.
        assert (Hnorm1:=H2). eapply mmap2_wc with (vars0:=vars++st_clocks x1) in H2 as [Hwt1 Hwt1']...
        assert (Hnorm2:=H3). eapply mmap2_wc with (vars0:=vars++st_clocks x7) in H3 as [Hwt2 Hwt2']...
        2,3:solve_mmap2.
        assert (Hnorm3:=H4). eapply unnest_resets_wc with (vars:=vars) in H4 as [Hwt3 [Hwt3' Hwt3'']]...
        2:solve_mmap2. 2:solve_forall; repeat solve_incl.
        repeat rewrite Forall_app. repeat split.
        3-5:solve_forall; repeat solve_incl.
        + eapply idents_for_anns_wc in H5...
        + assert (Forall (wc_exp G2 (vars++st_clocks st')) (unnest_fby (concat x2) (concat x6) x5 a)) as Hwcfby.
          { rewrite Forall2_eq in H13, H14.
            eapply unnest_fby_wc_exp...
            1-3:solve_forall; repeat solve_incl.
            + eapply mmap2_unnest_exp_clocksof'' in Hnorm1... congruence.
            + eapply mmap2_unnest_exp_clocksof'' in Hnorm2... congruence. }
          remember (unnest_fby _ _ _ _) as fby.
          assert (length (concat x2) = length a) as Hlen1.
          { eapply mmap2_unnest_exp_length in Hnorm1...
            apply Forall2_length in H13.
            repeat simpl_length; erewrite <- map_length, <- typesof_annots; solve_length. }
          assert (length (concat x6) = length a) as Hlen2.
          { eapply mmap2_unnest_exp_length in Hnorm2...
            apply Forall2_length in H14.
            repeat simpl_length. erewrite <- map_length, <- typesof_annots; solve_length. }
          assert (length fby = length x8).
          { rewrite Heqfby, unnest_fby_length...
            eapply idents_for_anns_length in H5... }
          assert (Forall2 (fun '(_, ck) e => nclockof e = [ck]) (map snd x8) fby) as Htys.
          { eapply idents_for_anns_values in H5; subst.
            specialize (unnest_fby_annot' _ _ _ x5 Hlen1 Hlen2) as Hanns; eauto. clear - Hanns.
            eapply Forall2_swap_args. solve_forall.
            destruct a0 as [ty [ck ?]]; simpl in *. rewrite nclockof_annot, H1; auto. }
          eapply mk_equations_Forall. solve_forall.
          repeat constructor; eauto; simpl; rewrite app_nil_r.
          * destruct a0 as [ty [ck name]].
            eapply idents_for_anns_values in H5; rewrite <- H5 in H16.
            eapply Forall_forall in H16. 2:simpl_In; exists (i, (ty, (ck, name))); auto.
            inv H16. simpl in *; subst.
            rewrite H6; constructor; simpl; auto.
          * destruct a0 as [ty [ck ?]]; simpl in *.
            rewrite clockof_nclockof, H6. repeat constructor.
            eapply idents_for_anns_incl_clocks in H5.
            apply in_or_app, or_intror, H5. simpl_In. eexists; split; eauto. reflexivity.
      - (* arrow *)
        repeat inv_bind.
        inv Hwc.
        assert (st_follows x4 x7) as Hfollows by repeat solve_st_follows.
        assert (Hnorm1:=H2). eapply mmap2_wc with (vars0:=vars++st_clocks x1) in H2 as [Hwt1 Hwt1']...
        assert (Hnorm2:=H3). eapply mmap2_wc with (vars0:=vars++st_clocks x7) in H3 as [Hwt2 Hwt2']...
        2,3:solve_mmap2.
        assert (Hnorm3:=H4). eapply unnest_resets_wc with (vars:=vars) in H4 as [Hwt3 [Hwt3' Hwt3'']]...
        2:solve_mmap2. 2:solve_forall; repeat solve_incl.
        repeat rewrite Forall_app. repeat split.
        3-5:solve_forall; repeat solve_incl.
        + eapply idents_for_anns_wc in H5...
        + assert (Forall (wc_exp G2 (vars++st_clocks st')) (unnest_arrow (concat x2) (concat x6) x5 a)) as Hwcarrow.
          { rewrite Forall2_eq in H13, H14.
            eapply unnest_arrow_wc_exp...
            1-3:solve_forall; repeat solve_incl.
            + eapply mmap2_unnest_exp_clocksof'' in Hnorm1... congruence.
            + eapply mmap2_unnest_exp_clocksof'' in Hnorm2... congruence. }
          remember (unnest_arrow _ _ _ _) as arrow.
          assert (length (concat x2) = length a) as Hlen1.
          { eapply mmap2_unnest_exp_length in Hnorm1...
            apply Forall2_length in H13.
            repeat simpl_length; erewrite <- map_length, <- typesof_annots; solve_length. }
          assert (length (concat x6) = length a) as Hlen2.
          { eapply mmap2_unnest_exp_length in Hnorm2...
            apply Forall2_length in H14.
            repeat simpl_length. erewrite <- map_length, <- typesof_annots; solve_length. }
          assert (length arrow = length x8).
          { rewrite Heqarrow, unnest_arrow_length...
            eapply idents_for_anns_length in H5... }
          assert (Forall2 (fun '(_, ck) e => nclockof e = [ck]) (map snd x8) arrow) as Htys.
          { eapply idents_for_anns_values in H5; subst.
            specialize (unnest_arrow_annot' _ _ _ x5 Hlen1 Hlen2) as Hanns; eauto. clear - Hanns.
            eapply Forall2_swap_args. solve_forall.
            destruct a0 as [ty [ck ?]]; simpl in *. rewrite nclockof_annot, H1; auto. }
          eapply mk_equations_Forall. solve_forall.
          repeat constructor; eauto; simpl; rewrite app_nil_r.
          * destruct a0 as [ty [ck name]].
            eapply idents_for_anns_values in H5; rewrite <- H5 in H16.
            eapply Forall_forall in H16. 2:simpl_In; exists (i, (ty, (ck, name))); auto.
            inv H16. simpl in *; subst.
            rewrite H6; constructor; simpl; auto.
          * destruct a0 as [ty [ck ?]]; simpl in *.
            rewrite clockof_nclockof, H6. repeat constructor.
            eapply idents_for_anns_incl_clocks in H5.
            apply in_or_app, or_intror, H5. simpl_In. eexists; split; eauto. reflexivity.
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
        assert (Hnorm1:=H0). eapply mmap2_wc in H0 as (?&?). 2:(intros; repeat solve_st_follows).
        2:{ solve_forall; repeat inv_bind.
            eapply mmap2_wc with (vars0:=vars++st_clocks x2) in H5... solve_mmap2. }
        assert (Forall (wc_exp G2 (vars++st_clocks st')) (unnest_merge (x0, tx) x tys (ck, None))) as Hwcexp.
        { eapply unnest_merge_wc_exp...
          + destruct is_control; repeat solve_incl.
          + eapply mmap2_length_1 in Hnorm1.
            intro contra; subst. destruct es; simpl in *; try congruence.
          + apply mmap2_mmap2_unnest_exp_length in Hnorm1. 2:solve_forall.
            clear - Hnorm1 H7.
            induction Hnorm1; inv H7; constructor; auto.
            now rewrite H2, H, length_clocksof_annots.
          + eapply Forall_concat. solve_forall; destruct is_control; repeat solve_incl.
          + eapply mmap2_mmap2_unnest_exp_clocksof1; eauto. }
        destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split; eauto.
        3:solve_forall; repeat solve_incl.
        + eapply idents_for_anns_wc in H1...
          solve_forall. unfold unnamed_stream; auto.
        + assert (Forall (fun e : exp => nclockof e = [(ck, None)]) (unnest_merge (x0, tx) x tys (ck, None))) as Hnck.
          { eapply unnest_merge_nclockof; solve_length. }
          eapply mk_equations_Forall. solve_forall.
          2:(rewrite unnest_merge_length; eapply idents_for_anns_length in H1; solve_length).
          repeat split. 2,3:rewrite app_nil_r.
          * repeat constructor...
          * rewrite H8. repeat constructor.
          * rewrite clockof_nclockof, H8; simpl. repeat constructor.
            assert (H':=H1). apply idents_for_anns_values in H'.
            apply idents_for_anns_incl_clocks in H1.
            destruct a as [ty [ck' name']].
            apply in_or_app; right. apply H1.
            simpl_In. exists (i, (ty, (ck', name'))). split; auto.
            assert (In (ty, (ck', name')) (map snd x3)) by (simpl_In; exists (i, (ty, (ck', name'))); auto).
            rewrite H' in H10. simpl_In. inv H10; auto.
      - (* case *)
        inv Hwc; repeat inv_bind.
        assert (st_follows x1 x4) as Hfollows.
        { repeat solve_st_follows. destruct a; repeat solve_st_follows. }
        assert (Hnorm0:=H1). eapply IHe in H1 as (Hwc0&?)...
        assert (Hnorm1:=H2). eapply mmap2_wc' in H2 as (?&?). 2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall; repeat inv_bind.
            destruct a; simpl in *; repeat inv_bind; simpl; auto.
            eapply mmap2_wc with (vars0:=vars++st_clocks x4) in H14... solve_mmap2.
            eapply Forall_forall in H8; eauto. repeat solve_incl. }
        assert (Hnorm2:=H3). eapply mmap2_wc with (vars0:=vars++st_clocks x7) in H3 as (?&?).
        2:intros; repeat solve_st_follows.
        2:{ solve_mmap2. }
        assert (length x = 1); try singleton_length.
        { eapply unnest_exp_length in Hnorm0...
          now rewrite Hnorm0, <-length_clockof_numstreams, H6. }
        apply Forall_singl in Hwc0.
        assert (Forall (wc_exp G2 (vars++st_clocks st')) (unnest_case e0 x2 (concat x8) tys (ck, None))) as Hwcexp.
        { eapply unnest_case_wc_exp...
          + destruct is_control; repeat solve_incl.
          + apply unnest_exp_clockof in Hnorm0; simpl in *...
            rewrite app_nil_r in Hnorm0. congruence.
          + eapply mmap2_length_1 in Hnorm1.
            intro contra; subst. destruct es; simpl in *; try congruence.
          + apply mmap2_mmap2_unnest_exp_length' in Hnorm1.
            2:{ solve_forall. destruct a; simpl; eauto. }
            clear - Hnorm1 H10.
            induction Hnorm1; constructor; eauto with datatypes.
            destruct y; simpl in *; auto.
            edestruct H as (?&?&Heq); subst; eauto.
            erewrite H10, length_clocksof_annots, <-Heq; auto.
          + solve_forall. destruct a; simpl in *; auto.
            solve_forall; destruct is_control; repeat solve_incl.
          + eapply mmap2_mmap2_unnest_exp_clocksof3 in Hnorm1; eauto.
            eapply Forall_forall; intros [|] Hin; simpl; auto.
            eapply Forall_forall; intros [|] Hin; simpl; auto.
          + rewrite length_clocksof_annots. eapply mmap2_unnest_exp_annots_length in Hnorm2; eauto.
            rewrite Hnorm2, <-length_clocksof_annots; auto.
          + solve_forall; destruct is_control; repeat solve_incl.
          + eapply mmap2_unnest_exp_clocksof''' in Hnorm2; eauto.
        }
        destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split; eauto.
        1,2,5-7:solve_forall; repeat solve_incl.
        + eapply idents_for_anns_wc in H4...
          solve_forall. unfold unnamed_stream; auto.
        + assert (Forall (fun e : exp => nclockof e = [(ck, None)]) (unnest_case e0 x2 (concat x8) tys (ck, None))) as Hnck.
          { eapply unnest_case_nclockof; solve_length. }
          eapply mk_equations_Forall. solve_forall.
          2:(rewrite unnest_case_length; eapply idents_for_anns_length in H4; solve_length).
          repeat split. 2,3:rewrite app_nil_r.
          * repeat constructor...
          * rewrite H17. repeat constructor.
          * rewrite clockof_nclockof, H17; simpl. repeat constructor.
            assert (H':=H4). apply idents_for_anns_values in H'.
            apply idents_for_anns_incl_clocks in H4.
            destruct a as [ty [ck' name']].
            apply in_or_app; right. apply H4.
            simpl_In. exists (i, (ty, (ck', name'))). split; auto.
            assert (In (ty, (ck', name')) (map snd x)) by (simpl_In; exists (i, (ty, (ck', name'))); auto).
            rewrite H' in H19. simpl_In. inv H19; auto.
      - (* app *)
        assert (st_follows x4 x7) as Hfollows by repeat solve_st_follows.
        eapply unnest_resets_wc in H3 as (Hck2&Hwt2&Hwt2'); eauto.
        2:solve_mmap2. 2:solve_forall; repeat solve_incl.
        assert (Hnorm:=H1). eapply mmap2_wc with (vars0:=vars++st_clocks x1) in H1 as [Hwc1 Hwc1']...
        2:solve_mmap2.

        assert (length (find_node_incks G1 f) = length (concat x6)) as Hlen1.
        { unfold find_node_incks. rewrite H11.
          eapply Forall2_length in H12. rewrite map_length.
          eapply mmap2_unnest_exp_length in Hnorm; eauto. rewrite length_nclocksof_annots in H12.
          rewrite length_idck in H12. congruence. }
        assert (Forall (fun e : exp => numstreams e = 1) (concat x6)) as Hnum.
        { eapply mmap2_unnest_exp_numstreams; eauto. }

        destruct Hiface as (_&Hiface').
        specialize (Hiface' f). rewrite H11 in Hiface'. inv Hiface'.
        destruct H5 as (?&?&Hin&Hout).
        repeat econstructor; simpl in *...
        + eapply idents_for_anns'_wc...
        + eapply unnest_noops_exps_wc with (vars:=vars) in H2 as (?&?)...
          solve_forall; repeat solve_incl.
        + solve_forall; repeat solve_incl.
        + erewrite <-Hin, unnest_noops_exps_nclocksof, mmap2_unnest_exp_nclocksof...
        + erewrite <-Hout, idents_for_anns'_values...
        + rewrite app_nil_r, map_map, Forall2_map_1, Forall2_map_2, <- Forall2_same.
          eapply idents_for_anns'_clocknames...
        + unfold clock_of_nclock, stripname.
          rewrite app_nil_r, map_map, Forall2_map_1, Forall2_map_2, <- Forall2_same.
          eapply idents_for_anns'_incl_clocks in H4.
          apply Forall_forall; intros.
          apply in_or_app; right. apply H4.
          rewrite in_map_iff. exists x; split; auto. destruct x as [? [? [? ?]]]; auto.
        + repeat rewrite Forall_app; repeat split.
          2:eapply unnest_noops_exps_wc in H2 as (?&?); eauto.
          1-3:solve_forall; repeat solve_incl.
    Qed.

    Corollary mmap2_unnest_exp_wc : forall vars is_control es es' eqs' st st',
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        mmap2 (unnest_exp G1 is_control) es st = (es', eqs', st') ->
        Forall (wc_exp G2 (vars++st_clocks st')) (concat es') /\
        Forall (wc_equation G2 (vars++st_clocks st')) (concat eqs').
    Proof.
      intros * Hwt Hmap.
      eapply mmap2_wc in Hmap; eauto.
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

    Fact unnest_rhs_wc : forall vars e es' eqs' st st',
        wc_exp G1 (vars++st_clocks st) e ->
        unnest_rhs G1 e st = (es', eqs', st') ->
        Forall (wc_exp G2 (vars++st_clocks st')) es' /\
        Forall (wc_equation G2 (vars++st_clocks st')) eqs'.
    Proof with eauto.
      intros * Hwc Hnorm.
      destruct e; unfold unnest_rhs in Hnorm;
        try (solve [eapply unnest_exp_wc in Hnorm; eauto]); repeat inv_bind. 3:inv Hwc.
      - (* fby *)
        inv Hwc.
        rewrite Forall2_eq in H9, H10.
        repeat inv_bind.
        assert (H':=H). eapply unnest_exps_wc in H' as [Hwc1 Hwc1']...
        assert (H0':=H0). eapply unnest_exps_wc with (vars:=vars) in H0' as [Hwc2 Hwc2']...
        2:solve_forall; repeat solve_incl.
        assert (H1':=H1). eapply unnest_resets_wc with (vars:=vars) in H1' as [Hwc3 [Hwc3' Hwc3'']]...
        2,3:solve_forall. 2:eapply unnest_exp_wc in H4; eauto. 2,3:repeat solve_incl.
        repeat rewrite Forall_app; repeat split.
        2-4:solve_forall; repeat solve_incl.
        eapply unnest_fby_wc_exp...
        1,2:solve_forall; repeat solve_incl.
        + unfold unnest_exps in H; repeat inv_bind.
          eapply mmap2_unnest_exp_clocksof'' in H... congruence.
        + unfold unnest_exps in H0; repeat inv_bind.
          eapply mmap2_unnest_exp_clocksof'' in H0... congruence.
      - (* arrow *)
        inv Hwc.
        rewrite Forall2_eq in H9, H10.
        repeat inv_bind.
        assert (H':=H). eapply unnest_exps_wc in H' as [Hwc1 Hwc1']...
        assert (H0':=H0). eapply unnest_exps_wc with (vars:=vars) in H0' as [Hwc2 Hwc2']...
        2:solve_forall; repeat solve_incl.
        assert (H1':=H1). eapply unnest_resets_wc with (vars:=vars) in H1' as [Hwc3 [Hwc3' Hwc3'']]...
        2,3:solve_forall. 2:eapply unnest_exp_wc in H4; eauto. 2,3:repeat solve_incl.
        repeat rewrite Forall_app; repeat split.
        2-4:solve_forall; repeat solve_incl.
        eapply unnest_arrow_wc_exp...
        1,2:solve_forall; repeat solve_incl.
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
          eapply unnest_exps_length in Hnorm; eauto. rewrite length_nclocksof_annots, length_idck in H9.
          congruence. }
        assert (Forall (fun e : exp => numstreams e = 1) x) as Hnum.
        { eapply unnest_exps_numstreams; eauto. }

        destruct Hiface as (_&Hiface').
        specialize (Hiface' i). rewrite H8 in Hiface'. inv Hiface'.
        destruct H2 as (?&?&Hin&Hout).

        repeat econstructor...
        + eapply unnest_noops_exps_wc in H0 as (?&?)...
          solve_forall; repeat solve_incl.
        + erewrite <-Hin, unnest_noops_exps_nclocksof, unnest_exps_nclocksof...
        + rewrite <-Hout...
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
      eapply mmap2_wc in H; eauto.
      solve_forall.
      eapply unnest_rhs_wc with (vars:=vars) in H2 as [? ?]; eauto.
      split. 1,2:solve_forall. 1,2,3:repeat solve_incl.
    Qed.

    Fact unnest_equation_wc_eq : forall vars e eqs' st st',
        wc_equation G1 (vars++st_clocks st) e ->
        unnest_equation G1 e st = (eqs', st') ->
        Forall (wc_equation G2 (vars++st_clocks st')) eqs'.
    Proof with eauto.
      intros vars [xs es] eqs' st st' Hwc Hnorm.
      unfold unnest_equation in Hnorm. repeat inv_bind.
      destruct Hwc as [Hwc1 [Hwc2 Hwc3]].
      assert (st_follows st st') as Hfollows by eauto.
      assert (H':=H). eapply unnest_rhss_wc in H' as [Hwc1' Hwc1'']...
      apply Forall_app; split...
      rewrite clocksof_nclocksof, Forall2_map_2 in Hwc3.
      eapply Forall2_Forall2 in Hwc2; [|eapply Hwc3]. clear Hwc3.
      replace (nclocksof es) with (nclocksof x) in Hwc2.
      2: { eapply unnest_rhss_nclocksof in H... }
      clear H Hwc1 Hwc1''.
      revert es xs Hwc2.
      induction x; intros; simpl in *; try constructor.
      + inv Hwc2; simpl; auto.
      + inv Hwc1'.
        assert (length (firstn (numstreams a) xs) = length (nclockof a)) as Hlen1.
        { apply Forall2_length in Hwc2. rewrite app_length in Hwc2.
          rewrite firstn_length, Hwc2, length_nclockof_numstreams.
          apply Nat.min_l. omega. }
        rewrite <- (firstn_skipn (numstreams a) xs) in Hwc2.
        apply Forall2_app_split in Hwc2 as [Hwc2 _]...
        repeat constructor...
        * simpl. rewrite app_nil_r.
          eapply Forall2_impl_In... intros; simpl in *. destruct H3...
        * simpl. rewrite app_nil_r, clockof_nclockof, Forall2_map_2.
          eapply Forall2_impl_In... intros; simpl in *. destruct H3...
          apply in_or_app. apply in_app_or in H3. destruct H3...
          right. eapply st_follows_clocks_incl...
      + inv Hwc1'. apply IHx...
        assert (length (firstn (numstreams a) xs) = length (nclockof a)) as Hlen1.
        { apply Forall2_length in Hwc2. rewrite app_length in Hwc2.
          rewrite firstn_length, Hwc2, length_nclockof_numstreams.
          apply Nat.min_l. omega. }
        rewrite <- (firstn_skipn (numstreams a) xs) in Hwc2.
        apply Forall2_app_split in Hwc2 as [_ Hwc2]...
    Qed.

    Corollary unnest_equations_wc_eq : forall vars eqs eqs' st st',
        Forall (wc_equation G1 (vars++st_clocks st)) eqs ->
        unnest_equations G1 eqs st = (eqs', st') ->
        Forall (wc_equation G2 (vars++st_clocks st')) eqs'.
    Proof with eauto.
      induction eqs; intros * Hwc Hnorm;
        unfold unnest_equations in *; simpl in *; repeat inv_bind; simpl...
      assert (st_follows st x1) as Hfollows1 by repeat solve_st_follows.
      assert (st_follows x1 st') as Hfollows2 by repeat solve_st_follows.
      inv Hwc. eapply unnest_equation_wc_eq in H...
      assert (unnest_equations G1 eqs x1 = (concat x2, st')) as Hnorm.
      { unfold unnest_equations; repeat inv_bind; eauto. }
      apply IHeqs in Hnorm... 2:solve_forall; repeat solve_incl.
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
      - eapply fresh_ident_wc_env in Hfresh; eauto.
        assert (Hwc' := Hk0). eapply unnest_exp_wc in Hwc' as [Hwc' _]; eauto.
        eapply wc_exp_clocksof in Hwc'; eauto.
        eapply unnest_exp_no_fresh in Hk0.
        rewrite Hk0 in Hwc'; simpl in Hwc'; rewrite app_nil_r in Hwc'.
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
      1:intros ? ? (?&?) ? ? Hun; eauto.
      eapply Forall2_combine'. eapply Forall2_forall2. split; auto.
      intros * Hn Hnth1 Hnth2 * Henv' Hunt Hf1 Hf2; subst.
      unfold unnest_noops_exp in Hunt.
      assert (In (nth n es b) es) as Hin by (eapply nth_In; congruence).
      eapply Forall_forall in Hnormed; eauto.
      eapply Forall_forall in Hnum; eauto.
      eapply Forall_forall in Hwc; eauto.
      rewrite <- length_annot_numstreams in Hnum. singleton_length.
      destruct p as (?&?&?).
      destruct (is_noops_exp _ _); repeat inv_bind; eauto.
      eapply fresh_ident_wc_env in H0; eauto.
      eapply wc_exp_clockof in Hwc; eauto.
      rewrite clockof_annot, Hsingl in Hwc; simpl in Hwc.
      erewrite normalized_lexp_no_fresh, app_nil_r in Hwc; auto. inv Hwc.
      repeat solve_incl.
    Qed.

    Fact unnest_exp_wc_env : forall vars e is_control es' eqs' st st',
        wc_env (vars++st_clocks st) ->
        wc_exp G1 (vars++st_clocks st) e ->
        unnest_exp G1 is_control e st = (es', eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof with eauto.
      Local Ltac solve_mmap2' :=
        solve_forall;
        match goal with
        | Hnorm : unnest_exp _ _ _ _ = _, H : context [unnest_exp _ _ _ _ = _ -> _] |- _ =>
          eapply H in Hnorm; eauto; repeat solve_incl
        end.
      induction e using exp_ind2; intros is_control es' eqs' st st' Hwenv Hwc Hnorm;
        assert (Hnorm':=Hnorm); apply unnest_exp_fresh_incl in Hnorm';
          simpl in *; repeat inv_bind...
      - (* unop *)
        inv Hwc; eauto.
      - (* binop *)
        inv Hwc.
        assert (st_follows st x1) as Hfollows by eauto.
        eapply IHe1 in H...
        eapply IHe2 in H0...
        repeat solve_incl.
      - (* fby *)
        assert (st_follows x4 x7) as Hfollows by repeat solve_st_follows.
        inv Hwc.
        rewrite Forall2_eq in H13, H14.
        assert (Hwenv1:=H2). eapply mmap2_wc_env in Hwenv1... 2:solve_mmap2'.
        assert (Hwenv2:=H3). eapply mmap2_wc_env in Hwenv2... 2:solve_mmap2'.
        assert (Hwenv3:=H4). eapply unnest_resets_wc_env in Hwenv3... 2:solve_mmap2'.
        2:solve_forall; repeat solve_incl.
        eapply idents_for_anns_wc_env in H5...
        assert (Forall (wc_clock ((vars ++ st_clocks x1))) (map clock_of_nclock a)).
        { rewrite H13.
          eapply wc_exp_clocksof in H10... eapply Forall_impl; [|eauto]. intros.
          eapply wc_clock_incl; [|eauto]. rewrite <- app_assoc in *.
          apply incl_appr', incl_app; repeat solve_incl.
          apply mmap2_unnest_exp_fresh_incl in H2...
          unfold st_clocks. apply incl_map, H2. }
        solve_forall; repeat solve_incl.
      - (* arrow *)
        assert (st_follows x4 x7) as Hfollows by repeat solve_st_follows.
        inv Hwc.
        rewrite Forall2_eq in H13, H14.
        assert (Hwenv1:=H2). eapply mmap2_wc_env in Hwenv1... 2:solve_mmap2'.
        assert (Hwenv2:=H3). eapply mmap2_wc_env in Hwenv2... 2:solve_mmap2'.
        assert (Hwenv3:=H4). eapply unnest_resets_wc_env in Hwenv3... 2:solve_mmap2'.
        2:solve_forall; repeat solve_incl.
        eapply idents_for_anns_wc_env in H5...
        assert (Forall (wc_clock ((vars ++ st_clocks x1))) (map clock_of_nclock a)).
        { rewrite H13.
          eapply wc_exp_clocksof in H10... eapply Forall_impl; [|eauto]. intros.
          eapply wc_clock_incl; [|eauto]. rewrite <- app_assoc in *.
          apply incl_appr', incl_app; repeat solve_incl.
          apply mmap2_unnest_exp_fresh_incl in H2...
          unfold st_clocks. apply incl_map, H2. }
        solve_forall; repeat solve_incl.
      - (* when *)
        inv Hwc; repeat inv_bind.
        eapply mmap2_wc_env in H0... solve_mmap2'.
      - (* merge *)
        inv Hwc; repeat inv_bind.
        assert (Hwenv1:=H0). eapply mmap2_wc_env in Hwenv1...
        2:(intros; repeat solve_st_follows).
        2:{ solve_forall; repeat inv_bind. eapply mmap2_wc_env in H7...
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
        2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall; destruct a; repeat inv_bind; auto.
            eapply mmap2_wc_env in H15...
            solve_mmap2'. eapply Forall_forall in H8; eauto. repeat solve_incl. }
        assert (Hwenv3:=H3). eapply mmap2_wc_env in Hwenv3... 2:solve_mmap2'.
        destruct is_control; repeat inv_bind...
        eapply idents_for_anns_wc_env in H4...
        repeat rewrite Forall_map.
        rewrite Forall_forall. intros ty _; simpl.
        eapply wc_exp_clockof in H5... rewrite H6 in H5. inv H5.
        solve_incl. rewrite <- app_assoc. apply incl_appr', incl_app; [repeat solve_incl|].
        unfold st_clocks. apply incl_map.
        eapply unnest_exp_fresh_incl in H1. etransitivity...
        apply st_follows_incl. repeat solve_st_follows.
      - (* app *)
        assert (st_follows x4 st') as Hfollows by repeat solve_st_follows.
        assert (Hwc':=Hwc). inv Hwc'.
        assert (Hwenv1:=H1). eapply mmap2_wc_env in Hwenv1... 2:solve_mmap2'.
        assert (Hwenv2:=H2). eapply unnest_noops_exps_wc_env in Hwenv2...
        2:{ unfold find_node_incks. rewrite H11.
            eapply Forall2_length in H12. rewrite map_length.
            eapply mmap2_unnest_exp_length in H1; eauto. rewrite length_nclocksof_annots, length_idck in H12.
            congruence. }
        2:{ eapply mmap2_unnest_exp_numstreams; eauto. }
        2:{ eapply mmap2_unnest_exp_wc in H1 as (?&?); eauto. }
        eapply unnest_resets_wc_env in H3... 2:solve_mmap2'.
        2:solve_forall; repeat solve_incl.
        eapply idents_for_anns'_wc_env...
        apply wc_exp_clockof in Hwc... simpl in Hwc.
        unfold clock_of_nclock, stripname in Hwc.
        rewrite map_map. eapply Forall_impl; [|eauto].
        intros. rewrite <- app_assoc in H5. repeat solve_incl.
        apply incl_app; [repeat solve_incl|].
        unfold st_clocks. apply incl_map...
    Qed.

    Corollary mmap2_unnest_exp_wc_env : forall vars es is_control es' eqs' st st',
        wc_env (vars++st_clocks st) ->
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        mmap2 (unnest_exp G1 is_control) es st = (es', eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof.
      intros.
      eapply mmap2_wc_env in H1; eauto.
      rewrite Forall_forall in *; intros.
      eapply unnest_exp_wc_env in H4; eauto.
      eapply H0 in H2. repeat solve_incl.
    Qed.

    Corollary unnest_exps_wc_env : forall vars es es' eqs' st st',
        wc_env (vars++st_clocks st) ->
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        unnest_exps G1 es st = (es', eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof with eauto.
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
    Proof with eauto.
      intros * Hwenv Hwc Hnorm.
      destruct e; unfold unnest_rhs in Hnorm;
        try (solve [eapply unnest_exp_wc_env in Hnorm; eauto]);
        repeat inv_bind.
      - (* fby *)
        inv Hwc.
        assert (Hwenv1:=H). eapply unnest_exps_wc_env in Hwenv1...
        assert (Hwenv2:=H0). eapply unnest_exps_wc_env in Hwenv2...
        2:solve_forall; repeat solve_incl.
        eapply unnest_resets_wc_env in H1...
        2:solve_forall; repeat solve_incl.
        eapply Forall_forall; intros.
        eapply unnest_exp_wc_env in H4; eauto.
        eapply Forall_forall in H8; eauto. repeat solve_incl.
      - (* arrow *)
        inv Hwc.
        assert (Hwenv1:=H). eapply unnest_exps_wc_env in Hwenv1...
        assert (Hwenv2:=H0). eapply unnest_exps_wc_env in Hwenv2...
        2:solve_forall; repeat solve_incl.
        eapply unnest_resets_wc_env in H1...
        2:solve_forall; repeat solve_incl.
        eapply Forall_forall; intros.
        eapply unnest_exp_wc_env in H4; eauto.
        eapply Forall_forall in H8; eauto. repeat solve_incl.
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
          eapply unnest_exps_length in Hnorm; eauto. rewrite length_nclocksof_annots, length_idck in H9.
          congruence.
        + eapply unnest_exps_numstreams; eauto.
        + eapply unnest_exps_wc in Hnorm as (?&?); eauto.
    Qed.

    Corollary unnest_rhss_wc_env : forall vars es es' eqs' st st',
        wc_env (vars++st_clocks st) ->
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        unnest_rhss G1 es st = (es', eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof with eauto.
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
    Proof with eauto.
      intros vars [xs es] * Hwenv [Hwc _] Hnorm.
      unfold unnest_equation in Hnorm. repeat inv_bind.
      eapply unnest_rhss_wc_env in H...
    Qed.

    Corollary unnest_equations_wc_env : forall vars eqs eqs' st st',
        wc_env (vars++st_clocks st) ->
        Forall (wc_equation G1 (vars++st_clocks st)) eqs ->
        unnest_equations G1 eqs st = (eqs', st') ->
        wc_env (vars++st_clocks st').
    Proof with eauto.
      induction eqs; intros * Hwenv Hwc Hnorm;
        unfold unnest_equations in *; simpl in *; repeat inv_bind...
      assert (st_follows st x1) as Hfollows1 by repeat solve_st_follows.
      inv Hwc. eapply unnest_equation_wc_env in H...
      assert (unnest_equations G1 eqs x1 = (concat x2, st')) as Hnorm.
      { unfold unnest_equations; repeat inv_bind; eauto. }
      apply IHeqs in Hnorm as Hwenv2... solve_forall; repeat solve_incl.
    Qed.

    Lemma unnest_node_wc : forall n,
        wc_node G1 n ->
        wc_node G2 (unnest_node G1 n).
    Proof with eauto.
      intros * [Hin [Hout [Henv Heq]]].
      unfold unnest_node.
      repeat constructor; simpl; auto.
      - destruct (unnest_equations _ _ _) as (eqs'&st') eqn:Heqres.
        unfold idck. repeat rewrite map_app.
        eapply unnest_equations_wc_env in Heqres as Henv'...
        2,3:unfold st_clocks; rewrite init_st_anns, app_nil_r...
        2:rewrite (Permutation_app_comm (n_vars _)) in Heq...
        unfold idck in Henv'; repeat rewrite map_app in Henv'; repeat rewrite <- app_assoc in Henv'...
      - destruct (unnest_equations _ _ _) as (eqs'&st') eqn:Heqres.
        unfold idck. repeat rewrite map_app.
        eapply unnest_equations_wc_eq in Heqres as Hwc'...
        2:unfold st_clocks; rewrite init_st_anns, app_nil_r...
        unfold st_clocks, idck in Hwc'; repeat rewrite map_app in Hwc'; repeat rewrite <- app_assoc in *.
        solve_forall; solve_incl.
        apply incl_appr', incl_appr'.
        rewrite Permutation_app_comm. reflexivity.
    Qed.

  End unnest_node_wc.

  Lemma unnest_global_wc : forall G,
      wc_global G ->
      wc_global (unnest_global G).
  Proof.
    intros (enums&nds). unfold wc_global, CommonTyping.wt_program; simpl.
    induction nds; intros * Hwc; simpl; inv Hwc; auto.
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
    Variable G1 : @global norm1_prefs.
    Variable G2 : @global norm2_prefs.

    Hypothesis Hiface : global_iface_eq G1 G2.
    Local Hint Resolve iface_eq_wc_exp.

    Fact add_whens_clockof : forall e ty ck,
      clockof e = [Cbase] ->
      clockof (add_whens e ty ck) = [ck].
    Proof. induction ck; try destruct p; intros Hlen; auto. Qed.

    Fact add_whens_wc_exp : forall vars e ty ck,
        clockof e = [Cbase] ->
        wc_exp G1 vars e ->
        wc_clock vars ck ->
        wc_exp G2 vars (add_whens e ty ck).
    Proof with eauto.
      induction ck; try destruct p; intros Hclof Hwc Hwc2; inv Hwc2; simpl...
      repeat constructor; simpl... 1,2:rewrite app_nil_r.
      + rewrite add_whens_clockof...
      + rewrite add_whens_clockof...
    Qed.

    Fact fby_iteexp_wc_exp : forall vars e0 e xr ty ck name e' eqs' st st' ,
        wc_exp G1 (vars++st_clocks' st) e0 ->
        wc_exp G1 (vars++st_clocks' st) e ->
        clockof e0 = [ck] ->
        clockof e = [ck] ->
        unnamed_stream (ty, (ck, name)) ->
        Forall (fun '(xr, (ckr, _)) => In (xr, ckr) (vars++st_clocks' st)) xr ->
        fby_iteexp e0 e xr (ty, (ck, name)) st = (e', eqs', st') ->
        wc_exp G2 (vars++st_clocks' st') e'.
    Proof with eauto.
      intros * Hwc1 Hwc2 Hck1 Hck2 Hunnamed Hr Hfby.
      unfold fby_iteexp in Hfby; simpl in *.
      inv Hunnamed; simpl in H; subst.
      assert (st_follows st st') as Hfollows.
      { eapply (fby_iteexp_st_follows _ _ _ (ty, (ck, None))) in Hfby; eauto. }
      repeat inv_bind; repeat econstructor; simpl; try congruence...
      2-4:intros ? [Heq|[Heq|Heq]]; inv Heq.
      3-4:simpl; rewrite app_nil_r; unfold clock_of_nclock, stripname; simpl;
        rewrite Hck1; repeat constructor.
      2:constructor; eauto; eapply iface_eq_wc_exp in Hwc1; eauto; repeat solve_incl.
      1-2:(apply in_or_app, or_intror; unfold st_clocks', idty, idck; rewrite map_map).
      2:(simpl_In; exists (x2, (ty, ck, None)); simpl; split; auto;
         eapply fresh_ident_In in H0; eauto).
      1:(apply init_var_for_clock_In in H as (?&?&H); simpl in *;
         eapply st_follows_incl in H; eauto;
         simpl_In; eexists; split; eauto; eauto).
    Qed.

    Fact fresh_ident_wc_env' : forall pref vars ty ck b id st st' ,
        wc_env (vars++st_clocks' st) ->
        wc_clock (vars++st_clocks' st) ck ->
        fresh_ident pref (ty, ck, b) st = (id, st') ->
        wc_env (vars++st_clocks' st').
    Proof.
      intros * Hwenv Hwc Hfresh.
      apply fresh_ident_anns in Hfresh.
      unfold st_clocks' in *. rewrite Hfresh; simpl.
      rewrite <- Permutation_middle.
      constructor; simpl.
      - repeat solve_incl.
      - eapply Forall_impl; [|eauto].
        intros; simpl in *. repeat solve_incl.
    Qed.

    Fact init_var_for_clock_wc_env : forall vars ck er id eqs' st st' ,
        wc_env (vars++st_clocks' st) ->
        wc_clock (vars++st_clocks' st) ck ->
        init_var_for_clock ck er st = (id, eqs', st') ->
        wc_env (vars++st_clocks' st').
    Proof with eauto.
      intros * Hwenv Hwc Hinit.
      unfold init_var_for_clock in Hinit.
      destruct find_init_var.
      - inv Hinit...
      - destruct fresh_ident eqn:Hfresh. inv Hinit.
        eapply fresh_ident_wc_env' in Hfresh...
    Qed.

    Fact fby_iteexp_wc_env : forall vars e0 e er ty ck es' eqs' st st' ,
        wc_env (vars++st_clocks' st) ->
        wc_clock (vars++st_clocks' st) (fst ck) ->
        fby_iteexp e0 e er (ty, ck) st = (es', eqs', st') ->
        wc_env (vars++st_clocks' st').
    Proof with eauto.
      intros vars e0 e er ty [ck name] es' eqs' st st' Hwenv Hwc Hfby.
      unfold fby_iteexp in Hfby; repeat inv_bind...
      eapply fresh_ident_wc_env' in H0... 2:repeat solve_incl.
      eapply init_var_for_clock_wc_env in H... eapply init_var_for_clock_st_follows in H...
    Qed.

    Fact init_var_for_clock_wc_eq : forall vars ck xr id eqs' st st' ,
        wc_clock (vars++st_clocks' st) ck ->
        Forall (fun '(xr, (ckr, namer)) =>
                  In (xr, ckr) (vars++st_clocks' st) /\ LiftO True (fun n => n = xr) namer) xr ->
        init_var_for_clock ck xr st = (id, eqs', st') ->
        Forall (wc_equation G2 (vars++st_clocks' st')) eqs'.
    Proof with eauto.
      intros * Hwc Hr Hinit.
      unfold init_var_for_clock in Hinit.
      destruct find_init_var.
      - repeat inv_bind...
      - destruct fresh_ident eqn:Hfresh; repeat inv_bind.
        simpl in *; repeat econstructor; simpl...
        1,2:apply add_whens_wc_exp... 1-2:repeat solve_incl.
        2-3:rewrite app_nil_r, add_whens_clockof...
        3:(apply fresh_ident_In in Hfresh;
           apply in_or_app; right;
           unfold st_clocks', idck, idty; rewrite map_map;
           simpl_In; eexists; split; eauto; eauto).
        1,2:rewrite Forall_map.
        + eapply Forall_impl; [|eauto].
          intros (?&?&?) (Wc&Name).
          destruct o; simpl in *; subst; econstructor; eauto.
          1,2:repeat solve_incl.
        + eapply Forall_forall. intros (?&?) ?; simpl; eauto.
    Qed.

    Fact normalized_lexp_wc_exp_clockof : forall vars e,
        normalized_lexp e ->
        wc_env vars ->
        wc_exp G2 vars e ->
        Forall (wc_clock vars) (clockof e).
    Proof with eauto.
      intros vars e Hnormed Hwenv Hwc.
      induction Hnormed; inv Hwc;
        simpl; unfold clock_of_nclock, stripname; simpl; repeat constructor...
      1,2:(unfold wc_env in Hwenv; rewrite Forall_forall in Hwenv; eapply Hwenv in H0; eauto).
      - eapply IHHnormed in H1. rewrite H4 in H1. inv H1...
      - eapply IHHnormed1 in H3. rewrite H6 in H3. inv H3...
      - apply Forall_singl in H5.
        eapply IHHnormed in H5.
        simpl in H7. rewrite app_nil_r in H7. symmetry in H7.
        singleton_length.
        inv H6. inv H5...
    Qed.

    Fact fby_iteexp_wc_eq : forall vars e0 e xr ty ck name e' eqs' st st' ,
        normalized_lexp e0 ->
        wc_env (vars++st_clocks' st) ->
        wc_exp G1 (vars++st_clocks' st) e0 ->
        wc_exp G1 (vars++st_clocks' st) e ->
        clockof e0 = [ck] ->
        clockof e = [ck] ->
        unnamed_stream (ty, (ck, name)) ->
        Forall (fun '(xr, (ckr, namer)) =>
                  In (xr, ckr) (vars++st_clocks' st) /\ LiftO True (fun n => n = xr) namer) xr ->
        fby_iteexp e0 e xr (ty, (ck, name)) st = (e', eqs', st') ->
        Forall (wc_equation G2 (vars++st_clocks' st')) eqs'.
    Proof with eauto.
      intros * Hnormed Henv Hwc1 Hwc2 Hcl1 Hcl2 Hunnamed Hr Hfby.
      assert (wc_clock (vars++st_clocks' st) ck) as Hwck.
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
      - unfold unnamed_stream in Hunnamed; simpl in Hunnamed. rewrite Hunnamed. constructor.
      - eapply fresh_ident_In in H0.
        apply in_or_app; right.
        unfold clock_of_nclock, stripname; simpl in *.
        unfold st_clocks', idck, idty. rewrite map_map.
        simpl_In. exists (x2, (ty, ck, None)); auto.
      - eapply init_var_for_clock_wc_eq in H...
        solve_forall; repeat solve_incl.
    Qed.

    Fact fby_equation_wc_eq : forall vars to_cut eq eqs' st st' ,
        unnested_equation G1 eq ->
        wc_env (vars++st_clocks' st) ->
        wc_equation G1 (vars++st_clocks' st) eq ->
        fby_equation to_cut eq st = (eqs', st') ->
        (Forall (wc_equation G2 (vars++st_clocks' st')) eqs' /\ wc_env (vars++st_clocks' st')).
    Proof with eauto.
      intros * Hunt Hwenv Hwc Hfby.
      inv_fby_equation Hfby to_cut eq; try destruct x3 as [ty [ck name]].
      - (* fby (constant) *)
        destruct PS.mem; repeat inv_bind; auto.
        2:{ split; auto. destruct Hwc as (?&?&?).
            do 2 constructor; auto.
            solve_forall. }
        destruct Hwc as (Hwc&Hn&Hins).
        apply Forall_singl in Hwc. apply Forall2_singl in Hn. apply Forall2_singl in Hins.
        assert (Hwc':=Hwc). inv Hwc'.
        apply Forall_singl in H4; apply Forall_singl in H5.
        apply Forall_singl in H10; inv H10; simpl in H0; subst.
        assert (wc_clock (vars ++ st_clocks' st) ck).
        { eapply wc_env_var; eauto. }
        repeat (econstructor; eauto).
        + eapply fresh_ident_In in H.
          eapply in_or_app, or_intror. unfold st_clocks', idck, idty.
          simpl_In. exists (x3, (ty, ck)); split; auto.
          simpl_In. eexists; split; eauto. auto.
        + repeat solve_incl.
        + eapply iface_eq_wc_exp... repeat solve_incl.
        + eapply iface_eq_wc_exp... repeat solve_incl.
        + solve_forall; eapply iface_eq_wc_exp; eauto; repeat solve_incl.
        + eapply fresh_ident_In in H.
          eapply in_or_app, or_intror. unfold st_clocks', idck, idty.
          simpl_In. exists (x3, (ty, ck)); split; auto.
          simpl_In. eexists; split; eauto. auto.
        + eapply fresh_ident_wc_env' in H; eauto.
      - (* fby *)
        assert (st_follows st st') as Hfollows by (eapply fby_iteexp_st_follows with (ann:=(ty, (ck, name))) in H; eauto).
        destruct Hwc as [Hwc [Hn Hins]].
        apply Forall_singl in Hwc. apply Forall2_singl in Hn. apply Forall2_singl in Hins.
        inv Hwc.
        simpl in *; rewrite app_nil_r in *.
        apply Forall_singl in H4; apply Forall_singl in H5.
        apply Forall_singl in H10; inv H10. simpl in H0; subst.
        rewrite Forall2_eq in H7, H8.
        assert (Forall (fun '(xr, (ckr, namer)) => In (xr, ckr) (vars ++ st_clocks' st) /\
                                                LiftO True (fun n : ident => n = xr) namer) x4) as Hr'.
        { clear - Hr H6.
          eapply Forall2_ignore1 in Hr. eapply Forall_impl; [|eauto].
          intros (?&?&?) (?&In&?&?); subst.
          eapply Forall_forall in H6; [|eauto]. inv H6; simpl; eauto. }
        assert (Hwce:=H). eapply fby_iteexp_wc_exp in Hwce; eauto.
        assert (Hck:=H). eapply (fby_iteexp_nclockof _ _ _ (ty, (ck, None))) in Hck; eauto.
        assert (Hwceq:=H). eapply fby_iteexp_wc_eq in Hwceq; eauto.
        2:(clear - Hunt; inv Hunt; eauto; inv H0; inv H).
        2,3:constructor.
        2:eapply Forall_impl; [|eapply Hr']; intros (?&?&?) (?&?); eauto.
        assert (wc_clock (vars ++ st_clocks' st) ck).
        { eapply wc_env_var; eauto. }
        eapply (fby_iteexp_wc_env _ _ _ _ ty (ck, None)) in H...
        repeat constructor; auto; simpl; rewrite app_nil_r.
        + rewrite Hck. repeat constructor.
        + rewrite clockof_nclockof, Hck. repeat constructor.
          repeat solve_incl.
      - (* arrow *)
        repeat inv_bind.
        destruct Hwc as [Hwc [Hn Hins]].
        apply Forall_singl in Hwc. apply Forall2_singl in Hn. apply Forall2_singl in Hins.
        inv Hwc.
        simpl in *; rewrite app_nil_r in *.
        apply Forall_singl in H4; apply Forall_singl in H5.
        apply Forall_singl in H10; inv H10.
        rewrite Forall2_eq in H7, H8.
        assert (wc_clock (vars ++ st_clocks' st) ck).
        { eapply wc_env_var; eauto. }
        assert (Hwce:=H). eapply init_var_for_clock_wc_env in Hwce; eauto.
        split; eauto.
        assert (st_follows st st') as Hfollows.
        { eapply init_var_for_clock_st_follows; eauto. }
        simpl in *; inv H0.
        assert (Forall (fun '(xr, (ckr, namer)) => In (xr, ckr) (vars ++ st_clocks' st) /\
                                                LiftO True (fun n : ident => n = xr) namer) x4) as Hr'.
        { clear - Hr H6.
          eapply Forall2_ignore1 in Hr. eapply Forall_impl; [|eauto].
          intros (?&?&?) (?&In&?&?); subst.
          eapply Forall_forall in H6; [|eauto]. inv H6; simpl; eauto. }
        repeat econstructor; auto; try congruence.
        2-4:intros ? [Heq|[Heq|Heq]]; inv Heq. 2:constructor; auto.
        2,5:eapply iface_eq_wc_exp; eauto; repeat solve_incl.
        2-5:simpl; rewrite app_nil_r; try rewrite <- H7; try rewrite <- H8; auto.
        + eapply init_var_for_clock_In in H as (ps&?&?).
          apply in_or_app, or_intror. unfold st_clocks', idck, idty. rewrite map_map.
          simpl_In. exists (x3, (OpAux.bool_velus_type, ck, Some ps)); auto.
        + repeat solve_incl.
        + eapply init_var_for_clock_wc_eq in H...
      - (* others *)
        split; auto.
        destruct Hwc as (?&?&?). do 2 constructor; auto.
        solve_forall.
    Qed.

    Fact fby_equations_wc_eq : forall vars to_cut eqs eqs' st st' ,
        Forall (unnested_equation G1) eqs ->
        wc_env (vars++st_clocks' st) ->
        Forall (wc_equation G1 (vars++st_clocks' st)) eqs ->
        fby_equations to_cut eqs st = (eqs', st') ->
        (Forall (wc_equation G2 (vars++st_clocks' st')) eqs' /\ wc_env (vars++st_clocks' st')).
    Proof.
      induction eqs; intros * Hunt Henv Hwc Hfby;
        unfold fby_equations in *; repeat inv_bind; simpl; auto.
      inv Hunt. inv Hwc.
      assert (fby_equations to_cut eqs x1 = (concat x2, st')) as Hnorm.
      { unfold fby_equations. repeat inv_bind; eauto. }
      assert (H':=H). eapply fby_equation_wc_eq in H as [Hwc' Henv']; auto. 2,3,4:eauto.
      apply IHeqs in Hnorm as [Hwc'' Henv'']; auto.
      2:solve_forall; repeat solve_incl; eapply fby_equation_st_follows in H'; eauto.
      rewrite Forall_app; repeat split; eauto.
      solve_forall; repeat solve_incl.
    Qed.

    Lemma normfby_node_wc : forall n,
        unnested_node G1 n ->
        wc_node G1 n ->
        wc_node G2 (normfby_node n).
    Proof.
      intros * Hunn [Hclin [Hclout [Hclvars Heq]]].
      unfold normfby_node.
      repeat constructor; simpl; auto.
      - destruct (fby_equations _ _ _) as (eqs'&st') eqn:Heqres.
        eapply fby_equations_wc_eq in Heqres as [_ ?]; eauto.
        1-3:unfold st_clocks' in *; try rewrite init_st_anns, app_nil_r; eauto.
        + repeat rewrite idck_app in *.
          repeat rewrite <- app_assoc in H; auto.
        + solve_forall.
          eapply wc_equation_incl; eauto.
          rewrite (Permutation_app_comm (n_out n)). reflexivity.
      - destruct (fby_equations _ _ _) as (eqs'&st') eqn:Heqres.
        eapply fby_equations_wc_eq in Heqres as [? _]; eauto.
        2,3:unfold st_clocks'; rewrite init_st_anns, app_nil_r.
        2:eapply Hclvars.
        + repeat rewrite idck_app in *.
          repeat rewrite <- app_assoc in *.
          solve_forall. eapply wc_equation_incl; eauto.
          apply incl_appr'.
          rewrite (Permutation_app_comm (idck (n_out _))), <- app_assoc. apply incl_appr', incl_refl.
        + solve_forall.
          eapply wc_equation_incl; eauto.
          rewrite (Permutation_app_comm (n_out n)). reflexivity.
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
      inversion_clear Hwc as [|?? (?&?)]; auto.
    constructor; [constructor|].
    - eapply normfby_node_wc; eauto.
      eapply normfby_global_eq.
    - simpl. eapply normfby_nodes_names; eauto.
    - eapply IHnds; eauto.
  Qed.

  (** ** Conclusion *)

  Lemma normalize_global_wc : forall G G',
      wc_global G ->
      normalize_global G = Errors.OK G' ->
      wc_global G'.
  Proof.
    intros * Hwc Hnorm.
    unfold normalize_global in Hnorm. destruct (Caus.check_causality _); inv Hnorm.
    eapply normfby_global_wc, unnest_global_wc, Hwc.
    eapply unnest_global_unnested_global; eauto.
  Qed.

End NCLOCKING.

Module NClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (Caus : LCAUSALITY Ids Op OpAux Cks Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (Norm : NORMALIZATION Ids Op OpAux Cks Syn Caus)
       <: NCLOCKING Ids Op OpAux Cks Syn Caus Clo Norm.
  Include NCLOCKING Ids Op OpAux Cks Syn Caus Clo Norm.
End NClockingFun.
