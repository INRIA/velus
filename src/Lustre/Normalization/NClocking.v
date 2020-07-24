From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Omega.

From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax Lustre.LCausality Lustre.LClocking.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

(** * Preservation of Typing through Normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type NCLOCKING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Caus : LCAUSALITY Ids Op Syn)
       (Import Clo : LCLOCKING Ids Op Syn)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn Caus).
  Import Fresh Fresh.Facts Fresh.Tactics.

  (** ** Rest of clockof preservation (started in Normalization.v) *)

  Fact normalize_reset_clockof : forall e e' eqs' st st',
      numstreams e = 1 ->
      normalize_reset e st = (e', eqs', st') ->
      clockof e' = clockof e.
  Proof.
    intros e e' eqs' st st' Hnum Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec];
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind; auto.
    destruct hd eqn:Hhd, p. repeat inv_bind; simpl.
    rewrite clockof_annot.
    rewrite <- length_annot_numstreams in Hnum. singleton_length.
    unfold clock_of_nclock, stripname; reflexivity.
  Qed.

  Hint Resolve nth_In.
  Corollary map_bind2_normalize_exp_clocksof' :
    forall G vars is_control es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => clocksof es' = clockof e) es' es.
  Proof with eauto.
    intros G vars is_control es es' eqs' st st' Hwt Hmap.
    eapply map_bind2_normalize_exp_annots' in Hmap...
    clear Hwt.
    induction Hmap; constructor; eauto.
    rewrite clocksof_annots, H, <- clockof_annot...
  Qed.

  Corollary map_bind2_normalize_exp_clocksof'' : forall G vars is_control es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall2 (fun e ck => clockof e = [ck]) (concat es') (clocksof es).
  Proof.
    intros * Hwl Hmap.
    eapply map_bind2_normalize_exp_annots'' in Hmap; eauto.
    rewrite clocksof_annots, Forall2_map_2, Forall2_map_2.
    eapply Forall2_impl_In; eauto. intros; simpl in *.
    rewrite clockof_annot, H1; auto.
  Qed.

  Corollary map_bind2_normalize_exp_clocksof''' : forall G vars is_control ck es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      Forall (eq ck) (clocksof es) ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall (fun e => clockof e = [ck]) (concat es').
  Proof.
    intros * Hwl Hck Hmap.
    assert (Hmap':=Hmap). eapply map_bind2_normalize_exp_numstreams in Hmap.
    eapply map_bind2_normalize_exp_annots'' in Hmap'; eauto.
    rewrite clocksof_annots in Hck.
    assert (length (concat es') = length (annots es)) by (apply Forall2_length in Hmap'; auto).
    assert (Forall (fun e => exists y, In y (annots es) /\ (clockof e = [ck])) (concat es')) as Hf'.
    { eapply Forall2_ignore2. solve_forall.
      rewrite clockof_annot, H2; simpl in *. congruence. }
    solve_forall. destruct H1 as [_ [_ ?]]; auto.
  Qed.

  Corollary map_bind2_normalize_exp_clocksof :
    forall G vars is_control es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      clocksof (concat es') = clocksof es.
  Proof.
    intros.
    eapply map_bind2_normalize_exp_annots in H0; eauto.
    rewrite clocksof_annots, H0, <- clocksof_annots; eauto.
  Qed.
  Hint Resolve map_bind2_normalize_exp_clocksof.

  Corollary normalize_exps_clocksof : forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      normalize_exps es st = (es', eqs', st') ->
      clocksof es' = clocksof es.
  Proof.
    intros.
    eapply normalize_exps_annots in H0; eauto.
    repeat rewrite clocksof_annots.
    congruence.
  Qed.

  Fact fby_iteexp_clockof : forall e0 e ann es' eqs' st st',
      fby_iteexp e0 e ann st = (es', eqs', st') ->
      clockof es' = [fst (snd ann)].
  Proof.
    intros e0 e [ty [cl name]] es' eqs' st st' Hfby; simpl in *.
    destruct (is_constant e0); repeat inv_bind; reflexivity.
  Qed.

  Fact normalize_fby_clockof : forall anns e0s es,
      length e0s = length anns ->
      length es = length anns ->
      clocksof (normalize_fby e0s es anns) = List.map clock_of_nclock anns.
  Proof.
    intros * Hlen1 Hlen2.
    rewrite clocksof_annots, normalize_fby_annot, map_map; auto.
  Qed.

  Fact normalize_rhs_clockof: forall G vars e es' eqs' st st',
      wc_exp G vars e ->
      normalize_rhs e st = (es', eqs', st') ->
      clocksof es' = clockof e.
  Proof.
    intros * Hwc Hnorm.
    eapply normalize_rhs_annot in Hnorm; eauto.
    rewrite clocksof_annots, Hnorm, <- clockof_annot. reflexivity.
  Qed.

  Corollary normalize_rhss_clocksof: forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      normalize_rhss es st = (es', eqs', st') ->
      clocksof es' = clocksof es.
  Proof.
    intros.
    eapply normalize_rhss_annots in H0; eauto.
    repeat rewrite clocksof_annots. congruence.
  Qed.

  (** ** nclockof is also preserved by normalize_exp *)

  Fact fby_iteexp_nclockof : forall e0 e ann es' eqs' st st',
      fby_iteexp e0 e ann st = (es', eqs', st') ->
      nclockof es' = [snd ann].
  Proof.
    intros e0 e [ty [cl name]] es' eqs' st st' Hfby; simpl in *.
    destruct (is_constant e0); repeat inv_bind; reflexivity.
  Qed.

  Fact normalize_merge_nclockof : forall ckid ets efs tys ck,
      length ets = length tys ->
      length efs = length tys ->
      Forall (fun e => nclockof e = [ck]) (normalize_merge ckid ets efs tys ck).
  Proof.
    intros * Hlen1 Hlen2.
    unfold normalize_merge. simpl_forall.
    eapply Forall3_forall3; split; eauto. congruence.
  Qed.

  Fact normalize_ite_nclockof : forall e ets efs tys ck,
      length ets = length tys ->
      length efs = length tys ->
      Forall (fun e => nclockof e = [ck]) (normalize_ite e ets efs tys ck).
  Proof.
    intros * Hlen1 Hlen2.
    unfold normalize_ite. simpl_forall.
    eapply Forall3_forall3; split; eauto. congruence.
  Qed.

  Fact normalize_exp_nclockof : forall G vars e is_control es' eqs' st st',
      wc_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      nclocksof es' = nclockof e.
  Proof with eauto.
    intros.
    eapply normalize_exp_annot in H0; eauto.
    rewrite nclocksof_annots, H0, <- nclockof_annot. reflexivity.
  Qed.

  Fact map_bind2_normalize_exp_nclocksof : forall G vars es is_control es' eqs' st st',
      Forall (wc_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      nclocksof (concat es') = nclocksof es.
  Proof with eauto.
    intros.
    eapply map_bind2_normalize_exp_annots in H0; eauto.
    repeat rewrite nclocksof_annots. congruence.
  Qed.

  Fact normalize_exps_nclocksof : forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      normalize_exps es st = (es', eqs', st') ->
      nclocksof es' = nclocksof es.
  Proof with eauto.
    intros.
    eapply normalize_exps_annots in H0; eauto.
    repeat rewrite nclocksof_annots. congruence.
  Qed.

  Fact normalize_rhs_nclockof : forall G vars e es' eqs' st st',
      wc_exp G vars e ->
      normalize_rhs e st = (es', eqs', st') ->
      nclocksof es' = nclockof e.
  Proof with eauto.
    intros.
    eapply normalize_rhs_annot in H0; eauto.
    rewrite nclocksof_annots, H0, <- nclockof_annot. reflexivity.
  Qed.

  Fact normalize_rhss_nclocksof : forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      normalize_rhss es st = (es', eqs', st') ->
      nclocksof es' = nclocksof es.
  Proof with eauto.
    intros.
    eapply normalize_rhss_annots in H0; eauto.
    rewrite nclocksof_annots, H0, <- nclocksof_annots. reflexivity.
  Qed.

  (** ** A few additional things *)

  Definition st_clocks (st : fresh_st (Op.type * clock)) :=
    idck (st_anns st).
  Definition st_clocks' (st : fresh_st ((Op.type * clock) * bool)) :=
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

  Fact fresh_ident_wc_env : forall vars ty ck id st st',
      wc_env (vars++st_clocks st) ->
      wc_clock (vars++st_clocks st) ck ->
      fresh_ident (ty, ck) st = (id, st') ->
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

  Fact map_bind2_wc_env {A A1 A2 : Type} :
    forall vars (k : A -> Untuple.FreshAnn (A1 * A2)) a a1s a2s st st',
      wc_env (vars++st_clocks st) ->
      map_bind2 k a st = (a1s, a2s, st') ->
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
    - eapply map_bind2_st_follows...
      solve_forall...
    - solve_forall.
      eapply H2 in H5...
      etransitivity...
  Qed.

  Fact normalize_reset_wc_env : forall vars e e' eqs' st st',
      wc_env (vars++st_clocks st) ->
      Forall (wc_clock (vars++st_clocks st)) (clockof e) ->
      normalize_reset e st = (e', eqs', st') ->
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros vars e e' eqs' st st' Hwenv Hwc Hnorm.
    specialize (normalize_reset_spec e) as [[v [a [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec;
        repeat inv_bind...
    destruct hd as [ty [cl name]] eqn:Hann; repeat inv_bind.
    eapply fresh_ident_wc_env in H...
    rewrite clockof_annot, map_map in Hwc.
    destruct (annot e) as [|[ty' [cl' name']]]; simpl in *; inv Hann...
    inv Hwc...
  Qed.

  Hint Constructors wc_exp.

  Fact hd_default_wc_exp : forall G vars es,
      Forall (wc_exp G vars) es ->
      wc_exp G vars (hd_default es).
  Proof.
    intros G vars es Hf.
    destruct es; simpl.
    - constructor.
    - inv Hf; auto.
  Qed.
  Hint Resolve hd_default_wc_exp.

  Fact idents_for_anns_wc : forall G vars anns ids st st',
      Forall unnamed_stream anns ->
      idents_for_anns anns st = (ids, st') ->
      Forall (wc_exp G (vars++st_clocks st')) (List.map (fun '(x, ann) => Evar x ann) ids).
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

  Fact idents_for_anns'_wc : forall G vars anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      Forall (wc_exp G (vars++st_clocks st')) (List.map (fun '(x, ann) => Evar x ann) ids).
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

  Fact map_bind2_wc_exp {A A2 B} :
    forall G vars (k : A -> Fresh (list exp * A2) B) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
      Forall (fun a => forall es' a2s st0 st0',
                  k a st0 = (es', a2s, st0') ->
                  st_follows st st0 ->
                  st_follows st0' st' ->
                  Forall (wc_exp G vars) es') a ->
      Forall (wc_exp G vars) (concat es').
  Proof.
    intros G vars k a.
    induction a; intros es' a2s st st' Hmap Hfollows Hforall;
      simpl in Hmap; repeat inv_bind.
    - constructor.
    - apply Forall_app. split; eauto.
      + rewrite Forall_forall in Hforall.
        eapply Hforall; eauto.
        * constructor. reflexivity.
        * reflexivity.
        * eapply map_bind2_st_follows in H0; eauto.
          rewrite Forall_forall; intros; eauto.
      + eapply IHa; eauto.
        rewrite Forall_forall in *; intros.
        eapply Hforall; eauto. apply in_cons; auto.
        etransitivity; eauto.
  Qed.

  Fact normalize_when_wc_exp : forall G vars ckid ck b es tys,
      length es = length tys ->
      In (ckid, ck) vars ->
      Forall (wc_exp G vars) es ->
      Forall (fun e => clockof e = [ck]) es ->
      Forall (wc_exp G vars) (normalize_when ckid b es tys (Con ck ckid b, None)).
  Proof.
    intros * Hlen Hin Hwc Hck. unfold normalize_when.
    solve_forall.
    repeat constructor; auto;
      simpl; rewrite app_nil_r, H1; auto.
  Qed.

  Fact normalize_fby_wc_exp : forall G vars e0s es anns,
      Forall (wc_exp G vars) e0s ->
      Forall (wc_exp G vars) es ->
      Forall unnamed_stream anns ->
      Forall2 (fun e0 a => clockof e0 = [a]) e0s (map clock_of_nclock anns) ->
      Forall2 (fun e a => clockof e = [a]) es (map clock_of_nclock anns) ->
      Forall (wc_exp G vars) (normalize_fby e0s es anns).
  Proof.
    intros * Hwc1 Hwc2 Hunnamed Hck1 Hck2.
    unfold normalize_fby.
    assert (length e0s = length anns) as Hlen1 by (eapply Forall2_length in Hck1; solve_length).
    assert (length es = length anns) as Hlen2 by (eapply Forall2_length in Hck2; solve_length).
    solve_forall.
    constructor; simpl; try rewrite app_nil_r; eauto.
  Qed.

  Fact normalize_merge_wc_exp : forall G vars ckid ck ets efs tys,
      length ets = length tys ->
      length efs = length tys ->
      In (ckid, ck) vars ->
      Forall (wc_exp G vars) ets ->
      Forall (wc_exp G vars) efs ->
      Forall (fun e => clockof e = [Con ck ckid true]) ets ->
      Forall (fun e => clockof e = [Con ck ckid false]) efs ->
      Forall (wc_exp G vars) (normalize_merge ckid ets efs tys (ck, None)).
  Proof.
    intros * Hlen1 Hlen2 Hin Hwc1 Hwc2 Hck1 Hck2. unfold normalize_merge.
    solve_forall.
    repeat constructor; auto;
      simpl; rewrite app_nil_r; try rewrite H2; try rewrite H3; auto.
  Qed.

  Fact normalize_ite_wc_exp : forall G vars ck e ets efs tys,
      length ets = length tys ->
      length efs = length tys ->
      wc_exp G vars e ->
      Forall (wc_exp G vars) ets ->
      Forall (wc_exp G vars) efs ->
      clockof e = [ck] ->
      Forall (fun e => clockof e = [ck]) ets ->
      Forall (fun e => clockof e = [ck]) efs ->
      Forall (wc_exp G vars) (normalize_ite e ets efs tys (ck, None)).
  Proof.
    intros * Hlen1 Hlen2 Hwc1 Hwc2 Hwc3 Hck1 Hck2 Hck3. unfold normalize_ite.
    solve_forall.
    repeat constructor; auto;
      simpl; rewrite app_nil_r; try rewrite H2; try rewrite H3; auto.
  Qed.

  Hint Resolve nth_In.
  Fact normalize_exp_wc_exp : forall G vars e is_control es' eqs' st st',
      wc_exp G (vars++st_clocks st) e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) es'.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwc Hnorm;
      inv Hwc; simpl in Hnorm; repeat inv_bind.
    - (* const *) repeat constructor.
    - (* var *)
      repeat constructor...
    - (* var (anon) *)
      repeat constructor...
    - (* unop *)
      assert (length x = numstreams e) as Hlen by eauto.
      assert (clocksof x = clockof e) as Hclockof by eauto.
      repeat constructor...
      rewrite <- length_clockof_numstreams in Hlen. rewrite H3 in Hlen; simpl in Hlen.
      singleton_length. congruence.
    - (* binop *)
      assert (length x = numstreams e1) as Hlen1 by eauto.
      assert (length x2 = numstreams e2) as Hlen2 by eauto.
      assert (clocksof x = clockof e1) as Hclockof1 by eauto.
      assert (clocksof x2 = clockof e2) as Hclockof2 by eauto.
      repeat constructor...
      + eapply hd_default_wc_exp.
        eapply IHe1 in H... solve_forall. repeat solve_incl.
      + eapply hd_default_wc_exp.
        eapply IHe2 in H0... solve_forall. repeat solve_incl.
      + rewrite <- length_clockof_numstreams in Hlen1. rewrite H5 in Hlen1; simpl in Hlen1.
        singleton_length. congruence.
      + rewrite <- length_clockof_numstreams in Hlen2. rewrite H6 in Hlen2; simpl in Hlen2.
        singleton_length. congruence.
    - (* fby *)
      eapply idents_for_anns_wc in H3...
    - (* when *)
      apply normalize_when_wc_exp...
      + eapply map_bind2_normalize_exp_length in H0...
        solve_length.
      + assert (incl (vars ++ st_clocks st) (vars ++ st_clocks st')) as Hincl by repeat solve_incl...
      + eapply map_bind2_wc_exp... solve_forall. eapply H8 in H2... solve_forall. 1,2:repeat solve_incl.
      + eapply map_bind2_normalize_exp_clocksof''' in H0...
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + (* control *)
        eapply normalize_merge_wc_exp; auto.
        * eapply map_bind2_normalize_exp_length in H1...
          rewrite H1, H10, clocksof_annots; solve_length.
        * eapply map_bind2_normalize_exp_length in H2...
          rewrite H2, H11, clocksof_annots; solve_length.
        * assert (incl (vars ++ st_clocks st) (vars ++ st_clocks st')) as Hincl by repeat solve_incl...
        * eapply map_bind2_wc_exp... solve_forall. eapply H12 in H4... solve_forall. 1,2:repeat solve_incl.
        * eapply map_bind2_wc_exp... solve_forall. eapply H12 in H4... solve_forall. 1,2:repeat solve_incl.
        * eapply map_bind2_normalize_exp_clocksof''' in H1...
        * eapply map_bind2_normalize_exp_clocksof''' in H2...
      + (* exp *)
        eapply idents_for_anns_wc in H3...
        solve_forall. unfold unnamed_stream; auto.
    - (* ite *)
      destruct is_control; repeat inv_bind.
      + (* control *)
        eapply normalize_ite_wc_exp; auto.
        * eapply map_bind2_normalize_exp_length in H2...
          rewrite H2, H11, clocksof_annots; solve_length.
        * eapply map_bind2_normalize_exp_length in H3...
          rewrite H3, H12, clocksof_annots; solve_length.
        * eapply hd_default_wc_exp. eapply IHe in H1...
          solve_forall. repeat solve_incl.
        * eapply map_bind2_wc_exp... solve_forall. eapply H15 in H6... solve_forall. 1,2:repeat solve_incl.
        * eapply map_bind2_wc_exp... solve_forall. eapply H15 in H6... solve_forall. 1,2:repeat solve_incl.
        * assert (length x = 1). 2:singleton_length.
          { eapply normalize_exp_length in H1... rewrite H1, <- length_clockof_numstreams, H8; auto. }
          eapply normalize_exp_clockof in H1... simpl in H1; rewrite app_nil_r in H1.
          congruence.
        * eapply map_bind2_normalize_exp_clocksof''' in H2...
        * eapply map_bind2_normalize_exp_clocksof''' in H3...
      + (* exp *)
        eapply idents_for_anns_wc in H4...
        rewrite Forall_map. eapply Forall_forall. intros ? _; unfold unnamed_stream; auto.
    - (* app *)
      eapply idents_for_anns'_wc in H2...
    - (* app (reset) *)
      eapply idents_for_anns'_wc in H3...
  Qed.

  Corollary map_bind2_normalize_exp_wc_exp : forall G vars is_control es es' eqs' st st',
      Forall (wc_exp G (vars++st_clocks st)) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) (concat es').
  Proof.
    intros G vars is_control es es' eqs' st st' Hwt Hmap.
    eapply map_bind2_wc_exp in Hmap; eauto.
    solve_forall. eapply normalize_exp_wc_exp with (G:=G) (vars:=vars) in H1; eauto.
    solve_forall. 1,2:repeat solve_incl.
  Qed.

  Corollary normalize_exps_wc_exp : forall G vars es es' eqs' st st',
      Forall (wc_exp G (vars++st_clocks st)) es ->
      normalize_exps es st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) es'.
  Proof.
    intros G vars es es' eqs' st st' Hwt Hmap.
    unfold normalize_exps in Hmap; repeat inv_bind.
    eapply map_bind2_normalize_exp_wc_exp in H; eauto.
  Qed.

  Fact map_bind2_wc_exp' {A A2 B} :
    forall G vars (k : A -> Fresh (exp * A2) B) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
      Forall (fun a => forall e' a2s st0 st0',
                  k a st0 = (e', a2s, st0') ->
                  st_follows st st0 ->
                  st_follows st0' st' ->
                  wc_exp G vars e') a ->
      Forall (wc_exp G vars) es'.
  Proof.
    intros G vars k a.
    induction a; intros es' a2s st st' Hmap Hfollows Hforall;
      simpl in Hmap; repeat inv_bind.
    - constructor.
    - constructor.
      + rewrite Forall_forall in Hforall.
        eapply Hforall; eauto.
        * constructor. reflexivity.
        * reflexivity.
        * eapply map_bind2_st_follows in H0; eauto.
          rewrite Forall_forall; intros; eauto.
      + eapply IHa; eauto.
        rewrite Forall_forall in *; intros.
        eapply Hforall; eauto. apply in_cons; auto.
        etransitivity; eauto.
  Qed.

  Fact normalize_reset_wc_exp : forall G vars e e' eqs' st st',
      wc_exp G (vars++st_clocks st) e ->
      normalize_reset e st = (e', eqs', st') ->
      wc_exp G (vars++st_clocks st') e'.
  Proof.
    intros G vars e e' eqs' st st' Hwc Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec];
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind; auto.
    destruct hd eqn:Hhd, p; repeat inv_bind.
    econstructor. apply fresh_ident_In in H.
    apply in_or_app; right.
    In_st_clocks x t c false.
  Qed.

  Fact normalize_rhs_wc_exp : forall G vars e es' eqs' st st',
      wc_exp G (vars++st_clocks st) e ->
      normalize_rhs e st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) es'.
  Proof with eauto.
    intros * Hwc Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (solve [eapply normalize_exp_wc_exp in Hnorm; eauto]); [| inv Hwc].
    - (* fby *)
      inv Hwc. rewrite Forall2_eq in H4, H5.
      repeat inv_bind. eapply normalize_fby_wc_exp...
      + eapply normalize_exps_wc_exp in H...
        solve_forall; repeat solve_incl.
      + eapply normalize_exps_wc_exp in H0...
        solve_forall; repeat solve_incl.
      + unfold normalize_exps in H; repeat inv_bind.
        eapply map_bind2_normalize_exp_clocksof'' in H... congruence.
      + unfold normalize_exps in H0; repeat inv_bind.
        eapply map_bind2_normalize_exp_clocksof'' in H0... congruence.
    - (* app *)
      repeat inv_bind.
      repeat constructor.
      econstructor...
      + eapply normalize_exps_wc_exp in H...
      + eapply normalize_exps_nclocksof in H... congruence.
    - (* app (reset) *)
      repeat inv_bind.
      repeat constructor.
      econstructor...
      + eapply normalize_exps_wc_exp in H...
        solve_forall. repeat solve_incl.
      + eapply normalize_exps_nclocksof in H... congruence.
      + eapply normalize_exp_wc_exp in H0...
        eapply hd_default_wc_exp in H0.
        eapply normalize_reset_wc_exp in H1...
        repeat solve_incl.
      + assert (length x4 = numstreams r) by eauto.
        rewrite <- length_clockof_numstreams, H8 in H2; simpl in H2. singleton_length.
        eapply normalize_exp_clockof in H0... simpl in H0; rewrite app_nil_r in H0.
        rewrite H8 in H0.
        eapply normalize_reset_clockof in H1. rewrite H1, H0. reflexivity.
        rewrite <- length_clockof_numstreams, H0. reflexivity.
  Qed.

  Corollary normalize_rhss_wc_exp : forall G vars es es' eqs' st st',
      Forall (wc_exp G (vars++st_clocks st)) es ->
      normalize_rhss es st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) es'.
  Proof.
    intros * Hwc Hnorm.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_wc_exp in H; eauto.
    solve_forall.
    eapply normalize_rhs_wc_exp with (G:=G) (vars:=vars) in H2; eauto.
    solve_forall. 1,2:repeat solve_incl.
  Qed.

  Fact map_bind2_wc_eq {A A1} :
    forall G vars (k : A -> Fresh (A1 * _) _) a a1s eqs' st st',
      wc_env (vars++st_clocks st) ->
      map_bind2 k a st = (a1s, eqs', st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
      Forall (fun a => forall a1 eqs' st0 st0',
                  st_follows st st0 ->
                  st_follows st0' st' ->
                  wc_env (vars++st_clocks st0) ->
                  k a st0 = (a1, eqs', st0') ->
                  (Forall (wc_equation G (vars++st_clocks st0')) eqs' /\
                   wc_env (vars++st_clocks st0'))) a ->
      (Forall (wc_equation G (vars++st_clocks st')) (concat eqs') /\
       wc_env (vars++st_clocks st')).
  Proof with eauto.
    intros G vars k a.
    induction a; intros a1s eqs' st st' Hwenv Hmap Hfollows Hforall;
      repeat inv_bind; simpl in *...
    assert (st_follows st x1) as Hfollows1 by eauto.
    assert (st_follows x1 st') as Hfollows2 by repeat solve_st_follows.
    rewrite Forall_forall in Hforall.
    eapply Hforall in H as [Hwc' Hwenv']...
    3,4:repeat solve_st_follows. 2:left...
    eapply IHa in H0 as [Hwc'' Hwenv'']...
    - split...
      apply Forall_app. split...
      solve_forall. repeat solve_incl.
    - rewrite Forall_forall in *; intros.
      eapply Hforall in H4... apply in_cons...
      etransitivity...
  Qed.

  Fact add_whens_clockof : forall e ty ck,
      clockof e = [Cbase] ->
      clockof (add_whens e ty ck) = [ck].
  Proof. induction ck; intros Hlen; auto. Qed.

  Fact add_whens_wc_exp : forall G vars e ty ck,
      clockof e = [Cbase] ->
      wc_exp G vars e ->
      wc_clock vars ck ->
      wc_exp G vars (add_whens e ty ck).
  Proof with eauto.
    induction ck; intros Hclof Hwc Hwc2; inv Hwc2; simpl...
    repeat constructor; simpl... 1,2:rewrite app_nil_r.
    + rewrite add_whens_clockof...
    + rewrite add_whens_clockof...
  Qed.

  Fact normalize_reset_wc_eq : forall G vars e e' eqs' st st',
      normalized_lexp e ->
      wc_exp G (vars++st_clocks st) e ->
      normalize_reset e st = (e', eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof with eauto.
    intros G vars e e' eqs' st st' Hnormed Hwc Hnorm.
    inv Hnormed; simpl in *; try destruct cl; repeat inv_bind; repeat constructor; simpl in *.
    2,5,8: repeat solve_incl.
    2,4,6:inv Hwc; simpl; auto.
    1,2,3,4:eapply in_or_app; right.
    1:apply fresh_ident_In in H; In_st_clocks x (Op.type_const c) Cbase false.
    1,3:apply fresh_ident_In in H0. 3:apply fresh_ident_In in H1.
    1,3:In_st_clocks x ty c false.
    In_st_clocks x0 ty c false.
  Qed.

  Fact normalize_exp_wc_eq : forall G vars e is_control es' eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      wc_exp G (vars++st_clocks st) e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs' /\
      wc_env (vars++st_clocks st').
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' HwG Hwenv Hwc Hnorm;
      assert (Hnorm':=Hnorm); apply normalize_exp_fresh_incl in Hnorm';
      simpl in *;
      assert (Hwc':=Hwc); inv Hwc'; repeat inv_bind...
    - (* binop *)
      assert (st_follows st x1) as Hfollows by eauto.
      eapply IHe1 in H as [Hwc1 Hwenv1]...
      assert (st_follows x1 st') as Hfollows2 by eauto.
      eapply IHe2 in H0 as [Hwc2 Hwenv2]... 2: repeat solve_incl.
      split... eapply Forall_app; split...
      solve_forall. repeat solve_incl.
    - (* fby *)
      assert (st_follows st x1) as Hfollows1 by repeat solve_st_follows.
      assert (st_follows x1 x4) as Hfollows2 by repeat solve_st_follows.
      assert (st_follows x4 st') as Hfollows3 by repeat solve_st_follows.
      rewrite Forall2_eq in H6, H7.
      assert (length (concat x2) = length (annots e0s)) as Hlen1 by eauto.
      assert (length (concat x6) = length (annots es)) as Hlen2 by eauto.
      remember (normalize_fby _ _ _) as fby.
      assert (length (concat x2) = length a) as Hlen1'.
      { eapply map_bind2_normalize_exp_length in H1...
        repeat simpl_length. erewrite <- map_length, <- map_length. setoid_rewrite <- H6. apply map_length. }
      assert (length (concat x6) = length a) as Hlen2'.
      { eapply map_bind2_normalize_exp_length in H2...
        repeat simpl_length. erewrite <- map_length, <- map_length. setoid_rewrite <- H7. apply map_length. }
      assert (length a = length fby) as Hlen4.
      { repeat simpl_length.
        rewrite normalize_fby_length... }
      assert (length x5 = length fby) as Hlen3.
      { eapply idents_for_anns_length in H3. solve_length. }
      assert (H1':=H1). eapply map_bind2_wc_eq in H1' as [Hwc1 Hwenv1]...
      2: { solve_forall. eapply H12 in H11... repeat solve_incl. }
      assert (H2':=H2). eapply map_bind2_wc_eq in H2' as [Hwc2 Hwenv2]...
      2: { solve_forall. eapply H12 in H11... repeat solve_incl. }
      clear H H0.
      repeat rewrite Forall_app; repeat split.
      2,3:solve_forall; repeat solve_incl.
      + assert (annots fby = a) as Hanns.
        { rewrite Heqfby, normalize_fby_annot... }
        assert (Forall (wc_exp G (vars++st_clocks st')) fby) as Hwcf.
        { rewrite Heqfby. eapply normalize_fby_wc_exp...
          + eapply map_bind2_normalize_exp_wc_exp in H1...
            solve_forall; repeat solve_incl.
          + eapply map_bind2_normalize_exp_wc_exp with (G:=G) (vars:=vars) in H2...
            1,2:solve_forall; repeat solve_incl.
          + eapply map_bind2_normalize_exp_clocksof'' in H1... congruence.
          + eapply map_bind2_normalize_exp_clocksof'' in H2... congruence. }
        assert (Forall2 (fun '(_, nck) e => nclockof e = [nck]) (map snd x5) fby) as Hcks.
        { eapply idents_for_anns_values in H3; subst.
          specialize (normalize_fby_annot' _ _ _ Hlen1' Hlen2') as Hanns'; eauto. clear - Hanns'.
          eapply Forall2_swap_args. solve_forall.
          destruct a0 as [ty ck]; simpl in *. rewrite nclockof_annot, H1; auto. } subst a.
        solve_forall.
        repeat constructor; eauto.
        * destruct a as [ty [ck name]]; simpl in *.
          rewrite app_nil_r, H9. constructor; auto.
          eapply idents_for_anns_values in H3; rewrite <- H3 in H8.
          eapply Forall_forall in H8. 2:simpl_In; exists (i, (ty, (ck, name))); auto.
          inv H8; simpl in H11; subst. constructor.
        * destruct a as [ty [ck name]]; simpl in *.
          rewrite app_nil_r, clockof_nclockof, H9; simpl.
          constructor; auto.
          eapply idents_for_anns_incl_clocks in H3.
          apply in_or_app, or_intror, H3.
          repeat simpl_In. exists (i, (ty, (ck, name))); auto.
      + eapply idents_for_anns_wc_env in H3...
        assert (Forall (wc_clock ((vars ++ st_clocks x1))) (map clock_of_nclock a)).
        { rewrite H6.
          eapply wc_exp_clocksof in H4... eapply Forall_impl; [|eauto]. intros.
          eapply wc_clock_incl; [|eauto]. rewrite <- app_assoc in *.
          apply incl_appr', incl_app; repeat solve_incl.
          apply map_bind2_normalize_exp_fresh_incl in H1...
          unfold st_clocks. apply incl_map, H1. }
        solve_forall; repeat solve_incl.
    - (* when *)
      eapply map_bind2_wc_eq in H0 as [Hwc1 Hwenv1]...
      rewrite Forall_forall in H, H4. rewrite Forall_forall; intros.
      eapply H in H1. 1,2,3,5:eauto.
      apply H4 in H1; repeat solve_incl.
    - (* merge *)
      assert (length (concat x3) = length (annots ets)) as Hlen1 by eauto.
      assert (length (concat x6) = length (annots efs)) as Hlen2 by eauto.
      assert (H1':=H1).
      eapply map_bind2_wc_eq in H1' as [Hwc1 Hwenv1]...
      2: { rewrite Forall_forall in *; intros; simpl in *.
           eapply H... eapply H5 in H4. repeat solve_incl. }
      assert (H2':=H2).
      eapply map_bind2_wc_eq in H2' as [Hwc2 Hwenv2]...
      2: { rewrite Forall_forall in *; intros; simpl in *.
           eapply H0... eapply H6 in H4. repeat solve_incl. }
      clear H H0.
      destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split.
      1,2,5,6:(solve_forall; repeat solve_incl). 1:eauto.
      2:{ eapply idents_for_anns_wc_env in H...
          repeat rewrite Forall_map.
          rewrite Forall_forall. intros ty _; simpl.
          unfold wc_env in Hwenv; rewrite Forall_forall in Hwenv; eapply Hwenv in H7; simpl in H7.
          repeat solve_incl. }
      assert (Forall (wc_exp G (vars++st_clocks st')) (normalize_merge x (concat x3) (concat x6) tys (ck, None))) as Hwcexp.
      { eapply normalize_merge_wc_exp...
        + rewrite Hlen1, H10. solve_length.
        + rewrite Hlen2, H11. solve_length.
        + assert (incl (vars++st_clocks st) (vars++st_clocks st')) by repeat solve_incl...
        + eapply map_bind2_normalize_exp_wc_exp with (vars:=vars) in H1...
          solve_forall; repeat solve_incl.
        + eapply map_bind2_normalize_exp_wc_exp with (G:=G) (vars:=vars) in H2...
          1,2: solve_forall; repeat solve_incl.
        + eapply map_bind2_normalize_exp_clocksof''' in H1...
        + eapply map_bind2_normalize_exp_clocksof''' in H2... }
      assert (Forall (fun e : exp => nclockof e = [(ck, None)]) (normalize_merge x (concat x3) (concat x6) tys (ck, None))) as Hnck.
      { eapply normalize_merge_nclockof; solve_length. }
      solve_forall. 2:(eapply idents_for_anns_length in H; solve_length).
      repeat split. 2,3:rewrite app_nil_r.
      + repeat constructor...
      + rewrite H4. repeat constructor.
      + rewrite clockof_nclockof, H4; simpl. repeat constructor.
        assert (H':=H). apply idents_for_anns_values in H'.
        apply idents_for_anns_incl_clocks in H.
        destruct a as [ty [ck' name']].
        apply in_or_app; right. apply H.
        simpl_In. exists (i, (ty, (ck', name'))). split; auto.
        assert (In (ty, (ck', name')) (map snd x0)) by (simpl_In; exists (i, (ty, (ck', name'))); auto).
        rewrite H' in H13. simpl_In. inv H13; auto.
    - (* ite *)
      assert (length (concat x5) = length (annots ets)) as Hlen1 by eauto.
      assert (length (concat x8) = length (annots efs)) as Hlen2 by eauto.
      assert (H1':=H1).
      eapply IHe in H1' as [Hwc1 Hwenv1]...
      assert (H2':=H2).
      eapply map_bind2_wc_eq in H2' as [Hwc2 Hwenv2]...
      2: { rewrite Forall_forall in *; intros; simpl in *.
           eapply H... eapply H6 in H14. repeat solve_incl. }
      assert (H3':=H3).
      eapply map_bind2_wc_eq in H3' as [Hwc3 Hwenv3]...
      2: { rewrite Forall_forall in *; intros; simpl in *.
           eapply H0... eapply H7 in H14. repeat solve_incl. }
      clear H H0 IHe.
      destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split.
      1,2,3,6,7,8:solve_forall;repeat solve_incl. 1:eauto.
      2:{ eapply idents_for_anns_wc_env in H...
          repeat rewrite Forall_map.
          rewrite Forall_forall. intros ty _; simpl.
          eapply wc_exp_clockof in H5... rewrite H8 in H5. inv H5.
          solve_incl. rewrite <- app_assoc. apply incl_appr', incl_app; [repeat solve_incl|].
          unfold st_clocks. apply incl_map.
          eapply normalize_exp_fresh_incl in H1. etransitivity...
          apply st_follows_incl. repeat solve_st_follows. }
      assert (Forall (wc_exp G (vars++st_clocks st')) (normalize_ite (hd_default x) (concat x5) (concat x8) tys (ck, None))) as Hwcexp.
      { eapply normalize_ite_wc_exp...
        + rewrite Hlen1, H11; solve_length.
        + rewrite Hlen2, H12; solve_length.
        + eapply hd_default_wc_exp. eapply normalize_exp_wc_exp in H1...
          solve_forall; repeat solve_incl.
        + eapply map_bind2_normalize_exp_wc_exp with (G:=G) (vars:=vars) in H2...
          1,2: solve_forall; repeat solve_incl.
        + eapply map_bind2_normalize_exp_wc_exp with (G:=G) (vars:=vars) in H3...
          1,2: solve_forall; repeat solve_incl.
        + assert (length x = 1); [|singleton_length].
          { eapply normalize_exp_length in H1... rewrite H1, <- length_clockof_numstreams, H8; auto. }
          eapply normalize_exp_clockof in H1... simpl in H1; rewrite app_nil_r in H1. congruence.
        + eapply map_bind2_normalize_exp_clocksof''' in H2...
        + eapply map_bind2_normalize_exp_clocksof''' in H3... }
      assert (Forall (fun e : exp => nclockof e = [(ck, None)]) (normalize_ite (hd_default x) (concat x5) (concat x8) tys (ck, None))) as Hnck.
      { eapply normalize_ite_nclockof; solve_length. }
      solve_forall. 2:(eapply idents_for_anns_length in H; solve_length).
      repeat split. 2,3:rewrite app_nil_r.
      + repeat constructor...
      + rewrite H14. repeat constructor.
      + rewrite clockof_nclockof, H14; simpl. repeat constructor.
        assert (H':=H). apply idents_for_anns_values in H'.
        apply idents_for_anns_incl_clocks in H.
        destruct a as [ty [ck' name']].
        apply in_or_app; right. apply H.
        simpl_In. exists (i, (ty, (ck', name'))). split; auto.
        assert (In (ty, (ck', name')) (map snd x2)) by (simpl_In; exists (i, (ty, (ck', name'))); auto).
        rewrite H' in H16. simpl_In. inv H16; auto.
    - (* app *)
      rewrite app_nil_r.
      assert (H1':=H1).
      eapply map_bind2_wc_eq in H1' as [Hwc1 Hwenv1]...
      2:{ rewrite Forall_forall in *; intros. eapply H0...
          eapply H5 in H3. repeat solve_incl. } clear H0.
      repeat constructor; simpl...
      + repeat econstructor; simpl...
        * eapply map_bind2_normalize_exp_wc_exp in H1...
          solve_forall. repeat solve_incl.
        * erewrite map_bind2_normalize_exp_nclocksof...
        * erewrite idents_for_anns'_values...
      + rewrite app_nil_r, map_map, Forall2_map_1, Forall2_map_2, <- Forall2_same.
        eapply idents_for_anns'_clocknames...
      + unfold clock_of_nclock, stripname.
        rewrite app_nil_r, map_map, Forall2_map_1, Forall2_map_2, <- Forall2_same.
        eapply idents_for_anns'_incl_clocks in H2.
        apply Forall_forall; intros.
        apply in_or_app; right. apply H2.
        rewrite in_map_iff. exists x; split; auto. destruct x as [? [? [? ?]]]; auto.
      + solve_forall. repeat solve_incl.
      + eapply idents_for_anns'_wc_env...
        apply wc_exp_clockof in Hwc...
        unfold clock_of_nclock, stripname in Hwc.
        rewrite map_map. eapply Forall_impl; [|eauto].
        intros. rewrite <- app_assoc in H0. repeat solve_incl.
        apply incl_app; [repeat solve_incl|].
        unfold st_clocks. apply incl_map...
    - (* app (reset) *)
      assert (H1':=H1).
      eapply map_bind2_wc_eq in H1' as [Hwc1 Hwenv1]...
      2:{ rewrite Forall_forall in *; intros. eapply H0...
          eapply H5 in H11. repeat solve_incl. }
      assert (H2':=H2).
      eapply H in H2' as [Hwc2 Hwenv2]... 2:repeat solve_incl.
      clear H H0.
      rewrite cons_is_app.
      repeat constructor; repeat rewrite Forall_app; repeat split; simpl...
      + repeat econstructor; simpl...
        * eapply map_bind2_normalize_exp_wc_exp in H1...
          solve_forall. repeat solve_incl.
        * erewrite map_bind2_normalize_exp_nclocksof...
        * erewrite idents_for_anns'_values...
        * eapply normalize_reset_wc_exp with (G:=G) (vars:=vars) in H4...
          repeat solve_incl.
          eapply hd_default_wc_exp.
          eapply normalize_exp_wc_exp in H2... repeat solve_incl.
        * assert (length x6 = numstreams r) as Hlen by eauto.
          rewrite <- length_clockof_numstreams, H10 in Hlen; simpl in Hlen.
          singleton_length.
          eapply normalize_exp_clockof in H2... simpl in H2; rewrite app_nil_r, H10 in H2; clear H10.
          assert (numstreams e = 1) as Hnum by (rewrite <- length_clockof_numstreams, H2; eauto).
          eapply normalize_reset_clockof in Hnum... rewrite Hnum, H2...
      + rewrite app_nil_r, map_map, Forall2_map_1, Forall2_map_2, <- Forall2_same.
        eapply idents_for_anns'_clocknames...
      + unfold clock_of_nclock, stripname.
        rewrite app_nil_r, map_map, Forall2_map_1, Forall2_map_2, <- Forall2_same.
        eapply idents_for_anns'_incl_clocks in H3.
        apply Forall_forall; intros.
        apply in_or_app; right. apply H3.
        rewrite in_map_iff. exists x; split; auto. destruct x as [? [? [? ?]]]; auto.
      + solve_forall; repeat solve_incl.
      + solve_forall; repeat solve_incl.
      + eapply normalize_reset_wc_eq with (G:=G) (vars:=vars) in H4...
        solve_forall; repeat solve_incl.
        eapply hd_default_wc_exp.
        eapply normalize_exp_wc_exp in H2... repeat solve_incl.
      + assert (length x6 = 1) as Hlen.
        { eapply normalize_exp_length in H2... rewrite H2, <- length_clockof_numstreams, H10... }
        singleton_length.
        assert (clockof e = [ckr]) as Hck.
        { eapply normalize_exp_clockof in H2... simpl in H2; rewrite app_nil_r in H2. congruence. }
        specialize (normalize_exp_fresh_incl _ _ _ _ _ _ H2) as Hincl'.
        assert (st_follows x8 st') as Hfollows3 by repeat solve_st_follows.
        eapply normalize_reset_wc_env in H4...
        2: { rewrite Hck. repeat constructor.
             eapply wc_exp_clockof in H9...
             rewrite H10 in H9; inv H9. rewrite <- app_assoc in H11.
             repeat solve_incl. apply incl_app; [repeat solve_incl|].
             unfold st_clocks. apply incl_map... }
        eapply idents_for_anns'_wc_env in H3...
        apply wc_exp_clockof in Hwc...
        unfold clock_of_nclock, stripname in Hwc.
        rewrite map_map. eapply Forall_impl; [|eauto].
        intros. rewrite <- app_assoc in H. repeat solve_incl.
        apply incl_app; [repeat solve_incl|].
        unfold st_clocks. apply incl_map...
  Qed.

  Corollary normalize_exp_wc_env : forall G vars e is_control es' eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      wc_exp G (vars++st_clocks st) e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      wc_env (vars++st_clocks st').
  Proof.
    intros. eapply normalize_exp_wc_eq in H as [_ ?]; eauto.
  Qed.

  Corollary map_bind2_normalize_exp_wc_env : forall G vars es is_control es' eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      Forall (wc_exp G (vars++st_clocks st)) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      wc_env (vars++st_clocks st').
  Proof.
    intros.
    eapply map_bind2_wc_env in H2; eauto.
    rewrite Forall_forall in *; intros.
    eapply normalize_exp_wc_env in H5; eauto.
    eapply H1 in H3. repeat solve_incl.
  Qed.

  Corollary normalize_exps_wc_eq : forall G vars es es' eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      Forall (wc_exp G (vars++st_clocks st)) es ->
      normalize_exps es st = (es', eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs' /\
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros G vars es es' eqs' st st' HwG Hwenv Hwc Hnorm.
    unfold normalize_exps in Hnorm; repeat inv_bind.
    eapply map_bind2_wc_eq in H...
    solve_forall.
    eapply normalize_exp_wc_eq with (G:=G) (vars:=vars) in H5...
    repeat solve_incl.
  Qed.

  Fact normalize_rhs_wc_eq : forall G vars e es' eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      wc_exp G (vars++st_clocks st) e ->
      normalize_rhs e st = (es', eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs' /\
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros * HwG Hwenv Hwc Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (solve [eapply normalize_exp_wc_eq in Hnorm; eauto]);
      [|inv Hwc].
    - (* fby *)
      assert (Hwc':=Hwc). inv Hwc'.
      repeat inv_bind.
      assert (st_follows x1 st') as Hfollows1 by repeat solve_st_follows.
      assert (H':=H). eapply normalize_exps_wc_eq in H' as [Hwc1 Hwenv1]...
      assert (H0':=H0). eapply normalize_exps_wc_eq in H0' as [Hwc2 Hwenv2]...
      2:solve_forall; repeat solve_incl.
      split; repeat rewrite Forall_app; repeat split; eauto.
      solve_forall; repeat solve_incl.
    - (* app *)
      repeat inv_bind. rewrite app_nil_r.
      eapply normalize_exps_wc_eq in H...
    - (* app (reset) *)
      repeat inv_bind.
      assert (H':=H).
      eapply normalize_exps_wc_eq in H' as [Hwc1 Hwenv1]...
      assert (H0':=H0).
      eapply normalize_exp_wc_eq with (G:=G) (vars:=vars) in H0' as [Hwc2 Hwenv2]...
      repeat rewrite Forall_app; repeat split.
      + solve_forall; repeat solve_incl.
      + solve_forall. repeat solve_incl.
      + eapply normalize_reset_wc_eq in H1...
        eapply hd_default_wc_exp. eapply normalize_exp_wc_exp in H0...
        repeat solve_incl.
      + assert (length x4 = 1) as Hlen.
        { eapply normalize_exp_length in H0... rewrite H0, <- length_clockof_numstreams, H8... }
        singleton_length.
        assert (clockof e = [ckr]) as Hck.
        { eapply normalize_exp_clockof in H0... simpl in H0; rewrite app_nil_r in H0. congruence. }
        specialize (normalize_exp_fresh_incl _ _ _ _ _ _ H0) as Hincl'.
        eapply normalize_reset_wc_env in H1...
        rewrite Hck. repeat constructor.
        eapply wc_exp_clockof in H7...
        rewrite H8 in H7; inv H7. rewrite <- app_assoc in H10.
        repeat solve_incl. apply incl_app; [repeat solve_incl|].
        unfold st_clocks. apply incl_map...
      + repeat solve_incl.
  Qed.

  Corollary normalize_rhss_wc_eq : forall G vars es es' eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      Forall (wc_exp G (vars++st_clocks st)) es ->
      normalize_rhss es st = (es', eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs' /\
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros * HwG Hwenv Hwc Hnorm.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_wc_eq in H...
    solve_forall.
    eapply normalize_rhs_wc_eq with (G:=G) (vars:=vars) in H5...
    repeat solve_incl.
  Qed.

  Fact untuple_equation_wc_eq : forall G vars e eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      wc_equation G (vars++st_clocks st) e ->
      untuple_equation e st = (eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs' /\
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros G vars [xs es] eqs' st st' HwG Hwenv Hwc Hnorm.
    unfold untuple_equation in Hnorm. repeat inv_bind.
    destruct Hwc as [Hwc1 [Hwc2 Hwc3]].
    assert (st_follows st st') as Hfollows by eauto.
    assert (H':=H). eapply normalize_rhss_wc_eq in H' as [Hwc' Hwenv']...
    split...
    apply Forall_app; split...
    rewrite clocksof_nclocksof, Forall2_map_2 in Hwc3.
    eapply Forall2_Forall2 in Hwc2; [|eapply Hwc3]. clear Hwc3.
    replace (nclocksof es) with (nclocksof x) in Hwc2.
    2: { eapply normalize_rhss_nclocksof in H... }
    eapply normalize_rhss_wc_exp in H... clear Hwc1 Hwc' Hwenv'.
    revert xs H Hwc2.
    induction x; intros xs Hwc1 Hwc2; simpl in *; constructor.
    + inv Hwc1.
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
    + inv Hwc1. apply IHx...
      assert (length (firstn (numstreams a) xs) = length (nclockof a)) as Hlen1.
      { apply Forall2_length in Hwc2. rewrite app_length in Hwc2.
        rewrite firstn_length, Hwc2, length_nclockof_numstreams.
        apply Nat.min_l. omega. }
      rewrite <- (firstn_skipn (numstreams a) xs) in Hwc2.
      apply Forall2_app_split in Hwc2 as [_ Hwc2]...
  Qed.

  Corollary untuple_equations_wc_eq : forall G vars eqs eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      Forall (wc_equation G (vars++st_clocks st)) eqs ->
      untuple_equations eqs st = (eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs' /\
      wc_env (vars++st_clocks st').
  Proof with eauto.
    induction eqs; intros * HwG Hwenv Hwc Hnorm;
      unfold untuple_equations in *; simpl in *; repeat inv_bind...
    assert (st_follows st x1) as Hfollows1 by repeat solve_st_follows.
    assert (st_follows x1 st') as Hfollows2 by repeat solve_st_follows.
    inv Hwc. eapply untuple_equation_wc_eq in H as [Hwc1 Hwenv1]...
    assert (untuple_equations eqs x1 = (concat x2, st')) as Hnorm.
      { unfold untuple_equations; repeat inv_bind. repeat eexists; eauto. inv_bind; eauto. }
    apply IHeqs in Hnorm as [Hwc2 Hwenv2]... 2:solve_forall; repeat solve_incl.
    split...
    apply Forall_app; split...
    solve_forall; repeat solve_incl.
  Qed.

  Lemma untuple_node_wc : forall G n Hwl,
      wc_global G ->
      wc_node G n ->
      wc_node G (untuple_node n Hwl).
  Proof with eauto.
    intros * HwG [Hin [Hout [Henv Heq]]].
    unfold untuple_node.
    repeat constructor; simpl; auto.
    - remember (untuple_equations _ _) as res. symmetry in Heqres.
      destruct res as [eqs' st']; simpl.
      unfold idck. repeat rewrite map_app.
      eapply untuple_equations_wc_eq in Heqres as [_ Henv']...
      2,3:unfold st_clocks; rewrite init_st_anns, app_nil_r...
      2:rewrite (Permutation_app_comm (n_vars _)) in Heq...
      unfold idck in Henv'; repeat rewrite map_app in Henv'; repeat rewrite <- app_assoc in Henv'...
    - remember (untuple_equations _ _) as res. symmetry in Heqres.
      destruct res as [eqs' st']; simpl.
      unfold idck. repeat rewrite map_app.
      eapply untuple_equations_wc_eq in Heqres as [Hwc' _]...
      2,3:unfold st_clocks; rewrite init_st_anns, app_nil_r...
      2:rewrite (Permutation_app_comm (n_vars _)) in Heq...
      unfold idck in Hwc'; repeat rewrite map_app in Hwc'; repeat rewrite <- app_assoc in *.
      rewrite (Permutation_app_comm (map _ (st_anns _))), (Permutation_swap (map _ (n_vars _)))...
  Qed.

  Lemma untuple_global_wc : forall G Hwl,
      wc_global G ->
      wc_global (untuple_global G Hwl).
  Proof.
    induction G; intros * Hwc; simpl; inv Hwc.
    - constructor.
    - constructor.
      + eapply IHG; eauto.
      + eapply untuple_node_wc; eauto.
        eapply iface_eq_wc_node; eauto.
        eapply untuple_global_eq.
      + eapply untuple_global_names; eauto.
  Qed.

  (** ** Preservation of clocking through second pass *)

  Fact fby_iteexp_wc_exp : forall G vars e0 e ty ck name e' eqs' st st',
      wc_exp G (vars++st_clocks' st) e0 ->
      wc_exp G (vars++st_clocks' st) e ->
      clockof e0 = [ck] ->
      clockof e = [ck] ->
      unnamed_stream (ty, (ck, name)) ->
      fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
      wc_exp G (vars++st_clocks' st') e'.
  Proof with eauto.
    intros * Hwc1 Hwc2 Hck1 Hck2 Hunnamed Hfby.
    unfold fby_iteexp in Hfby; simpl in *.
    inv Hunnamed; simpl in H; subst.
    destruct (is_constant e0); repeat inv_bind; repeat constructor; simpl...
    1,2,6,7:rewrite app_nil_r; unfold clock_of_nclock, stripname; simpl.
    1,3,4:rewrite Hck1; constructor; auto.
    - rewrite Hck2; constructor; auto.
    - apply in_or_app, or_intror. unfold st_clocks', idty, idck. rewrite map_map.
      simpl_In. exists (x, (Op.bool_type, ck, true)); split; auto.
      eapply init_var_for_clock_In in H.
      eapply fresh_ident_st_follows, st_follows_incl in H0; auto.
    - eapply init_var_for_clock_st_follows in H. repeat solve_incl.
    - eapply fresh_ident_In in H0.
      apply in_or_app, or_intror. unfold st_clocks', idty, idck. rewrite map_map.
      simpl_In. exists (x2, (ty, ck, false)); split; auto.
  Qed.

  Fact fresh_ident_wc_env' : forall vars ty ck b id st st',
      wc_env (vars++st_clocks' st) ->
      wc_clock (vars++st_clocks' st) ck ->
      fresh_ident (ty, ck, b) st = (id, st') ->
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

  Fact init_var_for_clock_wc_env : forall vars cl id eqs' st st',
      wc_env (vars++st_clocks' st) ->
      wc_clock (vars++st_clocks' st) cl ->
      init_var_for_clock cl st = (id, eqs', st') ->
      wc_env (vars++st_clocks' st').
  Proof with eauto.
    intros vars cl id eqs' st st' Hwenv Hwc Hinit.
    unfold init_var_for_clock in Hinit.
    destruct find.
    - destruct p. inv Hinit...
    - destruct fresh_ident eqn:Hfresh. inv Hinit.
      eapply fresh_ident_wc_env' in Hfresh...
  Qed.

  Fact fby_iteexp_wc_env : forall vars e0 e ty cl es' eqs' st st',
      wc_env (vars++st_clocks' st) ->
      wc_clock (vars++st_clocks' st) (fst cl) ->
      fby_iteexp e0 e (ty, cl) st = (es', eqs', st') ->
      wc_env (vars++st_clocks' st').
  Proof with eauto.
    intros vars e0 e ty [cl name] es' eqs' st st' Hwenv Hwc Hfby.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind...
    eapply fresh_ident_wc_env' in H0... 2:repeat solve_incl.
    eapply init_var_for_clock_wc_env in H... eapply init_var_for_clock_st_follows in H...
  Qed.

  Fact init_var_for_clock_wc_eq : forall G vars ck id eqs' st st',
      wc_clock (vars++st_clocks' st) ck ->
      init_var_for_clock ck st = (id, eqs', st') ->
      Forall (wc_equation G (vars++st_clocks' st')) eqs'.
  Proof with eauto.
    intros * Hwc Hinit.
    unfold init_var_for_clock in Hinit.
    destruct find.
    - destruct p; repeat inv_bind...
    - destruct fresh_ident eqn:Hfresh; repeat inv_bind.
      repeat constructor; simpl...
      + apply add_whens_wc_exp... repeat solve_incl.
      + apply add_whens_wc_exp... repeat solve_incl.
      + rewrite app_nil_r, add_whens_clockof...
      + rewrite app_nil_r, add_whens_clockof...
      + apply fresh_ident_In in Hfresh.
        apply in_or_app; right.
        unfold st_clocks', idck, idty. rewrite map_map.
        simpl_In. exists (id, (Op.bool_type, ck, true)); auto.
  Qed.

  Fact normalized_lexp_wc_exp_clockof : forall G vars e,
      normalized_lexp e ->
      wc_env vars ->
      wc_exp G vars e ->
      Forall (wc_clock vars) (clockof e).
  Proof with eauto.
    intros G vars e Hnormed Hwenv Hwc.
    induction Hnormed; inv Hwc;
      simpl; unfold clock_of_nclock, stripname; simpl; repeat constructor...
    1,2:(unfold wc_env in Hwenv; rewrite Forall_forall in Hwenv; eapply Hwenv in H0; eauto).
    - eapply IHHnormed in H1. rewrite H4 in H1. inv H1...
    - eapply IHHnormed1 in H3. rewrite H6 in H3. inv H3...
    - inv H3.
      eapply IHHnormed in H1.
      simpl in H7. rewrite app_nil_r in H7. symmetry in H7.
      singleton_length.
      inv H6. inv H1...
  Qed.

  Fact fby_iteexp_wc_eq : forall G vars e0 e ty ck name e' eqs' st st',
      normalized_lexp e0 ->
      wc_env (vars++st_clocks' st) ->
      wc_exp G (vars++st_clocks' st) e0 ->
      wc_exp G (vars++st_clocks' st) e ->
      clockof e0 = [ck] ->
      clockof e = [ck] ->
      unnamed_stream (ty, (ck, name)) ->
      fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
      Forall (wc_equation G (vars++st_clocks' st')) eqs'.
  Proof with eauto.
    intros * Hnormed Henv Hwc1 Hwc2 Hcl1 Hcl2 Hunnamed Hfby.
    assert (wc_clock (vars++st_clocks' st) ck) as Hwck.
    { eapply normalized_lexp_wc_exp_clockof in Hwc1...
      rewrite Hcl1 in Hwc1; inv Hwc1; auto. }
    unfold fby_iteexp in Hfby; simpl in *.
    destruct (is_constant e0); repeat inv_bind; repeat constructor; simpl...
    - eapply add_whens_wc_exp...
      eapply init_var_for_clock_st_follows in H. repeat solve_incl.
    - eapply init_var_for_clock_st_follows in H. repeat solve_incl.
    - rewrite app_nil_r, add_whens_clockof...
    - rewrite app_nil_r. rewrite Hcl2...
    - unfold unnamed_stream in Hunnamed; simpl in Hunnamed. rewrite Hunnamed. constructor.
    - eapply fresh_ident_In in H0.
      apply in_or_app; right.
      unfold clock_of_nclock, stripname; simpl in *.
      unfold st_clocks', idck, idty. rewrite map_map.
      simpl_In. exists (x2, (ty, ck, false)); auto.
    - eapply init_var_for_clock_wc_eq with (G:=G) in H...
      solve_forall; repeat solve_incl.
  Qed.

  Fact fby_equation_wc_eq : forall G vars to_cut eq eqs' st st',
      untupled_equation eq ->
      wc_env (vars++st_clocks' st) ->
      wc_equation G (vars++st_clocks' st) eq ->
      fby_equation to_cut eq st = (eqs', st') ->
      (Forall (wc_equation G (vars++st_clocks' st')) eqs' /\ wc_env (vars++st_clocks' st')).
  Proof with eauto.
    intros * Hunt Hwenv Hwc Hfby.
    inv_fby_equation Hfby to_cut eq.
    destruct x2 as [ty [ck name]]; repeat inv_bind.
    assert (st_follows st x4) as Hfollows by (eapply fby_iteexp_st_follows with (ann:=(ty, (ck, name))) in H; eauto).
    destruct Hwc as [Hwc [_ Hins]]; inv Hwc; clear H4.
    inv H3; simpl in *; rewrite app_nil_r in *.
    inv H5; clear H4. inv H6; clear H5. inv H9; clear H6. inv H5; simpl in H1; subst.
    inv Hunt. 2:inv H2; inv H1.
    inv Hins; clear H12.
    rewrite Forall2_eq in H7, H8.
    assert (H':=H). eapply fby_iteexp_wc_eq in H; eauto. 2:constructor.
    unfold clock_of_nclock, stripname in *; simpl in *.
    assert (wc_clock (vars++st_clocks' st) ck) as Hwck.
    { eapply normalized_lexp_wc_exp_clockof in H4...
      rewrite <- H8 in H4; inv H4; auto. }
    destruct (PS.mem _ _); repeat inv_bind; repeat constructor; simpl; auto.
    4,5,9,10:rewrite app_nil_r.
    - eapply fresh_ident_In in H0.
      apply in_or_app, or_intror. unfold st_clocks', idty, idck.
      simpl_In. exists (x5, (ty, ck)); split; auto.
      simpl_In. exists (x5, (ty, ck, false)); split; auto.
    - assert (incl (vars ++ st_clocks' st) (vars ++ st_clocks' st')) by repeat solve_incl; eauto.
    - eapply fby_iteexp_wc_exp in H'... 2:constructor. repeat solve_incl.
    - eapply fby_iteexp_nclockof with (ann:=(ty, (ck, None))) in H'.
      rewrite H'; simpl. constructor... constructor.
    - eapply fby_iteexp_clockof with (ann:=(ty, (ck, None))) in H'.
      rewrite H'; simpl. constructor; auto.
      eapply fresh_ident_In in H0.
      apply in_or_app, or_intror. unfold st_clocks', idty, idck.
      simpl_In. exists (x5, (ty, ck)); split; auto.
      simpl_In. exists (x5, (ty, ck, false)); split; auto.
    - eapply fby_iteexp_nclockof with (ann:=(ty, (ck, None))) in H'.
      rewrite H'; simpl. constructor; auto. constructor.
    - eapply fby_iteexp_clockof with (ann:=(ty, (ck, None))) in H'.
      rewrite H'; simpl. constructor; auto.
      assert (incl (vars ++ st_clocks' st) (vars ++ st_clocks' st')) by repeat solve_incl; eauto.
    - solve_forall; repeat solve_incl.
    - eapply fby_iteexp_wc_env in H'...
      eapply fresh_ident_wc_env' in H0... repeat solve_incl.
    - eapply fby_iteexp_wc_exp in H'... constructor.
    - eapply fby_iteexp_wc_env in H'...
  Qed.

  Fact fby_equations_wc_eq : forall G vars to_cut eqs eqs' st st',
      Forall untupled_equation eqs ->
      wc_env (vars++st_clocks' st) ->
      Forall (wc_equation G (vars++st_clocks' st)) eqs ->
      fby_equations to_cut eqs st = (eqs', st') ->
      (Forall (wc_equation G (vars++st_clocks' st')) eqs' /\ wc_env (vars++st_clocks' st')).
  Proof.
    induction eqs; intros * Hunt Henv Hwc Hfby;
      unfold fby_equations in *; repeat inv_bind; simpl; auto.
    inv Hunt. inv Hwc.
    assert (fby_equations to_cut eqs x1 = (concat x2, st')) as Hnorm.
    { unfold fby_equations. repeat inv_bind. repeat eexists; eauto.
      inv_bind; auto. }
    assert (H':=H). eapply fby_equation_wc_eq in H as [Hwc' Henv']; eauto.
    eapply IHeqs in Hnorm as [Hwc'' Henv'']; eauto.
    2:solve_forall; repeat solve_incl; eapply fby_equation_st_follows in H'; eauto.
    rewrite Forall_app; repeat split; eauto.
    solve_forall; repeat solve_incl.
  Qed.

  Lemma normfby_node_wc : forall G to_cut n Hunt,
      wc_node G n ->
      wc_node G (normfby_node to_cut n Hunt).
  Proof.
    intros * [Hclin [Hclout [Hclvars Heq]]].
    unfold normfby_node.
    repeat constructor; simpl; auto.
    - remember (fby_equations _ _ _) as res. symmetry in Heqres. destruct res as [eqs' st'].
      eapply fby_equations_wc_eq in Heqres as [_ ?]; eauto.
      2,3:unfold st_clocks'; rewrite init_st_anns, app_nil_r.
      2:eapply Hclvars.
      + repeat rewrite idck_app in *.
        repeat rewrite <- app_assoc in H; auto.
      + solve_forall.
        eapply wc_equation_incl; eauto.
        rewrite (Permutation_app_comm (n_out n)). reflexivity.
    - remember (fby_equations _ _ _) as res. symmetry in Heqres. destruct res as [eqs' st'].
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

  Lemma normfby_global_wc : forall G Hunt,
      wc_global G ->
      wc_global (normfby_global G Hunt).
  Proof.
    induction G; intros * Hwt; simpl; inv Hwt.
    - constructor.
    - constructor.
      + eapply IHG; eauto.
      + remember (normfby_node _ _) as n'. symmetry in Heqn'.
        subst.
        eapply normfby_node_wc; eauto.
        eapply iface_eq_wc_node; eauto.
        eapply normfby_global_eq.
      + eapply normfby_global_names; eauto.
  Qed.

  (** ** Conclusion *)

  Lemma normalize_global_wt : forall G Hwl G',
      wc_global G ->
      normalize_global G Hwl = Errors.OK G' ->
      wc_global G'.
  Proof.
    intros * Hwc Hnorm.
    unfold normalize_global in Hnorm. destruct (Caus.check_causality _); inv Hnorm.
    eapply normfby_global_wc, untuple_global_wc, Hwc.
  Qed.

End NCLOCKING.

Module NClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Caus : LCAUSALITY Ids Op Syn)
       (Clo : LCLOCKING Ids Op Syn)
       (Norm : NORMALIZATION Ids Op OpAux Syn Caus)
       <: NCLOCKING Ids Op OpAux Syn Caus Clo Norm.
  Include NCLOCKING Ids Op OpAux Syn Caus Clo Norm.
End NClockingFun.
