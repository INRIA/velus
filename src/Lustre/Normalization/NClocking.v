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

  Fact unnest_reset_clockof : forall G vars e e' eqs' st st',
      LiftO True (wc_exp G vars) e ->
      LiftO True (fun e => numstreams e = 1) e ->
      unnest_reset (unnest_exp true) e st = (e', eqs', st') ->
      LiftO True (fun e => LiftO True (fun e' => clockof e' = clockof e) e') e.
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
  Corollary map_bind2_unnest_exp_clocksof' :
    forall G vars is_control es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      map_bind2 (unnest_exp is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => clocksof es' = clockof e) es' es.
  Proof with eauto.
    intros G vars is_control es es' eqs' st st' Hwt Hmap.
    eapply map_bind2_unnest_exp_annots' in Hmap...
    clear Hwt.
    induction Hmap; constructor; eauto.
    rewrite clocksof_annots, H, <- clockof_annot...
  Qed.

  Corollary map_bind2_unnest_exp_clocksof'' : forall G vars is_control es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      map_bind2 (unnest_exp is_control) es st = (es', eqs', st') ->
      Forall2 (fun e ck => clockof e = [ck]) (concat es') (clocksof es).
  Proof.
    intros * Hwl Hmap.
    eapply map_bind2_unnest_exp_annots'' in Hmap; eauto.
    rewrite clocksof_annots, Forall2_map_2, Forall2_map_2.
    eapply Forall2_impl_In; eauto. intros; simpl in *.
    rewrite clockof_annot, H1; auto.
  Qed.

  Corollary map_bind2_unnest_exp_clocksof''' : forall G vars is_control ck es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      Forall (eq ck) (clocksof es) ->
      map_bind2 (unnest_exp is_control) es st = (es', eqs', st') ->
      Forall (fun e => clockof e = [ck]) (concat es').
  Proof.
    intros * Hwl Hck Hmap.
    assert (Hmap':=Hmap). eapply map_bind2_unnest_exp_numstreams in Hmap.
    eapply map_bind2_unnest_exp_annots'' in Hmap'; eauto.
    rewrite clocksof_annots in Hck.
    assert (length (concat es') = length (annots es)) by (apply Forall2_length in Hmap'; auto).
    assert (Forall (fun e => exists y, In y (annots es) /\ (clockof e = [ck])) (concat es')) as Hf'.
    { eapply Forall2_ignore2. solve_forall.
      rewrite clockof_annot, H2; simpl in *. congruence. }
    solve_forall. destruct H1 as [_ [_ ?]]; auto.
  Qed.

  Corollary map_bind2_unnest_exp_clocksof :
    forall G vars is_control es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      map_bind2 (unnest_exp is_control) es st = (es', eqs', st') ->
      clocksof (concat es') = clocksof es.
  Proof.
    intros.
    eapply map_bind2_unnest_exp_annots in H0; eauto.
    rewrite clocksof_annots, H0, <- clocksof_annots; eauto.
  Qed.
  Hint Resolve map_bind2_unnest_exp_clocksof.

  Corollary unnest_exps_clocksof : forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      unnest_exps es st = (es', eqs', st') ->
      clocksof es' = clocksof es.
  Proof.
    intros.
    eapply unnest_exps_annots in H0; eauto.
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

  Fact unnest_fby_clockof : forall anns e0s es,
      length e0s = length anns ->
      length es = length anns ->
      clocksof (unnest_fby e0s es anns) = List.map clock_of_nclock anns.
  Proof.
    intros * Hlen1 Hlen2.
    rewrite clocksof_annots, unnest_fby_annot, map_map; auto.
  Qed.

  Fact unnest_rhs_clockof: forall G vars e es' eqs' st st',
      wc_exp G vars e ->
      unnest_rhs e st = (es', eqs', st') ->
      clocksof es' = clockof e.
  Proof.
    intros * Hwc Hnorm.
    eapply unnest_rhs_annot in Hnorm; eauto.
    rewrite clocksof_annots, Hnorm, <- clockof_annot. reflexivity.
  Qed.

  Corollary unnest_rhss_clocksof: forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      unnest_rhss es st = (es', eqs', st') ->
      clocksof es' = clocksof es.
  Proof.
    intros.
    eapply unnest_rhss_annots in H0; eauto.
    repeat rewrite clocksof_annots. congruence.
  Qed.

  (** ** nclockof is also preserved by unnest_exp *)

  Fact fby_iteexp_nclockof : forall e0 e ann es' eqs' st st',
      fby_iteexp e0 e ann st = (es', eqs', st') ->
      nclockof es' = [snd ann].
  Proof.
    intros e0 e [ty [cl name]] es' eqs' st st' Hfby; simpl in *.
    destruct (is_constant e0); repeat inv_bind; reflexivity.
  Qed.

  Fact unnest_merge_nclockof : forall ckid ets efs tys ck,
      length ets = length tys ->
      length efs = length tys ->
      Forall (fun e => nclockof e = [ck]) (unnest_merge ckid ets efs tys ck).
  Proof.
    intros * Hlen1 Hlen2.
    unfold unnest_merge. simpl_forall.
    eapply Forall3_forall3; split; eauto. congruence.
  Qed.

  Fact unnest_ite_nclockof : forall e ets efs tys ck,
      length ets = length tys ->
      length efs = length tys ->
      Forall (fun e => nclockof e = [ck]) (unnest_ite e ets efs tys ck).
  Proof.
    intros * Hlen1 Hlen2.
    unfold unnest_ite. simpl_forall.
    eapply Forall3_forall3; split; eauto. congruence.
  Qed.

  Fact unnest_exp_nclockof : forall G vars e is_control es' eqs' st st',
      wc_exp G vars e ->
      unnest_exp is_control e st = (es', eqs', st') ->
      nclocksof es' = nclockof e.
  Proof with eauto.
    intros.
    eapply unnest_exp_annot in H0; eauto.
    rewrite nclocksof_annots, H0, <- nclockof_annot. reflexivity.
  Qed.

  Fact map_bind2_unnest_exp_nclocksof : forall G vars es is_control es' eqs' st st',
      Forall (wc_exp G vars) es ->
      map_bind2 (unnest_exp is_control) es st = (es', eqs', st') ->
      nclocksof (concat es') = nclocksof es.
  Proof with eauto.
    intros.
    eapply map_bind2_unnest_exp_annots in H0; eauto.
    repeat rewrite nclocksof_annots. congruence.
  Qed.

  Fact unnest_exps_nclocksof : forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      unnest_exps es st = (es', eqs', st') ->
      nclocksof es' = nclocksof es.
  Proof with eauto.
    intros.
    eapply unnest_exps_annots in H0; eauto.
    repeat rewrite nclocksof_annots. congruence.
  Qed.

  Fact unnest_rhs_nclockof : forall G vars e es' eqs' st st',
      wc_exp G vars e ->
      unnest_rhs e st = (es', eqs', st') ->
      nclocksof es' = nclockof e.
  Proof with eauto.
    intros.
    eapply unnest_rhs_annot in H0; eauto.
    rewrite nclocksof_annots, H0, <- nclockof_annot. reflexivity.
  Qed.

  Fact unnest_rhss_nclocksof : forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      unnest_rhss es st = (es', eqs', st') ->
      nclocksof es' = nclocksof es.
  Proof with eauto.
    intros.
    eapply unnest_rhss_annots in H0; eauto.
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

  Fact map_bind2_wc {A B} :
    forall G vars (k : A -> Fresh (list exp * list equation) B) a es' eqs' st st',
      map_bind2 k a st = (es', eqs', st') ->
      (forall st st' a es eqs', k a st = (es, eqs', st') -> st_follows st st') ->
      Forall (fun a => forall es' eqs' st0 st0',
                  k a st0 = (es', eqs', st0') ->
                  st_follows st st0 ->
                  st_follows st0' st' ->
                  Forall (wc_exp G vars) es' /\
                  Forall (wc_equation G vars) eqs') a ->
      Forall (wc_exp G vars) (concat es') /\
      Forall (wc_equation G vars) (concat eqs').
  Proof with eauto.
    intros G vars k a.
    induction a; intros * Hmap Hfollows Hforall;
      repeat inv_bind; simpl.
    - repeat constructor.
    - inv Hforall.
      assert (H':=H). eapply H3 in H' as [Hwc1 Hwc1']... 2,3:repeat solve_st_follows.
      eapply IHa in H0 as [Hwc2 Hwc2']...
      2:{ solve_forall. eapply H2 in H4... etransitivity... }
      repeat rewrite Forall_app. repeat split; eauto.
  Qed.

  Fact unnest_fby_wc_exp : forall G vars e0s es anns,
      Forall (wc_exp G vars) e0s ->
      Forall (wc_exp G vars) es ->
      Forall unnamed_stream anns ->
      Forall2 (fun e0 a => clockof e0 = [a]) e0s (map clock_of_nclock anns) ->
      Forall2 (fun e a => clockof e = [a]) es (map clock_of_nclock anns) ->
      Forall (wc_exp G vars) (unnest_fby e0s es anns).
  Proof.
    intros * Hwc1 Hwc2 Hunnamed Hck1 Hck2.
    unfold unnest_fby.
    assert (length e0s = length anns) as Hlen1 by (eapply Forall2_length in Hck1; solve_length).
    assert (length es = length anns) as Hlen2 by (eapply Forall2_length in Hck2; solve_length).
    solve_forall.
    constructor; simpl; try rewrite app_nil_r; eauto.
  Qed.

  Fact unnest_arrow_wc_exp : forall G vars e0s es anns,
      Forall (wc_exp G vars) e0s ->
      Forall (wc_exp G vars) es ->
      Forall unnamed_stream anns ->
      Forall2 (fun e0 a => clockof e0 = [a]) e0s (map clock_of_nclock anns) ->
      Forall2 (fun e a => clockof e = [a]) es (map clock_of_nclock anns) ->
      Forall (wc_exp G vars) (unnest_arrow e0s es anns).
  Proof.
    intros * Hwc1 Hwc2 Hunnamed Hck1 Hck2.
    unfold unnest_arrow.
    assert (length e0s = length anns) as Hlen1 by (eapply Forall2_length in Hck1; solve_length).
    assert (length es = length anns) as Hlen2 by (eapply Forall2_length in Hck2; solve_length).
    solve_forall.
    constructor; simpl; try rewrite app_nil_r; eauto.
  Qed.

  Fact unnest_when_wc_exp : forall G vars ckid ck b es tys,
      length es = length tys ->
      In (ckid, ck) vars ->
      Forall (wc_exp G vars) es ->
      Forall (fun e => clockof e = [ck]) es ->
      Forall (wc_exp G vars) (unnest_when ckid b es tys (Con ck ckid b, None)).
  Proof.
    intros * Hlen Hin Hwc Hck. unfold unnest_when.
    solve_forall.
    repeat constructor; auto;
      simpl; rewrite app_nil_r, H1; auto.
  Qed.

  Fact unnest_merge_wc_exp : forall G vars ckid ck ets efs tys,
      length ets = length tys ->
      length efs = length tys ->
      In (ckid, ck) vars ->
      Forall (wc_exp G vars) ets ->
      Forall (wc_exp G vars) efs ->
      Forall (fun e => clockof e = [Con ck ckid true]) ets ->
      Forall (fun e => clockof e = [Con ck ckid false]) efs ->
      Forall (wc_exp G vars) (unnest_merge ckid ets efs tys (ck, None)).
  Proof.
    intros * Hlen1 Hlen2 Hin Hwc1 Hwc2 Hck1 Hck2. unfold unnest_merge.
    solve_forall.
    repeat constructor; auto;
      simpl; rewrite app_nil_r; try rewrite H2; try rewrite H3; auto.
  Qed.

  Fact unnest_ite_wc_exp : forall G vars ck e ets efs tys,
      length ets = length tys ->
      length efs = length tys ->
      wc_exp G vars e ->
      Forall (wc_exp G vars) ets ->
      Forall (wc_exp G vars) efs ->
      clockof e = [ck] ->
      Forall (fun e => clockof e = [ck]) ets ->
      Forall (fun e => clockof e = [ck]) efs ->
      Forall (wc_exp G vars) (unnest_ite e ets efs tys (ck, None)).
  Proof.
    intros * Hlen1 Hlen2 Hwc1 Hwc2 Hwc3 Hck1 Hck2 Hck3. unfold unnest_ite.
    solve_forall.
    repeat constructor; auto;
      simpl; rewrite app_nil_r; try rewrite H2; try rewrite H3; auto.
  Qed.

  Fact unnest_reset_wc : forall G vars e e' eqs' st st' ck,
      LiftO True (fun e => forall es' eqs' st',
                   unnest_exp true e st = (es', eqs', st') ->
                   Forall (wc_exp G (vars++st_clocks st')) es' /\
                   Forall (wc_equation G (vars++st_clocks st')) eqs') e ->
      LiftO True (wc_exp G (vars++st_clocks st)) e ->
      LiftO True (fun e => clockof e = [ck]) e ->
      unnest_reset (unnest_exp true) e st = (e', eqs', st') ->
      LiftO True (fun e' => clockof e' = [ck]) e' /\
      LiftO True (wc_exp G (vars++st_clocks st')) e' /\
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof.
    intros * Hkwc Hwc Hck Hunn.
    repeat split.
    - unnest_reset_spec; simpl in *; auto.
      1,2:assert (length l = 1) by
          (eapply unnest_exp_length in Hk0; eauto;
           rewrite <- length_clockof_numstreams, Hck in Hk0; auto).
      1,2:singleton_length.
      + eapply unnest_exp_clockof in Hk0; eauto.
        rewrite Hck in Hk0; auto.
      + eapply unnest_exp_clockof in Hk0; eauto.
        simpl in Hk0. rewrite app_nil_r, Hck in Hk0.
        rewrite clockof_annot in Hk0.
        destruct (annot e); inv Hk0. destruct l; inv H1.
        simpl in *; subst; auto.
    - unnest_reset_spec; simpl in *; auto.
      1,2:assert (Hk:=Hk0);eapply Hkwc in Hk0 as [Hwt1 Hwt2]; auto.
      + destruct l; simpl in H; [inv H|]; subst. 
        inv Hwt1; auto.
      + constructor.
        eapply fresh_ident_In in Hfresh.
      apply in_or_app; right.
      unfold st_clocks, idck. simpl_In.
      repeat eexists; eauto. split; auto.
    - destruct e; simpl in *; repeat inv_bind; auto.
      assert (length x = 1).
      { eapply unnest_exp_length in H; eauto.
        rewrite <- length_clockof_numstreams, Hck in H; auto. }
      singleton_length.
      assert (Hk:=H). apply unnest_exp_normalized_cexp, Forall_singl in H.
      eapply Hkwc in Hk as [Hwc1 Hwc2]; auto.
      inv H; [| | inv H1]; simpl in *.
      1-7:try destruct cl as [ck' ?]; repeat inv_bind.
      1-3,5-7:constructor.
      2,4,6,8,10,12,13:solve_forall; repeat solve_incl.
      1-6:inv Hwc1.
      1-6:repeat split; [constructor;[|constructor]| |]; repeat solve_incl.
      1-12:simpl; repeat constructor.
      2,4,5,7,9,11:
        (unfold clock_of_nclock, stripname; simpl;
         match goal with
         | H : fresh_ident _ _ = _ |- _ =>
           apply fresh_ident_In in H
         end;
         apply in_or_app, or_intror;
         unfold st_clocks, idck; simpl_In;
         repeat eexists; eauto; auto).
      + inv H4; simpl; auto.
      + inv H5; simpl; auto.
      + inv H3; simpl; auto.
      + inv H4; simpl; auto.
      + inv H3; simpl; auto.
  Qed.

  Hint Resolve nth_In.
  Fact unnest_exp_wc : forall G vars e is_control es' eqs' st st',
      wc_exp G (vars++st_clocks st) e ->
      unnest_exp is_control e st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) es' /\
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwc Hnorm;
      inv Hwc; simpl in Hnorm. 1-11: repeat inv_bind.
    - (* const *) repeat constructor.
    - (* var *)
      repeat constructor...
    - (* var (anon) *)
      repeat constructor...
    - (* unop *)
      assert (length x = numstreams e) as Hlen by eauto.
      rewrite <- length_clockof_numstreams, H3 in Hlen; simpl in Hlen.
      singleton_length.
      assert (Hnorm:=H); eapply IHe in H as [Hwc1 Hwc1']; eauto.
      repeat econstructor...
      + inv Hwc1; eauto.
      + eapply unnest_exp_clockof in Hnorm; simpl in Hnorm; eauto.
        rewrite app_nil_r, H3 in Hnorm...
    - (* binop *)
      repeat inv_bind.
      assert (length x = numstreams e1) as Hlen1 by eauto.
      rewrite <- length_clockof_numstreams, H5 in Hlen1; simpl in Hlen1.
      assert (length x2 = numstreams e2) as Hlen2 by eauto.
      rewrite <- length_clockof_numstreams, H6 in Hlen2; simpl in Hlen2. repeat singleton_length.
      assert (Hnorm1:=H); eapply IHe1 in H as [Hwc1 Hwc1']; eauto.
      assert (Hnorm2:=H0); eapply IHe2 in H0 as [Hwc2 Hwc2']; eauto. 2:repeat solve_incl.
      repeat econstructor...
      + inv Hwc1. repeat solve_incl.
      + inv Hwc2...
      + eapply unnest_exp_clockof in Hnorm1; simpl in Hnorm1; eauto.
        rewrite app_nil_r, H5 in Hnorm1...
      + eapply unnest_exp_clockof in Hnorm2; simpl in Hnorm2; eauto.
        rewrite app_nil_r, H6 in Hnorm2...
      + apply Forall_app; split; auto.
        solve_forall. repeat solve_incl.
    - (* fby *)
      Local Ltac solve_map_bind2 :=
        solve_forall;
        match goal with
        | Hnorm : unnest_exp _ _ _ = _, H : context [unnest_exp _ _ _ = _ -> _] |- _ =>
          eapply H in Hnorm as [? ?]; eauto;
          [split|]; try solve_forall; repeat solve_incl
        end.
      rewrite Forall2_eq in H6, H7.
      assert (length (concat x2) = length (annots e0s)) as Hlen1 by eauto.
      assert (length (concat x6) = length (annots es)) as Hlen2 by eauto.
      remember (unnest_fby _ _ _) as fby.
      assert (length (concat x2) = length a) as Hlen1'.
      { eapply map_bind2_unnest_exp_length in H1...
        repeat simpl_length. erewrite <- map_length, <- map_length. setoid_rewrite <- H6. apply map_length. }
      assert (length (concat x6) = length a) as Hlen2'.
      { eapply map_bind2_unnest_exp_length in H2...
        repeat simpl_length. erewrite <- map_length, <- map_length. setoid_rewrite <- H7. apply map_length. }
      assert (length a = length fby) as Hlen4.
      { repeat simpl_length.
        rewrite unnest_fby_length... }
      assert (length x5 = length fby) as Hlen3.
      { eapply idents_for_anns_length in H3. solve_length. }
      assert (H1':=H1). eapply map_bind2_wc with (G0:=G) (vars0:=vars++st_clocks x1) in H1' as [Hwc1 Hwc1']...
      2:solve_map_bind2.
      assert (H2':=H2). eapply map_bind2_wc with (G0:=G) (vars0:=vars++st_clocks x4) in H2' as [Hwc2 Hwc2']...
      2:solve_map_bind2.
      clear H H0.
      repeat rewrite Forall_app; repeat split.
      3,4:solve_forall; repeat solve_incl.
      + eapply idents_for_anns_wc...
      + assert (annots fby = a) as Hanns.
        { rewrite Heqfby, unnest_fby_annot... }
        assert (Forall (wc_exp G (vars++st_clocks st')) fby) as Hwcf.
        { rewrite Heqfby. eapply unnest_fby_wc_exp...
          1,2:solve_forall; repeat solve_incl.
          + eapply map_bind2_unnest_exp_clocksof'' in H1... congruence.
          + eapply map_bind2_unnest_exp_clocksof'' in H2... congruence. }
        assert (Forall2 (fun '(_, nck) e => nclockof e = [nck]) (map snd x5) fby) as Hcks.
        { eapply idents_for_anns_values in H3; subst.
          specialize (unnest_fby_annot' _ _ _ Hlen1' Hlen2') as Hanns'; eauto. clear - Hanns'.
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
    - (* arrow *)
      rewrite Forall2_eq in H6, H7.
      assert (length (concat x2) = length (annots e0s)) as Hlen1 by eauto.
      assert (length (concat x6) = length (annots es)) as Hlen2 by eauto.
      remember (unnest_arrow _ _ _) as fby.
      assert (length (concat x2) = length a) as Hlen1'.
      { eapply map_bind2_unnest_exp_length in H1...
        repeat simpl_length. erewrite <- map_length, <- map_length. setoid_rewrite <- H6. apply map_length. }
      assert (length (concat x6) = length a) as Hlen2'.
      { eapply map_bind2_unnest_exp_length in H2...
        repeat simpl_length. erewrite <- map_length, <- map_length. setoid_rewrite <- H7. apply map_length. }
      assert (length a = length fby) as Hlen4.
      { repeat simpl_length.
        rewrite unnest_arrow_length... }
      assert (length x5 = length fby) as Hlen3.
      { eapply idents_for_anns_length in H3. solve_length. }
      assert (H1':=H1). eapply map_bind2_wc with (G0:=G) (vars0:=vars++st_clocks x1) in H1' as [Hwc1 Hwc1']...
      2:solve_map_bind2.
      assert (H2':=H2). eapply map_bind2_wc with (G0:=G) (vars0:=vars++st_clocks x4) in H2' as [Hwc2 Hwc2']...
      2:solve_map_bind2.
      clear H H0.
      repeat rewrite Forall_app; repeat split.
      3,4:solve_forall; repeat solve_incl.
      + eapply idents_for_anns_wc...
      + assert (annots fby = a) as Hanns.
        { rewrite Heqfby, unnest_arrow_annot... }
        assert (Forall (wc_exp G (vars++st_clocks st')) fby) as Hwcf.
        { rewrite Heqfby. eapply unnest_arrow_wc_exp...
          1,2:solve_forall; repeat solve_incl.
          + eapply map_bind2_unnest_exp_clocksof'' in H1... congruence.
          + eapply map_bind2_unnest_exp_clocksof'' in H2... congruence. }
        assert (Forall2 (fun '(_, nck) e => nclockof e = [nck]) (map snd x5) fby) as Hcks.
        { eapply idents_for_anns_values in H3; subst.
          specialize (unnest_arrow_annot' _ _ _ Hlen1' Hlen2') as Hanns'; eauto. clear - Hanns'.
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
    - (* when *)
      assert (H0':=H0). eapply map_bind2_wc with (G0:=G) (vars0:=vars++st_clocks st') in H0' as [Hwc1 Hwc1']...
      2:solve_map_bind2.
      split; auto.
      apply unnest_when_wc_exp...
      + eapply map_bind2_unnest_exp_length in H0...
        solve_length.
      + assert (incl (vars ++ st_clocks st) (vars ++ st_clocks st')) as Hincl by repeat solve_incl...
      + eapply map_bind2_unnest_exp_clocksof''' in H0...
    - (* merge *)
      assert (length (concat x3) = length (annots ets)) as Hlen1 by eauto.
      assert (length (concat x6) = length (annots efs)) as Hlen2 by eauto.
      assert (st_follows x5 st') as Hfollows by (destruct is_control; repeat inv_bind; repeat solve_st_follows).
      assert (H1':=H1). eapply map_bind2_wc with (G0:=G) (vars0:=vars++st_clocks x2) in H1' as [Hwc1 Hwc1']...
      2:solve_map_bind2.
      assert (H2':=H2). eapply map_bind2_wc with (G0:=G) (vars0:=vars++st_clocks x5) in H2' as [Hwc2 Hwc2']...
      2:solve_map_bind2.
      clear H H0.
      assert (Forall (wc_exp G (vars++st_clocks st')) (unnest_merge x (concat x3) (concat x6) tys (ck, None))) as Hwcexp.
      { eapply unnest_merge_wc_exp...
        4,5:solve_forall; repeat solve_incl.
        + rewrite Hlen1, H10. solve_length.
        + rewrite Hlen2, H11. solve_length.
        + assert (incl (vars++st_clocks st) (vars++st_clocks st'))...
          destruct is_control; repeat inv_bind; repeat solve_incl.
        + eapply map_bind2_unnest_exp_clocksof''' in H1...
        + eapply map_bind2_unnest_exp_clocksof''' in H2... }
      destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split.
      1,2,3,6,7:solve_forall; repeat solve_incl.
      + eapply idents_for_anns_wc in H...
        solve_forall. unfold unnamed_stream; auto.
      + assert (Forall (fun e : exp => nclockof e = [(ck, None)]) (unnest_merge x (concat x3) (concat x6) tys (ck, None))) as Hnck.
        { eapply unnest_merge_nclockof; solve_length. }
        solve_forall. 2:(eapply idents_for_anns_length in H; solve_length).
        repeat split. 2,3:rewrite app_nil_r.
        * repeat constructor...
        * rewrite H4. repeat constructor.
        * rewrite clockof_nclockof, H4; simpl. repeat constructor.
          assert (H':=H). apply idents_for_anns_values in H'.
          apply idents_for_anns_incl_clocks in H.
          destruct a as [ty [ck' name']].
          apply in_or_app; right. apply H.
          simpl_In. exists (i, (ty, (ck', name'))). split; auto.
          assert (In (ty, (ck', name')) (map snd x0)) by (simpl_In; exists (i, (ty, (ck', name'))); auto).
          rewrite H' in H13. simpl_In. inv H13; auto.
    - (* ite *)
      assert (length x = 1). 2:singleton_length.
      { eapply unnest_exp_length in H1; eauto.
        rewrite <- length_clockof_numstreams, H8 in H1; auto. }
      assert (length (concat x5) = length (annots ets)) as Hlen1 by eauto.
      assert (length (concat x8) = length (annots efs)) as Hlen2 by eauto.
      assert (st_follows x7 st') as Hfollows by (destruct is_control; repeat inv_bind; repeat solve_st_follows).
      assert (H1':=H1). eapply IHe in H1' as [Hwc1 Hwc1']...
      assert (H2':=H2). eapply map_bind2_wc with (G0:=G) (vars0:=vars++st_clocks x4) in H2' as [Hwc2 Hwc2']...
      2:solve_map_bind2.
      assert (H3':=H3). eapply map_bind2_wc with (G0:=G) (vars0:=vars++st_clocks x7) in H3' as [Hwc3 Hwc3']...
      2:solve_map_bind2.
      clear H H0 IHe.
      assert (Forall (wc_exp G (vars++st_clocks st')) (unnest_ite e0 (concat x5) (concat x8) tys (ck, None))) as Hwcexp.
      { eapply unnest_ite_wc_exp...
        3:inv Hwc1; repeat solve_incl.
        3,4:solve_forall; repeat solve_incl.
        + rewrite Hlen1, H11. solve_length.
        + rewrite Hlen2, H12. solve_length.
        + eapply unnest_exp_clockof in H1...
          simpl in H1; rewrite app_nil_r in H1. congruence.
        + eapply map_bind2_unnest_exp_clocksof''' in H2...
        + eapply map_bind2_unnest_exp_clocksof''' in H3... }
      destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split.
      1,2,3,4,7,8,9:solve_forall;repeat solve_incl.
      + eapply idents_for_anns_wc in H...
        solve_forall. unfold unnamed_stream; auto.
      + assert (Forall (fun e : exp => nclockof e = [(ck, None)]) (unnest_ite e0 (concat x5) (concat x8) tys (ck, None))) as Hnck.
        { eapply unnest_ite_nclockof; solve_length. }
        solve_forall. 2:(eapply idents_for_anns_length in H; solve_length).
        repeat split. 2,3:rewrite app_nil_r.
        * repeat constructor...
        * rewrite H14. repeat constructor.
        * rewrite clockof_nclockof, H14; simpl. repeat constructor.
          assert (H':=H). apply idents_for_anns_values in H'.
          apply idents_for_anns_incl_clocks in H.
          destruct a as [ty [ck' name']].
          apply in_or_app; right. apply H.
          simpl_In. exists (i, (ty, (ck', name'))). split; auto.
          assert (In (ty, (ck', name')) (map snd x)) by (simpl_In; exists (i, (ty, (ck', name'))); auto).
          rewrite H' in H16. simpl_In. inv H16; auto.
    - (* app *)
      rewrite app_nil_r.
      assert (H1':=H1).
      eapply map_bind2_wc with (G0:=G) (vars0:=vars++st_clocks st') in H1' as [Hwc1 Hwc1']...
      2:solve_map_bind2.
      repeat constructor; simpl...
      + eapply idents_for_anns'_wc...
      + repeat econstructor; simpl...
        * erewrite map_bind2_unnest_exp_nclocksof...
        * erewrite idents_for_anns'_values...
      + rewrite app_nil_r, map_map, Forall2_map_1, Forall2_map_2, <- Forall2_same.
        eapply idents_for_anns'_clocknames...
      + unfold clock_of_nclock, stripname.
        rewrite app_nil_r, map_map, Forall2_map_1, Forall2_map_2, <- Forall2_same.
        eapply idents_for_anns'_incl_clocks in H2.
        apply Forall_forall; intros.
        apply in_or_app; right. apply H2.
        rewrite in_map_iff. exists x; split; auto. destruct x as [? [? [? ?]]]; auto.
    - (* app (reset) *)
      do 5 inv_bind.
      assert (st_follows x1 x4) as Hfollows.
      { eapply (unnest_reset_st_follows _ (Some r)) in H2; eauto. }
      assert (Hs:=H2). eapply unnest_reset_Some in Hs as [er' ?]; subst.
      eapply (unnest_reset_wc G vars (Some r)) in H2 as [Hwt2 [Hwt2' Hwt2'']]; simpl; eauto.
      2-3:clear H2. 1-3:repeat inv_bind.
      2:intros; eapply H in H2; eauto. 2,3:repeat solve_incl.
      assert (H1':=H1). eapply map_bind2_wc with (G0:=G) (vars0:=vars++st_clocks st') in H1' as [Hwc1 Hwc1']...
      2:solve_map_bind2.
      repeat econstructor; simpl...
      + eapply idents_for_anns'_wc...
      + eapply map_bind2_unnest_exp_nclocksof in H1; eauto.
        rewrite H1; eauto.
      + erewrite idents_for_anns'_values...
      + repeat solve_incl.
      + rewrite app_nil_r, map_map, Forall2_map_1, Forall2_map_2, <- Forall2_same.
        eapply idents_for_anns'_clocknames...
      + unfold clock_of_nclock, stripname.
        rewrite app_nil_r, map_map, Forall2_map_1, Forall2_map_2, <- Forall2_same.
        eapply idents_for_anns'_incl_clocks in H3.
        apply Forall_forall; intros.
        apply in_or_app; right. apply H3.
        rewrite in_map_iff. exists x; split; auto. destruct x as [? [? [? ?]]]; auto.
      + rewrite Forall_app; split; eauto.
        solve_forall; repeat solve_incl.
  Qed.

  Corollary map_bind2_unnest_exp_wc : forall G vars is_control es es' eqs' st st',
      Forall (wc_exp G (vars++st_clocks st)) es ->
      map_bind2 (unnest_exp is_control) es st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) (concat es') /\
      Forall (wc_equation G (vars++st_clocks st')) (concat eqs').
  Proof.
    intros * Hwt Hmap.
    eapply map_bind2_wc in Hmap; eauto.
    solve_forall. eapply unnest_exp_wc with (G:=G) (vars:=vars) in H1 as [? ?]; eauto.
    split. 1,2:solve_forall. 1,2,3:repeat solve_incl.
  Qed.

  Corollary unnest_exps_wc : forall G vars es es' eqs' st st',
      Forall (wc_exp G (vars++st_clocks st)) es ->
      unnest_exps es st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) es' /\
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof.
    intros * Hwt Hmap.
    unfold unnest_exps in Hmap; repeat inv_bind.
    eapply map_bind2_unnest_exp_wc in H; eauto.
  Qed.

  Fact unnest_rhs_wc : forall G vars e es' eqs' st st',
      wc_exp G (vars++st_clocks st) e ->
      unnest_rhs e st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) es' /\
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof with eauto.
    intros * Hwc Hnorm.
    destruct e; unfold unnest_rhs in Hnorm;
      try (solve [eapply unnest_exp_wc in Hnorm; eauto]); inv Hwc.
    - (* fby *)
      rewrite Forall2_eq in H4, H5.
      repeat inv_bind.
      assert (H':=H). eapply unnest_exps_wc in H' as [Hwc1 Hwc1']...
      assert (H0':=H0). eapply unnest_exps_wc with (G:=G) (vars:=vars) in H0' as [Hwc2 Hwc2']...
      2:solve_forall; repeat solve_incl.
      rewrite Forall_app; repeat split.
      2,3:solve_forall; repeat solve_incl.
      eapply unnest_fby_wc_exp...
      + solve_forall; repeat solve_incl.
      + unfold unnest_exps in H; repeat inv_bind.
        eapply map_bind2_unnest_exp_clocksof'' in H... congruence.
      + unfold unnest_exps in H0; repeat inv_bind.
        eapply map_bind2_unnest_exp_clocksof'' in H0... congruence.
    - (* arrow *)
      rewrite Forall2_eq in H4, H5.
      repeat inv_bind.
      assert (H':=H). eapply unnest_exps_wc in H' as [Hwc1 Hwc1']...
      assert (H0':=H0). eapply unnest_exps_wc with (G:=G) (vars:=vars) in H0' as [Hwc2 Hwc2']...
      2:solve_forall; repeat solve_incl.
      rewrite Forall_app; repeat split.
      2,3:solve_forall; repeat solve_incl.
      eapply unnest_arrow_wc_exp...
      + solve_forall; repeat solve_incl.
      + unfold unnest_exps in H; repeat inv_bind.
        eapply map_bind2_unnest_exp_clocksof'' in H... congruence.
      + unfold unnest_exps in H0; repeat inv_bind.
        eapply map_bind2_unnest_exp_clocksof'' in H0... congruence.
    - (* app *)
      repeat inv_bind. rewrite app_nil_r.
      assert (H':=H). eapply unnest_exps_wc in H' as [Hwc1 Hwc1']...
      repeat constructor...
      econstructor...
      eapply unnest_exps_nclocksof in H... congruence.
    - (* app (reset) *)
      do 4 inv_bind.
      assert (H':=H). eapply unnest_exps_wc in H' as [Hwc1 Hwc1']...
      assert (Hs:=H0). eapply unnest_reset_Some in Hs as [er' ?]; subst.
      assert (st_follows x1 st') as Hfollows.
      { eapply (unnest_reset_st_follows _ (Some r)) in H0; eauto. }
      eapply (unnest_reset_wc G vars (Some r)) in H0 as [Hwc2 [Hwc2' Hwc2'']]; simpl in *; eauto.
      2:intros; eapply unnest_exp_wc in H1; eauto. 2,3:repeat solve_incl.
      repeat rewrite Forall_app; repeat split; repeat constructor.
      2,3:solve_forall; repeat solve_incl.
      econstructor...
      * solve_forall; repeat solve_incl.
      * eapply unnest_exps_nclocksof in H... congruence.
  Qed.

  Corollary unnest_rhss_wc : forall G vars es es' eqs' st st',
      Forall (wc_exp G (vars++st_clocks st)) es ->
      unnest_rhss es st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) es' /\
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof.
    intros * Hwc Hnorm.
    unfold unnest_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_wc in H; eauto.
    solve_forall.
    eapply unnest_rhs_wc with (G:=G) (vars:=vars) in H2 as [? ?]; eauto.
    split. 1,2:solve_forall. 1,2,3:repeat solve_incl.
  Qed.

  Fact unnest_equation_wc_eq : forall G vars e eqs' st st',
      wc_equation G (vars++st_clocks st) e ->
      unnest_equation e st = (eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof with eauto.
    intros G vars [xs es] eqs' st st' Hwc Hnorm.
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
    induction x; intros; simpl in *; constructor.
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

  Corollary unnest_equations_wc_eq : forall G vars eqs eqs' st st',
      Forall (wc_equation G (vars++st_clocks st)) eqs ->
      unnest_equations eqs st = (eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof with eauto.
    induction eqs; intros * Hwc Hnorm;
      unfold unnest_equations in *; simpl in *; repeat inv_bind...
    assert (st_follows st x1) as Hfollows1 by repeat solve_st_follows.
    assert (st_follows x1 st') as Hfollows2 by repeat solve_st_follows.
    inv Hwc. eapply unnest_equation_wc_eq in H...
    assert (unnest_equations eqs x1 = (concat x2, st')) as Hnorm.
      { unfold unnest_equations; repeat inv_bind. repeat eexists; eauto. inv_bind; eauto. }
    apply IHeqs in Hnorm... 2:solve_forall; repeat solve_incl.
    apply Forall_app; split...
    solve_forall; repeat solve_incl.
  Qed.

  (** *** The produced environment is also well-clocked *)

  Fact unnest_reset_wc_env : forall G vars e e' eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      LiftO True (fun e => forall es' eqs' st',
                   unnest_exp true e st = (es', eqs', st') ->
                   wc_env (vars++st_clocks st')) e ->
      LiftO True (wc_exp G (vars ++ st_clocks st)) e ->
      unnest_reset (unnest_exp true) e st = (e', eqs', st') ->
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros * HwcG Hwenv Hun Hwc Hnorm.
    unnest_reset_spec; simpl in *; eauto.
    eapply fresh_ident_wc_env in Hfresh; eauto.
    assert (Hwc' := Hk0). eapply unnest_exp_wc in Hwc' as [Hwc' _]; eauto.
    eapply wc_exp_clocksof in Hwc'; eauto.
    eapply unnest_exp_no_fresh in Hk0.
    rewrite Hk0 in Hwc'; simpl in Hwc'; rewrite app_nil_r in Hwc'.
    destruct l; simpl in *; inv Hhd. constructor.
    apply Forall_app in Hwc' as [Hwc' _].
    rewrite clockof_annot in Hwc'.
    destruct (annot e); simpl in *. inv H0; constructor.
    inv Hwc'; auto.
  Qed.

  Fact map_bind2_wc_env {A A1 A2 : Type} :
    forall vars (k : A -> Unnesting.FreshAnn (A1 * A2)) a a1s a2s st st',
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

  Fact unnest_exp_wc_env : forall G vars e is_control es' eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      wc_exp G (vars++st_clocks st) e ->
      unnest_exp is_control e st = (es', eqs', st') ->
      wc_env (vars++st_clocks st').
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' HwG Hwenv Hwc Hnorm;
      assert (Hnorm':=Hnorm); apply unnest_exp_fresh_incl in Hnorm';
      simpl in *;
      assert (Hwc':=Hwc); inv Hwc'. 1-11:repeat inv_bind...
    - (* binop *)
      assert (st_follows st x1) as Hfollows by eauto.
      eapply IHe1 in H...
      eapply IHe2 in H0...
      repeat solve_incl.
    - (* fby *)
      Local Ltac solve_map_bind2' :=
        solve_forall;
        match goal with
        | Hnorm : unnest_exp _ _ _ = _, H : context [unnest_exp _ _ _ = _ -> _] |- _ =>
          eapply H in Hnorm; eauto; repeat solve_incl
        end.
      rewrite Forall2_eq in H6, H7.
      assert (Hwenv1:=H1). eapply map_bind2_wc_env in Hwenv1... 2:solve_map_bind2'.
      assert (Hwenv2:=H2). eapply map_bind2_wc_env in Hwenv2... 2:solve_map_bind2'.
      eapply idents_for_anns_wc_env in H3...
      assert (Forall (wc_clock ((vars ++ st_clocks x1))) (map clock_of_nclock a)).
        { rewrite H6.
          eapply wc_exp_clocksof in H4... eapply Forall_impl; [|eauto]. intros.
          eapply wc_clock_incl; [|eauto]. rewrite <- app_assoc in *.
          apply incl_appr', incl_app; repeat solve_incl.
          apply map_bind2_unnest_exp_fresh_incl in H1...
          unfold st_clocks. apply incl_map, H1. }
        solve_forall; repeat solve_incl.
    - (* arrow *)
      rewrite Forall2_eq in H6, H7.
      assert (Hwenv1:=H1). eapply map_bind2_wc_env in Hwenv1... 2:solve_map_bind2'.
      assert (Hwenv2:=H2). eapply map_bind2_wc_env in Hwenv2... 2:solve_map_bind2'.
      eapply idents_for_anns_wc_env in H3...
      assert (Forall (wc_clock ((vars ++ st_clocks x1))) (map clock_of_nclock a)).
        { rewrite H6.
          eapply wc_exp_clocksof in H4... eapply Forall_impl; [|eauto]. intros.
          eapply wc_clock_incl; [|eauto]. rewrite <- app_assoc in *.
          apply incl_appr', incl_app; repeat solve_incl.
          apply map_bind2_unnest_exp_fresh_incl in H1...
          unfold st_clocks. apply incl_map, H1. }
        solve_forall; repeat solve_incl.
    - (* when *)
      eapply map_bind2_wc_env in H0... solve_map_bind2'.
    - (* merge *)
      assert (Hwenv1:=H1). eapply map_bind2_wc_env in Hwenv1... 2:solve_map_bind2'.
      assert (Hwenv2:=H2). eapply map_bind2_wc_env in Hwenv2... 2:solve_map_bind2'.
      destruct is_control; repeat inv_bind...
      eapply idents_for_anns_wc_env in H3...
      repeat rewrite Forall_map.
      rewrite Forall_forall. intros ty _; simpl.
      unfold wc_env in Hwenv; rewrite Forall_forall in Hwenv; eapply Hwenv in H7; simpl in H7.
      repeat solve_incl.
    - (* ite *)
      assert (Hwenv1:=H1). eapply IHe in Hwenv1...
      assert (Hwenv2:=H2). eapply map_bind2_wc_env in Hwenv2... 2:solve_map_bind2'.
      assert (Hwenv3:=H3). eapply map_bind2_wc_env in Hwenv3... 2:solve_map_bind2'.
      destruct is_control; repeat inv_bind...
      eapply idents_for_anns_wc_env in H4...
      repeat rewrite Forall_map.
      rewrite Forall_forall. intros ty _; simpl.
      eapply wc_exp_clockof in H5... rewrite H8 in H5. inv H5.
      solve_incl. rewrite <- app_assoc. apply incl_appr', incl_app; [repeat solve_incl|].
      unfold st_clocks. apply incl_map.
      eapply unnest_exp_fresh_incl in H1. etransitivity...
      apply st_follows_incl. repeat solve_st_follows.
    - (* app *)
      assert (Hwenv1:=H1). eapply map_bind2_wc_env in Hwenv1... 2:solve_map_bind2'.
      eapply idents_for_anns'_wc_env...
      apply wc_exp_clockof in Hwc... simpl in Hwc.
      unfold clock_of_nclock, stripname in Hwc.
      rewrite map_map. eapply Forall_impl; [|eauto].
      intros. rewrite <- app_assoc in H3. repeat solve_incl.
      apply incl_app; [repeat solve_incl|].
        unfold st_clocks. apply incl_map...
    - (* app (reset) *)
      do 5 inv_bind.
      assert (st_follows x1 x4) as Hfollows.
      { eapply (unnest_reset_st_follows _ (Some r)) in H2; eauto. }
      eapply idents_for_anns'_wc_env in H3...
      + assert (Hs:=H2). eapply unnest_reset_Some in Hs as [er' ?]; subst.
        eapply (unnest_reset_wc_env _ _ (Some r)) in H2; simpl in *; eauto.
        1-3:clear H2; repeat inv_bind.
        2:intros; eapply H in H2; eauto.
        3,4:repeat solve_incl.
        1,2:eapply map_bind2_wc_env in H1... 1,2:solve_map_bind2'.
      + clear H2; repeat inv_bind.
        apply wc_exp_clockof in Hwc... simpl in Hwc.
        unfold clock_of_nclock, stripname in Hwc.
        rewrite map_map. eapply Forall_impl; [|eauto].
        intros. rewrite <- app_assoc in H2. repeat solve_incl.
        apply incl_app; [repeat solve_incl|].
        unfold st_clocks. apply incl_map...
  Qed.

  Corollary map_bind2_unnest_exp_wc_env : forall G vars es is_control es' eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      Forall (wc_exp G (vars++st_clocks st)) es ->
      map_bind2 (unnest_exp is_control) es st = (es', eqs', st') ->
      wc_env (vars++st_clocks st').
  Proof.
    intros.
    eapply map_bind2_wc_env in H2; eauto.
    rewrite Forall_forall in *; intros.
    eapply unnest_exp_wc_env in H5; eauto.
    eapply H1 in H3. repeat solve_incl.
  Qed.

  Corollary unnest_exps_wc_env : forall G vars es es' eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      Forall (wc_exp G (vars++st_clocks st)) es ->
      unnest_exps es st = (es', eqs', st') ->
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros * HwG Hwenv Hwc Hnorm.
    unfold unnest_exps in Hnorm; repeat inv_bind.
    eapply map_bind2_wc_env in H...
    solve_forall.
    eapply unnest_exp_wc_env in H3...
    repeat solve_incl.
  Qed.

  Fact unnest_rhs_wc_env : forall G vars e es' eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      wc_exp G (vars++st_clocks st) e ->
      unnest_rhs e st = (es', eqs', st') ->
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros * HwG Hwenv Hwc Hnorm.
    destruct e; unfold unnest_rhs in Hnorm;
      try (solve [eapply unnest_exp_wc_env in Hnorm; eauto]);
      inv Hwc. 1-3:repeat inv_bind.
    - (* fby *)
      assert (Hwenv1:=H). eapply unnest_exps_wc_env in Hwenv1...
      assert (Hwenv2:=H0). eapply unnest_exps_wc_env in Hwenv2...
      solve_forall; repeat solve_incl.
    - (* arrow *)
      assert (Hwenv1:=H). eapply unnest_exps_wc_env in Hwenv1...
      assert (Hwenv2:=H0). eapply unnest_exps_wc_env in Hwenv2...
      solve_forall; repeat solve_incl.
    - (* app *)
      eapply unnest_exps_wc_env in H...
    - (* app (reset) *)
      do 4 inv_bind.
      eapply (unnest_reset_wc_env G vars (Some r)) in H0; simpl; eauto.
      2:intros; eapply unnest_exp_wc_env in H1; eauto.
      3,4:repeat solve_incl.
      1,2:eapply unnest_exps_wc_env in H; eauto.
  Qed.

  Corollary unnest_rhss_wc_env : forall G vars es es' eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      Forall (wc_exp G (vars++st_clocks st)) es ->
      unnest_rhss es st = (es', eqs', st') ->
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros * HwG Hwenv Hwc Hnorm.
    unfold unnest_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_wc_env in H...
    solve_forall.
    eapply unnest_rhs_wc_env in H3...
    repeat solve_incl.
  Qed.

  Fact unnest_equation_wc_env : forall G vars e eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      wc_equation G (vars++st_clocks st) e ->
      unnest_equation e st = (eqs', st') ->
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros G vars [xs es] * HwG Hwenv [Hwc _] Hnorm.
    unfold unnest_equation in Hnorm. repeat inv_bind.
    eapply unnest_rhss_wc_env in H...
  Qed.

  Corollary unnest_equations_wc_env : forall G vars eqs eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      Forall (wc_equation G (vars++st_clocks st)) eqs ->
      unnest_equations eqs st = (eqs', st') ->
      wc_env (vars++st_clocks st').
  Proof with eauto.
    induction eqs; intros * HwG Hwenv Hwc Hnorm;
      unfold unnest_equations in *; simpl in *; repeat inv_bind...
    assert (st_follows st x1) as Hfollows1 by repeat solve_st_follows.
    inv Hwc. eapply unnest_equation_wc_env in H...
    assert (unnest_equations eqs x1 = (concat x2, st')) as Hnorm.
      { unfold unnest_equations; repeat inv_bind. repeat eexists; eauto. inv_bind; eauto. }
    apply IHeqs in Hnorm as Hwenv2... solve_forall; repeat solve_incl.
  Qed.

  Lemma unnest_node_wc : forall G n Hwl,
      wc_global G ->
      wc_node G n ->
      wc_node G (unnest_node n Hwl).
  Proof with eauto.
    intros * HwG [Hin [Hout [Henv Heq]]].
    unfold unnest_node.
    repeat constructor; simpl; auto.
    - remember (unnest_equations _ _) as res. symmetry in Heqres.
      destruct res as [eqs' st']; simpl.
      unfold idck. repeat rewrite map_app.
      eapply unnest_equations_wc_env in Heqres as Henv'...
      2,3:unfold st_clocks; rewrite init_st_anns, app_nil_r...
      2:rewrite (Permutation_app_comm (n_vars _)) in Heq...
      unfold idck in Henv'; repeat rewrite map_app in Henv'; repeat rewrite <- app_assoc in Henv'...
    - remember (unnest_equations _ _) as res. symmetry in Heqres.
      destruct res as [eqs' st']; simpl.
      unfold idck. repeat rewrite map_app.
      eapply unnest_equations_wc_eq in Heqres as Hwc'...
      2:unfold st_clocks; rewrite init_st_anns, app_nil_r...
      unfold st_clocks, idck in Hwc'; repeat rewrite map_app in Hwc'; repeat rewrite <- app_assoc in *.
      solve_forall; solve_incl.
      apply incl_appr', incl_appr'.
      rewrite Permutation_app_comm. reflexivity.
  Qed.

  Lemma unnest_global_wc : forall G Hwl,
      wc_global G ->
      wc_global (unnest_global G Hwl).
  Proof.
    induction G; intros * Hwc; simpl; inv Hwc.
    - constructor.
    - constructor.
      + eapply IHG; eauto.
      + eapply unnest_node_wc; eauto.
        eapply iface_eq_wc_node; eauto.
        eapply unnest_global_eq.
      + eapply unnest_global_names; eauto.
  Qed.

  (** ** Preservation of clocking through second pass *)

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
    assert (st_follows st st') as Hfollows.
    { eapply (fby_iteexp_st_follows _ _ (ty, (ck, None))) in Hfby; eauto. }
    repeat inv_bind; repeat econstructor; simpl...
    4,5:rewrite app_nil_r; unfold clock_of_nclock, stripname; simpl.
    4-5:rewrite Hck1; repeat constructor.
    2:repeat solve_incl.
    1-2:(apply in_or_app, or_intror; unfold st_clocks', idty, idck; rewrite map_map).
    (apply init_var_for_clock_In in H; simpl in *;
     eapply st_follows_incl in H; eauto;
     simpl_In; eexists; split; eauto; eauto).
    (simpl_In; exists (x2, (ty, ck, false)); simpl; split; auto;
     eapply fresh_ident_In in H0; eauto).
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
    intros vars e0 e ty [ck name] es' eqs' st st' Hwenv Hwc Hfby.
    unfold fby_iteexp in Hfby; repeat inv_bind...
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
    repeat inv_bind; repeat constructor; simpl...
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
      unnested_equation eq ->
      wc_env (vars++st_clocks' st) ->
      wc_equation G (vars++st_clocks' st) eq ->
      fby_equation to_cut eq st = (eqs', st') ->
      (Forall (wc_equation G (vars++st_clocks' st')) eqs' /\ wc_env (vars++st_clocks' st')).
  Proof with eauto.
    intros * Hunt Hwenv Hwc Hfby.
    inv_fby_equation Hfby to_cut eq; destruct x2 as (ty&ck&name).
    - (* fby (constant) *)
      destruct PS.mem; repeat inv_bind; auto.
      destruct Hwc as (Hwc&Hn&Hins).
      apply Forall_singl in Hwc. apply Forall2_singl in Hn. apply Forall2_singl in Hins.
      assert (Hwc':=Hwc). inv Hwc'.
      simpl in *; rewrite app_nil_r in *.
      apply Forall_singl in H3; apply Forall_singl in H4.
      apply Forall_singl in H7; inv H7; simpl in H0; subst.
      assert (wc_clock (vars ++ st_clocks' st) ck).
      { eapply wc_env_var; eauto. }
      eapply wc_exp_incl with (vars':=vars ++ st_clocks' st') in Hwc; repeat solve_incl.
      repeat (econstructor; eauto).
      + eapply fresh_ident_In in H.
        eapply in_or_app, or_intror. unfold st_clocks', idck, idty.
        simpl_In. exists (x2, (ty, ck)); split; auto.
        simpl_In. eexists; split; eauto. auto.
      + assert (incl (vars++st_clocks' st) (vars++st_clocks' st')); eauto. repeat solve_incl.
      + eapply fresh_ident_In in H.
        eapply in_or_app, or_intror. unfold st_clocks', idck, idty.
        simpl_In. exists (x2, (ty, ck)); split; auto.
        simpl_In. eexists; split; eauto. auto.
      + eapply fresh_ident_wc_env' in H; eauto.
    - (* fby *)
      assert (st_follows st st') as Hfollows by eauto.
      destruct Hwc as [Hwc [Hn Hins]].
      apply Forall_singl in Hwc. apply Forall2_singl in Hn. apply Forall2_singl in Hins.
      inv Hwc.
      simpl in *; rewrite app_nil_r in *.
      apply Forall_singl in H3; apply Forall_singl in H4.
      apply Forall_singl in H7; inv H7. simpl in H0; subst.
      rewrite Forall2_eq in H5, H6.
      assert (Hwce:=H). eapply fby_iteexp_wc_exp in Hwce; eauto. 2:constructor.
      assert (Hck:=H). eapply (fby_iteexp_nclockof _ _ (ty, (ck, None))) in Hck; eauto.
      assert (Hwceq:=H). eapply fby_iteexp_wc_eq in Hwceq; eauto.
      2:(clear - Hunt; inv Hunt; eauto; inv H0; inv H). 2:constructor; auto.
      assert (wc_clock (vars ++ st_clocks' st) ck).
      { eapply wc_env_var; eauto. }
      eapply (fby_iteexp_wc_env _ _ _ ty (ck, None)) in H...
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
      apply Forall_singl in H3; apply Forall_singl in H4.
      apply Forall_singl in H7; inv H7.
      rewrite Forall2_eq in H5, H6.
      assert (wc_clock (vars ++ st_clocks' st) ck).
      { eapply wc_env_var; eauto. }
      assert (Hwce:=H). eapply init_var_for_clock_wc_env in Hwce; eauto.
      split; eauto.
      assert (st_follows st st') as Hfollows.
      { eapply init_var_for_clock_st_follows; eauto. }
      simpl in *; inv H0.
      repeat econstructor; auto.
      2,3,4,7:repeat solve_incl.
      2,3,4,5:simpl; rewrite app_nil_r; try rewrite <- H5; try rewrite <- H6; auto.
      + eapply init_var_for_clock_In in H.
        apply in_or_app, or_intror. unfold st_clocks', idck, idty. rewrite map_map.
        repeat simpl_In. exists (x2, (Op.bool_type, ck, true)); auto.
      + assert (incl (vars++st_clocks' st) (vars++st_clocks' st')) by repeat solve_incl; auto.
      + eapply init_var_for_clock_wc_eq in H; eauto.
  Qed.

  Fact fby_equations_wc_eq : forall G vars to_cut eqs eqs' st st',
      Forall unnested_equation eqs ->
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

  Lemma normalize_global_wc : forall (G : global_wl) G',
      wc_global G ->
      normalize_global G = Errors.OK G' ->
      wc_global G'.
  Proof.
    intros [G Hwl] * Hwc Hnorm.
    unfold normalize_global in Hnorm. destruct (Caus.check_causality _); inv Hnorm.
    eapply normfby_global_wc, unnest_global_wc, Hwc.
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
