From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams Clocks.
From Coq Require Import List. Import List.ListNotations. Open Scope list_scope.
Require Import Omega.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LClocking.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization Lustre.Normalization.FullNorm.

(** * Preservation of Typing through Normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type NCLOCKING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Clo : LCLOCKING Ids Op Syn)
       (Import Norm : FULLNORM Ids Op OpAux Syn).
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
    destruct (Norm.is_constant e0); repeat inv_bind; reflexivity.
  Qed.

  Fact normalize_fby_clockof : forall anns e0s es es' eqs' st st',
      length e0s = length anns ->
      length es = length anns ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      clocksof es' = List.map fst (List.map snd anns).
  Proof.
    intros anns e0s es es' eqs' st st' Hlen1 Hlen2 Hnorm.
    eapply normalize_fby_annot in Hnorm; eauto.
    rewrite clocksof_annots, Hnorm.
    unfold without_names. repeat rewrite map_map.
    apply map_ext. intros [? [? ?]]; auto.
  Qed.

  Fact normalize_rhs_clockof: forall G vars e keep_fby es' eqs' st st',
      wc_exp G vars e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      clocksof es' = clockof e.
  Proof.
    intros G vars e keep_fby es' eqs' st st' Hwc Hnorm.
    eapply normalize_rhs_annot in Hnorm; eauto.
    rewrite clocksof_annots, Hnorm, <- clockof_annot. reflexivity.
  Qed.

  Corollary normalize_rhss_clocksof: forall G vars es keep_fby es' eqs' st st',
      Forall (wc_exp G vars) es ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      clocksof es' = clocksof es.
  Proof.
    intros.
    eapply normalize_rhss_annots in H0; eauto.
    repeat rewrite clocksof_annots. congruence.
  Qed.

  (** ** nclockof is also preserved by normalize_exp *)

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

  Fact normalize_rhs_nclockof : forall G vars e keep_fby es' eqs' st st',
      wc_exp G vars e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      nclocksof es' = nclockof e.
  Proof with eauto.
    intros.
    eapply normalize_rhs_annot in H0; eauto.
    rewrite nclocksof_annots, H0, <- nclockof_annot. reflexivity.
  Qed.

  Fact normalize_rhss_nclocksof : forall G vars es keep_fby es' eqs' st st',
      Forall (wc_exp G vars) es ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      nclocksof es' = nclocksof es.
  Proof with eauto.
    intros.
    eapply normalize_rhss_annots in H0; eauto.
    rewrite nclocksof_annots, H0, <- nclocksof_annots. reflexivity.
  Qed.

  (** ** A few additional things *)

  Definition st_clocks (st : fresh_st ((Op.type * clock) * bool)) :=
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
    assert (In (id, (t, cl)) (idty (st_anns st'))).
    { eapply Hids. repeat simpl_In. exists (id, (t, (cl, o))); auto. }
    In_st_clocks id t cl b. inv H; auto.
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
    assert (In (id, (t, cl)) (idty (st_anns st'))).
    { eapply Hids. repeat simpl_In. exists (id, (t, (cl, o))); auto. }
    In_st_clocks id t cl b. inv H; auto.
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
    | H : incl ?l1 ?l2 |- incl (idty ?l1) (idty ?l2) =>
      eapply incl_map; eauto
    end; auto.

  (** ** Auxilary lemmas for perservation of wc_env *)

  Import Permutation.

  Fact fresh_ident_wc_env : forall vars ty ck b id st st',
      wc_env (vars++st_clocks st) ->
      wc_clock (vars++st_clocks st) ck ->
      fresh_ident ((ty, ck), b) st = (id, st') ->
      wc_env (vars++st_clocks st').
  Proof.
    intros vars ty ck b id st st' Hwenv Hwc Hfresh.
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

  Fact reuse_ident_wc_env : forall vars ty ck b id st st',
      wc_env (vars++st_clocks st) ->
      wc_clock (vars++st_clocks st') ck ->
      reuse_ident id ((ty, ck), b) st = (tt, st') ->
      wc_env (vars++st_clocks st').
  Proof.
    intros vars ty ck b id st st' Hwenv Hwc Hfresh.
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
      Permutation (idty (st_anns st')) (map (fun '(id, (ty, (cl, _))) => (id, (ty, cl))) ids++idty (st_anns st)).
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
      replace (map (fun x => (fst x, snd (fst (snd x)))) (st_anns st'))
                 with (idck (map (fun x => (fst x, fst (snd x))) (st_anns st'))).
      2:{ unfold idck. rewrite map_map. eapply map_ext. intros [id' [ty' cl']]... }
      rewrite Hids. unfold idck. rewrite map_app, map_map, map_map.
      eapply incl_appr', incl_refl.
    - eapply Forall_impl... intros; simpl in *. repeat solve_incl.
  Qed.

  Fact init_var_for_clock_wc_env : forall vars cl id eqs' st st',
      wc_env (vars++st_clocks st) ->
      wc_clock (vars++st_clocks st) cl ->
      init_var_for_clock cl st = (id, eqs', st') ->
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros vars cl id eqs' st st' Hwenv Hwc Hinit.
    unfold init_var_for_clock in Hinit.
    destruct find.
    - destruct p. inv Hinit...
    - destruct fresh_ident eqn:Hfresh. inv Hinit.
      eapply fresh_ident_wc_env in Hfresh...
  Qed.

  Fact fby_iteexp_wc_env : forall vars e0 e ty cl es' eqs' st st',
      wc_env (vars++st_clocks st) ->
      wc_clock (vars++st_clocks st) (fst cl) ->
      fby_iteexp e0 e (ty, cl) st = (es', eqs', st') ->
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros vars e0 e ty [cl name] es' eqs' st st' Hwenv Hwc Hfby.
    unfold fby_iteexp in Hfby.
    destruct (Norm.is_constant e0); repeat inv_bind...
    eapply fresh_ident_wc_env in H0... 2:repeat solve_incl.
    eapply init_var_for_clock_wc_env in H...
  Qed.

  Fact map_bind2_wc_env {A A1 A2 : Type} :
    forall vars (k : A -> FreshAnn (A1 * A2)) a a1s a2s st st',
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
      eapply H1 in H2...
      etransitivity...
  Qed.

  Fact normalize_fby_wc_env : forall vars e0s es anns es' eqs' st st',
      wc_env (vars++st_clocks st) ->
      Forall (fun '(_, (cl, _)) => wc_clock (vars++st_clocks st) cl) anns ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros vars e0s es anns es' eqs' st st' Hwenv Hwc Hnorm.
    unfold normalize_fby in Hnorm; repeat inv_bind.
    eapply map_bind2_wc_env in H...
    - intros ? ? [[e0 e] ann] ? ? Hfby. repeat solve_st_follows.
    - clear H.
      eapply Forall_forall; intros [[e0 e] [ty [cl name]]] ? ? ? ? ? Hwc' Hfby Hfollows1 Hfollows2.
      eapply fby_iteexp_wc_env in Hfby... simpl.
      repeat simpl_In. rewrite Forall_forall in Hwc. eapply Hwc in H. repeat solve_incl.
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

  (** ** Preservation of wc *)

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
      eapply idents_for_anns_wc in H9...
    - (* when *)
      rewrite Forall_map. eapply Forall2_combine'.
      assert (length (concat x1) = length (annots es)) as Hlength by eauto.
      assert (clocksof (concat x1) = clocksof es) as Hclockof by eauto.
      rewrite clocksof_annots in H7.
      specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H0) as Hnumstreams.
      repeat rewrite_Forall_forall; solve_length.
      repeat constructor; simpl.
      + eapply map_bind2_wc_exp in H0...
        * rewrite Forall_forall in H0. eapply H0... eapply nth_In; solve_length.
        * rewrite Forall_forall; intros...
          eapply H in H3...
          solve_forall; repeat solve_incl.
          eapply H4 in H2. repeat solve_incl.
      + eapply in_app_or in H5.
        eapply in_or_app. destruct H5... right.
        assert (incl (st_clocks st) (st_clocks st')) by repeat solve_incl...
      + rewrite app_nil_r.
        rewrite Forall_forall; intros.
        eapply H6. rewrite <- Hclockof.
        repeat simpl_nth; repeat simpl_length.
        assert (length (clockof (nth n (concat x1) a)) = 1).
        { rewrite <- Hlength in H1. eapply nth_In in H1. eapply Hnumstreams in H1.
          rewrite length_clockof_numstreams... }
        repeat singleton_length. destruct x3; try omega; subst.
        rewrite concat_length_map_nth with (db:=x0) in Hsingl; solve_length. inv Hsingl.
        2: (solve_forall; rewrite length_clockof_numstreams; eauto).
        rewrite <- clocksof_annots. repeat simpl_list.
        apply nth_In. rewrite <- Hlength in H1.
        rewrite concat_length_1...
        solve_forall; rewrite length_clockof_numstreams...
      + rewrite app_nil_r. rewrite <- Hlength in H1.
        eapply nth_In in H1. eapply Hnumstreams in H1.
        rewrite length_clockof_numstreams...
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + (* control *)
        rewrite Forall_map. eapply Forall2_combine'.
        assert (length (concat x3) = length (annots ets)) as Hlen1 by (eapply map_bind2_normalize_exp_length; eauto).
        assert (length (concat x6) = length (annots efs)) as Hlen2 by (eapply map_bind2_normalize_exp_length; eauto).
        replace (clocksof ets) with (clocksof (concat x3)) in H8 by (eapply map_bind2_normalize_exp_clocksof; eauto).
        replace (clocksof efs) with  (clocksof (concat x6)) in H9 by (eapply map_bind2_normalize_exp_clocksof; eauto).
        specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H1) as Hnums1.
        specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H2) as Hnums2.
        repeat rewrite_Forall_forall; solve_length.
        destruct nth eqn:Hnth. destruct a as [a1 a2]. repeat simpl_nth.
        repeat constructor; simpl; try rewrite app_nil_r.
        * eapply map_bind2_wc_exp in H1...
          -- rewrite Forall_forall in H1. eapply H1... eapply nth_In; solve_length.
          -- rewrite Forall_forall; intros...
             eapply H in H14...
             solve_forall; repeat solve_incl.
             eapply H5 in H13; repeat solve_incl.
        * eapply map_bind2_wc_exp in H2...
          -- rewrite Forall_forall in H2. eapply H2... eapply nth_In; solve_length.
          -- rewrite Forall_forall; intros...
             eapply H0 in H14...
             solve_forall; repeat solve_incl.
             eapply H6 in H13; repeat solve_incl.
        * eapply nth_In in H7; rewrite H12 in H7.
          eapply in_app_or in H7.
          eapply in_or_app. destruct H7... right.
          assert (incl (st_clocks st) (st_clocks st')) by repeat solve_incl...
        * rewrite Forall_forall; intros. eapply H8.
          unfold annots; rewrite flat_map_concat_map, map_map, concat_map, map_map.
          eapply concat_map_incl.
          2: rewrite clockof_annot, map_map in H13; eauto.
          eapply nth_In; solve_length.
        * rewrite Forall_forall; intros. eapply H9.
          unfold annots; rewrite flat_map_concat_map, map_map, concat_map, map_map.
          eapply concat_map_incl.
          2: rewrite clockof_annot, map_map in H13; eauto.
          eapply nth_In; solve_length.
        * rewrite <- Hlen1 in H3.
          eapply nth_In in H3. eapply Hnums1 in H3.
          rewrite length_clockof_numstreams...
        * rewrite <- Hlen2 in H3.
          eapply nth_In in H3. eapply Hnums2 in H3.
          rewrite length_clockof_numstreams...
      + (* exp *)
        eapply idents_for_anns_wc in H3...
        rewrite Forall_map. eapply Forall_forall. intros ? _; unfold unnamed_stream; auto.
    - (* ite *)
      destruct is_control; repeat inv_bind.
      + (* control *)
        rewrite Forall_map. eapply Forall2_combine'.
        assert (length (concat x5) = length (annots ets)) as Hlen1 by (eapply map_bind2_normalize_exp_length; eauto).
        assert (length (concat x8) = length (annots efs)) as Hlen2 by (eapply map_bind2_normalize_exp_length; eauto).
        replace (clocksof ets) with (clocksof (concat x5)) in H9 by (eapply map_bind2_normalize_exp_clocksof; eauto).
        replace (clocksof efs) with  (clocksof (concat x8)) in H10 by (eapply map_bind2_normalize_exp_clocksof; eauto).
        specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H2) as Hnums1.
        specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H3) as Hnums2.
        assert (clocksof x = clockof e) as Hclock by (eapply normalize_exp_clockof; eauto).
        assert (length x = numstreams e) as Hlen3 by (eapply normalize_exp_length; eauto).
        rewrite <- length_clockof_numstreams in Hlen3.
        rewrite H8 in Hlen3; simpl in Hlen3. singleton_length.
        repeat rewrite_Forall_forall; solve_length.
        destruct nth eqn:Hnth. destruct a as [a1 a2]. repeat simpl_nth.
        repeat constructor; simpl; try rewrite app_nil_r.
        * eapply IHe in H1...
          inv H1. repeat solve_incl.
        * eapply map_bind2_wc_exp in H2...
          -- rewrite Forall_forall in H2. eapply H2... eapply nth_In; solve_length.
          -- rewrite Forall_forall; intros...
             eapply H in H16...
             solve_forall. repeat solve_incl.
             eapply H6 in H15; repeat solve_incl.
        * eapply map_bind2_wc_exp in H3...
          -- rewrite Forall_forall in H3. eapply H3... eapply nth_In; solve_length.
          -- rewrite Forall_forall; intros...
             eapply H0 in H16...
             solve_forall. repeat solve_incl.
             eapply H7 in H15; repeat solve_incl.
        * congruence.
        * rewrite Forall_forall; intros. eapply H9.
          unfold annots; rewrite flat_map_concat_map, map_map, concat_map, map_map.
          eapply concat_map_incl.
          2: rewrite clockof_annot, map_map in H15; eauto.
          eapply nth_In; solve_length.
        * rewrite Forall_forall; intros. eapply H10.
          unfold annots; rewrite flat_map_concat_map, map_map, concat_map, map_map.
          eapply concat_map_incl.
          2: rewrite clockof_annot, map_map in H15; eauto.
          eapply nth_In; solve_length.
        * rewrite <- Hlen1 in H4.
          eapply nth_In in H4. eapply Hnums1 in H4.
          rewrite length_clockof_numstreams...
        * rewrite <- Hlen2 in H4.
          eapply nth_In in H4. eapply Hnums2 in H4.
          rewrite length_clockof_numstreams...
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
    solve_forall. eapply normalize_exp_wc_exp with (G:=G) (vars:=vars) in H0; eauto.
    solve_forall; repeat solve_incl.
    repeat solve_incl.
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

  Fact normalize_fby_wc_exp : forall G vars e0s es anns es' eqs' st st',
      Forall (wc_exp G (vars++st_clocks st)) e0s ->
      Forall (wc_exp G (vars++st_clocks st)) es ->
      Forall2 (fun e0 a => clockof e0 = [fst (snd a)]) e0s anns ->
      Forall2 (fun e a => clockof e = [fst (snd a)]) es anns ->
      Forall unnamed_stream anns ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) es'.
  Proof with eauto.
    intros G vars e0s es anns es' eqs' st st' Hwc1 Hwc2 Hcl1 Hcl2 Hunnamed Hnorm.
    unfold normalize_fby in Hnorm; repeat inv_bind.
    eapply map_bind2_wc_exp' in H...
    - destruct a as [[e0 e] a]...
    - solve_forall. destruct x as [[e0 e] [ty [cl n]]].
      unfold fby_iteexp in H1.
      destruct (Norm.is_constant e0); repeat inv_bind.
      + repeat rewrite_Forall_forall.
        repeat constructor; simpl...
        * repeat simpl_In.
          apply Hwc1 in H8.
          repeat solve_incl.
        * repeat simpl_In.
          apply Hwc2 in H7.
          repeat solve_incl.
        * rewrite app_nil_r. unfold clock_of_nclock; simpl.
          repeat simpl_nth; repeat simpl_length.
          specialize (H6 _ _ _ _ _ H7 H8 H10); simpl in H6.
          rewrite H8. rewrite H6...
        * rewrite app_nil_r.
          repeat simpl_nth; repeat simpl_length.
          specialize (H4 _ _ _ _ _ H7 H11 H10).
          rewrite H11. rewrite H4.
          repeat constructor. rewrite H10. reflexivity.
      + repeat rewrite_Forall_forall.
        repeat simpl_length.
        assert (unnamed_stream (ty, (cl, n))) as Hunnamed' by (repeat simpl_In; eauto).
        unfold unnamed_stream in Hunnamed'; simpl in Hunnamed'; subst.
        repeat constructor; simpl...
        * eapply init_var_for_clock_In in H1.
          apply in_or_app. right.
          eapply fresh_ident_st_follows in H4. eapply st_follows_incl in H4.
          eapply st_follows_incl in H3.
          eapply H4 in H1. eapply H3 in H1; simpl in H1.
          In_st_clocks x Op.bool_type cl true.
        * repeat simpl_In...
          eapply Hwc1 in H10.
          repeat solve_incl.
        * eapply fresh_ident_In in H4; simpl in H4.
          eapply in_or_app. right.
          In_st_clocks x3 ty cl false.
          eapply st_follows_incl in H3; eauto.
        * rewrite app_nil_r.
          repeat simpl_nth; repeat simpl_length.
          specialize (H8 _ _ _ _ _ H9 H10 H12); simpl in H6.
          rewrite H10. rewrite H8; simpl. constructor...
        * rewrite app_nil_r; simpl.
          repeat simpl_nth; repeat simpl_length.
          specialize (H8 _ _ _ _ _ H0 H10 H12); simpl in H8.
          rewrite H10. rewrite H8. reflexivity.
  Qed.

  Corollary normalize_fby_wc_exp' : forall G vars e0s es anns e0s' es' res eqs1 eqs2 eqs3 st st' st'' st''',
      wc_exp G vars (Efby e0s es anns) ->
      normalize_exps e0s st = (e0s', eqs1, st') ->
      normalize_exps es st' = (es', eqs2, st'') ->
      normalize_fby e0s' es' anns st'' = (res, eqs3, st''') ->
      Forall (wc_exp G (vars++st_clocks st''')) res.
  Proof with eauto.
    intros G vars e0s es anns e0s' es' res eqs1 eqs2 eqs3 st st' st'' st''' Hwc Hnorm1 Hnorm2 Hnorm3.
    inv Hwc. eapply normalize_fby_wc_exp. 6,5:eauto.
    - eapply normalize_exps_wc_exp with (G:=G) (vars:=vars) in Hnorm1...
      1,2:solve_forall; repeat solve_incl.
    - eapply normalize_exps_wc_exp with (G:=G) (vars:=vars) in Hnorm2...
      1,2:solve_forall; repeat solve_incl.
    - clear Hnorm3 Hnorm2 H3 H5.
      assert (length e0s' = length (annots e0s)) by eauto.
      specialize (normalize_exps_numstreams _ _ _ _ _ Hnorm1) as Hnumstreams.
      unfold normalize_exps in Hnorm1; repeat inv_bind.
      eapply map_bind2_normalize_exp_clocksof' in H0...
      assert (Forall2 eq (map clocksof x) (map clockof e0s)).
      { specialize (Forall2_map_1 (fun tys e => tys = clockof e) clocksof x e0s) as [_ Hfm].
        specialize (Forall2_map_2 (fun tys tys' => tys = tys') clockof (map clocksof x) e0s) as [_ Hfm2].
        auto. } rewrite Forall2_eq in H4. rewrite Forall2_eq in H1.
      repeat rewrite_Forall_forall.
      + rewrite <- length_clocksof_annots in *. solve_length.
         erewrite <- map_length, <- map_length. setoid_rewrite <- H4. apply map_length.
      + setoid_rewrite (concat_length_map_nth _ _ _ _ _)...
        * repeat simpl_list.
          replace (concat (map clockof (concat x))) with (concat (map clockof e0s)).
          2: { rewrite <- H1. rewrite clockof_concat_clocksof; auto. } clear H1.
          rewrite <- (map_nth snd), <- (map_nth fst), map_map, <- H4; auto.
        * solve_forall. rewrite length_clockof_numstreams...
    - clear Hnorm1 Hnorm3 H2 H4 H6.
      assert (length es' = length (annots es)) by eauto.
      specialize (normalize_exps_numstreams _ _ _ _ _ Hnorm2) as Hnumstreams.
      unfold normalize_exps in Hnorm2; repeat inv_bind.
      eapply map_bind2_normalize_exp_clocksof' in H0...
      assert (Forall2 (fun tys tys' => tys = tys') (map clocksof x) (map clockof es)).
      { specialize (Forall2_map_1 (fun tys e => tys = clockof e) clocksof x es) as [_ Hfm].
        specialize (Forall2_map_2 (fun tys tys' => tys = tys') clockof (map clocksof x) es) as [_ Hfm2].
        auto. } rewrite Forall2_eq in H1. rewrite Forall2_eq in H5.
      repeat rewrite_Forall_forall.
      -- rewrite <- length_clocksof_annots in *. solve_length.
         erewrite <- map_length, <- map_length. setoid_rewrite <- H5. apply map_length.
      -- setoid_rewrite (concat_length_map_nth _ _ _ _ _)...
         ++ repeat simpl_list.
            replace (concat (map clockof (concat x))) with (concat (map clockof es)).
            2: { rewrite <- H1. rewrite clockof_concat_clocksof; auto. } clear H1.
            rewrite <- (map_nth snd), <- (map_nth fst), map_map, <- H5; auto.
         ++ solve_forall. rewrite length_clockof_numstreams...
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

  Fact normalize_rhs_wc_exp : forall G vars e keep_fby es' eqs' st st',
      wc_exp G (vars++st_clocks st) e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) es'.
  Proof with eauto.
    intros G vars e keep_fby es' eqs' st st' Hwc Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (solve [eapply normalize_exp_wc_exp in Hnorm; eauto]); [| inv Hwc].
    - (* fby *)
      destruct keep_fby.
      + repeat inv_bind.
        eapply normalize_fby_wc_exp' in Hwc...
        solve_forall. solve_incl.
        rewrite <- app_assoc. apply incl_appr', incl_app; solve_incl.
      + eapply normalize_exp_wc_exp in Hnorm...
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

  Corollary normalize_rhss_wc_exp : forall G vars es keep_fby es' eqs' st st',
      Forall (wc_exp G (vars++st_clocks st)) es ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) es'.
  Proof.
    intros G vars es keep_fby es' eqs' st st' Hwc Hnorm.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_wc_exp in H; eauto.
    solve_forall.
    eapply normalize_rhs_wc_exp with (G:=G) (vars:=vars) in H1; eauto.
    - solve_forall. repeat solve_incl.
    - repeat solve_incl.
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

  Fact init_var_for_clock_wc_eq : forall G vars cl id eqs' st st',
      wc_clock vars cl ->
      init_var_for_clock cl st = (id, eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof with eauto.
    intros G vars cl id eqs' st st' Hwc Hinit.
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
        In_st_clocks id Op.bool_type cl true.
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

  Fact fby_iteexp_wc_eq : forall G vars e0 e a e' eqs' st st',
      normalized_lexp e0 ->
      wc_env (vars++st_clocks st) ->
      wc_exp G (vars++st_clocks st) e0 ->
      wc_exp G (vars++st_clocks st) e ->
      clockof e0 = [(fst (snd a))] ->
      clockof e = [(fst (snd a))] ->
      unnamed_stream a ->
      fby_iteexp e0 e a st = (e', eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof with eauto.
    intros G vars e0 e [ty cl] e' eqs' st st' Hnormed Henv Hwc1 Hwc2 Hcl1 Hcl2 Hunnamed Hfby.
    unfold fby_iteexp in Hfby; simpl in *.
    destruct (Norm.is_constant e0); repeat inv_bind; repeat constructor; simpl...
    - eapply add_whens_wc_exp...
      eapply normalized_lexp_wc_exp_clockof in Hnormed...
      rewrite Hcl1 in Hnormed. inv Hnormed. repeat solve_incl.
    - repeat solve_incl.
    - rewrite app_nil_r, add_whens_clockof...
    - rewrite app_nil_r. rewrite Hcl2...
    - unfold unnamed_stream in Hunnamed; simpl in Hunnamed. rewrite Hunnamed. constructor.
    - eapply fresh_ident_In in H0.
      apply in_or_app; right.
      destruct cl. unfold clock_of_nclock, stripname; simpl in *.
      In_st_clocks x2 ty c false.
    - assert (st_follows st x1) as Hfollows1 by repeat solve_st_follows.
      eapply init_var_for_clock_wc_eq with (G:=G) (vars:=(vars++st_clocks st)) in H...
      2: { eapply normalized_lexp_wc_exp_clockof in Hnormed...
           rewrite Hcl1 in Hnormed. inv Hnormed... }
      solve_forall. solve_incl.
      rewrite <- app_assoc. apply incl_appr', incl_app; repeat solve_incl.
  Qed.

  Fact normalize_fby_wc_eq : forall G vars anns e0s es es' eqs' st st',
      Forall normalized_lexp e0s ->
      wc_env (vars++st_clocks st) ->
      Forall (wc_exp G (vars++st_clocks st)) e0s ->
      Forall (wc_exp G (vars++st_clocks st)) es ->
      Forall2 (fun e0 a => clockof e0 = [fst (snd a)]) e0s anns ->
      Forall2 (fun e a => clockof e = [fst (snd a)]) es anns ->
      Forall unnamed_stream anns ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof with eauto.
    induction anns; intros e0s es es' eqs' st st' Hnormed Hwenv Hwc1 Hwc2 Hcl1 Hcl2 Hunnamed Hnorm;
      inv Hcl1; inv Hcl2;
        unfold normalize_fby in Hnorm; simpl in Hnorm; repeat inv_bind; simpl...
    inv Hnormed; inv Hwc1; inv Hwc2; inv Hunnamed.
    apply Forall_app; split.
    - clear IHanns.
      eapply fby_iteexp_wc_eq in H...
      solve_forall. repeat solve_incl. destruct x2 as [[? ?] ?]. repeat solve_st_follows.
    - assert (normalize_fby l l0 anns x4 = (x5, concat x6, st')) as Hnorm.
      { unfold normalize_fby; repeat inv_bind. repeat eexists... inv_bind... }
      eapply IHanns in Hnorm...
      + destruct a as [ty cl]. eapply fby_iteexp_wc_env in H...
        eapply normalized_lexp_wc_exp_clockof in H9...
        rewrite H2 in H9. inv H9...
      + solve_forall. repeat solve_incl.
      + solve_forall. repeat solve_incl.
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
      assert (st_follows x4 x7) as Hfollows3 by repeat solve_st_follows.
      assert (st_follows x7 st') as Hfollows4 by repeat solve_st_follows.
      rewrite Forall2_eq in H6, H7.
      assert (length (concat x2) = length (annots e0s)) as Hlen1 by eauto.
      assert (length (concat x9) = length (annots es)) as Hlen2 by eauto.
      assert (length a = length x5) as Hlen4.
      { repeat simpl_length.
        eapply normalize_fby_length in H3...
        1,2:symmetry;erewrite <- map_length.
        + setoid_rewrite H6; solve_length.
        + setoid_rewrite H7; solve_length. }
      assert (length x8 = length x5) as Hlen3.
      { eapply idents_for_anns_length in H9. solve_length. }
      specialize (normalize_fby_numstreams _ _ _ _ _ _ _ H3) as Hnumstreams.
      assert (H1':=H1).
      eapply map_bind2_wc_eq in H1' as [Hwc1 Hwenv1]...
      2: { rewrite Forall_forall in *; intros; simpl in *.
           eapply H... eapply H4 in H10. repeat solve_incl. }
      assert (H2':=H2).
      eapply map_bind2_wc_eq in H2' as [Hwc2 Hwenv2]...
      2: { rewrite Forall_forall in *; intros; simpl in *.
           eapply H0... eapply H5 in H10. repeat solve_incl. }
      clear H H0.
      split; repeat rewrite Forall_app; repeat split.
      + assert (st_follows x4 st') as Hfollows by repeat solve_st_follows.
        assert (annots x5 = a) as Hanns.
        { repeat simpl_length.
          eapply normalize_fby_annot in H3...
          + erewrite Hlen1, <- map_length, <- map_length. setoid_rewrite <- H6. apply map_length.
          + erewrite Hlen2, <- map_length, <- map_length. setoid_rewrite <- H7. apply map_length. } subst.
        eapply normalize_fby_wc_exp' in H3...
        2,3:unfold normalize_exps; repeat inv_bind; repeat eexists; repeat inv_bind; try reflexivity; eauto.
        clear H4 H5 H6 H7.
        rewrite Forall_map.
        repeat rewrite_Forall_forall.
        destruct x as [[x ann] e]; repeat constructor.
        * simpl_In. eapply H3 in H.
          solve_incl. rewrite <- app_assoc.
          apply incl_appr', incl_app; solve_incl.
        * apply idents_for_anns_values in H9.
          repeat simpl_nth.
          assert (In e x5) as Hin. { repeat simpl_length. eapply nth_In in H. rewrite H6 in H... }
          simpl; rewrite app_nil_r, H6.
          assert (Forall unnamed_stream (annot e)).
          { rewrite Forall_forall. intros ann' Hin'.
            apply H8. unfold annots; rewrite flat_map_concat_map.
            eapply in_concat'... apply in_map... }
          apply Hnumstreams in Hin.
          rewrite nclockof_annot. rewrite <- length_annot_numstreams in Hin. singleton_length.
          repeat constructor. inv H0. inv H10. rewrite H4. constructor.
        * assert (numstreams e = 1).
          { eapply Hnumstreams. repeat simpl_In... }
          rewrite <- length_clockof_numstreams in H0. singleton_length.
          assert ([c] = map (fun x => (fst (snd x))) [ann]); subst.
          { repeat simpl_nth. apply idents_for_anns_values in H9.
            rewrite split_nth in H5; inv H5.
            rewrite split_map_snd, H9.
            unfold annots. erewrite flat_map_concat_map, <- concat_length_map_nth.
            2: solve_length. 2:{ rewrite Forall_forall; intros. rewrite length_annot_numstreams... }
            rewrite H6. rewrite clockof_annot, map_map in Hsingl... }
          simpl in H0. inv H0.
          repeat constructor. apply in_or_app; right.
          apply idents_for_anns_incl_clocks in H9. apply H9.
          repeat simpl_In. exists (x, ann).
          destruct ann as [? [? ?]]...
      + solve_forall. repeat solve_incl.
      + solve_forall. repeat solve_incl.
      + eapply normalize_fby_wc_eq with (G:=G) (vars:=vars) in H3...
        * solve_forall. repeat solve_incl.
        * eapply map_bind2_normalize_exp_wc_exp with (G:=G) (vars:=vars) in H1...
          1,2:solve_forall; repeat solve_incl.
        * eapply map_bind2_normalize_exp_wc_exp with (G:=G) (vars:=vars) in H2...
          1,2:solve_forall; repeat solve_incl.
        * assert (H1':=H1). eapply map_bind2_normalize_exp_numstreams in H1'.
          eapply map_bind2_normalize_exp_clocksof' in H1...
          assert (Forall2 (fun e a => clockof e = [a]) (concat x2) (map clock_of_nclock a)).
          { rewrite H6. unfold clocksof. rewrite flat_map_concat_map.
            apply Forall2_concat. rewrite Forall2_map_2.
            eapply Forall2_impl_In... intros; simpl in *. rewrite <- H10.
            unfold clocksof. rewrite flat_map_concat_map. rewrite <- (concat_map_singl1 a0) at 1.
            apply Forall2_concat. rewrite Forall2_map_2, Forall2_map_1, <- Forall2_same.
            apply Forall_forall. intros ? Hin.
            assert (length (clockof x) = 1).
            { rewrite length_clockof_numstreams. rewrite Forall_forall in H1'; apply H1'. eapply in_concat'... }
            singleton_length. repeat constructor...
          }
          rewrite Forall2_map_2 in H...
        * assert (H2':=H2). eapply map_bind2_normalize_exp_numstreams in H2'.
          eapply map_bind2_normalize_exp_clocksof' in H2...
          assert (Forall2 (fun e a => clockof e = [a]) (concat x9) (map clock_of_nclock a)).
          { rewrite H7. unfold clocksof. rewrite flat_map_concat_map.
            apply Forall2_concat. rewrite Forall2_map_2.
            eapply Forall2_impl_In... intros; simpl in *. rewrite <- H10.
            unfold clocksof. rewrite flat_map_concat_map. rewrite <- (concat_map_singl1 a0) at 1.
            apply Forall2_concat. rewrite Forall2_map_2, Forall2_map_1, <- Forall2_same.
            apply Forall_forall. intros ? Hin.
            assert (length (clockof x) = 1).
            { rewrite length_clockof_numstreams. rewrite Forall_forall in H2'; apply H2'. eapply in_concat'... }
            singleton_length. repeat constructor...
          }
          rewrite Forall2_map_2 in H...
      + assert (Forall (wc_clock ((vars ++ st_clocks x1))) (map clock_of_nclock a)).
        { rewrite H6.
          eapply wc_exp_clocksof in H4... eapply Forall_impl; [|eauto]. intros.
          eapply wc_clock_incl; [|eauto]. rewrite <- app_assoc in *.
          apply incl_appr', incl_app; repeat solve_incl.
          apply map_bind2_normalize_exp_fresh_incl in H1...
          unfold st_clocks. apply incl_map, H1. }
        eapply normalize_fby_wc_env in H3...
        2:{ rewrite Forall_map in H. eapply Forall_impl...
            intros [ty [cl name]] Hwc'.
            unfold clock_of_nclock, stripname in Hwc'; simpl in Hwc'.
            repeat solve_incl. }
      eapply idents_for_anns_wc_env in H9...
      unfold clock_of_nclock, stripname in H. rewrite map_map.
      eapply Forall_impl; [|eauto]. intros.
      repeat solve_incl.
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
      apply Forall2_combine'.
      assert (length x0 = length tys) as Hlen3 by (eapply idents_for_anns_length in H; solve_length).
      rewrite Forall2_map_1, map_map, Forall2_map_2.
      repeat rewrite_Forall_forall...
      + solve_length.
      + destruct nth as [[? ?] ?] eqn:Hnth. inv H3; [|inv H4].
        destruct b as [[? ?] ?]; repeat simpl_nth.
        repeat constructor; simpl; try rewrite app_nil_r.
        Local Ltac mergeitelength H :=
          rewrite length_clockof_numstreams; symmetry;
          apply map_bind2_normalize_exp_numstreams in H; rewrite Forall_forall in H;
          apply H, nth_In; solve_length.
        * eapply map_bind2_normalize_exp_wc_exp with (vars:=vars) in H1...
           1,2:rewrite Forall_forall in *; intros...
           eapply wc_exp_incl; [| eapply H1, nth_In; solve_length]. repeat solve_incl.
        * eapply map_bind2_normalize_exp_wc_exp with (vars:=vars) in H2...
           1,2:rewrite Forall_forall in *; intros...
           eapply wc_exp_incl; [| eapply H2, nth_In; solve_length]. repeat solve_incl.
           eapply wc_exp_incl; [| eauto]. repeat solve_incl.
        * assert (incl (vars++st_clocks st) (vars++st_clocks st')) by repeat solve_incl.
           rewrite <- H4; eauto.
        * rewrite Forall_forall; intros.
           eapply H8. erewrite <- map_bind2_normalize_exp_clocksof... 2:rewrite Forall_forall...
           unfold clocksof; rewrite flat_map_concat_map.
           eapply concat_map_incl... eapply nth_In; solve_length.
        * rewrite Forall_forall; intros.
           eapply H9. erewrite <- map_bind2_normalize_exp_clocksof... 2:rewrite Forall_forall...
           unfold clocksof; rewrite flat_map_concat_map.
           eapply concat_map_incl... eapply nth_In; solve_length.
        * mergeitelength H1.
        * mergeitelength H2.
      + destruct nth, nth, p...
      + destruct nth; simpl in H3. destruct n0; try omega; simpl.
        destruct (nth n _ _) as [[? ?] ?]; simpl...
      + destruct nth, nth, p...
      + destruct nth as [? [? [? ?]]] eqn:Hi; simpl in H3. destruct n0; try omega; simpl.
        destruct (nth n (combine _ _) _) as [[? ?] ?] eqn:Hi2; simpl...
        unfold clock_of_nclock, stripname; simpl.
        assert (c = ck); subst. {
          apply idents_for_anns_values in H.
          specialize (map_nth snd x0 a n) as Hmap.
          rewrite H, Hi, map_nth' with (d':=Op.bool_type) in Hmap; simpl in Hmap; inv Hmap; auto.
          solve_length. }
        apply idents_for_anns_incl_clocks in H.
        apply in_or_app. right. apply H.
        rewrite in_map_iff. exists (i, (t, (ck, o))); split...
        setoid_rewrite <- Hi...
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
          apply incl_map, st_follows_incl. repeat solve_st_follows. }
        assert (length x2 = length tys) as Hlen3 by (eapply idents_for_anns_length in H; solve_length).
        apply Forall2_combine'.
        rewrite Forall2_map_1, map_map, Forall2_map_2.
        repeat rewrite_Forall_forall...
        + solve_length.
        + destruct nth as [[? ?] ?] eqn:Hnth. inv H4; [|inv H14].
          destruct b as [[? ?] ?]; repeat simpl_nth.
          repeat constructor; simpl; try rewrite app_nil_r.
          * eapply hd_default_wc_exp. eapply normalize_exp_wc_exp in H1...
            solve_forall. repeat solve_incl.
          * eapply map_bind2_normalize_exp_wc_exp with (vars:=vars) in H2...
            1,2:rewrite Forall_forall in *; intros.
            eapply wc_exp_incl; [| eapply H2, nth_In; solve_length]. repeat solve_incl.
            eapply wc_exp_incl; [| eauto]. repeat solve_incl.
          * eapply map_bind2_normalize_exp_wc_exp with (vars:=vars) in H3...
            1,2:rewrite Forall_forall in *; intros.
            eapply wc_exp_incl; [| eapply H3, nth_In; solve_length]. repeat solve_incl.
            eapply wc_exp_incl; [| eauto]. repeat solve_incl.
          * assert (length x = numstreams e) as Hlen4 by eauto.
            rewrite <- length_clockof_numstreams, H8 in Hlen4; simpl in Hlen4.
            erewrite <- normalize_exp_clockof in H8...
            repeat singleton_length...
          * rewrite Forall_forall; intros.
            eapply H9. erewrite <- map_bind2_normalize_exp_clocksof... 2:rewrite Forall_forall...
            unfold clocksof; rewrite flat_map_concat_map.
            eapply concat_map_incl... eapply nth_In; solve_length.
          * rewrite Forall_forall; intros.
            eapply H10. erewrite <- map_bind2_normalize_exp_clocksof... 2:rewrite Forall_forall...
            unfold clocksof; rewrite flat_map_concat_map.
            eapply concat_map_incl... eapply nth_In; solve_length.
          * mergeitelength H2.
          * mergeitelength H3.
        + destruct nth, nth, p...
        + destruct nth; simpl in H4. destruct n0; try omega; simpl.
          destruct (nth n _ _) as [[? ?] ?]; simpl...
        + destruct nth, nth, p...
        + destruct nth as [? [? [? ?]]] eqn:Hi; simpl in H4. destruct n0; try omega; simpl.
          destruct (nth n (combine _ _) _) as [[? ?] ?] eqn:Hi2; simpl...
          unfold clock_of_nclock, stripname; simpl.
          assert (c = ck); subst. {
            apply idents_for_anns_values in H.
            specialize (map_nth snd x2 a n) as Hmap.
            rewrite H, Hi, map_nth' with (d':=Op.bool_type) in Hmap; simpl in Hmap; inv Hmap; auto.
            solve_length. }
          apply idents_for_anns_incl_clocks in H.
          apply in_or_app. right. apply H.
          rewrite in_map_iff. exists (i, (t, (ck, o))); split...
          setoid_rewrite <- Hi...
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
    eapply normalize_exp_wc_eq with (G:=G) (vars:=vars) in H4...
    repeat solve_incl.
  Qed.

  Fact normalize_rhs_wc_eq : forall G vars e keep_fby es' eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      wc_exp G (vars++st_clocks st) e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs' /\
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros G vars e keep_fby es' eqs' st st' HwG Hwenv Hwc Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (solve [eapply normalize_exp_wc_eq in Hnorm; eauto]);
      [destruct keep_fby|inv Hwc].
    - (* fby (keep) *)
      assert (Hwc':=Hwc). inv Hwc'.
      repeat inv_bind.
      assert (st_follows x1 x4) as Hfollows1 by repeat solve_st_follows.
      assert (st_follows x4 st') as Hfollows2 by repeat solve_st_follows.
      assert (H':=H).
      eapply normalize_exps_wc_eq in H' as [Hwc1 Hwenv1]...
      assert (H0':=H0).
      eapply normalize_exps_wc_eq in H0' as [Hwc2 Hwenv2]...
      2:solve_forall; repeat solve_incl.
      split; repeat rewrite Forall_app; repeat split.
      + solve_forall; repeat solve_incl.
      + solve_forall; repeat solve_incl.
      + eapply normalize_fby_wc_eq in H1...
        * eapply normalize_exps_wc_exp in H... solve_forall. repeat solve_incl.
        * eapply normalize_exps_wc_exp in H0... solve_forall. repeat solve_incl.
        * unfold normalize_exps in H; repeat inv_bind.
          assert (H':=H). eapply map_bind2_normalize_exp_numstreams in H'.
          eapply map_bind2_normalize_exp_clocksof' in H...
          assert (Forall2 (fun e a => clockof e = [a]) (concat x5) (map clock_of_nclock l1)).
          { rewrite Forall2_eq in H4; rewrite H4. unfold clocksof. rewrite flat_map_concat_map.
            apply Forall2_concat. rewrite Forall2_map_2.
            eapply Forall2_impl_In... intros; simpl in *. rewrite <- H9.
            unfold clocksof. rewrite flat_map_concat_map. rewrite <- (concat_map_singl1 a) at 1.
            apply Forall2_concat. rewrite Forall2_map_2, Forall2_map_1, <- Forall2_same.
            apply Forall_forall. intros ? Hin.
            assert (length (clockof x) = 1).
            { rewrite length_clockof_numstreams. rewrite Forall_forall in H'; apply H'. eapply in_concat'... }
            singleton_length. repeat constructor...
          }
          rewrite Forall2_map_2 in H7...
        * unfold normalize_exps in H0; repeat inv_bind.
          assert (H0':=H0). eapply map_bind2_normalize_exp_numstreams in H0'.
          eapply map_bind2_normalize_exp_clocksof' in H0...
          assert (Forall2 (fun e a => clockof e = [a]) (concat x5) (map clock_of_nclock l1)).
          { rewrite Forall2_eq in H5; rewrite H5. unfold clocksof. rewrite flat_map_concat_map.
            apply Forall2_concat. rewrite Forall2_map_2.
            eapply Forall2_impl_In... intros; simpl in *. rewrite <- H9.
            unfold clocksof. rewrite flat_map_concat_map. rewrite <- (concat_map_singl1 a) at 1.
            apply Forall2_concat. rewrite Forall2_map_2, Forall2_map_1, <- Forall2_same.
            apply Forall_forall. intros ? Hin.
            assert (length (clockof x2) = 1).
            { rewrite length_clockof_numstreams. rewrite Forall_forall in H0'; apply H0'. eapply in_concat'... }
            singleton_length. repeat constructor...
          }
          rewrite Forall2_map_2 in H7...
      + eapply normalize_fby_wc_env in H1...
        eapply wc_exp_clockof in Hwc...
        simpl in Hwc.
        rewrite Forall_map in Hwc. eapply Forall_impl; [|eapply Hwc].
        intros [ty [cl name]] Hwc'.
        unfold clock_of_nclock, stripname in Hwc'; simpl in Hwc'.
        solve_incl. rewrite <- app_assoc.
        repeat solve_incl. apply incl_app; try solve_incl.
        apply incl_map, incl_app.
        * eapply normalize_exps_fresh_incl in H...
          etransitivity... apply incl_map, st_follows_incl...
        * eapply normalize_exps_fresh_incl in H0...
    - (* fby (dont keep) *)
      eapply normalize_exp_wc_eq in Hnorm...
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

  Corollary normalize_rhss_wc_eq : forall G vars es keep_fby es' eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      Forall (wc_exp G (vars++st_clocks st)) es ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs' /\
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros G vars es keep_fby es' eqs' st st' HwG Hwenv Hwc Hnorm.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_wc_eq in H...
    solve_forall.
    eapply normalize_rhs_wc_eq with (G:=G) (vars:=vars) in H4...
    repeat solve_incl.
  Qed.

  Fact normalize_equation_wc_eq : forall G vars e to_cut eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      wc_equation G (vars++st_clocks st) e ->
      normalize_equation to_cut e st = (eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs' /\
      wc_env (vars++st_clocks st').
  Proof with eauto.
    intros G vars [xs es] to_cut eqs' st st' HwG Hwenv Hwc Hnorm.
    unfold normalize_equation in Hnorm. repeat inv_bind.
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

  Corollary normalize_equations_wc_eq : forall G vars eqs to_cut eqs' st st',
      wc_global G ->
      wc_env (vars++st_clocks st) ->
      Forall (wc_equation G (vars++st_clocks st)) eqs ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs' /\
      wc_env (vars++st_clocks st').
  Proof with eauto.
    induction eqs; intros to_cut eqs' st st' HwG Hwenv Hwc Hnorm;
      simpl in *; repeat inv_bind...
    assert (st_follows st x0) as Hfollows1 by repeat solve_st_follows.
    assert (st_follows x0 st') as Hfollows2 by repeat solve_st_follows.
    inv Hwc. eapply normalize_equation_wc_eq in H as [Hwc1 Hwenv1]...
    apply IHeqs in H0 as [Hwc2 Hwenv2]... 2:solve_forall; repeat solve_incl.
    split...
    apply Forall_app; split...
    solve_forall; repeat solve_incl.
  Qed.

  Lemma normalize_node_wc : forall G n to_cut Hwl n',
      wc_global G ->
      wc_node G n ->
      normalize_node to_cut n Hwl = n' ->
      wc_node G n'.
  Proof with eauto.
    intros G n to_cut Hwl n' HwG [Hin [Hout [Henv Heq]]] Hnorm.
    unfold normalize_node in Hnorm. subst.
    repeat constructor; simpl; auto.
    - remember (normalize_equations _ _ _) as res. symmetry in Heqres.
      destruct res as [eqs' st']; simpl.
      unfold idck. repeat rewrite map_app.
      eapply normalize_equations_wc_eq in Heqres as [_ Henv']...
      2,3:unfold st_clocks; rewrite init_st_anns, app_nil_r...
      2:rewrite (Permutation_app_comm (n_vars _)) in Heq...
      unfold idck in Henv'; repeat rewrite map_app in Henv'; repeat rewrite <- app_assoc in Henv'...
    - remember (normalize_equations _ _ _) as res. symmetry in Heqres.
      destruct res as [eqs' st']; simpl.
      unfold idck. repeat rewrite map_app.
      eapply normalize_equations_wc_eq in Heqres as [Hwc' _]...
      2,3:unfold st_clocks; rewrite init_st_anns, app_nil_r...
      2:rewrite (Permutation_app_comm (n_vars _)) in Heq...
      unfold idck in Hwc'; repeat rewrite map_app in Hwc'; repeat rewrite <- app_assoc in *.
      rewrite (Permutation_app_comm (map _ (idty _))), (Permutation_swap (map _ (n_vars _)))...
  Qed.

  Lemma normalize_global_wc : forall G Hwl G',
      wc_global G ->
      normalize_global G Hwl = G' ->
      wc_global G'.
  Proof.
    induction G; intros Hwl G' Hwt Hnorm; simpl in Hnorm; inv Hwt.
    - constructor.
    - constructor.
      + eapply IHG; eauto.
      + remember (normalize_node _ _ _) as n'. symmetry in Heqn'.
        eapply normalize_node_wc in Heqn'; eauto. simpl in Heqn'.
        eapply iface_eq_wc_node; eauto.
        eapply normalize_global_eq.
      + eapply normalize_global_names; eauto.
  Qed.
End NCLOCKING.

Module NClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Clo : LCLOCKING Ids Op Syn)
       (Norm : FULLNORM Ids Op OpAux Syn)
       <: NCLOCKING Ids Op OpAux Syn Clo Norm.
  Include NCLOCKING Ids Op OpAux Syn Clo Norm.
End NClockingFun.
