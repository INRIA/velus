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

  (** ** wc implies wl *)

  Hint Constructors wl_exp.
  Fact wc_exp_wl_exp : forall G vars e,
      wc_exp G vars e ->
      wl_exp G e.
  Proof with eauto.
    induction e using exp_ind2; intro Hwt; inv Hwt; auto.
    - (* unop *)
      constructor...
      rewrite <- length_clockof_numstreams. rewrite H3. reflexivity.
    - (* binop *)
      constructor...
      + rewrite <- length_clockof_numstreams. rewrite H5. reflexivity.
      + rewrite <- length_clockof_numstreams. rewrite H6. reflexivity.
    - (* fby *)
      constructor; repeat rewrite_Forall_forall...
      + solve_length.
      + solve_length.
    - (* when *)
      constructor; repeat rewrite_Forall_forall...
      solve_length.
    - (* merge *)
      constructor; repeat rewrite_Forall_forall...
      + solve_length.
      + solve_length.
    - (* ite *)
      constructor; repeat rewrite_Forall_forall...
      + rewrite <- length_clockof_numstreams. rewrite H8. reflexivity.
      + solve_length.
      + solve_length.
    - (* app *)
      repeat rewrite_Forall_forall.
      econstructor...
      + rewrite_Forall_forall...
      + unfold idck in *. rewrite nclocksof_annots in *. solve_length.
      + solve_length.
    - (* app (reset) *)
      repeat rewrite_Forall_forall.
      econstructor...
      + rewrite_Forall_forall...
      + rewrite <- length_clockof_numstreams. rewrite H10. reflexivity.
      + unfold idck in *. rewrite nclocksof_annots in *. solve_length.
      + solve_length.
  Qed.
  Hint Resolve wc_exp_wl_exp.

  Corollary Forall_wc_exp_wl_exp : forall G vars es,
      Forall (wc_exp G vars) es ->
      Forall (wl_exp G) es.
  Proof. intros. solve_forall. Qed.
  Hint Resolve Forall_wc_exp_wl_exp.

  Fact wc_equation_wl_equation : forall G vars equ,
      wc_equation G vars equ ->
      wl_equation G equ.
  Proof with eauto.
    intros G vars [xs es] [Hwc1 [Hwc2 _]].
    constructor.
    + repeat rewrite_Forall_forall...
    + rewrite nclocksof_annots in Hwc2.
      repeat rewrite_Forall_forall.
      solve_length.
  Qed.
  Hint Resolve wc_equation_wl_equation.

  Fact wc_node_wl_node : forall G n,
      wc_node G n ->
      wl_node G n.
  Proof with eauto.
    intros G n [_ [_ [_ Hwc]]].
    unfold wl_node.
    repeat rewrite_Forall_forall...
  Qed.
  Hint Resolve wc_node_wl_node.

  Fact wc_global_wl_global : forall G,
      wc_global G ->
      wl_global G.
  Proof with eauto.
    intros G Hwt.
    induction Hwt; constructor...
  Qed.
  Hint Resolve wc_global_wl_global.

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

  (** ** A few additional things *)

  Definition st_clocks (st : fresh_st ((Op.type * clock) * bool)) :=
    List.map (fun '(id, ((_, cl), _)) => (id, cl)) (st_anns st).

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
    unfold st_clocks, idty in *.
    repeat simpl_In. inv H.
    exists (id, (t, cl, b)); auto.
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
    unfold st_clocks, idty in *.
    repeat simpl_In. inv H.
    exists (id, (t, cl, b)); auto.
  Qed.

  Fact idents_for_anns'_clocknames : forall anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      Forall (fun x => LiftO True (eq (fst x)) (snd (snd (snd x)))) ids.
  Proof with eauto.
    induction anns; intros ids st st' Hids; simpl in *; repeat inv_bind...
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

  (** ** For a normalized_lexp, wc_exp implies wc_clock (clockof) *)

  Lemma wc_exp_clockof : forall G vars e,
      normalized_lexp e ->
      wc_env vars ->
      wc_exp G vars e ->
      Forall (wc_clock vars) (clockof e).
  Proof with eauto.
    intros G e vas Hnormed Henv Hwc.
    induction Hnormed; inv Hwc; simpl; unfold clock_of_nclock, stripname;
      simpl in *; repeat constructor...
    - (* var *)
      unfold wc_env in Henv; rewrite Forall_forall in Henv.
      apply Henv in H0...
    - (* var (anon) *)
      unfold wc_env in Henv; rewrite Forall_forall in Henv.
      apply Henv in H0...
    - (* unop *)
      apply IHHnormed in H1...
      rewrite H4 in H1. inv H1...
    - (* binop *)
      apply IHHnormed1 in H3...
      rewrite H6 in H3. inv H3...
    - (* when *)
      inv H3; clear H2.
      apply IHHnormed in H1.
      rewrite app_nil_r in *. symmetry in H7. singleton_length.
      inv H6. inv H1...
  Qed.

  (** ** Perservation of wc_env *)

  (* Fact normalize_exp_wc_env : forall *)

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
      simpl in *; repeat inv_bind; simpl; auto.
    destruct a as [? [? ?]]. repeat inv_bind.
    inv Hunnamed. constructor; eauto.
    unfold unnamed_stream in H3; simpl in H3; subst.
    constructor.
    eapply fresh_ident_In in H.
    eapply idents_for_anns_st_follows in H0.
    eapply st_follows_incl in H; eauto.
    eapply in_or_app. right.
    unfold st_clocks. simpl_In. exists (x, (t, c, false)); auto.
  Qed.

  Fact idents_for_anns'_wc : forall G vars anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      Forall (wc_exp G (vars++st_clocks st')) (List.map (fun '(x, ann) => Evar x ann) ids).
  Proof.
    induction anns; intros ids st st' Hident;
      simpl in *; repeat inv_bind; simpl; auto.
    destruct a as [? [? ?]].
    destruct o; repeat inv_bind; constructor; eauto.
    - constructor.
      destruct x. eapply reuse_ident_In in H.
      eapply idents_for_anns'_st_follows in H0.
      eapply st_follows_incl in H; eauto.
      eapply in_or_app. right.
      unfold st_clocks. simpl_In. exists (i, (t, c, false)); auto.
    - constructor.
      eapply fresh_ident_In in H.
      eapply idents_for_anns'_st_follows in H0.
      eapply st_follows_incl in H; eauto.
      eapply in_or_app. right.
      unfold st_clocks. simpl_In. exists (x, (t, c, false)); auto.
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
          unfold st_clocks. repeat simpl_In. exists (x, (Op.bool_type, cl, true)); auto.
        * repeat simpl_In...
          eapply Hwc1 in H10.
          repeat solve_incl.
        * eapply fresh_ident_In in H4; simpl in H4.
          eapply in_or_app. right.
          unfold st_clocks.
          repeat simpl_In. exists (x3, (ty, cl, false)); split; auto.
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
    unfold st_clocks.
    rewrite in_map_iff. exists (x, (t, c, false)); auto.
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

  Fact map_bind2_wc_eq {A A1 B} :
    forall G vars (k : A -> Fresh (A1 * list equation) B) a a1s eqs' st st',
      map_bind2 k a st = (a1s, eqs', st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
      Forall (fun a => forall a1 eqs' st0 st0',
                  k a st0 = (a1, eqs', st0') ->
                  st_follows st st0 ->
                  st_follows st0' st' ->
                  Forall (wc_equation G vars) eqs') a ->
      Forall (wc_equation G vars) (concat eqs').
  Proof.
    intros G vars k a.
    induction a; intros a1s eqs' st st' Hmap Hfollows Hforall;
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
        unfold clock_of_nclock, stripname, st_clocks; simpl.
        apply in_map_iff. exists (id, (Op.bool_type, cl, true))...
  Qed.

  Fact fby_iteexp_wc_eq : forall G vars e0 e a e' eqs' st st',
      wc_exp G (vars++st_clocks st) e0 ->
      wc_exp G (vars++st_clocks st) e ->
      clockof e = [(fst (snd a))] ->
      clockof e0 = [(fst (snd a))] ->
      unnamed_stream a ->
      fby_iteexp e0 e a st = (e', eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof with eauto.
    intros G vars e0 e [ty cl] e' eqs' st st' Hwc1 Hwc2 Hcl1 Hcl2 Hunnamed Hfby.
    unfold fby_iteexp in Hfby; simpl in *.
    destruct (Norm.is_constant e0); repeat inv_bind; repeat constructor; simpl...
    - eapply add_whens_wc_exp... admit.
    - repeat solve_incl.
    - rewrite app_nil_r, add_whens_clockof...
    - rewrite app_nil_r. rewrite Hcl1...
    - unfold unnamed_stream in Hunnamed; simpl in Hunnamed. rewrite Hunnamed. constructor.
    - eapply fresh_ident_In in H0.
      apply in_or_app; right. unfold st_clocks.
      apply in_map_iff. exists (x2, (ty, fst cl, false)); auto.
    - eapply init_var_for_clock_wc_eq with (G:=G) (vars:=vars) in H...
      2: admit.
      solve_forall. repeat solve_incl.
  Admitted.

  Fact normalize_fby_wc_eq : forall G vars anns e0s es es' eqs' st st',
      Forall (wc_exp G (vars++st_clocks st)) e0s ->
      Forall (wc_exp G (vars++st_clocks st)) es ->
      Forall2 (fun e0 a => clockof e0 = [fst (snd a)]) e0s anns ->
      Forall2 (fun e a => clockof e = [fst (snd a)]) es anns ->
      Forall unnamed_stream anns ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof with eauto.
    induction anns; intros e0s es es' eqs' st st' Hwc1 Hwc2 Hcl1 Hcl2 Hunnamed Hnorm;
      inv Hcl1; inv Hcl2;
        unfold normalize_fby in Hnorm; simpl in Hnorm; repeat inv_bind; simpl...
    inv Hwc1; inv Hwc2; inv Hunnamed.
    apply Forall_app; split.
    - clear IHanns.
      eapply fby_iteexp_wc_eq in H...
      solve_forall. repeat solve_incl. destruct x2 as [[? ?] ?]. repeat solve_st_follows.
    - assert (normalize_fby l l0 anns x4 = (x5, concat x6, st')) as Hnorm.
      { unfold normalize_fby; repeat inv_bind. repeat eexists... inv_bind... }
      eapply IHanns in Hnorm...
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
    1,2,3,4:eapply in_or_app; right; unfold st_clocks; rewrite in_map_iff.
    - apply fresh_ident_In in H. exists (x, (Op.type_const c, Cbase, false))...
    - apply fresh_ident_In in H0. exists (x, (ty, c, false))...
    - apply fresh_ident_In in H1. exists (x, (ty, c, false))...
    - apply fresh_ident_In in H0. exists (x0, (ty, c, false))...
  Qed.

  Fact normalize_exp_wc_eq : forall G vars e is_control es' eqs' st st',
      wc_exp G (vars++st_clocks st) e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwc Hnorm;
      simpl in *; inv Hwc; repeat inv_bind...
    - (* binop *)
      assert (st_follows st x1) as Hfollows by eauto. eapply st_follows_clocks_incl in Hfollows.
      assert (st_follows x1 st') as Hfollows2 by eauto.
      eapply IHe1 in H...
      eapply IHe2 in H0... 2: repeat solve_incl.
      eapply Forall_app; split...
      solve_forall. repeat solve_incl.
    - (* fby *)
      rewrite Forall2_eq in H6, H7.
      assert (length (concat x2) = length (annots e0s)) as Hlen1 by eauto.
      assert (length (concat x9) = length (annots es)) as Hlen2 by eauto.
      assert (length x5 = length a) as Hlen3.
      { repeat simpl_length.
        eapply normalize_fby_length in H3...
        1,2:symmetry;erewrite <- map_length.
        + setoid_rewrite H6; solve_length.
        + setoid_rewrite H7; solve_length. }
      repeat rewrite Forall_app; repeat split.
      + assert (st_follows x4 st') as Hfollows by repeat solve_st_follows.
        assert (annots x5 = a) as Hanns.
        { repeat simpl_length.
          eapply normalize_fby_annot in H3...
          + erewrite Hlen1, <- map_length, <- map_length. setoid_rewrite <- H6. apply map_length.
          + erewrite Hlen2, <- map_length, <- map_length. setoid_rewrite <- H7. apply map_length. } subst.
        eapply normalize_fby_wc_exp' in H3.
        3,4:unfold normalize_exps; repeat inv_bind; repeat eexists; repeat inv_bind; try reflexivity; eauto.
        2: eauto.
        clear H H0 H4 H5 H6 H7.
        rewrite Forall_map.
        repeat rewrite_Forall_forall.
        destruct x as [[x ann] e]; repeat constructor.
        * simpl_In. eapply H3 in H.
          solve_incl. rewrite <- app_assoc.
          apply incl_appr', incl_app; solve_incl.
        * apply idents_for_anns_values in H9.
          repeat simpl_nth. 2:erewrite <- map_length, H9; auto.
          simpl; rewrite app_nil_r, H6.
          admit. (* ok because we know unnamed_stream *)
        * admit. (* idem *)
      + eapply map_bind2_wc_eq in H1...
        rewrite Forall_forall in H, H4. rewrite Forall_forall; intros.
        eapply H in H10; [| |eauto].
        solve_forall; repeat solve_incl.
        eapply H4 in H10. repeat solve_incl.
      + eapply map_bind2_wc_eq in H2...
        rewrite Forall_forall in H0, H5. rewrite Forall_forall; intros.
        eapply H0 in H10; [| |eauto].
        solve_forall; repeat solve_incl.
        eapply H5 in H10; repeat solve_incl.
      + admit. (* The equations generated by normalize_fby should be wc *)
    - (* when *)
      eapply map_bind2_wc_eq in H0...
      rewrite Forall_forall in H, H4. rewrite Forall_forall; intros.
      eapply H in H1; [| |eauto].
      solve_forall; repeat solve_incl.
      apply H4 in H1; repeat solve_incl.
    - (* merge *)
      assert (length (concat x3) = length (annots ets)) as Hlen1 by eauto.
      assert (length (concat x6) = length (annots efs)) as Hlen2 by eauto.
      destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split.
      1,4: eapply map_bind2_wc_eq in H1... 3,5: eapply map_bind2_wc_eq in H2...
      1,2,3,4: repeat rewrite_Forall_forall.
      Local Ltac mergeiteeqs Hin1 Hin2 Hind Hnorm Hwc :=
        eapply Hind in Hnorm; eauto;
        [rewrite Forall_forall in Hnorm; eapply Hnorm in Hin2; repeat solve_incl
        |eapply Hwc in Hin1; repeat solve_incl].
      + mergeiteeqs H3 H14 H H4 H5.
      + mergeiteeqs H4 H15 H H12 H5.
      + mergeiteeqs H3 H14 H0 H4 H6.
      + mergeiteeqs H4 H15 H0 H12 H6.
      + clear H H0.
        assert (length x0 = length tys) as Hlen3 by (eapply idents_for_anns_length in H3; solve_length).
        apply Forall2_combine'.
        rewrite Forall2_map_1, map_map, Forall2_map_2.
        repeat rewrite_Forall_forall...
        * solve_length.
        * destruct nth as [[? ?] ?] eqn:Hnth. inv H0; [|inv H4].
          destruct b as [[? ?] ?]; repeat simpl_nth.
          repeat constructor; simpl; try rewrite app_nil_r.
          Local Ltac mergeitelength H :=
            rewrite length_clockof_numstreams; symmetry;
            apply map_bind2_normalize_exp_numstreams in H; rewrite Forall_forall in H;
            apply H, nth_In; solve_length.
          -- eapply map_bind2_normalize_exp_wc_exp with (vars:=vars) in H1...
             1,2:rewrite Forall_forall in *; intros.
             eapply wc_exp_incl; [| eapply H1, nth_In; solve_length]. repeat solve_incl.
             eapply wc_exp_incl; [| eauto]. repeat solve_incl.
          -- eapply map_bind2_normalize_exp_wc_exp with (vars:=vars) in H2...
             1,2:rewrite Forall_forall in *; intros.
             eapply wc_exp_incl; [| eapply H2, nth_In; solve_length]. repeat solve_incl.
             eapply wc_exp_incl; [| eauto]. repeat solve_incl.
          -- assert (incl (vars++st_clocks st) (vars++st_clocks st')) by repeat solve_incl.
             rewrite <- H4; eauto.
          -- rewrite Forall_forall; intros.
             eapply H8. erewrite <- map_bind2_normalize_exp_clocksof... 2:rewrite Forall_forall...
             unfold clocksof; rewrite flat_map_concat_map.
             eapply concat_map_incl... eapply nth_In; solve_length.
          -- rewrite Forall_forall; intros.
             eapply H9. erewrite <- map_bind2_normalize_exp_clocksof... 2:rewrite Forall_forall...
             unfold clocksof; rewrite flat_map_concat_map.
             eapply concat_map_incl... eapply nth_In; solve_length.
          -- mergeitelength H1.
          -- mergeitelength H2.
        * destruct nth, nth, p...
        * destruct nth; simpl in H0. destruct n0; try omega; simpl.
          destruct (nth n _ _) as [[? ?] ?]; simpl...
        * destruct nth, nth, p...
        * destruct nth as [? [? [? ?]]] eqn:Hi; simpl in H0. destruct n0; try omega; simpl.
          destruct (nth n (combine _ _) _) as [[? ?] ?] eqn:Hi2; simpl...
          unfold clock_of_nclock, stripname; simpl.
          assert (c = ck); subst. {
            apply idents_for_anns_values in H3.
            specialize (map_nth snd x0 a n) as Hmap.
            rewrite H3, Hi, map_nth' with (d':=Op.bool_type) in Hmap; simpl in Hmap; inv Hmap; auto.
            solve_length. }
          apply idents_for_anns_incl_clocks in H3.
          apply in_or_app. right. apply H3.
          rewrite in_map_iff. exists (i, (t, (ck, o))); split...
          setoid_rewrite <- Hi...
    - (* ite *)
      assert (length (concat x5) = length (annots ets)) as Hlen1 by eauto.
      assert (length (concat x8) = length (annots efs)) as Hlen2 by eauto.
      destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split.
      2,6: eapply map_bind2_wc_eq in H2... 4,7: eapply map_bind2_wc_eq in H3...
      1,7:eapply IHe in H1; eauto; solve_forall; repeat solve_incl.
      1,2,3,4: repeat rewrite_Forall_forall.
      + mergeiteeqs H4 H17 H H14 H6.
      + mergeiteeqs H14 H18 H H15 H6.
      + mergeiteeqs H4 H17 H0 H14 H7.
      + mergeiteeqs H14 H18 H0 H15 H7.
      + clear H H0.
        assert (length x2 = length tys) as Hlen3 by (eapply idents_for_anns_length in H4; solve_length).
        apply Forall2_combine'.
        rewrite Forall2_map_1, map_map, Forall2_map_2.
        repeat rewrite_Forall_forall...
        * solve_length.
        * destruct nth as [[? ?] ?] eqn:Hnth. inv H0; [|inv H4].
          destruct b as [[? ?] ?]; repeat simpl_nth.
          repeat constructor; simpl; try rewrite app_nil_r.
          -- eapply hd_default_wc_exp. eapply normalize_exp_wc_exp in H1...
             solve_forall. repeat solve_incl.
          -- eapply map_bind2_normalize_exp_wc_exp with (vars:=vars) in H2...
             1,2:rewrite Forall_forall in *; intros.
             eapply wc_exp_incl; [| eapply H2, nth_In; solve_length]. repeat solve_incl.
             eapply wc_exp_incl; [| eauto]. repeat solve_incl.
          -- eapply map_bind2_normalize_exp_wc_exp with (vars:=vars) in H3...
             1,2:rewrite Forall_forall in *; intros.
             eapply wc_exp_incl; [| eapply H3, nth_In; solve_length]. repeat solve_incl.
             eapply wc_exp_incl; [| eauto]. repeat solve_incl.
          -- assert (length x = numstreams e) as Hlen4 by eauto.
             rewrite <- length_clockof_numstreams, H8 in Hlen4; simpl in Hlen4.
             erewrite <- normalize_exp_clockof in H8...
             repeat singleton_length...
          -- rewrite Forall_forall; intros.
             eapply H9. erewrite <- map_bind2_normalize_exp_clocksof... 2:rewrite Forall_forall...
             unfold clocksof; rewrite flat_map_concat_map.
             eapply concat_map_incl... eapply nth_In; solve_length.
          -- rewrite Forall_forall; intros.
             eapply H10. erewrite <- map_bind2_normalize_exp_clocksof... 2:rewrite Forall_forall...
             unfold clocksof; rewrite flat_map_concat_map.
             eapply concat_map_incl... eapply nth_In; solve_length.
          -- mergeitelength H2.
          -- mergeitelength H3.
          -- inv H14.
        * destruct nth, nth, p...
        * destruct nth; simpl in H0. destruct n0; try omega; simpl.
          destruct (nth n _ _) as [[? ?] ?]; simpl...
        * destruct nth, nth, p...
        * destruct nth as [? [? [? ?]]] eqn:Hi; simpl in H0. destruct n0; try omega; simpl.
          destruct (nth n (combine _ _) _) as [[? ?] ?] eqn:Hi2; simpl...
          unfold clock_of_nclock, stripname; simpl.
          assert (c = ck); subst. {
            apply idents_for_anns_values in H4.
            specialize (map_nth snd x2 a n) as Hmap.
            rewrite H4, Hi, map_nth' with (d':=Op.bool_type) in Hmap; simpl in Hmap; inv Hmap; auto.
            solve_length. }
          apply idents_for_anns_incl_clocks in H4.
          apply in_or_app. right. apply H4.
          rewrite in_map_iff. exists (i, (t, (ck, o))); split...
          setoid_rewrite <- Hi...
    - (* app *)
      rewrite app_nil_r. constructor.
      + repeat econstructor; simpl...
        * eapply map_bind2_normalize_exp_wc_exp in H1...
          solve_forall. repeat solve_incl.
        * erewrite map_bind2_normalize_exp_nclocksof...
        * erewrite idents_for_anns'_values...
        * rewrite app_nil_r, map_map, Forall2_map_1, Forall2_map_2, <- Forall2_same.
          eapply idents_for_anns'_clocknames...
        * unfold clock_of_nclock, stripname.
          rewrite app_nil_r, map_map, Forall2_map_1, Forall2_map_2, <- Forall2_same.
          eapply idents_for_anns'_incl_clocks in H2.
          apply Forall_forall; intros.
          apply in_or_app; right. apply H2.
          rewrite in_map_iff. exists x; split; auto. destruct x as [? [? [? ?]]]; auto.
      + eapply map_bind2_wc_eq in H1...
        rewrite Forall_forall in *. intros.
        eapply H0 in H4... solve_forall; repeat solve_incl.
        eapply H5 in H3. repeat solve_incl.
    - (* app (reset) *)
      rewrite cons_is_app.
      repeat rewrite Forall_app. repeat split.
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
        * rewrite app_nil_r, map_map, Forall2_map_1, Forall2_map_2, <- Forall2_same.
          eapply idents_for_anns'_clocknames...
        * unfold clock_of_nclock, stripname.
          rewrite app_nil_r, map_map, Forall2_map_1, Forall2_map_2, <- Forall2_same.
          eapply idents_for_anns'_incl_clocks in H3.
          apply Forall_forall; intros.
          apply in_or_app; right. apply H3.
          rewrite in_map_iff. exists x; split; auto. destruct x as [? [? [? ?]]]; auto.
      + eapply map_bind2_wc_eq in H1...
        rewrite Forall_forall in *. intros.
        eapply H0 in H12... solve_forall; repeat solve_incl.
        eapply H5 in H11. repeat solve_incl.
      + eapply H in H2... solve_forall; repeat solve_incl.
        repeat solve_incl.
      + eapply normalize_reset_wc_eq with (G:=G) (vars:=vars) in H4...
        solve_forall; repeat solve_incl.
        eapply hd_default_wc_exp.
        eapply normalize_exp_wc_exp in H2... repeat solve_incl.
  Admitted.

  Corollary normalize_exps_wc_eq : forall G vars es es' eqs' st st',
      Forall (wc_exp G (vars++st_clocks st)) es ->
      normalize_exps es st = (es', eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof with eauto.
    intros G vars es es' eqs' st st' Hwc Hnorm.
    unfold normalize_exps in Hnorm; repeat inv_bind.
    eapply map_bind2_wc_eq in H...
    solve_forall.
    eapply normalize_exp_wc_eq with (G:=G) (vars:=vars) in H1...
    + solve_forall; repeat solve_incl.
    + repeat solve_incl.
  Qed.

  Fact normalize_rhs_wc_eq : forall G vars e keep_fby es' eqs' st st',
      wc_exp G (vars++st_clocks st) e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      Forall (wc_equation G (vars++st_clocks st')) eqs'.
  Proof with eauto.
    intros G vars e keep_fby es' eqs' st st' Hwc Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (solve [eapply normalize_exp_wc_eq in Hnorm; eauto]);
      [destruct keep_fby|inv Hwc].
    - (* fby (keep) *)
      inv Hwc.
      repeat inv_bind.
      repeat rewrite Forall_app; repeat split.
      + eapply normalize_exps_wc_eq with (G:=G) (vars:=vars) in H...
        solve_forall; repeat solve_incl.
      + eapply normalize_exps_wc_eq with (G:=G) (vars:=vars) in H0...
        1,2:solve_forall; repeat solve_incl.
      + eapply normalize_fby_wc_eq in H1...
        * eapply normalize_exps_wc_exp in H...
          solve_forall; repeat solve_incl.
        * eapply normalize_exps_wc_exp in H0...
          solve_forall; repeat solve_incl.
        * admit.
        * admit.
    - (* fby (dont keep) *)
      eapply normalize_exp_wc_eq in Hnorm...
    - (* app *)
      repeat inv_bind. rewrite app_nil_r.
      eapply normalize_exps_wc_eq in H...
    - (* app (reset) *)
      repeat inv_bind.
      repeat rewrite Forall_app; repeat split.
      + eapply normalize_exps_wc_eq in H...
        solve_forall; repeat solve_incl.
      + eapply normalize_exp_wc_eq with (G:=G) (vars:=vars) in H0...
        * solve_forall. repeat solve_incl.
        * repeat solve_incl.
      + eapply normalize_reset_wc_eq in H1...
        eapply hd_default_wc_exp. eapply normalize_exp_wc_exp in H0...
        repeat solve_incl.
  Admitted.
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
