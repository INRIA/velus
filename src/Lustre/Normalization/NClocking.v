From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Omega.

From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LClocking.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

(** * Preservation of Typing through Normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type NCLOCKING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Clo : LCLOCKING Ids Op Syn)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn).

  Import Fresh Fresh.Facts Fresh.Tactics.

  (** ** wc implies wl *)

  Hint Constructors wl_exp.
  Fact wc_exp_wl_exp : forall G vars e,
      wc_exp G vars e ->
      wl_exp e.
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
      constructor...
      repeat rewrite_Forall_forall...
    - (* app (reset) *)
      constructor...
      + repeat rewrite_Forall_forall...
      + rewrite <- length_clockof_numstreams. rewrite H10. reflexivity.
  Qed.
  Hint Resolve wc_exp_wl_exp.

  Corollary Forall_wc_exp_wl_exp : forall G vars es,
      Forall (wc_exp G vars) es ->
      Forall wl_exp es.
  Proof. intros. solve_forall. Qed.
  Hint Resolve Forall_wc_exp_wl_exp.

  Fact wc_equation_wl_equation : forall G vars equ,
      wc_equation G vars equ ->
      wl_equation equ.
  Proof with eauto.
    intros G vars [xs es] [Hwc1 [Hwc2 [Hwc3 Hwc4]]].
    constructor.
    + repeat rewrite_Forall_forall...
    + repeat rewrite_Forall_forall.
      solve_length.
  Qed.
  Hint Resolve wc_equation_wl_equation.

  Fact wc_node_wl_node : forall G n,
      wc_node G n ->
      wl_node n.
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
    unfold wl_global.
    induction Hwt...
  Qed.
  Hint Resolve wc_global_wl_global.

  (** ** Preservation of clockof *)

  Fact normalize_exp_clockof : forall G vars e is_control es' eqs' st st',
      wc_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st')  ->
      clocksof es' = clockof e.
  Proof.
    intros.
    eapply normalize_exp_annot in H0; eauto.
    rewrite clocksof_without_names. rewrite clockof_without_names.
    congruence.
  Qed.

  Corollary map_bind2_normalize_exp_clocksof' :
    forall G vars is_control es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => clocksof es' = clockof e) es' es.
  Proof.
    intros.
    eapply map_bind2_normalize_exp_annots' in H0; eauto.
    repeat rewrite_Forall_forall.
    rewrite clocksof_without_names. rewrite clockof_without_names.
    erewrite H1; eauto.
  Qed.

  Corollary map_bind2_normalize_exp_clocksof :
    forall G vars is_control es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      clocksof (concat es') = clocksof es.
  Proof.
    intros.
    eapply map_bind2_normalize_exp_annots in H0; eauto.
    repeat rewrite clocksof_without_names.
    congruence.
  Qed.

  Corollary normalize_exps_clocksof : forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      normalize_exps es st = (es', eqs', st') ->
      clocksof es' = clocksof es.
  Proof.
    intros.
    eapply normalize_exps_annots in H0; eauto.
    repeat rewrite clocksof_without_names.
    congruence.
  Qed.

  Fact fby_iteexp_clockof : forall e0 e ann es' eqs' st st',
      fby_iteexp e0 e ann st = (es', eqs', st') ->
      clockof es' = [fst (snd ann)].
  Proof.
    intros.
    eapply fby_iteexp_annot in H.
    rewrite clockof_without_names. rewrite H.
    destruct ann0 as [? [? ?]]; reflexivity.
  Qed.

  Fact normalize_fby_typeof : forall inits es anns es' eqs' st st',
      length inits = length anns ->
      length es = length anns ->
      normalize_fby inits es anns st = (es', eqs', st') ->
      clocksof es' = List.map fst (List.map snd anns).
  Proof.
    intros.
    eapply normalize_fby_annot in H1; eauto.
    rewrite clocksof_without_names. rewrite H1.
    unfold without_names.
    clear H H0 H1.
    induction anns; simpl; auto.
    destruct a as [? [? ?]]; simpl. f_equal; auto.
  Qed.

  Fact normalize_rhs_typeof : forall G vars e keep_fby es' eqs' st st',
      wc_exp G vars e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      clocksof es' = clockof e.
  Proof.
    intros.
    eapply normalize_rhs_annot in H0; eauto.
    rewrite clocksof_without_names. rewrite clockof_without_names.
    congruence.
  Qed.

  Corollary normalize_rhss_typesof : forall G vars es keep_fby es' eqs' st st',
      Forall (wc_exp G vars) es ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      clocksof es' = clocksof es.
  Proof.
    intros.
    eapply normalize_rhss_annots in H0; eauto.
    repeat rewrite clocksof_without_names. congruence.
  Qed.

  (** ** A few additinal things *)

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

  Fact st_follows_clocks_incl : forall st st',
      fresh_st_follows st st' ->
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
    | H : wc_exp ?G ?l1 ?e |- wc_exp ?G ?l2 ?e =>
      eapply wc_exp_incl; [| eauto]
    (* | H : wc_equation ?G ?l1 ?eq |- wc_equation ?G ?l2 ?eq => *)
    (*   eapply wc_equation_incl; [| eauto] *)
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
      idents_for_anns anns st = (ids, st') ->
      Forall (wc_exp G (vars++st_clocks st')) (List.map (fun '(x, ann) => Evar x ann) ids).
  Proof.
    induction anns; intros ids st st' Hident;
      simpl in *; repeat inv_bind; simpl.
    - constructor.
    - destruct a as [? [? ?]]. repeat inv_bind.
      constructor; eauto.
      constructor.
      eapply fresh_ident_In in H.
      eapply idents_for_anns_st_follows in H0.
      eapply st_follows_incl in H; eauto.
      eapply in_or_app. right.
      unfold st_clocks. simpl_In. exists (x, (t, c, false)); auto.
  Qed.

  Fact map_bind2_wc_exp' {A A2 B} :
    forall G vars (k : A -> Fresh (exp * A2) B) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> fresh_st_follows st st') ->
      Forall (fun a => forall e' a2s st0 st0',
                  k a st0 = (e', a2s, st0') ->
                  fresh_st_follows st st0 ->
                  fresh_st_follows st0' st' ->
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

  Fact map_bind2_wc_exp {A A2 B} :
    forall G vars (k : A -> Fresh (list exp * A2) B) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> fresh_st_follows st st') ->
      Forall (fun a => forall es' a2s st0 st0',
                  k a st0 = (es', a2s, st0') ->
                  fresh_st_follows st st0 ->
                  fresh_st_follows st0' st' ->
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
      destruct (is_constant e0); repeat inv_bind.
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
        * repeat simpl_In...
      + repeat rewrite_Forall_forall.
        repeat simpl_length.
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

  Hint Resolve nth_In.
  Fact normalize_exp_wc_exp : forall G vars e is_control es' eqs' st st',
      wc_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) es'.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwc Hnorm;
      inv Hwc; simpl in Hnorm; repeat inv_bind.
    - (* const *) repeat constructor.
    - (* var *)
      repeat constructor...
      eapply in_or_app; auto.
    - (* var (anon) *)
      repeat constructor...
      eapply in_or_app; auto.
    - (* unop *)
      assert (length x = numstreams e) as Hlen by (eapply normalize_exp_length; eauto).
      assert (clocksof x = clockof e) as Hclockof by (eapply normalize_exp_clockof; eauto).
      repeat constructor...
      rewrite <- length_clockof_numstreams in Hlen. rewrite H3 in Hlen; simpl in Hlen.
      singleton_length. congruence.
    - (* binop *)
      assert (length x = numstreams e1) as Hlen1 by (eapply normalize_exp_length; eauto).
      assert (length x2 = numstreams e2) as Hlen2 by (eapply normalize_exp_length; eauto).
      assert (clocksof x = clockof e1) as Hclockof1 by (eapply normalize_exp_clockof; eauto).
      assert (clocksof x2 = clockof e2) as Hclockof2 by (eapply normalize_exp_clockof; eauto).
      repeat constructor...
      + eapply hd_default_wc_exp.
        eapply IHe1 in H... solve_forall. repeat solve_incl.
      + rewrite <- length_clockof_numstreams in Hlen1. rewrite H5 in Hlen1; simpl in Hlen1.
        singleton_length. congruence.
      + rewrite <- length_clockof_numstreams in Hlen2. rewrite H6 in Hlen2; simpl in Hlen2.
        singleton_length. congruence.
    - (* fby *)
      eapply idents_for_anns_wc in H9...
    - (* when *)
      rewrite Forall_map. eapply Forall2_combine'.
      assert (length (concat x1) = length (annots es)) as Hlength by (eapply map_bind2_normalize_exp_length; eauto).
      assert (clocksof (concat x1) = clocksof es) as Hclockof by (eapply map_bind2_normalize_exp_clocksof; eauto).
      rewrite clocksof_annots in H7.
      specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H0) as Hnumstreams.
      repeat rewrite_Forall_forall; solve_length.
      repeat constructor; simpl.
      + eapply map_bind2_wc_exp in H0...
        * rewrite Forall_forall in H0. eapply H0... eapply nth_In; solve_length.
        * rewrite Forall_forall; intros...
          eapply H in H3...
          solve_forall. repeat solve_incl.
      + eapply in_or_app...
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
        rewrite <- clocksof_annots. unfold clocksof. rewrite flat_map_concat_map.
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
        repeat constructor; simpl.
        * eapply map_bind2_wc_exp in H1...
          -- rewrite Forall_forall in H1. eapply H1... eapply nth_In; solve_length.
          -- rewrite Forall_forall; intros...
             eapply H in H14...
             solve_forall. repeat solve_incl.
        * eapply map_bind2_wc_exp in H2...
          -- rewrite Forall_forall in H2. eapply H2... eapply nth_In; solve_length.
          -- rewrite Forall_forall; intros...
             eapply H0 in H14...
             solve_forall. repeat solve_incl.
        * eapply in_or_app. left. rewrite <- H12...
        * rewrite app_nil_r.
          rewrite Forall_forall; intros.
          eapply H8.
          repeat simpl_nth; repeat simpl_length.
          assert (length (clockof (nth n (concat x3) a1)) = 1).
          { rewrite <- Hlen1 in H3. eapply nth_In in H3. eapply Hnums1 in H3.
            rewrite length_clockof_numstreams... }
          repeat singleton_length. destruct x5; try omega; subst.
          rewrite concat_length_map_nth with (db:=x1) in Hsingl; solve_length. inv Hsingl.
          2: (solve_forall; rewrite length_clockof_numstreams; eauto).
          rewrite <- clocksof_annots. unfold clocksof. rewrite flat_map_concat_map.
          apply nth_In. rewrite <- Hlen1 in H3.
          rewrite concat_length_1...
          solve_forall; rewrite length_clockof_numstreams...
        * rewrite app_nil_r.
          rewrite Forall_forall; intros.
          eapply H9.
          repeat simpl_nth; repeat simpl_length.
          assert (length (clockof (nth n (concat x6) a2)) = 1).
          { rewrite <- Hlen2 in H3. eapply nth_In in H3. eapply Hnums2 in H3.
            rewrite length_clockof_numstreams... }
          repeat singleton_length. destruct x5; try omega; subst.
          rewrite concat_length_map_nth with (db:=x1) in Hsingl; solve_length. inv Hsingl.
          2: (solve_forall; rewrite length_clockof_numstreams; eauto).
          rewrite <- clocksof_annots. unfold clocksof. rewrite flat_map_concat_map.
          apply nth_In. rewrite <- Hlen2 in H3.
          rewrite concat_length_1...
          solve_forall; rewrite length_clockof_numstreams...
        * rewrite app_nil_r. rewrite <- Hlen1 in H3.
          eapply nth_In in H3. eapply Hnums1 in H3.
          rewrite length_clockof_numstreams...
        * rewrite app_nil_r. rewrite <- Hlen2 in H3.
          eapply nth_In in H3. eapply Hnums2 in H3.
          rewrite length_clockof_numstreams...
      + (* exp *) eapply idents_for_anns_wc in H3...
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
        repeat constructor; simpl.
        * eapply IHe in H1...
          inv H1. repeat solve_incl.
        * eapply map_bind2_wc_exp in H2...
          -- rewrite Forall_forall in H2. eapply H2... eapply nth_In; solve_length.
          -- rewrite Forall_forall; intros...
             eapply H in H16...
             solve_forall. repeat solve_incl.
        * eapply map_bind2_wc_exp in H3...
          -- rewrite Forall_forall in H3. eapply H3... eapply nth_In; solve_length.
          -- rewrite Forall_forall; intros...
             eapply H0 in H16...
             solve_forall. repeat solve_incl.
        * congruence.
        * rewrite app_nil_r.
          rewrite Forall_forall; intros.
          eapply H9.
          repeat simpl_nth; repeat simpl_length.
          assert (length (clockof (nth n (concat x5) a1)) = 1).
          { rewrite <- Hlen1 in H4. eapply nth_In in H4. eapply Hnums1 in H4.
            rewrite length_clockof_numstreams... }
          repeat singleton_length. destruct x2; try omega; subst.
          rewrite concat_length_map_nth with (db:=x) in Hsingl; solve_length. inv Hsingl.
          2: (solve_forall; rewrite length_clockof_numstreams; eauto).
          rewrite <- clocksof_annots. unfold clocksof. rewrite flat_map_concat_map.
          apply nth_In. rewrite <- Hlen1 in H4.
          rewrite concat_length_1...
          solve_forall; rewrite length_clockof_numstreams...
        * rewrite app_nil_r.
          rewrite Forall_forall; intros.
          eapply H10.
          repeat simpl_nth; repeat simpl_length.
          assert (length (clockof (nth n (concat x8) a2)) = 1).
          { rewrite <- Hlen2 in H4. eapply nth_In in H4. eapply Hnums2 in H4.
            rewrite length_clockof_numstreams... }
          repeat singleton_length. destruct x2; try omega; subst.
          rewrite concat_length_map_nth with (db:=x) in Hsingl; solve_length. inv Hsingl.
          2: (solve_forall; rewrite length_clockof_numstreams; eauto).
          rewrite <- clocksof_annots. unfold clocksof. rewrite flat_map_concat_map.
          apply nth_In. rewrite <- Hlen2 in H4.
          rewrite concat_length_1...
          solve_forall; rewrite length_clockof_numstreams...
        * rewrite app_nil_r. rewrite <- Hlen1 in H4.
          eapply nth_In in H4. eapply Hnums1 in H4.
          rewrite length_clockof_numstreams...
        * rewrite app_nil_r. rewrite <- Hlen2 in H4.
          eapply nth_In in H4. eapply Hnums2 in H4.
          rewrite length_clockof_numstreams...
      + (* exp *) eapply idents_for_anns_wc in H4...
    - (* app *)
      eapply idents_for_anns_wc in H2...
    - (* app (reset) *)
      eapply idents_for_anns_wc in H3...
  Qed.

  Corollary normalize_exps_wc_exp : forall G vars es es' eqs' st st',
      Forall (wc_exp G vars) es ->
      normalize_exps es st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) es'.
  Proof.
    intros G vars es es' eqs' st st' Hwt Hmap.
    unfold normalize_exps in Hmap; repeat inv_bind.
    eapply map_bind2_wc_exp in H; eauto.
    solve_forall. eapply normalize_exp_wc_exp in H1; eauto.
    solve_forall. repeat solve_incl.
  Qed.

  Fact normalize_rhs_wc_exp : forall G vars e keep_fby es' eqs' st st',
      wc_exp G vars e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      Forall (wc_exp G (vars++st_clocks st')) es'.
  Proof with eauto.
    intros G vars e keep_fby es' eqs' st st' Hwc Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (solve [eapply normalize_exp_wc_exp in Hnorm; eauto]); inv Hwc.
    - (* fby *)
      destruct keep_fby.
      + repeat inv_bind.
        admit.
      + eapply normalize_exp_wc_exp in Hnorm...
    - (* app *)
      repeat inv_bind.
      repeat constructor.
      (* Donner sub explicitement : Il faut modifier la sub de base pour faire coincider les cas qui ont change dans (nclocksof e) *)
      eapply wc_Eapp with
          (bck:=bck)
          (sub:=sub_set (List.combine (List.map fst (n_in n))
                                      (List.map snd (nclocksof x))) sub);
        eauto.
      + eapply normalize_exps_wc_exp in H...
      + admit.
      + admit.
  Admitted.
End NCLOCKING.

Module NClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Clo : LCLOCKING Ids Op Syn)
       (Norm : NORMALIZATION Ids Op OpAux Syn)
       <: NCLOCKING Ids Op OpAux Syn Clo Norm.
  Include NCLOCKING Ids Op OpAux Syn Clo Norm.
End NClockingFun.
