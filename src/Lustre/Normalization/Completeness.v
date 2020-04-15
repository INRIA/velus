From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import Omega.

From Velus Require Import Common Ident.
From Velus Require Import Operators.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

(** * Completeness of the normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type COMPLETENESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Typ : LTYPING Ids Op Syn)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn Typ).

  Import Fresh Fresh.Fresh Facts Tactics.

  (** Describe normalized nodes *)

  Inductive normalized_lexp : exp -> Prop :=
  | normalized_Econst : forall c, normalized_lexp (Econst c)
  | normalized_Evar : forall x ty cl, normalized_lexp (Evar x (ty, cl))
  | normalized_Eunop : forall op e1 ty cl,
      normalized_lexp e1 ->
      normalized_lexp (Eunop op e1 (ty, cl))
  | normalized_Ebinop : forall op e1 e2 ty cl,
      normalized_lexp e1 ->
      normalized_lexp e2 ->
      normalized_lexp (Ebinop op e1 e2 (ty, cl))
  | normalized_Ewhen : forall e x b ty cl,
      normalized_lexp e ->
      normalized_lexp (Ewhen [e] x b ([ty], cl)).

  Inductive normalized_cexp : exp -> Prop :=
  | normalized_Emerge : forall x et ef ty cl,
      normalized_cexp et ->
      normalized_cexp ef ->
      normalized_cexp (Emerge x [et] [ef] ([ty], cl))
  | normalized_Eite : forall e et ef ty cl,
      normalized_lexp e ->
      normalized_cexp et ->
      normalized_cexp ef ->
      normalized_cexp (Eite e [et] [ef] ([ty], cl))
    | normalized_lexp_cexp : forall e,
      normalized_lexp e ->
      normalized_cexp e.

  Inductive is_constant : exp -> Prop :=
  | constant_Econst : forall c,
      is_constant (Econst c)
  | constant_Ewhen : forall e x b ty cl,
      is_constant e ->
      is_constant (Ewhen [e] x b ([ty], cl)).

  Inductive normalized_equation : PS.t -> equation -> Prop :=
  | normalized_eq_Eapp : forall out xs f es lann,
      Forall normalized_lexp es ->
      normalized_equation out (xs, [Eapp f es None lann])
  | normalized_eq_Eapp_reset : forall out xs f es x ty cl lann,
      Forall normalized_lexp es ->
      normalized_equation out (xs, [Eapp f es (Some (Evar x (ty, cl))) lann])
  | normalized_eq_Efby : forall out x e0 e ann,
      ~PS.In x out ->
      is_constant e0 ->
      normalized_lexp e ->
      normalized_equation out ([x], [Efby [e0] [e] [ann]])
  | normalized_eq_cexp : forall out x e,
      normalized_cexp e ->
      normalized_equation out ([x], [e]).

  Definition normalized_node (n : node) :=
    Forall (normalized_equation (ps_from_list (List.map fst (n_out n)))) (n_eqs n).

  Hint Constructors is_constant normalized_lexp normalized_cexp normalized_equation.

  Fact normalized_lexp_numstreams : forall e,
      normalized_lexp e ->
      numstreams e = 1.
  Proof.
    induction e; intros Hnorm; inv Hnorm; reflexivity.
  Qed.

  Fact normalized_cexp_numstreams : forall e,
      normalized_cexp e ->
      numstreams e = 1.
  Proof.
    induction e; intros Hnorm; inv Hnorm;
      try apply normalized_lexp_numstreams in H; auto.
  Qed.

  Fact normalized_lexp_hd_default : forall es,
      Forall normalized_lexp es ->
      normalized_lexp (hd_default es).
  Proof.
    intros es Hf.
    destruct es; simpl.
    - constructor.
    - inv Hf; auto.
  Qed.

  Fact map_bind2_normalized_lexp {A A2} :
    forall (k : A -> FreshAnn ((list exp) * A2)) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      Forall (fun a => forall es' a2s st st',
                  k a st = (es', a2s, st') ->
                  Forall normalized_lexp es') a ->
      Forall normalized_lexp (concat es').
  Proof.
    intros k a eqs' a2s st st' Hmap Hf.
    apply map_bind2_values in Hmap.
    induction Hmap; simpl in *.
    - constructor.
    - destruct H as [? [? H]]. inv Hf.
      rewrite Forall_app.
      split; eauto.
  Qed.

  Fact map_bind2_normalized_cexp {A A2} :
    forall (k : A -> FreshAnn ((list exp) * A2)) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      Forall (fun a => forall es' a2s st st',
                  k a st = (es', a2s, st') ->
                  Forall normalized_cexp es') a ->
      Forall normalized_cexp (concat es').
  Proof.
    intros k a eqs' a2s st st' Hmap Hf.
    apply map_bind2_values in Hmap.
    induction Hmap; simpl in *.
    - constructor.
    - destruct H as [? [? H]]. inv Hf.
      rewrite Forall_app.
      split; eauto.
  Qed.

  Fact map_bind2_normalized_eq {A A1} :
    forall (k : A -> FreshAnn (A1 * (list equation))) a out a1s eqs' st st',
      map_bind2 k a st = (a1s, eqs', st') ->
      (forall o, PS.In o out -> Pos.lt o (smallest_ident st)) ->
      (forall a a1s eqs' st st', k a st = (a1s, eqs', st') -> fresh_st_follows st st') ->
      Forall (fun a => forall a1s eqs' st st',
                  k a st = (a1s, eqs', st') ->
                  (forall o, PS.In o out -> Pos.lt o (smallest_ident st)) ->
                  Forall (normalized_equation out) eqs') a ->
      Forall (normalized_equation out) (concat eqs').
  Proof.
    induction a; intros out a1s eqs' st st' Hmap Hlt Hfollows Hf;
      simpl in *; repeat inv_bind.
    - constructor.
    - inv Hf. simpl.
      rewrite Forall_app.
      split; eauto.
      eapply IHa; eauto.
      clear IHa H3 H4.
      intros o Hin. eapply Pos.lt_le_trans; eauto.
  Qed.

  Fact add_whens_is_constant : forall ty cl e,
    is_constant e ->
    is_constant (add_whens e ty cl).
  Proof.
    induction cl; intros e Hcons; simpl.
    - assumption.
    - constructor. eauto.
  Qed.

  Fact add_whens_normalized_lexp : forall ty cl e,
      normalized_lexp e ->
      normalized_lexp (add_whens e ty cl).
  Proof.
    induction cl; intros e Hadd; simpl in Hadd.
    - assumption.
    - constructor. eauto.
  Qed.

  Hint Resolve in_combine_l in_combine_r.
  Hint Resolve normalized_lexp_hd_default.

  Lemma normalize_exp_normalized_lexp : forall e es' eqs' st st',
      normalize_exp false e st = (es', eqs', st') ->
      Forall normalized_lexp es'.
  Proof with eauto.
    induction e using exp_ind2; intros es' eqs' st st' Hnorm;
      simpl in Hnorm; repeat inv_bind; repeat constructor.
    - (* var *)
      destruct a...
    - (* unop *)
      destruct a...
    - (* binop *)
      destruct a. constructor...
    - (* fby *)
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a0...
    - (* when *)
      destruct a. repeat inv_bind.
      apply map_bind2_normalized_lexp in H0...
      repeat rewrite_Forall_forall.
      repeat simpl_In...
    - (* merge *)
      destruct a. repeat inv_bind.
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a...
    - (* ite *)
      destruct a. repeat inv_bind.
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a...
    - (* app *)
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a0...
  Qed.
  Hint Resolve normalize_exp_normalized_lexp.

  Lemma normalize_exp_normalized_cexp : forall e es' eqs' st st',
      normalize_exp true e st = (es', eqs', st') ->
      Forall normalized_cexp es'.
  Proof with eauto.
    induction e using exp_ind2; intros es' eqs' st st' Hnorm;
      simpl in Hnorm; repeat inv_bind; repeat constructor.
    - (* var *)
      destruct a...
    - (* unop *)
      destruct a...
    - (* binop *)
      destruct a. constructor...
    - (* fby *)
      solve_forall.
      repeat simpl_In. destruct a0...
    - (* when *)
      destruct a. repeat inv_bind.
      apply map_bind2_normalized_lexp in H0; solve_forall.
      repeat rewrite_Forall_forall.
      repeat simpl_In...
    - (* merge *)
      destruct a. repeat inv_bind.
      apply map_bind2_normalized_cexp in H1; solve_forall.
      apply map_bind2_normalized_cexp in H2; solve_forall.
      repeat rewrite_Forall_forall.
      repeat simpl_In...
    - (* ite *)
      destruct a. repeat inv_bind.
      apply normalize_exp_normalized_lexp in H1.
      apply map_bind2_normalized_cexp in H2; solve_forall.
      apply map_bind2_normalized_cexp in H3; solve_forall.
      repeat rewrite_Forall_forall.
      repeat simpl_In.
      constructor...
      apply normalized_lexp_hd_default. solve_forall.
    - (* app *)
      solve_forall.
      repeat simpl_In. destruct a0...
  Qed.

  Fact init_var_for_clock_normalized_eq : forall cl id eqs' out st st',
      init_var_for_clock cl st = (id, eqs', st') ->
      (forall o, PS.In o out -> Pos.lt o (smallest_ident st)) ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros cl id eqs' out st st' Hinit Hlt.
    unfold init_var_for_clock in Hinit.
    destruct (find _ _).
    - destruct p. inv Hinit. constructor.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit. repeat constructor.
      + simpl in Hlt.
        intros contra.
        apply Hlt in contra.
        specialize (fresh_ident_st_follows _ _ _ _ Hfresh) as Hfollows. apply st_follows_smallest in Hfollows.
        apply fresh_ident_In in Hfresh.
        assert (In id (st_ids st')) as Hin by (rewrite <- st_anns_ids_In; eexists; eauto).
        eapply smallest_ident_In in Hin.
        apply (Pos.lt_irrefl id).
        eapply Pos.lt_le_trans; eauto. etransitivity; eauto.
      + apply add_whens_is_constant. auto.
      + apply add_whens_normalized_lexp. auto.
  Qed.

  Fact fby_iteexp_normalized_eq : forall e0 e a e' eqs' out st st',
      fby_iteexp e0 e a st = (e', eqs', st') ->
      normalized_lexp e ->
      (forall o, PS.In o out -> Pos.lt o (smallest_ident st)) ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros e0 e [ty cl] e' eqs' out st st' Hfby He Hlt.
    specialize (fby_iteexp_spec e0 e ty cl) as [[? [? Hspec]]|Hspec]; subst;
      rewrite Hspec in Hfby; clear Hspec; repeat inv_bind.
    - constructor.
    - constructor.
      + constructor; auto.
        intro contra.
        apply Hlt in contra; clear Hlt.
        assert (fresh_st_follows st st') as Hfollows by (etransitivity; eauto).
        apply fresh_ident_In in H0.
        assert (In x2 (st_ids st')) by (unfold st_ids, idty; simpl_In; exists (x2, (ty, cl, false)); eauto).
        apply smallest_ident_In in H1.
        apply (Pos.lt_irrefl x2).
        eapply Pos.lt_le_trans; eauto. etransitivity; eauto.
      + eapply init_var_for_clock_normalized_eq in H; eauto.
  Qed.

  Fact normalize_fby_normalized_eq : forall e0s es anns es' eqs' out st st',
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall normalized_lexp es ->
      (forall o, PS.In o out -> Pos.lt o (smallest_ident st)) ->
      Forall (normalized_equation out) eqs'.
  Proof with eauto.
    intros e0s es anns es' eqs' out st st' Hnorm Hf Hlt.
    unfold normalize_fby in Hnorm.
    repeat inv_bind.
    - eapply map_bind2_normalized_eq...
      + intros. destruct a as [[e0 e] [ty cl]].
        eapply fby_iteexp_st_follows...
      + rewrite Forall_forall; intros.
        destruct x as [[e0 e] [ty cl]].
        eapply fby_iteexp_normalized_eq in H1...
        rewrite Forall_forall in Hf...
  Qed.

  Lemma normalize_exp_normalized_eq : forall e is_control es' eqs' out st st',
      normalize_exp is_control e st = (es', eqs', st') ->
      (forall o, PS.In o out -> Pos.lt o (smallest_ident st)) ->
      Forall (normalized_equation out) eqs'.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' out st st' Hnorm Hlt;
      simpl in Hnorm; repeat inv_bind; repeat constructor.
    - (* unop *) eauto.
    - (* binop *)
      apply Forall_app. split...
      apply normalize_exp_st_follows in H.
      assert (forall o, PS.In o out -> (o < smallest_ident x1)%positive)...
      intros. eapply Pos.lt_le_trans...
    - (* fby *)
      repeat rewrite Forall_app. repeat split.
      + assert (fresh_st_follows st x1) as Hfollows1 by (eapply map_bind2_st_follows; eauto; solve_forall).
        assert (fresh_st_follows x1 x4) as Hfollows2 by (eapply map_bind2_st_follows; eauto; solve_forall).
        assert (fresh_st_follows x4 x7) as Hfollows3 by eauto.
        apply map_bind2_normalized_lexp in H1; [| solve_forall].
        apply map_bind2_normalized_lexp in H2; [| solve_forall].
        clear H H0.
        unfold normalize_fby in H3; repeat inv_bind. apply map_bind2_values in H.
        repeat rewrite_Forall_forall.
        repeat simpl_In.
        apply In_nth with (d:=(hd_default [])) in H6; destruct H6 as [n [? ?]].
        replace (length x5) in H6.
        specialize (H3 (e, e, a0) (hd_default []) [] _ _ _ _ H6 eq_refl eq_refl eq_refl). destruct H3 as [? [? H3]].
        destruct (nth n _) as [[e0 e'] [ty cl]] eqn:Hnth.
        specialize (fby_iteexp_spec e0 e' ty cl) as [[? [? Hspec]]|Hspec]; subst;
          rewrite Hspec in H3; clear Hspec; repeat inv_bind.
        * simpl in *. rewrite <- H8. repeat constructor.
          -- intro contra. apply Hlt in contra.
             specialize (idents_for_anns_st_follows _ _ _ _ H4) as Hfollows.
             apply idents_for_anns_incl in H4.
             apply H4 in H5.
             assert (In i (st_ids st')) as Hin.
             { unfold st_ids, idty in *. repeat simpl_In. inv H3.
               exists (i, (a0, b)); auto. }
             apply smallest_ident_In in Hin.
             apply (Pos.lt_irrefl i).
             eapply Pos.lt_le_trans; eauto.
             repeat (etransitivity; eauto).
          -- eapply nth_In in H6; rewrite Hnth in H6...
        * repeat constructor.
          eapply nth_In in H6; rewrite Hnth in H6...
      + eapply map_bind2_normalized_eq in H1... solve_forall.
      + eapply map_bind2_normalized_eq in H2...
        * eapply map_bind2_st_follows in H1; solve_forall.
          intros. eapply Pos.lt_le_trans...
        * solve_forall.
      + eapply normalize_fby_normalized_eq in H3; eauto.
        * eapply map_bind2_normalized_lexp; eauto. solve_forall.
        * eapply map_bind2_st_follows in H1; solve_forall.
          eapply map_bind2_st_follows in H2; solve_forall.
          intros. eapply Pos.lt_le_trans; eauto.
          etransitivity; eauto.
    - (* when *)
      destruct a. repeat inv_bind.
      eapply map_bind2_normalized_eq in H0; eauto. solve_forall.
    - (* merge *)
      destruct a; destruct is_control; repeat inv_bind;
        repeat rewrite Forall_app; repeat split.
      1,2,4,5: (eapply map_bind2_normalized_eq; eauto; solve_forall).
      1,2: (eapply map_bind2_st_follows in H1; eauto; solve_forall;
            intros; eapply Pos.lt_le_trans; eauto).
      rewrite Forall_forall; intros [? ?] Hin. rewrite map_map in Hin; simpl in Hin.
      repeat simpl_In.
      constructor. constructor.
      + eapply map_bind2_normalized_cexp in H1; eauto; solve_forall.
        rewrite Forall_forall in H1...
        eapply normalize_exp_normalized_cexp...
      + eapply map_bind2_normalized_cexp in H2; eauto; solve_forall.
        rewrite Forall_forall in H2...
        eapply normalize_exp_normalized_cexp...
    - (* ite *)
      destruct a; destruct is_control; repeat inv_bind;
        repeat rewrite Forall_app; repeat split.
      1,5: (eapply IHe; eauto).
      1,2,4,5: (eapply map_bind2_normalized_eq; eauto; solve_forall).
      1,2,3,4: (eapply normalize_exp_st_follows in H1; eauto;
                intros; eapply Pos.lt_le_trans; eauto).
      1,2: (eapply map_bind2_st_follows in H2; eauto; solve_forall;
            etransitivity; eauto).
      rewrite Forall_forall; intros [? ?] Hin. rewrite map_map in Hin; simpl in Hin.
      repeat simpl_In.
      constructor. constructor.
      + eapply normalized_lexp_hd_default.
        eapply normalize_exp_normalized_lexp...
      + eapply map_bind2_normalized_cexp in H2; eauto; solve_forall.
        rewrite Forall_forall in H2...
        eapply normalize_exp_normalized_cexp...
      + eapply map_bind2_normalized_cexp in H3; eauto; solve_forall.
        rewrite Forall_forall in H3...
        eapply normalize_exp_normalized_cexp...
    - (* app *)
      eapply map_bind2_normalized_lexp in H2; eauto; solve_forall.
      destruct ro; repeat inv_bind.
      + specialize (normalize_reset_spec (hd_default x2)) as [[? [? [? Hspec]]]|Hspec]; subst;
          rewrite Hspec in H4; clear Hspec; repeat inv_bind.
        * destruct x0...
        * destruct (hd _); simpl in *; repeat inv_bind...
      + constructor...
    - (* app (auxiliary equations) *)
      rewrite Forall_app. split.
      + destruct ro; repeat inv_bind; try constructor.
        eapply Forall_app. split...
        specialize (normalize_reset_spec (hd_default x2)) as [[? [? [? Hspec]]]|Hspec]; subst;
          rewrite Hspec in H4; clear Hspec; repeat inv_bind...
        destruct (hd _); simpl in *; repeat inv_bind.
        repeat constructor. apply normalized_lexp_hd_default...
      + destruct ro; repeat inv_bind;
          eapply map_bind2_normalized_eq; eauto; solve_forall.
        eapply normalize_exp_st_follows in H1.
        eapply normalize_reset_st_follows in H4.
        intros. eapply Pos.lt_le_trans; eauto. etransitivity; eauto.
  Qed.
  Hint Resolve normalize_exp_normalized_eq.

  Corollary normalize_exps_normalized_lexp: forall es es' eqs' st st',
      normalize_exps es st = (es', eqs', st') ->
      Forall normalized_lexp es'.
  Proof.
    intros es es' eqs' st st' Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    apply map_bind2_normalized_lexp in H; auto.
    rewrite Forall_forall; intros; eauto.
  Qed.
  Hint Resolve normalize_exps_normalized_lexp.

  Corollary normalize_exps_normalized_eq : forall es es' eqs' out st st',
      normalize_exps es st = (es', eqs', st') ->
      (forall o, PS.In o out -> Pos.lt o (smallest_ident st)) ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros es es' eqs' out st st' Hnorm Hlt.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_normalized_eq in H; eauto.
    solve_forall.
  Qed.
  Hint Resolve normalize_exps_normalized_eq.

  (* Intermediary predicate for normalized rhs *)
  Inductive normalized_rhs : bool -> exp -> Prop :=
  | normalized_rhs_Eapp : forall f es lann keep_fby,
      Forall normalized_lexp es ->
      normalized_rhs keep_fby (Eapp f es None lann)
  | normalized_rhs_Eapp_reset : forall f es x ty cl lann keep_fby,
      Forall normalized_lexp es ->
      normalized_rhs keep_fby (Eapp f es (Some (Evar x (ty, cl))) lann)
  | normalized_rhs_Efby : forall e0 e ann,
      is_constant e0 ->
      normalized_lexp e ->
      normalized_rhs true (Efby [e0] [e] [ann])
  | normalized_rhs_cexp : forall e keep_fby,
      normalized_cexp e ->
      normalized_rhs keep_fby e.
  Hint Constructors normalized_rhs.

  Fact normalize_rhs_normalized_rhs : forall e keep_fby es' eqs' st st',
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      Forall (normalized_rhs keep_fby) es'.
  Proof with eauto.
    intros e keep_fby es' eqs' st st' Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (apply normalize_exp_normalized_cexp in Hnorm; solve_forall; auto).
    - (* fby *)
      destruct keep_fby; try (apply normalize_exp_normalized_cexp in Hnorm; solve_forall; auto).
      repeat inv_bind.
      apply normalize_exps_normalized_lexp in H.
      apply normalize_exps_normalized_lexp in H0.
      unfold normalize_fby in H1. repeat inv_bind.
      apply map_bind2_values in H1.
      repeat rewrite_Forall_forall.
      apply In_nth with (d:=(hd_default [])) in H4; destruct H4 as [n [Hn Hnth]].
      replace (length es') in Hn.
      specialize (H3 (x5, x5, (bool_type, (Cbase, None))) (hd_default []) [] _ _ _ _ Hn eq_refl eq_refl eq_refl).
      destruct H3 as [? [? H3]]. destruct (nth n _ _) as [[e0 e] [ty cl]] eqn:Hnth'.
      specialize (fby_iteexp_spec e0 e ty cl) as [[? [? Hspec]]|Hspec]; subst;
        rewrite Hspec in H3; clear Hspec; repeat inv_bind; simpl in *.
      + rewrite <- H5. repeat constructor.
        eapply nth_In in Hn. rewrite Hnth' in Hn...
      + repeat constructor.
        eapply nth_In in Hn. rewrite Hnth' in Hn...
    - (* app *)
      destruct o; repeat inv_bind...
      specialize (normalize_reset_spec (hd_default x4)) as [[? [[? ?] [? Hspec]]]|Hspec]; subst;
        rewrite Hspec in H1; clear Hspec; repeat inv_bind...
      destruct (hd _) as [? [ty cl]]; simpl in H1. repeat inv_bind...
  Qed.

  Corollary normalize_rhss_normalized_rhs : forall es keep_fby es' eqs' st st',
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      Forall (normalized_rhs keep_fby) es'.
  Proof with eauto.
    intros es keep_fby es' eqs' st st' Hnorm.
    unfold normalize_rhss in Hnorm. repeat inv_bind.
    eapply map_bind2_values in H.
    induction H; simpl; try constructor.
    apply Forall_app. split; auto.
    destruct H as [? [? H]].
    eapply normalize_rhs_normalized_rhs; eauto.
  Qed.

  Fact normalize_rhs_normalized_eq : forall e keep_fby es' eqs' out st st',
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      (forall o, PS.In o out -> Pos.lt o (smallest_ident st)) ->
      Forall (normalized_equation out) eqs'.
  Proof with eauto.
    intros e keep_fby es' eqs' out st st' Hnorm Hlt.
    destruct e; unfold normalize_rhs in Hnorm;
    try (eapply normalize_exp_normalized_eq in Hnorm; eauto).
    - (* fby *)
      destruct keep_fby; try (eapply normalize_exp_normalized_eq in Hnorm; eauto).
      simpl in Hnorm. repeat inv_bind.
      repeat rewrite Forall_app. repeat split...
      + eapply normalize_exps_normalized_eq; eauto; solve_forall.
        eapply normalize_exps_st_follows in H;
        intros. eapply Pos.lt_le_trans...
      + unfold normalize_fby in H1. repeat inv_bind.
        eapply map_bind2_normalized_eq in H1; eauto; solve_forall.
        * eapply normalize_exps_st_follows in H.
          eapply normalize_exps_st_follows in H0.
          intros. eapply Pos.lt_le_trans... etransitivity...
        * intros. destruct a as [[e0 e] ann]. apply fby_iteexp_st_follows in H2...
        * repeat rewrite_Forall_forall. destruct x5 as [[e0 e] [ty cl]].
          specialize (fby_iteexp_spec e0 e ty cl) as [[? [? Hspec]]|Hspec]; subst;
            rewrite Hspec in H3; clear Hspec; repeat inv_bind; inv H5.
          -- econstructor...
             ++ intro contra. apply H4 in contra.
                specialize (fresh_ident_In _ _ _ _ H6) as Hin.
                apply fresh_ident_st_follows in H6.
                apply init_var_for_clock_st_follows in H3.
                assert (In x10 (st_ids st'0)).
                { unfold st_ids, idty. repeat simpl_In. exists (x10, (ty, cl, false))... }
                apply smallest_ident_In in H5.
                eapply (Pos.lt_irrefl x10).
                eapply Pos.lt_le_trans...
                repeat (etransitivity; eauto).
             ++ eapply normalize_exps_normalized_lexp in H0. rewrite Forall_forall in H0...
          -- eapply init_var_for_clock_normalized_eq in H3; intros...
             rewrite Forall_forall in *...
    - (* app *)
      simpl in Hnorm. destruct o; repeat inv_bind...
      rewrite <- app_assoc.
      repeat rewrite Forall_app. repeat split...
      specialize (normalize_reset_spec (hd_default x4)) as [[? [? [? Hspec]]]|Hspec]; subst;
        rewrite Hspec in H1; clear Hspec; repeat inv_bind.
      + constructor.
      + destruct (hd _ _); simpl in H1.
        repeat inv_bind. repeat constructor.
        apply normalized_lexp_hd_default...
      + eapply normalize_exps_normalized_eq in H0; eauto.
        apply normalize_exp_st_follows in H.
        apply normalize_reset_st_follows in H1.
        intros. eapply Pos.lt_le_trans... etransitivity...
  Qed.
  Hint Resolve normalize_rhs_normalized_eq.

  Corollary normalize_rhss_normalized_eq : forall es keep_fby es' eqs' out st st',
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      (forall o, PS.In o out -> Pos.lt o (smallest_ident st)) ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros es keep_fby es' eqs' out st st' Hnorm Hlt.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_normalized_eq in H; eauto.
    rewrite Forall_forall; intros; eauto.
  Qed.
  Hint Resolve normalize_rhss_normalized_eq.

  Lemma normalize_equation_normalized_eq : forall eq to_cut eqs' out st st',
      wl_equation eq ->
      normalize_equation to_cut eq st = (eqs', st') ->
      (forall o, PS.In o out -> Pos.lt o (smallest_ident st)) ->
      PS.Subset out to_cut ->
      Forall (normalized_equation out) eqs'.
  Proof with eauto.
    intros [xs es] to_cut eqs' out st st' Hwl Hnorm Hlt Hincl.
    unfold normalize_equation in Hnorm.
    repeat inv_bind.
    remember (negb (existsb (fun x => PS.mem x to_cut) xs)) as keep_fby.
    assert (keep_fby = true -> Forall (fun x => ~PS.In x out) xs) as Hin.
    { intro Hkeep; subst.
      rewrite Bool.negb_true_iff in Hkeep. rewrite existsb_Forall in Hkeep.
      rewrite forallb_Forall in Hkeep. solve_forall.
      rewrite Bool.negb_true_iff in H0. apply PSE.mem_4 in H0.
      intro contra. apply Hincl in contra. contradiction.
    }
    clear Heqkeep_fby.
    rewrite Forall_app. split.
    - assert (length xs = length (annots x)) as Hlen.
      { destruct Hwl as [Hwl1 Hwl2].
        eapply normalize_rhss_annots in H; eauto.
        congruence. } clear Hwl.
      eapply normalize_rhss_normalized_rhs in H; eauto.
      revert xs Hin Hlen.
      induction H; intros xs Hin Hlen; constructor.
      + inv H...
        * destruct xs; simpl in *; try omega.
          constructor...
          specialize (Hin eq_refl). inv Hin. auto.
        * simpl in Hlen. rewrite app_length in Hlen.
          rewrite length_annot_numstreams in Hlen.
          specialize (normalized_cexp_numstreams _ H1) as Hlen'.
          rewrite Hlen' in *. simpl.
          destruct xs... simpl in Hlen. omega.
      + eapply IHForall.
        * intro Hkeep. apply Hin in Hkeep.
          apply Forall_skipn...
        * rewrite skipn_length.
          rewrite Hlen. simpl. rewrite app_length.
          rewrite length_annot_numstreams. omega.
    - eapply normalize_rhss_normalized_eq in H; eauto.
  Qed.

  Corollary normalize_equations_normalized_eq : forall eqs to_cut eqs' out st st',
      Forall wl_equation eqs ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      (forall o, PS.In o out -> Pos.lt o (smallest_ident st)) ->
      PS.Subset out to_cut ->
      Forall (normalized_equation out) eqs'.
  Proof.
    induction eqs; intros to_cut eqs' out st st' Hf Hnorm Hlt Hincl;
      simpl in Hnorm; repeat inv_bind.
    - constructor.
    - inv Hf. apply Forall_app; split.
      + eapply normalize_equation_normalized_eq; eauto.
      + eapply normalize_equation_st_follows in H.
        eapply IHeqs; eauto. solve_forall.
        intros. eapply Pos.lt_le_trans; eauto.
  Qed.

  Lemma normalize_node_normalized_node : forall n to_cut Hwl,
      normalized_node (normalize_node to_cut n Hwl).
  Proof.
    intros n to_cut Hwl.
    unfold normalize_node.
    unfold normalized_node; simpl.
    eapply normalize_equations_normalized_eq; eauto.
    - apply surjective_pairing.
    - intros o HIn. rewrite ps_from_list_In in HIn.
      specialize (first_unused_ident_gt n _ eq_refl) as Hgt.
      unfold used_idents in Hgt. repeat rewrite map_app in Hgt.
      repeat rewrite Forall_app in Hgt.
      destruct Hgt as [_ [_ [_ Hgt]]].
      rewrite Forall_forall in Hgt.
      rewrite init_st_smallest. auto.
    - apply PSP.union_subset_2.
  Qed.

End COMPLETENESS.

Module CompletenessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn)
       (Norm : NORMALIZATION Ids Op OpAux Syn Typ)
       <: COMPLETENESS Ids Op OpAux Syn Typ Norm.
  Include COMPLETENESS Ids Op OpAux Syn Typ Norm.
End CompletenessFun.
