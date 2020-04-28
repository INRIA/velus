From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import Omega.
Require Import ProofIrrelevance.

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
       (Import Norm : NORMALIZATION Ids Op OpAux Syn).

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

  Definition normalized_global (G : global) := Forall normalized_node G.

  Hint Constructors is_constant normalized_lexp normalized_cexp normalized_equation.

  Fact constant_normalized_lexp : forall e,
      is_constant e ->
      normalized_lexp e.
  Proof.
    intros e Hconst.
    induction Hconst; auto.
  Qed.

  Fact is_constant_numstreams : forall e,
      is_constant e ->
      numstreams e = 1.
  Proof.
    intros e Hconst; induction Hconst; reflexivity.
  Qed.

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

  (** ** After normalization, a node is normalized *)

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

  Fact is_constant_is_constant : forall e,
      Norm.is_constant e = true <->
      is_constant e.
  Proof with eauto.
    intros e. split; intros Hconst.
    - induction e using exp_ind2; simpl in Hconst; try congruence.
      + constructor.
      + repeat (destruct es; try congruence).
        inv H; inv H3.
        destruct a.
        repeat (destruct l; try congruence).
        constructor...
    - induction Hconst...
  Qed.

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
    unfold fby_iteexp in Hfby.
    destruct (Norm.is_constant e0); repeat inv_bind.
    - constructor.
    - constructor.
      + constructor; auto.
        * intro contra.
          apply Hlt in contra; clear Hlt.
          assert (fresh_st_follows st st') as Hfollows by (etransitivity; eauto).
          apply fresh_ident_In in H0.
          assert (In x2 (st_ids st')) by (unfold st_ids, idty; simpl_In; exists (x2, (ty, fst cl, false)); eauto).
          apply smallest_ident_In in H1.
          apply (Pos.lt_irrefl x2).
          eapply Pos.lt_le_trans; eauto. etransitivity; eauto.
        * eapply add_whens_is_constant; eauto.
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
        unfold fby_iteexp in H3.
        destruct (Norm.is_constant e0) eqn:Hisconst; repeat inv_bind.
        * simpl in *. rewrite <- H9. repeat constructor.
          -- intro contra. apply Hlt in contra.
             specialize (idents_for_anns_st_follows _ _ _ _ H4) as Hfollows.
             apply idents_for_anns_incl_ids in H4.
             apply in_split_l in H5; simpl in H5. rewrite split_map_fst in H5. apply H4 in H5.
             apply smallest_ident_In in H5.
             apply (Pos.lt_irrefl i).
             eapply Pos.lt_le_trans; eauto.
             repeat (etransitivity; eauto).
          -- rewrite is_constant_is_constant in Hisconst...
          -- eapply nth_In in H6; rewrite Hnth in H6...
        * simpl. rewrite <- H11. repeat constructor.
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
        * destruct (hd _) as [? [? ?]]; simpl in *; repeat inv_bind...
      + constructor...
    - (* app (auxiliary equations) *)
      rewrite Forall_app. split.
      + destruct ro; repeat inv_bind; try constructor.
        eapply Forall_app. split...
        specialize (normalize_reset_spec (hd_default x2)) as [[? [? [? Hspec]]]|Hspec]; subst;
          rewrite Hspec in H4; clear Hspec; repeat inv_bind...
        destruct (hd _) as [? [? ?]]; simpl in *; repeat inv_bind.
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

  Fact normalized_equation_normalized_rhs : forall xs es to_cut,
      normalized_equation to_cut (xs, es) ->
      Forall (normalized_rhs (negb (existsb (fun x => PS.mem x to_cut) xs))) es.
  Proof with eauto.
    intros xs es to_cut Hnormed.
    inv Hnormed...
    constructor; [| constructor].
    simpl.
    apply PSE.mem_3 in H1. rewrite H1; simpl...
  Qed.

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
      unfold fby_iteexp in H3.
      destruct (Norm.is_constant e0) eqn:Hisconst; repeat inv_bind; simpl in *.
      + rewrite <- H5. repeat constructor.
        * rewrite is_constant_is_constant in Hisconst...
        * eapply nth_In in Hn. rewrite Hnth' in Hn...
      + rewrite <- H7. repeat constructor.
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
          unfold fby_iteexp in H3.
          destruct (Norm.is_constant e0) eqn:Hisconstant; repeat inv_bind; simpl in *; inv H5.
          -- econstructor...
             ++ intro contra. apply H4 in contra.
                specialize (fresh_ident_In _ _ _ _ H6) as Hin.
                apply fresh_ident_st_follows in H6.
                apply init_var_for_clock_st_follows in H3.
                assert (In x10 (st_ids st'0)).
                { unfold st_ids, idty. repeat simpl_In. exists (x10, (ty, (fst cl), false))... }
                apply smallest_ident_In in H5.
                eapply (Pos.lt_irrefl x10).
                eapply Pos.lt_le_trans...
                repeat (etransitivity; eauto).
             ++ eapply add_whens_is_constant...
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
      + destruct (hd _ _) as [? [? ?]]; simpl in H1.
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

  Lemma normalize_equation_normalized_eq : forall G eq to_cut eqs' out st st',
      wl_equation G eq ->
      normalize_equation to_cut eq st = (eqs', st') ->
      (forall o, PS.In o out -> Pos.lt o (smallest_ident st)) ->
      PS.Subset out to_cut ->
      Forall (normalized_equation out) eqs'.
  Proof with eauto.
    intros G [xs es] to_cut eqs' out st st' Hwl Hnorm Hlt Hincl.
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
        rewrite Hwl2. unfold without_names in H.
        erewrite <- map_length. setoid_rewrite <- H.
        rewrite map_length. reflexivity. } clear Hwl.
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

  Corollary normalize_equations_normalized_eq : forall G eqs to_cut eqs' out st st',
      Forall (wl_equation G) eqs ->
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
    intros n to_cut [G Hwl].
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

  Theorem normalize_global_normalized_global : forall G Hwl,
      normalized_global (normalize_global G Hwl).
  Proof.
    induction G; intros Hwl; simpl; constructor.
    - apply normalize_node_normalized_node.
    - apply IHG.
  Qed.

  (** ** Idempotence of normalization *)

  Fact normalized_lexp_normalize_idem : forall e is_control st,
      normalized_lexp e ->
      normalize_exp is_control e st = ([e], [], st).
  Proof with eauto.
    intros e is_control st Hnormed; revert is_control.
    induction Hnormed; intro is_control; simpl; repeat inv_bind...
    - (* unop *)
      repeat eexists...
      inv_bind...
    - (* binop *)
      repeat eexists...
      inv_bind. repeat eexists...
      inv_bind...
    - (* when *)
      exists [e]. exists []. exists st.
      repeat split; inv_bind...
      exists [[e]]. exists [[]]. exists st.
      repeat split; simpl; inv_bind...
      repeat eexists...
      inv_bind.
      repeat eexists; inv_bind...
  Qed.

  Corollary normalized_lexps_normalize_idem' : forall es is_control st,
      Forall normalized_lexp es ->
      (exists eqs, map_bind2 (normalize_exp is_control) es st = (List.map (fun e => [e]) es, eqs, st) /\ (concat eqs = [])).
  Proof with eauto.
    induction es; intros is_control st Hf;
      inv Hf; simpl; repeat inv_bind...
    eapply normalized_lexp_normalize_idem in H1...
    eapply (IHes is_control st) in H2; clear IHes.
    destruct H2 as [eqs [H2 Heqs]].
    exists ([]::eqs).
    repeat eexists... inv_bind.
    repeat eexists... inv_bind.
    repeat eexists... inv_bind.
    repeat f_equal.
  Qed.

  Corollary normalized_lexps_normalize_idem : forall es st,
      Forall normalized_lexp es ->
      normalize_exps es st = (es, [], st).
  Proof with eauto.
    intros.
    eapply normalized_lexps_normalize_idem' in H. destruct H as [eqs [H Heqs]].
    unfold normalize_exps; inv_bind.
    repeat eexists...
    inv_bind. rewrite concat_map_singl1. congruence.
  Qed.

  Fact normalized_cexp_normalize_idem : forall e st,
      normalized_cexp e ->
      normalize_exp true e st = ([e], [], st).
  Proof with eauto.
    intros e st Hnormed.
    induction Hnormed; simpl; repeat inv_bind...
    - (* merge *)
      exists [et]. exists []. exists st.
      repeat split; inv_bind...
      + exists [[et]]. exists [[]]. exists st.
        repeat split; simpl; inv_bind...
        repeat eexists...
        inv_bind.
        repeat eexists; inv_bind...
      + exists [ef]. exists []. exists st.
        repeat split; simpl; inv_bind...
        exists [[ef]]. exists [[]]. exists st.
        repeat split; simpl; inv_bind...
        repeat eexists...
        inv_bind.
        repeat eexists; inv_bind...
    - (* ite *)
      eapply normalized_lexp_normalize_idem in H. repeat eexists...
      repeat inv_bind.
      exists [et]. exists []. exists st.
      repeat split; inv_bind...
      + exists [[et]]. exists [[]]. exists st.
        repeat split; simpl; inv_bind...
        repeat eexists...
        inv_bind.
        repeat eexists; inv_bind...
      + exists [ef]. exists []. exists st.
        repeat split; simpl; inv_bind...
        exists [[ef]]. exists [[]]. exists st.
        repeat split; simpl; inv_bind...
        repeat eexists...
        inv_bind.
        repeat eexists; inv_bind...
    - (* lexp *) eapply normalized_lexp_normalize_idem...
  Qed.

  Fact normalize_fby_idem : forall e0 e ann st,
      is_constant e0 ->
      normalized_lexp e ->
      normalize_fby [e0] [e] [ann] st = ([Efby [e0] [e] [ann]], [], st).
  Proof with eauto.
    intros e0 e [ty cl] st Hcons Hnormed.
    unfold normalize_fby; inv_bind.
    eexists. exists [[]]. exists st. split; simpl; inv_bind...
    eexists. exists []. exists st. split; simpl.
    - unfold fby_iteexp.
      destruct (Norm.is_constant e0) eqn:Hisconstant; repeat inv_bind...
      rewrite <- is_constant_is_constant in Hcons. congruence.
    - inv_bind.
      repeat eexists; inv_bind...
  Qed.

  Fact normalized_rhs_normalize_idem : forall e keep_fby st,
      normalized_rhs keep_fby e ->
      normalize_rhs keep_fby e st = ([e], [], st).
  Proof with eauto.
    intros e keep_fby st Hnormed.
    destruct e; inv Hnormed; unfold normalize_rhs;
      try (solve [eapply normalized_cexp_normalize_idem; eauto]);
      try (solve [inv H; inv H0]).
    - (* fby *)
      repeat inv_bind.
      exists [e0]. exists []. exists st.
      split; unfold normalize_exps; inv_bind.
      + exists [[e0]]. exists [[]]. exists st. split; simpl; inv_bind...
        eapply constant_normalized_lexp in H2. eapply normalized_lexp_normalize_idem in H2.
        repeat eexists...
        inv_bind.
        exists []. exists []. exists st.
        repeat split; inv_bind...
      + exists [e]. exists []. exists st. split; simpl; inv_bind...
        * exists [[e]]. exists [[]]. exists st. split; simpl; inv_bind...
          eapply normalized_lexp_normalize_idem in H4.
          repeat eexists... inv_bind.
          repeat eexists; inv_bind...
        * repeat eexists; try inv_bind...
          eapply normalize_fby_idem...
    - (* app *)
      repeat inv_bind.
      repeat eexists. inv_bind.
      eapply normalized_lexps_normalize_idem in H1.
      repeat eexists...
      inv_bind...
    - (* app (reset) *)
      repeat inv_bind.
      repeat eexists; inv_bind.
      + repeat eexists; simpl; inv_bind...
        repeat eexists; simpl; inv_bind...
      + eapply normalized_lexps_normalize_idem in H1.
        repeat eexists...
        inv_bind...
  Qed.

  Corollary normalized_rhss_normalize_idem' : forall es keep_fby st,
      Forall (normalized_rhs keep_fby) es ->
      (exists eqs, map_bind2 (normalize_rhs keep_fby) es st = (List.map (fun e => [e]) es, eqs, st) /\ (concat eqs = [])).
  Proof with eauto.
    induction es; intros keep_fby st Hf;
      inv Hf; simpl; repeat inv_bind...
    eapply normalized_rhs_normalize_idem in H1...
    eapply (IHes keep_fby st) in H2; clear IHes.
    destruct H2 as [eqs [H2 Heqs]].
    exists ([]::eqs).
    repeat eexists... inv_bind.
    repeat eexists... inv_bind.
    repeat eexists... inv_bind.
    repeat f_equal.
  Qed.

  Corollary normalized_rhss_normalize_idem : forall es keep_fby st,
      Forall (normalized_rhs keep_fby) es ->
      normalize_rhss keep_fby es st = (es, [], st).
  Proof with eauto.
    intros.
    eapply normalized_rhss_normalize_idem' in H. destruct H as [eqs [H Heqs]].
    unfold normalize_rhss; inv_bind.
    repeat eexists...
    inv_bind. rewrite concat_map_singl1. congruence.
  Qed.

  Fact normalized_equation_normalize_idem : forall G eq to_cut st,
      wl_equation G eq ->
      normalized_equation to_cut eq ->
      normalize_equation to_cut eq st = ([eq], st).
  Proof with eauto.
    intros G [xs es] to_cut st Hwl Hnormed. inv Hwl.
    specialize (normalized_equation_normalized_rhs _ _ _ Hnormed) as Hnormed2.
    apply normalized_rhss_normalize_idem with (st:=st) in Hnormed2.
    inv Hnormed; simpl; repeat inv_bind;
      repeat eexists; eauto;
        inv_bind; rewrite app_nil_r;
          simpl in *; repeat f_equal.
    - rewrite app_nil_r in H0.
      apply firstn_all2. rewrite H0. apply le_refl.
    - rewrite app_nil_r in H0.
      apply firstn_all2. rewrite H0. apply le_refl.
    - rewrite app_nil_r in H0. rewrite length_annot_numstreams in H0.
      apply firstn_all2. simpl. rewrite H0. apply le_refl.
  Qed.

  Corollary normalized_equations_normalize_idem : forall G eqs to_cut st,
      Forall (wl_equation G) eqs ->
      Forall (normalized_equation to_cut) eqs ->
      normalize_equations to_cut eqs st = (eqs, st).
  Proof with eauto.
    induction eqs; intros to_cut st Hwl Hnormed; inv Hwl; inv Hnormed;
      unfold normalize_equations; repeat inv_bind...
    eapply normalized_equation_normalize_idem in H3...
    repeat eexists... inv_bind.
    repeat eexists... inv_bind.
    rewrite <- cons_is_app...
  Qed.

  Definition transport1 {n1 n2 : node} (Hin : n_in n1 = n_in n2) : 0 < length (n_in n1) -> 0 < length (n_in n2).
  Proof. intros. induction Hin. auto. Defined.

  Definition transport2 {n1 n2 : node} (Hout : n_out n1 = n_out n2) : 0 < length (n_out n1) -> 0 < length (n_out n2).
  Proof. intros. induction Hout. auto. Defined.

  Definition transport3 {n1 n2 : node}
             (Heqs : n_eqs n1 = n_eqs n2)
             (Hvars : n_vars n1 = n_vars n2)
             (Hout : n_out n1 = n_out n2) :
    Permutation (vars_defined (n_eqs n1)) (map fst ((n_vars n1) ++ (n_out n1))) ->
    Permutation (vars_defined (n_eqs n2)) (map fst ((n_vars n2) ++ (n_out n2))).
  Proof.
    intros.
    induction Heqs. induction Hvars. induction Hout.
    auto.
  Defined.

  Definition transport4 {n1 n2 : node}
             (Hin : n_in n1 = n_in n2)
             (Hvars : n_vars n1 = n_vars n2)
             (Hout : n_out n1 = n_out n2) :
    NoDupMembers (n_in n1 ++ n_vars n1 ++ n_out n1) ->
    NoDupMembers (n_in n2 ++ n_vars n2 ++ n_out n2).
  Proof.
    intros.
    induction Hin. induction Hvars. induction Hout.
    auto.
  Defined.

  Definition transport5 {n1 n2 : node}
             (Hname : n_name n1 = n_name n2)
             (Hin : n_in n1 = n_in n2)
             (Hvars : n_vars n1 = n_vars n2)
             (Hout : n_out n1 = n_out n2) :
    Forall ValidId (n_in n1 ++ n_vars n1 ++ n_out n1) /\ valid (n_name n1) ->
    Forall ValidId (n_in n2 ++ n_vars n2 ++ n_out n2) /\ valid (n_name n2).
  Proof.
    intros.
    induction Hname. induction Hin. induction Hvars. induction Hout.
    auto.
  Defined.

  Fact equal_node (n1 n2 : node)
    (Hname : n_name n1 = n_name n2)
    (Hstate : n_hasstate n1 = n_hasstate n2)
    (Hin : n_in n1 = n_in n2)
    (Hout : n_out n1 = n_out n2)
    (Hvars : n_vars n1 = n_vars n2)
    (Heqs : n_eqs n1 = n_eqs n2) :
    (transport1 Hin (n_ingt0 n1) = n_ingt0 n2) ->
    (transport2 Hout (n_outgt0 n1) = n_outgt0 n2) ->
    (transport3 Heqs Hvars Hout (n_defd n1) = n_defd n2) ->
    (transport4 Hin Hvars Hout (n_nodup n1) = n_nodup n2) ->
    (transport5 Hname Hin Hvars Hout (n_good n1) = n_good n2) ->
    n1 = n2.
  Proof.
    intros Heq1 Heq2 Heq3 Heq4 Heq5.
    destruct n1. destruct n2.
    simpl in *.
    destruct Hname. destruct Hstate.
    destruct Hin. destruct Hout. destruct Hvars.
    destruct Heqs.
    simpl in *; subst.
    reflexivity.
  Qed.

  Lemma normalized_node_normalize_idem : forall n Hwl,
      normalized_node n ->
      normalize_node PS.empty n Hwl = n.
  Proof with eauto.
    intros n [G Hwl] Hnormed.
    unfold normalize_node, normalized_node in *.
    eapply normalized_equations_normalize_idem with (st:=init_st (first_unused_ident n)) in Hnormed...
    destruct n; simpl in *.
    eapply equal_node; simpl...
    Unshelve. 6,7,8,9,10:simpl.
    6,7,8: exact eq_refl.
    1,2:reflexivity.
    4: { rewrite Hnormed; simpl.
         rewrite init_st_anns; simpl.
         apply app_nil_r. }
    4: { rewrite Hnormed... }
    simpl.
    1,2,3:apply proof_irrelevance.
  Qed.

  Corollary normalized_global_normalize_idem : forall G Hwl,
      normalized_global G ->
      normalize_global G Hwl = G.
  Proof with eauto.
    induction G; intros Hwl Hnormed...
    simpl. inv Hnormed.
    eapply normalized_node_normalize_idem in H1...
    rewrite H1.
    rewrite IHG...
  Qed.

  Theorem normalize_global_idem : forall G Hwl1 Hwl2,
      normalize_global (normalize_global G Hwl1) Hwl2 = normalize_global G Hwl1.
  Proof.
    intros G Hwl1 Hwl2.
    apply normalized_global_normalize_idem.
    apply normalize_global_normalized_global.
  Qed.
End COMPLETENESS.

Module CompletenessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn)
       (Norm : NORMALIZATION Ids Op OpAux Syn)
       <: COMPLETENESS Ids Op OpAux Syn Typ Norm.
  Include COMPLETENESS Ids Op OpAux Syn Typ Norm.
End CompletenessFun.
