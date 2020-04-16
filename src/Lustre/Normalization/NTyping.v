From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Omega.

From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

(** * Preservation of Typing through Normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type NTYPING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Typ : LTYPING Ids Op Syn)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn Typ).
  Import List.
  Import Fresh Facts Tactics.

  (** ** wt implies wl *)

  Hint Constructors wl_exp.
  Fact wt_exp_wl_exp : forall G vars e,
      wt_exp G vars e ->
      wl_exp e.
  Proof with eauto.
    induction e using exp_ind2; intro Hwt; inv Hwt; auto.
    - (* unop *)
      constructor...
      rewrite <- length_typeof_numstreams. rewrite H3. reflexivity.
    - (* binop *)
      constructor...
      + rewrite <- length_typeof_numstreams. rewrite H5. reflexivity.
      + rewrite <- length_typeof_numstreams. rewrite H6. reflexivity.
    - (* fby *)
      constructor...
      + repeat rewrite_Forall_forall...
      + repeat rewrite_Forall_forall...
      + rewrite typesof_annots in *. erewrite <- map_length.
        rewrite H7. solve_length.
      + rewrite typesof_annots in *. erewrite <- map_length.
        rewrite H6. solve_length.
    - (* when *)
      constructor...
      + repeat rewrite_Forall_forall...
      + rewrite typesof_annots. solve_length.
    - (* merge *)
      constructor...
      + repeat rewrite_Forall_forall...
      + repeat rewrite_Forall_forall...
      + rewrite typesof_annots. solve_length.
      + rewrite <- H9. clear H9. rewrite typesof_annots. solve_length.
    - (* ite *)
      constructor...
      + repeat rewrite_Forall_forall...
      + repeat rewrite_Forall_forall...
      + rewrite <- length_typeof_numstreams. rewrite H8. reflexivity.
      + rewrite typesof_annots. solve_length.
      + rewrite <- H10. clear H10. rewrite typesof_annots. solve_length.
    - (* app *)
      constructor...
      repeat rewrite_Forall_forall...
    - (* app (reset) *)
      constructor...
      + repeat rewrite_Forall_forall...
      + rewrite <- length_typeof_numstreams. rewrite H11. reflexivity.
  Qed.
  Hint Resolve wt_exp_wl_exp.

  Corollary Forall_wt_exp_wl_exp : forall G vars es,
      Forall (wt_exp G vars) es ->
      Forall wl_exp es.
  Proof. intros. solve_forall. Qed.
  Hint Resolve Forall_wt_exp_wl_exp.

  Fact wt_equation_wl_equation : forall G vars equ,
      wt_equation G vars equ ->
      wl_equation equ.
  Proof with eauto.
    intros G vars [xs es] Hwt.
    inv Hwt. constructor.
    + repeat rewrite_Forall_forall...
    + repeat rewrite_Forall_forall.
      solve_length.
  Qed.
  Hint Resolve wt_equation_wl_equation.

  Fact wt_node_wl_node : forall G n,
      wt_node G n ->
      wl_node n.
  Proof with eauto.
    intros G n [_ [_ [_ Hwt]]].
    unfold wl_node.
    repeat rewrite_Forall_forall...
  Qed.
  Hint Resolve wt_node_wl_node.

  Fact wt_global_wl_global : forall G,
      wt_global G ->
      wl_global G.
  Proof with eauto.
    intros G Hwt.
    unfold wl_global.
    induction Hwt...
  Qed.
  Hint Resolve wt_global_wl_global.

  (** ** Preservation of typeof *)

  Fact normalize_exp_typeof : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st')  ->
      typesof es' = typeof e.
  Proof.
    intros.
    eapply normalize_exp_annot in H0; eauto.
    rewrite typesof_without_names. rewrite typeof_without_names.
    congruence.
  Qed.

  Corollary map_bind2_normalize_exp_typesof' :
    forall G vars is_control es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => typesof es' = typeof e) es' es.
  Proof.
    intros.
    eapply map_bind2_normalize_exp_annots' in H0; eauto.
    repeat rewrite_Forall_forall.
    rewrite typesof_without_names. rewrite typeof_without_names.
    erewrite H1; eauto.
  Qed.

  Corollary map_bind2_normalize_exp_typesof :
    forall G vars is_control es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      typesof (concat es') = typesof es.
  Proof.
    intros.
    eapply map_bind2_normalize_exp_annots in H0; eauto.
    repeat rewrite typesof_without_names.
    congruence.
  Qed.

  Corollary normalize_exps_typesof : forall G vars es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_exps es st = (es', eqs', st') ->
      typesof es' = typesof es.
  Proof.
    intros.
    eapply normalize_exps_annots in H0; eauto.
    repeat rewrite typesof_without_names.
    congruence.
  Qed.

  Fact fby_iteexp_typeof : forall e0 e ann es' eqs' st st',
      fby_iteexp e0 e ann st = (es', eqs', st') ->
      typeof es' = [fst ann].
  Proof.
    intros.
    eapply fby_iteexp_annot in H; simpl.
    rewrite typeof_without_names. rewrite H.
    destruct ann0 as [? [? ?]]; reflexivity.
  Qed.

  Fact normalize_fby_typeof : forall inits es anns es' eqs' st st',
      length inits = length anns ->
      length es = length anns ->
      normalize_fby inits es anns st = (es', eqs', st') ->
      typesof es' = List.map fst anns.
  Proof.
    intros.
    eapply normalize_fby_annot in H1; eauto.
    rewrite typesof_without_names.
    rewrite H1. unfold without_names. rewrite map_map; simpl.
    clear H H0 H1. induction anns; simpl; f_equal; auto.
    destruct a as [? [? ?]]; auto.
  Qed.

  Fact normalize_rhs_typeof : forall G vars e keep_fby es' eqs' st st',
      wt_exp G vars e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      typesof es' = typeof e.
  Proof.
    intros.
    eapply normalize_rhs_annot in H0; eauto.
    rewrite typesof_without_names. rewrite typeof_without_names.
    congruence.
  Qed.

  Corollary normalize_rhss_typesof : forall G vars es keep_fby es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      typesof es' = typesof es.
  Proof.
    intros.
    eapply normalize_rhss_annots in H0; eauto.
    repeat rewrite typesof_without_names. congruence.
  Qed.

  (** ** A few additional tactics *)

  Definition st_tys (st : fresh_st ((Op.type * clock) * bool)) := idty (idty (st_anns st)).

  Fact st_anns_tys_In : forall st id ty,
      In (id, ty) (st_tys st) <-> (exists cl, exists b, In (id, (ty, cl, b)) (st_anns st)).
  Proof.
    intros st id ty.
    split; intros; unfold st_tys, idty in *.
    - repeat simpl_In; simpl in *.
      inv H0. inv H.
      exists c. exists b. assumption.
    - repeat simpl_In; simpl in *.
      destruct H as [cl [b HIn]].
      exists (id, (ty, cl)); simpl; split; auto.
      simpl_In. exists (id, (ty, cl, b)); auto.
  Qed.

  Fact st_follows_tys_incl : forall st st',
      fresh_st_follows st st' ->
      incl (st_tys st) (st_tys st').
  Proof.
    intros st st' Hfollows.
    apply st_follows_incl in Hfollows.
    unfold st_tys, idty.
    repeat apply incl_map.
    assumption.
  Qed.

  Fact idents_for_anns_incl_ty : forall anns ids st st',
    idents_for_anns anns st = (ids, st') ->
    incl (idty ids) (st_tys st').
  Proof.
    intros anns ids st st' Hids.
    apply idents_for_anns_incl in Hids.
    intros [id ty] Hin.
    unfold st_tys, idty in *.
    repeat simpl_In. inv H.
    exists (id, (ty, (fst n))); split; auto.
    apply Hids. repeat simpl_In.
    exists (id, (ty, n)). destruct n; auto.
  Qed.

  Ltac solve_incl :=
    match goal with
    | H : wt_clock ?l1 ?cl |- wt_clock ?l2 ?cl =>
      eapply wt_clock_incl; [| eauto]
    | H : wt_nclock ?l1 ?cl |- wt_nclock ?l2 ?cl =>
      eapply wt_nclock_incl; [| eauto]
    | H : wt_exp ?G ?l1 ?e |- wt_exp ?G ?l2 ?e =>
      eapply wt_exp_incl; [| eauto]
    | H : wt_equation ?G ?l1 ?eq |- wt_equation ?G ?l2 ?eq =>
      eapply wt_equation_incl; [| eauto]
    | |- incl ?l1 ?l1 => reflexivity
    | |- incl ?l1 (?l1 ++ ?l2) =>
      eapply incl_appl; reflexivity
    | |- incl (?l1 ++ ?l2) (?l1 ++ ?l3) =>
      eapply incl_app
    | |- incl ?l1 (?l2 ++ ?l3) =>
      eapply incl_appr
    | |- incl ?l1 (?a::?l2) =>
      eapply incl_tl
    | |- incl (st_tys ?st1) (st_tys _) =>
      eapply st_follows_tys_incl; repeat solve_st_follows
    | H : incl ?l1 ?l2 |- incl (idty ?l1) (idty ?l2) =>
      eapply incl_map; eauto
    end; auto.

  Hint Resolve in_combine_l in_combine_r.
  Hint Resolve incl_tl incl_appl incl_appr incl_app incl_refl.

  (** ** Preservation of wt *)

  Fact idents_for_anns_wt : forall G vars anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      Forall (fun '(ty, cl) => wt_nclock vars cl) anns ->
      Forall (wt_exp G (vars++(idty ids))) (map (fun '(x, ann) => Evar x ann) ids).
  Proof.
    induction anns; intros ids st st' Hidents Hf;
      simpl in *; repeat inv_bind.
    - constructor.
    - inv Hf. destruct a as [ty [cl ?]]. repeat inv_bind.
      rewrite Forall_map.
      specialize (IHanns x1 _ _ H0 H2).
      econstructor; eauto.
      + repeat constructor; simpl.
        * apply in_or_app. right. constructor; auto.
        * inv H1. repeat solve_incl.
      + rewrite Forall_map in IHanns.
        solve_forall. repeat solve_incl.
  Qed.

  Fact hd_default_wt_exp : forall G vars es,
      Forall (wt_exp G vars) es ->
      wt_exp G vars (hd_default es).
  Proof.
    intros G vars es Hf.
    destruct es; simpl.
    - constructor.
    - inv Hf; auto.
  Qed.

  Fact map_bind2_wt_exp' {A A2 B} :
    forall G vars (k : A -> Fresh (exp * A2) B) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> fresh_st_follows st st') ->
      Forall (fun a => forall e' a2s st0 st0',
                  k a st0 = (e', a2s, st0') ->
                  fresh_st_follows st st0 ->
                  fresh_st_follows st0' st' ->
                  wt_exp G vars e') a ->
      Forall (wt_exp G vars) es'.
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

  Fact map_bind2_wt_exp {A A2 B} :
    forall G vars (k : A -> Fresh (list exp * A2) B) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> fresh_st_follows st st') ->
      Forall (fun a => forall es' a2s st0 st0',
                  k a st0 = (es', a2s, st0') ->
                  fresh_st_follows st st0 ->
                  fresh_st_follows st0' st' ->
                  Forall (wt_exp G vars) es') a ->
      Forall (wt_exp G vars) (concat es').
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

  Hint Constructors wt_exp.

  Fact normalize_fby_wt_exp : forall G vars e0s es anns es' eqs' st st',
      Forall (wt_exp G (vars++(st_tys st))) e0s ->
      Forall (wt_exp G (vars++(st_tys st))) es ->
      Forall2 (fun e0 a => typeof e0 = [fst a]) e0s anns ->
      Forall2 (fun e a => typeof e = [fst a]) es anns ->
      Forall (fun '(_, cl) => wt_nclock vars cl) anns ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall (wt_exp G (vars++(st_tys st'))) es'.
  Proof.
    intros G vars e0s es anns es' eqs' st st' Hwt1 Hwt2 Hty1 Hty2 Hclock Hnorm.
    unfold normalize_fby in Hnorm. repeat inv_bind.
    eapply map_bind2_wt_exp' in H; eauto.
    - destruct a as [[e0 e] a]. eauto.
    - solve_forall. destruct x as [[e0 e] [ty cl]].
      specialize (fby_iteexp_spec e0 e ty cl) as [[? [? Hspec]]|Hspec]; subst;
        rewrite Hspec in H1; clear Hspec; repeat inv_bind.
      + repeat rewrite_Forall_forall.
        repeat constructor; simpl.
        * repeat simpl_In.
          apply Hwt2 in H7.
          repeat solve_incl.
        * rewrite app_nil_r.
          repeat rewrite_Forall_forall.
          repeat simpl_nth; repeat simpl_length.
          specialize (H4 _ _ _ _ _ H0 H11 H10). simpl in H4.
          congruence.
        * f_equal. repeat simpl_nth; repeat simpl_length.
          specialize (H6 _ _ _ _ _ H0 H8 H10); simpl in H6.
          congruence.
        * repeat simpl_In.
          apply Hclock in H0. repeat solve_incl.
      + repeat rewrite_Forall_forall.
        repeat simpl_length.
        repeat constructor; simpl.
        * unfold init_var_for_clock in H1.
          destruct (find _ _) eqn:Hfind.
          -- destruct p. inv H1.
             apply find_some in Hfind; destruct Hfind as [Hfind1 Hfind2].
             destruct p as [[? ?] ?].
             repeat rewrite Bool.andb_true_iff in Hfind2. destruct Hfind2 as [_ Hfind2].
             rewrite equiv_decb_equiv in Hfind2.
             assert (incl (st_tys x2) (vars++(st_tys st'))) as Hincl by repeat solve_incl.
             apply Hincl. repeat unfold st_tys, idty; repeat simpl_In.
             exists (x, (t, c)); simpl; auto. split.
             ++ repeat f_equal. apply Hfind2.
             ++ repeat simpl_In. exists (x, (t, c, b)); simpl; eauto.
          -- destruct (fresh_ident _ _) eqn:Hfresh. inv H1.
             apply fresh_ident_In in Hfresh.
             assert (incl (st_tys x2) (st_tys st')) as Hincl by repeat solve_incl.
             apply in_or_app. right. apply Hincl.
             unfold st_tys, idty. repeat simpl_In.
             exists (x, (Op.bool_type, (fst cl))); simpl; split; auto.
             repeat simpl_In. exists (x, (Op.bool_type, (fst cl), true)); simpl; auto.
        * repeat simpl_In. apply Hclock in H0. inv H0. repeat solve_incl.
        * repeat simpl_In. apply Hwt1 in H10. repeat solve_incl.
        * apply fresh_ident_In in H4.
          apply st_follows_tys_incl in H3.
          apply in_or_app; right. apply H3.
          rewrite st_anns_tys_In. exists (fst cl). exists false. assumption.
        * repeat simpl_In. apply Hclock in H0. repeat solve_incl.
        * rewrite app_nil_r.
          repeat simpl_nth. repeat simpl_length.
          specialize (H8 _ _ _ _ _ H0 H10 H12). simpl in H8.
          congruence.
        * repeat simpl_In. apply Hclock in H0. repeat solve_incl.
          inv H0. repeat solve_incl.
  Qed.

  Fact normalize_reset_typeof_bool : forall e e' eqs' st st',
      typeof e = [Op.bool_type] ->
      normalize_reset e st = (e', eqs', st') ->
      typeof e' = [Op.bool_type].
  Proof.
    intros e e' eqs' st st' Htyp Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind.
    - simpl in Htyp. assumption.
    - destruct (hd _) as [? [? ?]] eqn:Hann; simpl in *; repeat inv_bind;
        destruct e; simpl in *; try solve [inv Hann; auto].
      1,3,4: (destruct l1; try destruct l1; simpl in *; inv Hann; simpl in *; auto; destruct l1; congruence).
      + destruct l0. destruct l0; simpl in *; inv Hann; simpl in *; auto.
        destruct l0; congruence.
      + destruct l0; try destruct a; simpl in *; inv Hann; simpl in *; auto.
        destruct l0; congruence.
  Qed.

  Fact normalize_reset_wt_exp : forall G vars e e' eqs' st st',
      wt_exp G (vars++(st_tys st)) e ->
      normalize_reset e st = (e', eqs', st') ->
      wt_exp G (vars++(st_tys st')) e'.
  Proof.
    intros G vars e e' eqs' st st' Hwt Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind.
    - assumption.
    - destruct (hd _) as [? [? ?]] eqn:Hann; simpl in *; repeat inv_bind.
      constructor.
      + apply fresh_ident_In in H.
        apply in_or_app; right.
        rewrite st_anns_tys_In. exists c. exists false. assumption.
      + apply fresh_ident_st_follows in H.
        destruct e; simpl in Hann; inv Hann; inv Hwt; repeat constructor.
        * inv H4. repeat solve_incl.
        * inv H7. repeat solve_incl.
        * inv H10. repeat solve_incl.
        * destruct l1; simpl in *; inv H1; repeat constructor. inv H8. inv H2. repeat solve_incl.
        * destruct (typesof l); simpl in *; inv H1; repeat constructor. inv H8. repeat solve_incl.
        * destruct (typesof l); simpl in *; inv H1; repeat constructor. inv H10. repeat solve_incl.
        * destruct (typesof l); simpl in *; inv H1; repeat constructor. inv H11. repeat solve_incl.
        * destruct l0; simpl in *; inv H1; repeat constructor. inv H9; simpl in *. inv H2. repeat solve_incl.
        * destruct l0; simpl in *; inv H1; repeat constructor. inv H9; simpl in *. inv H2. repeat solve_incl.
  Qed.

  Fact normalize_exp_wt_exp : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wt_exp G (vars++(st_tys st'))) es'.
  Proof with eauto.
    intros G vars e is_control es' eqs' st st' Hwt;
      revert is_control eqs' es' st st'.
    induction Hwt using wt_exp_ind2;
      intros is_control eqs' es' st st' Hnorm; simpl in *.
    - (* const *)
      repeat inv_bind...
    - (* var *)
      repeat inv_bind.
      repeat constructor.
      + apply in_or_app...
      + repeat solve_incl.
    - (* unop *)
      repeat inv_bind.
      specialize (IHHwt _ _ _ _ _ H2).
      repeat constructor.
      assert (length x = numstreams e) as Hlen by (eapply normalize_exp_length; eauto).
      rewrite <- length_typeof_numstreams in Hlen.
      replace (typeof e) in *.
      singleton_length.
      inv IHHwt. econstructor...
      eapply normalize_exp_typeof in Hwt...
      simpl in *; rewrite app_nil_r in Hwt; rewrite Hwt...
      eapply wt_nclock_incl; [| eauto]...
    - (* binop *)
      repeat inv_bind.
      specialize (IHHwt1 _ _ _ _ _ H3).
      specialize (IHHwt2 _ _ _ _ _ H4).
      repeat constructor.
      assert (length x = numstreams e1) as Hlen1 by (eapply normalize_exp_length; eauto).
      assert (length x2 = numstreams e2) as Hlen2 by (eapply normalize_exp_length; eauto).
      rewrite <- length_typeof_numstreams in Hlen1.
      rewrite <- length_typeof_numstreams in Hlen2.
      replace (typeof e1) in *.
      replace (typeof e2) in *.
      repeat singleton_length.
      eapply normalize_exp_typeof in Hwt1...
      eapply normalize_exp_typeof in Hwt2...
      inv IHHwt1. inv IHHwt2. inv H8. inv H10.
      econstructor; eauto;
        simpl in *; rewrite app_nil_r in *;
          try rewrite Hwt1; try rewrite Hwt2...
      + eapply normalize_exp_st_follows in H4. repeat solve_incl.
      + repeat solve_incl.
    - (* fby *)
      repeat inv_bind.
      specialize (idents_for_anns_incl_ty _ _ _ _ H9) as Hincl.
      apply idents_for_anns_wt with (G:=G) (vars:=vars) in H9.
      + solve_forall.
        eapply wt_exp_incl; [| eauto].
        apply incl_app...
      + rewrite Forall_forall in *; intros.
        destruct x as [? [? ?]]. eapply H5.
        simpl_In.
        exists (t, (c, o)); simpl...
    - (* when *)
      repeat inv_bind.
      assert (length (concat x1) = length (annots es)) as Hlength by (eapply map_bind2_normalize_exp_length; eauto).
      assert (typesof (concat x1) = typesof es) as Htypeof by (eapply map_bind2_normalize_exp_typesof; eauto).
      repeat rewrite_Forall_forall.
      rewrite in_map_iff in H4; destruct H4 as [[? ?] [? Hin]]; subst.
      constructor; simpl...
      + repeat constructor. eapply map_bind2_wt_exp in H1.
        * rewrite Forall_forall in H1...
        * intros; eapply normalize_exp_st_follows...
        * rewrite Forall_forall; intros.
          eapply H0 in H5; eauto.
          solve_forall. repeat solve_incl.
      + rewrite app_nil_r.
        specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H1) as Hnumstreams.
        eapply map_bind2_normalize_exp_typesof in H1; [| rewrite Forall_forall; intros; auto].
        rewrite <- Htypeof in Hin.
        repeat simpl_nth.
        unfold typesof. rewrite flat_map_concat_map.
        eapply concat_length_map_nth; solve_forall.
        * repeat solve_length.
        * rewrite length_typeof_numstreams...
      + apply in_or_app...
      + repeat solve_incl.
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + rewrite Forall_forall; intros ? Hin.
        rewrite in_map_iff in Hin; destruct Hin as [[[? ?] ?] [? Hin]]; subst.
        assert (length (concat x3) = length (annots ets)) by (eapply map_bind2_normalize_exp_length; eauto).
        assert (length (concat x5) = length (annots efs)) by (eapply map_bind2_normalize_exp_length; eauto).
        constructor; simpl...
        * eapply map_bind2_wt_exp with (G0:=G) (vars0 := (vars++(st_tys x2))) in H7...
          -- repeat constructor.
             repeat simpl_In.
             rewrite Forall_forall in H7. apply H7 in H11.
             repeat solve_incl.
          -- solve_forall. apply H10 in H11.
             solve_forall. repeat solve_incl.
        * eapply map_bind2_wt_exp with (G0:=G) (vars0 := (vars++(st_tys st'))) in H4...
          -- repeat constructor.
             repeat simpl_In.
             rewrite Forall_forall in H4. apply H4 in H10.
             repeat solve_incl.
          -- solve_forall. eapply H10 in H11.
             solve_forall. repeat solve_incl.
        * apply in_or_app...
        * rewrite app_nil_r.
          specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H7) as Hnumstreams.
          eapply map_bind2_normalize_exp_typesof in H7; [| rewrite Forall_forall in *; intros; auto].
          rewrite <- H7 in Hin. rewrite <- length_typesof_annots in *.
          repeat simpl_nth.
          unfold typesof. rewrite flat_map_concat_map.
          eapply concat_length_map_nth; solve_forall.
          -- repeat solve_length.
          -- rewrite length_typeof_numstreams...
        * rewrite app_nil_r.
          specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H4) as Hnumstreams.
          eapply map_bind2_normalize_exp_typesof in H4; [| rewrite Forall_forall in *; intros; auto].
          rewrite <- H5 in Hin. rewrite <- H4 in Hin. rewrite <- length_typesof_annots in *.
          repeat simpl_nth.
          unfold typesof. rewrite flat_map_concat_map.
          eapply concat_length_map_nth; solve_forall.
          -- repeat solve_length.
          -- rewrite length_typeof_numstreams...
        * repeat solve_incl.
      + specialize (idents_for_anns_incl_ty _ _ _ _ H9) as Hincl.
        apply idents_for_anns_wt with (G:=G) (vars:=vars) in H9.
        * solve_forall. repeat solve_incl...
        * rewrite Forall_forall; intros.
          repeat simpl_In. inv H8...
    - (* ite *)
      destruct is_control; repeat inv_bind.
      + rewrite Forall_forall; intros ? Hin.
        rewrite in_map_iff in Hin; destruct Hin as [[[? ?] ?] [? Hin]]; subst.
        assert (length (concat x5) = length (annots ets)) by (eapply map_bind2_normalize_exp_length; eauto).
        assert (length (concat x7) = length (annots efs)) by (eapply map_bind2_normalize_exp_length; eauto).
        constructor; simpl...
        * apply IHHwt in H7.
          apply hd_default_wt_exp. solve_forall.
          apply map_bind2_st_follows in H8; solve_forall.
          apply map_bind2_st_follows in H4; solve_forall.
          repeat solve_incl.
        * eapply map_bind2_wt_exp with (G0:=G) (vars0 := (vars++(st_tys x4))) in H8...
          -- repeat constructor.
             repeat simpl_In.
             rewrite Forall_forall in H8. apply H8 in H12.
             repeat solve_incl.
          -- solve_forall. apply H11 in H12.
             solve_forall. repeat solve_incl.
        * eapply map_bind2_wt_exp with (G0:=G) (vars0 := (vars++(st_tys st'))) in H4...
          -- repeat constructor.
             repeat simpl_In.
             rewrite Forall_forall in H4. apply H4 in H11.
             repeat solve_incl.
          -- solve_forall. eapply H11 in H12.
             solve_forall. repeat solve_incl.
        * assert (length x = numstreams e) as Hlength by (eapply normalize_exp_length; eauto).
          rewrite <- length_typeof_numstreams in Hlength.
          rewrite H3 in Hlength; simpl in Hlength.
          eapply normalize_exp_typeof in H7...
          destruct x; simpl in *; try congruence.
          destruct x; simpl in *; try congruence.
          rewrite app_nil_r in H7. congruence.
        * rewrite app_nil_r.
          specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H8) as Hnumstreams.
          eapply map_bind2_normalize_exp_typesof in H8; [| rewrite Forall_forall in *; intros; auto].
          rewrite <- H8 in Hin. rewrite <- length_typesof_annots in *.
          repeat simpl_nth.
          unfold typesof. rewrite flat_map_concat_map.
          eapply concat_length_map_nth; solve_forall.
          -- repeat solve_length.
          -- rewrite length_typeof_numstreams...
        * rewrite app_nil_r.
          specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H4) as Hnumstreams.
          eapply map_bind2_normalize_exp_typesof in H4; [| rewrite Forall_forall in *; intros; auto].
          rewrite <- H5 in Hin. rewrite <- H4 in Hin. rewrite <- length_typesof_annots in *.
          repeat simpl_nth.
          unfold typesof. rewrite flat_map_concat_map.
          eapply concat_length_map_nth; solve_forall.
          -- repeat solve_length.
          -- rewrite length_typeof_numstreams...
        * repeat solve_incl.
      + specialize (idents_for_anns_incl_ty _ _ _ _ H10) as Hincl.
        apply idents_for_anns_wt with (G:=G) (vars:=vars) in H10.
        * solve_forall. repeat solve_incl.
        * rewrite Forall_forall; intros.
          destruct x2. repeat simpl_In. inv H9...
    - (* app *)
      repeat inv_bind.
      specialize (idents_for_anns_incl_ty _ _ _ _ H6) as Hincl.
      apply idents_for_anns_wt with (G:=G) (vars:=vars) in H6.
      + solve_forall. repeat solve_incl.
      + rewrite Forall_forall in *; intros.
        destruct x as [? [? ?]]. specialize (H4 _ H7); simpl in H4; eauto.
    - (* app (reset) *)
      repeat inv_bind.
      specialize (idents_for_anns_incl_ty _ _ _ _ H8) as Hincl.
      apply idents_for_anns_wt with (G:=G) (vars:=vars) in H8.
      + solve_forall. repeat solve_incl.
      + rewrite Forall_forall in *; intros.
        destruct x as [? [? ?]]. specialize (H4 _ H10); simpl in H4; eauto.
  Qed.

  Corollary map_bind2_normalize_exp_wt_exp : forall G vars is_control es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall (wt_exp G (vars++(st_tys st'))) (concat es').
  Proof.
    intros G vars is_control es es' eqs' st st' Hwt Hmap.
    eapply map_bind2_wt_exp in Hmap; solve_forall; eauto.
    eapply normalize_exp_wt_exp in H0; eauto.
    solve_forall. repeat solve_incl.
  Qed.

  Corollary normalize_exps_wt_exp : forall G vars es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_exps es st = (es', eqs', st') ->
      Forall (wt_exp G (vars++(st_tys st'))) es'.
  Proof.
    intros G vars es es' eqs' st st' Hwt Hmap.
    unfold normalize_exps in Hmap; repeat inv_bind.
    eapply map_bind2_normalize_exp_wt_exp in H; eauto.
  Qed.

  Fact normalize_rhs_wt_exp : forall G vars e keep_fby es' eqs' st st',
      wt_exp G vars e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      Forall (wt_exp G (vars++(st_tys st'))) es'.
  Proof with eauto.
    intros G vars e keep_fby es' eqs' st st' Hwt Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (solve [eapply normalize_exp_wt_exp in Hnorm; eauto]).
    - (* fby *)
      destruct keep_fby.
      + inv Hwt. repeat inv_bind.
        eapply normalize_fby_wt_exp in H1; eauto.
        * eapply normalize_exps_wt_exp in H; eauto.
          solve_forall.
          eapply normalize_exps_st_follows in H0.
          eapply normalize_fby_st_follows in H1.
          repeat solve_incl.
        * eapply normalize_exps_wt_exp in H0; eauto.
        * assert (length x = length (annots l)) by (eapply normalize_exps_length; eauto).
          specialize (normalize_exps_numstreams _ _ _ _ _ H) as Hnumstreams.
          unfold normalize_exps in H; repeat inv_bind.
          eapply map_bind2_normalize_exp_typesof' in H; eauto.
          assert (Forall2 (fun tys tys' => tys = tys') (map typesof x5) (map typeof l)).
          { specialize (Forall2_map_1 (fun tys e => tys = typeof e) typesof x5 l) as [_ Hfm].
            specialize (Forall2_map_2 (fun tys tys' => tys = tys') typeof (map typesof x5) l) as [_ Hfm2].
            auto. } rewrite Forall2_eq in H8.
          repeat rewrite_Forall_forall.
          -- rewrite <- length_typesof_annots in *. solve_length.
          -- rewrite (concat_length_map_nth _ _ _ _ (fst b))...
             ++ unfold typesof in *. rewrite flat_map_concat_map in H5. rewrite <- H8 in H5.
              rewrite <- (map_nth fst). rewrite <- H5.
             rewrite typeof_concat_typesof. reflexivity.
             ++ solve_forall. rewrite length_typeof_numstreams...
        * assert (length x2 = length (annots l0)) by (eapply normalize_exps_length; eauto).
          specialize (normalize_exps_numstreams _ _ _ _ _ H0) as Hnumstreams.
          unfold normalize_exps in H0; repeat inv_bind.
          eapply map_bind2_normalize_exp_typesof' in H0; eauto.
          assert (Forall2 (fun tys tys' => tys = tys') (map typesof x5) (map typeof l0)).
          { specialize (Forall2_map_1 (fun tys e => tys = typeof e) typesof x5 l0) as [_ Hfm].
            specialize (Forall2_map_2 (fun tys tys' => tys = tys') typeof (map typesof x5) l0) as [_ Hfm2].
            auto. } rewrite Forall2_eq in H8.
          repeat rewrite_Forall_forall.
          -- rewrite <- length_typesof_annots in *. solve_length.
          -- rewrite (concat_length_map_nth _ _ _ _ (fst b))...
             ++ unfold typesof in *. rewrite flat_map_concat_map in H4. rewrite <- H8 in H4.
              rewrite <- (map_nth fst). rewrite <- H4.
             rewrite typeof_concat_typesof. reflexivity.
             ++ solve_forall. rewrite length_typeof_numstreams...
        * rewrite Forall_map in H6. solve_forall. destruct a...
      + eapply normalize_exp_wt_exp in Hnorm; eauto.
    - (* app *)
      inv Hwt; repeat inv_bind; repeat econstructor; eauto.
      1,4: eapply normalize_exps_wt_exp...
      2,4:solve_forall; repeat solve_incl.
      + eapply normalize_exps_typesof in H... congruence.
      + eapply normalize_exps_typesof in H0... congruence.
      + eapply normalize_exp_wt_exp in H...
        eapply hd_default_wt_exp in H.
        eapply normalize_reset_wt_exp in H1...
        apply normalize_exps_st_follows in H0.
        repeat solve_incl.
      + specialize (normalize_exp_numstreams _ _ _ _ _ _ H) as Hlength.
        eapply normalize_exp_typeof in H...
        eapply normalize_reset_typeof_bool in H1...
        rewrite H9 in H.
        destruct x4; simpl in *; try congruence.
        inv Hlength. rewrite <- length_typeof_numstreams in H11.
        destruct (typeof e); simpl in *; try congruence.
        destruct l1; simpl in *; try congruence.
  Qed.

  Corollary normalize_rhss_wt_exp : forall G vars es keep_fby es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      Forall (wt_exp G (vars++(st_tys st'))) es'.
  Proof with eauto.
    intros G vars es keep_fby es' eqs' st st' Hwt Hnorm.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_wt_exp in H...
    solve_forall.
    eapply normalize_rhs_wt_exp in H1...
    solve_forall. repeat solve_incl.
  Qed.

  Fact map_bind2_wt_eq {A A1 B} :
    forall G vars (k : A -> Fresh (A1 * list equation) B) a a1s eqs' st st',
      map_bind2 k a st = (a1s, eqs', st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> fresh_st_follows st st') ->
      Forall (fun a => forall a1 eqs' st0 st0',
                  k a st0 = (a1, eqs', st0') ->
                  fresh_st_follows st st0 ->
                  fresh_st_follows st0' st' ->
                  Forall (wt_equation G vars) eqs') a ->
      Forall (wt_equation G vars) (concat eqs').
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

  Fact add_whens_typeof : forall e ty cl,
      typeof e = [ty] ->
      typeof (add_whens e ty cl) = [ty].
  Proof.
    induction cl; intro Hty; simpl; auto.
  Qed.

  Fact add_whens_wt_exp : forall G vars e ty cl e',
      wt_exp G vars e ->
      typeof e = [ty] ->
      wt_clock vars cl ->
      add_whens e ty cl = e' ->
      wt_exp G vars e'.
  Proof.
    induction cl; intros e' Hwt Hty Hclock Hwhens; simpl in Hwhens; inv Hclock; subst.
    - assumption.
    - repeat constructor; simpl; auto.
      rewrite app_nil_r.
      rewrite add_whens_typeof; auto.
  Qed.

  Fact normalize_fby_wt_eq : forall G vars e0s es anns es' eqs' st st',
      Forall (wt_exp G (vars++(st_tys st))) e0s ->
      Forall (wt_exp G (vars++(st_tys st))) es ->
      Forall2 (fun e0 a => typeof e0 = [fst a]) e0s anns ->
      Forall2 (fun e a => typeof e = [fst a]) es anns ->
      Forall (fun '(_, cl) => wt_nclock vars cl) anns ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    intros G vars e0s es anns es' eqs' st st' Hwt1 Hwt2 Hty1 Hty2 Hclock Hnorm.
    unfold normalize_fby in Hnorm. repeat inv_bind.
    eapply map_bind2_wt_eq in H; eauto.
    - intros; destruct a as [[e0 e] a]...
    - repeat rewrite_Forall_forall. destruct x as [[e0 e] [ty cl]].
      specialize (fby_iteexp_spec e0 e ty cl) as [[c [? Hspec]]|Hspec]; subst;
        rewrite Hspec in H5; clear Hspec;
          repeat inv_bind; inv H8.
      + repeat constructor; simpl.
        * repeat simpl_In.
          apply Hwt2 in H8. repeat solve_incl.
        * rewrite app_nil_r.
          repeat simpl_nth. repeat simpl_length.
          specialize (H1 _ _ _ _ _ H4 H13 H12); simpl in H1. congruence.
        * f_equal. apply Op.type_init_type.
        * repeat simpl_In.
          apply Hclock in H4. repeat solve_incl.
        * apply fresh_ident_In in H9.
          apply in_or_app; right.
          apply st_follows_tys_incl in H7. apply H7.
          rewrite st_anns_tys_In. exists (fst cl). exists false. assumption.
      + unfold init_var_for_clock in H5.
        destruct (find _ _) eqn:Hfind; [destruct p | destruct (fresh_ident _ _) eqn:Hfresh];
          inv H5; inv H10; repeat constructor; simpl; try rewrite app_nil_r.
        1,2: eapply add_whens_wt_exp; eauto; simpl.
        5,6: rewrite add_whens_typeof; eauto; simpl.
        1,6: f_equal; apply Op.type_true_const.
        2,4: f_equal; apply Op.type_false_const.
        1,2: repeat simpl_In; apply Hclock in H4; destruct cl; inv H4; simpl in *; repeat solve_incl.
        * simpl_In. apply Hclock in H4. repeat solve_incl.
        * apply fresh_ident_In in Hfresh.
          assert (incl (st_tys x3) (st_tys st')) as Hincl by repeat solve_incl.
          apply in_or_app. right. apply Hincl.
          rewrite st_anns_tys_In. exists (fst cl). exists true. assumption.
        * inv H5.
  Qed.

  Fact normalize_reset_wt_eq : forall G vars e e' eqs' st st',
      wt_exp G (vars++(st_tys st)) e ->
      typeof e = [Op.bool_type] ->
      normalize_reset e st = (e', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof.
    intros G vars e e' eqs' st st' Hwt Hty Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind.
    - constructor.
    - destruct (hd _) as [? [? ?]] eqn:Hann; simpl in *. repeat inv_bind.
      repeat constructor; simpl.
      + repeat solve_incl.
      + rewrite app_nil_r. rewrite Hty.
        repeat constructor.
        apply fresh_ident_In in H.
        apply in_or_app; right.
        unfold st_tys, idty.
        repeat simpl_In.
        exists (x, (t, c)); simpl; split; auto.
        2: simpl_In; exists (x, ((t, c), false)); auto.
        destruct (annot e) eqn:Hannot; simpl in Hann; inv Hann. reflexivity.
        destruct e; simpl in *; inv Hannot; inv Hty; auto;
          try destruct l1; try destruct l2; simpl in *; subst; inv H1; reflexivity.
  Qed.

  Definition default_ann : ann := (Op.bool_type, (Cbase, None)).

  Fact normalize_exp_wt_eq : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwt Hnorm;
      simpl in Hnorm; repeat inv_bind.
    - (* const *) constructor.
    - (* var *) constructor.
    - (* unop *) inv Hwt...
    - (* binop *)
      inv Hwt.
      rewrite Forall_app.
      split; eauto.
      eapply IHe1 in H; eauto.
      solve_forall. eapply wt_equation_incl; [| eauto].
      eapply normalize_exp_st_follows in H0.
      repeat solve_incl.
    - (* fby *)
      inv Hwt.
      repeat rewrite Forall_app.
      repeat split; eauto.
      + rewrite Forall_map.
        solve_forall.
        destruct x as [[x ?] ?].
        repeat constructor.
        * repeat simpl_In.
          eapply normalize_fby_wt_exp with (G:=G) (vars:=vars) in H3...
          -- rewrite Forall_forall in H3...
             apply H3 in H5. repeat solve_incl.
          -- eapply map_bind2_normalize_exp_wt_exp in H1...
             solve_forall. repeat solve_incl.
          -- eapply map_bind2_normalize_exp_wt_exp in H2...
          -- specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H1) as Hnumstreams.
             eapply map_bind2_normalize_exp_typesof in H1...
             rewrite <- Forall2_map_2 with (P:=(fun e0 a => typeof e0 = [a])) (f:=fst).
             rewrite <- H11. rewrite <- H1.
             clear H1 H3 H10. induction x2; simpl in *...
             rewrite Forall_app in Hnumstreams; destruct Hnumstreams.
             unfold typesof in *. rewrite flat_map_concat_map in *. rewrite map_app; rewrite concat_app.
             apply Forall2_app... clear IHx2.
             induction a1; simpl...
             inv H1. rewrite <- length_typeof_numstreams in H13. singleton_length.
             constructor...
          -- specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H2) as Hnumstreams.
             eapply map_bind2_normalize_exp_typesof in H2...
             rewrite <- Forall2_map_2 with (P:=(fun e0 a => typeof e0 = [a])) (f:=fst).
             rewrite <- H10. rewrite <- H2.
             clear H2 H3 H11. induction x9; simpl in *...
             rewrite Forall_app in Hnumstreams; destruct Hnumstreams.
             unfold typesof in *. rewrite flat_map_concat_map in *. rewrite map_app; rewrite concat_app.
             apply Forall2_app... clear IHx9.
             induction a1; simpl...
             inv H2. rewrite <- length_typeof_numstreams in H13. singleton_length.
             constructor...
          -- rewrite Forall_forall in *; intros [ty cl] Hin.
             apply H12. repeat simpl_In. exists (ty, cl)...
        * clear H H0 H12.
          specialize (normalize_fby_numstreams _ _ _ _ _ _ _ H3) as Hnumstreams. rewrite Forall_forall in Hnumstreams.
          simpl. rewrite app_nil_r.
          assert (numstreams e = 1).
          { apply Hnumstreams. simpl_length. simpl_length. repeat simpl_In... }
          rewrite <- length_typeof_numstreams in H. singleton_length.
          repeat constructor.
          apply in_or_app. right. eapply (idents_for_anns_incl_ty _ _ _ _ H4).
          specialize (normalize_fby_numstreams _ _ _ _ _ _ _ H3) as Hnum.
          assert (length (concat x2) = length (annots e0s)) by (eapply map_bind2_normalize_exp_length; eauto).
          assert (length (concat x9) = length (annots es)) by (eapply map_bind2_normalize_exp_length; eauto).
          rewrite <- length_typesof_annots in *.
          assert (length x5 = length a) by (eapply normalize_fby_length in H3; solve_length).
          assert (length x8 = length a) by (eapply idents_for_anns_length in H4; auto).
          apply normalize_fby_typeof in H3; try solve_length...
          repeat simpl_nth.
          unfold idty. repeat simpl_In.
          exists (x, a0); simpl... split.
          -- f_equal.
             apply idents_for_anns_values in H4.
             rewrite Forall2_forall2 in H4; destruct H4 as [_ H4].
             repeat simpl_length.
             specialize (H4 default_ann (xH, default_ann) _ _ _ H5 eq_refl eq_refl).
             destruct nth as [? [? ?]] eqn:Hnth in H4. destruct nth as [? [? [? ?]]] eqn:Hnth' in H4.
             destruct H4 as [? [? ?]]; subst.
             rewrite <- H15 in Hsingl.
             rewrite concat_length_map_nth with (db:=Op.bool_type) in Hsingl; solve_length.
             2: (solve_forall; rewrite length_typeof_numstreams; eauto).
             inv Hsingl.
             rewrite <- typesof_annots in H3; unfold typesof in H3; rewrite flat_map_concat_map in H3.
             rewrite H3. erewrite map_nth'; solve_length. setoid_rewrite Hnth; simpl.
             rewrite split_nth in H14; inv H14. rewrite split_map_snd.
             erewrite map_nth'; solve_length. setoid_rewrite Hnth'. reflexivity.
          -- repeat simpl_length. rewrite <- H7 in H5.
             eapply nth_In in H5. setoid_rewrite H14 in H5. assumption.
      + eapply map_bind2_wt_eq in H1; eauto.
        rewrite Forall_forall in *; intros.
        specialize (H _ H5 _ _ _ _ _ (H8 _ H5) H6).
        solve_forall. repeat solve_incl.
      + eapply map_bind2_wt_eq in H2; eauto.
        rewrite Forall_forall in *; intros.
        specialize (H0 _ H5 _ _ _ _ _ (H9 _ H5) H6).
        solve_forall. repeat solve_incl.
      + eapply normalize_fby_wt_eq with (G:=G) (vars:=vars) in H3...
        * solve_forall. repeat solve_incl.
        * eapply map_bind2_normalize_exp_wt_exp in H1...
          solve_forall. repeat solve_incl.
        * eapply map_bind2_normalize_exp_wt_exp in H2...
        * specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H1) as Hnumstreams.
          eapply map_bind2_normalize_exp_typesof in H1...
          rewrite <- Forall2_map_2 with (P:=(fun e0 a => typeof e0 = [a])) (f:=fst).
          rewrite <- H11. rewrite <- H1.
          clear H1 H3 H10. induction x2; simpl in *...
          rewrite Forall_app in Hnumstreams; destruct Hnumstreams.
          unfold typesof in *. rewrite flat_map_concat_map in *. rewrite map_app; rewrite concat_app.
          apply Forall2_app... clear IHx2.
          induction a0; simpl...
          inv H1. rewrite <- length_typeof_numstreams in H7. singleton_length.
          constructor...
        * specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H2) as Hnumstreams.
          eapply map_bind2_normalize_exp_typesof in H2...
          rewrite <- Forall2_map_2 with (P:=(fun e0 a => typeof e0 = [a])) (f:=fst).
          rewrite <- H10. rewrite <- H2.
          clear H2 H3 H11. induction x9; simpl in *...
          rewrite Forall_app in Hnumstreams; destruct Hnumstreams.
          unfold typesof in *. rewrite flat_map_concat_map in *. rewrite map_app; rewrite concat_app.
          apply Forall2_app... clear IHx9.
          induction a0; simpl...
          inv H2. rewrite <- length_typeof_numstreams in H7. singleton_length.
          constructor...
        * rewrite Forall_forall in *; intros [ty cl] Hin.
          apply H12. repeat simpl_In. exists (ty, cl)...
    - (* when *)
      inv Hwt; repeat inv_bind.
      eapply map_bind2_wt_eq; eauto.
      rewrite Forall_forall in *; intros.
      eapply H in H2; eauto.
      solve_forall.
      eapply wt_equation_incl; [| eauto]. repeat solve_incl.
    - (* merge *)
      inv Hwt.
      destruct is_control; repeat inv_bind.
      + (* control *)
        apply Forall_app; split.
        * eapply map_bind2_wt_eq in H1; eauto.
          rewrite Forall_forall in *; intros.
          eapply H in H4; eauto.
          solve_forall. repeat solve_incl.
        * eapply map_bind2_wt_eq in H2; eauto.
          rewrite Forall_forall in *; intros.
          eapply H0 in H4; eauto.
          solve_forall. repeat solve_incl.
      + (* exp *)
        repeat rewrite Forall_app; repeat split.
        * solve_forall.
          destruct x0 as [xs es].
          assert (length (concat x3) = length (annots ets)) as Hlen1 by (eapply map_bind2_normalize_exp_length; eauto).
          assert (length (concat x7) = length (annots efs)) as Hlen2 by (eapply map_bind2_normalize_exp_length; eauto).
          specialize (idents_for_anns_length _ _ _ _ H3) as Hlen3.
          repeat constructor. rewrite <- length_typesof_annots in *.
          -- specialize (idents_for_anns_st_follows _ _ _ _ H3) as Hfollows.
             apply idents_for_anns_values in H3.
             repeat rewrite_Forall_forall. repeat simpl_length.
             repeat simpl_nth. repeat simpl_length.
             destruct (nth x9 _ _) eqn:Hnth1 in H16; subst.
             destruct (nth x9 _ _) as [[? ?] ?] eqn:Hnth2 in H17; subst.
             erewrite combine_nth in Hnth2; [| solve_length]; inv Hnth2.
             erewrite combine_nth in H13; [| solve_length]; inv H13.
             simpl in H11. destruct x1; [clear H11| omega]. simpl in H12; subst.
             constructor; simpl.
             ++ rewrite <- H16; repeat constructor.
                eapply map_bind2_normalize_exp_wt_exp in H1; solve_forall.
                rewrite Forall_forall in H1.
                rewrite <- Hlen1 in l. eapply nth_In in l. apply H1 in l.
                eapply wt_exp_incl; [| eauto]. repeat solve_incl.
             ++ rewrite <- H17; repeat constructor.
                eapply map_bind2_normalize_exp_wt_exp in H2; solve_forall.
                rewrite Forall_forall in H2.
                rewrite <- Hlen2 in l2. eapply nth_In in l2. apply H2 in l2.
                eapply wt_exp_incl; [| eauto]. repeat solve_incl.
             ++ eapply nth_In in H7. rewrite H14 in H7.
                apply in_or_app...
             ++ rewrite app_nil_r.
                specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H1) as Hnumstreams.
                eapply map_bind2_normalize_exp_typesof in H1; [| rewrite Forall_forall in *; intros; auto].
                rewrite <- H16. rewrite <- H15. rewrite <- typesof_annots. rewrite <- H1.
                erewrite concat_length_map_nth.
                unfold typesof; rewrite flat_map_concat_map... solve_length.
                solve_forall. rewrite length_typeof_numstreams...
             ++ rewrite app_nil_r.
                specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H2) as Hnumstreams.
                eapply map_bind2_normalize_exp_typesof in H2; [| rewrite Forall_forall in *; intros; auto].
                rewrite <- H15. rewrite <- H17. repeat rewrite <- typesof_annots in *. replace (typesof efs) in *. rewrite <- H2.
                erewrite concat_length_map_nth.
                unfold typesof; rewrite flat_map_concat_map... solve_length.
                solve_forall. rewrite length_typeof_numstreams...
             ++ repeat solve_incl.
                Unshelve. 1,2,4: exact (hd_default []). exact Op.bool_type. exact (x, default_ann).
          -- rewrite <- length_typesof_annots in *.
             repeat simpl_nth. repeat simpl_length.
             Unshelve. 2,5: exact (hd_default []). 3,4:exact (xH, default_ann). 2,3:exact (hd_default [], hd_default [], Op.bool_type).
             destruct (nth x0 x6 _) eqn:Hnth1.
             destruct (nth x0 (combine _ _) _) as [[? ?] ?] eqn:Hnth2.
             simpl. repeat constructor; subst.
             repeat simpl_nth. Unshelve. 2:exact default_ann.
             apply in_or_app. right. apply (idents_for_anns_incl_ty _ _ _ _ H3).
             apply idents_for_anns_values in H3.
             repeat rewrite Forall2_map_1 in H3. repeat rewrite map_map in H3; simpl in H3.
             rewrite Forall2_forall2 in H3; destruct H3 as [_ H3].
             eapply H3 with (a:=default_ann) in H4... destruct nck. destruct a as [? [? ?]]. destruct H4 as [? [? ?]].
             unfold idty. repeat simpl_In.
             exists (i, (t, (c0, o0))); subst; split; auto.
             setoid_rewrite <- Hnth1. eapply nth_In; solve_length.
        * eapply map_bind2_wt_eq in H1; eauto.
          rewrite Forall_forall in *; intros.
          eapply H in H4; [| eauto | eauto].
          solve_forall. repeat solve_incl.
        * eapply map_bind2_wt_eq in H2; eauto.
          rewrite Forall_forall in *; intros.
          eapply H0 in H4; [| eauto | eauto].
          solve_forall. repeat solve_incl.
    - (* ite *)
      inv Hwt.
      destruct is_control; repeat inv_bind.
      + (* control *)
        repeat rewrite Forall_app; repeat split.
        * eapply IHe in H1...
          solve_forall. repeat solve_incl.
        * eapply map_bind2_wt_eq in H2...
          rewrite Forall_forall in *; intros.
          eapply H in H9; eauto.
          solve_forall. repeat solve_incl.
        * eapply map_bind2_wt_eq in H3...
          rewrite Forall_forall in *; intros.
          eapply H0 in H9; eauto.
          solve_forall. repeat solve_incl.
      + (* exp *)
        repeat rewrite Forall_app; repeat split.
        * solve_forall.
          destruct x2 as [xs es].
          assert (length (concat x5) = length (annots ets)) as Hlen1 by (eapply map_bind2_normalize_exp_length; eauto).
          assert (length (concat x9) = length (annots efs)) as Hlen2 by (eapply map_bind2_normalize_exp_length; eauto).
          specialize (idents_for_anns_length _ _ _ _ H4) as Hlen3.
          repeat constructor. rewrite <- length_typesof_annots in *.
          -- specialize (idents_for_anns_st_follows _ _ _ _ H4) as Hfollows.
             apply idents_for_anns_values in H4.
             repeat rewrite_Forall_forall. repeat simpl_length.
             repeat simpl_nth. repeat simpl_length.
             destruct (nth _ _ _) eqn:Hnth1 in H17; subst.
             destruct (nth _ _ _) as [[? ?] ?] eqn:Hnth2 in H18; subst.
             erewrite combine_nth in Hnth2; [| solve_length]; inv Hnth2.
             erewrite combine_nth in H15; [| solve_length]; inv H15.
             simpl in H13. destruct x3; [clear H13| omega]. simpl in H14; subst.
             constructor; simpl.
             ++ apply hd_default_wt_exp.
                eapply normalize_exp_wt_exp in H1...
                solve_forall. repeat solve_incl.
             ++ rewrite <- H17; repeat constructor.
                eapply map_bind2_normalize_exp_wt_exp in H2; solve_forall.
                rewrite Forall_forall in H2.
                rewrite <- Hlen1 in l. eapply nth_In in l. apply H2 in l.
                eapply wt_exp_incl; [| eauto]. repeat solve_incl.
             ++ rewrite <- H18; repeat constructor.
                eapply map_bind2_normalize_exp_wt_exp in H3; solve_forall.
                rewrite Forall_forall in H3.
                rewrite <- Hlen2 in l. eapply nth_In in l. apply H3 in l.
                eapply wt_exp_incl; [| eauto]. repeat solve_incl.
             ++ assert (length x = numstreams e) as Hlength by (eapply normalize_exp_length; eauto).
                specialize (normalize_exp_numstreams _ _ _ _ _ _ H1) as Hnumstreams.
                rewrite <- length_typeof_numstreams in Hlength. rewrite H8 in Hlength; simpl in Hlength.
                eapply normalize_exp_typeof in H1...
                singleton_length. congruence.
             ++ rewrite app_nil_r.
                specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H2) as Hnumstreams.
                eapply map_bind2_normalize_exp_typesof in H2; [| rewrite Forall_forall in *; intros; auto].
                rewrite <- H16. rewrite <- H17. rewrite <- typesof_annots. rewrite <- H2.
                erewrite concat_length_map_nth.
                unfold typesof; rewrite flat_map_concat_map... solve_length.
                solve_forall. rewrite length_typeof_numstreams...
             ++ rewrite app_nil_r.
                specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H3) as Hnumstreams.
                eapply map_bind2_normalize_exp_typesof in H3; [| rewrite Forall_forall in *; intros; auto].
                rewrite <- H16. rewrite <- H18. repeat rewrite <- typesof_annots in *; replace (typesof efs) in *. rewrite <- H3.
                erewrite concat_length_map_nth.
                unfold typesof; rewrite flat_map_concat_map... solve_length.
                solve_forall. rewrite length_typeof_numstreams...
             ++ repeat solve_incl.
                Unshelve. 1,2,4: exact (hd_default []). exact Op.bool_type. exact (xH, default_ann).
          -- rewrite <- length_typesof_annots in *.
             repeat simpl_nth. repeat simpl_length.
             Unshelve. 2,5: exact (hd_default []). 3,4:exact (xH, default_ann). 2,3:exact (hd_default [], hd_default [], Op.bool_type).
             destruct (nth x2 x8 _) eqn:Hnth1.
             destruct (nth x2 (combine _ _) _) as [[? ?] ?] eqn:Hnth2.
             simpl. repeat constructor; subst.
             repeat simpl_nth. Unshelve. 2:exact default_ann.
             apply in_or_app. right. apply (idents_for_anns_incl_ty _ _ _ _ H4).
             apply idents_for_anns_values in H4.
             repeat rewrite Forall2_map_1 in H4. repeat rewrite map_map in H4; simpl in H4.
             rewrite Forall2_forall2 in H4; destruct H4 as [_ H4].
             eapply H4 with (a:=default_ann) in H9... destruct nck. destruct a as [? [? ?]]. destruct H9 as [? [? ?]].
             unfold idty. repeat simpl_In.
             exists (i, (t, (c0, o0))); subst; split; auto.
             setoid_rewrite <- Hnth1. eapply nth_In; solve_length.
        * eapply IHe in H1... solve_forall. repeat solve_incl.
        * eapply map_bind2_wt_eq in H2; eauto.
          rewrite Forall_forall in *; intros.
          eapply H in H12; [| eauto | eauto].
          solve_forall. repeat solve_incl.
        * eapply map_bind2_wt_eq in H3; eauto.
          rewrite Forall_forall in *; intros.
          eapply H0 in H12; [| eauto | eauto].
          solve_forall. repeat solve_incl.
    - (* app *)
      inv Hwt; repeat inv_bind; repeat econstructor; simpl; eauto.
      1,6: (eapply map_bind2_wt_exp with (vars0:=(vars++(st_tys st'))) in H2; eauto;
            solve_forall;
            try eapply normalize_exp_wt_exp in H4; try eapply normalize_exp_wt_exp in H6; eauto;
            solve_forall; repeat solve_incl).
      1,5: eapply map_bind2_normalize_exp_typesof in H2; eauto; congruence.
      1,4: (solve_forall; repeat solve_incl).
      1,5: rewrite app_nil_r.
      + clear H0 H8 H10 H11 H12.
        rewrite Forall2_map_1. rewrite Forall2_map_2.
        specialize (idents_for_anns_incl_ty _ _ _ _ H3) as Hincl.
        apply idents_for_anns_values in H3.
        rewrite Forall2_swap_args in H3.
        eapply Forall2_impl_In; [| eauto].
        intros [? [? [? ?]]] [? [? ?]] HIn1 HIn2 [? [? ?]]; subst; simpl.
        apply in_or_app. right. apply Hincl.
        unfold idty. repeat simpl_In. exists (i, (t0, (c0, Some i))); auto.
      + clear H H0 H8 H10 H11 H12.
        rewrite Forall2_map_1. rewrite Forall2_map_2.
        specialize (idents_for_anns_incl_ty _ _ _ _ H3) as Hincl.
        apply idents_for_anns_values in H3.
        rewrite Forall2_swap_args in H3.
        eapply Forall2_impl_In; [| eauto].
        intros [? [? [? ?]]] [? [? ?]] HIn1 HIn2 [? [? ?]]; subst; simpl.
        apply in_or_app. right. apply Hincl.
        unfold idty. repeat simpl_In. exists (i, (t0, (c0, Some i))); auto.
      + eapply map_bind2_wt_eq in H2; eauto.
        rewrite Forall_forall in *; intros.
        eapply H0 in H4; eauto.
        solve_forall. repeat solve_incl.
      + eapply normalize_exp_wt_exp in H1...
        eapply hd_default_wt_exp in H1...
        eapply normalize_reset_wt_exp in H4...
        eapply map_bind2_st_follows in H2; solve_forall.
        repeat solve_incl.
      + specialize (normalize_exp_numstreams _ _ _ _ _ _ H1) as Hlength.
        eapply normalize_exp_typeof in H1...
        eapply normalize_reset_typeof_bool in H4...
        rewrite H14 in H1.
        destruct x2; simpl in *; try congruence.
        inv Hlength. rewrite <- length_typeof_numstreams in H7.
        destruct (typeof e); simpl in *; try congruence.
        destruct l; simpl in *; try congruence.
      + repeat rewrite Forall_app. repeat split.
        * eapply H in H1...
          apply normalize_reset_st_follows in H4.
          apply map_bind2_st_follows in H2; solve_forall.
          apply idents_for_anns_st_follows in H3.
          solve_forall. repeat solve_incl.
        * assert (length x2 = numstreams r) as Hlength by (eapply normalize_exp_length; eauto).
          specialize (normalize_exp_typeof _ _ _ _ _ _ _ _ H13 H1) as Htypeof.
          rewrite H14 in Htypeof.
          eapply normalize_exp_wt_exp in H1... eapply hd_default_wt_exp in H1...
          eapply normalize_reset_wt_eq in H4...
          -- solve_forall. repeat solve_incl.
          -- rewrite <- length_typeof_numstreams in Hlength. rewrite H14 in Hlength.
             destruct x2; simpl in *; try congruence.
             destruct x2; simpl in *; try congruence.
             rewrite app_nil_r in Htypeof...
        * eapply map_bind2_wt_eq in H2; eauto.
          rewrite Forall_forall in *; intros.
          eapply H0 in H6...
          solve_forall. repeat solve_incl.
  Qed.

  Corollary normalize_exps_wt_eq : forall G vars es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_exps es st = (es', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    intros G vars es es' eqs' st st' Hwt Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_wt_eq in H...
    solve_forall.
    eapply normalize_exp_wt_eq in H1...
    solve_forall. repeat solve_incl.
  Qed.

  Fact normalize_rhs_wt_eq : forall G vars e keep_fby es' eqs' st st',
      wt_exp G vars e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    intros G vars e keep_fby es' eqs' st st' Hwt Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try eapply normalize_exp_wt_eq in Hnorm; eauto;
        [destruct keep_fby|].
    - (* fby *)
      inv Hwt. repeat inv_bind.
      repeat rewrite Forall_app. repeat split.
      + eapply normalize_exps_wt_eq in H...
        solve_forall. repeat solve_incl.
      + eapply normalize_exps_wt_eq in H0...
        solve_forall. repeat solve_incl.
      + eapply normalize_fby_wt_eq in H1...
        * eapply normalize_exps_wt_exp in H...
          solve_forall. repeat solve_incl.
        * eapply normalize_exps_wt_exp in H0...
        * specialize (normalize_exps_numstreams _ _ _ _ _ H) as Hnumstreams.
          eapply normalize_exps_typesof in H...
          rewrite <- Forall2_map_2 with (P:=(fun e0 a => typeof e0 = [a])) (f:=fst).
          rewrite <- H5. rewrite <- H.
          clear H H1 H4 H5. induction x; simpl...
          inv Hnumstreams. rewrite <- length_typeof_numstreams in H4. singleton_length.
          constructor...
        * specialize (normalize_exps_numstreams _ _ _ _ _ H0) as Hnumstreams.
          eapply normalize_exps_typesof in H0...
          rewrite <- Forall2_map_2 with (P:=(fun e0 a => typeof e0 = [a])) (f:=fst).
          rewrite <- H4. rewrite <- H0.
          clear H H0 H1 H4 H5. induction x2; simpl...
          inv Hnumstreams. rewrite <- length_typeof_numstreams in H1. singleton_length.
          constructor...
        * rewrite Forall_forall in *; intros.
          destruct x5. eapply H6. simpl_In.
          exists (t, n)...
    - eapply normalize_exp_wt_eq...
    - (* app *)
      repeat inv_bind.
      apply Forall_app. split.
      + inv Hwt; repeat inv_bind; try constructor.
        apply Forall_app. split.
        * eapply normalize_exp_wt_eq in H...
          solve_forall. repeat solve_incl.
        * eapply normalize_reset_wt_eq with (G:=G) (vars:=vars) in H1...
          -- solve_forall. repeat solve_incl.
          -- eapply hd_default_wt_exp.
             eapply normalize_exp_wt_exp in H...
          -- specialize (normalize_exp_numstreams _ _ _ _ _ _ H) as Hnumstreams.
             eapply normalize_exp_typeof in H...
             rewrite H11 in H.
             destruct x4; simpl in *; try congruence.
             inv Hnumstreams. rewrite <- length_typeof_numstreams in H4. singleton_length.
      + inv Hwt; eapply normalize_exps_wt_eq in H0...
  Qed.

  Corollary normalize_rhss_wt_eq : forall G vars es keep_fby es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    intros G vars es keep_fby es' eqs' st st' Hwt Hnorm.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_wt_eq in H...
    solve_forall. eapply normalize_rhs_wt_eq in H1...
    solve_forall. repeat solve_incl.
  Qed.

  Fact normalize_equation_wt_eq : forall G vars eq to_cut eqs' st st',
      wt_equation G vars eq ->
      normalize_equation to_cut eq st = (eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    intros G vars eq to_cut eqs' st st' Hwt Hnorm.
    destruct eq as [xs es]; simpl in Hnorm.
    repeat inv_bind. destruct Hwt.
    apply Forall_app. split.
    - specialize (normalize_rhss_typesof _ _ _ _ _ _ _ _ H0 H) as Htypeof.
      eapply normalize_rhss_wt_exp in H...
      rewrite <- Htypeof in H1.
      clear Htypeof. revert xs H1.
      induction x; intros xs H1; constructor; simpl in H1.
      + inv H. repeat constructor...
        simpl. rewrite app_nil_r.
        repeat rewrite_Forall_forall.
        * rewrite app_length in H.
          rewrite firstn_length. rewrite H.
          rewrite length_typeof_numstreams.
          apply Nat.min_l. omega.
        * rewrite firstn_length in H2.
          rewrite PeanoNat.Nat.min_glb_lt_iff in H2; destruct H2 as [Hlen1 Hlen2].
          specialize (H1 a0 b _ _ _ Hlen2 eq_refl eq_refl).
          rewrite app_nth1 in H1. 2: rewrite length_typeof_numstreams...
          rewrite nth_firstn_1...
          apply in_or_app...
      + inv H. apply IHx...
        repeat rewrite_Forall_forall.
        * rewrite app_length in H.
          rewrite skipn_length. rewrite H.
          rewrite length_typeof_numstreams. omega.
        * rewrite skipn_length in H2.
          rewrite nth_skipn.
          assert (n + numstreams a < length xs) as Hlen by omega.
          specialize (H1 a0 b _ _ _ Hlen eq_refl eq_refl).
          rewrite app_nth2 in H1. 2: rewrite length_typeof_numstreams; omega.
          rewrite length_typeof_numstreams in H1.
          replace (n + numstreams a - numstreams a) with n in H1 by omega...
    - eapply normalize_rhss_wt_eq in H...
  Qed.

  Corollary normalize_equations_wt_eq : forall G vars eqs to_cut eqs' st st',
      Forall (wt_equation G vars) eqs ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    induction eqs; intros to_cut eqs' st st' Hwt Hnorm;
      simpl in Hnorm; repeat inv_bind.
    - constructor.
    - inv Hwt. apply Forall_app. split...
      eapply normalize_equation_wt_eq in H...
      solve_forall. repeat solve_incl.
  Qed.

  Definition st_clocks (st : fresh_st ((Op.type * clock) * bool)) : list clock :=
    map snd (map fst (map snd (st_anns st))).

  Fact fresh_ident_wt_nclock : forall vars ty cl b id st st',
      Forall (wt_clock vars) (st_clocks st) ->
      wt_clock vars cl ->
      fresh_ident (ty, cl, b) st = (id, st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof.
    intros vars ty cl b id st st' Hclocks Hwt Hfresh.
    apply fresh_ident_anns in Hfresh.
    unfold st_clocks in *. setoid_rewrite Hfresh; simpl.
    constructor; auto.
  Qed.

  Corollary idents_for_anns_wt_nclock : forall vars anns ids st st',
      Forall (wt_clock vars) (st_clocks st) ->
      Forall (wt_nclock vars) (map snd anns) ->
      idents_for_anns anns st = (ids, st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof.
    induction anns; intros ids st st' Hclocks Hwt Hidents;
      simpl in Hidents; repeat inv_bind.
    - assumption.
    - inv Hwt. destruct a as [ty [cl ?]]. repeat inv_bind.
      eapply IHanns in H0; eauto.
      inv H1.
      eapply fresh_ident_wt_nclock; eauto.
  Qed.

  Fact map_bind2_wt_nclock {A A1 A2 : Type} :
    forall vars (k : A -> FreshAnn (A1 * A2)) a a1s a2s st st',
      Forall (wt_clock vars) (st_clocks st) ->
      map_bind2 k a st = (a1s, a2s, st') ->
      Forall (fun a => forall a1s a2s st st',
                  Forall (wt_clock vars) (st_clocks st) ->
                  k a st = (a1s, a2s, st') ->
                  Forall (wt_clock vars) (st_clocks st')) a ->
      Forall (wt_clock vars) (st_clocks st').
  Proof.
    induction a; intros a1s a2s st st' Hclocks Hmap Hf;
      simpl in Hmap; repeat inv_bind.
    - assumption.
    - inv Hf.
      specialize (H3 _ _ _ _ Hclocks H).
      eapply IHa in H3; eauto.
  Qed.

  Fact normalize_fby_wt_nclock : forall vars e0s es anns es' eqs' st st',
      Forall (wt_clock vars) (st_clocks st) ->
      Forall (wt_nclock vars) (map snd anns) ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof with eauto.
    intros vars e0s es anns es' eqs' st st' Hclocks Hwt Hnorm.
    unfold normalize_fby in Hnorm. repeat inv_bind.
    eapply map_bind2_wt_nclock in H...
    solve_forall. destruct x as [[e0 e] [ty cl]].
    specialize (fby_iteexp_spec e0 e ty cl) as [[? [? Hspec]]| Hspec]; subst;
      rewrite Hspec in H2; clear Hspec; repeat inv_bind.
    - assumption.
    - repeat simpl_In.
      unfold init_var_for_clock in H2.
      assert (wt_nclock vars cl) as Hcl.
      { rewrite Forall_forall in Hwt. eapply Hwt.
        repeat simpl_In. exists (ty, cl)... }
      destruct (find _ _).
      + destruct p. inv H2.
        inv Hcl.
        eapply fresh_ident_wt_nclock in H3...
      + destruct (fresh_ident _ _) eqn:Hfresh. inv H2.
        inv Hcl.
        eapply fresh_ident_wt_nclock in Hfresh...
        eapply fresh_ident_wt_nclock in H3...
  Qed.

  Fact normalize_reset_wt_nclock : forall vars e e' eqs' st st',
      Forall (wt_clock vars) (clockof e) ->
      Forall (wt_clock vars) (st_clocks st) ->
      normalize_reset e st = (e', eqs', st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof with eauto.
  intros vars e e' eqs' st st' Hwt Hclocks Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind.
    - assumption.
    - destruct (hd _) as [? [? ?]] eqn:Hhd; simpl in Hnorm.
      repeat inv_bind.
      eapply fresh_ident_wt_nclock in H...
      destruct e; inv Hwt; simpl in Hhd;
        unfold clock_of_nclock, stripname in *; simpl in *.
      1,2,3,4: (inv Hhd; repeat constructor; auto).
      + symmetry in H1. apply map_eq_nil in H1. subst. inv Hhd. repeat constructor.
      + destruct l1; simpl in *; inv Hhd; repeat constructor.
        inv H0...
      + destruct l0. symmetry in H1. apply map_eq_nil in H1; simpl in *; subst; simpl in *. inv Hhd. repeat constructor.
      + destruct l0; destruct l0; simpl in *; try congruence. inv H0. inv Hhd...
      + symmetry in H1. apply map_eq_nil in H1. destruct l1; simpl in *; subst; simpl in *. inv Hhd. repeat constructor.
      + destruct l1; destruct l1; simpl in *; try congruence. inv H0. inv Hhd...
      + destruct l1; destruct l1; simpl in *; try congruence. inv Hhd. repeat constructor.
      + destruct l1; destruct l1; simpl in *; try congruence. inv H0. inv Hhd...
      + symmetry in H1. apply map_eq_nil in H1. subst. simpl in *. inv Hhd. repeat constructor.
      + destruct l0; simpl in *; try congruence. destruct a; destruct n; simpl in *.
        inv H0. inv Hhd...
  Qed.

  Fact normalize_exp_wt_nclock : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      Forall (wt_clock vars) (st_clocks st) ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwt Hclocks Hnorm;
      inv Hwt; simpl in Hnorm; repeat inv_bind.
    - (* const *) assumption.
    - (* var *) assumption.
    - (* unop *) eauto.
    - (* binop *) eauto.
    - (* fby *)
      eapply map_bind2_wt_nclock in H1...
      2: rewrite Forall_forall in *; intros...
      eapply map_bind2_wt_nclock in H2...
      2: rewrite Forall_forall in *; intros...
      eapply normalize_fby_wt_nclock in H3...
      eapply idents_for_anns_wt_nclock in H9...
    - (* when *)
      eapply map_bind2_wt_nclock in H0...
      rewrite Forall_forall in *; intros...
    - (* merge *)
      destruct is_control; repeat inv_bind.
      1,2: (eapply map_bind2_wt_nclock in H1; eauto; [|rewrite Forall_forall in *; intros; eauto];
            eapply map_bind2_wt_nclock in H2; eauto; try (solve [rewrite Forall_forall in *; intros; eauto])).
      eapply idents_for_anns_wt_nclock in H3...
      rewrite map_map; simpl.
      solve_forall. simpl_In. assumption.
    - (* ite *)
      destruct is_control; repeat inv_bind.
      1,2: (eapply IHe in H1; eauto;
            eapply map_bind2_wt_nclock in H2; eauto; [|rewrite Forall_forall in *; intros; eauto];
            eapply map_bind2_wt_nclock in H3; eauto; try (solve [rewrite Forall_forall in *; intros; eauto])).
      eapply idents_for_anns_wt_nclock in H4...
      rewrite map_map; simpl.
      solve_forall. simpl_In. assumption.
    - (* app *)
      eapply map_bind2_wt_nclock in H1...
      2: rewrite Forall_forall in *; intros...
      eapply idents_for_anns_wt_nclock in H2...
      rewrite Forall_forall in *; intros.
      repeat simpl_In. eauto.
    - (* app (reset) *)
      assert (length x2 = numstreams r) as Hlength by (eapply normalize_exp_length; eauto).
      assert (clocksof x2 = clockof r) as Hannot.
      { eapply normalize_exp_annot in H1; eauto.
        rewrite clocksof_without_names. rewrite clockof_without_names. congruence.
      }
      specialize (normalize_exp_wt_exp _ _ _ _ _ _ _ _ H10 H1) as Hwt.
      apply hd_default_wt_exp in Hwt.
      eapply H in H1...
      eapply normalize_reset_wt_nclock in H4...
      eapply map_bind2_wt_nclock in H2...
      2: rewrite Forall_forall in *; intros...
      eapply idents_for_anns_wt_nclock in H3...
      rewrite Forall_forall in *; intros. simpl_In...
      apply wt_exp_clockof in H10. (* annots => clocksof *)
      assert (length x2 = 1).
      { rewrite Hlength. rewrite <- length_annot_numstreams.
        rewrite typeof_annot in H11. erewrite <- map_length. rewrite H11. reflexivity. }
      singleton_length. rewrite Hannot...
  Qed.

  Corollary normalize_exps_wt_nclock : forall G vars es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      Forall (wt_clock vars) (st_clocks st) ->
      normalize_exps es st = (es', eqs', st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof.
    intros G vars es es' eqs' st st' Hwt Hclocks Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_wt_nclock in H; eauto.
    solve_forall. eapply normalize_exp_wt_nclock in H2; eauto.
  Qed.

  Corollary normalize_rhs_wt_nclock : forall G vars e keep_fby es' eqs' st st',
      wt_exp G vars e ->
      Forall (wt_clock vars) (st_clocks st) ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof with eauto.
    intros G vars e keep_fby es' eqs' st st' Hwt Hclocks Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try eapply normalize_exp_wt_nclock in Hnorm; eauto;
        inv Hwt; [destruct keep_fby| |].
    - (* fby (keep) *)
      repeat inv_bind.
      eapply normalize_exps_wt_nclock in H...
      eapply normalize_exps_wt_nclock in H0...
      eapply normalize_fby_wt_nclock in H1...
    - (* fby (don't keep) *) eapply normalize_exp_wt_nclock in Hnorm...
    - (* app *)
      repeat inv_bind.
      eapply normalize_exps_wt_nclock in H...
    - (* app (reset) *)
      repeat inv_bind.
      assert (length x4 = numstreams r) as Hlength by (eapply normalize_exp_length; eauto).
      assert (clocksof x4 = clockof r) as Hclockof.
      { eapply normalize_exp_annot in H; eauto.
        rewrite clocksof_without_names. rewrite clockof_without_names. congruence.
      }
      specialize (normalize_exp_wt_exp _ _ _ _ _ _ _ _ H8 H) as Hwt.
      eapply normalize_exp_wt_nclock in H...
      eapply normalize_exps_wt_nclock in H0...
      eapply normalize_reset_wt_nclock in H1...
      assert (length x4 = 1).
      { rewrite Hlength. rewrite typeof_annot in H9. rewrite <- length_annot_numstreams.
        erewrite <- map_length. rewrite H9. reflexivity. }
      singleton_length.
      rewrite Hclockof.
      eapply wt_exp_clockof in H8. assumption.
  Qed.

  Corollary normalize_rhss_wt_nclock : forall G vars es keep_fby es' eqs' st st',
      Forall (wt_exp G vars) es ->
      Forall (wt_clock vars) (st_clocks st) ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof.
    intros G vars es keep_fby es' eqs' st st' Hwt Hclocks Hnorm.
    unfold normalize_rhss in Hnorm. repeat inv_bind.
    eapply map_bind2_wt_nclock in H; eauto.
    solve_forall. eapply normalize_rhs_wt_nclock in H2; eauto.
  Qed.

  Fact normalize_equation_wt_nclock : forall G vars eq to_cut eqs' st st',
      wt_equation G vars eq ->
      Forall (wt_clock vars) (st_clocks st) ->
      normalize_equation to_cut eq st = (eqs', st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof.
    intros G vars eq to_cut eqs' st st' Hwt Hclocks Hnorm.
    destruct eq; simpl in Hnorm. repeat inv_bind.
    destruct Hwt.
    eapply normalize_rhss_wt_nclock in H; eauto.
  Qed.

  Corollary normalize_equations_wt_nclock : forall G vars eqs to_cut eqs' st st',
      Forall (wt_equation G vars) eqs ->
      Forall (wt_clock vars) (st_clocks st) ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof.
    induction eqs; intros to_cut eqs' st st' Hwt Hclocks Hnorm;
      unfold normalize_equations in Hnorm; repeat inv_bind.
    - assumption.
    - inv Hwt.
      eapply normalize_equation_wt_nclock in H; eauto.
  Qed.

  Lemma normalize_node_wt : forall G n to_cut Hwl n',
      wt_node G n ->
      normalize_node to_cut n Hwl = n' ->
      wt_node G n'.
  Proof.
    intros G n to_cut Hwl n' [Hclin [Hclout [Hclvars Heq]]] Hnorm.
    unfold normalize_node in Hnorm. subst.
    repeat constructor; simpl; auto.
    - unfold wt_clocks in *.
      apply Forall_app. split.
      + solve_forall. destruct a as [_ [_ ck]]. unfold idty in *.
        solve_incl. repeat rewrite map_app. repeat solve_incl.
      + remember (normalize_equations _ _ _) as res.
        destruct res as [eqs st']. symmetry in Heqres.
        eapply normalize_equations_wt_nclock in Heqres; eauto.
        * simpl. unfold st_clocks in Heqres.
          solve_forall. rewrite Forall_forall in Heqres.
          destruct x as [? [? ck]].
          eapply wt_clock_incl; [| eapply Heqres].
          -- unfold idty. eapply incl_map.
             solve_incl.
          -- unfold idty in H.
             repeat simpl_In. inv H.
             exists (t, ck); simpl; split; auto.
             simpl_In. exists (t, ck, b); simpl; split; auto.
             simpl_In. eexists; split; [| eauto]. simpl; auto.
        * unfold st_clocks. rewrite init_st_anns; simpl.
          constructor.
    - remember (normalize_equations _ _ _) as res.
      destruct res as [eqs' st']; simpl.
      symmetry in Heqres.
      eapply normalize_equations_wt_eq in Heqres; eauto.
      solve_forall. repeat solve_incl. clear Heqres H.
      unfold st_tys, idty in *. apply incl_app.
      + apply incl_map. apply incl_app; [solve_incl|].
        apply incl_app; [| repeat solve_incl].
        apply incl_appr. apply incl_appl; solve_incl.
      + repeat rewrite map_map; simpl.
        repeat rewrite map_app; simpl.
        apply incl_appr. apply incl_appl. apply incl_appr.
        repeat rewrite map_map; simpl. reflexivity.
  Qed.

  Fact normalize_global_eq : forall G Hwt,
      global_iface_eq G (normalize_global G Hwt).
  Proof.
    induction G; intros Hwt.
    - reflexivity.
    - simpl. apply global_iface_eq_cons; auto.
  Qed.

  Fact normalize_global_names : forall a G Hwt,
      Forall (fun n => (n_name a <> n_name n)%type) G ->
      Forall (fun n => (n_name a <> n_name n)%type) (normalize_global G Hwt).
  Proof.
    induction G; intros Hwt Hnames; simpl.
    - constructor.
    - inv Hnames.
      constructor; eauto.
  Qed.

  Lemma normalize_global_wt : forall G Hwl G',
      wt_global G ->
      normalize_global G Hwl = G' ->
      wt_global G'.
  Proof.
    induction G; intros Hwl G' Hwt Hnorm; simpl in Hnorm; inv Hwt.
    - constructor.
    - constructor.
      + eapply IHG; eauto.
      + remember (normalize_node _ _ _) as n'. symmetry in Heqn'.
        eapply normalize_node_wt in Heqn'; eauto. simpl in Heqn'.
        eapply global_eq_wt_node; eauto.
        eapply normalize_global_eq.
      + eapply normalize_global_names; eauto.
  Qed.

End NTYPING.

Module NTypingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn)
       (Norm : NORMALIZATION Ids Op OpAux Syn Typ)
       <: NTYPING Ids Op OpAux Syn Typ Norm.
  Include NTYPING Ids Op OpAux Syn Typ Norm.
End NTypingFun.
