Require Import Omega.
From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams.
From Coq Require Import List. Import List.ListNotations. Open Scope list_scope.
From Velus Require Import Lustre.LSyntax Lustre.LTyping.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.FullNorm.

(** * Preservation of Typing through Normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type NTYPING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Typ : LTYPING Ids Op Syn)
       (Import Norm : FULLNORM Ids Op OpAux Syn).
  Import Fresh Facts Tactics.

  (** ** Preservation of typeof *)

  (* Fact idents_for_anns_typesof : forall anns ids st st', *)
  (*     idents_for_anns anns st = (ids, st') -> *)
  (*     typesof (map (fun '(id, a) => Evar id a) ids) = map fst anns. *)
  (* Proof. *)
  (*   induction anns as [|[ty [n cl]] anns]; intros ids st st' Hids; *)
  (*     simpl in *; repeat inv_bind; simpl. *)
  (*   - reflexivity. *)
  (*   - f_equal; eauto. *)
  (* Qed. *)

  (* Fact idents_for_anns'_typesof : forall anns ids st st', *)
  (*     idents_for_anns' anns st = (ids, st') -> *)
  (*     typesof (map (fun '(id, a) => Evar id a) ids) = map fst anns. *)
  (* Proof. *)
  (*   induction anns as [|[ty cl] anns]; intros ids st st' Hids; *)
  (*     simpl in *; repeat inv_bind; auto. *)
  (*   destruct cl as [cl [name|]]; repeat inv_bind; simpl; f_equal; eauto. *)
  (* Qed. *)

  Fact normalize_exp_typeof : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st')  ->
      typesof es' = typeof e.
  Proof with eauto.
    intros G vars e is_control es' eqs' st st' Hwt Hnorm.
    eapply normalize_exp_annot in Hnorm...
    rewrite typesof_annots, Hnorm, <- typeof_annot...
  Qed.

  Hint Resolve nth_In.
  Corollary map_bind2_normalize_exp_typesof' :
    forall G vars is_control es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => typesof es' = typeof e) es' es.
  Proof with eauto.
    intros G vars is_control es es' eqs' st st' Hwt Hmap.
    eapply map_bind2_normalize_exp_annots' in Hmap...
    clear Hwt.
    induction Hmap; constructor; eauto.
    rewrite typesof_annots, H, <- typeof_annot...
  Qed.

  Corollary map_bind2_normalize_exp_typesof :
    forall G vars is_control es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      typesof (concat es') = typesof es.
  Proof.
    intros G vars is_control es es' eqs' st st' Hwt Hmap.
    eapply map_bind2_normalize_exp_annots in Hmap; eauto.
    rewrite typesof_annots, Hmap, <- typesof_annots; eauto.
  Qed.
  Hint Resolve map_bind2_normalize_exp_typesof.

  Corollary normalize_exps_typesof : forall G vars es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_exps es st = (es', eqs', st') ->
      typesof es' = typesof es.
  Proof.
    intros G vars es es' eqs' st st' Hwt Hnorm.
    unfold normalize_exps in Hnorm; repeat inv_bind.
    eapply map_bind2_normalize_exp_typesof in H; eauto.
  Qed.

  Fact fby_iteexp_typeof : forall e0 e ann es' eqs' st st',
      fby_iteexp e0 e ann st = (es', eqs', st') ->
      typeof es' = [fst ann].
  Proof.
    intros e0 e [ty cl] es' eqs' st st' Hfby.
    unfold fby_iteexp in Hfby.
    destruct (Norm.is_constant e0); repeat inv_bind; try reflexivity.
  Qed.

  Fact normalize_fby_typeof : forall anns e0s es es' eqs' st st',
      length e0s = length anns ->
      length es = length anns ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      typesof es' = List.map fst anns.
  Proof.
    intros anns e0s es es' eqs' st st' Hlen1 Hlen2 Hfby.
    eapply normalize_fby_annot in Hfby; eauto.
    rewrite typesof_annots, Hfby.
    apply map_ext; intros [? [? ?]]; auto.
  Qed.

  Fact normalize_rhs_typeof : forall G vars e keep_fby es' eqs' st st',
      wt_exp G vars e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      typesof es' = typeof e.
  Proof with eauto.
    intros G vars e keep_fby es' eqs' st st' Hwt Hnorm.
    eapply normalize_rhs_annot in Hnorm...
    rewrite typesof_annots, Hnorm, <- typeof_annot...
  Qed.

  Corollary normalize_rhss_typesof : forall G vars es keep_fby es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      typesof es' = typesof es.
  Proof with eauto.
    intros G vars es keep_fby es' eqs' st st' Hwt Hnorm.
    eapply normalize_rhss_annots in Hnorm...
    rewrite typesof_annots, Hnorm, <- typesof_annots...
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
      st_follows st st' ->
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

  Fact idents_for_anns'_incl_ty : forall anns ids st st',
    idents_for_anns' anns st = (ids, st') ->
    incl (idty ids) (st_tys st').
  Proof.
    intros anns ids st st' Hids.
    apply idents_for_anns'_incl in Hids.
    intros [id ty] Hin.
    unfold st_tys, idty in *.
    repeat simpl_In. inv H.
    exists (id, (ty, c)); split; auto.
    apply Hids. repeat simpl_In.
    exists (id, (ty, (c, o))); auto.
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
    | |- incl (st_anns ?st1) (st_anns _) =>
      eapply st_follows_incl; repeat solve_st_follows
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
      repeat inv_bind.
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

  Fact idents_for_anns'_wt_exp : forall G vars anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      Forall (fun '(ty, cl) => wt_nclock (vars++(idty ids)++st_tys st) cl) anns ->
      Forall (wt_exp G (vars++(idty ids)++st_tys st')) (map (fun '(x, ann) => Evar x ann) ids).
  Proof.
    induction anns; intros ids st st' Hidents Hf;
      repeat inv_bind.
    - constructor.
    - inv Hf. destruct a as [ty [cl ?]]. repeat inv_bind.
      rewrite Forall_map.
      destruct o; repeat inv_bind; econstructor; eauto.
      + repeat constructor; simpl.
        * apply in_or_app. right. constructor; auto.
        * inv H1. destruct x; simpl in *. solve_incl.
          eapply incl_appr', incl_tl', incl_appr'. solve_incl.
      + eapply IHanns in H0.
        * rewrite Forall_map in H0.
          solve_forall. repeat solve_incl.
        * solve_forall. destruct a, x. solve_incl.
          rewrite Permutation.Permutation_middle.
          eapply incl_appr', incl_appr', incl_cons; try solve_incl.
          eapply reuse_ident_In in H. unfold st_tys, idty, idty.
          rewrite in_map_iff. exists (i, (ty, cl)); split; auto.
          rewrite in_map_iff. eexists; split; [|eauto]; eauto.
      + repeat constructor; simpl.
        * apply in_or_app. right. constructor; auto.
        * inv H1. solve_incl; simpl.
          eapply incl_appr', incl_tl', incl_appr'. solve_incl.
      + eapply IHanns in H0.
        * rewrite Forall_map in H0.
          solve_forall. repeat solve_incl.
        * solve_forall. destruct a. solve_incl.
          rewrite Permutation.Permutation_middle.
          eapply incl_appr', incl_appr', incl_cons; try solve_incl.
          eapply fresh_ident_In in H. unfold st_tys, idty, idty.
          rewrite in_map_iff. exists (x, (ty, cl)); split; auto.
          rewrite in_map_iff. eexists; split; [|eauto]; eauto.
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
      (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
      Forall (fun a => forall e' a2s st0 st0',
                  k a st0 = (e', a2s, st0') ->
                  st_follows st st0 ->
                  st_follows st0' st' ->
                  wt_exp G vars e') a ->
      Forall (wt_exp G vars) es'.
  Proof.
    intros G vars k a.
    induction a; intros es' a2s st st' Hmap Hfollows Hforall;
      repeat inv_bind.
    - constructor.
    - constructor.
      + rewrite Forall_forall in Hforall.
        eapply Hforall. 2,3:eauto.
        * constructor. reflexivity.
        * reflexivity.
        * eapply map_bind2_st_follows in H0; eauto.
          rewrite Forall_forall; intros; eauto.
      + eapply IHa; eauto.
        rewrite Forall_forall in *; intros.
        eapply Hforall. 2,4:eauto.
        * apply in_cons; auto.
        * etransitivity; eauto.
  Qed.

  Hint Constructors wt_exp.

  Lemma idty_without_names : forall vars,
      idty (without_names' vars) = idty vars.
  Proof.
    intros vars.
    unfold idty, without_names'.
    rewrite map_map.
    eapply map_ext; intros [id [ty [cl n]]]; reflexivity.
  Qed.

  Definition idck' (vars : list (ident * ann)) : list (ident * clock) :=
    idck (without_names' vars).

  Fact map_bind2_wt_exp {A A2 B} :
    forall G vars (k : A -> Fresh (list exp * A2) B) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
      Forall (fun a => forall es' a2s st0 st0',
                  k a st0 = (es', a2s, st0') ->
                  st_follows st st0 ->
                  st_follows st0' st' ->
                  Forall (wt_exp G vars) es') a ->
      Forall (wt_exp G vars) (concat es').
  Proof.
    intros G vars k a.
    induction a; intros es' a2s st st' Hmap Hfollows Hforall;
      repeat inv_bind.
    - constructor.
    - apply Forall_app. split; eauto.
      + rewrite Forall_forall in Hforall.
        eapply Hforall. 2:eauto.
        * constructor. reflexivity.
        * reflexivity.
        * eapply map_bind2_st_follows in H0; eauto.
          rewrite Forall_forall; intros; eauto.
      + eapply IHa; eauto.
        rewrite Forall_forall in *; intros.
        eapply Hforall. 2,4:eauto.
        * apply in_cons; auto.
        * etransitivity; eauto.
  Qed.

  Fact normalize_exp_wt_exp : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wt_exp G (vars++st_tys st')) es'.
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
      assert (length x = numstreams e) as Hlen by eauto.
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
      assert (length x = numstreams e1) as Hlen1 by eauto.
      assert (length x2 = numstreams e2) as Hlen2 by eauto.
      rewrite <- length_typeof_numstreams in Hlen1.
      rewrite <- length_typeof_numstreams in Hlen2.
      replace (typeof e1) in *.
      replace (typeof e2) in *.
      repeat singleton_length.
      eapply normalize_exp_typeof in Hwt1...
      eapply normalize_exp_typeof in Hwt2...
      inv IHHwt1. inv IHHwt2.
      econstructor; eauto;
        simpl in *; rewrite app_nil_r in *;
          try rewrite Hwt1; try rewrite Hwt2...
      + eapply normalize_exp_st_follows in H3. repeat solve_incl.
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
      assert (length (concat x1) = length (annots es)) as Hlength by eauto.
      assert (typesof (concat x1) = typesof es) as Htypeof by eauto.
      repeat rewrite_Forall_forall.
      rewrite in_map_iff in H4; destruct H4 as [[? ?] [? Hin]]; subst.
      constructor; simpl.
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
        repeat simpl_list.
        eapply concat_length_map_nth; solve_forall.
        * repeat solve_length.
        * rewrite length_typeof_numstreams...
      + apply in_or_app...
      + repeat solve_incl.
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + rewrite Forall_map.
        rewrite Forall_forall; intros [[et ef] ty] Hin.
        assert (length (concat x3) = length (annots ets)) by eauto.
        assert (length (concat x5) = length (annots efs)) by eauto.
        constructor; simpl.
        * eapply map_bind2_wt_exp with (G0:=G) (vars0 := (vars++(st_tys x2))) in H7...
          -- repeat constructor.
             repeat simpl_In.
             rewrite Forall_forall in H7. apply H7 in H11.
             repeat solve_incl.
          -- clear H1 H2.
             repeat rewrite_Forall_forall. apply H0 in H2...
             rewrite_Forall_forall. apply H2 in H12. repeat solve_incl.
        * eapply map_bind2_wt_exp with (G0:=G) (vars0 := (vars++(st_tys st'))) in H4...
          -- repeat constructor.
             repeat simpl_In.
             rewrite Forall_forall in H4. apply H4 in H10.
             repeat solve_incl.
          -- clear H H0.
             repeat rewrite_Forall_forall. eapply H2 in H0...
             rewrite_Forall_forall. apply H0 in H12. repeat solve_incl.
        * apply in_or_app...
        * rewrite app_nil_r.
          specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H7) as Hnumstreams.
          eapply map_bind2_normalize_exp_typesof in H7; [| rewrite Forall_forall in *; intros; auto].
          rewrite <- H7 in Hin. rewrite <- length_typesof_annots in *.
          repeat simpl_nth.
          repeat simpl_list.
          eapply concat_length_map_nth; solve_forall.
          -- repeat solve_length.
          -- rewrite length_typeof_numstreams...
        * rewrite app_nil_r.
          specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H4) as Hnumstreams.
          eapply map_bind2_normalize_exp_typesof in H4; [| rewrite Forall_forall in *; intros; auto].
          rewrite <- H5 in Hin. rewrite <- H4 in Hin. rewrite <- length_typesof_annots in *.
          repeat simpl_nth.
          repeat simpl_list.
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
      + rewrite Forall_map.
        rewrite Forall_forall; intros [[et ef] ty] Hin.
        assert (length (concat x5) = length (annots ets)) by eauto.
        assert (length (concat x7) = length (annots efs)) by eauto.
        constructor; simpl...
        * apply IHHwt in H7...
          apply hd_default_wt_exp. solve_forall.
          apply map_bind2_st_follows in H8; solve_forall.
          apply map_bind2_st_follows in H4; solve_forall.
          repeat solve_incl.
        * eapply map_bind2_wt_exp with (G0:=G) (vars0 := (vars++(st_tys x4))) in H8...
          -- repeat constructor.
             repeat simpl_In.
             rewrite Forall_forall in H8. apply H8 in H12.
             repeat solve_incl.
          -- clear H1 H2 IHHwt.
             repeat rewrite_Forall_forall. apply H0 in H2...
             rewrite_Forall_forall. eapply H2 in H13. repeat solve_incl.
        * eapply map_bind2_wt_exp with (G0:=G) (vars0 := (vars++(st_tys st'))) in H4...
          -- repeat constructor.
             repeat simpl_In.
             rewrite Forall_forall in H4. apply H4 in H11.
             repeat solve_incl.
          -- clear H H0 IHHwt.
             repeat rewrite_Forall_forall. apply H2 in H0...
             rewrite_Forall_forall. apply H0 in H13. repeat solve_incl.
        * assert (length x = numstreams e) as Hlength by eauto.
          rewrite <- length_typeof_numstreams in Hlength.
          rewrite H3 in Hlength; simpl in Hlength.
          eapply normalize_exp_typeof in H7...
          singleton_length. congruence.
        * rewrite app_nil_r.
          specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H8) as Hnumstreams.
          eapply map_bind2_normalize_exp_typesof in H8; [| rewrite Forall_forall in *; intros; auto].
          rewrite <- H8 in Hin. rewrite <- length_typesof_annots in *.
          repeat simpl_nth.
          repeat simpl_list.
          eapply concat_length_map_nth; solve_forall.
          -- repeat solve_length.
          -- rewrite length_typeof_numstreams...
        * rewrite app_nil_r.
          specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H4) as Hnumstreams.
          eapply map_bind2_normalize_exp_typesof in H4; [| rewrite Forall_forall in *; intros; auto].
          rewrite <- H5 in Hin. rewrite <- H4 in Hin. rewrite <- length_typesof_annots in *.
          repeat simpl_nth.
          repeat simpl_list.
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
      specialize (idents_for_anns'_incl_ty _ _ _ _ H6) as Hincl.
      eapply idents_for_anns'_wt_exp with (G:=G) (vars:=vars) in H6...
      + solve_forall. repeat solve_incl.
      + solve_forall. destruct a; simpl in *...
        solve_incl. unfold idty. rewrite map_app.
        eapply incl_appr'. rewrite Permutation.Permutation_app_comm.
        eapply incl_app; [eapply incl_appl|eapply incl_appr].
        * apply idents_for_anns'_anon_streams_incl in H6.
          eapply incl_map in H6. etransitivity. eapply H6.
          replace (map _ (without_names' x1)) with (map (fun xtc => (fst xtc, fst (snd xtc))) x1); auto.
          unfold without_names'; rewrite map_map; simpl.
          apply map_ext; intros [? [? [? ?]]]; auto.
        * eapply map_bind2_normalize_exp_fresh_incl in H5.
          unfold st_tys, idty in *. eapply incl_map; eauto.
    - (* app (reset) *)
      repeat inv_bind.
      specialize (idents_for_anns'_incl_ty _ _ _ _ H8) as Hincl.
      eapply idents_for_anns'_wt_exp with (G:=G) (vars:=vars) in H8...
      + solve_forall. repeat solve_incl.
      + solve_forall. destruct a; simpl in *...
        solve_incl. unfold idty. rewrite map_app.
        eapply incl_appr'. rewrite Permutation.Permutation_app_comm.
        eapply incl_app; [eapply incl_appl|eapply incl_appr].
        * apply idents_for_anns'_anon_streams_incl in H8.
          eapply incl_map in H8. etransitivity. eapply H8.
          replace (map _ (without_names' x5)) with (map (fun xtc => (fst xtc, fst (snd xtc))) x5); auto.
          unfold without_names'; rewrite map_map; simpl.
          apply map_ext; intros [? [? [? ?]]]; auto.
        * eapply map_bind2_normalize_exp_fresh_incl in H6.
          unfold st_tys, idty in *. eapply incl_map.
          assert (st_follows x1 x4) by repeat solve_st_follows.
          etransitivity... eapply incl_map...
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
      unfold fby_iteexp in H1.
      destruct (Norm.is_constant e0); repeat inv_bind.
      + repeat rewrite_Forall_forall.
        repeat constructor; simpl.
        * repeat simpl_In.
          apply Hwt1 in H8.
          repeat solve_incl.
        * repeat simpl_In.
          apply Hwt2 in H7.
          repeat solve_incl.
        * rewrite app_nil_r.
          repeat rewrite_Forall_forall.
          repeat simpl_nth; repeat simpl_length.
          specialize (H4 _ _ _ _ _ H0 H11 H10). simpl in H4.
          congruence.
        * rewrite app_nil_r. repeat simpl_nth; repeat simpl_length.
          specialize (H6 _ _ _ _ _ H0 H8 H10); simpl in H6.
          congruence.
        * repeat simpl_In.
          apply Hclock in H0. repeat solve_incl.
      + repeat rewrite_Forall_forall.
        repeat simpl_length.
        repeat constructor; simpl.
        * apply init_var_for_clock_In in H1.
          apply in_or_app; right.
          eapply fresh_ident_st_follows in H4. eapply st_follows_incl in H4.
          eapply st_follows_incl in H3.
          eapply H4 in H1. eapply H3 in H1; simpl in H1.
          unfold st_tys, idty. rewrite map_map; simpl.
          repeat simpl_In. exists (x, (Op.bool_type, (fst cl), true)); auto.
        * repeat simpl_In. apply Hclock in H0. inv H0. repeat solve_incl.
        * repeat simpl_In. apply Hwt1 in H10. repeat solve_incl.
        * apply fresh_ident_In in H4.
          apply st_follows_tys_incl in H3.
          apply in_or_app; right. apply H3.
          rewrite st_anns_tys_In. exists (fst cl). exists false. assumption.
        * repeat simpl_In. apply Hclock in H0. inv H0. repeat solve_incl.
        * rewrite app_nil_r.
          repeat simpl_nth. repeat simpl_length.
          specialize (H8 _ _ _ _ _ H0 H10 H12). simpl in H8.
          congruence.
        * repeat simpl_In. apply Hclock in H0. repeat solve_incl.
  Qed.

  Corollary normalize_fby_wt_exp' : forall G vars e0s es anns e0s' es' res eqs1 eqs2 eqs3 st st' st'' st''',
      wt_exp G vars (Efby e0s es anns) ->
      normalize_exps e0s st = (e0s', eqs1, st') ->
      normalize_exps es st' = (es', eqs2, st'') ->
      normalize_fby e0s' es' anns st'' = (res, eqs3, st''') ->
      Forall (wt_exp G (vars++st_tys st''')) res.
  Proof with eauto.
    intros G vars e0s es anns e0s' es' res eqs1 eqs2 eqs3 st st' st'' st''' Hwc Hnorm1 Hnorm2 Hnorm3.
    inv Hwc. eapply normalize_fby_wt_exp. 6:eauto.
    - eapply normalize_exps_wt_exp with (G:=G) (vars:=vars) in Hnorm1...
      1,2:solve_forall; repeat solve_incl.
    - eapply normalize_exps_wt_exp with (G:=G) (vars:=vars) in Hnorm2...
    - clear Hnorm3 Hnorm2 H3 H4.
      assert (length e0s' = length (annots e0s)) by eauto.
      specialize (normalize_exps_numstreams _ _ _ _ _ Hnorm1) as Hnumstreams.
      unfold normalize_exps in Hnorm1; repeat inv_bind.
      eapply map_bind2_normalize_exp_typesof' in H0...
      assert (Forall2 eq (map typesof x) (map typeof e0s)).
      { specialize (Forall2_map_1 (fun tys e => tys = typeof e) typesof x e0s) as [_ Hfm].
        specialize (Forall2_map_2 (fun tys tys' => tys = tys') typeof (map typesof x) e0s) as [_ Hfm2].
        auto. } rewrite Forall2_eq in H1.
      repeat rewrite_Forall_forall.
      + rewrite <- length_typesof_annots, typesof_annots in *. solve_length.
      + setoid_rewrite (concat_length_map_nth _ _ _ _ _)...
        * repeat simpl_list.
          replace (concat (map typeof (concat x))) with (concat (map typeof e0s)).
          2: { rewrite <- H1. rewrite typeof_concat_typesof... } clear H1.
          rewrite H5, map_nth...
        * solve_forall. rewrite length_typeof_numstreams...
    - clear Hnorm1 Hnorm3 H2 H5 H6.
      assert (length es' = length (annots es)) by eauto.
      specialize (normalize_exps_numstreams _ _ _ _ _ Hnorm2) as Hnumstreams.
      unfold normalize_exps in Hnorm2; repeat inv_bind.
      eapply map_bind2_normalize_exp_typesof' in H0...
      assert (Forall2 (fun tys tys' => tys = tys') (map typesof x) (map typeof es)).
      { specialize (Forall2_map_1 (fun tys e => tys = typeof e) typesof x es) as [_ Hfm].
        specialize (Forall2_map_2 (fun tys tys' => tys = tys') typeof (map typesof x) es) as [_ Hfm2].
        auto. } rewrite Forall2_eq in H1.
      repeat rewrite_Forall_forall.
      -- rewrite <- length_typesof_annots in *. solve_length.
      -- setoid_rewrite (concat_length_map_nth _ _ _ _ _)...
         ++ repeat simpl_list.
            replace (concat (map typeof (concat x))) with (concat (map typeof es)).
            2: { rewrite <- H1. rewrite typeof_concat_typesof... } clear H1.
            rewrite H4, map_nth...
         ++ solve_forall. rewrite length_typeof_numstreams...
    - rewrite Forall_map in H6.
      eapply Forall_impl; [| eauto]. intros [? ?] ?...
  Qed.

  Fact normalize_reset_typeof_bool : forall e e' eqs' st st',
      typeof e = [Op.bool_type] ->
      normalize_reset e st = (e', eqs', st') ->
      typeof e' = [Op.bool_type].
  Proof with eauto.
    intros e e' eqs' st st' Htyp Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind; simpl in *...
    destruct (hd _) as [? [? ?]] eqn:Hann; repeat inv_bind.
    rewrite typeof_annot in Htyp.
    destruct (annot e); simpl in *; try congruence.
    inv Hann.
    destruct l; simpl in *; try congruence.
  Qed.

  Fact normalize_reset_wt_exp : forall G vars e e' eqs' st st',
      incl (fresh_in e) (idty (st_anns st')) ->
      wt_exp G (vars++(st_tys st)) e ->
      normalize_reset e st = (e', eqs', st') ->
      wt_exp G (vars++(st_tys st')) e'.
  Proof.
    intros G vars e e' eqs' st st' Hincl Hwt Hnorm.
    assert (st_follows st st') as Hfollows by eauto.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind.
    - assumption.
    - destruct (hd _) as [? [? ?]] eqn:Hann; repeat inv_bind.
      constructor.
      + apply fresh_ident_In in H.
        apply in_or_app; right.
        rewrite st_anns_tys_In. exists c. exists false. assumption.
      + constructor. destruct (annot e) eqn:Hann'; simpl in Hann.
        * inv Hann. constructor.
        * subst. eapply wt_exp_clockof in Hwt.
          rewrite Forall_forall in Hwt.
          eapply wt_clock_incl; [| eapply Hwt].
          -- rewrite <- app_assoc.
             eapply incl_appr'. eapply incl_app.
             ++ eapply st_follows_tys_incl; auto.
             ++ apply incl_map; auto.
          -- rewrite clockof_annot. rewrite Hann'; simpl. left; auto.
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
        eapply normalize_fby_wt_exp' in H1. 1,3,4:eauto. eauto.
      + eapply normalize_exp_wt_exp in Hnorm; eauto.
    - (* app *)
      inv Hwt; repeat inv_bind; repeat econstructor; eauto.
      1,4: eapply normalize_exps_wt_exp in H...
      1,3,5:solve_forall. repeat solve_incl.
      1,2:replace (fresh_ins x) with (@nil (ident * (Op.type * clock))); simpl. 2,4:(eapply normalize_exps_no_fresh in H; eauto).
      3,4: (eapply normalize_exps_typesof in H; eauto; congruence).
      + unfold idty in *. rewrite <- app_assoc, map_app in *.
        solve_incl. eapply incl_appr', incl_appl'.
        apply normalize_exps_fresh_incl in H.
        unfold st_tys, idty. eapply incl_map...
      + unfold idty in *. rewrite <- app_assoc, map_app in *.
        solve_incl. eapply incl_appr', incl_appl'.
        apply normalize_exps_fresh_incl in H.
        assert (st_follows x1 st') by repeat solve_st_follows.
        unfold st_tys, idty. eapply incl_map.
        etransitivity... eapply incl_map...
      + specialize (normalize_exp_no_fresh _ _ _ _ _ _ H0) as Hincl.
        eapply normalize_exp_wt_exp in H0...
        eapply hd_default_wt_exp in H0.
        eapply normalize_reset_wt_exp in H1...
        destruct x4; simpl; try apply incl_nil'.
        apply fresh_ins_nil in Hincl; rewrite Hincl; apply incl_nil'.
      + specialize (normalize_exp_numstreams _ _ _ _ _ _ H0) as Hlength.
        eapply normalize_exp_typeof in H0...
        eapply normalize_reset_typeof_bool in H1...
        rewrite H9 in H0.
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
      (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
      Forall (fun a => forall a1 eqs' st0 st0',
                  k a st0 = (a1, eqs', st0') ->
                  st_follows st st0 ->
                  st_follows st0' st' ->
                  Forall (wt_equation G vars) eqs') a ->
      Forall (wt_equation G vars) (concat eqs').
  Proof.
   intros G vars k a.
    induction a; intros es' a2s st st' Hmap Hfollows Hforall;
      repeat inv_bind.
    - constructor.
    - apply Forall_app. split; eauto.
      + rewrite Forall_forall in Hforall.
        eapply Hforall. 2:eauto.
        * constructor. reflexivity.
        * reflexivity.
        * eapply map_bind2_st_follows in H0; eauto.
          rewrite Forall_forall; intros; eauto.
      + eapply IHa; eauto.
        rewrite Forall_forall in *; intros.
        eapply Hforall. 2,4:eauto.
        * apply in_cons; auto.
        * etransitivity; eauto.
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
      unfold fby_iteexp in H5.
      destruct (Norm.is_constant e0); repeat inv_bind; inv H8.
      + repeat constructor; simpl.
        * repeat simpl_In.
          eapply add_whens_wt_exp...
          -- simpl. f_equal... apply Op.type_init_type.
          -- eapply Hclock in H4. destruct cl; simpl. inv H4.
             solve_incl.
        * repeat simpl_In.
          apply Hwt2 in H8. repeat solve_incl.
        * rewrite app_nil_r.
          repeat simpl_nth. repeat simpl_length.
          specialize (H1 _ _ _ _ _ H4 H13 H12); simpl in H1. congruence.
        * rewrite app_nil_r.
          apply add_whens_typeof; simpl.
          f_equal. apply Op.type_init_type.
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
        * simpl_In. apply Hclock in H4. inv H4. repeat solve_incl.
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
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind; auto.
    destruct (hd _) as [? [? ?]] eqn:Hann; repeat inv_bind.
    repeat constructor; simpl.
    - repeat solve_incl.
    - rewrite app_nil_r. rewrite Hty.
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

  Fact idents_for_anns'_wt_nclock : forall vars anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      Forall (fun '(ty, cl) => wt_nclock (vars++idty (anon_streams anns)++st_tys st) cl) anns ->
      Forall (wt_nclock (vars++idty (anon_streams (map snd ids))++st_tys st')) (map snd (map snd ids)).
  Proof with eauto.
    induction anns; intros ids st st' Hidents Hf;
      repeat inv_bind; simpl; auto.
    inv Hf. destruct a as [ty [cl ?]].
    destruct o; repeat inv_bind; econstructor.
    - repeat constructor; simpl.
      inv H1. destruct x; simpl in *. solve_incl.
      eapply incl_appr', incl_tl', incl_app.
      + apply incl_appl.
        eapply idents_for_anns'_anon_streams, incl_map in H0...
      + apply incl_appr. solve_incl.
    - eapply IHanns in H0.
      + solve_forall. repeat solve_incl.
      + solve_forall. destruct a, x. solve_incl.
        rewrite Permutation.Permutation_middle.
        eapply incl_appr', incl_appr', incl_cons; try solve_incl.
        eapply reuse_ident_In in H. unfold st_tys, idty, idty.
        rewrite in_map_iff. exists (i, (ty, cl)); split; auto.
        rewrite in_map_iff. eexists; split; [|eauto]; eauto.
    - repeat constructor; simpl.
      inv H1. solve_incl.
      eapply incl_appr', incl_app.
      + apply incl_appl.
        eapply idents_for_anns'_anon_streams, incl_map in H0...
      + apply incl_appr. solve_incl.
    - eapply IHanns in H0.
      + solve_forall.
      + solve_forall. destruct a. solve_incl.
        eapply incl_appr', incl_appr'. solve_incl.
  Qed.

  Import Permutation.
  Fact normalize_exp_wt_eq : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwt Hnorm;
      repeat inv_bind.
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
          eapply normalize_fby_wt_exp' with (G:=G) (vars:=vars) in H3.
          3,4: (unfold normalize_exps; inv_bind; repeat eexists; [| inv_bind; eauto]; eauto).
          2:eauto.
          rewrite Forall_forall in H3. apply H3 in H5. repeat solve_incl.
        * clear H H0 H12.
          specialize (normalize_fby_numstreams _ _ _ _ _ _ _ H3) as Hnumstreams. rewrite Forall_forall in Hnumstreams.
          simpl. rewrite app_nil_r.
          assert (numstreams e = 1).
          { apply Hnumstreams. simpl_length. simpl_length. repeat simpl_In... }
          rewrite <- length_typeof_numstreams in H. singleton_length.
          repeat constructor.
          apply in_or_app. right. eapply (idents_for_anns_incl_ty _ _ _ _ H4).
          specialize (normalize_fby_numstreams _ _ _ _ _ _ _ H3) as Hnum.
          assert (length (concat x2) = length (annots e0s)) by eauto.
          assert (length (concat x9) = length (annots es)) by eauto.
          rewrite <- length_typesof_annots in *.
          assert (length x5 = length a) by (eapply normalize_fby_length in H3; solve_length).
          assert (length x8 = length a) by eauto. simpl_length.
          apply normalize_fby_typeof in H3; solve_length.
          repeat simpl_nth.
          unfold idty. repeat simpl_In.
          exists (x, a0); simpl... split.
          -- f_equal.
             apply idents_for_anns_values in H4; symmetry in H4. rewrite <- Forall2_eq in H4.
             rewrite Forall2_forall2 in H4; destruct H4 as [_ H4].
             repeat simpl_length.
             specialize (H4 a0 a0 _ _ _ H5 eq_refl eq_refl).
             destruct nth as [? [? ?]] eqn:Hnth in H4. destruct nth as [? [? ?]] eqn:Hnth' in H4. inv H4.
             rewrite <- H15 in Hsingl.
             rewrite concat_length_map_nth with (db:=Op.bool_type) in Hsingl; solve_length.
             2: (solve_forall; rewrite length_typeof_numstreams; eauto).
             inv Hsingl.
             rewrite <- typesof_annots in H3. repeat simpl_list.
             rewrite H3. erewrite map_nth'; solve_length. setoid_rewrite Hnth; simpl.
             rewrite split_nth in H14; inv H14. rewrite split_map_snd.
             setoid_rewrite Hnth'. reflexivity.
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
          repeat simpl_list.
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
          repeat simpl_list.
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
      eapply H in H2. 2,3: eauto.
      solve_forall.
      eapply wt_equation_incl; [| eauto]. repeat solve_incl.
    - (* merge *)
      inv Hwt.
      destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split.
      1,4: eapply map_bind2_wt_eq in H1... 3,5: eapply map_bind2_wt_eq in H2...
      1,2,3,4:repeat rewrite_Forall_forall.
      Local Ltac mergeiteeqs Hin1 Hin2 Hind Hnorm :=
        eapply Hind in Hnorm; eauto;
        rewrite Forall_forall in Hnorm; eapply Hnorm in Hin2;
        repeat solve_incl.
      + mergeiteeqs H3 H12 H H4.
      + mergeiteeqs H4 H13 H H8.
      + mergeiteeqs H3 H12 H0 H4.
      + mergeiteeqs H4 H13 H0 H8.
      + solve_forall.
        destruct x0 as [xs es].
        assert (length (concat x3) = length (annots ets)) as Hlen1 by eauto.
        assert (length (concat x7) = length (annots efs)) as Hlen2 by eauto.
        specialize (idents_for_anns_length _ _ _ _ H3) as Hlen3.
        repeat constructor. rewrite <- length_typesof_annots in *.
        -- specialize (idents_for_anns_st_follows _ _ _ _ H3) as Hfollows.
           apply idents_for_anns_values in H3; symmetry in H3. rewrite <- Forall2_eq in H3.
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
              repeat simpl_list...
              solve_length.
              solve_forall. rewrite length_typeof_numstreams...
           ++ rewrite app_nil_r.
              specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H2) as Hnumstreams.
              eapply map_bind2_normalize_exp_typesof in H2; [| rewrite Forall_forall in *; intros; auto].
              rewrite <- H15. rewrite <- H17. repeat rewrite <- typesof_annots in *. replace (typesof efs) in *. rewrite <- H2.
              erewrite concat_length_map_nth.
              repeat simpl_list...
              solve_length.
              solve_forall. rewrite length_typeof_numstreams...
           ++ repeat solve_incl.
              Unshelve. 1,3,4: exact (hd_default []). exact Op.bool_type. exact (x, default_ann).
        -- rewrite <- length_typesof_annots in *.
           repeat simpl_nth. repeat simpl_length.
           Unshelve. 2,5: exact (hd_default []). 3,4:exact (xH, default_ann). 2,3:exact (hd_default [], hd_default [], Op.bool_type).
           destruct (nth x0 x6 _) eqn:Hnth1.
           destruct (nth x0 (combine _ _) _) as [[? ?] ?] eqn:Hnth2.
           simpl. repeat constructor; subst.
           repeat simpl_nth. Unshelve. 2:exact default_ann.
           apply in_or_app. right. apply (idents_for_anns_incl_ty _ _ _ _ H3).
           apply idents_for_anns_values in H3; symmetry in H3; rewrite <- Forall2_eq in H3.
           rewrite Forall2_map_1, Forall2_map_1, Forall2_map_2 in H3.
           rewrite Forall2_forall2 in H3; destruct H3 as [_ H3].
           specialize (H3 default_ann (xH, default_ann) _ _ _ H4 eq_refl eq_refl).
           rewrite Hnth1 in H3; simpl in H3.
           destruct a as [? [? ?]]. inversion H3; rewrite H14.
           unfold idty. repeat simpl_In.
           exists (i, (t, (c, o))); subst; split; simpl; auto.
           setoid_rewrite <- Hnth1.
           eapply nth_In; solve_length.
    - (* ite *)
      inv Hwt.
      destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split.
      1,5: eapply IHe in H1; eauto; solve_forall; repeat solve_incl.
      1,4: eapply map_bind2_wt_eq in H2... 3,5: eapply map_bind2_wt_eq in H3...
      1,2,3,4:repeat rewrite_Forall_forall.
      + mergeiteeqs H4 H14 H H9.
      + mergeiteeqs H9 H15 H H12.
      + mergeiteeqs H4 H14 H0 H9.
      + mergeiteeqs H9 H15 H0 H12.
      + solve_forall.
        destruct x2 as [xs es].
        assert (length (concat x5) = length (annots ets)) as Hlen1 by eauto.
        assert (length (concat x9) = length (annots efs)) as Hlen2 by eauto.
        specialize (idents_for_anns_length _ _ _ _ H4) as Hlen3.
        repeat constructor. rewrite <- length_typesof_annots in *.
        -- specialize (idents_for_anns_st_follows _ _ _ _ H4) as Hfollows.
           apply idents_for_anns_values in H4; symmetry in H4; rewrite <- Forall2_eq in H4.
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
           ++ assert (length x = numstreams e) as Hlength by eauto.
              specialize (normalize_exp_numstreams _ _ _ _ _ _ H1) as Hnumstreams.
              rewrite <- length_typeof_numstreams in Hlength. rewrite H8 in Hlength; simpl in Hlength.
              eapply normalize_exp_typeof in H1...
              singleton_length. congruence.
           ++ rewrite app_nil_r.
              specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H2) as Hnumstreams.
              eapply map_bind2_normalize_exp_typesof in H2; [| rewrite Forall_forall in *; intros; auto].
              rewrite <- H16. rewrite <- H17. rewrite <- typesof_annots. rewrite <- H2.
              erewrite concat_length_map_nth.
              repeat simpl_list...
              solve_length.
              solve_forall. rewrite length_typeof_numstreams...
           ++ rewrite app_nil_r.
              specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H3) as Hnumstreams.
              eapply map_bind2_normalize_exp_typesof in H3; [| rewrite Forall_forall in *; intros; auto].
              rewrite <- H16. rewrite <- H18. repeat rewrite <- typesof_annots in *; replace (typesof efs) in *. rewrite <- H3.
              erewrite concat_length_map_nth.
              repeat simpl_list...
              solve_length.
              solve_forall. rewrite length_typeof_numstreams...
           ++ repeat solve_incl.
              Unshelve. 1,3,4: exact (hd_default []). exact Op.bool_type. exact (xH, default_ann).
        -- rewrite <- length_typesof_annots in *.
           repeat simpl_nth. repeat simpl_length.
           Unshelve. 2,5: exact (hd_default []). 3,4:exact (xH, default_ann). 2,3:exact (hd_default [], hd_default [], Op.bool_type).
           destruct (nth x2 x8 _) eqn:Hnth1.
           destruct (nth x2 (combine _ _) _) as [[? ?] ?] eqn:Hnth2.
           simpl. repeat constructor; subst.
           repeat simpl_nth. Unshelve. 2:exact default_ann.
           apply in_or_app. right. apply (idents_for_anns_incl_ty _ _ _ _ H4).
           apply idents_for_anns_values in H4; symmetry in H4; rewrite <- Forall2_eq in H4.
           rewrite Forall2_map_1, Forall2_map_1, Forall2_map_2 in H4.
           rewrite Forall2_forall2 in H4; destruct H4 as [_ H4].
           specialize (H4 default_ann (xH, default_ann) _ _ _ H9 eq_refl eq_refl).
           destruct nck. destruct a as [? [? ?]].
           rewrite Hnth1 in H4; simpl in H4. inversion H4; rewrite H15.
           unfold idty. repeat simpl_In.
           exists (i, (t, (c0, o0))); subst; split...
           setoid_rewrite <- Hnth1. eapply nth_In; solve_length.
    - (* app *)
      inv Hwt; repeat inv_bind; repeat econstructor; simpl; eauto.
      1,7: (eapply map_bind2_wt_exp with (vars0:=(vars++(st_tys st'))) in H1; eauto;
            solve_forall;
            try eapply normalize_exp_wt_exp in H4; try eapply normalize_exp_wt_exp in H6; eauto;
            solve_forall; repeat solve_incl).
      1,6: (eapply map_bind2_normalize_exp_typesof in H1; eauto; congruence).
      3,4,9: rewrite app_nil_r.
      + clear H0 H8 H10 H12.
        eapply idents_for_anns'_values in H3; subst. assumption.
      + eapply idents_for_anns'_wt_nclock with (vars:=vars) in H3.
        * rewrite Forall_map in H3. solve_forall.
          solve_incl.
          rewrite <- app_assoc. apply incl_appr'.
          rewrite Permutation_app_comm. apply incl_appr'.
          unfold idty. rewrite map_app. apply incl_appr, incl_refl.
        * solve_forall. destruct a0; simpl in *.
          solve_incl. apply incl_appr'.
          unfold idty. rewrite map_app, Permutation_app_comm. apply incl_appr'.
          apply map_bind2_normalize_exp_fresh_incl in H1. eapply incl_map in H1; eauto.
      + rewrite Forall2_map_1, Forall2_map_2, Forall2_map_2.
        eapply Forall2_same.
        eapply idents_for_anns'_incl_ty in H3.
        eapply Forall_forall; intros [id [ty [cl name]]] Hin; simpl.
        apply in_or_app; right. apply H3.
        unfold idty. rewrite in_map_iff. eexists; split; eauto...
      + eapply map_bind2_wt_eq in H1...
        rewrite Forall_forall in *; intros.
        eapply H0 in H4...
        solve_forall. repeat solve_incl.
      + rewrite Forall2_map_1, Forall2_map_2, Forall2_map_2.
        eapply Forall2_same.
        eapply idents_for_anns'_incl_ty in H3.
        eapply Forall_forall; intros [id [ty [cl name]]] Hin; simpl.
        apply in_or_app; right. apply H3.
        unfold idty. rewrite in_map_iff. eexists; split; eauto...
      + clear H0 H8 H10 H12.
        eapply idents_for_anns'_values in H3; subst. assumption.
      + eapply idents_for_anns'_wt_nclock with (vars:=vars) in H3.
        * rewrite Forall_map in H3. solve_forall.
          solve_incl.
          rewrite <- app_assoc. apply incl_appr'.
          rewrite Permutation_app_comm. apply incl_appr'.
          unfold idty. rewrite map_app. apply incl_appr, incl_refl.
        * solve_forall. destruct a0; simpl in *.
          solve_incl. apply incl_appr'.
          unfold idty. rewrite map_app, Permutation_app_comm. apply incl_appr'.
          apply map_bind2_normalize_exp_fresh_incl in H1.
          assert (st_follows x1 x8) by eauto. apply st_follows_incl in H6. eapply incl_map in H6.
          assert (st_follows x8 x4) by eauto. apply st_follows_incl in H7. eapply incl_map in H7.
          assert (incl (fresh_ins es) (idty (st_anns x4))) by (repeat (etransitivity; eauto)).
          eapply incl_map...
      + specialize (normalize_exp_no_fresh _ _ _ _ _ _ H2) as Hnofresh.
        eapply normalize_exp_wt_exp in H2...
        eapply hd_default_wt_exp in H2...
        eapply normalize_reset_wt_exp in H4...
        2:{ destruct x; simpl. apply incl_nil'.
            apply fresh_ins_nil in Hnofresh; rewrite Hnofresh; apply incl_nil'. }
        eapply map_bind2_st_follows in H1; solve_forall.
        repeat solve_incl.
      + specialize (normalize_exp_numstreams _ _ _ _ _ _ H2) as Hlength.
        eapply normalize_exp_typeof in H2...
        eapply normalize_reset_typeof_bool in H4...
        rewrite H14 in H2.
        destruct x; simpl in *; try congruence.
        inv Hlength. rewrite <- length_typeof_numstreams in H7.
        destruct (typeof e); simpl in *; try congruence.
        destruct l; simpl in *; try congruence.
      + repeat rewrite Forall_app. repeat split.
        * eapply map_bind2_wt_eq in H1; eauto.
          rewrite Forall_forall in *; intros.
          eapply H0 in H6...
          solve_forall. repeat solve_incl.
        * eapply H in H2...
          apply normalize_reset_st_follows in H4.
          apply idents_for_anns'_st_follows in H3.
          solve_forall. repeat solve_incl.
        * assert (length x = numstreams r) as Hlength by eauto.
          specialize (normalize_exp_typeof _ _ _ _ _ _ _ _ H13 H2) as Htypeof.
          rewrite H14 in Htypeof.
          eapply normalize_exp_wt_exp in H2... eapply hd_default_wt_exp in H2...
          eapply normalize_reset_wt_eq in H4...
          -- solve_forall. repeat solve_incl.
          -- rewrite <- length_typeof_numstreams in Hlength. rewrite H14 in Hlength; simpl in Hlength.
             singleton_length...
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
      + inv Hwt; repeat inv_bind; eapply normalize_exps_wt_eq in H...
        solve_forall. repeat solve_incl.
      + inv Hwt; repeat inv_bind; try constructor.
        apply Forall_app. split.
        * eapply normalize_exp_wt_eq in H0...
          solve_forall. repeat solve_incl.
        * eapply normalize_reset_wt_eq with (G:=G) (vars:=vars) in H1...
          -- eapply hd_default_wt_exp.
             eapply normalize_exp_wt_exp in H0...
          -- specialize (normalize_exp_numstreams _ _ _ _ _ _ H0) as Hnumstreams.
             eapply normalize_exp_typeof in H0...
             rewrite H11 in H0.
             destruct x4; simpl in *; try congruence.
             inv Hnumstreams. rewrite <- length_typeof_numstreams in H4. singleton_length.
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
          rewrite app_nth1 in H1. 2: rewrite length_typeof_numstreams.
          rewrite nth_firstn_1. 2,3:eauto.
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
      repeat inv_bind.
    - constructor.
    - inv Hwt. apply Forall_app. split...
      eapply normalize_equation_wt_eq in H...
      solve_forall. repeat solve_incl.
  Qed.

  (** ** Preservation of wt_clock *)

  Definition st_clocks (st : fresh_st ((Op.type * clock) * bool)) : list clock :=
    map (fun '(_, (_, cl, _)) => cl) (st_anns st).

  Fact fresh_ident_wt_clock : forall vars ty cl b id st st',
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

  Corollary idents_for_anns_wt_clock : forall vars anns ids st st',
      Forall (wt_clock vars) (st_clocks st) ->
      Forall (wt_nclock vars) (map snd anns) ->
      idents_for_anns anns st = (ids, st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof.
    induction anns; intros ids st st' Hclocks Hwt Hidents;
      repeat inv_bind.
    - assumption.
    - inv Hwt. destruct a as [ty [cl ?]]. repeat inv_bind.
      eapply IHanns in H0; eauto.
      inv H1.
      eapply fresh_ident_wt_clock; eauto.
  Qed.

  Fact reuse_ident_wt_clock : forall vars ty cl b id st st',
      Forall (wt_clock vars) (st_clocks st) ->
      wt_clock vars cl ->
      reuse_ident id (ty, cl, b) st = (tt, st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof.
    intros vars ty cl b id st st' Hclocks Hwt Hfresh.
    apply reuse_ident_anns in Hfresh.
    unfold st_clocks in *. setoid_rewrite Hfresh; simpl.
    constructor; auto.
  Qed.

  Corollary idents_for_anns'_wt_clock : forall vars anns ids st st',
      Forall (wt_clock vars) (st_clocks st) ->
      Forall (wt_nclock vars) (map snd anns) ->
      idents_for_anns' anns st = (ids, st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof.
    induction anns; intros ids st st' Hclocks Hwt Hidents;
      repeat inv_bind.
    - assumption.
    - inv Hwt. destruct a as [ty [cl ?]]. destruct o; repeat inv_bind.
      + eapply IHanns in H0; eauto.
        inv H1.
        destruct x. eapply reuse_ident_wt_clock; eauto.
      + eapply IHanns in H0; eauto.
        inv H1.
        eapply fresh_ident_wt_clock; eauto.
  Qed.

  Fact map_bind2_wt_clock {A A1 A2 : Type} :
    forall vars (k : A -> FreshAnn (A1 * A2)) a a1s a2s st st',
      Forall (wt_clock (vars++st_tys st)) (st_clocks st) ->
      map_bind2 k a st = (a1s, a2s, st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
      Forall (fun a => forall a1s a2s st0 st0',
                  Forall (wt_clock (vars++st_tys st0)) (st_clocks st0) ->
                  k a st0 = (a1s, a2s, st0') ->
                  st_follows st st0 ->
                  st_follows st0' st' ->
                  Forall (wt_clock (vars++st_tys st0')) (st_clocks st0')) a ->
      Forall (wt_clock (vars++st_tys st')) (st_clocks st').
  Proof with eauto.
    induction a; intros a1s a2s st st' Hclocks Hmap Hfollows Hf;
      repeat inv_bind...
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

  Fact normalize_fby_wt_clock : forall vars e0s es anns es' eqs' st st',
      Forall (wt_clock (vars++st_tys st)) (st_clocks st) ->
      Forall (wt_nclock vars) (map snd anns) ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall (wt_clock (vars++st_tys st')) (st_clocks st').
  Proof with eauto.
    intros vars e0s es anns es' eqs' st st' Hclocks Hwt Hnorm.
    unfold normalize_fby in Hnorm. repeat inv_bind.
    eapply map_bind2_wt_clock in H...
    1: intros ? ? [[? ?] ?] ? ? Hfby; eapply fby_iteexp_st_follows...
    solve_forall. destruct x as [[e0 e] [ty cl]].
    unfold fby_iteexp in H2.
    destruct (Norm.is_constant e0); repeat inv_bind.
    - assumption.
    - repeat simpl_In.
      unfold init_var_for_clock in H2.
      assert (wt_nclock vars cl) as Hcl.
      { rewrite Forall_forall in Hwt. eapply Hwt.
        repeat simpl_In. exists (ty, cl)... }
      destruct (find _ _).
      + destruct p. inv H2.
        inv Hcl.
        eapply fresh_ident_wt_clock in H5...
        * solve_forall. repeat solve_incl.
        * simpl. repeat solve_incl.
      + destruct (fresh_ident _ _) eqn:Hfresh. inv H2.
        inv Hcl.
        assert (st_follows st0 st0') by repeat solve_st_follows.
        eapply fresh_ident_wt_clock in Hfresh...
        eapply fresh_ident_wt_clock in H5...
        2,3:simpl; repeat solve_incl.
        solve_forall. repeat solve_incl.
  Qed.

  Fact normalize_reset_wt_clock : forall vars e e' eqs' st st',
      Forall (wt_clock vars) (clockof e) ->
      Forall (wt_clock vars) (st_clocks st) ->
      normalize_reset e st = (e', eqs', st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof with eauto.
  intros vars e e' eqs' st st' Hwt Hclocks Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind...
    destruct (hd _) as [? [? ?]] eqn:Hhd.
    repeat inv_bind.
    eapply fresh_ident_wt_clock in H...
    rewrite clockof_annot in Hwt.
    destruct (annot e); simpl in *; inv Hhd.
    - constructor.
    - simpl in Hwt. inv Hwt...
  Qed.

  Fact normalize_exp_wt_clock : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      Forall (wt_clock (vars++st_tys st)) (st_clocks st) ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wt_clock (vars++st_tys st')) (st_clocks st').
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwt Hclocks Hnorm;
      inv Hwt; repeat inv_bind; eauto.
    - (* fby *)
      eapply map_bind2_wt_clock in H1...
      2: rewrite Forall_forall in *; intros...
      eapply map_bind2_wt_clock in H2...
      2: rewrite Forall_forall in *; intros...
      eapply normalize_fby_wt_clock in H3...
      eapply idents_for_anns_wt_clock in H9...
      1,2: solve_forall; repeat solve_incl.
    - (* when *)
      eapply map_bind2_wt_clock in H0...
      rewrite Forall_forall in *; intros...
    - (* merge *)
      destruct is_control; repeat inv_bind.
      1,2: (eapply map_bind2_wt_clock in H1; eauto; [|rewrite Forall_forall in *; intros; eauto];
            eapply map_bind2_wt_clock in H2; eauto; try (solve [rewrite Forall_forall in *; intros; eauto])).
      eapply idents_for_anns_wt_clock in H3...
      1:solve_forall; repeat solve_incl.
      rewrite map_map; simpl.
      solve_forall. simpl_In. solve_incl.
    - (* ite *)
      destruct is_control; repeat inv_bind.
      1,2: (eapply IHe in H1; eauto;
            eapply map_bind2_wt_clock in H2; eauto; [|rewrite Forall_forall in *; intros; eauto];
            eapply map_bind2_wt_clock in H3; eauto; try (solve [rewrite Forall_forall in *; intros; eauto])).
      eapply idents_for_anns_wt_clock in H4...
      1: solve_forall; repeat solve_incl.
      rewrite map_map; simpl.
      solve_forall. simpl_In. solve_incl.
    - (* app *)
      assert (incl (fresh_ins es) (idty (st_anns x4))) as Hincl by (apply map_bind2_normalize_exp_fresh_incl in H1; auto).
      eapply map_bind2_wt_clock in H1...
      2: rewrite Forall_forall in *; intros...
      eapply idents_for_anns'_wt_clock in H2...
      1: solve_forall; repeat solve_incl.
      rewrite Forall_map. solve_forall. solve_incl.
      apply incl_appr'. unfold idty; rewrite map_app; apply incl_app; apply incl_map.
      + etransitivity... apply incl_map. solve_incl.
      + apply idents_for_anns'_fresh_incl in H2...
    - (* app (reset) *)
      assert (st_follows x8 st') by repeat solve_st_follows.
      assert (st_follows x1 st') by repeat solve_st_follows.
      assert (incl (fresh_in r) (idty (st_anns x8))) as Hincl1 by (apply normalize_exp_fresh_incl in H2; auto).
      assert (incl (fresh_ins es) (idty (st_anns x1))) as Hincl2 by (apply map_bind2_normalize_exp_fresh_incl in H1; auto).
      assert (length x6 = numstreams r) as Hlength by eauto.
      assert (clocksof x6 = clockof r) as Hannot by eauto.
      eapply map_bind2_wt_clock in H1...
      2: { rewrite Forall_forall in *; intros. repeat simpl_In... }
      eapply H in H2...
      eapply normalize_reset_wt_clock in H4...
      2: { apply wt_exp_clockof in H10. rewrite <- Hannot in H10.
           rewrite <- length_typeof_numstreams, H11 in Hlength; simpl in Hlength.
           singleton_length.
           solve_forall. solve_incl.
           apply incl_appr', incl_map... }
      eapply idents_for_anns'_wt_clock in H3...
      1: solve_forall; repeat solve_incl.
      rewrite Forall_map. solve_forall. solve_incl.
      apply incl_appr'. unfold idty; rewrite map_app; apply incl_app; apply incl_map.
      + etransitivity... apply incl_map. solve_incl.
      + apply idents_for_anns'_fresh_incl in H3...
  Qed.

  Corollary normalize_exps_wt_clock : forall G vars es es' eqs' st st',
      Forall (wt_exp G (vars++st_tys st)) es ->
      Forall (wt_clock (vars++st_tys st)) (st_clocks st) ->
      normalize_exps es st = (es', eqs', st') ->
      Forall (wt_clock (vars++st_tys st')) (st_clocks st').
  Proof.
    intros G vars es es' eqs' st st' Hwt Hclocks Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_wt_clock in H; eauto.
    solve_forall.
    assert (st_follows st0 st0') by eauto.
    eapply normalize_exp_wt_clock in H2; [|eauto|].
    - solve_forall. solve_incl.
      rewrite <- app_assoc. apply incl_appr', incl_app; auto.
      repeat solve_incl.
    - solve_forall. solve_incl.
  Qed.

  Corollary normalize_rhs_wt_clock : forall G vars e keep_fby es' eqs' st st',
      wt_exp G vars e ->
      Forall (wt_clock (vars++st_tys st)) (st_clocks st) ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      Forall (wt_clock (vars++st_tys st')) (st_clocks st').
  Proof with eauto.
    intros G vars e keep_fby es' eqs' st st' Hwt Hclocks Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try eapply normalize_exp_wt_clock in Hnorm; eauto;
        inv Hwt; [destruct keep_fby| |].
    - (* fby (keep) *)
      repeat inv_bind.
      eapply normalize_exps_wt_clock with (G:=G) in H...
      eapply normalize_exps_wt_clock with (G:=G) in H0...
      eapply normalize_fby_wt_clock in H1...
      1,2:solve_forall; solve_incl.
    - (* fby (don't keep) *) eapply normalize_exp_wt_clock in Hnorm...
    - (* app *)
      repeat inv_bind.
      eapply normalize_exps_wt_clock with (G:=G) in H...
      solve_forall. solve_incl.
    - (* app (reset) *)
      repeat inv_bind.
      assert (incl (fresh_in r) (idty (st_anns x6))) as Hincl by (eapply normalize_exp_fresh_incl; eauto).
      assert (st_follows x6 st') as Hfollows by repeat solve_st_follows.
      assert (length x4 = numstreams r) as Hlength by eauto.
      assert (clocksof x4 = clockof r) as Hclockof by eauto.
      specialize (normalize_exp_wt_exp _ _ _ _ _ _ _ _ H8 H0) as Hwt.
      eapply normalize_exps_wt_clock with (G:=G) in H...
      eapply normalize_exp_wt_clock with (G:=G) in H0...
      eapply normalize_reset_wt_clock in H1...
      2,3:solve_forall; solve_incl.
      2:apply incl_appr'; solve_incl.
      assert (length x4 = 1).
      { rewrite Hlength. rewrite typeof_annot in H9. rewrite <- length_annot_numstreams.
        erewrite <- map_length. rewrite H9. reflexivity. }
      singleton_length.
      rewrite Hclockof.
      eapply wt_exp_clockof in H8.
      solve_forall. repeat solve_incl.
      apply incl_map. etransitivity...
      apply incl_map, st_follows_incl...
  Qed.

  Corollary normalize_rhss_wt_clock : forall G vars es keep_fby es' eqs' st st',
      Forall (wt_exp G vars) es ->
      Forall (wt_clock (vars++st_tys st)) (st_clocks st) ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      Forall (wt_clock (vars++st_tys st')) (st_clocks st').
  Proof.
    intros G vars es keep_fby es' eqs' st st' Hwt Hclocks Hnorm.
    unfold normalize_rhss in Hnorm. repeat inv_bind.
    eapply map_bind2_wt_clock in H; eauto.
    solve_forall. eapply normalize_rhs_wt_clock in H2; eauto.
  Qed.

  Fact normalize_equation_wt_clock : forall G vars eq to_cut eqs' st st',
      wt_equation G vars eq ->
      Forall (wt_clock (vars++st_tys st)) (st_clocks st) ->
      normalize_equation to_cut eq st = (eqs', st') ->
      Forall (wt_clock (vars++st_tys st')) (st_clocks st').
  Proof.
    intros G vars eq to_cut eqs' st st' Hwt Hclocks Hnorm.
    destruct eq; repeat inv_bind.
    destruct Hwt.
    eapply normalize_rhss_wt_clock in H; eauto.
  Qed.

  Corollary normalize_equations_wt_clock : forall G vars eqs to_cut eqs' st st',
      Forall (wt_equation G vars) eqs ->
      Forall (wt_clock (vars++st_tys st)) (st_clocks st) ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      Forall (wt_clock (vars++st_tys st')) (st_clocks st').
  Proof.
    induction eqs; intros to_cut eqs' st st' Hwt Hclocks Hnorm;
      unfold normalize_equations in Hnorm; repeat inv_bind.
    - assumption.
    - inv Hwt.
      eapply normalize_equation_wt_clock in H; eauto.
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
        eapply normalize_equations_wt_clock in Heqres; eauto.
        * simpl. unfold st_clocks in Heqres.
          solve_forall. rewrite Forall_forall in Heqres.
          destruct x as [? [? ck]].
          eapply wt_clock_incl; [| eapply Heqres].
          -- unfold idty. repeat rewrite map_app.
             repeat rewrite <- app_assoc; apply incl_appr'.
             rewrite Permutation_swap; apply incl_appr', incl_appr'.
             reflexivity.
          -- unfold idty in H.
             repeat simpl_In. inv H.
             exists (i, (t, ck, b)); simpl; split; auto.
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
        eapply iface_eq_wt_node; eauto.
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
       (Norm : FULLNORM Ids Op OpAux Syn)
       <: NTYPING Ids Op OpAux Syn Typ Norm.
  Include NTYPING Ids Op OpAux Syn Typ Norm.
End NTypingFun.
