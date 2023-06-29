From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping.
From Velus Require Import Lustre.NormLast.NormLast.

Module Type NLTYPING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Clo : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import NL  : NORMLAST Ids Op OpAux Cks Senv Syn).

  Import Fresh Notations Facts Tactics.

  (** *** Phase 1 *)

  Section init_block.
    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Variable sub : Env.t ident.

    Variable Γ Γ' : static_env.

    Hypothesis Hty : forall x ty, HasType Γ x ty -> HasType Γ' x ty.
    Hypothesis Hvar : forall x y ty, Env.find x sub = Some y -> HasType Γ x ty -> HasType Γ' y ty.
    Hypothesis Hlast : forall x, Env.find x sub = None -> IsLast Γ x -> IsLast Γ' x.

    Lemma init_exp_wt : forall e,
        wt_exp G Γ e ->
        wt_exp G Γ' (init_exp sub e).
    Proof.
      induction e using exp_ind2; intros * Wt; inv Wt; simpl;
        try econstructor; eauto; simpl_Forall; eauto using wt_clock_incl;
        rewrite ? init_exp_typeof, ? init_exp_typesof; auto;
        try rewrite fst_NoDupMembers in *;
        try (erewrite map_map, map_ext; eauto; intros; destruct_conjs; auto);
        try (intros contra; take (_ -> False) and eapply it, map_eq_nil; eauto).
      cases_eqn Eq; constructor; eauto using wt_clock_incl.
    Qed.

    Lemma init_block_wt : forall blk,
        unnested_block blk ->
        wt_block G Γ blk ->
        wt_block G Γ' (init_block sub blk).
    Proof.
      induction blk using block_ind2; intros * Un Wt; inv Un; inv Wt; simpl.
      - (* equation *)
        constructor. destruct eq. take (wt_equation _ _ _) and inv it. simpl.
        rewrite init_exp_typesof.
        split; simpl_Forall; eauto using init_exp_wt.
      - (* last *)
        take (typeof _ = _) and rewrite typeof_annot in it.
        destruct (annot e) as [|(?&?)[|]] eqn:Ann; simpl in *; inv it.
        take (wt_exp _ _ _) and eapply wt_exp_clockof in it as WtC; rewrite clockof_annot, Ann in WtC; simpl_Forall.
        cases_eqn Eq; repeat constructor; eauto using init_exp_wt, wt_clock_incl.
        + simpl. rewrite init_exp_typeof, app_nil_r, typeof_annot, Ann; auto.
        + econstructor; eauto using init_exp_wt.
          rewrite init_exp_typeof, typeof_annot, Ann; auto.
      - (* reset *)
        constructor; simpl_Forall; auto.
        take (wt_exp _ _ _) and inv it; constructor; eauto using wt_clock_incl.
    Qed.

  End init_block.

  Lemma init_top_block_wt {PSyn prefs} (G: @global PSyn prefs) : forall ins outs blk outs' blk' st st',
      unnested outs blk ->
      NoDupMembers (ins ++ senv_of_decls outs) ->
      NoDupLocals (map fst (ins ++ senv_of_decls outs)) blk ->
      Forall (fun '(_, ann) => OpAux.wt_type (types G) (typ ann)) (senv_of_decls outs) ->
      wt_clocks G.(types) (ins ++ senv_of_decls outs) (senv_of_decls outs) ->
      wt_block G (ins ++ senv_of_decls outs) blk ->
      init_top_block outs blk st = (outs', blk', st') ->
      wt_block G (ins ++ senv_of_decls outs') blk'.
  Proof.
    intros * Un Nd1 Nd2 WtO WtCk Wt In. inv Un. inv Nd2. inv Wt.
    repeat (Syn.inv_scope || inv_scope). subst Γ'. repeat inv_bind.
    take (forall x, _ -> ~_) and eapply NoDupScope_NoDupMembers in it as ND; eauto.
    assert (forall x2 ty,
               HasType ((ins ++ senv_of_decls outs) ++ senv_of_decls locs) x2 ty ->
               HasType
                 ((ins ++
                     senv_of_decls
                     (map
                        (fun '(x3, (ty0, ck, cx, clx)) =>
                           if Env.mem x3 (Env.from_list (map fst x0)) then (x3, (ty0, ck, cx, None)) else (x3, (ty0, ck, cx, clx)))
                        outs)) ++
                    senv_of_decls
                    (map
                       (fun '(x3, (ty0, ck, cx, o)) =>
                          (x3, (ty0, ck, cx, if PS.mem x3 (PSUnion (map non_constant_lasts blks)) then None else o))) locs ++
                       map (fun '(_, lx, (ty0, ck)) => (lx, (ty0, ck, 1%positive, None))) x0)) x2 ty
           ) as Incl.
    { intros *. rewrite senv_of_decls_app, ? HasType_app.
        intros [[In|In]|In]; [auto|left;right|right;left].
        * inv In; simpl_In. destruct (Env.mem x2 (Env.from_list (map fst x0))) eqn:Mem.
          1,2:econstructor; solve_In; [rewrite Mem|]; eauto.
        * inv In; simpl_In.
          destruct (PS.mem x2 (PSUnion (map non_constant_lasts blks))) eqn:Mem.
          1,2:econstructor; solve_In; simpl; auto.
    }
    do 2 constructor.
    - unfold wt_clocks, senv_of_decls in *. rewrite senv_of_decls_app, ? Forall_app; split.
      + simpl_Forall. simpl_In. simpl_Forall.
        eapply wt_clock_incl; [|eauto]. intros. simpl_app. auto.
      + simpl_Forall. simpl_In.
        eapply fresh_idents_In' in H2; eauto. rewrite <-filter_app, in_app_iff in H2.
        destruct H2; simpl_In; simpl_Forall.
        1,2:eapply wt_clock_incl; [|eauto].
        * intros * Ty. simpl_app. eapply Incl. rewrite app_assoc, HasType_app; auto.
        * intros. simpl_app. eauto.
    - rewrite map_app, Forall_app. split; simpl_Forall; auto.
      take (fresh_idents _ _ = _) and eapply fresh_idents_In' in it; eauto.
      unfold senv_of_decls in *.
      rewrite <-filter_app, in_app_iff in it. destruct it; simpl_In; simpl_Forall; auto.
    - simpl_Forall.
      take (wt_block _ _ _) and eapply init_block_wt in it; eauto.
      + intros * Find.
        apply Env.from_list_find_In in Find.
        rewrite senv_of_decls_app, <-app_assoc, <-senv_of_decls_app, HasType_app.
        intros [In|In]; [exfalso|rewrite ? HasType_app; right; right].
        * inv In. simpl_In.
          eapply fresh_idents_In' in H2; eauto. simpl_In.
          rewrite <-app_assoc in ND. eapply NoDupMembers_app_InMembers in ND; [|solve_In].
          eapply ND, InMembers_app.
          apply in_app_iff in Hin0 as [|]; [left|right]; solve_In.
        * simpl_In. econstructor. solve_In. simpl.
          eapply fresh_idents_In' in H2; eauto.
          rewrite <-map_filter_app in *.
          inv In. simpl_In.
          eapply NoDupMembers_det in Hin1; eauto. now inv Hin1.
          rewrite <-app_assoc, <-senv_of_decls_app in ND.
          now apply NoDupMembers_app_r, NoDupMembers_senv_of_decls in ND.
      + intros *. rewrite senv_of_decls_app, ? IsLast_app.
        intros Find [[In|In]|In]; [auto|left;right|right;left].
        * inv In. econstructor. solve_In.
          rewrite Env.mem_find, Find; eauto. auto.
        * inv In. simpl_In. econstructor. solve_In. simpl.
          destruct o; cases_eqn Mem; try congruence.
          exfalso.
          eapply Env.Props.P.F.not_find_in_iff, Env.In_from_list; eauto.
          erewrite <-fresh_idents_InMembers; eauto.
          rewrite <-filter_app, InMembers_app. right. solve_In. auto.
  Qed.

  (** *** Phase 2 *)

  Section rename_block.
    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Variable sub : Env.t ident.

    Variable Γ Γ' : static_env.

    Hypothesis Hty : forall x ty, HasType Γ x ty -> HasType Γ' x ty.
    Hypothesis Hvar : forall x y ty, Env.find x sub = Some y -> HasType Γ x ty -> HasType Γ' y ty.
    Hypothesis Hlast : forall x, Env.find x sub = None -> IsLast Γ x -> IsLast Γ' x.
    Hypothesis Hnlast : forall x y, Env.find x sub = Some y -> IsLast Γ x -> IsLast Γ' y.

    Lemma rename_exp_wt : forall e,
        wt_exp G Γ e ->
        wt_exp G Γ' (rename_exp sub e).
    Proof.
      induction e using exp_ind2; intros * Wt; inv Wt; simpl;
        try econstructor; eauto; simpl_Forall; eauto using wt_clock_incl;
        rewrite ? rename_exp_typeof, ? rename_exp_typesof; auto;
        try rewrite fst_NoDupMembers in *;
        try (erewrite map_map, map_ext; eauto; intros; destruct_conjs; auto);
        try (intros contra; take (_ -> False) and eapply it, map_eq_nil; eauto).
      1,2:unfold rename_var, or_default; cases_eqn Eq; eauto.
    Qed.

    Lemma rename_block_wt : forall blk,
        unnested_block blk ->
        wt_block G Γ blk ->
        Forall (wt_block G Γ') (rename_block sub blk).
    Proof.
      induction blk using block_ind2; intros * Un Wt; inv Un; inv Wt; simpl.
      - (* equation *)
        destruct eq. take (wt_equation _ _ _) and inv it; simpl.
        assert (Forall (wt_exp G Γ') (map (rename_exp sub) l0)).
        { simpl_Forall. eauto using rename_exp_wt. }
        inv H0. 5:take (normalized_cexp _) and inv it; try take (normalized_lexp _) and inv it.
        all:repeat (constructor; simpl in *; destruct_conjs; eauto using rename_exp_wt).
        all:try now (simpl_Forall; unfold rename_var, or_default; cases_eqn Eq; eauto).
        all:try now (cases_eqn Eq; repeat constructor; simpl_Forall; eauto;
                     take (wt_exp _ _ _) and eapply wt_exp_clockof in it; simpl in it;
                     simpl_Forall; eauto using wt_clock_incl).
        apply Forall_singl, wt_exp_clockof in H; simpl in H.
        rewrite app_nil_r, Forall2_map_2 in H1. clear - Hty Hvar H H1.
        induction H1 as [|? (?&?)]; inv H; simpl in *; cases_eqn Eq; constructor; auto.
        do 2 econstructor; repeat constructor; eauto using wt_clock_incl.
      - (* last *)
        do 2 econstructor; eauto using rename_exp_wt.
        1,2:unfold rename_var, or_default; cases_eqn Eq; eauto.
        rewrite rename_exp_typeof; auto.
      - (* reset *)
        simpl_Forall. eapply H3 in H4; eauto. simpl_Forall.
        constructor; eauto.
        take (wt_exp _ _ _) and inv it; constructor; eauto using wt_clock_incl.
    Qed.

  End rename_block.

  Lemma output_top_block_wt {PSyn prefs} (G: @global PSyn prefs) : forall ins outs blk blk' st st',
      unnested outs blk ->
      NoDupMembers (ins ++ senv_of_decls outs) ->
      NoDupLocals (map fst (ins ++ senv_of_decls outs)) blk ->
      Forall (fun '(_, ann) => OpAux.wt_type (types G) (typ ann)) (senv_of_decls outs) ->
      wt_clocks G.(types) (ins ++ senv_of_decls outs) (senv_of_decls outs) ->
      wt_block G (ins ++ senv_of_decls outs) blk ->
      output_top_block outs blk st = (blk', st') ->
      wt_block G (ins ++ senv_of_decls (remove_lasts outs)) blk'.
  Proof.
    intros * Un Nd1 Nd2 WtO WtCk Wt In. inv Un. inv Nd2. inv Wt.
    repeat (Syn.inv_scope || inv_scope). subst Γ'. repeat inv_bind.
    take (forall x, _ -> ~_) and eapply NoDupScope_NoDupMembers in it as ND; eauto.
    unfold remove_lasts.
    do 2 constructor.
    - unfold wt_clocks, senv_of_decls in *. rewrite senv_of_decls_app, ? Forall_app; split.
      + simpl_Forall. simpl_In. simpl_Forall.
        eapply wt_clock_incl; [|eauto]. intros * Ty.
        rewrite ? HasType_app in *. destruct Ty as [[|Ty]|]; auto.
        left; right. inv Ty. simpl_In. econstructor. solve_In. auto.
      + simpl_Forall. simpl_In.
        eapply fresh_idents_In' in H2; eauto. simpl_In. simpl_Forall.
        eapply wt_clock_incl; [|eauto]. intros * Ty.
        rewrite ? HasType_app in *. destruct Ty as [|Ty]; auto.
        left; right. inv Ty. simpl_In. econstructor. solve_In. auto.
    - rewrite map_app, Forall_app. split; simpl_Forall; auto.
      take (fresh_idents _ _ = _) and eapply fresh_idents_In' in it; eauto.
      unfold senv_of_decls in *. simpl_In. simpl_Forall. auto.
    - apply Forall_flat_map. simpl_Forall.
      take (wt_block _ _ _) and eapply rename_block_wt, Forall_forall in it; eauto.
      + intros * Ty. rewrite ? senv_of_decls_app, ? HasType_app in *. destruct Ty as [[|Ty]|Ty]; auto.
        left; right. inv Ty. simpl_In. econstructor. solve_In. auto.
      + intros * Find.
        apply Env.from_list_find_In in Find.
        rewrite senv_of_decls_app, <-app_assoc, <-senv_of_decls_app, HasType_app.
        intros [In|In]; [exfalso|rewrite ? HasType_app; right; right].
        * inv In. simpl_In.
          eapply fresh_idents_In' in H2; eauto. simpl_In.
          rewrite <-app_assoc in ND. eapply NoDupMembers_app_InMembers in ND; [|solve_In].
          eapply ND, InMembers_app. left. solve_In.
        * simpl_In. econstructor. solve_In. simpl.
          eapply fresh_idents_In' in H2; eauto.
          inv In. simpl_In.
          eapply NoDupMembers_det in Hin1; [| |apply in_app_iff; eauto]. now inv Hin1.
          rewrite <-app_assoc, <-senv_of_decls_app in ND.
          now apply NoDupMembers_app_r, NoDupMembers_senv_of_decls in ND.
      + intros *. rewrite senv_of_decls_app, ? IsLast_app.
        intros Find [[In|In]|In]; auto. repeat right.
        exfalso. inv In. simpl_In. destruct o; try congruence.
        eapply Env.Props.P.F.not_find_in_iff, Env.In_from_list; eauto.
        erewrite <-fresh_idents_InMembers; eauto. solve_In. auto.
      + intros * Find. rewrite senv_of_decls_app, ? IsLast_app.
        apply Env.from_list_find_In in Find. simpl_In. eapply fresh_idents_In' in H2; eauto. simpl_In.
        intros [[In|In]|In]; auto.
        * exfalso. inv In.
          eapply NoDupMembers_app_InMembers in Nd1; eauto using In_InMembers. eapply Nd1; solve_In.
        * repeat right. econstructor. solve_In. simpl. congruence.
        * exfalso. inv In. simpl_In.
          eapply it0; eauto using In_InMembers. rewrite map_app, in_app_iff. right. solve_In.
  Qed.

  (** *** Phase 3 *)

  Section unnest_block.
    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Variable sub : Env.t ident.

    Variable Γ Γ' : static_env.

    Hypothesis Hty : forall x ty, HasType Γ x ty -> HasType Γ' x ty.
    Hypothesis Hvar : forall x y ty, Env.find x sub = Some y -> HasType Γ x ty -> HasType Γ' y ty.
    Hypothesis Hlast : forall x, Env.find x sub = None -> IsLast Γ x -> IsLast Γ' x.
    Hypothesis Hnlast : forall x y, Env.find x sub = Some y -> IsLast Γ x -> IsLast Γ' y.

    Lemma unnest_block_wt : forall blk,
        unnested_block blk ->
        wt_block G Γ blk ->
        wt_block G Γ' (unnest_block sub blk).
    Proof.
      induction blk using block_ind2; intros * Un Wt; inv Un; inv Wt; simpl.
      - (* equation *)
        cases. take (wt_equation _ _ _) and inv it.
        repeat constructor; auto.
        + simpl_Forall; eauto using rename_exp_wt.
        + rewrite rename_exp_typesof. simpl_Forall. auto.
      - (* last *)
        econstructor; eauto using rename_exp_wt.
        1,2:unfold rename_var, or_default; cases_eqn Eq; eauto.
        rewrite rename_exp_typeof; auto.
      - (* reset *)
        constructor; simpl_Forall; auto.
        take (wt_exp _ _ _) and inv it; constructor; eauto using wt_clock_incl.
    Qed.
  End unnest_block.

  Lemma unnest_top_block_wt {PSyn prefs} (G: @global PSyn prefs) : forall ins outs blk blk' st st',
      unnested outs blk ->
      NoDupMembers (senv_of_ins ins ++ senv_of_decls outs) ->
      NoDupLocals (map fst (senv_of_ins ins ++ senv_of_decls outs)) blk ->
      wt_block G (senv_of_ins ins ++ senv_of_decls outs) blk ->
      unnest_top_block blk st = (blk', st') ->
      wt_block G (senv_of_ins ins ++ senv_of_decls outs) blk'.
  Proof.
    intros * Un Nd1 Nd2 (* WtO WtCk *) Wt In. inv Un. inv Nd2. inv Wt.
    repeat (Syn.inv_scope || inv_scope). subst Γ'. repeat inv_bind.
    take (forall x, _ -> ~_) and eapply NoDupScope_NoDupMembers in it as ND; eauto.
    unfold remove_lasts.
    do 2 constructor. 3:apply Forall_app; split.
    - unfold wt_clocks, senv_of_decls in *. rewrite senv_of_decls_app, ? Forall_app; split.
      + simpl_Forall. simpl_In. simpl_Forall.
        eapply wt_clock_incl; [|eauto]. intros * Ty.
        rewrite ? HasType_app in *. destruct Ty as [|Ty]; auto.
        right; left. inv Ty. simpl_In. econstructor. solve_In. auto.
      + simpl_Forall. simpl_In.
        eapply fresh_idents_In' in H2; eauto. simpl_In. simpl_Forall.
        eapply wt_clock_incl; [|eauto]. intros * Ty.
        rewrite ? HasType_app in *. destruct Ty as [|Ty]; auto.
        right; left. inv Ty. simpl_In. econstructor. solve_In. auto.
    - rewrite map_app, Forall_app. split; simpl_Forall; auto.
      take (fresh_idents _ _ = _) and eapply fresh_idents_In' in it; eauto.
      unfold senv_of_decls in *. simpl_In. simpl_Forall. auto.
    - simpl_Forall.
      eapply fresh_idents_In' in H2; eauto.
      unfold senv_of_decls in *. simpl_In.
      repeat constructor.
      + rewrite ? map_app, ? HasType_app. right; left. econstructor. solve_In. auto.
      + unfold wt_clocks in *. simpl_Forall.
        eapply wt_clock_incl; [|eauto]. intros * Ty.
        rewrite ? map_app, ? HasType_app in *. destruct Ty as [|Ty]; auto.
        right; left. inv Ty. simpl_In. econstructor. solve_In. auto.
      + rewrite ? map_app, ? HasType_app. repeat right. econstructor. solve_In. auto.
    - simpl_Forall.
      take (wt_block _ _ _) and eapply unnest_block_wt in it; eauto.
      + intros * Ty. rewrite ? senv_of_decls_app, ? HasType_app in *. destruct Ty as [[|Ty]|Ty]; auto.
        right; left. inv Ty. simpl_In. econstructor. solve_In. auto.
      + intros * Find.
        apply Env.from_list_find_In in Find.
        rewrite senv_of_decls_app, <-app_assoc, ? HasType_app.
        intros [In|[In|In]]; [exfalso|exfalso|repeat right].
        * inv In. simpl_In.
          eapply fresh_idents_In' in H2; eauto. simpl_In.
          rewrite <-app_assoc in ND. eapply NoDupMembers_app_InMembers in ND; [|solve_In].
          eapply ND, InMembers_app. right. solve_In.
        * inv In. simpl_In.
          eapply fresh_idents_In' in H2; eauto. simpl_In.
          rewrite <-app_assoc in ND. eapply NoDupMembers_app_r, NoDupMembers_app_InMembers in ND; [|solve_In].
          eapply ND. solve_In.
        * inv In. simpl_In.
          eapply fresh_idents_In' in H2; eauto. simpl_In.
          eapply NoDupMembers_det in Hin0; eauto. inv Hin0.
          econstructor. solve_In. auto.
      + intros *. rewrite senv_of_decls_app, ? IsLast_app.
        intros Find [[In|In]|In]; auto. right; left.
        inv In. simpl_In. destruct o; try congruence.
        econstructor. solve_In. simpl. cases_eqn Eq; auto.
        exfalso.
        eapply Env.Props.P.F.not_find_in_iff, Env.In_from_list; eauto.
        erewrite <-fresh_idents_InMembers; eauto. solve_In. auto.
      + intros * Find. rewrite senv_of_decls_app, ? IsLast_app.
        apply Env.from_list_find_In in Find. simpl_In. eapply fresh_idents_In' in H2; eauto. simpl_In.
        intros [[In|In]|In]; auto.
        * exfalso. inv In. unfold senv_of_ins in *. simpl_In. congruence.
        * exfalso. inv In.
          eapply it0; eauto using In_InMembers. rewrite map_app, in_app_iff. right. solve_In.
        * repeat right. econstructor. solve_In. simpl. congruence.
  Qed.

  Lemma normlast_top_block_wt {PSyn prefs} (G: @global PSyn prefs) : forall ins outs blk blk' st st',
      let Γ := senv_of_ins ins ++ senv_of_decls outs in
      let Γ' := senv_of_ins ins ++ senv_of_decls (remove_lasts outs) in
      unnested outs blk ->
      (exists ls : list ident, LastsDefined blk ls /\ Permutation.Permutation ls (lasts_of_decls outs)) ->
      NoDupMembers Γ ->
      NoDupLocals (map fst Γ) blk ->
      Forall (AtomOrGensym norm1_prefs) (map fst ins ++ map fst outs) ->
      GoodLocals norm1_prefs blk ->
      wt_clocks (types G) Γ (senv_of_decls outs) ->
      Forall (fun '(_, ann) => OpAux.wt_type (types G) (typ ann)) (senv_of_decls outs) ->
      wt_block G Γ blk ->
      normlast_top_block outs blk st = (blk', st') ->
      wt_block G Γ' blk'.
  Proof.
    unfold normlast_top_block in *.
    intros * Un Lasts NDenv ND At Good WtC WtT Wt DL. repeat inv_bind.

    assert (NoDupMembers outs) as NDo.
    { now apply NoDupMembers_app_r, NoDupMembers_senv_of_decls in NDenv. }

    (* Phase 1 *)
    eapply init_top_block_unnested in H as Un1; eauto.
    2:{ eapply NoDupLocals_incl; [|eauto]. rewrite map_app, map_fst_senv_of_decls. solve_incl_app. }
    inversion Un. inversion Un1. subst.
    assert (Forall (fun x : ident => AtomOrGensym norm1_prefs x \/ In x (st_ids st)) (map fst locs)) as AtL0.
    { inv Good. repeat Syn.inv_scope. simpl_Forall. auto. }
    eapply init_top_block_NoDupLocals with (xs:=map fst ins ++ map fst outs) in H as ND1; eauto.
    2:{ now rewrite map_app, map_fst_senv_of_ins, map_fst_senv_of_decls in ND. }
    eapply init_top_block_wt in H as Wt1; eauto.

    (* remove some lasts in outs *)
    assert (remove_lasts x = remove_lasts outs) as RM.
    { clear - H. repeat inv_bind. unfold remove_lasts.
      erewrite map_map, map_ext; [reflexivity|].
      intros; destruct_conjs; cases; auto.
    }
    assert (map fst x = map fst outs) as Fst.
    { now rewrite <-remove_lasts_fst, RM, remove_lasts_fst. }
    assert (NoDupMembers x) as NDo1.
    { now rewrite fst_NoDupMembers, Fst, <-fst_NoDupMembers. }
    assert (NoDupLocals (map fst x) (Blocal (Scope locs0 blks0))) as ND'1.
    { rewrite Fst. eapply NoDupLocals_incl; [|eauto]. apply incl_appr, incl_refl. }

    (* Phase 2 *)
    eapply output_top_block_unnested in H0 as Un2; eauto.
    inversion Un2. subst.
    assert (Forall (fun x : ident => AtomOrGensym norm1_prefs x \/ In x (st_ids x1)) (map fst locs0)) as AtL1.
    { clear - H AtL0. repeat inv_bind. rewrite map_app, Forall_app. split.
      + simpl_Forall. destruct AtL0; auto.
        right. eapply incl_map; eauto. apply st_follows_incl; eauto using fresh_idents_st_follows.
      + eapply fresh_idents_In_ids in H. simpl_Forall. auto.
    }
    eapply output_top_block_NoDupLocals with (outs:=x) in H0 as ND2; eauto.
    eapply output_top_block_wt in H0 as Wt2; eauto.
    2:now rewrite fst_NoDupMembers, map_app, map_fst_senv_of_decls, Fst,
        <-map_fst_senv_of_decls, <-map_app, <-fst_NoDupMembers.
    2:now rewrite map_app, map_fst_senv_of_ins, map_fst_senv_of_decls, Fst.
    2:{ clear - H WtT. repeat inv_bind. unfold remove_lasts, senv_of_decls in *.
        simpl_Forall. destruct (Env.mem _ _); simpl_Forall; auto. }
    2:{ clear - H WtC. repeat inv_bind. unfold wt_clocks, remove_lasts, senv_of_decls in *.
        simpl_Forall. destruct (Env.mem _ _); simpl_Forall; auto.
        1,2:eapply wt_clock_incl; [|eauto].
        1,2:(intros *; rewrite ?HasType_app; intros [|Ty]; auto; right; inv Ty; simpl_In;
             (destruct (Env.mem x (Env.from_list (map fst x0))) eqn:Eq;
              econstructor; solve_In; try rewrite Eq; eauto)).
    }

    (* Phase 3 *)
    eapply unnest_top_block_wt in H1 as Wt3; eauto.
    1:{ clear - Fst Un2. inv Un2. constructor; auto.
        rewrite remove_lasts_fst, <-Fst, <-remove_lasts_fst; auto. }
    1:now rewrite fst_NoDupMembers, map_app, map_fst_senv_of_decls, remove_lasts_fst,
        <- map_fst_senv_of_decls, <-map_app, <-fst_NoDupMembers.
    1:now rewrite map_app, map_fst_senv_of_ins, map_fst_senv_of_decls, remove_lasts_fst.
    1:rewrite <-RM; auto.
  Qed.

  (** Typing of the node *)

  Lemma normlast_node_wt : forall G1 G2 (n : @node _ _),
      global_iface_incl G1 G2 ->
      wt_node G1 n ->
      wt_node G2 (normlast_node n).
  Proof.
    intros * Hiface Wt. inversion_clear Wt as [??? Wt1 Wt2 Wt3]. subst Γ.
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    pose proof (n_good n) as (Hat&Hgood&_).
    repeat econstructor; simpl; eauto.
    1-3:unfold remove_lasts, wt_clocks, senv_of_decls in *; simpl_Forall; eauto with ltyping.
    - eapply wt_clock_incl; [|eauto with ltyping].
      intros *. rewrite 2 HasType_app. intros [|Ty]; auto. right.
      inv Ty. simpl_In. econstructor. solve_In. auto.
    - apply Forall_app in Wt2 as (?&?). unfold senv_of_ins, senv_of_decls in *.
      apply in_app_iff in H0 as [|]; simpl_In; simpl_Forall; eauto with ltyping.
    - eapply normlast_top_block_wt in Wt3; eauto with ltyping. 6:apply surjective_pairing.
      + apply n_syn.
      + apply n_lastd.
      + apply node_NoDupMembers.
      + apply node_NoDupLocals.
      + apply Forall_app in Wt2 as (?&?); auto.
  Qed.

  Theorem normlast_global_wt : forall G,
      wt_global G ->
      wt_global (normlast_global G).
  Proof.
    unfold wt_global, normlast_global.
    intros * (?&Hwt).
    split; auto.
    eapply CommonTyping.transform_units_wt_program; eauto.
    intros ?? Hwt'.
    eapply normlast_node_wt; eauto. eapply iface_eq_iface_incl, normlast_global_iface_eq.
  Qed.

End NLTYPING.

Module NLTypingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LTYPING Ids Op OpAux Cks Senv Syn)
       (NL  : NORMLAST Ids Op OpAux Cks Senv Syn)
       <: NLTYPING Ids Op OpAux Cks Senv Syn Clo NL.
  Include NLTYPING Ids Op OpAux Cks Senv Syn Clo NL.
End NLTypingFun.
