From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LClocking.
From Velus Require Import Lustre.NormLast.NormLast.

Module Type NLCLOCKING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import NL  : NORMLAST Ids Op OpAux Cks Senv Syn).

  Import Fresh Notations Facts Tactics.

  (** *** Phase 1 *)

  Section init_block.
    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Variable sub : Env.t ident.

    Lemma init_exp_clockof : forall e,
        clockof (init_exp sub e) = clockof e.
    Proof.
      induction e using exp_ind2; destruct_conjs; simpl; auto.
      cases; auto.
    Qed.

    Corollary init_exp_clocksof : forall es,
        clocksof (map (init_exp sub) es) = clocksof es.
    Proof.
      unfold clocksof. intros.
      rewrite ? flat_map_concat_map, map_map. f_equal.
      apply map_ext; eauto using init_exp_clockof.
    Qed.

    Lemma init_exp_nclockof : forall sub e,
        Forall2 (fun '(ck1, o1) '(ck2, o2) => ck1 = ck2 /\ LiftO True (fun id1 => o2 = Some id1) o1)
          (nclockof e) (nclockof (init_exp sub e)).
    Proof.
      destruct e; destruct_conjs; simpl_Forall; auto.
      cases; simpl_Forall; repeat constructor.
    Qed.

    Corollary init_exp_nclocksof : forall sub es,
        Forall2 (fun '(ck1, o1) '(ck2, o2) => ck1 = ck2 /\ LiftO True (fun id1 => o2 = Some id1) o1)
          (nclocksof es) (nclocksof (map (init_exp sub) es)).
    Proof.
      intros.
      unfold nclocksof. rewrite 2 flat_map_concat_map.
      apply Forall2_concat. simpl_Forall.
      apply init_exp_nclockof.
    Qed.

    Variable Γ Γ' : static_env.

    Hypothesis Hck : forall x ck, HasClock Γ x ck -> HasClock Γ' x ck.
    Hypothesis Hvar : forall x y ck, Env.find x sub = Some y -> HasClock Γ x ck -> HasClock Γ' y ck.
    Hypothesis Hlast : forall x, Env.find x sub = None -> IsLast Γ x -> IsLast Γ' x.

    Lemma init_exp_wc : forall e,
        wc_exp G Γ e ->
        wc_exp G Γ' (init_exp sub e).
    Proof.
      induction e using exp_ind2; intros * Wc; inv Wc; simpl.
      1-12:(try econstructor; eauto; simpl_Forall; eauto using wc_clock_incl;
            intros; inv_equalities;
            repeat (take (forall d, Some _ = Some _ -> _) and specialize (it _ eq_refl));
            rewrite ? init_exp_clockof, ? init_exp_clocksof in *; simpl_Forall; eauto;
            try rewrite fst_NoDupMembers in *;
            try (erewrite map_map, map_ext; eauto; intros; destruct_conjs; auto);
            try (intros contra; take (_ -> False) and eapply it, map_eq_nil; eauto)).
      - (* last *)
        cases_eqn Eq; constructor; eauto using wc_clock_incl.
      - (* function call *)
        remember (Env.from_list (map_filter (fun '(x, (_, ox)) => option_map (fun xc => (x, xc)) ox)
                                   (combine (map fst (n_in n)) (nclocksof (map (init_exp sub) es))))) as sub2.
        assert (length (n_in n) = length (nclocksof (map (init_exp sub) es))) as Hlen2.
        1:{ apply Forall2_length in H8. repeat setoid_rewrite length_map in H8. rewrite H8.
            pose proof (init_exp_nclocksof sub es) as Hncks. apply Forall2_length in Hncks; auto. }
        assert (Forall2 (fun '(x, _) '(ck, ox) => LiftO (Env.find x sub2 = None) (fun x' => Env.MapsTo x x' sub2) ox) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof (map (init_exp sub) es))) as Hsub2.
        apply Forall2_forall; split. 2:repeat setoid_rewrite length_map; auto.
        1:{ intros (?&?) (?&?) Hin'.
            assert (In (k, (c0, o)) (combine (map fst (n_in n)) (nclocksof (map (init_exp sub) es)))) as Hin2.
            { repeat setoid_rewrite combine_map_fst in Hin'.
              eapply in_map_iff in Hin' as (((?&(?&?)&?)&?&?)&Heq&?); inv Heq.
              rewrite combine_map_fst. eapply in_map_iff. do 2 esplit; eauto. simpl; auto. }
            assert (NoDupMembers (combine (map fst (n_in n)) (nclocksof (map (init_exp sub) es)))) as Hnd1.
            { rewrite fst_NoDupMembers, combine_map_fst', <-fst_NoDupMembers. 2:now rewrite length_map.
              pose proof (n_nodup n) as (Hnd1&_). apply fst_NoDupMembers; eauto using NoDup_app_l. }
            destruct o; simpl; subst.
            + eapply Env.find_In_from_list.
              2:{ clear - Hnd1. remember (combine _ _) as comb. clear - Hnd1.
                  induction comb as [|(?&?&?)]; simpl in *; inv Hnd1. constructor.
                  destruct (option_map _ _) as [(?&?)|] eqn:Hopt; simpl; auto.
                  eapply option_map_inv in Hopt as (?&?&Heq); inv Heq.
                  econstructor; auto. intro contra. apply H1.
                  apply fst_InMembers, in_map_iff in contra as ((?&?)&?&Hin); subst.
                  apply map_filter_In' in Hin as ((?&?&?)&Hin&Hopt). apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
                  apply In_InMembers in Hin; auto.
              }
              eapply map_filter_In; eauto.
            + destruct (Env.find _ _) eqn:Hfind; auto. exfalso.
              eapply Env.from_list_find_In, map_filter_In' in Hfind as ((?&?&?)&Hin3&Hopt).
              apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
              eapply NoDupMembers_det in Hin2; eauto. inv Hin2.
        }
        pose proof (init_exp_nclocksof sub es) as Hncks; eapply Forall2_trans_ex in Hncks; eauto.
        eapply wc_Eapp with
          (bck:=bck)
          (sub:=fun x => match (sub0 x) with
                      | Some y => Some y
                      | _ => Env.find x sub2
                      end).
        all:simpl_Forall; eauto.
        + simpl_Forall. destruct b; inv_equalities. destruct o; simpl in *; subst.
          * eapply WellInstantiated_refines2; eauto. intros ?? Hsub. rewrite Hsub; auto.
          * eapply WellInstantiated_refines1; eauto.
            -- intros ?? Hsub. rewrite Hsub; auto.
            -- destruct H11 as (Hsub&_); simpl in *. rewrite Hsub.
               destruct o0; simpl in *; auto.
        + simpl_Forall. eapply WellInstantiated_refines1; eauto.
          * intros ?? Hsub. rewrite Hsub; auto.
          * destruct H3 as (Hsub&_); simpl in *. rewrite Hsub. subst.
            destruct (Env.find i _) eqn:Hfind; auto. exfalso.
            eapply Env.from_list_find_In, map_filter_In' in Hfind as ((?&?&?)&?&Hopt).
            apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
            pose proof (n_nodup n) as (Hnd&_). eapply NoDup_app_In in Hnd. eapply Hnd. solve_In.
            eapply in_combine_l in H3. solve_In.
        + erewrite init_exp_clockof; eauto.
    Qed.

    Lemma init_equation_wc : forall eq,
        wc_equation G Γ eq ->
        wc_equation G Γ' (init_equation sub eq).
    Proof.
      intros * Hwc. inv Hwc.
      - (* app *)
        remember (Env.from_list (map_filter (fun '(x, (_, ox)) => option_map (fun xc => (x, xc)) ox)
                                   (combine (map fst (n_in n)) (nclocksof (map (init_exp sub) es))))) as sub2.
        assert (length (n_in n) = length (nclocksof (map (init_exp sub) es))) as Hlen2.
        { apply Forall2_length in H2. repeat setoid_rewrite length_map in H2. rewrite H2.
          pose proof (init_exp_nclocksof sub es) as Hncks. apply Forall2_length in Hncks; auto. }
        assert (Forall2 (fun '(x, _) '(ck, ox) => LiftO (Env.find x sub2 = None) (fun x' => Env.MapsTo x x' sub2) ox) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof (map (init_exp sub) es))) as Hsub2.
        { apply Forall2_forall; split. 2:repeat setoid_rewrite length_map; auto.
          intros (?&?) (?&?) Hin'.
          assert (In (k, (c0, o)) (combine (map fst (n_in n)) (nclocksof (map (init_exp sub) es)))) as Hin2.
          { repeat setoid_rewrite combine_map_fst in Hin'.
            eapply in_map_iff in Hin' as (((?&(?&?)&?)&?&?)&Heq&?); inv Heq.
            rewrite combine_map_fst. eapply in_map_iff. do 2 esplit; eauto. simpl; auto. }
          assert (NoDupMembers (combine (map fst (n_in n)) (nclocksof (map (init_exp sub) es)))) as Hnd1.
          { rewrite fst_NoDupMembers, combine_map_fst', <-fst_NoDupMembers. 2:now rewrite length_map.
            pose proof (n_nodup n) as (Hnd1&_). apply fst_NoDupMembers; eauto using NoDup_app_l. }
          destruct o; simpl; subst.
          - eapply Env.find_In_from_list.
            2:{ clear - Hnd1. remember (combine _ _) as comb. clear - Hnd1.
                induction comb as [|(?&?&?)]; simpl in *; inv Hnd1. constructor.
                destruct (option_map _ _) as [(?&?)|] eqn:Hopt; simpl; auto.
                eapply option_map_inv in Hopt as (?&?&Heq); inv Heq.
                econstructor; auto. intro contra. apply H1.
                apply fst_InMembers, in_map_iff in contra as ((?&?)&?&Hin); subst.
                apply map_filter_In' in Hin as ((?&?&?)&Hin&Hopt). apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
                apply In_InMembers in Hin; auto.
            }
            eapply map_filter_In; eauto.
          - destruct (Env.find _ _) eqn:Hfind; auto. exfalso.
            eapply Env.from_list_find_In, map_filter_In' in Hfind as ((?&?&?)&Hin3&Hopt).
            apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
            eapply NoDupMembers_det in Hin2; eauto. inv Hin2.
        }
        pose proof (init_exp_nclocksof sub es) as Hncks; eapply Forall2_trans_ex in Hncks; eauto.
        eapply wc_EqApp with
          (bck:=bck)
          (sub:=fun x => match (sub0 x) with
                      | Some y => Some y
                      | _ => Env.find x sub2
                      end); simpl_Forall; eauto using in_or_app, init_exp_wc.
        3:erewrite init_exp_clockof; eauto.
        + simpl_Forall. destruct b; inv_equalities.
          destruct o; simpl in *; subst.
          * eapply WellInstantiated_refines2; eauto. intros ?? Hsub. rewrite Hsub; auto.
          * eapply WellInstantiated_refines1; eauto.
            -- intros ?? Hsub. rewrite Hsub; auto.
            -- destruct H10 as (Hsub&_); simpl in *. rewrite Hsub.
               destruct o0; simpl in *; auto.
        + eapply Forall3_impl_In; [|eauto]; intros; simpl in *.
          eapply WellInstantiated_refines2; eauto.
          intros * Hsub; rewrite Hsub; auto.

      - (* general case *)
        constructor; simpl_Forall; eauto using init_exp_wc.
        rewrite init_exp_clocksof; simpl_Forall; auto using in_or_app.
    Qed.

    Lemma init_block_wc : forall blk,
        unnested_block blk ->
        wc_block G Γ blk ->
        wc_block G Γ' (init_block sub blk).
    Proof.
      induction blk using block_ind2; intros * Un Wc; inv Un; inv Wc; simpl.
      - (* equation *)
        constructor. destruct eq. eapply init_equation_wc; eauto.
      - (* last *)
        take (clockof _ = _) and rewrite clockof_annot in it.
        destruct (annot e) as [|(?&?)[|]] eqn:Ann; simpl in *; inv it.
        cases_eqn Eq; repeat constructor; eauto using init_exp_wc.
        + simpl. rewrite init_exp_clockof, app_nil_r, clockof_annot, Ann; auto.
        + econstructor; eauto using init_exp_wc.
          rewrite init_exp_clockof, clockof_annot, Ann; auto.
      - (* reset *)
        econstructor; simpl_Forall; eauto.
        take (wc_exp _ _ _) and inv it; constructor; eauto using wc_clock_incl.
    Qed.

  End init_block.

  Lemma init_top_block_wc {PSyn prefs} (G: @global PSyn prefs) : forall ins outs blk outs' blk' st st',
      unnested outs blk ->
      NoDupMembers (ins ++ senv_of_decls outs) ->
      NoDupLocals (map fst (ins ++ senv_of_decls outs)) blk ->
      Forall (fun '(x, (_, ck, _, _)) => wc_clock (idck (ins ++ senv_of_decls outs)) ck) outs ->
      wc_block G (ins ++ senv_of_decls outs) blk ->
      init_top_block outs blk st = (outs', blk', st') ->
      wc_block G (ins ++ senv_of_decls outs') blk'.
  Proof.
    intros * Un Nd1 Nd2 WcCk Wc In. inv Un. inv Nd2. inv Wc.
    repeat (Syn.inv_scope || inv_scope). subst Γ'. repeat inv_bind.
    take (forall x, _ -> ~_) and eapply NoDupScope_NoDupMembers in it as ND; eauto.
    assert (forall x2 ty,
               HasClock ((ins ++ senv_of_decls outs) ++ senv_of_decls locs) x2 ty ->
               HasClock
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
    { intros *. rewrite senv_of_decls_app, ? HasClock_app.
        intros [[In|In]|In]; [auto|left;right|right;left].
        * inv In; simpl_In. destruct (Env.mem x2 (Env.from_list (map fst x0))) eqn:Mem.
          1,2:econstructor; solve_In; [rewrite Mem|]; eauto.
        * inv In; simpl_In.
          destruct (PS.mem x2 (PSUnion (map non_constant_lasts blks))) eqn:Mem.
          1,2:econstructor; solve_In; simpl; auto.
    }
    do 2 constructor.
    - rewrite ? map_app, ? Forall_app; split.
      + simpl_Forall.
        eapply wc_clock_incl; [|eauto]. apply HasClock_idck_incl. intros. simpl_app. auto.
      + simpl_Forall.
        eapply fresh_idents_In' in H2; eauto. rewrite <-filter_app, in_app_iff in H2.
        destruct H2; simpl_In; simpl_Forall.
        1,2:eapply wc_clock_incl; [|eauto]; apply HasClock_idck_incl.
        * intros * Ty. simpl_app. eapply Incl. rewrite app_assoc, HasClock_app; auto.
        * intros. simpl_app. eauto.
    - simpl_Forall.
      take (wc_block _ _ _) and eapply init_block_wc in it; eauto.
      + intros * Find.
        apply Env.from_list_find_In in Find.
        rewrite senv_of_decls_app, <-app_assoc, <-senv_of_decls_app, HasClock_app.
        intros [In|In]; [exfalso|rewrite ? HasClock_app; right; right].
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

    Lemma rename_exp_clockof : forall e,
        clockof (rename_exp sub e) = clockof e.
    Proof.
      induction e using exp_ind2; destruct_conjs; simpl; auto.
    Qed.

    Corollary rename_exp_clocksof : forall es,
        clocksof (map (rename_exp sub) es) = clocksof es.
    Proof.
      unfold clocksof. intros.
      rewrite ? flat_map_concat_map, map_map. f_equal.
      apply map_ext; eauto using rename_exp_clockof.
    Qed.

    Lemma rename_exp_nclockof : forall e,
        nclockof (rename_exp sub e) = nclockof e.
    Proof.
      induction e using exp_ind2; destruct_conjs; simpl; auto.
    Qed.

    Corollary rename_exp_nclocksof : forall es,
        nclocksof (map (rename_exp sub) es) = nclocksof es.
    Proof.
      unfold nclocksof. intros.
      rewrite ? flat_map_concat_map, map_map. f_equal.
      apply map_ext; eauto using rename_exp_nclockof.
    Qed.

    Variable Γ Γ' : static_env.

    Hypothesis Hty : forall x ck, HasClock Γ x ck -> HasClock Γ' x ck.
    Hypothesis Hvar : forall x y ck, Env.find x sub = Some y -> HasClock Γ x ck -> HasClock Γ' y ck.
    Hypothesis Hlast : forall x, Env.find x sub = None -> IsLast Γ x -> IsLast Γ' x.
    Hypothesis Hnlast : forall x y, Env.find x sub = Some y -> IsLast Γ x -> IsLast Γ' y.

    Lemma rename_exp_wc : forall e,
        wc_exp G Γ e ->
        wc_exp G Γ' (rename_exp sub e).
    Proof.
      induction e using exp_ind2; intros * Wc; inv Wc; simpl;
        try econstructor; eauto;
        intros; inv_equalities; repeat (take (forall d0, _ = _ -> _) and specialize (it _ eq_refl));
        simpl_Forall; eauto;
        rewrite ? rename_exp_clockof, ? rename_exp_clocksof, ? rename_exp_nclocksof in *; auto;
        simpl_Forall; eauto;
        try (intros contra; take (_ -> False) and eapply it, map_eq_nil; eauto).
      1,2:unfold rename_var, or_default; cases_eqn Eq; eauto.
    Qed.

    Lemma rename_block_wc : forall blk,
        unnested_block blk ->
        wc_block G Γ blk ->
        Forall (wc_block G Γ') (rename_block sub blk).
    Proof.
      induction blk using block_ind2; intros * Un Wc; inv Un; inv Wc; simpl.
      - (* equation *)
        destruct eq. take (wc_equation _ _ _) and inv it; simpl.
        + (* app *)
          repeat econstructor. 1-7:simpl_Forall; eauto using rename_exp_wc.
          * rewrite rename_exp_nclocksof; auto.
          * take (clockof _ = [_]) and rewrite rename_exp_clockof, it; eauto.
          * clear - Hty Hvar H8. rewrite Forall2_map_2 in H8.
            induction H8 as [|?(?&?)]; simpl; cases_eqn Eq; constructor; auto.
            do 2 econstructor; repeat constructor; eauto.
        + (* general case *)
          assert (Forall (wc_exp G Γ') (map (rename_exp sub) l0)).
          { simpl_Forall. eauto using rename_exp_wc. }
          inv H0. 5:take (normalized_cexp _) and inv it; try take (normalized_lexp _) and inv it.
          all:repeat (constructor; simpl in *; destruct_conjs; eauto using rename_exp_wc).
          all:try now (simpl_Forall; unfold rename_var, or_default; cases_eqn Eq; eauto).
          all:try now (cases_eqn Eq; repeat constructor; simpl_Forall; eauto).
          clear - Hty Hvar H3. rewrite app_nil_r, Forall2_map_2 in H3.
            induction H3 as [|?(?&?)]; simpl; cases_eqn Eq; constructor; auto.
            do 2 econstructor; repeat constructor; eauto.
      - (* last *)
        simpl_Forall. econstructor; eauto using rename_exp_wc.
        1,2:unfold rename_var, or_default; cases_eqn Eq; eauto.
        rewrite rename_exp_clockof; auto.
      - (* reset *)
        simpl_Forall.
        eapply H3 in H4; eauto.
        econstructor; simpl_Forall; eauto.
        take (wc_exp _ _ _) and inv it; constructor; eauto.
    Qed.

  End rename_block.

  Lemma output_top_block_wc {PSyn prefs} (G: @global PSyn prefs) : forall ins outs blk blk' st st',
      unnested outs blk ->
      NoDupMembers (ins ++ senv_of_decls outs) ->
      NoDupLocals (map fst (ins ++ senv_of_decls outs)) blk ->
      Forall (fun '(x, (_, ck, _, _)) => wc_clock (idck (ins ++ senv_of_decls outs)) ck) outs ->
      wc_block G (ins ++ senv_of_decls outs) blk ->
      output_top_block outs blk st = (blk', st') ->
      wc_block G (ins ++ senv_of_decls (remove_lasts outs)) blk'.
  Proof.
    intros * Un Nd1 Nd2 WcCk Wc In. inv Un. inv Nd2. inv Wc.
    repeat (Syn.inv_scope || inv_scope). subst Γ'. repeat inv_bind.
    take (forall x, _ -> ~_) and eapply NoDupScope_NoDupMembers in it as ND; eauto.
    unfold remove_lasts.
    do 2 constructor.
    - rewrite ? senv_of_decls_app, ? map_app, ? Forall_app; split.
      + simpl_Forall. simpl_In. simpl_Forall.
        eapply wc_clock_incl; [|eauto].
        apply HasClock_idck_incl. intros *.
        rewrite ? HasClock_app. intros [[|Ck]|]; auto.
        left; right. inv Ck. simpl_In. econstructor. solve_In. auto.
      + simpl_Forall.
        eapply fresh_idents_In' in H2; eauto. simpl_In. simpl_Forall.
        eapply wc_clock_incl; [|eauto].
        apply HasClock_idck_incl. intros *.
        rewrite ? HasClock_app in *. intros [|Ck]; auto.
        left; right. inv Ck. simpl_In. econstructor. solve_In. auto.
    - apply Forall_flat_map. simpl_Forall.
      take (wc_block _ _ _) and eapply rename_block_wc, Forall_forall in it; eauto.
      + intros * Ck. rewrite ? senv_of_decls_app, ? HasClock_app in *. destruct Ck as [[|Ty]|Ty]; auto.
        left; right. inv Ty. simpl_In. econstructor. solve_In. auto.
      + intros * Find.
        apply Env.from_list_find_In in Find.
        rewrite senv_of_decls_app, <-app_assoc, <-senv_of_decls_app, HasClock_app.
        intros [In|In]; [exfalso|rewrite ? HasClock_app; right; right].
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

    Hypothesis Hty : forall x ck, HasClock Γ x ck -> HasClock Γ' x ck.
    Hypothesis Hvar : forall x y ck, Env.find x sub = Some y -> HasClock Γ x ck -> HasClock Γ' y ck.
    Hypothesis Hlast : forall x, Env.find x sub = None -> IsLast Γ x -> IsLast Γ' x.
    Hypothesis Hnlast : forall x y, Env.find x sub = Some y -> IsLast Γ x -> IsLast Γ' y.

    Lemma unnest_block_wc : forall blk,
        unnested_block blk ->
        wc_block G Γ blk ->
        wc_block G Γ' (unnest_block sub blk).
    Proof.
      induction blk using block_ind2; intros * Un Wc; inv Un; inv Wc; simpl.
      - (* equation *)
        destruct eq. take (wc_equation _ _ _) and inv it; simpl.
        + (* app *)
          repeat econstructor. 1-7:simpl_Forall; eauto using rename_exp_wc.
          * rewrite rename_exp_nclocksof; auto.
          * take (clockof _ = [_]) and rewrite rename_exp_clockof, it; eauto.
        + (* general case *)
          assert (Forall (wc_exp G Γ') (map (rename_exp sub) l0)).
          { simpl_Forall. eauto using rename_exp_wc. }
          inv H0. 5:take (normalized_cexp _) and inv it; try take (normalized_lexp _) and inv it.
          all:repeat (constructor; simpl in *; destruct_conjs; eauto using rename_exp_wc).
          all:try now (simpl_Forall; unfold rename_var, or_default; cases_eqn Eq; eauto).
      - (* last *)
        econstructor; eauto using rename_exp_wc.
        1,2:unfold rename_var, or_default; cases_eqn Eq; eauto.
        rewrite rename_exp_clockof; auto.
      - (* reset *)
        simpl_Forall.
        eapply H3 in H4; eauto.
        econstructor; simpl_Forall; eauto.
        take (wc_exp _ _ _) and inv it; constructor; eauto.
    Qed.
  End unnest_block.

  Lemma unnest_top_block_wc {PSyn prefs} (G: @global PSyn prefs) : forall ins outs blk blk' st st',
      unnested outs blk ->
      NoDupMembers (senv_of_ins ins ++ senv_of_decls outs) ->
      NoDupLocals (map fst (senv_of_ins ins ++ senv_of_decls outs)) blk ->
      wc_block G (senv_of_ins ins ++ senv_of_decls outs) blk ->
      unnest_top_block blk st = (blk', st') ->
      wc_block G (senv_of_ins ins ++ senv_of_decls outs) blk'.
  Proof.
    intros * Un Nd1 Nd2 (* WcO WcCk *) Wc In. inv Un. inv Nd2. inv Wc.
    repeat (Syn.inv_scope || inv_scope). subst Γ'. repeat inv_bind.
    take (forall x, _ -> ~_) and eapply NoDupScope_NoDupMembers in it as ND; eauto.
    unfold remove_lasts.
    do 2 constructor. 2:apply Forall_app; split.
    - unfold senv_of_decls in *. rewrite ? map_app, ? Forall_app; split.
      + simpl_Forall.
        eapply wc_clock_incl; [|eauto]. apply HasClock_idck_incl. intros * Ty.
        rewrite ? HasClock_app in *. destruct Ty as [[|Ty]|Ty]; auto.
        right; left. inv Ty. simpl_In. econstructor. solve_In. auto.
      + simpl_Forall. simpl_In.
        eapply fresh_idents_In' in H2; eauto. simpl_In. simpl_Forall.
        eapply wc_clock_incl; [|eauto]. apply HasClock_idck_incl. intros * Ty.
        rewrite ? HasClock_app in *. destruct Ty as [[Ty|Ty]|Ty]; auto.
        right; left. inv Ty. simpl_In. econstructor. solve_In. auto.
    - simpl_Forall.
      eapply fresh_idents_In' in H2; eauto.
      unfold senv_of_decls in *. simpl_In.
      repeat constructor.
      + rewrite ? map_app, ? HasClock_app. right; left. econstructor. solve_In. auto.
      + rewrite ? map_app, ? HasClock_app. repeat right. econstructor. solve_In. auto.
    - simpl_Forall.
      take (wc_block _ _ _) and eapply unnest_block_wc in it; eauto.
      + intros * Ty. rewrite ? senv_of_decls_app, ? HasClock_app in *. destruct Ty as [[|Ty]|Ty]; auto.
        right; left. inv Ty. simpl_In. econstructor. solve_In. auto.
      + intros * Find.
        apply Env.from_list_find_In in Find.
        rewrite senv_of_decls_app, <-app_assoc, ? HasClock_app.
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

  Lemma normlast_top_block_wc {PSyn prefs} (G: @global PSyn prefs) : forall ins outs blk blk' st st',
      let Γ := senv_of_ins ins ++ senv_of_decls outs in
      let Γ' := senv_of_ins ins ++ senv_of_decls (remove_lasts outs) in
      unnested outs blk ->
      (exists ls : list ident, LastsDefined blk ls /\ Permutation.Permutation ls (lasts_of_decls outs)) ->
      NoDupMembers Γ ->
      NoDupLocals (map fst Γ) blk ->
      Forall (AtomOrGensym norm1_prefs) (map fst ins ++ map fst outs) ->
      GoodLocals norm1_prefs blk ->
      Forall (fun '(x, (_, ck, _, _)) => wc_clock (idck Γ) ck) outs ->
      wc_block G Γ blk ->
      normlast_top_block outs blk st = (blk', st') ->
      wc_block G Γ' blk'.
  Proof.
    unfold normlast_top_block in *.
    intros * Un Lasts NDenv ND At Good WcC Wc DL. repeat inv_bind.

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
    eapply init_top_block_wc in H as Wc1; eauto.

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
    eapply output_top_block_wc in H0 as Wc2; eauto.
    2:now rewrite fst_NoDupMembers, map_app, map_fst_senv_of_decls, Fst,
        <-map_fst_senv_of_decls, <-map_app, <-fst_NoDupMembers.
    2:now rewrite map_app, map_fst_senv_of_ins, map_fst_senv_of_decls, Fst.
    2:{ clear - H WcC. repeat inv_bind.
        simpl_Forall. destruct (Env.mem _ _); simpl.
        1,2:eapply wc_clock_incl; [|eauto].
        1,2:unfold idck, senv_of_ins, senv_of_decls; simpl_app; apply incl_appr'; erewrite ? map_map, map_ext; [reflexivity|].
        1,2:intros; destruct_conjs; destruct (Env.mem _ _); simpl; auto. }

    (* Phase 3 *)
    eapply unnest_top_block_wc in H1 as Wc3; eauto.
    1:{ clear - Fst Un2. inv Un2. constructor; auto.
        rewrite remove_lasts_fst, <-Fst, <-remove_lasts_fst; auto. }
    1:now rewrite fst_NoDupMembers, map_app, map_fst_senv_of_decls, remove_lasts_fst,
        <- map_fst_senv_of_decls, <-map_app, <-fst_NoDupMembers.
    1:now rewrite map_app, map_fst_senv_of_ins, map_fst_senv_of_decls, remove_lasts_fst.
    1:rewrite <-RM; auto.
  Qed.

  (** Typing of the node *)

  Lemma normlast_node_wc : forall G1 G2 (n : @node _ _),
      global_iface_incl G1 G2 ->
      wc_node G1 n ->
      wc_node G2 (normlast_node n).
  Proof.
    intros * Hiface Wc. inversion_clear Wc as [? Wc1 Wc2 Wc3].
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    pose proof (n_good n) as (Hat&Hgood&_).
    repeat econstructor; simpl; eauto.
    - unfold remove_lasts; erewrite map_map, map_ext with (l:=n_out _); eauto.
      intros; unfold decl in *; destruct_conjs; auto.
    - eapply normlast_top_block_wc in Wc3; eauto with lclocking. 6:apply surjective_pairing.
      + apply n_syn.
      + apply n_lastd.
      + apply node_NoDupMembers.
      + apply node_NoDupLocals.
      + apply Forall_app in Wc2 as (?&?); auto.
        simpl_Forall.
        unfold idck, senv_of_ins, senv_of_decls.
        erewrite ? map_app, ? map_map, map_ext with (l:=n_in _), map_ext with (l:=n_out _); eauto.
        1,2:intros; unfold decl in *; destruct_conjs; auto.
  Qed.

  Theorem normlast_global_wc : forall G,
      wc_global G ->
      wc_global (normlast_global G).
  Proof.
    unfold wc_global, normlast_global.
    intros * Hwc.
    eapply CommonTyping.transform_units_wt_program; eauto.
    intros ?? Hwc'.
    eapply normlast_node_wc; eauto. eapply iface_eq_iface_incl, normlast_global_iface_eq.
  Qed.


End NLCLOCKING.

Module NLClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (NL  : NORMLAST Ids Op OpAux Cks Senv Syn)
       <: NLCLOCKING Ids Op OpAux Cks Senv Syn Clo NL.
  Include NLCLOCKING Ids Op OpAux Cks Senv Syn Clo NL.
End NLClockingFun.
