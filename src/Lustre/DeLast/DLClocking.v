From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LClocking.
From Velus Require Import Lustre.DeLast.DeLast.

Module Type DLCLOCKING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import DL  : DELAST Ids Op OpAux Cks Senv Syn).

  Section rename.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Variable sub : Env.t ident.

    Section rename_in_exp.
      Variable Γ Γ' : static_env.

      Hypothesis Hvar : forall x ty, HasClock Γ x ty -> HasClock Γ' x ty.
      Hypothesis Hlast : forall x ty, HasClock Γ x ty -> IsLast Γ x -> HasClock Γ' (rename_in_var sub x) ty.

      Lemma rename_in_exp_clockof : forall e,
          clockof (rename_in_exp sub e) = clockof e.
      Proof.
        destruct e; destruct_conjs; simpl; auto.
      Qed.

      Corollary rename_in_exp_clocksof : forall es,
          clocksof (map (rename_in_exp sub) es) = clocksof es.
      Proof.
        induction es; simpl; auto.
        f_equal; auto using rename_in_exp_clockof.
      Qed.

      Lemma rename_in_exp_nclockof : forall sub e,
          Forall2 (fun '(ck1, o1) '(ck2, o2) => ck1 = ck2 /\ LiftO True (fun id1 => o2 = Some id1) o1)
                  (nclockof e) (nclockof (rename_in_exp sub e)).
      Proof.
        destruct e; destruct_conjs; simpl_Forall; auto.
      Qed.

      Corollary rename_in_exp_nclocksof : forall sub es,
          Forall2 (fun '(ck1, o1) '(ck2, o2) => ck1 = ck2 /\ LiftO True (fun id1 => o2 = Some id1) o1)
                  (nclocksof es) (nclocksof (map (rename_in_exp sub) es)).
      Proof.
        intros.
        unfold nclocksof. rewrite 2 flat_map_concat_map.
        apply Forall2_concat. simpl_Forall.
        apply rename_in_exp_nclockof.
      Qed.

      Lemma rename_in_exp_wc : forall e,
          wc_exp G Γ e ->
          wc_exp G Γ' (rename_in_exp sub e).
      Proof.
        intros * Hwc; induction e using exp_ind2; inv Hwc; simpl.
        12:remember (Env.from_list (map_filter (fun '(x, (_, ox)) => option_map (fun xc => (x, xc)) ox)
                                            (combine (map fst (n_in n)) (nclocksof (map (rename_in_exp sub) es))))) as sub2.
        12:assert (length (n_in n) = length (nclocksof (map (rename_in_exp sub) es))) as Hlen2.
        12:{ apply Forall2_length in H8. repeat setoid_rewrite map_length in H8. rewrite H8.
             pose proof (rename_in_exp_nclocksof sub es) as Hncks. apply Forall2_length in Hncks; auto. }
        12:assert (Forall2 (fun '(x, _) '(ck, ox) => LiftO (Env.find x sub2 = None) (fun x' => Env.MapsTo x x' sub2) ox) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof (map (rename_in_exp sub) es))) as Hsub2.
        12:{ apply Forall2_forall; split. 2:repeat setoid_rewrite map_length; auto.
             intros (?&?) (?&?) Hin'.
             assert (In (k, (c0, o)) (combine (map fst (n_in n)) (nclocksof (map (rename_in_exp sub) es)))) as Hin2.
             { repeat setoid_rewrite combine_map_fst in Hin'.
               eapply in_map_iff in Hin' as (((?&(?&?)&?)&?&?)&Heq&?); inv Heq.
               rewrite combine_map_fst. eapply in_map_iff. do 2 esplit; eauto. simpl; auto. }
             assert (NoDupMembers (combine (map fst (n_in n)) (nclocksof (map (rename_in_exp sub) es)))) as Hnd1.
             { rewrite fst_NoDupMembers, combine_map_fst', <-fst_NoDupMembers. 2:now rewrite map_length.
               pose proof (n_nodup n) as (Hnd1&_). apply NoDupMembers_app_l in Hnd1; auto. }
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
        12:(pose proof (rename_in_exp_nclocksof sub es) as Hncks; eapply Forall2_trans_ex in Hncks; eauto).

        12:eapply wc_Eapp with
          (bck:=bck)
          (sub:=fun x => match (sub0 x) with
                      | Some y => Some y
                      | _ => Env.find x sub2
                      end).
        1-11:econstructor.
        1-40:eauto using in_or_app; simpl_Forall; eauto;
          match goal with
          | |- clockof _ = _ => rewrite rename_in_exp_clockof; auto
          | |- context [clocksof _] => rewrite rename_in_exp_clocksof; auto
          | H: context [clocksof _] |- _ => rewrite rename_in_exp_clocksof in H; auto
          | _ => idtac
          end.
        - simpl_Forall; auto.
        - intros contra. apply map_eq_nil in contra; subst. contradiction.
        - simpl_Forall; auto.
        - intros contra. apply map_eq_nil in contra; subst. contradiction.
        - simpl_Forall; auto.
        - intros. inv_equalities; subst. specialize (H11 _ eq_refl). simpl_Forall; eauto.
        - intros. inv_equalities; subst. rewrite rename_in_exp_clocksof; eauto.
        - intros. inv_equalities; subst. rewrite rename_in_exp_clocksof; eauto.
        - destruct b; inv_equalities. destruct o; simpl in *; subst.
          + eapply WellInstantiated_refines2; eauto. intros ?? Hsub. rewrite Hsub; auto.
          + eapply WellInstantiated_refines1; eauto.
            * intros ?? Hsub. rewrite Hsub; auto.
            * destruct H11 as (Hsub&_); simpl in *. rewrite Hsub.
              destruct o0; simpl in *; auto.
        - eapply WellInstantiated_refines1; eauto.
          + intros ?? Hsub. rewrite Hsub; auto.
          + destruct H3 as (Hsub&_); simpl in *. rewrite Hsub. subst.
            destruct (Env.find i _) eqn:Hfind; auto. exfalso.
            eapply Env.from_list_find_In, map_filter_In' in Hfind as ((?&?&?)&?&Hopt).
            apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
            pose proof (n_nodup n) as (Hnd&_). eapply NoDupMembers_app_InMembers in Hnd. eapply Hnd.
            rewrite fst_InMembers. solve_In.
            apply In_InMembers, fst_InMembers in H3. erewrite combine_map_fst', <-fst_InMembers in H3; eauto.
            now rewrite map_length.
        - erewrite rename_in_exp_clockof; eauto.
      Qed.

      Lemma rename_in_equation_wc : forall eq,
          wc_equation G Γ eq ->
          wc_equation G Γ' (rename_in_equation sub eq).
      Proof.
        intros * Hwc. inv Hwc.
        - (* app *)
          remember (Env.from_list (map_filter (fun '(x, (_, ox)) => option_map (fun xc => (x, xc)) ox)
                                              (combine (map fst (n_in n)) (nclocksof (map (rename_in_exp sub) es))))) as sub2.
          assert (length (n_in n) = length (nclocksof (map (rename_in_exp sub) es))) as Hlen2.
          { apply Forall2_length in H2. repeat setoid_rewrite map_length in H2. rewrite H2.
            pose proof (rename_in_exp_nclocksof sub es) as Hncks. apply Forall2_length in Hncks; auto. }
          assert (Forall2 (fun '(x, _) '(ck, ox) => LiftO (Env.find x sub2 = None) (fun x' => Env.MapsTo x x' sub2) ox) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof (map (rename_in_exp sub) es))) as Hsub2.
          { apply Forall2_forall; split. 2:repeat setoid_rewrite map_length; auto.
            intros (?&?) (?&?) Hin'.
            assert (In (k, (c0, o)) (combine (map fst (n_in n)) (nclocksof (map (rename_in_exp sub) es)))) as Hin2.
            { repeat setoid_rewrite combine_map_fst in Hin'.
              eapply in_map_iff in Hin' as (((?&(?&?)&?)&?&?)&Heq&?); inv Heq.
              rewrite combine_map_fst. eapply in_map_iff. do 2 esplit; eauto. simpl; auto. }
            assert (NoDupMembers (combine (map fst (n_in n)) (nclocksof (map (rename_in_exp sub) es)))) as Hnd1.
            { rewrite fst_NoDupMembers, combine_map_fst', <-fst_NoDupMembers. 2:now rewrite map_length.
              pose proof (n_nodup n) as (Hnd1&_). apply NoDupMembers_app_l in Hnd1; auto. }
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
          pose proof (rename_in_exp_nclocksof sub es) as Hncks; eapply Forall2_trans_ex in Hncks; eauto.
          eapply wc_EqApp with
          (bck:=bck)
          (sub:=fun x => match (sub0 x) with
                      | Some y => Some y
                      | _ => Env.find x sub2
                      end); simpl_Forall; eauto using in_or_app, rename_in_exp_wc.
          3:erewrite rename_in_exp_clockof; eauto.
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
          constructor; simpl_Forall; eauto using rename_in_exp_wc.
          rewrite rename_in_exp_clocksof; simpl_Forall; auto using in_or_app.
      Qed.

    End rename_in_exp.

  End rename.

  Import Fresh Facts Tactics.

  Fact delast_scope_wc {A} P_nd P_wc1 (P_wc2: _ -> _ -> Prop) f_dl f_add {PSyn prefs} (G: @global PSyn prefs) :
    forall locs caus (blk: A) sub Γ Γty Γ' s' st st',
      (forall x ty, HasClock Γ x ty -> HasClock Γ' x ty) ->
      (forall x ty, HasClock Γ x ty -> IsLast Γ x -> HasClock Γ' (rename_in_var sub x) ty) ->
      incl (map fst Γ) Γty ->
      (forall x, Env.In x sub -> In x Γty) ->
      NoDupScope P_nd Γty (Scope locs caus blk) ->
      wc_scope P_wc1 G Γ (Scope locs caus blk) ->
      delast_scope f_dl f_add sub (Scope locs caus blk) st = (s', st') ->
      (forall Γ Γty Γ' sub blk' st st',
          (forall x ty, HasClock Γ x ty -> HasClock Γ' x ty) ->
          (forall x ty, HasClock Γ x ty -> IsLast Γ x -> HasClock Γ' (rename_in_var sub x) ty) ->
          incl (map fst Γ) Γty ->
          (forall x, Env.In x sub -> In x Γty) ->
          P_nd Γty blk ->
          P_wc1 Γ blk ->
          f_dl sub blk st = (blk', st') ->
          P_wc2 Γ' blk') ->
      (forall Γ blks1 blks2,
          Forall (wc_block G Γ) blks1 ->
          P_wc2 Γ blks2 ->
          P_wc2 Γ (f_add blks1 blks2)) ->
      wc_scope P_wc2 G Γ' s'.
  Proof.
    intros * Hvar Hlast Hincl Hsubin Hnd Hwt Hdl Hind Hadd; inv Hnd; inv Hwt; repeat inv_bind.
    assert (forall y, Env.In y (Env.from_list (map fst x)) -> IsLast (senv_of_locs locs) y) as Hsubin'.
    { intros *. rewrite Env.In_from_list.
      eapply fresh_idents_InMembers in H. erewrite <-H, fst_InMembers.
      intros; simpl_In. econstructor; solve_In. simpl. congruence. }
    assert (forall x2 ty,
               HasClock (Γ ++ senv_of_locs locs) x2 ty ->
               HasClock
                 (Γ' ++ @senv_of_locs exp
                     (map (fun '(x3, (ty0, ck, cx, _)) => (x3, (ty0, ck, cx, None))) locs ++
                          map (fun '(_, lx, (ty0, ck, _)) => (lx, (ty0, ck, 1%positive, None))) x)) x2 ty) as Hvar'.
    { intros *. rewrite 2 HasClock_app. intros [|Hck]; auto.
      right. inv Hck; simpl_In.
      econstructor. solve_In. 2:apply in_app_iff, or_introl; solve_In.
      1,2:eauto.
    }
    assert (forall x2 ty,
               HasClock (Γ ++ senv_of_locs locs) x2 ty ->
               IsLast (Γ ++ senv_of_locs locs) x2 ->
               HasClock
                 (Γ' ++
                     @senv_of_locs exp
                     (map (fun '(x3, (ty0, ck, cx, _)) => (x3, (ty0, ck, cx, None))) locs ++
                          map (fun '(_, lx, (ty0, ck, _)) => (lx, (ty0, ck, 1%positive, None))) x))
                 (rename_in_var (Env.union sub (Env.from_list (map fst x))) x2) ty) as Hlast'.
    { intros *. rewrite 2 HasClock_app, IsLast_app.
      intros [Hty|Hty] [Hl|Hl]; eauto.
      - left. rewrite not_in_union_rename2; eauto.
        intro contra. apply Hsubin' in contra.
        inv Hl. inv contra. simpl_In.
        eapply H5; eauto using In_InMembers. eapply Hincl; solve_In.
      - exfalso.
        inv Hty. inv Hl. simpl_In.
        eapply H5; eauto using In_InMembers. eapply Hincl; solve_In.
      - exfalso.
        inv Hty. inv Hl. simpl_In.
        eapply H5; eauto using In_InMembers. eapply Hincl; solve_In.
      - right. simpl_app. apply HasClock_app. right.
        inv Hty. inv Hl. simpl_In. eapply NoDupMembers_det in Hin0; eauto; inv_equalities.
        destruct o0 as [(?&?)|]; simpl in *; try congruence.
        eapply fresh_idents_In_rename in H. 3:solve_In; simpl; auto.
        2:{ apply NoDupMembers_map_filter; auto. intros; destruct_conjs; auto.
            destruct o as [(?&?)|]; simpl in *; auto. }
        econstructor. solve_In. rewrite not_in_union_rename1; eauto. 2:reflexivity.
        intro contra. apply Hsubin in contra.
        eapply H5; eauto using In_InMembers.
    }
    econstructor; eauto. 3:apply Hadd.
    + rewrite map_app. apply Forall_app; split; auto.
      * simpl_Forall. eapply wc_clock_incl; eauto.
        intros (?&?) Hin. simpl_In. assert (HasClock (Γ++map _ locs) i1 a.(clo)) as Hck by eauto with senv.
        eapply Hvar' in Hck. inv Hck; solve_In. congruence.
      * eapply mmap_values, Forall2_ignore1 in H; simpl_Forall.
        repeat inv_bind. simpl_In.
        simpl_Forall. eapply wc_clock_incl; eauto.
        intros (?&?) ?. simpl_In. assert (HasClock (Γ++map _ locs) i a.(clo)) as Hck by eauto with senv.
        eapply Hvar' in Hck. inv Hck; solve_In. congruence.
    + simpl_app. apply Forall_app; split; auto.
      * simpl_Forall; auto.
      * eapply mmap_values, Forall2_ignore1 in H; simpl_Forall.
        repeat inv_bind. simpl_In.
        simpl_Forall; eauto.
    + simpl_Forall. repeat constructor; simpl.
      * eapply fresh_idents_In' in H; eauto. simpl_In. simpl_Forall.
        eapply rename_in_exp_wc in H; eauto.
      * eapply fresh_idents_In' in H; eauto. simpl_In.
        econstructor. simpl_app. repeat rewrite in_app_iff. right; left; solve_In. auto.
      * eapply fresh_idents_In' in H; eauto. simpl_In.
        simpl_Forall.
        rewrite rename_in_exp_clockof, app_nil_r, H3; auto.
      * econstructor. simpl_app. repeat rewrite in_app_iff. right; right; solve_In. simpl; eauto.
    + eapply Hind; eauto.
      * rewrite map_app, map_fst_senv_of_locs. apply incl_appl'; auto.
      * intros * Hin. rewrite in_app_iff. apply Env.union_In in Hin as [|Hin]; eauto.
        right.
        apply Hsubin' in Hin. inv Hin. solve_In.
  Qed.

  Lemma delast_block_wc {PSyn prefs} (G: @global PSyn prefs) : forall blk sub Γ Γty Γ' blk' st st',
      (forall x ck, HasClock Γ x ck -> HasClock Γ' x ck) ->
      (forall x ck, HasClock Γ x ck -> IsLast Γ x -> HasClock Γ' (rename_in_var sub x) ck) ->
      incl (map fst Γ) Γty ->
      (forall x, Env.In x sub -> In x Γty) ->
      NoDupLocals Γty blk ->
      wc_block G Γ blk ->
      delast_block sub blk st = (blk', st') ->
      wc_block G Γ' blk'.
  Proof.
    Opaque delast_scope.
    induction blk using block_ind2; intros * Hvar Hlast Hincl Hsubin Hnd Hwc Hdl;
      inv Hnd; inv Hwc; repeat inv_bind.

    - (* equation *)
      constructor.
      eapply rename_in_equation_wc; eauto.

    - (* reset *)
      econstructor.
      + eapply mmap_values, Forall2_ignore1 in H0; eauto.
        simpl_Forall; eauto.
      + eapply rename_in_exp_wc; eauto.
      + rewrite rename_in_exp_clockof; eauto.

    - (* switch *)
      eapply wc_Bswitch with (Γ':=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, Build_annotation e.(typ) Cbase e.(causl) e.(causl_last)) else None) Γ').
      + eapply rename_in_exp_wc; eauto.
      + rewrite rename_in_exp_clockof; eauto.
      + apply mmap_values in H0. inv H0; auto. congruence.
      + intros * Hca. inv Hca. simpl_In. destruct (clo a ==b ck) eqn:Hck; inv Hf; simpl.
        rewrite equiv_decb_equiv in Hck. inv Hck.
        split; eauto with senv.
      + intros * Hl. inv Hl. simpl_In. destruct (clo a ==b ck) eqn:Hck; inv Hf; simpl.
        eauto with senv.
      + eapply mmap_values, Forall2_ignore1 in H0; eauto.
        simpl_Forall; eauto. repeat inv_bind.
        destruct s0. eapply delast_scope_wc in H9; eauto.
        * intros * Hck. apply H6 in Hck as (?&?); subst; eauto.
          eapply Hvar in H10. inv H10. econstructor; solve_In. simpl. rewrite equiv_decb_refl; eauto. auto.
        * intros * Hck Hl. apply H6 in Hck as (Hck&?); subst.
          eapply H8, Hlast in Hl; eauto.
          inv Hl. econstructor; solve_In. simpl. rewrite equiv_decb_refl. eauto. auto.
        * intros ? Hin. simpl_In. assert (HasClock Γ'0 a a0.(clo)) as Hck by eauto with senv.
          apply H6 in Hck as (Hck&?); subst. inv Hck.
          apply Hincl; solve_In.
        * intros; simpl in *.
          eapply mmap_values, Forall2_ignore1 in H16. simpl_Forall; eauto.
        * intros. apply Forall_app; auto.

    - (* automaton *)
      assert (forall x ck',
                 HasClock Γ'0 x ck' ->
                 HasClock
                   (map_filter
                      (fun '(x, e0) =>
                         if clo e0 ==b ck then Some (x, ann_with_clock e0 Cbase) else None) Γ') x ck') as Hvar'.
      { intros * Hck. apply H8 in Hck as (?&?); subst; eauto.
        eapply Hvar in H1. inv H1. econstructor; solve_In. simpl. rewrite equiv_decb_refl; eauto. auto.
      }
      assert (forall x ck',
                 HasClock Γ'0 x ck' ->
                 IsLast Γ'0 x ->
                 HasClock
                   (map_filter
                      (fun '(x, e0) =>
                         if clo e0 ==b ck then Some (x, ann_with_clock e0 Cbase) else None) Γ') (rename_in_var sub x) ck') as Hlast'.
      { intros * Hck Hl. apply H8 in Hck as (Hck&?); subst.
        eapply H9, Hlast in Hl; eauto.
        inv Hl. econstructor; solve_In. simpl. rewrite equiv_decb_refl. eauto. auto.
      }
      eapply wc_Bauto with (Γ':=map_filter (fun '(x, e) => if e.(clo) ==b ck then Some (x, Build_annotation e.(typ) Cbase e.(causl) e.(causl_last)) else None) Γ').
      + eapply wc_clock_incl; eauto. intros ? Hin; simpl_In.
        assert (HasClock Γ i0 a0.(clo)) as Hck by (eauto with senv).
        apply Hvar in Hck; inv Hck. solve_In. congruence.
      + apply mmap_values in H0. inv H0; auto. congruence.
      + intros * Hca. inv Hca. simpl_In. destruct (clo a ==b ck) eqn:Hck; inv Hf; simpl.
        rewrite equiv_decb_equiv in Hck. inv Hck.
        split; eauto with senv.
      + intros * Hl. inv Hl. simpl_In. destruct (clo a ==b ck) eqn:Hck; inv Hf; simpl.
        eauto with senv.
      + simpl_Forall. split; eauto using rename_in_exp_wc.
        now rewrite rename_in_exp_clockof.
      + eapply mmap_values, Forall2_ignore1 in H0; eauto.
        simpl_Forall. repeat inv_bind.
        destruct s0; destruct_conjs; split.
        2:eapply delast_scope_wc in H3; eauto.
        * simpl_Forall. rewrite rename_in_exp_clockof; eauto using rename_in_exp_wc.
        * intros ? Hin. simpl_In. assert (HasClock Γ'0 a a0.(clo)) as Hck by eauto with senv.
          apply H8 in Hck as (Hck&?); subst. inv Hck.
          apply Hincl; solve_In.
        * intros; destruct_conjs; repeat inv_bind. split.
          -- eapply mmap_values, Forall2_ignore1 in H17. simpl_Forall; eauto.
          -- simpl_Forall; split; eauto using rename_in_exp_wc.
             now rewrite rename_in_exp_clockof.
        * intros; simpl in *. destruct_conjs.
          split; auto. apply Forall_app; auto.

    - (* local *)
      constructor. eapply delast_scope_wc; eauto.
        * intros; simpl in *.
          eapply mmap_values, Forall2_ignore1 in H9. simpl_Forall; eauto.
        * intros. apply Forall_app; auto.
          Transparent delast_scope.
  Qed.

  (** Typing of the node *)

  Lemma delast_node_wc : forall G1 G2 (n : @node _ _),
      global_iface_incl G1 G2 ->
      wc_node G1 n ->
      wc_node G2 (delast_node n).
  Proof.
    intros * Hiface (Hwc1&Hwc2&Hwc3).
    pose proof (n_nodup n) as (_&Hnd2).
    pose proof (n_good n) as (_&Hgood&_).
    pose proof (n_syn n) as Hsyn.
    repeat econstructor; simpl; eauto.
    eapply delast_block_wc in Hwc3. 7:apply surjective_pairing.
    - eapply iface_incl_wc_block, Hwc3; eauto.
    - auto.
    - intros * _ Hl. apply senv_of_inout_NoLast in Hl as [].
    - reflexivity.
    - intros. rewrite Env.Props.P.F.empty_in_iff in H. inv H.
    - rewrite map_fst_senv_of_inout; auto.
  Qed.

  Theorem delast_global_wc : forall G,
      wc_global G ->
      wc_global (delast_global G).
  Proof.
    unfold wc_global, delast_global.
    intros * Hwc.
    eapply CommonTyping.transform_units_wt_program; eauto.
    intros ?? Hwc'.
    eapply delast_node_wc; eauto. eapply iface_eq_iface_incl, delast_global_iface_eq.
  Qed.

End DLCLOCKING.

Module DLClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (DL  : DELAST Ids Op OpAux Cks Senv Syn)
       <: DLCLOCKING Ids Op OpAux Cks Senv Syn Clo DL.
  Include DLCLOCKING Ids Op OpAux Cks Senv Syn Clo DL.
End DLClockingFun.
