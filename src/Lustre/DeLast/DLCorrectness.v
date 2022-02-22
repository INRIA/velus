From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LCausality Lustre.LSemantics Lustre.LClockSemantics.
From Velus Require Import Lustre.DeLast.DeLast Lustre.DeLast.DLTyping Lustre.DeLast.DLClocking.

Module Type DLCORRECTNESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (LCA        : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Import Ty : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import Cl : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import Ord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (Import LCS : LCLOCKSEMANTICS Ids Op OpAux Cks Senv Syn Ty Cl LCA Ord CStr Sem)
       (Import DL  : DELAST Ids Op OpAux Cks Senv Syn).

  Module Typing := DLTypingFun Ids Op OpAux Cks Senv Syn Ty DL.
  Module Clocking := DLClockingFun Ids Op OpAux Cks Senv Syn Cl DL.

  Section rename.
    Variable sub : Env.t ident.

    Import List.

    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Section rename_in_exp.

      Variable Γ : static_env.
      Variable H Hl H' : CStr.history.

      Hypothesis Hsub : forall x vs,
          IsLast Γ x ->
          sem_var Hl x vs ->
          sem_var H' (rename_in_var sub x) vs.

      Hypothesis Hnsub : Env.refines (@EqSt _) H H'.

      Lemma rename_in_exp_sem : forall bs e vss,
          wx_exp Γ e ->
          sem_exp_ck G (H, Hl) bs e vss ->
          sem_exp_ck G (H', Env.empty _) bs (rename_in_exp sub e) vss.
      Proof.
        induction e using exp_ind2; intros * Hwx Hsem; inv Hwx; inv Hsem; simpl.
        1-13:econstructor; simpl in *; eauto using sem_var_refines.
        1-3:rewrite Typing.rename_in_exp_typeof; auto.
        1-5,10-12:(simpl in *; simpl_Forall; eauto).
        - specialize (H8 _ eq_refl). simpl_Forall; eauto.
        - rewrite <-Forall2Brs_map_1. eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hs.
          simpl_Exists. simpl_Forall. eauto.
        - rewrite <-Forall2Brs_map_1. eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hs.
          simpl_Exists. simpl_Forall. eauto.
        - rewrite Typing.rename_in_exp_typeof; auto.
        - rewrite <-Forall2Brs_map_1. eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hs.
          simpl_Exists. simpl_Forall. eauto.
      Qed.

      Corollary rename_in_equation_sem : forall bs eq,
          wx_equation Γ eq ->
          sem_equation_ck G (H, Hl) bs eq ->
          sem_equation_ck G (H', @Env.empty _) bs (rename_in_equation sub eq).
      Proof.
        intros * Hwx Hsem. inv Hsem. inv Hwx. simpl in *.
        eapply Seq with (ss:=ss); simpl_Forall; eauto using sem_var_refines, rename_in_exp_sem.
      Qed.

    End rename_in_exp.

    Fact mask_hist_sub2 Γ : forall k r H H',
      (forall x vs, IsLast Γ x -> sem_var H x vs -> sem_var H' (rename_in_var sub x) vs) ->
      forall x vs, IsLast Γ x -> sem_var (CStr.mask_hist k r H) x vs -> sem_var (CStr.mask_hist k r H') (rename_in_var sub x) vs.
    Proof.
      intros * Hsub * ? Hv.
      eapply sem_var_mask_inv in Hv as (?&Hv&Heq).
      eapply Hsub, sem_var_mask in Hv; eauto. rewrite Heq; eauto.
    Qed.

    Fact filter_hist_sub2 Γ : forall k r H H',
      (forall x vs, IsLast Γ x -> sem_var H x vs -> sem_var H' (rename_in_var sub x) vs) ->
      forall x vs, IsLast Γ x -> sem_var (CStr.ffilter_hist k r H) x vs -> sem_var (CStr.ffilter_hist k r H') (rename_in_var sub x) vs.
    Proof.
      intros * Hsub * ? Hv.
      eapply sem_var_ffilter_inv in Hv as (?&Hv&Heq).
      eapply Hsub, sem_var_ffilter in Hv; eauto. rewrite Heq; eauto.
    Qed.

  End rename.

  Import Fresh Facts Tactics.
  Import List.

  Section delast_node_sem.
    Variable G1 : @global (fun _ => True) elab_prefs.
    Variable G2 : @global nolast_block last_prefs.

    Hypothesis HGref : global_sem_refines G1 G2.
    Hypothesis HwG1 : wc_global G1.

    Fact sem_var_adds' : forall H xs x vs,
        sem_var (Env.adds' xs H) x vs ->
        (exists vs', vs ≡ vs' /\ In (x, vs') xs) \/ sem_var H x vs.
    Proof.
      intros * Hv. inv Hv.
      eapply Env.find_adds'_In in H1 as [Hin|Hfind]; eauto using sem_var.
    Qed.

    Lemma sem_var_disj_adds' : forall xs Hi2 x vs,
        NoDupMembers xs ->
        (forall x, InMembers x xs -> ~Env.In x Hi2) ->
        sem_var (Env.adds' xs Hi2) x vs <-> (exists vs', vs ≡ vs' /\ In (x, vs') xs) \/ sem_var Hi2 x vs.
    Proof.
      intros * Hnd Hdisj.
      split.
      - eapply sem_var_adds'.
      - intros [(?&Heq&Hin)|Hv]; [|inv Hv]; econstructor; eauto; unfold Env.MapsTo in *.
        + eapply Env.In_find_adds'; eauto.
        + erewrite Env.gsso'; eauto.
          intros Hinm. eapply Hdisj; eauto.
          econstructor; eauto.
    Qed.

    Lemma sem_var_disj_union : forall Hi1 Hi2 x vs,
        (forall x, Env.In x Hi1 -> ~Env.In x Hi2) ->
        sem_var (Env.union Hi1 Hi2) x vs <-> sem_var Hi1 x vs \/ sem_var Hi2 x vs.
    Proof.
      intros * Hdisj; split.
      - eapply sem_var_union.
      - intros [Hv|Hv]; inv Hv; econstructor; eauto; unfold Env.MapsTo in *.
        + erewrite Env.union_find2; eauto.
          eapply Env.Props.P.F.not_find_in_iff, Hdisj.
          econstructor; eauto.
        + erewrite Env.union_find3; eauto.
          eapply Env.Props.P.F.not_find_in_iff; intros ?.
          eapply Hdisj; eauto. econstructor; eauto.
    Qed.

    Lemma local_hist_dom_ub : forall xs ys (H H' : Env.t (Stream svalue)),
        Env.dom_ub H xs ->
        Env.dom H' (map fst (Env.elements H) ++ ys) ->
        Env.dom_ub H' (xs ++ ys).
    Proof.
      intros * Hdom1 Hdom2.
      eapply Env.dom_ub_intro; intros ? Hin.
      eapply Env.dom_use in Hin; [|eauto].
      rewrite in_app_iff in *. destruct Hin as [?|?]; auto.
      left. eapply Env.dom_ub_use; eauto.
      eapply in_map_iff in H0 as ((?&?)&?&?); subst.
      eapply Env.elements_In; eauto.
    Qed.

    Fact InMembers_sub {A} : forall (sub : Env.t ident) (xs : list (ident * A)) x,
        InMembers x (map_filter (fun '(x, vs) => option_map (fun y : ident => (y, vs)) (Env.find x sub)) xs) ->
        exists y, Env.MapsTo y x sub.
    Proof.
      intros * Hinm.
      eapply InMembers_In in Hinm as (?&Hin).
      eapply map_filter_In' in Hin as ((?&?)&Hin&Hopt).
      eapply option_map_inv in Hopt as (?&Hfind'&Heq); inv Heq.
      eauto.
    Qed.

    (** Induction on blocks *)

    Import Permutation.

    Local Hint Resolve InMembers_incl : datatypes.
    Local Hint Resolve <- fst_InMembers InMembers_idck InMembers_idty : datatypes.
    Local Hint Resolve -> fst_InMembers InMembers_idck InMembers_idty : datatypes.

    Lemma delast_block_Is_defined : forall x blk blk' sub st st',
        delast_block sub blk st = (blk', st') ->
        Is_defined_in x blk' ->
        Is_defined_in x blk.
    Proof.
      induction blk using block_ind2; intros * Hdl Hdef; inv Hdef; repeat inv_bind.
      - (* equation *)
        destruct eq; repeat inv_bind. constructor; auto.
      - (* reset *)
        apply mmap_values, Forall2_ignore1 in H1.
        constructor. simpl_Exists. simpl_Forall. solve_Exists.
      - (* switch *)
        simpl_Exists.
        apply mmap_values, Forall2_ignore1 in H1. simpl_Forall. repeat inv_bind.
        apply mmap_values, Forall2_ignore1 in H2. simpl_Forall.
        constructor. solve_Exists.
      - (* local *)
        apply mmap_values, Forall2_ignore1 in H3. simpl_Exists.
        apply in_app_iff in Hin as [Hin|Hin]; simpl_In.
        + exfalso. inv H0. apply In_singleton in H5; subst.
          apply H1, InMembers_app, or_intror. apply fst_InMembers. solve_In.
        + simpl_Forall. constructor. solve_Exists.
          intro contra. apply H1, InMembers_app, or_introl.
          rewrite fst_InMembers in *. solve_In.
    Qed.

    (** Central correctness lemma                                              *)
    Lemma delast_block_sem : forall blk sub Γck Γty blk' st st' bs Hi Hl Hi',
        Env.refines (@EqSt _) Hi Hi' ->
        (forall x vs, IsLast Γck x -> sem_var Hl x vs -> sem_var Hi' (rename_in_var sub x) vs) ->
        (forall x, Env.In x sub -> IsLast Γty x) ->
        (forall x, IsLast Γck x -> Env.In x sub) ->
        (forall x y, Env.find x sub = Some y -> In y (st_ids st)) ->
        incl (map fst Γck) (map fst Γty) ->
        NoDupLocals (map fst Γty) blk ->
        Forall (AtomOrGensym elab_prefs) (map fst Γty) ->
        GoodLocals elab_prefs blk ->
        Env.dom_ub Hi (map fst Γty) ->
        Env.dom_ub Hi' (map fst Γck++st_ids st) ->
        (forall x, IsLast Γck x -> Env.In x Hl) ->
        wc_block G1 Γck blk ->
        wt_block G1 Γty blk ->
        sc_vars Γck (Hi, Hl) bs ->
        sem_block_ck G1 (Hi, Hl) bs blk ->
        st_valid_after st Ids.last PS.empty ->
        delast_block sub blk st = (blk', st') ->
        sem_block_ck G2 (Hi', @Env.empty _) bs blk'.
    Proof with eauto with datatypes.
      induction blk using block_ind2;
        intros * Hvar Hvarl Hsubin1 Hsubin2 Hsubin3 Hincl Hnd2 Hat Hgood Hdom1 Hdom2 Hdom3 Hwc Hwt Hsc Hsem Hvalid Hdl;
        inv Hnd2; inv Hgood; inv Hwc; inv Hwt; inv Hsem; repeat inv_bind; simpl.
      - (* equation *)
        constructor.
        eapply rename_in_equation_sem with (H':=Hi'); eauto using sem_ref_sem_equation with lclocking.

      - (* reset *)
        econstructor; eauto using rename_in_exp_sem, sem_ref_sem_exp with lclocking.
        intros k. specialize (H15 k).
        eapply mmap_values_valid_follows, Forall2_ignore1 in H0; eauto.
        2:intros; eapply delast_block_st_valid_after; eauto.
        2:intros; eapply delast_block_st_follows; eauto.
        simpl_Forall.
        eapply H in H13; eauto using refines_mask, mask_hist_sub2.
        + intros * Hin. eapply incl_map; eauto. apply st_follows_incl; auto.
        + simpl_Forall; auto.
        + apply Env.dom_ub_map; auto.
        + eapply Env.dom_ub_map, Env.dom_ub_incl; eauto.
          apply incl_appr'. apply incl_map, st_follows_incl; auto.
        + setoid_rewrite Env.Props.P.F.map_in_iff; auto.
        + eapply sc_vars_mask in Hsc; eauto.

      - (* switch *)
        econstructor; eauto using rename_in_exp_sem, sem_ref_sem_exp with lclocking.
        + rewrite Typing.rename_in_exp_typeof; auto.
        + take (sem_exp_ck _ _ _ _ _) and eapply sc_exp in it as Hsemck; eauto.
          take (clockof _ = [_]) and rewrite it in Hsemck; apply Forall2_singl in Hsemck.
          eapply mmap_values_valid_follows, Forall2_ignore1 in H0; eauto.
          2:{ intros; destruct_conjs; repeat inv_bind; eapply mmap_st_valid; eauto.
              simpl_Forall. eapply delast_block_st_valid_after; eauto. }
          2:{ intros; destruct_conjs; repeat inv_bind; eapply mmap_st_follows; eauto.
              simpl_Forall. eapply delast_block_st_follows; eauto. }
          simpl_Forall. take (filter_hist _ _ _ _) and destruct it as (Hfilter1&Hfilter2). apply filter_hist_ffilter_hist in Hfilter1.
          do 2 esplit.
          1:{ instantiate (1:=(_, _)). split; simpl; [|reflexivity].
              take (wt_streams _ _) and rewrite H11 in it; apply Forall2_singl in it.
              eapply filter_hist_restrict_ac
                with (xs:=map fst Γ' ++ map_filter (fun '(x, a) => option_map (fun _ => rename_in_var sub x) a.(causl_last)) Γ'); eauto.
              intros * Hin Hv; simpl_In. apply in_app_iff in Hin as [Hin|Hin]; simpl_In.
              + edestruct Hsc as ((?&Hv'&Hck)&_). eapply H7; eauto with senv.
                eapply sem_var_refines in Hv'; eauto. eapply sem_var_det in Hv; eauto. rewrite <-Hv.
                eapply sem_clock_det in Hsemck; eauto.
              + unfold rename_in_var in Hv.
                assert (IsLast Γck i0) as Hlast.
                { eapply H9. econstructor; eauto. congruence. }
                edestruct Hsubin2 as (?&Hsubfind); eauto.
                destruct Hsc as (_&(?&Hv'&Hck)); eauto.
                1:{ eapply H7; eauto with senv. }
                apply Hvarl in Hv'; auto. eapply sem_var_det in Hv; eauto. rewrite <-Hv.
                eapply sem_clock_det in Hsemck; eauto.
          }
          simpl_Forall. repeat inv_bind.
          eapply mmap_values_valid_follows, Forall2_ignore1 in H17; eauto.
          2:intros; eapply delast_block_st_valid_after; eauto.
          2:intros; eapply delast_block_st_follows; eauto.
          simpl_Forall.
          eapply H with (st:=x4) (Γck:=Γ') (Hl:=t).
          apply Env.restrict_refines', refines_ffilter; eauto. all:eauto.
          * intros * Hlast Hv. rewrite Hfilter2 in Hv. apply sem_var_ffilter_inv in Hv as (?&Hv&Hfilter). rewrite Hfilter.
            eapply sem_var_restrict, sem_var_ffilter; eauto.
            apply in_app_iff, or_intror. inv Hlast. solve_In; simpl.
            destruct (causl_last e0); simpl in *; try congruence.
          * intros * Hin. eapply incl_map; eauto. apply st_follows_incl; etransitivity; eauto.
          * intros ? Hin; simpl_In.
            edestruct H7 as (Hin'&_); eauto with senv. inv Hin'.
            take (In _ Γck) and eapply In_InMembers, fst_InMembers, Hincl in it.
            solve_In.
          * simpl_Forall; auto.
          * apply Env.restrict_dom_ub', Env.dom_ub_map; auto.
          * eapply Env.dom_ub_incl, Env.restrict_dom_ub. apply incl_appr'.
            intros ? Hin. simpl_In.
            unfold rename_in_var. edestruct Hsubin2 as (?&Hfind).
            eapply H9; econstructor; eauto. congruence.
            rewrite Hfind. apply Hsubin3 in Hfind. simpl; auto.
            eapply incl_map; eauto. apply st_follows_incl; etransitivity; eauto.
          * intros. rewrite Hfilter2. setoid_rewrite Env.Props.P.F.map_in_iff. eauto.
          * eapply sc_vars_refines, sc_vars_restrict, sc_vars_ffilter; eauto.
            -- eapply Env.incl_restrict_refines; auto using EqStrel_Reflexive. apply incl_appl, incl_refl.
            -- rewrite Hfilter2; reflexivity.
            -- reflexivity.
            -- simpl_Forall; simpl_In.
               edestruct H7 as (?&Hbase); eauto with senv. rewrite Hbase. constructor.
          * take (sem_block_ck _ _ _ _) and eapply sem_block_refines, sem_block_restrict, sem_block_refines in it; eauto.
            apply Env.incl_restrict_refines; auto using EqStrel_Reflexive. solve_incl_app.
            unfold wc_env. simpl_Forall; simpl_In.
            edestruct H7 as (?&Hbase); eauto with senv. rewrite Hbase. constructor.

      - (* local *)
        assert (forall y, Env.In y (Env.from_list (map fst x)) <-> IsLast (senv_of_locs locs) y) as Hsubin4.
        { intros *. rewrite Env.In_from_list.
          eapply fresh_idents_InMembers in H0. erewrite <-H0, fst_InMembers.
          split; intros * Hin.
          - simpl_In. econstructor; solve_In. simpl. congruence.
          - inv Hin. simpl_In. destruct o as [(?&?)|]; simpl in *; try congruence.
            solve_In. auto. }

        assert (NoDupMembers (map (fun '(x3, lx, _) => (lx, or_default (Streams.const absent) (Env.find x3 Hl'))) x)) as Hndl1.
        { eapply fresh_idents_NoDup in H0; eauto. clear - H0.
          rewrite fst_NoDupMembers, map_map in H0. erewrite fst_NoDupMembers, map_map, map_ext; eauto.
          intros; destruct_conjs; auto. }
        assert (forall x3,
                   InMembers x3 (map (fun '(x4, lx, _) => (lx, or_default (Streams.const absent) (Env.find x4 Hl'))) x) ->
                   ~ Env.In x3 (Env.union (Env.restrict H' (map fst locs)) Hi')) as Hndl2.
        { intros * Hinm. rewrite fst_InMembers in Hinm. simpl_In.
          assert (Hf:=H0). eapply fresh_idents_prefixed in H0. simpl_Forall; subst.
          rewrite Env.union_In, Env.restrict_In_iff, not_or'. split.
          - intros (_&Hin2); simpl_In.
            simpl_Forall. apply contradict_AtomOrGensym in H3; eauto using last_not_in_elab_prefs.
          - intros Hin. eapply Env.dom_ub_use, in_app_iff in Hin as [Hin|]; eauto.
            + apply Hincl in Hin. simpl_In. simpl_Forall.
              apply contradict_AtomOrGensym in Hat; eauto using last_not_in_elab_prefs.
            + eapply fresh_idents_nIn_ids in Hf; eauto. simpl_Forall. eauto.
        }
        assert (forall x3 : Env.key, Env.In x3 (Env.restrict H' (map fst locs)) -> ~ Env.In x3 Hi') as Hndl3.
        { intros * Hin contra. apply Env.restrict_In in Hin.
          eapply Env.dom_ub_use, in_app_iff in contra as [|]; eauto.
          - eapply H5; eauto using in_or_app. now apply fst_InMembers.
          - eapply st_valid_prefixed in Hvalid. simpl_Forall; subst.
            apply contradict_AtomOrGensym in H3; eauto using last_not_in_elab_prefs. }

        remember (Env.adds' (map (fun '(x, lx, _) => (lx, or_default (Streams.const absent) (Env.find x Hl'))) x)
                            (Env.union (Env.restrict H' (map fst locs)) Hi')) as Hi2'.
        assert (Env.refines (@EqSt _) H' Hi2') as Hvar'.
        { intros ?? Hv.
          assert (sem_var Hi2' x2 v) as Hv'. 2:inv Hv'; eauto.
          subst.
          rewrite sem_var_disj_adds', sem_var_disj_union; eauto. right.
          destruct (in_dec ident_eq_dec x2 (map fst locs)).
          - left. eapply sem_var_restrict; eauto. econstructor; eauto. reflexivity.
          - right. eapply sem_var_refines; eauto.
            eapply H17; eauto. 2:now rewrite fst_InMembers.
            econstructor; eauto. reflexivity.
        }
        assert (forall y vs,
                   IsLast (Γck ++ senv_of_locs locs) y ->
                   sem_var Hl' y vs ->
                   sem_var Hi2' (rename_in_var (Env.union sub (Env.from_list (map fst x))) y) vs) as Hvarl'.
        { intros * Hin Hv. subst Hi2'.
          rewrite sem_var_disj_adds', sem_var_disj_union; eauto.
          apply IsLast_app in Hin as [Hin|Hin]; simpl_In; subst.
          - do 2 right. rewrite not_in_union_rename2.
            2:{ intros contra. rewrite Env.In_from_list, fst_InMembers in contra. simpl_In.
                eapply fresh_idents_In' in H0; eauto. simpl_In.
                eapply H5; eauto using In_InMembers, in_or_app. apply Hincl. inv Hin. solve_In. }
            eapply Hvarl; eauto. eapply sem_var_refines'; eauto using Env.dom_lb_use.
          - left. inv Hin. simpl_In. destruct o as [(?&?)|]; simpl in *; try congruence.
            eapply fresh_idents_In_rename in H0. 3:solve_In; simpl; eauto.
            2:{ apply nodupmembers_map_filter; auto.
                intros; destruct_conjs; destruct o as [(?&?)|]; simpl; auto. }
            erewrite not_in_union_rename1.
            2:{ intro contra. apply Hsubin1 in contra. inv contra.
                eapply H5; eauto using In_InMembers, in_or_app. solve_In. }
            inv Hv. unfold Env.MapsTo in *.
            solve_In. take (Env.find _ Hl' = _) and rewrite it; reflexivity.
        }
        assert (forall x, Env.In x (Env.restrict H' (map fst locs)) <-> In x (map fst locs)) as Hdom1'.
        { intros. rewrite Env.restrict_In_iff. symmetry.
          split; [intros|intros (?&?)]; eauto.
          split; auto.
          eapply Env.dom_use; eauto. apply in_or_app; auto.
        }
        assert (Env.dom Hi2'
                        (map fst (Env.elements Hi') ++
                             map fst
                             (map (fun '(x2, (ty, ck, cx, _)) => (x2, (ty, ck, cx, @None (exp * ident)))) locs ++
                                  map (fun '(_, lx, (ty, ck, _)) => (lx, (ty, ck, 1%positive, None))) x))
               ) as Hdom2'.
        { subst. apply Env.dom_intro; intros.
          rewrite Env.In_adds_spec', Env.union_In, map_app, 2 in_app_iff, Env.In_Members with (m:=Hi'), 2 fst_InMembers.
          rewrite or_comm, (or_comm (Env.In _ _)), or_assoc. apply or_iff_compat_l.
          repeat rewrite map_map. erewrite map_ext with (l:=x). apply or_iff_compat_r.
          erewrite Hdom1', map_ext with (l:=locs). reflexivity.
          1,2:intros; destruct_conjs; auto. }

        eapply Slocal with (H':=Hi2') (Hl':=Env.empty _).
        6:apply Forall_app; split.
        + subst. intros * Hv' Hnin.
          eapply sem_var_adds' in Hv' as [(?&?&?)|Hv']; auto. 2:apply sem_var_union in Hv' as [Hv'|Hv']; auto.
          * exfalso. eapply Hnin, InMembers_app, or_intror, fst_InMembers.
            solve_In.
          * exfalso. apply sem_var_restrict_inv in Hv' as (?&Hin).
            eapply Hnin, InMembers_app, or_introl, fst_InMembers.
            solve_In.
        + assumption.
        + reflexivity.
        + intros * Hin. apply in_app_iff in Hin as [|]; simpl_In.
        + take (sc_vars (senv_of_locs _) _ _) and destruct it as (Hsc1&Hsc2).
          split; intros * Hck; inv Hck; simpl_In; rewrite in_app_iff in *;
            destruct Hin as [Hin|Hin]; simpl_In;
            try (intros Hca; inv Hca; simpl_In;
                 take (In _ (_ ++ _)) and apply in_app_iff in it as [|]; simpl_In);
            try congruence.
          * edestruct Hsc1 as (?&?&?); eauto. 1:econstructor; solve_In; auto. simpl in *.
            eauto using sem_var_refines, sem_clock_refines.
          * eapply fresh_idents_In'_rename in H0 as (?&?); eauto.
            2:{ apply nodupmembers_map_filter; auto.
                intros; destruct_conjs; destruct o as [(?&?)|]; simpl; auto. }
            simpl_In.
            edestruct Hsc2 as (?&?&?). 1,2:econstructor; solve_In; simpl; eauto. congruence.
            do 2 esplit; eauto using sem_clock_refines.
            eapply Hvarl' in H0. rewrite not_in_union_rename1 in H0; eauto.
            -- intro contra. apply Hsubin1 in contra. inv contra.
               eapply H5; eauto using In_InMembers, in_or_app. solve_In.
            -- apply IsLast_app; right. econstructor. solve_In. simpl; congruence.
        + simpl_Forall. constructor.
          eapply fresh_idents_In'_rename in H0 as (?&?); subst; [| |eauto]. simpl_In.
          2:{ apply nodupmembers_map_filter; auto.
              intros; destruct_conjs; destruct o as [(?&?)|]; simpl; auto. }
          edestruct H21 as (vs0&vs1&vs&He&Hv&Hfby&Hvl); eauto.
          eapply Seq with (ss:=[[vs]]); simpl; repeat constructor.
          * eapply Sfby with (s0ss:=[[vs0]]) (sss:=[[vs1]]); simpl.
            1-3:repeat constructor; eauto using sem_var_refines.
            eapply rename_in_exp_sem; eauto using sem_ref_sem_exp.
            simpl_Forall; eauto with lclocking.
          * erewrite <-not_in_union_rename1 with (sub:=sub).
            2:{ intro contra. apply Hsubin1 in contra. inv contra.
                eapply H5; eauto using In_InMembers, in_or_app. solve_In. }
            eapply Hvarl'; eauto.
            apply IsLast_app, or_intror. econstructor; solve_In. simpl; congruence.
        + eapply mmap_values_valid_follows, Forall2_ignore1 in H1; eauto.
          2:eapply fresh_idents_st_valid_after; eauto.
          2:intros; eapply delast_block_st_valid_after; eauto.
          2:intros; eapply delast_block_st_follows; eauto.
          simpl_Forall. eapply H with (Γck:=Γck ++ senv_of_locs locs); eauto.
          * intros * Hin. rewrite IsLast_app. apply Env.union_In in Hin as [|Hin]; eauto.
            right. apply Hsubin4; auto.
          * intros * Hin. apply Env.union_In. apply IsLast_app in Hin as [|]; eauto.
            right. apply Hsubin4; auto.
          * intros * Hfind. apply Env.union_find4 in Hfind as [Hfind|Hfind].
            -- eapply incl_map; eauto.
               apply st_follows_incl; etransitivity; eauto using fresh_idents_st_follows.
            -- eapply incl_map; eauto. eapply st_follows_incl; eauto.
               apply Env.from_list_find_In in Hfind. simpl_In.
               apply fresh_idents_In_ids in H0. simpl_Forall. solve_In.
          * rewrite 2 map_app. apply incl_appl'; auto.
          * rewrite map_app, map_fst_senv_of_locs; auto.
          * rewrite map_app, map_fst_senv_of_locs; auto. apply Forall_app; split; simpl_Forall; auto.
          * rewrite map_app, map_fst_senv_of_locs. eapply local_hist_dom_ub in Hdom1; eauto.
          * eapply local_hist_dom_ub in Hdom2'; [|eauto].
            apply Env.dom_ub_intro; intros.
            eapply Env.dom_ub_use in Hdom2'; eauto. rewrite map_app, map_fst_senv_of_locs.
            rewrite map_app in Hdom2'. repeat rewrite in_app_iff in *. destruct Hdom2' as [[|]|[|]]; auto.
            -- right. eapply incl_map; eauto.
               apply st_follows_incl. etransitivity; eauto using fresh_idents_st_follows.
            -- left. right. solve_In.
            -- right. simpl_In. eapply fresh_idents_In_ids in H0. simpl_Forall.
               eapply incl_map; eauto. apply st_follows_incl; eauto using fresh_idents_st_follows.
          * intros * Hil. apply IsLast_app in Hil as [Hil|Hil].
            -- eapply Env.In_refines; eauto.
            -- inv Hil. simpl_In. destruct o as [(?&?)|]; simpl in *; try congruence.
               edestruct H21 as (?&?&?&?&?&?&?); eauto using sem_var_In.
          * eapply sc_vars_app; eauto using sc_vars_refines, local_hist_dom_ub_refines.
            intros * Hin. rewrite InMembers_senv_of_locs.
            intro contra. eapply H5; eauto. apply Hincl, fst_InMembers; auto.
    Qed.

    Lemma delast_node_sem : forall f n ins outs,
        wt_global (Global G1.(enums) (n::G1.(nodes))) ->
        wc_global (Global G1.(enums) (n::G1.(nodes))) ->
        Ordered_nodes (Global G1.(enums) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(enums) ((delast_node n)::G2.(nodes))) ->
        sem_node_ck (Global G1.(enums) (n::G1.(nodes))) f ins outs ->
        sem_node_ck (Global G2.(enums) ((delast_node n)::G2.(nodes))) f ins outs.
    Proof with eauto.
      intros * (_&Hwt) Hwc Hord1 Hord2 Hsem.

      inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
      - erewrite find_node_now in Hfind; eauto. inv Hfind.
        (*The semantics of equations can be given according to G only *)
        eapply sem_block_ck_cons in H3; eauto. rename H3 into Hblksem.
        2:{ inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }

        replace {| enums := enums G1; nodes := nodes G1 |} with G1 in Hblksem by (destruct G1; auto).
        pose proof (n_nodup n0) as (Hnd1&Hnd2).
        pose proof (n_good n0) as (Hgood1&Hgood2&_).
        inv Hwc. destruct H4 as (Hwc&_); simpl in Hwc.
        inv Hwt. destruct H4 as (Hwt&_); simpl in Hwt.
        destruct H5 as (Hdom1&Hsc1).
        eapply delast_block_sem in Hblksem; eauto. 16:apply surjective_pairing.
        eapply Snode; eauto.
        + erewrite find_node_now; eauto.
        + eauto.
        + eauto.
        + apply sem_block_ck_cons'; simpl...
          2:{ eapply find_node_not_Is_node_in in Hord2.
            2:erewrite find_node_now; eauto. eauto. }
          destruct G2; eauto.
        + simpl. constructor; simpl; auto.
        + reflexivity.
        + intros * _ Hv. inv Hv. apply Env.Props.P.F.empty_mapsto_iff in H3 as [].
        + intros * Hin. apply Env.Props.P.F.empty_in_iff in Hin as [].
        + intros * Hl. apply senv_of_inout_NoLast in Hl as [].
        + intros * Hfind. rewrite Env.gempty in Hfind. congruence.
        + reflexivity.
        + rewrite map_fst_senv_of_inout. apply n_nodup.
        + rewrite map_fst_senv_of_inout. auto.
        + apply Env.dom_dom_ub; auto.
        + unfold st_ids. rewrite init_st_anns, app_nil_r.
          apply Env.dom_dom_ub; auto.
        + intros * Hl. apply senv_of_inout_NoLast in Hl as [].
        + destruct Hwc as (_&_&Hwc). destruct G1; auto.
        + destruct Hwt as (_&_&_&Hwt). destruct G1; auto.
        + eapply init_st_valid; eauto using last_not_in_elab_prefs.
          intros ? Hin. apply PSF.empty_iff in Hin as [].
      - erewrite find_node_other in Hfind; eauto.
        eapply sem_node_ck_cons'...
        destruct G2; apply HGref.
        econstructor...
        destruct G1; eapply sem_block_ck_cons...
        eapply find_node_later_not_Is_node_in in Hord1...
    Qed.

  End delast_node_sem.

  Fact wc_global_Ordered_nodes {PSyn prefs} : forall (G: @global PSyn prefs),
      wc_global G ->
      Ordered_nodes G.
  Proof.
    intros G Hwt.
    apply wl_global_Ordered_nodes; auto with lclocking.
  Qed.

  Lemma delast_global_refines : forall G,
      wt_global G ->
      wc_global G ->
      global_sem_refines G (delast_global G).
  Proof with eauto using wc_global_Ordered_nodes.
    intros (enms&nds) (Henums&Hwt).
    induction nds; intros * Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      eapply Clocking.delast_global_wc, wc_global_Ordered_nodes in Hwc' ;
        unfold delast_global in Hwc'; simpl in Hwc'.
      apply global_sem_ref_cons with (f:=n_name a)...
      + inv Hwt. inv Hwc. eapply IHnds...
      + intros ins outs Hsem; simpl in *.
        change enms with ((Global enms (map delast_node nds)).(enums)).
        eapply delast_node_sem with (G1:=Global enms nds)...
        1-3:inv Hwt; inv Hwc...
        destruct H1. constructor... constructor...
  Qed.

  Theorem delast_global_sem : forall G f ins outs,
      wt_global G ->
      wc_global G ->
      sem_node_ck G f ins outs ->
      sem_node_ck (delast_global G) f ins outs.
  Proof.
    intros.
    eapply delast_global_refines in H; eauto.
    specialize (H f ins outs); auto.
  Qed.

End DLCORRECTNESS.

Module DLCorrectnessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (LCA : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Ty : LTYPING Ids Op OpAux Cks Senv Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Lord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
       (LClockSem : LCLOCKSEMANTICS Ids Op OpAux Cks Senv Syn Ty Clo LCA Lord CStr Sem)
       (DL  : DELAST Ids Op OpAux Cks Senv Syn)
       <: DLCORRECTNESS Ids Op OpAux Cks CStr Senv Syn LCA Ty Clo Lord Sem LClockSem DL.
  Include DLCORRECTNESS Ids Op OpAux Cks CStr Senv Syn LCA Ty Clo Lord Sem LClockSem DL.
End DLCorrectnessFun.
