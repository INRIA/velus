From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LCausality Lustre.LSemantics Lustre.LClockSemantics.
From Velus Require Import Lustre.DeLast.DeLast Lustre.DeLast.DLTyping Lustre.DeLast.DLClocking.

Module Type DLCORRECTNESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (LCA        : LCAUSALITY Ids Op OpAux Cks Syn)
       (Import Ty : LTYPING Ids Op OpAux Cks Syn)
       (Import Cl : LCLOCKING Ids Op OpAux Cks Syn)
       (Import Ord : LORDERED Ids Op OpAux Cks Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Cks Syn Ord CStr)
       (Import LCS : LCLOCKSEMANTICS Ids Op OpAux Cks Syn Ty Cl LCA Ord CStr Sem)
       (Import DL  : DELAST Ids Op OpAux Cks Syn).

  Module Typing := DLTypingFun Ids Op OpAux Cks Syn Ty DL.
  Module Clocking := DLClockingFun Ids Op OpAux Cks Syn Cl DL.

  Section rename.
    Variable sub : Env.t ident.

    Import List.

    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Section rename_in_exp.

      Variable Γ Γl : list ident.
      Variable H Hl H' : CStr.history.

      Hypothesis Hsub : forall x vs,
          In x Γl ->
          sem_var Hl x vs ->
          sem_var H' (rename_in_var sub x) vs.

      Hypothesis Hnsub : Env.refines (@EqSt _) H H'.

      Lemma rename_in_exp_sem : forall bs e vss,
          wx_exp Γ Γl e ->
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
          wx_equation Γ Γl eq ->
          sem_equation_ck G (H, Hl) bs eq ->
          sem_equation_ck G (H', @Env.empty _) bs (rename_in_equation sub eq).
      Proof.
        intros * Hwx Hsem. inv Hsem. inv Hwx. simpl in *.
        eapply Seq with (ss0:=ss); simpl_Forall; eauto using sem_var_refines, rename_in_exp_sem.
      Qed.

      Lemma rename_in_sc_vars : forall bs Γ Γl',
          incl (map fst Γl') Γl ->
          sc_vars Γ Γl' (H, Hl) bs ->
          sc_vars (Γ++List.map (fun '(x, ck) => (rename_in_var sub x, ck)) Γl') [] (H', @Env.empty _) bs.
      Proof.
        intros * Hincl (Hsc1&Hsc2). split; auto.
        apply Forall_app; split.
        - simpl_Forall. do 2 esplit; eauto using sem_var_refines, sem_clock_refines.
        - simpl_Forall.
          do 2 esplit; eauto using sem_clock_refines. eapply Hsub; eauto.
          eapply Hincl. solve_In.
      Qed.

    End rename_in_exp.

    Fact mask_hist_sub2 Γl : forall k r H H',
      (forall x vs, In x Γl -> sem_var H x vs -> sem_var H' (rename_in_var sub x) vs) ->
      forall x vs, In x Γl -> sem_var (CStr.mask_hist k r H) x vs -> sem_var (CStr.mask_hist k r H') (rename_in_var sub x) vs.
    Proof.
      intros * Hsub * ? Hv.
      eapply sem_var_mask_inv in Hv as (?&Hv&Heq).
      eapply Hsub, sem_var_mask in Hv; eauto. rewrite Heq; eauto.
    Qed.

    Fact filter_hist_sub2 Γl : forall k r H H',
      (forall x vs, In x Γl -> sem_var H x vs -> sem_var H' (rename_in_var sub x) vs) ->
      forall x vs, In x Γl -> sem_var (CStr.filter_hist k r H) x vs -> sem_var (CStr.filter_hist k r H') (rename_in_var sub x) vs.
    Proof.
      intros * Hsub * ? Hv.
      eapply sem_var_filter_inv in Hv as (?&Hv&Heq).
      eapply Hsub, sem_var_filter in Hv; eauto. rewrite Heq; eauto.
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

    Lemma sem_var_union : forall Hi1 Hi2 x vs,
        sem_var (Env.union Hi1 Hi2) x vs ->
        sem_var Hi1 x vs \/ sem_var Hi2 x vs.
    Proof.
      intros * Hv. inv Hv.
      eapply Env.union_find4 in H0 as [Hfind|Hfind]; eauto using sem_var.
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
    Lemma delast_block_sem (* vars *) : forall blk sub Γ Γl (* vars' *) blk' st st' bs Hi Hl Hi',
        Env.refines (@EqSt _) Hi Hi' ->
        (forall x vs, In x Γl -> sem_var Hl x vs -> sem_var Hi' (rename_in_var sub x) vs) ->
        (forall x, Env.In x sub -> In x Γl) ->
        NoDupLocals (Γ++Γl) blk ->
        Forall (AtomOrGensym elab_prefs) Γ ->
        GoodLocals elab_prefs blk ->
        Env.dom_ub Hi' (Γ++st_ids st) -> (* faux *)
        Env.dom_lb Hl Γl ->
        wx_block Γ Γl blk ->
        sem_block_ck G1 (Hi, Hl) bs blk ->
        st_valid_after st Ids.last PS.empty ->
        delast_block sub blk st = (blk', st') ->
        sem_block_ck G2 (Hi', @Env.empty _) bs blk'.
    Proof with eauto with datatypes.
      induction blk using block_ind2;
        intros * Hvar Hvarl Hsubin Hnd2 Hat Hgood Hdom1 Hdom2 Hwx Hsem Hvalid Hdl;
        inv Hnd2; inv Hgood; inv Hwx; inv Hsem; repeat inv_bind; simpl.
      - (* equation *)
        constructor.
        eapply rename_in_equation_sem with (H':=Hi'); eauto using sem_ref_sem_equation.
      - (* reset *)
        econstructor; eauto using rename_in_exp_sem, sem_ref_sem_exp.
        intros k. specialize (H11 k).
        eapply mmap_values_valid_follows, Forall2_ignore1 in H0; eauto.
        2:intros; eapply delast_block_st_valid_after; eauto.
        2:intros; eapply delast_block_st_follows; eauto.
        simpl_Forall.
        eapply H; eauto using refines_mask, mask_hist_sub2.
        + eapply Env.dom_ub_map, Env.dom_ub_incl; eauto.
          apply incl_appr'. apply incl_map, st_follows_incl; auto.
        + apply Env.dom_lb_map; auto.

      - (* switch *)
        econstructor; eauto using rename_in_exp_sem, sem_ref_sem_exp.
        + rewrite Typing.rename_in_exp_typeof; auto.
        + eapply mmap_values_valid_follows, Forall2_ignore1 in H0; eauto.
          2:{ intros; destruct_conjs; repeat inv_bind; eapply mmap_st_valid; eauto.
              simpl_Forall. eapply delast_block_st_valid_after; eauto. }
          2:{ intros; destruct_conjs; repeat inv_bind; eapply mmap_st_follows; eauto.
              simpl_Forall. eapply delast_block_st_follows; eauto. }
          simpl_Forall. repeat inv_bind.
          eapply mmap_values_valid_follows, Forall2_ignore1 in H10; eauto.
          2:intros; eapply delast_block_st_valid_after; eauto.
          2:intros; eapply delast_block_st_follows; eauto.
          simpl_Forall.
          eapply H; eauto using refines_filter, filter_hist_sub2.
          * eapply Env.dom_ub_map, Env.dom_ub_incl; eauto.
            apply incl_appr'. apply incl_map, st_follows_incl; auto. etransitivity; eauto.
          * apply Env.dom_lb_map; auto.
        + intros ?? Hdef Hf; simpl in *.
          assert (sem_var Hi x0 vs) as Hv'.
          { eapply delast_block_Is_defined with (blk:=Bswitch ec branches) in Hdef. 2:repeat inv_bind; eauto.
            eapply sem_block_sem_var in Hdef as (?&Hv').
            2:{ eapply sem_block_ck_sem_block; econstructor; eauto. }
            assert (x1 ≡ vs) as Heq; [|rewrite <-Heq; auto].
            eapply sem_var_det. eapply sem_var_refines; eauto.
            econstructor; eauto. reflexivity. }
          inv Hv'. take (vs ≡ _) and rewrite it.
          take (slower_subhist _ _ _) and eapply it; eauto.
          eapply delast_block_Is_defined; eauto. repeat inv_bind; eauto.

      - (* local *)
        assert (forall y, Env.In y (Env.from_list (map fst x)) <->
                   InMembers y (map_filter (fun '(x, (ty, ck, _, o)) => option_map (fun '(e, _) => (x, (ty, ck, e))) o) locs)) as Hsubin'.
      { intros. rewrite Env.In_from_list.
        eapply fresh_idents_InMembers in H0. erewrite H0, 2 fst_InMembers.
        split; intros; solve_In. }

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
          - intros Hin. eapply Env.dom_ub_use, in_app_iff in Hin as [|]; eauto.
            + simpl_Forall. apply contradict_AtomOrGensym in Hat; eauto using last_not_in_elab_prefs.
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
            eapply H12; eauto. 2:now rewrite fst_InMembers.
            econstructor; eauto. reflexivity.
        }
        assert (forall y vs,
                   In y envl' ->
                   sem_var Hl' y vs ->
                   sem_var Hi2' (rename_in_var (Env.union sub (Env.from_list (map fst x))) y) vs) as Hvarl'.
        { intros * Hin Hv. subst envl' Hi2'.
          rewrite sem_var_disj_adds', sem_var_disj_union; eauto.
          apply in_app_iff in Hin as [Hin|]; simpl_In; subst.
          - do 2 right. rewrite not_in_union_rename2.
            2:{ intros contra. rewrite Env.In_from_list, fst_InMembers in contra. simpl_In.
                eapply fresh_idents_In' in H0; eauto. simpl_In.
                eapply H5; eauto using In_InMembers, in_or_app. }
            eapply Hvarl; eauto. eapply sem_var_refines'; eauto using Env.dom_lb_use.
          - left. eapply fresh_idents_In_rename in H0. 3:solve_In; simpl; eauto.
            2:{ apply nodupmembers_map_filter; auto.
                intros; destruct_conjs; destruct o as [(?&?)|]; simpl; auto. }
            erewrite not_in_union_rename1.
            2:{ intro contra. eapply H5; eauto using In_InMembers, in_or_app. }
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

        eapply Slocal with (H'0:=Hi2') (Hl'0:=Env.empty _).
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
        + eapply rename_in_sc_vars in H17 as (Hsc&_). 2,3:eauto.
          2:{ subst envl'. apply incl_appr. intros ??. solve_In. }
          rewrite map_filter_nil.
          2:{ simpl_Forall. apply in_app_iff in H7 as [|]; simpl_In; auto. }
          split; auto. apply Forall_app in Hsc as (Hsc1&Hsc2).
          simpl_app. apply Forall_app; split; simpl_Forall. eauto.
          eapply fresh_idents_In'_rename in H0 as (?&?); eauto; subst.
          2:{ apply nodupmembers_map_filter; auto.
              intros; destruct_conjs; destruct o as [(?&?)|]; simpl; auto. }
          simpl_In.
          eapply Forall_forall in Hsc2; [|solve_In; simpl; eauto]; simpl in *.
          destruct_conjs. do 2 esplit; eauto.
          rewrite not_in_union_rename1 in H0; eauto.
          intro contra. eapply H5; eauto using In_InMembers, in_or_app.
        + simpl_Forall. constructor.
          eapply fresh_idents_In'_rename in H0 as (?&?); subst; [| |eauto]. simpl_In.
          2:{ apply nodupmembers_map_filter; auto.
              intros; destruct_conjs; destruct o as [(?&?)|]; simpl; auto. }
          edestruct H16 as (vs0&vs1&vs&He&Hv&Hfby&Hvl); eauto.
          eapply Seq with (ss:=[[vs]]); simpl; repeat constructor.
          * eapply Sfby with (s0ss:=[[vs0]]) (sss:=[[vs1]]); simpl.
            1-3:repeat constructor; eauto using sem_var_refines.
            eapply rename_in_exp_sem with (Γl:=Γl++_); eauto using sem_ref_sem_exp.
            simpl_Forall; eauto using sem_var_refines.
          * erewrite <-not_in_union_rename1 with (sub:=sub).
            2:{ intro contra. eapply H5; eauto using In_InMembers, in_or_app. }
            eapply Hvarl'; eauto.
            subst envl'. apply in_app_iff, or_intror. solve_In.
        + eapply mmap_values_valid_follows, Forall2_ignore1 in H1; eauto.
          2:eapply fresh_idents_st_valid_after; eauto.
          2:intros; eapply delast_block_st_valid_after; eauto.
          2:intros; eapply delast_block_st_follows; eauto.
          simpl_Forall. eapply H with (Γ:=env'); eauto.
          * intros * Hin. subst envl'. rewrite in_app_iff. apply Env.union_In in Hin as [|Hin]; eauto.
            right.
            rewrite Hsubin' in Hin. rewrite fst_InMembers in Hin. solve_In.
          * subst env' envl'. eapply NoDupLocals_incl; [|eauto].
            simpl_app. apply incl_appr', incl_app; [apply incl_appr, incl_refl|].
            apply incl_appr'. intros ??. solve_In.
          * subst env'. apply Forall_app; split; auto.
            simpl_Forall; auto.
          * eapply local_hist_dom_ub in Hdom2'; [|eauto].
            apply Env.dom_ub_intro; intros.
            eapply Env.dom_ub_use in Hdom2'; eauto. subst env'. simpl_app.
            repeat rewrite in_app_iff in *. destruct Hdom2' as [|[|[|]]]; auto.
            -- right. right. eapply incl_map; eauto.
               apply st_follows_incl. etransitivity; eauto using fresh_idents_st_follows.
            -- right. left. solve_In.
            -- right. right. simpl_In. eapply fresh_idents_In_ids in H0. simpl_Forall.
               eapply incl_map; eauto. apply st_follows_incl; eauto using fresh_idents_st_follows.
          * subst envl'. apply Env.dom_lb_app'; eauto using Env.dom_lb_refines.
            apply Env.dom_lb_intro. intros. simpl_In; subst.
            edestruct H16 as (?&?&?&?&?&?&?); eauto using sem_var_In.
    Qed.

    Lemma delast_node_sem : forall f n ins outs,
        wc_global (Global G1.(enums) (n::G1.(nodes))) ->
        Ordered_nodes (Global G1.(enums) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(enums) ((delast_node n)::G2.(nodes))) ->
        sem_node_ck (Global G1.(enums) (n::G1.(nodes))) f ins outs ->
        sem_node_ck (Global G2.(enums) ((delast_node n)::G2.(nodes))) f ins outs.
    Proof with eauto.
      intros * Hwc Hord1 Hord2 Hsem.

      inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
      - erewrite find_node_now in Hfind; eauto. inv Hfind.
        (*The semantics of equations can be given according to G only *)
        eapply sem_block_ck_cons in H3; eauto. rename H3 into Hblksem.
        2:{ inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }

        replace {| enums := enums G1; nodes := nodes G1 |} with G1 in Hblksem by (destruct G1; auto).
        pose proof (n_nodup n0) as (Hnd1&Hnd2).
        pose proof (n_good n0) as (Hgood1&Hgood2&_).
        inv Hwc. destruct H4 as (Hwc&_); simpl in Hwc.
        destruct H5 as (Hdom1&Hsc1).
        eapply delast_block_sem with (Γl:=[]) in Hblksem; eauto. 10:apply surjective_pairing.
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
        + rewrite app_nil_r. apply n_nodup.
        + unfold st_ids. rewrite init_st_anns, app_nil_r.
          rewrite map_fst_idty in Hdom1. apply Env.dom_dom_ub; auto.
        + apply Env.dom_lb_nil.
        + destruct Hwc as (_&_&Hwc). apply wc_block_wx_block in Hwc.
          now rewrite map_fst_idck, map_fst_idty in Hwc.
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
      wc_global G ->
      global_sem_refines G (delast_global G).
  Proof with eauto using wc_global_Ordered_nodes.
    intros (enms&nds).
    induction nds; intros * Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      eapply Clocking.delast_global_wc, wc_global_Ordered_nodes in Hwc' ;
        unfold delast_global in Hwc'; simpl in Hwc'.
      apply global_sem_ref_cons with (f:=n_name a)...
      + inv Hwc. eapply IHnds...
      + intros ins outs Hsem; simpl in *.
        change enms with ((Global enms (map delast_node nds)).(enums)).
        eapply delast_node_sem with (G1:=Global enms nds)...
        1,2:inv Hwc...
  Qed.

  Theorem delast_global_sem : forall G f ins outs,
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
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (LCA : LCAUSALITY Ids Op OpAux Cks Syn)
       (Ty : LTYPING Ids Op OpAux Cks Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (Lord : LORDERED Ids Op OpAux Cks Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Syn Lord CStr)
       (LClockSem : LCLOCKSEMANTICS Ids Op OpAux Cks Syn Ty Clo LCA Lord CStr Sem)
       (DL  : DELAST Ids Op OpAux Cks Syn)
       <: DLCORRECTNESS Ids Op OpAux Cks CStr Syn LCA Ty Clo Lord Sem LClockSem DL.
  Include DLCORRECTNESS Ids Op OpAux Cks CStr Syn LCA Ty Clo Lord Sem LClockSem DL.
End DLCorrectnessFun.
