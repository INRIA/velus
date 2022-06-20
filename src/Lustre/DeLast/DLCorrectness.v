From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LSemantics Lustre.LClockedSemantics.
From Velus Require Import Lustre.DeLast.DeLast Lustre.DeLast.DLTyping Lustre.DeLast.DLClocking.

Module Type DLCORRECTNESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Ty : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import Cl : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import Ord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (Import LCS : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Cl Ord CStr Sem)
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

      Hypothesis Hnsub : FEnv.refines (@EqSt _) H H'.

      Lemma rename_in_exp_sem : forall bs e vss,
          wx_exp Γ e ->
          sem_exp_ck G (H, Hl) bs e vss ->
          sem_exp_ck G (H', FEnv.empty _) bs (rename_in_exp sub e) vss.
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
          sem_equation_ck G (H', @FEnv.empty _) bs (rename_in_equation sub eq).
      Proof.
        intros * Hwx Hsem. inv Hsem. inv Hwx. simpl in *.
        eapply Seq with (ss:=ss); simpl_Forall; eauto using sem_var_refines, rename_in_exp_sem.
      Qed.

      Corollary rename_in_transitions_sem : forall bs trans default stres,
          Forall (fun '(e, _) => wx_exp Γ e) trans ->
          sem_transitions_ck G (H, Hl) bs trans default stres ->
          sem_transitions_ck G (H', @FEnv.empty _) bs (map (fun '(e, k) => (rename_in_exp sub e, k)) trans) default stres.
      Proof.
        induction trans; intros * Hwx Hsem; inv Hwx; inv Hsem;
          econstructor; eauto using rename_in_exp_sem.
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

    Fact select_hist_sub2 Γ : forall e k r H H',
      (forall x vs, IsLast Γ x -> sem_var H x vs -> sem_var H' (rename_in_var sub x) vs) ->
      forall x vs, IsLast Γ x -> sem_var (CStr.fselect_hist e k r H) x vs -> sem_var (CStr.fselect_hist e k r H') (rename_in_var sub x) vs.
    Proof.
      intros * Hsub * ? Hv.
      eapply sem_var_fselect_inv in Hv as (?&Hv&Heq).
      eapply Hsub, sem_var_fselect in Hv; eauto. rewrite Heq; eauto.
    Qed.

  End rename.

  Import Fresh Facts Tactics.
  Import List.

  Section delast_node_sem.
    Variable G1 : @global (fun _ => True) elab_prefs.
    Variable G2 : @global nolast_block last_prefs.

    Hypothesis HGref : global_sem_refines G1 G2.
    Hypothesis HwG1 : wc_global G1.

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

    Lemma delast_scope_Is_defined {A} f_dl f_add P_def : forall x locs caus (blk: A) s' sub st st',
        delast_scope f_dl f_add sub (Scope locs caus blk) st = (s', st') ->
        Is_defined_in_scope P_def x s' ->
        (forall sub blk' st st',
            f_dl sub blk st = (blk', st') ->
            P_def blk' ->
            P_def blk) ->
        (forall blks1 blks2,
            P_def (f_add blks1 blks2) ->
            Exists (Is_defined_in x) blks1 \/ P_def blks2) ->
        Is_defined_in_scope P_def x (Scope locs caus blk).
    Proof.
      intros * Hdl Hdef Hind Hadd; inv Hdef; repeat inv_bind.
      rewrite InMembers_app in H0. apply not_or' in H0 as (Hnin1&Hnin2).
      econstructor.
      - eapply Hadd in H as [Hvd|Hvd]; eauto.
        exfalso. simpl_Exists. inv Hvd. apply In_singleton in H0; subst.
        eapply Hnin2, fst_InMembers. solve_In.
      - intro contra. apply Hnin1. rewrite fst_InMembers in *. solve_In.
    Qed.

    Lemma delast_block_Is_defined : forall x blk blk' sub st st',
        delast_block sub blk st = (blk', st') ->
        Is_defined_in x blk' ->
        Is_defined_in x blk.
    Proof.
      Opaque delast_scope.
      induction blk using block_ind2; intros * Hdl Hdef; destruct_conjs; repeat inv_bind; inv Hdef.
      - (* equation *)
        destruct eq; repeat inv_bind. constructor; auto.
      - (* reset *)
        apply mmap_values, Forall2_ignore1 in H0.
        constructor. simpl_Exists. simpl_Forall. solve_Exists.
      - (* switch *)
        simpl_Exists.
        apply mmap_values, Forall2_ignore1 in H0. simpl_Forall. repeat inv_bind.
        destruct s0. eapply delast_scope_Is_defined in H1; eauto.
        + constructor. solve_Exists.
        + intros. eapply mmap_values, Forall2_ignore1 in H3.
          simpl_Exists. simpl_Forall. solve_Exists.
        + intros. now apply Exists_app.
      - (* automaton *)
        simpl_Exists.
        apply mmap_values, Forall2_ignore1 in H0. simpl_Forall. repeat inv_bind.
        destruct s0; destruct_conjs. eapply delast_scope_Is_defined in H1; eauto.
        + constructor. solve_Exists.
        + intros; repeat inv_bind. eapply mmap_values, Forall2_ignore1 in H3.
          simpl_Exists. simpl_Forall. solve_Exists.
        + intros. destruct blks2. now apply Exists_app.
      - (* local *)
        eapply delast_scope_Is_defined in H0; eauto.
        + constructor. solve_Exists.
        + intros. eapply mmap_values, Forall2_ignore1 in H1.
          simpl_Exists. simpl_Forall. solve_Exists.
        + intros. now apply Exists_app.
          Transparent delast_scope.
    Qed.

    (** Central correctness lemma                                              *)

    Lemma delast_scope_sem {A} P_nd P_good P_wc P_wt P_sem1 (P_sem2: _ -> _ -> Prop) f_dl f_add :
      forall locs caus (blk: A) sub Γck Γty s' st st' bs Hi Hl Hi',
        FEnv.refines (@EqSt _) Hi Hi' ->
        (forall x vs, IsLast Γck x -> sem_var Hl x vs -> sem_var Hi' (rename_in_var sub x) vs) ->
        (forall x, Env.In x sub -> IsLast Γty x) ->
        (forall x, IsLast Γck x -> Env.In x sub) ->
        (forall x y, Env.find x sub = Some y -> In y (st_ids st)) ->
        incl (map fst Γck) (map fst Γty) ->
        NoDupScope P_nd (map fst Γty) (Scope locs caus blk) ->
        Forall (AtomOrGensym elab_prefs) (map fst Γty) ->
        GoodLocalsScope P_good elab_prefs (Scope locs caus blk) ->
        FEnv.dom_ub Hi (map fst Γty) ->
        FEnv.dom_ub Hi' (map fst Γck++st_ids st) ->
        (forall x, IsLast Γck x -> FEnv.In x Hl) ->
        wc_scope P_wc G1 Γck (Scope locs caus blk) ->
        wt_scope P_wt G1 Γty (Scope locs caus blk) ->
        sc_vars Γck (Hi, Hl) bs ->
        sem_scope_ck (fun Hi => sem_exp_ck G1 Hi bs) P_sem1 (Hi, Hl) bs (Scope locs caus blk) ->
        st_valid_after st Ids.last PS.empty ->
        delast_scope f_dl f_add sub (Scope locs caus blk) st = (s', st') ->
        (forall sub Γck Γty blk' st st' Hi Hl Hi',
            FEnv.refines (@EqSt _) Hi Hi' ->
            (forall x vs, IsLast Γck x -> sem_var Hl x vs -> sem_var Hi' (rename_in_var sub x) vs) ->
            (forall x, Env.In x sub -> IsLast Γty x) ->
            (forall x, IsLast Γck x -> Env.In x sub) ->
            (forall x y, Env.find x sub = Some y -> In y (st_ids st)) ->
            incl (map fst Γck) (map fst Γty) ->
            P_nd (map fst Γty) blk ->
            Forall (AtomOrGensym elab_prefs) (map fst Γty) ->
            P_good blk ->
            FEnv.dom_ub Hi (map fst Γty) ->
            FEnv.dom_ub Hi' (map fst Γck++st_ids st) ->
            (forall x, IsLast Γck x -> FEnv.In x Hl) ->
            P_wc Γck blk ->
            P_wt Γty blk ->
            sc_vars Γck (Hi, Hl) bs ->
            P_sem1 (Hi, Hl) blk ->
            st_valid_after st Ids.last PS.empty ->
            f_dl sub blk st = (blk', st') ->
            P_sem2 (Hi', @FEnv.empty _) blk') ->
        (forall blks1 blks2 Hi,
            Forall (sem_block_ck G2 Hi bs) blks1 ->
            P_sem2 Hi blks2 ->
            P_sem2 Hi (f_add blks1 blks2)) ->
        sem_scope_ck (fun Hi => sem_exp_ck G2 Hi bs) P_sem2 (Hi', @FEnv.empty _) bs s'.
    Proof.
      intros * Hvar Hvarl Hsubin1 Hsubin2 Hsubin3 Hincl Hnd2 Hat Hgood Hdom1 Hdom2 Hdom3 Hwc Hwt Hsc Hsem Hvalid Hdl Hind Hadd;
        inv Hnd2; inv Hgood; inv Hwc; inv Hwt; inv Hsem; repeat inv_bind; simpl.
      assert (forall y, Env.In y (Env.from_list (map fst x)) <-> IsLast (senv_of_locs locs) y) as Hsubin4.
      { intros *. rewrite Env.In_from_list.
        eapply fresh_idents_InMembers in H. erewrite <-H, fst_InMembers.
        split; intros * Hin.
        - simpl_In. econstructor; solve_In. simpl. congruence.
        - inv Hin. simpl_In. destruct o as [(?&?)|]; simpl in *; try congruence.
          solve_In. auto. }

      assert (NoDupMembers (map (fun '(x3, lx, _) => (lx, or_default (Streams.const absent) (Hl' x3))) x)) as Hndl1.
      { eapply fresh_idents_NoDup in H; eauto.
        rewrite fst_NoDupMembers, map_map in H. erewrite fst_NoDupMembers, map_map, map_ext; eauto.
        intros; destruct_conjs; auto. }
      assert (forall x3,
                 FEnv.In x3 (FEnv.union (FEnv.restrict Hi'0 (map fst locs)) Hi') ->
                 ~InMembers x3 (map (fun '(x4, lx, _) => (lx, or_default (Streams.const absent) (Hl' x4))) x)) as Hndl2.
      { intros * Hin Hinm. rewrite fst_InMembers in Hinm. simpl_In.
        assert (Hf:=H). eapply fresh_idents_prefixed in H. simpl_Forall; subst.
        rewrite FEnv.union_In, FEnv.restrict_In in Hin. destruct Hin as [(?&Hin2)|Hin].
        - simpl_In. simpl_Forall.
          apply contradict_AtomOrGensym in H1; eauto using last_not_in_elab_prefs.
        - eapply Hdom2, in_app_iff in Hin as [Hin|]; eauto.
          + apply Hincl in Hin. simpl_In. simpl_Forall.
            apply contradict_AtomOrGensym in Hat; eauto using last_not_in_elab_prefs.
          + eapply fresh_idents_nIn_ids in Hf; eauto. simpl_Forall. eauto.
      }
      assert (forall x3, FEnv.In x3 (FEnv.restrict Hi'0 (map fst locs)) -> ~ FEnv.In x3 Hi') as Hndl3.
      { intros * Hin contra. apply FEnv.restrict_In in Hin.
        eapply Hdom2, in_app_iff in contra as [|]; eauto.
        - eapply H5; eauto using in_or_app. now apply fst_InMembers.
        - eapply st_valid_prefixed in Hvalid. simpl_Forall; subst.
          apply contradict_AtomOrGensym in H1; eauto using last_not_in_elab_prefs. }

      remember (((FEnv.restrict Hi'0 (map fst locs)) + Hi') +
                  (FEnv.of_list (map (fun '(x, lx, _) => (lx, or_default (Streams.const absent) (Hl' x))) x))) as Hi2'.
      assert (FEnv.refines (@EqSt _) Hi'0 Hi2') as Hvar'.
      { intros ?? Hv.
        assert (sem_var Hi2' x2 v) as Hv'. 2:inv Hv'; eauto.
        subst.
        rewrite 2 sem_var_disj_union; eauto. 2:setoid_rewrite FEnv.of_list_In; auto. left.
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
        rewrite sem_var_disj_union, sem_var_disj_union; eauto. 2:setoid_rewrite FEnv.of_list_In; auto.
        apply IsLast_app in Hin as [Hin|Hin]; simpl_In; subst.
        - left; right. rewrite not_in_union_rename2.
          2:{ intros contra. rewrite Env.In_from_list, fst_InMembers in contra. simpl_In.
              eapply fresh_idents_In' in H; eauto. simpl_In.
              eapply H5; eauto using In_InMembers, in_or_app. apply Hincl. inv Hin. solve_In. }
          eapply Hvarl; eauto. eapply sem_var_refines'; eauto using Env.dom_lb_use.
        - right. inv Hin. simpl_In. destruct o as [(?&?)|]; simpl in *; try congruence.
          eapply fresh_idents_In_rename in H. 3:solve_In; simpl; eauto.
          2:{ apply NoDupMembers_map_filter; auto.
              intros; destruct_conjs; destruct o as [(?&?)|]; simpl; auto. }
          erewrite not_in_union_rename1.
          2:{ intro contra. apply Hsubin1 in contra. inv contra.
              eapply H5; eauto using In_InMembers, in_or_app. solve_In. }
          inv Hv. econstructor; [|eauto].
          apply FEnv.of_list_In_find; auto. solve_In.
          take (Hl' _ = _) and rewrite it; reflexivity.
      }
      assert (forall x, FEnv.In x (FEnv.restrict Hi'0 (map fst locs)) <-> In x (map fst locs)) as Hdom1'.
      { intros. rewrite FEnv.restrict_In. symmetry.
        split; [intros|intros (?&?)]; eauto.
        split; auto.
        rewrite H18, fst_InMembers; auto.
      }
      assert (forall x1, FEnv.In x1 Hi2' <->
                      (FEnv.In x1 Hi'
                       \/ InMembers x1
                                   (map (fun '(x2, (ty, ck, cx, _)) => (x2, (ty, ck, cx, @None (exp * ident)))) locs ++
                                        map (fun '(_, lx, (ty, ck, _)) => (lx, (ty, ck, 1%positive, None))) x))
             ) as Hdom2'.
      { subst. intros.
        rewrite 2 FEnv.union_In, InMembers_app, FEnv.of_list_In, Hdom1', 3 fst_InMembers.
        repeat rewrite map_map.
        split; [intros [[|]|]|intros [|[|]]]; auto.
        1,3:erewrite map_ext with (l:=locs); eauto; intros; destruct_conjs; auto.
        1,2:erewrite map_ext with (l:=x); eauto; intros; destruct_conjs; auto.
      }

      eapply Sscope with (Hi':=Hi2') (Hl':=FEnv.empty _).
      6:apply Hadd.
      + subst. intros * Hv' Hnin.
        repeat apply sem_var_union in Hv' as [Hv'|Hv']; auto.
        * exfalso. apply sem_var_restrict_inv in Hv' as (?&Hin).
          eapply Hnin, InMembers_app, or_introl, fst_InMembers.
          solve_In.
        * inv Hv'. apply FEnv.of_list_find_In in H8.
          exfalso. eapply Hnin, InMembers_app, or_intror, fst_InMembers. solve_In.
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
        * eapply fresh_idents_In'_rename in H as (?&?); eauto.
          2:{ apply NoDupMembers_map_filter; auto.
              intros; destruct_conjs; destruct o as [(?&?)|]; simpl; auto. }
          simpl_In.
          edestruct Hsc2 as (?&?&?). 1,2:econstructor; solve_In; simpl; eauto. congruence.
          do 2 esplit; eauto using sem_clock_refines.
          eapply Hvarl' in H. rewrite not_in_union_rename1 in H; eauto.
          -- intro contra. apply Hsubin1 in contra. inv contra.
             eapply H5; eauto using In_InMembers, in_or_app. solve_In.
          -- apply IsLast_app; right. econstructor. solve_In. simpl; congruence.
      + simpl_Forall. constructor.
        eapply fresh_idents_In'_rename in H as (?&?); subst; [| |eauto]. simpl_In.
        2:{ apply NoDupMembers_map_filter; auto.
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
      + eapply Hind with (st:=x0) (Γck:=Γck++senv_of_locs _) (Γty:=Γty++senv_of_locs _); eauto.
        * intros * Hin. rewrite IsLast_app. apply Env.union_In in Hin as [|Hin]; eauto.
          right. apply Hsubin4; auto.
        * intros * Hin. apply Env.union_In. apply IsLast_app in Hin as [|]; eauto.
          right. apply Hsubin4; auto.
        * intros * Hfind. apply Env.union_find4 in Hfind as [Hfind|Hfind].
          -- eapply incl_map; eauto using st_follows_incl, fresh_idents_st_follows.
          -- apply Env.from_list_find_In in Hfind. simpl_In.
             apply fresh_idents_In_ids in H. now simpl_Forall.
        * rewrite 2 map_app. apply incl_appl'; auto.
        * rewrite map_app, map_fst_senv_of_locs; auto.
        * rewrite map_app, map_fst_senv_of_locs; auto. apply Forall_app; split; simpl_Forall; auto.
        * rewrite map_app, map_fst_senv_of_locs. eapply local_hist_dom_ub in Hdom1; eauto.
        * eapply local_hist_dom_ub in Hdom2'; [|eauto].
          intros ? Hin. apply Hdom2' in Hin.
          rewrite map_app, map_fst_senv_of_locs.
          rewrite map_app in Hin. repeat rewrite in_app_iff in *. destruct Hin as [[|]|[|]]; auto.
          -- right. eapply incl_map; eauto using st_follows_incl, fresh_idents_st_follows.
          -- left. right. solve_In.
          -- right. simpl_In. eapply fresh_idents_In_ids in H. now simpl_Forall.
        * intros * Hil. apply IsLast_app in Hil as [Hil|Hil].
          -- eapply FEnv.In_refines; eauto.
          -- inv Hil. simpl_In. destruct o as [(?&?)|]; simpl in *; try congruence.
             edestruct H21 as (?&?&?&?&?&?&?); eauto using sem_var_In.
        * eapply sc_vars_app; eauto using sc_vars_refines, local_hist_dom_ub_refines.
          intros * Hin. rewrite InMembers_senv_of_locs.
          intro contra. eapply H5; eauto. apply Hincl, fst_InMembers; auto.
        * eapply fresh_idents_st_valid_after; eauto.
    Qed.

    Lemma delast_block_sem : forall blk sub Γck Γty blk' st st' bs Hi Hl Hi',
        FEnv.refines (@EqSt _) Hi Hi' ->
        (forall x vs, IsLast Γck x -> sem_var Hl x vs -> sem_var Hi' (rename_in_var sub x) vs) ->
        (forall x, Env.In x sub -> IsLast Γty x) ->
        (forall x, IsLast Γck x -> Env.In x sub) ->
        (forall x y, Env.find x sub = Some y -> In y (st_ids st)) ->
        incl (map fst Γck) (map fst Γty) ->
        NoDupLocals (map fst Γty) blk ->
        Forall (AtomOrGensym elab_prefs) (map fst Γty) ->
        GoodLocals elab_prefs blk ->
        FEnv.dom_ub Hi (map fst Γty) ->
        FEnv.dom_ub Hi' (map fst Γck++st_ids st) ->
        (forall x, IsLast Γck x -> FEnv.In x Hl) ->
        wc_block G1 Γck blk ->
        wt_block G1 Γty blk ->
        sc_vars Γck (Hi, Hl) bs ->
        sem_block_ck G1 (Hi, Hl) bs blk ->
        st_valid_after st Ids.last PS.empty ->
        delast_block sub blk st = (blk', st') ->
        sem_block_ck G2 (Hi', @FEnv.empty _) bs blk'.
    Proof with eauto with datatypes.
      Opaque delast_scope.
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
        + apply FEnv.dom_ub_map; auto.
        + eapply FEnv.dom_ub_map, FEnv.dom_ub_incl; eauto.
          apply incl_appr'. apply incl_map, st_follows_incl; auto.
        + setoid_rewrite FEnv.map_in_iff; auto.
        + eapply sc_vars_mask in Hsc; eauto.

      - (* switch *)
        econstructor; eauto using rename_in_exp_sem, sem_ref_sem_exp with lclocking.
        + rewrite Typing.rename_in_exp_typeof; auto.
        + take (sem_exp_ck _ _ _ _ _) and eapply sc_exp in it as Hsemck; eauto.
          take (clockof _ = [_]) and rewrite it in Hsemck; apply Forall2_singl in Hsemck.
          eapply mmap_values_valid_follows, Forall2_ignore1 in H0; eauto.
          2:{ intros; destruct_conjs; repeat inv_bind.
              destruct s0. eapply delast_scope_st_valid; eauto.
              intros; simpl in *. eapply mmap_st_valid; eauto.
              simpl_Forall; eapply delast_block_st_valid_after; eauto. }
          2:{ intros; destruct_conjs; repeat inv_bind.
              destruct s0. eapply delast_scope_st_follows; eauto.
              intros; simpl in *. eapply mmap_st_follows; eauto.
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
                assert (IsLast Γck i) as Hlast.
                { eapply H9. econstructor; eauto. congruence. }
                edestruct Hsubin2 as (?&Hsubfind); eauto.
                destruct Hsc as (_&(?&Hv'&Hck)); eauto.
                1:{ eapply H7; eauto with senv. }
                apply Hvarl in Hv'; auto. eapply sem_var_det in Hv; eauto. rewrite <-Hv.
                eapply sem_clock_det in Hsemck; eauto.
          }
          destruct s0; repeat inv_bind.
          eapply delast_scope_sem with (st:=x1) (Γck:=Γ') (Hl:=t).
          apply FEnv.restrict_refines', refines_ffilter; eauto. all:eauto.
          * intros * Hlast Hv. rewrite Hfilter2 in Hv. apply sem_var_ffilter_inv in Hv as (?&Hv&Hfilter). rewrite Hfilter.
            eapply sem_var_restrict, sem_var_ffilter; eauto.
            apply in_app_iff, or_intror. inv Hlast. solve_In; simpl.
            destruct (causl_last e0); simpl in *; try congruence.
          * intros * Hin. eapply incl_map; eauto using st_follows_incl.
          * intros ? Hin; simpl_In.
            edestruct H7 as (Hin'&_); eauto with senv. inv Hin'.
            take (In _ Γck) and eapply In_InMembers, fst_InMembers, Hincl in it.
            solve_In.
          * simpl_Forall; auto.
          * apply FEnv.restrict_dom_ub', FEnv.dom_ub_map; auto.
          * eapply FEnv.dom_ub_incl, FEnv.restrict_dom_ub. apply incl_appr'.
            intros ? Hin. simpl_In.
            unfold rename_in_var. edestruct Hsubin2 as (?&Hfind).
            eapply H9; econstructor; eauto. congruence.
            rewrite Hfind. apply Hsubin3 in Hfind. simpl; auto.
            eapply incl_map; eauto using st_follows_incl.
          * intros. rewrite Hfilter2. setoid_rewrite FEnv.map_in_iff. eauto.
          * eapply sc_vars_refines, sc_vars_restrict, sc_vars_ffilter; eauto.
            -- eapply FEnv.incl_restrict_refines; auto using EqStrel_Reflexive. apply incl_appl, incl_refl.
            -- rewrite Hfilter2; reflexivity.
            -- reflexivity.
            -- simpl_Forall; simpl_In.
               edestruct H7 as (?&Hbase); eauto with senv. rewrite Hbase. constructor.
          * take (sem_scope_ck _ _ _ _ _) and eapply sem_scope_refines1, sem_scope_restrict1, sem_scope_refines1 in it; eauto.
            apply FEnv.incl_restrict_refines; auto using EqStrel_Reflexive. solve_incl_app.
            unfold wc_env. simpl_Forall; simpl_In.
            edestruct H7 as (?&Hbase); eauto with senv. rewrite Hbase. constructor.
          * intros; simpl in *.
            eapply mmap_values_valid_follows, Forall2_ignore1 in H37; eauto.
            2:{ intros. eapply delast_block_st_valid_after; eauto. }
            2:{ intros. eapply delast_block_st_follows; eauto. }
            simpl_Forall. eapply H in H41; eauto.
            -- intros. eapply incl_map; eauto using st_follows_incl.
            -- simpl_Forall; auto.
            -- eapply FEnv.dom_ub_incl; eauto. apply incl_appr', incl_map; eauto using st_follows_incl.
          * intros. apply Forall_app; auto.

      - (* automaton (weak) *)
        assert (bs' ≡ abstract_clock stres) as Hac.
        { take (sem_transitions_ck _ _ _ _ _ _) and eapply sc_transitions in it; eauto.
          - take (fby _ _ _) and apply ac_fby1 in it. rewrite <-it0, <-it. reflexivity.
          - eapply sc_vars_subclock; eauto.
          - simpl_Forall; eauto. }
        econstructor; eauto using sem_clock_refines.
        + take (sem_transitions_ck _ _ _ _ _ _) and eapply rename_in_transitions_sem in it; eauto.
          2:{ simpl_Forall.
              eapply wx_exp_incl. 2,3:eauto with lclocking.
              intros * Hv. inv Hv. apply fst_InMembers in H15; simpl_In.
              edestruct H9 as (Hck&_); eauto with senv. }
          rewrite map_map in it. erewrite map_map, map_ext; eauto using sem_ref_sem_transitions.
          intros; destruct_conjs; auto.
        + eapply mmap_values_valid_follows, Forall2_ignore1 in H0; eauto.
          2:{ intros; destruct_conjs; repeat inv_bind.
              destruct s0; destruct_conjs. eapply delast_scope_st_valid; eauto.
              intros; repeat inv_bind. eapply mmap_st_valid; eauto.
              simpl_Forall; eapply delast_block_st_valid_after; eauto. }
          2:{ intros; destruct_conjs; repeat inv_bind.
              destruct s0; destruct_conjs. eapply delast_scope_st_follows; eauto.
              intros; repeat inv_bind. eapply mmap_st_follows; eauto.
              simpl_Forall. eapply delast_block_st_follows; eauto. }
          simpl_Forall. specialize (H25 k); destruct_conjs.
          take (select_hist _ _ _ _ _) and destruct it as (Hsel1&Hsel2). apply select_hist_fselect_hist in Hsel1.
          repeat inv_bind.
          assert (forall x vs,
                     IsLast Γ' x ->
                     sem_var t0 x vs ->
                     sem_var
                       (FEnv.restrict (fselect_hist e k stres Hi')
                                     (map fst Γ' ++ map_filter (fun '(x7, a) => option_map (fun _ : ident => rename_in_var sub x7) (causl_last a)) Γ'))
                       (rename_in_var sub x) vs) as Hvarl'.
          { intros * Hlast Hv. rewrite Hsel2 in Hv. apply sem_var_fselect_inv in Hv as (?&Hv&Hfilter). rewrite Hfilter.
            eapply sem_var_restrict, sem_var_fselect; eauto.
            apply in_app_iff, or_intror. inv Hlast. solve_In; simpl.
            destruct (causl_last e0); simpl in *; try congruence. }
          do 2 esplit.
          1:{ instantiate (1:=(_, _)). split; simpl; [|reflexivity].
              eapply select_hist_restrict_ac
                with (xs:=map fst Γ' ++ map_filter (fun '(x, a) => option_map (fun _ => rename_in_var sub x) a.(causl_last)) Γ'); eauto.
              intros * Hin Hv; simpl_In. apply in_app_iff in Hin as [Hin|Hin]; simpl_In.
              + edestruct Hsc as ((?&Hv'&Hck)&_). eapply H9; eauto with senv.
                eapply sem_var_refines in Hv'; eauto. eapply sem_var_det in Hv; eauto. rewrite <-Hv.
                rewrite <-Hac. eapply sem_clock_det; eauto.
              + unfold rename_in_var in Hv.
                assert (IsLast Γck i0) as Hlast.
                { eapply H10. econstructor; eauto. congruence. }
                edestruct Hsubin2 as (?&Hsubfind); eauto.
                destruct Hsc as (_&(?&Hv'&Hck)); eauto.
                1:{ eapply H9; eauto with senv. }
                apply Hvarl in Hv'; auto. eapply sem_var_det in Hv; eauto. rewrite <-Hv, <-Hac.
                eapply sem_clock_det; eauto.
          }
          destruct s0; destruct_conjs.
          eapply delast_scope_sem with (st:=x1) (Γck:=Γ') (Hl:=t0) (Hi:=FEnv.restrict _ _); eauto.
          * apply FEnv.restrict_refines'. eapply FEnv.refines_map; eauto.
            intros * Heq. rewrite Heq; reflexivity.
          * intros * Hin. eapply incl_map; eauto using st_follows_incl.
          * intros ? Hin; simpl_In.
            edestruct H9 as (Hin'&_); eauto with senv. inv Hin'.
            take (In _ Γck) and eapply In_InMembers, fst_InMembers, Hincl in it.
            solve_In.
          * simpl_Forall; auto.
          * apply FEnv.restrict_dom_ub', FEnv.dom_ub_map; auto.
          * eapply FEnv.dom_ub_incl, FEnv.restrict_dom_ub. apply incl_appr'.
            intros ? Hin. simpl_In.
            unfold rename_in_var. edestruct Hsubin2 as (?&Hfind).
            eapply H10; econstructor; eauto. congruence.
            rewrite Hfind. apply Hsubin3 in Hfind. simpl; auto.
            eapply incl_map; eauto using st_follows_incl.
          * intros. rewrite Hsel2. setoid_rewrite FEnv.map_in_iff. eauto.
          * eapply sc_vars_refines, sc_vars_restrict, sc_vars_fselect; eauto.
            -- eapply FEnv.incl_restrict_refines; auto using EqStrel_Reflexive. apply incl_appl, incl_refl.
            -- rewrite Hsel2; reflexivity.
            -- reflexivity.
            -- simpl_Forall; simpl_In.
               edestruct H9 as (?&Hbase); eauto with senv. rewrite Hbase. constructor.
            -- rewrite <-Hac; eauto.
          * take (sem_scope_ck _ _ _ _ _) and eapply sem_scope_refines2, sem_scope_restrict2, sem_scope_refines2 in it; eauto.
            apply FEnv.incl_restrict_refines; auto using EqStrel_Reflexive. solve_incl_app.
            unfold wc_env. simpl_Forall; simpl_In.
            edestruct H9 as (?&Hbase); eauto with senv. rewrite Hbase. constructor.
          * intros; repeat inv_bind. destruct_conjs; split.
            2:{ eapply rename_in_transitions_sem with (Hl:=Hl0); eauto using sem_ref_sem_transitions.
                simpl_Forall; eauto with lclocking. }
            take (mmap _ _ _ = _) and eapply mmap_values_valid_follows, Forall2_ignore1 in it; eauto.
            2:{ intros. eapply delast_block_st_valid_after; eauto. }
            2:{ intros. eapply delast_block_st_follows; eauto. }
            simpl_Forall. take (delast_block _ _ _ = _) and eapply H in it; eauto.
            -- intros. eapply incl_map; eauto using st_follows_incl.
            -- simpl_Forall; auto.
            -- eapply FEnv.dom_ub_incl; eauto. apply incl_appr', incl_map; eauto using st_follows_incl.
          * intros; destruct_conjs. split; auto. apply Forall_app; auto.

      - (* automaton (strong) *)
        assert (bs' ≡ abstract_clock stres) as Hac.
        { take (fby _ _ _) and apply ac_fby1 in it as Hac1.
          rewrite <-Hac1. symmetry. apply const_stres_ac. }
        assert (bs' ≡ abstract_clock stres1) as Hac1.
        { take (fby _ _ _) and apply ac_fby2 in it; now rewrite it. }
        econstructor; eauto using sem_clock_refines.
        + clear H.
          eapply mmap_values_valid_follows, Forall2_ignore1 in H0; eauto.
          2:{ intros; destruct_conjs; repeat inv_bind.
              destruct s0; destruct_conjs. eapply delast_scope_st_valid; eauto.
              intros; repeat inv_bind. eapply mmap_st_valid; eauto.
              simpl_Forall; eapply delast_block_st_valid_after; eauto. }
          2:{ intros; destruct_conjs; repeat inv_bind.
              destruct s0; destruct_conjs. eapply delast_scope_st_follows; eauto.
              intros; repeat inv_bind. eapply mmap_st_follows; eauto.
              simpl_Forall. eapply delast_block_st_follows; eauto. }
          simpl_Forall; repeat inv_bind.
          specialize (H22 k); destruct_conjs.
          take (select_hist _ _ _ _ _) and destruct it as (Hsel1&Hsel2). apply select_hist_fselect_hist in Hsel1.
          assert (forall x vs,
                     IsLast Γ' x ->
                     sem_var t0 x vs ->
                     sem_var
                       (FEnv.restrict (fselect_hist e k stres Hi')
                                     (map fst Γ' ++ map_filter (fun '(x7, a) => option_map (fun _ : ident => rename_in_var sub x7) (causl_last a)) Γ'))
                       (rename_in_var sub x) vs) as Hvarl'.
          { intros * Hlast Hv. rewrite Hsel2 in Hv. apply sem_var_fselect_inv in Hv as (?&Hv&Hfilter). rewrite Hfilter.
            eapply sem_var_restrict, sem_var_fselect; eauto.
            apply in_app_iff, or_intror. inv Hlast. solve_In; simpl.
            destruct (causl_last e0); simpl in *; try congruence. }
          do 2 esplit.
          1:{ instantiate (1:=(_, _)). split; simpl; [|reflexivity].
              eapply select_hist_restrict_ac
                with (xs:=map fst Γ' ++ map_filter (fun '(x, a) => option_map (fun _ => rename_in_var sub x) a.(causl_last)) Γ'); eauto.
              intros * Hin Hv; simpl_In. apply in_app_iff in Hin as [Hin|Hin]; simpl_In.
              + edestruct Hsc as ((?&Hv'&Hck)&_). eapply H9; eauto with senv.
                eapply sem_var_refines in Hv'; eauto. eapply sem_var_det in Hv; eauto. rewrite <-Hv.
                eapply sem_clock_det in H8; eauto. rewrite H8; auto.
              + unfold rename_in_var in Hv.
                assert (IsLast Γck i0) as Hlast.
                { eapply H10. econstructor; eauto. congruence. }
                edestruct Hsubin2 as (?&Hsubfind); eauto.
                destruct Hsc as (_&(?&Hv'&Hck)); eauto.
                1:{ eapply H9; eauto with senv. }
                apply Hvarl in Hv'; auto. eapply sem_var_det in Hv; eauto. rewrite <-Hv.
                eapply sem_clock_det in H8; eauto. rewrite H8; auto.
          }
          eapply rename_in_transitions_sem, sem_transitions_restrict; eauto using sem_ref_sem_transitions.
          2,3:simpl_Forall; eauto with lclocking.
          etransitivity; [|eapply FEnv.incl_restrict_refines]; eauto using EqStrel_Reflexive.
          eapply FEnv.restrict_refines'. 2:solve_incl_app.
          etransitivity; eauto. eapply FEnv.refines_map; eauto. intros * Heq; now rewrite Heq.
        + eapply mmap_values_valid_follows, Forall2_ignore1 in H0; eauto.
          2:{ intros; destruct_conjs; repeat inv_bind.
              destruct s0; destruct_conjs. eapply delast_scope_st_valid; eauto.
              intros; repeat inv_bind. eapply mmap_st_valid; eauto.
              simpl_Forall; eapply delast_block_st_valid_after; eauto. }
          2:{ intros; destruct_conjs; repeat inv_bind.
              destruct s0; destruct_conjs. eapply delast_scope_st_follows; eauto.
              intros; repeat inv_bind. eapply mmap_st_follows; eauto.
              simpl_Forall. eapply delast_block_st_follows; eauto. }
          simpl_Forall. specialize (H23 k); destruct_conjs.
          take (select_hist _ _ _ _ _) and destruct it as (Hsel1&Hsel2). apply select_hist_fselect_hist in Hsel1.
          repeat inv_bind.
          assert (forall x vs,
                     IsLast Γ' x ->
                     sem_var t0 x vs ->
                     sem_var
                       (FEnv.restrict (fselect_hist e k stres1 Hi')
                                     (map fst Γ' ++ map_filter (fun '(x7, a) => option_map (fun _ : ident => rename_in_var sub x7) (causl_last a)) Γ'))
                       (rename_in_var sub x) vs) as Hvarl'.
          { intros * Hlast Hv. rewrite Hsel2 in Hv. apply sem_var_fselect_inv in Hv as (?&Hv&Hfilter). rewrite Hfilter.
            eapply sem_var_restrict, sem_var_fselect; eauto.
            apply in_app_iff, or_intror. inv Hlast. solve_In; simpl.
            destruct (causl_last e0); simpl in *; try congruence. }
          do 2 esplit.
          1:{ instantiate (1:=(_, _)). split; simpl; [|reflexivity].
              eapply select_hist_restrict_ac
                with (xs:=map fst Γ' ++ map_filter (fun '(x, a) => option_map (fun _ => rename_in_var sub x) a.(causl_last)) Γ'); eauto.
              intros * Hin Hv; simpl_In. apply in_app_iff in Hin as [Hin|Hin]; simpl_In.
              + edestruct Hsc as ((?&Hv'&Hck)&_). eapply H9; eauto with senv.
                eapply sem_var_refines in Hv'; eauto. eapply sem_var_det in Hv; eauto. rewrite <-Hv.
                eapply sem_clock_det in H8; eauto. rewrite H8; auto.
              + unfold rename_in_var in Hv.
                assert (IsLast Γck i0) as Hlast.
                { eapply H10. econstructor; eauto. congruence. }
                edestruct Hsubin2 as (?&Hsubfind); eauto.
                destruct Hsc as (_&(?&Hv'&Hck)); eauto.
                1:{ eapply H9; eauto with senv. }
                apply Hvarl in Hv'; auto. eapply sem_var_det in Hv; eauto. rewrite <-Hv.
                eapply sem_clock_det in H8; eauto. rewrite H8; auto.
          }
          destruct s0; destruct_conjs.
          eapply delast_scope_sem with (st:=x1) (Γck:=Γ') (Hl:=t0) (Hi:=FEnv.restrict _ _); eauto.
          * apply FEnv.restrict_refines'. eapply FEnv.refines_map; eauto.
            intros * Heq. rewrite Heq; reflexivity.
          * intros * Hin. eapply incl_map; eauto using st_follows_incl.
          * intros ? Hin; simpl_In.
            edestruct H9 as (Hin'&_); eauto with senv. inv Hin'.
            take (In _ Γck) and eapply In_InMembers, fst_InMembers, Hincl in it.
            solve_In.
          * simpl_Forall; auto.
          * apply FEnv.restrict_dom_ub', FEnv.dom_ub_map; auto.
          * eapply FEnv.dom_ub_incl, FEnv.restrict_dom_ub. apply incl_appr'.
            intros ? Hin. simpl_In.
            unfold rename_in_var. edestruct Hsubin2 as (?&Hfind).
            eapply H10; econstructor; eauto. congruence.
            rewrite Hfind. apply Hsubin3 in Hfind. simpl; auto.
            eapply incl_map; eauto using st_follows_incl.
          * intros. rewrite Hsel2. setoid_rewrite FEnv.map_in_iff. eauto.
          * eapply sc_vars_refines, sc_vars_restrict, sc_vars_fselect; eauto.
            -- eapply FEnv.incl_restrict_refines; auto using EqStrel_Reflexive. apply incl_appl, incl_refl.
            -- rewrite Hsel2; reflexivity.
            -- reflexivity.
            -- simpl_Forall; simpl_In.
               edestruct H9 as (?&Hbase); eauto with senv. rewrite Hbase. constructor.
            -- rewrite <-Hac1; eauto.
          * take (sem_scope_ck _ _ _ _ _) and eapply sem_scope_refines3, sem_scope_restrict3, sem_scope_refines3 in it; eauto.
            apply FEnv.incl_restrict_refines; auto using EqStrel_Reflexive. solve_incl_app.
            unfold wc_env. simpl_Forall; simpl_In.
            edestruct H9 as (?&Hbase); eauto with senv. rewrite Hbase. constructor.
          * intros; repeat inv_bind.
            eapply mmap_values_valid_follows, Forall2_ignore1 in H40; eauto.
            2:{ intros. eapply delast_block_st_valid_after; eauto. }
            2:{ intros. eapply delast_block_st_follows; eauto. }
            simpl_Forall. take (delast_block _ _ _ = _) and eapply H in it; eauto.
            -- intros. eapply incl_map; eauto using st_follows_incl.
            -- simpl_Forall; auto.
            -- eapply FEnv.dom_ub_incl; eauto. apply incl_appr', incl_map; eauto using st_follows_incl.
          * intros; destruct_conjs. apply Forall_app; auto.

      - (* local *)
        constructor. eapply delast_scope_sem; eauto.
        + intros; simpl in *.
          eapply mmap_values_valid_follows, Forall2_ignore1 in H23; eauto.
          2:{ intros. eapply delast_block_st_valid_after; eauto. }
          2:{ intros. eapply delast_block_st_follows; eauto. }
          simpl_Forall. eapply H in H27; eauto.
          * intros. eapply incl_map; eauto using st_follows_incl.
          * simpl_Forall; auto.
          * eapply FEnv.dom_ub_incl; eauto. apply incl_appr', incl_map; eauto using st_follows_incl.
        + intros. apply Forall_app; auto.
    Qed.

    Lemma delast_node_sem : forall f n ins outs,
        wt_global (Global G1.(types) (n::G1.(nodes))) ->
        wc_global (Global G1.(types) (n::G1.(nodes))) ->
        Ordered_nodes (Global G1.(types) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(types) ((delast_node n)::G2.(nodes))) ->
        sem_node_ck (Global G1.(types) (n::G1.(nodes))) f ins outs ->
        sem_node_ck (Global G2.(types) ((delast_node n)::G2.(nodes))) f ins outs.
    Proof with eauto.
      intros * (_&Hwt) Hwc Hord1 Hord2 Hsem.

      inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
      - erewrite find_node_now in Hfind; eauto. inv Hfind.
        (*The semantics of equations can be given according to G only *)
        eapply sem_block_ck_cons in H3; eauto. rename H3 into Hblksem.
        2:{ inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }

        replace {| types := types G1; nodes := nodes G1 |} with G1 in Hblksem by (destruct G1; auto).
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
        + intros * _ Hv. inv Hv. inv H3.
        + intros * Hin. apply Env.Props.P.F.empty_in_iff in Hin as [].
        + intros * Hl. apply senv_of_inout_NoLast in Hl as [].
        + intros * Hfind. rewrite Env.gempty in Hfind. congruence.
        + reflexivity.
        + rewrite map_fst_senv_of_inout. apply n_nodup.
        + rewrite map_fst_senv_of_inout. auto.
        + apply FEnv.dom_dom_ub; auto.
        + unfold st_ids. rewrite init_st_anns, app_nil_r.
          apply FEnv.dom_dom_ub; auto.
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

  Lemma delast_global_refines : forall G,
      wt_global G ->
      wc_global G ->
      global_sem_refines G (delast_global G).
  Proof with eauto using wc_global_Ordered_nodes.
    intros (enms&nds) (Htypes&Hwt).
    induction nds; intros * Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      eapply Clocking.delast_global_wc, wc_global_Ordered_nodes in Hwc' ;
        unfold delast_global in Hwc'; simpl in Hwc'.
      apply global_sem_ref_cons with (f:=n_name a)...
      + inv Hwt. inv Hwc. eapply IHnds...
      + intros ins outs Hsem; simpl in *.
        change enms with ((Global enms (map delast_node nds)).(types)).
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
       (Ty : LTYPING Ids Op OpAux Cks Senv Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Lord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
       (LClockSem : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Clo Lord CStr Sem)
       (DL  : DELAST Ids Op OpAux Cks Senv Syn)
       <: DLCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Ty Clo Lord Sem LClockSem DL.
  Include DLCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Ty Clo Lord Sem LClockSem DL.
End DLCorrectnessFun.
