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
        1-14:econstructor; simpl in *; eauto using sem_var_refines.
        1-3:rewrite Typing.rename_in_exp_typeof; auto.
        all:(simpl in *; simpl_Forall; eauto).
        - now rewrite Typing.rename_in_exp_typesof.
        - rewrite <-Forall2Brs_map_1. eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hs.
          simpl_Exists. simpl_Forall. eauto.
        - rewrite <-Forall2Brs_map_1. eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hs.
          simpl_Exists. simpl_Forall. eauto.
        - rewrite Typing.rename_in_exp_typeof; auto.
        - rewrite <-Forall2Brs_map_1. eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hs.
          simpl_Exists. simpl_Forall. eauto.
        - specialize (H8 _ eq_refl). simpl_Forall; eauto.
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
      forall x vs, IsLast Γ x -> sem_var (CStr.fwhen_hist k r H) x vs -> sem_var (CStr.fwhen_hist k r H') (rename_in_var sub x) vs.
    Proof.
      intros * Hsub * ? Hv.
      eapply sem_var_fwhen_inv in Hv as (?&Hv&Heq).
      eapply Hsub, sem_var_fwhen in Hv; eauto. rewrite Heq; eauto.
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

    Fact rename_in_var_of_list_inj : forall xs x1 x2,
        NoDup (map snd xs) ->
        InMembers x1 xs ->
        InMembers x2 xs ->
        rename_in_var (Env.from_list xs) x1 = rename_in_var (Env.from_list xs) x2 ->
        x1 = x2.
    Proof.
      intros * Hnd Hin1 Hin2 Hrename. unfold rename_in_var in Hrename.
      destruct (Env.find x1 _) eqn:Hf1, (Env.find x2 _) eqn:Hf2; simpl in *; subst; auto.
      - apply Env.from_list_find_In in Hf1. apply Env.from_list_find_In in Hf2.
        eapply NoDup_snd_det; eauto.
      - exfalso.
        rewrite <-Env.Props.P.F.not_find_in_iff, Env.In_from_list in Hf2; eauto.
      - exfalso.
        rewrite <-Env.Props.P.F.not_find_in_iff, Env.In_from_list in Hf1; eauto.
    Qed.

    (** Central correctness lemma                                              *)

    Lemma delast_scope_sem {A} P_nd P_good P_wc P_wt P_sem1 (P_sem2: _ -> _ -> Prop) f_dl f_add :
      forall locs (blk: A) sub Γck Γty s' st st' bs Hi Hl Hi2,
        FEnv.refines (@EqSt _) Hi Hi2 ->
        (forall x vs, IsLast Γck x -> sem_var Hl x vs -> sem_var Hi2 (rename_in_var sub x) vs) ->
        (forall x, Env.In x sub -> IsLast Γty x) ->
        (forall x, IsLast Γck x -> Env.In x sub) ->
        (forall x y, Env.find x sub = Some y -> In y (st_ids st)) ->
        (forall x1 x2, IsLast Γck x1 -> IsLast Γck x2 -> rename_in_var sub x1 = rename_in_var sub x2 -> x1 = x2) ->
        incl (map fst Γck) (map fst Γty) ->
        NoDupScope P_nd (map fst Γty) (Scope locs blk) ->
        Forall (AtomOrGensym elab_prefs) (map fst Γty) ->
        GoodLocalsScope P_good elab_prefs (Scope locs blk) ->
        FEnv.dom_ub Hi (map fst Γty) ->
        FEnv.dom_ub Hi2 (map fst Γty++st_ids st) ->
        FEnv.dom_ub Hl (map fst Γty) ->
        wc_scope P_wc G1 Γck (Scope locs blk) ->
        wt_scope P_wt G1 Γty (Scope locs blk) ->
        sem_scope_ck (fun Hi => sem_exp_ck G1 Hi bs) P_sem1 (Hi, Hl) bs (Scope locs blk) ->
        delast_scope f_dl f_add sub (Scope locs blk) st = (s', st') ->
        (forall sub Γck Γty blk' st st' Hi Hl Hi2,
            FEnv.refines (@EqSt _) Hi Hi2 ->
            (forall x vs, IsLast Γck x -> sem_var Hl x vs -> sem_var Hi2 (rename_in_var sub x) vs) ->
            (forall x, Env.In x sub -> IsLast Γty x) ->
            (forall x, IsLast Γck x -> Env.In x sub) ->
            (forall x y, Env.find x sub = Some y -> In y (st_ids st)) ->
            (forall x1 x2, IsLast Γck x1 -> IsLast Γck x2 -> rename_in_var sub x1 = rename_in_var sub x2 -> x1 = x2) ->
            incl (map fst Γck) (map fst Γty) ->
            P_nd (map fst Γty) blk ->
            Forall (AtomOrGensym elab_prefs) (map fst Γty) ->
            P_good blk ->
            FEnv.dom_ub Hi (map fst Γty) ->
            FEnv.dom_ub Hi2 (map fst Γty++st_ids st) ->
            FEnv.dom_ub Hl (map fst Γty) ->
            P_wc Γck blk ->
            P_wt Γty blk ->
            P_sem1 (Hi, Hl) blk ->
            f_dl sub blk st = (blk', st') ->
            P_sem2 (Hi2, @FEnv.empty _) blk') ->
        (forall blks1 blks2 Hi,
            Forall (sem_block_ck G2 Hi bs) blks1 ->
            P_sem2 Hi blks2 ->
            P_sem2 Hi (f_add blks1 blks2)) ->
        sem_scope_ck (fun Hi => sem_exp_ck G2 Hi bs) P_sem2 (Hi2, @FEnv.empty _) bs s'.
    Proof.
      intros * Hvar Hvarl Hsubin1 Hsubin2 Hsubin3 Hinj Hincl Hnd2 Hat Hgood Hub1 (* Hlb1 *) Hub2 Hub3 (* Hlb2 *) Hwc Hwt (* Hsc *) Hsem Hdl Hind Hadd;
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
                 FEnv.In x3 Hi' ->
                 ~InMembers x3 (map (fun '(x4, lx, _) => (lx, or_default (Streams.const absent) (Hl' x4))) x)) as Hndl2.
      { intros * Hin Hinm. rewrite fst_InMembers in Hinm. simpl_In.
        assert (Hf:=H). eapply fresh_idents_prefixed in H. simpl_Forall; subst.
        eapply H15, IsVar_senv_of_locs in Hin. simpl_In. simpl_Forall.
        take (AtomOrGensym _ _) and apply contradict_AtomOrGensym in it; eauto using last_not_in_elab_prefs.
      }
      assert (forall x3,
                 FEnv.In x3 Hi2 ->
                 ~ FEnv.In x3 (Hi' + FEnv.of_list (map (fun '(x4, lx, _) => (lx, or_default (Streams.const absent) (Hl' x4))) x))) as Hndl3.
      { intros * Hin1 Hin2. apply FEnv.union_In in Hin2 as [Hin2|Hin2].
        - apply H15, IsVar_senv_of_locs in Hin2.
          apply Hub2, in_app_iff in Hin1 as [Hin1|Hin1].
          + take (forall x, InMembers x locs -> ~_) and eapply it; eauto.
          + simpl_In. simpl_Forall.
            specialize (st_valid_prefixed st) as Hvalid. unfold st_ids in Hvalid. simpl_Forall; subst.
            apply contradict_AtomOrGensym in H2; eauto using last_not_in_elab_prefs.
        - apply FEnv.of_list_In in Hin2. simpl_In.
          apply Hub2, in_app_iff in Hin1 as [Hin1|Hin1].
          + eapply fresh_idents_prefixed in H. simpl_Forall; subst.
            eapply contradict_AtomOrGensym in Hat; eauto using last_not_in_elab_prefs.
          + eapply fresh_idents_nIn_ids in H. simpl_Forall; eauto.
      }

      remember (Hi' + (FEnv.of_list (map (fun '(x, lx, _) => (lx, or_default (Streams.const absent) (Hl' x))) x))) as Hi2'.
      assert (FEnv.refines (@EqSt _) Hi' Hi2') as Href1.
      { intros ?? Hv.
        assert (sem_var Hi2' x2 v) as Hv'. 2:inv Hv'; eauto. subst.
        rewrite sem_var_disj_union; eauto. 2:setoid_rewrite FEnv.of_list_In; auto. left.
        econstructor; eauto. reflexivity.
      }
      assert (FEnv.refines (@EqSt _) (Hi + Hi') (Hi2 + Hi2')) as Href2.
      { intros ?? Hv.
        assert (sem_var (Hi2 + Hi2') x2 v) as Hv'. 2:inv Hv'; eauto. subst.
        rewrite sem_var_disj_union; eauto.
        eapply FEnv.union4 in Hv as [Hv|Hv]; [left|right]; eapply sem_var_refines; eauto.
        1,2:econstructor; eauto; reflexivity.
      }
      assert (forall y vs,
                 IsLast (Γck ++ senv_of_locs locs) y ->
                 sem_var (Hl + Hl') y vs ->
                 sem_var (Hi2 + Hi2') (rename_in_var (Env.union sub (Env.from_list (map fst x))) y) vs) as Hvarl'.
      { intros * Hin Hv. subst Hi2'.
        rewrite sem_var_disj_union, sem_var_disj_union; eauto. 2:setoid_rewrite FEnv.of_list_In; auto.
        apply IsLast_app in Hin as [Hin|Hin]; simpl_In; subst.
        - apply sem_var_union in Hv as [Hv|Hv]; auto.
          2:{ exfalso. eapply sem_var_In, H16, IsLast_senv_of_locs in Hv. inv Hin.
              eapply H4; eauto. apply Hincl; solve_In. }
          left. rewrite not_in_union_rename2.
          2:{ intros contra. rewrite Env.In_from_list, fst_InMembers in contra. simpl_In.
              eapply fresh_idents_In' in H; eauto. simpl_In.
              inv Hin. eapply H4; eauto using In_InMembers. eapply Hincl; solve_In. }
          eapply Hvarl; eauto.
        - inv Hin. simpl_In. destruct o as [(?&?)|]; simpl in *; try congruence.
          apply sem_var_union in Hv as [Hv|Hv]; auto.
          1:{ exfalso. eapply sem_var_In, Hub3 in Hv.
              eapply H4; eauto using In_InMembers. }
          right; right.
          eapply fresh_idents_In_rename in H. 3:solve_In; simpl; eauto.
          2:{ apply NoDupMembers_map_filter; auto.
              intros; destruct_conjs; destruct o as [(?&?)|]; simpl; auto. }
          erewrite not_in_union_rename1.
          2:{ intro contra. apply Hsubin1 in contra. inv contra.
              eapply H4; eauto using In_InMembers, in_or_app. solve_In. }
          inv Hv. econstructor; [|eauto].
          apply FEnv.of_list_In_find; auto. solve_In.
          take (Hl' _ = _) and rewrite it; reflexivity.
      }
      assert (forall x1, FEnv.In x1 Hi2'
                    <-> IsVar (senv_of_locs (locs++map (fun '(_, lx, (ty, ck, _)) => (lx, (ty, ck, xH, None))) x)) x1
             ) as Hdom2'.
      { subst. intros.
        rewrite FEnv.union_In, FEnv.of_list_In, H15, 2 IsVar_senv_of_locs, InMembers_app.
        apply or_iff_compat_l.
        clear - x2. split; intros * Hin; solve_In.
      }

      eapply Sscope with (Hi':=Hi2') (Hl':=FEnv.empty _).
      5:apply Hadd.
      - subst. intros.
        rewrite FEnv.union_In, (H15 x2), FEnv.of_list_In, 2 IsVar_senv_of_locs, InMembers_app, 4 fst_InMembers,
          3 map_map.
        split; (intros [|]; [left|right]); erewrite map_ext; eauto.
        all:intros; destruct_conjs; auto.
      - intros. simpl_app. rewrite IsLast_app.
        split; [intros []; take (_ _ = Some _) and inv it|intros [Hil|Hil]; inv Hil]; simpl_In; congruence.
      - intros * Hin. apply in_app_iff in Hin as [|]; simpl_In.
      - take (sc_vars (senv_of_locs _) _ _) and destruct it as (Hsc1&Hsc2).
        split; intros * Hck; inv Hck; simpl_In; rewrite in_app_iff in *;
          destruct Hin as [Hin|Hin]; simpl_In;
          try (intros Hca; inv Hca; simpl_In;
               take (In _ (_ ++ _)) and apply in_app_iff in it as [|]; simpl_In);
          try congruence.
        + intros Hv. eapply sem_clock_refines, Hsc1; eauto.
          econstructor. clear - Hin0; solve_In. eauto. eapply sem_var_refines'; eauto.
          apply FEnv.union_In, or_intror, H15. econstructor; clear - Hin0; solve_In.
        + eapply fresh_idents_In'_rename in H as (?&?); eauto.
          2:{ apply NoDupMembers_map_filter; auto.
              intros; destruct_conjs; destruct o as [(?&?)|]; simpl; auto. }
          simpl_In.
          intros Hv. eapply sem_clock_refines, Hsc2; eauto.
          1,2:econstructor; clear - Hin; solve_In; simpl; eauto. congruence.
          assert (exists vs, sem_var (Hl + Hl') i0 vs) as (vs&Hv').
          { assert (FEnv.In i0 (Hl + Hl')) as (?&?); [|esplit; econstructor; eauto; reflexivity].
            apply FEnv.union_In, or_intror, H16.
            clear - Hin; econstructor; solve_In. simpl. congruence.
          }
          assert (Hv'':=Hv'). eapply Hvarl' in Hv''. rewrite not_in_union_rename1 in Hv''; eauto.
          -- eapply sem_var_det in Hv''; [|eapply Hv]. now rewrite Hv''.
          -- intro contra. apply Hsubin1 in contra. inv contra.
             eapply H4; eauto using In_InMembers, in_or_app. solve_In.
          -- apply IsLast_app; right. econstructor. solve_In. simpl; congruence.
      - simpl_Forall. constructor.
        eapply fresh_idents_In'_rename in H as (?&?); subst; [| |eauto]. simpl_In.
        2:{ apply NoDupMembers_map_filter; auto.
            intros; destruct_conjs; destruct o as [(?&?)|]; simpl; auto. }
        edestruct H18 as (vs0&vs1&vs&He&Hv&Hfby&Hvl); eauto.
        eapply Seq with (ss:=[[vs]]); simpl; repeat constructor.
        + eapply Sfby with (s0ss:=[[vs0]]) (sss:=[[vs1]]); simpl.
          1-3:repeat constructor; simpl; eauto.
          * eapply rename_in_exp_sem; eauto using sem_ref_sem_exp.
            simpl_Forall; eauto with lclocking.
          * do 2 (eapply sem_var_refines; eauto).
            apply FEnv.union_refines4', EqStrel_Reflexive.
        + erewrite <-not_in_union_rename1 with (sub:=sub).
          2:{ intro contra. apply Hsubin1 in contra. inv contra.
              eapply H4; eauto using In_InMembers, in_or_app. solve_In. }
          eapply Hvarl'; eauto.
          * apply IsLast_app, or_intror. econstructor; solve_In. simpl; congruence.
          * eapply sem_var_refines; eauto.
            apply FEnv.union_refines4', EqStrel_Reflexive.
      - eapply Hind with (st:=x0) (Γck:=Γck++senv_of_locs _) (Γty:=Γty++senv_of_locs _); eauto.
        + intros * Hin. rewrite IsLast_app. apply Env.union_In in Hin as [|Hin]; eauto.
          right. apply Hsubin4; auto.
        + intros * Hin. apply Env.union_In. apply IsLast_app in Hin as [|]; eauto.
          right. apply Hsubin4; auto.
        + intros * Hfind. apply Env.union_find4 in Hfind as [Hfind|Hfind].
          * eapply incl_map; eauto using st_follows_incl, fresh_idents_st_follows.
          * apply Env.from_list_find_In in Hfind. simpl_In.
            apply fresh_idents_In_ids in H. now simpl_Forall.
        + intros * Hl1 Hl2 Hrename.
          assert (forall y, IsLast Γck y -> ~Env.In y (Env.from_list (map fst x))) as Hdisj1.
          { intros * Hlast Hin2. inv Hlast.
            eapply Env.In_from_list, fresh_idents_InMembers in Hin2; eauto.
            simpl_In. take (forall x, InMembers x locs -> ~_) and eapply it; eauto using In_InMembers. apply Hincl. solve_In.
          }
          assert (forall y, IsLast (senv_of_locs locs) y -> ~ Env.In y sub) as Hdisj2.
          { intros * Hin1 Hin2. apply Hsubin1 in Hin2. inv Hin2.
            inv Hin1. simpl_In.
            take (forall x, InMembers x locs -> ~_) and eapply it; eauto using In_InMembers. solve_In.
          }
          assert (forall y, IsLast Γck y -> In (rename_in_var sub y) (st_ids st)) as Hst1.
          { intros * Hlast. apply Hsubin2 in Hlast as (?&Hfind).
            unfold rename_in_var. rewrite Hfind; eauto. }
          assert (forall y, IsLast (senv_of_locs locs) y -> ~In (rename_in_var (Env.from_list (map fst x)) y) (st_ids st)) as Hst2.
          { intros * Hlast. apply Hsubin4 in Hlast as (?&Hfind).
            unfold rename_in_var. rewrite Hfind; simpl.
            apply Env.from_list_find_In in Hfind. simpl_In.
            eapply fresh_idents_nIn_ids in H. simpl_Forall. auto. }
          apply IsLast_app in Hl1 as [Hl1|Hl1]; apply IsLast_app in Hl2 as [Hl2|Hl2].
          * rewrite 2 not_in_union_rename2 in Hrename; auto.
          * rewrite not_in_union_rename2, not_in_union_rename1 in Hrename; auto. exfalso.
            eapply Hst2; eauto. rewrite <-Hrename; auto.
          * rewrite not_in_union_rename1, not_in_union_rename2 in Hrename; auto. exfalso.
            eapply Hst2; eauto. rewrite Hrename; auto.
          * rewrite 2 not_in_union_rename1 in Hrename; auto.
            apply rename_in_var_of_list_inj in Hrename; auto.
            2-3:eapply fresh_idents_InMembers; eauto.
            -- clear - H. eapply fresh_idents_NoDup, fst_NoDupMembers in H.
               rewrite map_map in *. erewrite map_ext; eauto. intros; destruct_conjs; auto.
            -- clear - Hl1. inv Hl1. simpl_In. destruct o as [(?&?)|]; simpl in *; try congruence. solve_In. auto.
            -- clear - Hl2. inv Hl2. simpl_In. destruct o as [(?&?)|]; simpl in *; try congruence. solve_In. auto.
        + rewrite 2 map_app. apply incl_appl'; auto.
        + rewrite map_app, map_fst_senv_of_locs; auto.
        + rewrite map_app, map_fst_senv_of_locs. apply Forall_app; split; simpl_Forall; auto.
        + rewrite map_app, map_fst_senv_of_locs. eapply local_hist_dom_ub in Hub1; eauto.
        + eapply local_hist_dom_ub with (H:=Hi2) (H':=Hi2') in Hdom2'; [|eauto].
          intros ? Hin. apply Hdom2' in Hin.
          rewrite map_app, map_fst_senv_of_locs.
          rewrite map_app in Hin. repeat rewrite in_app_iff in *. destruct Hin as [[|]|[|]]; auto.
          * right. eapply incl_map; eauto using st_follows_incl, fresh_idents_st_follows.
          * right. simpl_In. eapply fresh_idents_In_ids in H. now simpl_Forall.
        + intros ? Hin. rewrite map_app, in_app_iff, map_fst_senv_of_locs.
          apply FEnv.union_In in Hin as [|Hin]; auto.
          right. apply H16, IsLast_senv_of_locs in Hin. solve_In.
    Qed.

    Ltac inv_branch := (Syn.inv_branch || Ty.inv_branch || Cl.inv_branch || Sem.inv_branch).

    Fact find_rename_var1 (Γ: static_env) sub : forall x y a,
      find (fun '(y, ann) => isSome ann.(causl_last) && (x ==b rename_in_var sub y)) Γ = Some (y, a) ->
      IsLast Γ y /\ x = rename_in_var sub y.
    Proof.
      intros * Hfind.
      apply find_some in Hfind as (Hin&Heq).
      apply andb_prop in Heq as (Hsome&Heq).
      rewrite equiv_decb_equiv in Heq. inv Heq.
      apply isSome_true in Hsome as (?&Hsome).
      split; auto.
      econstructor; eauto. congruence.
    Qed.

    Fact find_rename_var2 (Γ: static_env) sub : forall x,
        (forall x1 x2, IsLast Γ x1 -> IsLast Γ x2 -> rename_in_var sub x1 = rename_in_var sub x2 -> x1 = x2) ->
        IsLast Γ x ->
        exists a, find (fun '(y, ann0) => isSome (causl_last ann0) && (rename_in_var sub x ==b rename_in_var sub y)) Γ = Some (x, a).
    Proof.
      intros * Hinj Hlast. inv Hlast.
      induction Γ as [|(?&?)]; [inv H|inv H]; subst; simpl.
      * inv H1. esplit. rewrite equiv_decb_refl; simpl.
        destruct (causl_last e); try congruence; simpl; eauto.
      * destruct IHΓ as (?&Hfind); eauto.
        1:{ intros * Hl1 Hl2; inv Hl1; inv Hl2. eapply Hinj. 1,2:econstructor; eauto with datatypes. }
        cases_eqn Heq; eauto.
        apply andb_prop in Heq as (Heq1&Heq). apply isSome_true in Heq1 as (?&Hsome).
        rewrite equiv_decb_equiv in Heq. inv Heq.
        eapply Hinj in H2; subst; eauto.
        1,2:econstructor; eauto with datatypes. now rewrite Hsome.
    Qed.

    Lemma delast_block_sem : forall blk sub Γck Γty blk' st st' bs Hi Hl Hi',
        FEnv.refines (@EqSt _) Hi Hi' ->
        (forall x vs, IsLast Γck x -> sem_var Hl x vs -> sem_var Hi' (rename_in_var sub x) vs) ->
        (forall x, Env.In x sub -> IsLast Γty x) ->
        (forall x, IsLast Γck x -> Env.In x sub) ->
        (forall x y, Env.find x sub = Some y -> In y (st_ids st)) ->
        (forall x1 x2, IsLast Γck x1 -> IsLast Γck x2 -> rename_in_var sub x1 = rename_in_var sub x2 -> x1 = x2) ->
        incl (map fst Γck) (map fst Γty) ->
        NoDupLocals (map fst Γty) blk ->
        Forall (AtomOrGensym elab_prefs) (map fst Γty) ->
        GoodLocals elab_prefs blk ->
        FEnv.dom_ub Hi (map fst Γty) ->
        FEnv.dom_ub Hi' (map fst Γty++st_ids st) ->
        FEnv.dom_ub Hl (map fst Γty) ->
        wc_block G1 Γck blk ->
        wt_block G1 Γty blk ->
        sem_block_ck G1 (Hi, Hl) bs blk ->
        delast_block sub blk st = (blk', st') ->
        sem_block_ck G2 (Hi', @FEnv.empty _) bs blk'.
    Proof with eauto with datatypes.
      Opaque delast_scope.
      induction blk using block_ind2;
        intros * Hvar Hvarl Hsubin1 Hsubin2 Hsubin3 Hinj Hincl Hnd2 Hat Hgood Hub1 Hub2 Hub3 Hwc Hwt Hsem Hdl;
        inv Hnd2; inv Hgood; inv Hwc; inv Hwt; inv Hsem; repeat inv_bind; simpl.
      - (* equation *)
        constructor.
        eapply rename_in_equation_sem with (H':=Hi'); eauto using sem_ref_sem_equation with lclocking.

      - (* reset *)
        econstructor; eauto using rename_in_exp_sem, sem_ref_sem_exp with lclocking.
        intros k. specialize (H15 k).
        eapply mmap_values_follows, Forall2_ignore1 in H0; eauto.
        2:intros; eapply delast_block_st_follows; eauto.
        simpl_Forall.
        eapply H in H12; eauto using refines_mask, mask_hist_sub2.
        + intros * Hin. eapply incl_map; eauto. apply st_follows_incl; auto.
        + simpl_Forall; auto.
        + apply FEnv.dom_ub_map; auto.
        + eapply FEnv.dom_ub_map, FEnv.dom_ub_incl; eauto.
          apply incl_appr'. apply incl_map, st_follows_incl; auto.
        + apply FEnv.dom_ub_map; auto.

      - (* switch *)
        econstructor; eauto using rename_in_exp_sem, sem_ref_sem_exp with lclocking.
        + rewrite Typing.rename_in_exp_typeof; auto.
        + eapply mmap_values_follows, Forall2_ignore1 in H0; eauto.
          2:{ intros; destruct_conjs; repeat inv_bind.
              destruct b0. repeat inv_bind.
              eapply mmap_st_follows; eauto.
              simpl_Forall. eapply delast_block_st_follows; eauto. }
          simpl_Forall. repeat inv_branch. repeat inv_bind.
          take (when_hist _ _ _ _) and destruct it as (Hwhen1&Hwhen2).
          exists ((h + (fun x => obind (List.find (fun '(y, ann) => (isSome ann.(causl_last)) && (x ==b rename_in_var sub y)) Γ') (fun '(x, _) => h0 x))), FEnv.empty _).
          split.
          1:{ split; simpl; [|intros ?? Hfind; inv Hfind].
              intros ?? Hfind. apply FEnv.union4 in Hfind as [Hfind|Hfind].
              - apply Hwhen1 in Hfind as (?&Hwhen&Hfind).
                apply Hvar in Hfind as (?&Heq&Hfind).
                do 2 esplit; [|eauto]. now rewrite <-Heq.
              - apply obind_inversion in Hfind as ((?&?)&Heq&Hfind).
                apply Hwhen2 in Hfind as (?&Hwhen&Hfind).
                assert (sem_var Hl i x4) as Hv by (econstructor; eauto; reflexivity).
                apply find_rename_var1 in Heq as (Hlast&Heq); subst.
                apply Hvarl in Hv; [|auto]. inv Hv.
                do 2 esplit; [|eauto]. now rewrite <-H21.
          }
          constructor.
          eapply mmap_values_follows, Forall2_ignore1 in H1; eauto.
          2:{ intros. eapply delast_block_st_follows; eauto. }
          simpl_Forall.
          eapply H with (Hi:=h) (Hl:=h0) (Γck:=Γ') in H21; eauto.
          * intros ?? Hfind. do 2 esplit; [reflexivity|].
            apply FEnv.union2; auto.
            destruct (obind _ _) eqn:Ho; auto. exfalso.
            apply obind_inversion in Ho as ((?&?)&Ho&Hhi).
            apply find_rename_var1 in Ho as (Hlast&?); subst.
            eapply FEnv.In_refines in Hwhen1; [|econstructor; eauto].
            apply Hub1 in Hwhen1. simpl_In. simpl_Forall.
            eapply H9, Hsubin2 in Hlast as (?&Hsub). unfold rename_in_var in Hat. rewrite Hsub in Hat.
            eapply st_valid_AtomOrGensym_nIn; eauto using last_not_in_elab_prefs.
          * intros * Hlast Hv. eapply sem_var_union3'.
            inv Hv. econstructor; [|eauto].
            edestruct find_rename_var2 with (Γ:=Γ') as (?&Hfind); eauto. rewrite Hfind; simpl. auto.
          * intros * Hin. eapply incl_map; [|eauto]. eapply st_follows_incl; etransitivity; eauto.
          * intros ? Hin; simpl_In.
            edestruct H7 as (Hin'&_); eauto with senv. inv Hin'.
            take (In _ Γck) and eapply In_InMembers, fst_InMembers, Hincl in it.
            solve_In.
          * simpl_Forall; auto.
          * eapply FEnv.dom_ub_refines; eauto.
          * apply FEnv.union_dom_ub.
            -- eapply FEnv.dom_ub_refines; eauto.
               intros ? Hin. apply in_app_iff. apply Hub1 in Hin; auto.
            -- intros ? (?&Hfind).  apply obind_inversion in Hfind as ((?&?)&Hfind&Hhi).
               apply find_rename_var1 in Hfind as (Hlast&?); subst.
               apply in_app_iff, or_intror.
               apply H9, Hsubin2 in Hlast as (?&Hsub). unfold rename_in_var. rewrite Hsub.
               eapply incl_map; [|eauto]. apply st_follows_incl. etransitivity; eauto.
          * eapply FEnv.dom_ub_refines; eauto.

      - (* automaton (weak) *)
        econstructor; eauto using sem_clock_refines.
        + take (sem_transitions_ck _ _ _ _ _ _) and eapply rename_in_transitions_sem in it; eauto.
          2:{ simpl_Forall.
              eapply wx_exp_incl. 2,3:eauto with lclocking.
              intros * Hv. inv Hv. apply fst_InMembers in H15; simpl_In.
              edestruct H9 as (Hck&_); eauto with senv. }
          rewrite map_map in it. erewrite map_map, map_ext; eauto using sem_ref_sem_transitions.
          intros; destruct_conjs; auto.
        + eapply mmap_values_follows, Forall2_ignore1 in H0; eauto.
          2:{ intros; destruct_conjs.
              destruct b0 as [?(?&[])]; destruct_conjs; repeat inv_bind. eapply delast_scope_st_follows; eauto.
              intros; repeat inv_bind. eapply mmap_st_follows; eauto.
              simpl_Forall. eapply delast_block_st_follows; eauto. }
          simpl_Forall. specialize (H25 k); destruct_conjs. repeat inv_branch. repeat inv_bind.
          take (select_hist _ _ _ _ _) and destruct it as (Hsel1&Hsel2).
          exists ((t + (fun x => obind (List.find (fun '(y, ann) => (isSome ann.(causl_last)) && (x ==b rename_in_var sub y)) Γ') (fun '(x, _) => t0 x))), FEnv.empty _).
          split.
          1:{ split; simpl; [|intros ?? Hfind; inv Hfind].
              intros ?? Hfind. apply FEnv.union4 in Hfind as [Hfind|Hfind].
              - apply Hsel1 in Hfind as (?&Hwhen&Hfind).
                apply Hvar in Hfind as (?&Heq&Hfind).
                do 2 esplit; [|eauto]. now rewrite <-Heq.
              - apply obind_inversion in Hfind as ((?&?)&Heq&Hfind).
                apply Hsel2 in Hfind as (?&Hwhen&Hfind).
                assert (sem_var Hl i0 x4) as Hv by (econstructor; eauto; reflexivity).
                apply find_rename_var1 in Heq as (Hlast&Heq); subst.
                apply Hvarl in Hv; [|auto]. inv Hv.
                do 2 esplit; [|eauto]. now rewrite <-H20.
          }
          constructor.

          destruct s. eapply delast_scope_sem with (st:=x1) (Γck:=Γ') (Hl:=t0) (Hi:=t); eauto.
          * intros ?? Hfind. do 2 esplit; [reflexivity|].
            apply FEnv.union2; auto.
            destruct (obind _ _) eqn:Ho; auto. exfalso.
            apply obind_inversion in Ho as ((?&?)&Ho&Hhi).
            apply find_rename_var1 in Ho as (Hlast&?); subst.
            eapply FEnv.In_refines in Hsel1; [|econstructor; eauto].
            apply Hub1 in Hsel1. simpl_In. simpl_Forall.
            eapply H10, Hsubin2 in Hlast as (?&Hsub). unfold rename_in_var in Hat. rewrite Hsub in Hat.
            eapply st_valid_AtomOrGensym_nIn; eauto using last_not_in_elab_prefs.
          * intros * Hlast Hv. eapply sem_var_union3'.
            inv Hv. econstructor; [|eauto].
            edestruct find_rename_var2 with (Γ:=Γ') as (?&Hfind); eauto. rewrite Hfind; simpl. auto.
          * intros * Hin. eapply incl_map; [|eauto]. eapply st_follows_incl; eauto.
          * intros ? Hin; simpl_In.
            edestruct H9 as (Hin'&_); eauto with senv. inv Hin'.
            take (In _ Γck) and eapply In_InMembers, fst_InMembers, Hincl in it.
            solve_In.
          * simpl_Forall; auto.
          * eapply FEnv.dom_ub_refines; eauto.
          * apply FEnv.union_dom_ub.
            -- eapply FEnv.dom_ub_refines; eauto.
               intros ? Hin. apply in_app_iff. apply Hub1 in Hin; auto.
            -- intros ? (?&Hfind).  apply obind_inversion in Hfind as ((?&?)&Hfind&Hhi).
               apply find_rename_var1 in Hfind as (Hlast&?); subst.
               apply in_app_iff, or_intror.
               apply H10, Hsubin2 in Hlast as (?&Hsub). unfold rename_in_var. rewrite Hsub.
               eapply incl_map; [|eauto]. apply st_follows_incl; auto.
          * eapply FEnv.dom_ub_refines; eauto.
          * intros. destruct_conjs; repeat inv_bind; split.
            2:{ eapply rename_in_transitions_sem; eauto using sem_ref_sem_transitions.
                simpl_Forall; eauto with lclocking. }
            take (mmap _ _ _ = _) and eapply mmap_values_follows, Forall2_ignore1 in it; eauto.
            2:{ intros. eapply delast_block_st_follows; eauto. }
            simpl_Forall. take (delast_block _ _ _ = _) and eapply H in it; eauto.
            -- intros. eapply incl_map; eauto using st_follows_incl.
            -- simpl_Forall; auto.
            -- eapply FEnv.dom_ub_incl; eauto. apply incl_appr', incl_map; eauto using st_follows_incl.
          * intros; destruct_conjs. split; auto. apply Forall_app; auto.

      - (* automaton (strong) *)
        econstructor; eauto using sem_clock_refines.
        + clear H.
          eapply mmap_values_follows, Forall2_ignore1 in H0; eauto.
          2:{ intros; destruct_conjs; repeat inv_bind.
              destruct b0 as [?(?&[])]; destruct_conjs; repeat inv_bind. eapply delast_scope_st_follows; eauto.
              intros; repeat inv_bind. eapply mmap_st_follows; eauto.
              simpl_Forall. eapply delast_block_st_follows; eauto. }
          simpl_Forall; repeat inv_bind.
          specialize (H22 k); destruct_conjs. repeat inv_branch. repeat inv_bind.
          take (select_hist _ _ _ _ _) and destruct it as (Hsel1&Hsel2).
          exists ((t + (fun x => obind (List.find (fun '(y, ann) => (isSome ann.(causl_last)) && (x ==b rename_in_var sub y)) Γ') (fun '(x, _) => t0 x))), FEnv.empty _).
          split.
          1:{ split; simpl; [|intros ?? Hfind; inv Hfind].
              intros ?? Hfind. apply FEnv.union4 in Hfind as [Hfind|Hfind].
              - apply Hsel1 in Hfind as (?&Hwhen&Hfind).
                apply Hvar in Hfind as (?&Heq&Hfind).
                do 2 esplit; [|eauto]. now rewrite <-Heq.
              - apply obind_inversion in Hfind as ((?&?)&Heq&Hfind).
                apply Hsel2 in Hfind as (?&Hwhen&Hfind).
                assert (sem_var Hl i0 x4) as Hv by (econstructor; eauto; reflexivity).
                apply find_rename_var1 in Heq as (Hlast&Heq); subst.
                apply Hvarl in Hv; [|auto]. inv Hv.
                do 2 esplit; [|eauto]. now rewrite <-H24.
          }
          constructor.
          eapply rename_in_transitions_sem; eauto using sem_ref_sem_transitions.
          * intros * Hlast Hv. eapply sem_var_union3'.
            inv Hv. econstructor; [|eauto].
            edestruct find_rename_var2 with (Γ:=Γ') as (?&Hfind); eauto. rewrite Hfind; simpl. auto.
          * intros ?? Hfind. do 2 esplit; [reflexivity|].
            apply FEnv.union2; auto.
            destruct (obind _ _) eqn:Ho; auto. exfalso.
            apply obind_inversion in Ho as ((?&?)&Ho&Hhi).
            apply find_rename_var1 in Ho as (Hlast&?); subst.
            eapply FEnv.In_refines in Hsel1; [|econstructor; eauto].
            apply Hub1 in Hsel1. simpl_In. simpl_Forall.
            eapply H10, Hsubin2 in Hlast as (?&Hsub). unfold rename_in_var in Hat. rewrite Hsub in Hat.
            eapply st_valid_AtomOrGensym_nIn; eauto using last_not_in_elab_prefs.
          * simpl_Forall; eauto with lclocking.
        + eapply mmap_values_follows, Forall2_ignore1 in H0; eauto.
          2:{ intros; destruct_conjs; repeat inv_bind.
              destruct b0 as [?(?&[])]; destruct_conjs; repeat inv_bind. eapply delast_scope_st_follows; eauto.
              intros; repeat inv_bind. eapply mmap_st_follows; eauto.
              simpl_Forall. eapply delast_block_st_follows; eauto. }
          simpl_Forall. specialize (H23 k); destruct_conjs. repeat inv_branch. repeat inv_bind.
          take (select_hist _ _ _ _ _) and destruct it as (Hsel1&Hsel2).
          exists ((t + (fun x => obind (List.find (fun '(y, ann) => (isSome ann.(causl_last)) && (x ==b rename_in_var sub y)) Γ') (fun '(x, _) => t0 x))), FEnv.empty _).
          split.
          1:{ split; simpl; [|intros ?? Hfind; inv Hfind].
              intros ?? Hfind. apply FEnv.union4 in Hfind as [Hfind|Hfind].
              - apply Hsel1 in Hfind as (?&Hwhen&Hfind).
                apply Hvar in Hfind as (?&Heq&Hfind).
                do 2 esplit; [|eauto]. now rewrite <-Heq.
              - apply obind_inversion in Hfind as ((?&?)&Heq&Hfind).
                apply Hsel2 in Hfind as (?&Hwhen&Hfind).
                assert (sem_var Hl i0 x4) as Hv by (econstructor; eauto; reflexivity).
                apply find_rename_var1 in Heq as (Hlast&Heq); subst.
                apply Hvarl in Hv; [|auto]. inv Hv.
                do 2 esplit; [|eauto]. now rewrite <-H25.
          }
          constructor.

          destruct s. eapply delast_scope_sem with (st:=x1) (Γck:=Γ') (Hl:=t0) (Hi:=t); eauto.
          * intros ?? Hfind. do 2 esplit; [reflexivity|].
            apply FEnv.union2; auto.
            destruct (obind _ _) eqn:Ho; auto. exfalso.
            apply obind_inversion in Ho as ((?&?)&Ho&Hhi).
            apply find_rename_var1 in Ho as (Hlast&?); subst.
            eapply FEnv.In_refines in Hsel1; [|econstructor; eauto].
            apply Hub1 in Hsel1. simpl_In. simpl_Forall.
            eapply H10, Hsubin2 in Hlast as (?&Hsub). unfold rename_in_var in Hat. rewrite Hsub in Hat.
            eapply st_valid_AtomOrGensym_nIn; eauto using last_not_in_elab_prefs.
          * intros * Hlast Hv. eapply sem_var_union3'.
            inv Hv. econstructor; [|eauto].
            edestruct find_rename_var2 with (Γ:=Γ') as (?&Hfind); eauto. rewrite Hfind; simpl. auto.
          * intros * Hin. eapply incl_map; [|eauto]. eapply st_follows_incl; eauto.
          * intros ? Hin; simpl_In.
            edestruct H9 as (Hin'&_); eauto with senv. inv Hin'.
            take (In _ Γck) and eapply In_InMembers, fst_InMembers, Hincl in it.
            solve_In.
          * simpl_Forall; auto.
          * eapply FEnv.dom_ub_refines; eauto.
          * apply FEnv.union_dom_ub.
            -- eapply FEnv.dom_ub_refines; eauto.
               intros ? Hin. apply in_app_iff. apply Hub1 in Hin; auto.
            -- intros ? (?&Hfind).  apply obind_inversion in Hfind as ((?&?)&Hfind&Hhi).
               apply find_rename_var1 in Hfind as (Hlast&?); subst.
               apply in_app_iff, or_intror.
               apply H10, Hsubin2 in Hlast as (?&Hsub). unfold rename_in_var. rewrite Hsub.
               eapply incl_map; [|eauto]. apply st_follows_incl; auto.
          * eapply FEnv.dom_ub_refines; eauto.
          * intros; destruct_conjs. repeat inv_bind.
            take (mmap _ _ _ = _) and eapply mmap_values_follows, Forall2_ignore1 in it; eauto.
            2:{ intros. eapply delast_block_st_follows; eauto. }
            simpl_Forall. take (delast_block _ _ _ = _) and eapply H in it; eauto.
            -- intros. eapply incl_map; eauto using st_follows_incl.
            -- simpl_Forall; auto.
            -- eapply FEnv.dom_ub_incl; eauto. apply incl_appr', incl_map; eauto using st_follows_incl.
          * intros; destruct_conjs. apply Forall_app; auto.

      - (* local *)
        constructor. eapply delast_scope_sem; eauto.
        + intros; simpl in *.
          eapply mmap_values_follows, Forall2_ignore1 in H22; eauto.
          2:{ intros. eapply delast_block_st_follows; eauto. }
          simpl_Forall. eapply H in H25; eauto.
          * intros. eapply incl_map; eauto using st_follows_incl.
          * simpl_Forall; auto.
          * eapply FEnv.dom_ub_incl; eauto. apply incl_appr', incl_map; eauto using st_follows_incl.
        + intros. apply Forall_app; auto.
    Qed.

    Lemma delast_node_sem : forall f n ins outs,
        wt_global (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        wc_global (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        Ordered_nodes (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(types) G2.(externs) ((delast_node n)::G2.(nodes))) ->
        sem_node_ck (Global G1.(types) G1.(externs) (n::G1.(nodes))) f ins outs ->
        sem_node_ck (Global G2.(types) G2.(externs) ((delast_node n)::G2.(nodes))) f ins outs.
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
        + intros * _ _ Hrename. now rewrite 2 rename_in_var_empty in Hrename.
        + reflexivity.
        + rewrite map_fst_senv_of_inout. apply n_nodup.
        + rewrite map_fst_senv_of_inout. auto.
        + apply FEnv.dom_dom_ub; auto.
        + unfold st_ids. rewrite init_st_anns, app_nil_r.
          apply FEnv.dom_dom_ub; auto.
        + intros ? (?&Hl). inv Hl.
        + destruct Hwc as (_&_&Hwc). destruct G1; auto.
        + destruct Hwt as (_&_&_&Hwt). destruct G1; auto.
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
    intros [] (Htypes&Hwt).
    induction nodes0; intros * Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      eapply Clocking.delast_global_wc, wc_global_Ordered_nodes in Hwc' ;
        unfold delast_global in Hwc'; simpl in Hwc'.
      apply global_sem_ref_cons with (f:=n_name a)...
      + inv Hwt. inv Hwc. eapply IHnodes0...
      + intros ins outs Hsem; simpl in *.
        change types0 with ((Global types0 externs0 (map delast_node nodes0)).(types)).
        eapply delast_node_sem with (G1:=Global types0 externs0 nodes0)...
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
