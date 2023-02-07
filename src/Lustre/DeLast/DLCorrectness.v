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

    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Section rename_in_exp.

      Variable Γ : static_env.
      Variable H H' : history.

      Hypothesis Hsub : forall x vs,
          IsLast Γ x ->
          sem_var H (Last x) vs ->
          sem_var H' (Var (rename_in_var sub x)) vs.

      Hypothesis Hnsub : forall x vs,
          sem_var H (Var x) vs ->
          sem_var H' (Var x) vs.

      Lemma rename_in_exp_sem : forall bs e vss,
          wx_exp Γ e ->
          sem_exp_ck G H bs e vss ->
          sem_exp_ck G H' bs (rename_in_exp sub e) vss.
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
          sem_equation_ck G H bs eq ->
          sem_equation_ck G H' bs (rename_in_equation sub eq).
      Proof.
        intros * Hwx Hsem. inv Hsem. inv Hwx. simpl in *.
        eapply Seq with (ss:=ss); simpl_Forall; eauto using sem_var_refines, rename_in_exp_sem.
      Qed.

      Corollary rename_in_transitions_sem : forall bs trans default stres,
          Forall (fun '(e, _) => wx_exp Γ e) trans ->
          sem_transitions_ck G H bs trans default stres ->
          sem_transitions_ck G H' bs (map (fun '(e, k) => (rename_in_exp sub e, k)) trans) default stres.
      Proof.
        induction trans; intros * Hwx Hsem; inv Hwx; inv Hsem;
          econstructor; eauto using rename_in_exp_sem.
      Qed.

    End rename_in_exp.

    Fact mask_hist_sub2 Γ : forall k r H H',
      (forall x vs, IsLast Γ x -> sem_var H x vs -> sem_var H' (rename_in_var sub x) vs) ->
      forall x vs, IsLast Γ x -> sem_var (mask_hist k r H) x vs -> sem_var (mask_hist k r H') (rename_in_var sub x) vs.
    Proof.
      intros * Hsub * ? Hv.
      eapply sem_var_mask_inv in Hv as (?&Hv&Heq).
      eapply Hsub, sem_var_mask in Hv; eauto. rewrite Heq; eauto.
    Qed.

    Fact filter_hist_sub2 Γ : forall k r H H',
      (forall x vs, IsLast Γ x -> sem_var H x vs -> sem_var H' (rename_in_var sub x) vs) ->
      forall x vs, IsLast Γ x -> sem_var (fwhen_hist k H r) x vs -> sem_var (fwhen_hist k H' r) (rename_in_var sub x) vs.
    Proof.
      intros * Hsub * ? Hv.
      eapply sem_var_fwhen_inv in Hv as (?&Hv&Heq).
      eapply Hsub, sem_var_fwhen in Hv; eauto. rewrite Heq; eauto.
    Qed.

    Fact select_hist_sub2 Γ : forall e k r H H',
      (forall x vs, IsLast Γ x -> sem_var H x vs -> sem_var H' (rename_in_var sub x) vs) ->
      forall x vs, IsLast Γ x -> sem_var (fselect_hist e k r H) x vs -> sem_var (fselect_hist e k r H') (rename_in_var sub x) vs.
    Proof.
      intros * Hsub * ? Hv.
      eapply sem_var_fselect_inv in Hv as (?&Hv&Heq).
      eapply Hsub, sem_var_fselect in Hv; eauto. rewrite Heq; eauto.
    Qed.

  End rename.

  Import Fresh Facts Tactics.
  Import List.

  Section delast_node_sem.
    Variable G1 : @global complete elab_prefs.
    Variable G2 : @global nolast last_prefs.

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

    Definition st_senv {pref} (st: fresh_st pref _) := senv_of_tyck (st_anns st).

    Lemma fresh_idents_st_senv : forall locs locs' st st',
        fresh_idents locs st = (locs', st') ->
        Permutation (st_senv st') (st_senv st ++ @senv_of_decls exp (map (fun '(_, x, (ty, ck, e)) => (x, (ty, ck, xH, None))) locs')).
    Proof.
      unfold fresh_idents.
      induction locs as [|(?&(?&?)&?)]; intros * Fresh; repeat inv_bind; simpl.
      - now rewrite app_nil_r.
      - apply fresh_ident_anns in H.
        apply IHlocs in H0. rewrite H0.
        unfold st_senv. rewrite H; simpl.
        apply Permutation_middle.
    Qed.

    Fact IsVar_st_senv {pref} : forall x (st: fresh_st pref _),
        IsVar (st_senv st) x <-> In x (st_ids st).
    Proof.
      unfold st_senv, senv_of_tyck.
      split; intros * Hv; [inv Hv|econstructor]; solve_In.
    Qed.

    (** Central correctness lemma                                              *)

    Lemma delast_scope_sem {A} P_nd P_good P_wc P_wt P_sem1 (P_sem2: _ -> _ -> Prop) f_dl f_add :
      forall locs (blk: A) sub Γck Γty s' st st' bs Hi Hi2,
        (forall x vs, sem_var Hi (Var x) vs -> sem_var Hi2 (Var x) vs) ->
        (forall x vs, IsLast Γck x -> sem_var Hi (Last x) vs -> sem_var Hi2 (Var (rename_in_var sub x)) vs) ->
        (forall x, Env.In x sub -> IsLast Γty x) ->
        (forall x, IsLast Γck x -> Env.In x sub) ->
        (forall x y, Env.find x sub = Some y -> In y (st_ids st)) ->
        (forall x1 x2, IsLast Γck x1 -> IsLast Γck x2 -> rename_in_var sub x1 = rename_in_var sub x2 -> x1 = x2) ->
        incl (map fst Γck) (map fst Γty) ->
        NoDupScope P_nd (map fst Γty) (Scope locs blk) ->
        Forall (AtomOrGensym elab_prefs) (map fst Γty) ->
        GoodLocalsScope P_good elab_prefs (Scope locs blk) ->
        dom_ub Hi Γty ->
        dom_ub Hi2 (Γty ++ st_senv st) ->
        wc_scope P_wc G1 Γck (Scope locs blk) ->
        wt_scope P_wt G1 Γty (Scope locs blk) ->
        sem_scope_ck (sem_exp_ck G1) P_sem1 Hi bs (Scope locs blk) ->
        delast_scope f_dl f_add sub (Scope locs blk) st = (s', st') ->
        (forall sub Γck Γty blk' st st' Hi Hi2,
            (forall x vs, sem_var Hi (Var x) vs -> sem_var Hi2 (Var x) vs) ->
            (forall x vs, IsLast Γck x -> sem_var Hi (Last x) vs -> sem_var Hi2 (Var (rename_in_var sub x)) vs) ->
            (forall x, Env.In x sub -> IsLast Γty x) ->
            (forall x, IsLast Γck x -> Env.In x sub) ->
            (forall x y, Env.find x sub = Some y -> In y (st_ids st)) ->
            (forall x1 x2, IsLast Γck x1 -> IsLast Γck x2 -> rename_in_var sub x1 = rename_in_var sub x2 -> x1 = x2) ->
            incl (map fst Γck) (map fst Γty) ->
            P_nd (map fst Γty) blk ->
            Forall (AtomOrGensym elab_prefs) (map fst Γty) ->
            P_good blk ->
            dom_ub Hi Γty ->
            dom_ub Hi2 (Γty++st_senv st) ->
            P_wc Γck blk ->
            P_wt Γty blk ->
            P_sem1 Hi blk ->
            f_dl sub blk st = (blk', st') ->
            P_sem2 Hi2 blk') ->
        (forall blks1 blks2 Hi,
            Forall (sem_block_ck G2 Hi bs) blks1 ->
            P_sem2 Hi blks2 ->
            P_sem2 Hi (f_add blks1 blks2)) ->
        sem_scope_ck (sem_exp_ck G2) P_sem2 Hi2 bs s'.
    Proof.
      intros * Hvar Hvarl Hsubin1 Hsubin2 Hsubin3 Hinj Hincl Hnd2 Hat Hgood Hub1 (* Hlb1 *) Hub2 (* Hlb2 *) Hwc Hwt (* Hsc *) Hsem Hdl Hind Hadd;
        inv Hnd2; inv Hgood; inv Hwc; inv Hwt; inv Hsem; repeat inv_bind; simpl. subst Γ' Γ'0.
      assert (forall y, Env.In y (Env.from_list (map fst x)) <-> IsLast (senv_of_decls locs) y) as Hsubin4.
      { intros *. rewrite Env.In_from_list.
        eapply fresh_idents_InMembers in H. erewrite <-H, fst_InMembers.
        split; intros * Hin.
        - simpl_In. econstructor; solve_In. simpl. congruence.
        - inv Hin. simpl_In. destruct o as [(?&?)|]; simpl in *; try congruence.
          solve_In. auto. }

      assert (NoDupMembers (map (fun '(x, lx, _) => (Var lx, or_default (Streams.const absent) (Hi' (Last x)))) x)) as Hndl1.
      { eapply fresh_idents_NoDup in H; eauto.
        rewrite fst_NoDupMembers, map_map in H. erewrite fst_NoDupMembers, map_map, map_ext, <-map_map.
        eapply FinFun.Injective_map_NoDup; [|eauto]. 2:instantiate (1:=Var); intros; destruct_conjs; reflexivity.
        intros ?? Eq; now inv Eq. }
      remember (fun x => match x with Var x => Hi' (Var x) | _ => None end) as Hi''.
      assert (forall x, FEnv.In (Var x) Hi'' <-> FEnv.In (Var x) Hi') as Dom''.
      { intros. split; intros In; inv In; econstructor; eauto. }
      assert (forall y,
                 FEnv.In y Hi'' ->
                 ~FEnv.In y (FEnv.of_list (map (fun '(x, lx, _) => (Var lx, or_default (Streams.const absent) (Hi' (Last x)))) x))) as Hndl2.
      { intros * Hin Hinm. rewrite FEnv.of_list_In, fst_InMembers in Hinm. simpl_In.
        assert (Hf:=H). eapply fresh_idents_prefixed in H. simpl_Forall; subst.
        eapply H11, IsVar_senv_of_decls in Hin. simpl_In. simpl_Forall.
        take (AtomOrGensym _ _) and apply contradict_AtomOrGensym in it; eauto using last_not_in_elab_prefs.
      }
      assert (forall y,
                 FEnv.In y Hi2 ->
                 ~ FEnv.In y (Hi'' + FEnv.of_list (map (fun '(x, lx, _) => (Var lx, or_default (Streams.const absent) (Hi' (Last x)))) x))) as Hndl3.
      { intros * Hin1 Hin2. apply FEnv.union_In in Hin2 as [Hin2|Hin2].
        - subst. inv Hin2. cases. take (Hi' _ = Some _) and apply FEnv.find_In in it as Hin2.
          apply H11, IsVar_senv_of_decls in Hin2.
          apply Hub2, IsVar_app in Hin1 as [Hin1|Hin1].
          + take (forall x, InMembers x locs -> ~_) and eapply it; eauto. now apply IsVar_fst.
          + inv Hin1. simpl_In. simpl_Forall.
            specialize (st_valid_prefixed st) as Hvalid. unfold st_ids in Hvalid. simpl_Forall; subst.
            apply contradict_AtomOrGensym in H2; eauto using last_not_in_elab_prefs.
        - apply FEnv.of_list_In in Hin2. simpl_In.
          apply Hub2, IsVar_app in Hin1 as [Hin1|Hin1]; inv Hin1; simpl_In.
          + eapply fresh_idents_prefixed in H. simpl_Forall; subst.
            eapply contradict_AtomOrGensym in Hat; eauto using last_not_in_elab_prefs.
          + eapply fresh_idents_nIn_ids in H. simpl_Forall; eauto.
            eapply H; unfold st_ids; solve_In.
      }

      remember (Hi'' + (FEnv.of_list (map (fun '(x, lx, _) => (Var lx, or_default (Streams.const absent) (Hi' (Last x)))) x))) as Hi2'.
      assert (FEnv.refines (@EqSt _) Hi'' Hi2') as Href1.
      { intros ?? Hv.
        assert (sem_var Hi2' x2 v) as Hv'. 2:inv Hv'; eauto. subst.
        rewrite sem_var_disj_union; eauto. left.
        econstructor; eauto. reflexivity.
      }
      assert (forall x vs, sem_var (Hi + Hi'') (Var x) vs -> sem_var (Hi2 + Hi2') (Var x) vs) as Href2.
      { intros ?? Hv.
        rewrite sem_var_disj_union; eauto.
        eapply sem_var_union in Hv as [Hv|Hv]; eauto using sem_var_refines. }
       assert (forall x vs, sem_var (Hi + Hi') (Var x) vs -> sem_var (Hi2 + Hi2') (Var x) vs) as Hvar'.
      { intros ?? Hv. subst. eapply Href2.
        inv Hv. econstructor; eauto. }

      assert (forall y vs,
                 IsLast (Γck ++ senv_of_decls locs) y ->
                 sem_var (Hi + Hi') (Last y) vs ->
                 sem_var (Hi2 + Hi2') (Var (rename_in_var (Env.union sub (Env.from_list (map fst x))) y)) vs) as Hvarl'.
      { intros * Hin Hv. subst Hi2'.
        rewrite sem_var_disj_union, sem_var_disj_union; eauto.
        apply IsLast_app in Hin as [Hin|Hin]; simpl_In; subst.
        - apply sem_var_union in Hv as [Hv|Hv]; auto.
          2:{ exfalso. eapply sem_var_In, H11, IsLast_senv_of_decls in Hv. inv Hin.
              eapply H4; eauto. apply Hincl; solve_In. }
          left. rewrite not_in_union_rename2.
          2:{ intros contra. rewrite Env.In_from_list, fst_InMembers in contra. simpl_In.
              eapply fresh_idents_In' in H; eauto. simpl_In.
              inv Hin. eapply H4; eauto using In_InMembers. eapply Hincl; solve_In. }
          eapply Hvarl; eauto.
        - inv Hin. simpl_In. destruct o as [(?&?)|]; simpl in *; try congruence.
          apply sem_var_union in Hv as [Hv|Hv]; auto.
          1:{ exfalso. eapply sem_var_In, Hub1 in Hv. inv Hv.
              eapply H4; eauto using In_InMembers. solve_In. }
          right; right.
          eapply fresh_idents_In_rename in H. 3:solve_In; simpl; eauto.
          2:{ apply NoDupMembers_map_filter; auto.
              intros; destruct_conjs; destruct o as [(?&?)|]; simpl; auto. }
          erewrite not_in_union_rename1.
          2:{ intro contra. apply Hsubin1 in contra. inv contra.
              eapply H4; eauto using In_InMembers, in_or_app. solve_In. }
          inv Hv. econstructor; [|eauto].
          apply FEnv.of_list_In_find; auto. solve_In.
          take (Hi' (Last _) = _) and rewrite it; reflexivity.
      }
      assert (forall x1, FEnv.In (Var x1) Hi2'
                    <-> IsVar (senv_of_decls (locs++map (fun '(_, lx, (ty, ck, _)) => (lx, (ty, ck, xH, None))) x)) x1
             ) as Hdom2'.
      { subst. intros. destruct H11 as (D1&_).
        rewrite FEnv.union_In, FEnv.of_list_In, Dom'', D1, 2 IsVar_senv_of_decls, InMembers_app.
        apply or_iff_compat_l.
        clear - x2. split; intros * Hin; solve_In.
      }

      assert (var_history (Hi + Hi') ⊑ var_history (Hi2 + Hi2')) as Hrefvar.
      { subst. etransitivity; [|eauto using var_history_refines'].
        intros ?? Find. unfold var_history, FEnv.union in *.
        do 2 esplit; [|eauto]. reflexivity. }

      eapply Sscope with (Hi':=Hi2').
      4:apply Hadd.
      - subst. intros. destruct H11 as (D1&D2).
        split; intros ?; clear - Dom'' D1 D2.
        + rewrite FEnv.union_In, Dom'', D1, FEnv.of_list_In, 2 IsVar_senv_of_decls, InMembers_app, 4 fst_InMembers, 3 map_map.
          split; (intros [|]; [left|right]); solve_In.
        + rewrite FEnv.union_In, FEnv.of_list_In.
          unfold senv_of_decls. repeat rewrite map_app. repeat rewrite IsLast_app.
          split; [intros [Hin|Hin]; [left|right]|intros [Hin|Hin]; [left|right]]; try inv Hin; simpl_In; congruence.
      - apply Forall_app; split; simpl_Forall. 1,2:constructor.
      - take (sc_vars (senv_of_decls _) _ _) and destruct it as (Hsc1&Hsc2).
        split; intros * Hck; inv Hck; simpl_In; rewrite in_app_iff in *;
          destruct Hin as [Hin|Hin]; simpl_In;
          try (intros Hca; inv Hca; simpl_In;
               take (In _ (_ ++ _)) and apply in_app_iff in it as [|]; simpl_In);
          try congruence.
        + intros Hv. eapply sem_clock_refines, Hsc1; eauto.
          * econstructor. clear - Hin0; solve_In. eauto.
          * eapply sem_var_history, sem_var_refines', sem_var_history; eauto.
            apply FEnv.union_In, or_intror, H11. econstructor; clear - Hin0; solve_In.
        + eapply fresh_idents_In'_rename in H as (?&?); eauto.
          2:{ apply NoDupMembers_map_filter; auto.
              intros; destruct_conjs; destruct o as [(?&?)|]; simpl; auto. }
          simpl_In.
          intros Hv. eapply sem_clock_refines, Hsc2; eauto.
          1,2:econstructor; clear - Hin; solve_In; simpl; eauto. congruence.
          assert (exists vs, sem_var (Hi + Hi') (Last i0) vs) as (vs&Hv').
          { assert (FEnv.In (Last i0) (Hi + Hi')) as (?&?); [|esplit; econstructor; eauto; reflexivity].
            apply FEnv.union_In, or_intror, H11.
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
        simpl_Forall. inversion_clear H14 as [|????????? He Hv Hfby Hvl].
        eapply Seq with (ss:=[[vs]]); simpl; repeat constructor.
        + eapply Sfby with (s0ss:=[[vs0]]) (sss:=[[vs1]]); simpl.
          1-3:repeat constructor; simpl; eauto.
          * eapply rename_in_exp_sem; eauto using sem_ref_sem_exp.
            simpl_Forall; eauto with lclocking.
          * eapply Hvar', sem_var_refines; [|eauto].
            apply FEnv.union_refines4', EqStrel_Reflexive.
        + erewrite <-not_in_union_rename1 with (sub:=sub).
          2:{ intro contra. apply Hsubin1 in contra. inv contra.
              eapply H4; eauto using In_InMembers, in_or_app. solve_In. }
          eapply Hvarl'; eauto.
          * apply IsLast_app, or_intror. econstructor; solve_In. simpl; congruence.
          * eapply sem_var_refines; eauto.
            apply FEnv.union_refines4', EqStrel_Reflexive.
      - eapply Hind with (st:=x0) (Γck:=Γck++senv_of_decls _) (Γty:=Γty++senv_of_decls _); eauto.
        + intros * Hin. rewrite IsLast_app. apply Env.union_In in Hin as [|Hin]; eauto.
          right. apply Hsubin4; auto.
        + intros * Hin. apply Env.union_In. apply IsLast_app in Hin as [|]; eauto.
          right. apply Hsubin4; auto.
        + intros * Hfind. apply Env.union_find4 in Hfind as [Hfind|Hfind].
          * eapply incl_map; eauto using st_follows_incl, fresh_idents_st_follows.
          * apply Env.from_list_find_In in Hfind. simpl_In.
            apply fresh_idents_In_ids in H. simpl_Forall. simpl_In. do 2 esplit; eauto. auto.
        + intros * Hl1 Hl2 Hrename.
          assert (forall y, IsLast Γck y -> ~Env.In y (Env.from_list (map fst x))) as Hdisj1.
          { intros * Hlast Hin2. inv Hlast.
            eapply Env.In_from_list, fresh_idents_InMembers in Hin2; eauto.
            simpl_In. take (forall x, InMembers x locs -> ~_) and eapply it; eauto using In_InMembers. apply Hincl. solve_In.
          }
          assert (forall y, IsLast (senv_of_decls locs) y -> ~ Env.In y sub) as Hdisj2.
          { intros * Hin1 Hin2. apply Hsubin1 in Hin2. inv Hin2.
            inv Hin1. simpl_In.
            take (forall x, InMembers x locs -> ~_) and eapply it; eauto using In_InMembers. solve_In.
          }
          assert (forall y, IsLast Γck y -> In (rename_in_var sub y) (st_ids st)) as Hst1.
          { intros * Hlast. apply Hsubin2 in Hlast as (?&Hfind).
            unfold rename_in_var. rewrite Hfind; eauto. }
          assert (forall y, IsLast (senv_of_decls locs) y -> ~In (rename_in_var (Env.from_list (map fst x)) y) (st_ids st)) as Hst2.
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
        + rewrite map_app, map_fst_senv_of_decls; auto.
        + rewrite map_app, map_fst_senv_of_decls. apply Forall_app; split; simpl_Forall; auto.
        + eapply local_hist_dom_ub in Hub1; eauto.
        +{ subst. clear - H Hub2 Hdom2' H6.
           split; intros ?; rewrite FEnv.union_In;
             [rewrite Hdom2'|rewrite FEnv.union_In, 2 IsLast_app, FEnv.of_list_In].
           - intros [In|In].
             + apply Hub2 in In. repeat rewrite IsVar_app in *.
               destruct In as [|In]; auto. right.
               eapply IsVar_incl; eauto. eapply incl_map, st_follows_incl, fresh_idents_st_follows; eauto.
             + repeat simpl_app. repeat rewrite IsVar_app in *.
               destruct In as [In|In]; auto. do 2 right.
               inv In; simpl_In.
               eapply fresh_idents_In_ids in H. simpl_Forall. simpl_In.
               unfold st_senv, senv_of_tyck. econstructor; solve_In.
           - intros [In|[In|In]].
             + apply Hub2, IsLast_app in In as [|In]; auto.
               inv In. simpl_In. congruence.
             + inv In. congruence.
             + simpl_In.
         }
    Qed.

    Ltac inv_branch := (Syn.inv_branch || Ty.inv_branch || Cl.inv_branch || Sem.inv_branch || LCS.inv_branch).

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

    Lemma delast_block_sem : forall blk sub Γck Γty blk' st st' bs Hi Hi',
        (forall x vs, sem_var Hi (Var x) vs -> sem_var Hi' (Var x) vs) ->
        (forall x vs, IsLast Γck x -> sem_var Hi (Last x) vs -> sem_var Hi' (Var (rename_in_var sub x)) vs) ->
        (forall x, Env.In x sub -> IsLast Γty x) ->
        (forall x, IsLast Γck x -> Env.In x sub) ->
        (forall x y, Env.find x sub = Some y -> In y (st_ids st)) ->
        (forall x1 x2, IsLast Γck x1 -> IsLast Γck x2 -> rename_in_var sub x1 = rename_in_var sub x2 -> x1 = x2) ->
        incl (map fst Γck) (map fst Γty) ->
        NoDupLocals (map fst Γty) blk ->
        Forall (AtomOrGensym elab_prefs) (map fst Γty) ->
        GoodLocals elab_prefs blk ->
        dom_ub Hi Γty ->
        dom_ub Hi' (Γty++st_senv st) ->
        wc_block G1 Γck blk ->
        wt_block G1 Γty blk ->
        sem_block_ck G1 Hi bs blk ->
        delast_block sub blk st = (blk', st') ->
        sem_block_ck G2 Hi' bs blk'.
    Proof with eauto with datatypes.
      Opaque delast_scope.
      induction blk using block_ind2;
        intros * Vars Lasts Hsubin1 Hsubin2 Hsubin3 Hinj Hincl Hnd2 Hat Hgood Hub1 Hub2 Hwc Hwt Hsem Hdl;
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
        eapply H with (Hi:=mask_hist _ _ Hi) in H12; eauto using refines_mask, mask_hist_sub2.
        + intros * Hv. eapply sem_var_mask_inv in Hv as (?&?&Eq).
          rewrite Eq; eauto using sem_var_mask.
        + intros * Hl Hv. eapply sem_var_mask_inv in Hv as (?&?&Eq).
          rewrite Eq; eauto using sem_var_mask.
        + intros * Hin. eapply incl_map; eauto. apply st_follows_incl; auto.
        + simpl_Forall; auto.
        + apply dom_ub_map; auto.
        + eapply dom_ub_map, dom_ub_incl; eauto.
          apply incl_appr'. apply incl_map, st_follows_incl; auto.

      - (* switch *)
        econstructor; eauto using rename_in_exp_sem, sem_ref_sem_exp with lclocking.
        + rewrite Typing.rename_in_exp_typeof; auto.
        + eapply mmap_values_follows, Forall2_ignore1 in H0; eauto.
          2:{ intros; destruct_conjs; repeat inv_bind.
              destruct b0. repeat inv_bind.
              eapply mmap_st_follows; eauto.
              simpl_Forall. eapply delast_block_st_follows; eauto. }
          simpl_Forall. repeat inv_branch. repeat inv_bind.
          take (when_hist _ _ _ _) and rename it into When.
          exists (fun x => match x with
                   | Var x => match List.find (fun '(y, ann) => (isSome ann.(causl_last)) && (x ==b rename_in_var sub y)) Γ' with
                             | Some (y, _) => x0 (Last y)
                             | None => x0 (Var x)
                             end
                   | Last _ => None
                   end).
          split.
          1:{ intros ?? Hfind; inv Hfind. cases_eqn Eq; subst; destruct_conjs.
              - apply find_rename_var1 in Eq0 as (Il&?); subst.
                eapply When in H20 as (?&W&Hlast).
                assert (sem_var Hi (Last i) x4) as Hlast' by (econstructor; eauto; reflexivity).
                eapply Lasts in Hlast'; [|eauto]. inv Hlast'.
                do 2 esplit; [|eauto]. now take (_ ≡ _) and rewrite <-it.
              - eapply When in H20 as (?&W&Hvar).
                assert (sem_var Hi (Var x5) x4) as Hvar' by (econstructor; eauto; reflexivity).
                eapply Vars in Hvar'. inv Hvar'.
                do 2 esplit; [|eauto]. now take (_ ≡ _) and rewrite <-it.
          }
          constructor.
          eapply mmap_values_follows, Forall2_ignore1 in H1; eauto.
          2:{ intros. eapply delast_block_st_follows; eauto. }
          simpl_Forall.
          eapply H with (Hi:=x0) (Γck:=Γ') in H21; eauto.
          * intros ?? Hvar. inv Hvar. econstructor; [|eauto].
            cases_eqn Eq; subst.
            apply find_rename_var1 in Eq as (Hlast&?); subst. exfalso.
            eapply FEnv.In_refines in When ; [|econstructor; eauto].
            apply Hub1 in When. inv When. simpl_In. simpl_Forall.
            eapply H9, Hsubin2 in Hlast as (?&Hsub). unfold rename_in_var in Hat. rewrite Hsub in Hat.
            eapply st_valid_AtomOrGensym_nIn; eauto using last_not_in_elab_prefs.
          * intros * Hlast Hv. inv Hv. econstructor; [|eauto].
            cases_eqn Eq; subst.
            -- apply find_rename_var1 in Eq as (?&Sub).
               eapply Hinj in Sub; subst; eauto.
            -- exfalso. inv Hlast.
               eapply find_none in Eq; [|eauto]. simpl in *.
               destruct (causl_last _); try congruence. rewrite equiv_decb_refl in Eq. inv Eq.
          * intros * Hin. eapply incl_map; [|eauto]. eapply st_follows_incl; etransitivity; eauto.
          * intros ? Hin; simpl_In.
            edestruct H7 as (Hin'&_); eauto with senv. inv Hin'.
            take (In _ Γck) and eapply In_InMembers, fst_InMembers, Hincl in it.
            solve_In.
          * simpl_Forall; auto.
          * eapply dom_ub_refines; eauto.
          * split; intros ? In; inv In; cases_eqn Eq; subst; try congruence.
            -- apply find_rename_var1 in Eq as (?&Eq); subst.
               apply IsVar_app. right. apply IsVar_st_senv.
               do 2 (eapply incl_map; [eauto using st_follows_incl|]).
               eapply H9, Hsubin2 in H26 as (?&Sub).
               eapply Hsubin3. unfold rename_in_var. now rewrite Sub.
            -- eapply FEnv.find_In, FEnv.In_refines, Hub1 in H25; [|eauto].
               apply IsVar_app; auto.

      - (* automaton (weak) *)
        econstructor; eauto using sem_clock_refines, var_history_refines'.
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
          take (select_hist _ _ _ _ _) and rename it into Select.
          exists (fun x => match x with
                   | Var x => match List.find (fun '(y, ann) => (isSome ann.(causl_last)) && (x ==b rename_in_var sub y)) Γ' with
                             | Some (y, _) => x0 (Last y)
                             | None => x0 (Var x)
                             end
                   | Last _ => None
                   end).
          split.
          1:{ intros ?? Hfind; inv Hfind. cases_eqn Eq; subst; destruct_conjs.
              - apply find_rename_var1 in Eq0 as (Il&?); subst.
                eapply Select in H15 as (?&W&Hlast).
                assert (sem_var Hi (Last i0) x4) as Hlast' by (econstructor; eauto; reflexivity).
                eapply Lasts in Hlast'; [|eauto]. inv Hlast'.
                do 2 esplit; [|eauto]. now take (_ ≡ _) and rewrite <-it.
              - eapply Select in H15 as (?&W&Hvar).
                assert (sem_var Hi (Var x5) x4) as Hvar' by (econstructor; eauto; reflexivity).
                eapply Vars in Hvar'. inv Hvar'.
                do 2 esplit; [|eauto]. now take (_ ≡ _) and rewrite <-it.
          }
          constructor.

          destruct s. eapply delast_scope_sem with (st:=x1) (Γck:=Γ') (Hi:=x0); eauto.
          * intros ?? Hvar. inv Hvar. econstructor; [|eauto].
            cases_eqn Eq; subst.
            apply find_rename_var1 in Eq0 as (Hlast&?); subst. exfalso.
            eapply FEnv.In_refines in Select; [|econstructor; eauto].
            apply Hub1 in Select. inv Select. simpl_In. simpl_Forall.
            eapply H10, Hsubin2 in Hlast as (?&Hsub). unfold rename_in_var in Hat. rewrite Hsub in Hat.
            eapply st_valid_AtomOrGensym_nIn; eauto using last_not_in_elab_prefs.
          * intros * Hlast Hv. inv Hv. econstructor; [|eauto].
            cases_eqn Eq; subst.
            -- apply find_rename_var1 in Eq0 as (?&Sub).
               eapply Hinj in Sub; subst; eauto.
            -- exfalso. inv Hlast.
               eapply find_none in Eq0; [|eauto]. simpl in *.
               destruct (causl_last _); try congruence. rewrite equiv_decb_refl in Eq0. inv Eq0.
          * intros * Hin. eapply incl_map; [|eauto]. eapply st_follows_incl; eauto.
          * intros ? Hin; simpl_In.
            edestruct H9 as (Hin'&_); eauto with senv. inv Hin'.
            take (In _ Γck) and eapply In_InMembers, fst_InMembers, Hincl in it.
            solve_In.
          * simpl_Forall; auto.
          * eapply dom_ub_refines; eauto.
          * split; intros ? In; inv In; cases_eqn Eq; subst; try congruence.
            -- apply find_rename_var1 in Eq as (?&Eq); subst.
               apply IsVar_app. right. apply IsVar_st_senv.
               do 1 (eapply incl_map; [eauto using st_follows_incl|]).
               eapply H10, Hsubin2 in H15 as (?&Sub).
               eapply Hsubin3. unfold rename_in_var. now rewrite Sub.
            -- eapply FEnv.find_In, FEnv.In_refines, Hub1 in H8; [|eauto].
               apply IsVar_app; auto.
          * intros. destruct_conjs; repeat inv_bind; split.
            2:{ eapply rename_in_transitions_sem; eauto using sem_ref_sem_transitions.
                simpl_Forall; eauto with lclocking. }
            take (mmap _ _ _ = _) and eapply mmap_values_follows, Forall2_ignore1 in it; eauto.
            2:{ intros. eapply delast_block_st_follows; eauto. }
            simpl_Forall. take (delast_block _ _ _ = _) and eapply H in it; eauto.
            -- intros. eapply incl_map; eauto using st_follows_incl.
            -- simpl_Forall; auto.
            -- eapply dom_ub_incl; eauto. apply incl_appr', incl_map; eauto using st_follows_incl.
          * intros; destruct_conjs. split; auto. apply Forall_app; auto.

      - (* automaton (strong) *)
        econstructor; eauto using sem_clock_refines, var_history_refines'.
        + clear H.
          eapply mmap_values_follows, Forall2_ignore1 in H0; eauto.
          2:{ intros; destruct_conjs; repeat inv_bind.
              destruct b0 as [?(?&[])]; destruct_conjs; repeat inv_bind. eapply delast_scope_st_follows; eauto.
              intros; repeat inv_bind. eapply mmap_st_follows; eauto.
              simpl_Forall. eapply delast_block_st_follows; eauto. }
          simpl_Forall; repeat inv_bind.
          specialize (H22 k); destruct_conjs. repeat inv_branch. repeat inv_bind.
          take (select_hist _ _ _ _ _) and rename it into Select.
          exists (fun x => match x with
                   | Var x => match List.find (fun '(y, ann) => (isSome ann.(causl_last)) && (x ==b rename_in_var sub y)) Γ' with
                             | Some (y, _) => x0 (Last y)
                             | None => x0 (Var x)
                             end
                   | Last _ => None
                   end).
          split.
          1:{ intros ?? Hfind; inv Hfind. cases_eqn Eq; subst; destruct_conjs.
              - apply find_rename_var1 in Eq0 as (Il&?); subst.
                eapply Select in H11 as (?&W&Hlast).
                assert (sem_var Hi (Last i0) x4) as Hlast' by (econstructor; eauto; reflexivity).
                eapply Lasts in Hlast'; [|eauto]. inv Hlast'.
                do 2 esplit; [|eauto]. now take (_ ≡ _) and rewrite <-it.
              - eapply Select in H11 as (?&W&Hvar).
                assert (sem_var Hi (Var x5) x4) as Hvar' by (econstructor; eauto; reflexivity).
                eapply Vars in Hvar'. inv Hvar'.
                do 2 esplit; [|eauto]. now take (_ ≡ _) and rewrite <-it.
          }
          constructor.
          eapply rename_in_transitions_sem with (Γ:=Γ'). 4:eauto using sem_ref_sem_transitions.
          * intros * Hlast Hv. inv Hv. econstructor; [|eauto].
            cases_eqn Eq; subst.
            -- apply find_rename_var1 in Eq as (?&Sub).
               eapply Hinj in Sub; subst; eauto.
            -- exfalso. inv Hlast.
               eapply find_none in Eq; [|eauto]. simpl in *.
               destruct (causl_last _); try congruence. rewrite equiv_decb_refl in Eq. inv Eq.
          * intros ?? Hvar. inv Hvar. econstructor; [|eauto].
            cases_eqn Eq; subst.
            apply find_rename_var1 in Eq as (Hlast&?); subst. exfalso.
            eapply FEnv.In_refines in Select; [|econstructor; eauto].
            apply Hub1 in Select. inv Select. simpl_In. simpl_Forall.
            eapply H10, Hsubin2 in Hlast as (?&Hsub). unfold rename_in_var in Hat. rewrite Hsub in Hat.
            eapply st_valid_AtomOrGensym_nIn; eauto using last_not_in_elab_prefs.
          * simpl_Forall; eauto with lclocking.
        + eapply mmap_values_follows, Forall2_ignore1 in H0; eauto.
          2:{ intros; destruct_conjs; repeat inv_bind.
              destruct b0 as [?(?&[])]; destruct_conjs; repeat inv_bind. eapply delast_scope_st_follows; eauto.
              intros; repeat inv_bind. eapply mmap_st_follows; eauto.
              simpl_Forall. eapply delast_block_st_follows; eauto. }
          simpl_Forall. specialize (H23 k); destruct_conjs. repeat inv_branch. repeat inv_bind.
          take (select_hist _ _ _ _ _) and rename it into Select.
          exists (fun x => match x with
                   | Var x => match List.find (fun '(y, ann) => (isSome ann.(causl_last)) && (x ==b rename_in_var sub y)) Γ' with
                             | Some (y, _) => x0 (Last y)
                             | None => x0 (Var x)
                             end
                   | Last _ => None
                   end).
          split.
          1:{ intros ?? Hfind; inv Hfind. cases_eqn Eq; subst; destruct_conjs.
              - apply find_rename_var1 in Eq0 as (Il&?); subst.
                eapply Select in H14 as (?&W&Hlast).
                assert (sem_var Hi (Last i0) x4) as Hlast' by (econstructor; eauto; reflexivity).
                eapply Lasts in Hlast'; [|eauto]. inv Hlast'.
                do 2 esplit; [|eauto]. now take (_ ≡ _) and rewrite <-it.
              - eapply Select in H14 as (?&W&Hvar).
                assert (sem_var Hi (Var x5) x4) as Hvar' by (econstructor; eauto; reflexivity).
                eapply Vars in Hvar'. inv Hvar'.
                do 2 esplit; [|eauto]. now take (_ ≡ _) and rewrite <-it.
          }
          constructor.

          destruct s. eapply delast_scope_sem with (st:=x1) (Γck:=Γ') (Hi:=x0); eauto.
          * intros ?? Hvar. inv Hvar. econstructor; [|eauto].
            cases_eqn Eq; subst.
            apply find_rename_var1 in Eq0 as (Hlast&?); subst. exfalso.
            eapply FEnv.In_refines in Select; [|econstructor; eauto].
            apply Hub1 in Select. inv Select. simpl_In. simpl_Forall.
            eapply H10, Hsubin2 in Hlast as (?&Hsub). unfold rename_in_var in Hat. rewrite Hsub in Hat.
            eapply st_valid_AtomOrGensym_nIn; eauto using last_not_in_elab_prefs.
          * intros * Hlast Hv. inv Hv. econstructor; [|eauto].
            cases_eqn Eq; subst.
            -- apply find_rename_var1 in Eq0 as (?&Sub).
               eapply Hinj in Sub; subst; eauto.
            -- exfalso. inv Hlast.
               eapply find_none in Eq0; [|eauto]. simpl in *.
               destruct (causl_last _); try congruence. rewrite equiv_decb_refl in Eq0. inv Eq0.
          * intros * Hin. eapply incl_map; [|eauto]. eapply st_follows_incl; eauto.
          * intros ? Hin; simpl_In.
            edestruct H9 as (Hin'&_); eauto with senv. inv Hin'.
            take (In _ Γck) and eapply In_InMembers, fst_InMembers, Hincl in it.
            solve_In.
          * simpl_Forall; auto.
          * eapply dom_ub_refines; eauto.
          * split; intros ? In; inv In; cases_eqn Eq; subst; try congruence.
            -- apply find_rename_var1 in Eq as (?&Eq); subst.
               apply IsVar_app. right. apply IsVar_st_senv.
               do 1 (eapply incl_map; [eauto using st_follows_incl|]).
               eapply H10, Hsubin2 in H14 as (?&Sub).
               eapply Hsubin3. unfold rename_in_var. now rewrite Sub.
            -- eapply FEnv.find_In, FEnv.In_refines, Hub1 in H11; [|eauto].
               apply IsVar_app; auto.
          * intros; destruct_conjs. repeat inv_bind.
            take (mmap _ _ _ = _) and eapply mmap_values_follows, Forall2_ignore1 in it; eauto.
            2:{ intros. eapply delast_block_st_follows; eauto. }
            simpl_Forall. take (delast_block _ _ _ = _) and eapply H in it; eauto.
            -- intros. eapply incl_map; eauto using st_follows_incl.
            -- simpl_Forall; auto.
            -- eapply dom_ub_incl; eauto. apply incl_appr', incl_map; eauto using st_follows_incl.
          * intros; destruct_conjs. apply Forall_app; auto.

      - (* local *)
        constructor. eapply delast_scope_sem; eauto.
        + intros; simpl in *.
          eapply mmap_values_follows, Forall2_ignore1 in H21; eauto.
          2:{ intros. eapply delast_block_st_follows; eauto. }
          simpl_Forall. eapply H in H24; eauto.
          * intros. eapply incl_map; eauto using st_follows_incl.
          * simpl_Forall; auto.
          * eapply dom_ub_incl; eauto. apply incl_appr', incl_map; eauto using st_follows_incl.
        + intros. apply Forall_app; auto.
    Qed.

    Lemma st_senv_senv_of_decls {pref} : forall (st : fresh_st pref _),
        st_senv st = @senv_of_decls exp (map (fun xtc => (fst xtc, ((fst (snd xtc)), snd (snd xtc), xH, None))) (st_anns st)).
    Proof.
      intros.
      unfold st_senv, senv_of_decls, senv_of_tyck.
      repeat rewrite map_map. eapply map_ext. intros; destruct_conjs; auto.
    Qed.

    Lemma delast_outs_and_block_sem : forall ins outs blk blk' st st' bs Hi Hi',
        let Γ := senv_of_ins ins ++ senv_of_decls outs in
        (forall x vs, sem_var Hi (Var x) vs -> sem_var Hi' (Var x) vs) ->
        NoDupMembers Γ ->
        NoDupLocals (map fst Γ) blk ->
        Forall (AtomOrGensym elab_prefs) (map fst Γ) ->
        GoodLocals elab_prefs blk ->
        dom Hi Γ ->
        dom_ub Hi' (Γ++st_senv st) ->
        wc_block G1 Γ blk ->
        Forall (fun '(_, (ty, _, _, o)) => LiftO True (fun '(e, _) => wt_exp G1 Γ e /\ typeof e = [ty]) o) outs ->
        wt_block G1 Γ blk ->
        sc_vars Γ Hi bs ->
        Forall (sem_last_decl (sem_exp_ck G1) (FEnv.empty _) Hi bs) outs ->
        sem_block_ck G1 Hi bs blk ->
        delast_outs_and_block outs blk st = (blk', st') ->
        sem_block_ck G2 Hi' bs blk'.
    Proof.
      unfold delast_outs_and_block.
      intros * Vars ND1 ND2 At Good Dom Ub2 Wc WtL Wt Sc ScL Sem DL. repeat inv_bind.

      assert (forall x1, Env.In x1 (Env.from_list (map fst x)) ->
                    IsLast (senv_of_ins ins ++ senv_of_decls outs) x1) as IsL.
      { intros * In. apply Env.In_from_list in In. simpl_In.
        eapply fresh_idents_In' in H; eauto.
        right. simpl_In. econstructor. solve_In. simpl; congruence. }
      assert (forall x1, IsLast (senv_of_ins ins ++ senv_of_decls outs) x1 ->
                    Env.In x1 (Env.from_list (map fst x))) as IsL'.
      { intros * In. apply Env.In_from_list. simpl_In.
        destruct In as [In|In]; [apply senv_of_ins_NoLast in In as []|inv In; simpl_In].
        destruct o as [(?&?)|]; simpl in *; try congruence.
        eapply fresh_idents_In in H as (?&In'); [|solve_In; simpl; eauto].
        solve_In. }
      assert (forall x1 y, Env.find x1 (Env.from_list (map fst x)) = Some y ->
                      In y (st_ids x0)) as St.
      { intros * Find. apply Env.from_list_find_In in Find.
        eapply fresh_idents_In_ids in H. simpl_In. simpl_Forall. solve_In. }
      assert (forall x1 x2,
                 IsLast (senv_of_ins ins ++ senv_of_decls outs) x1 ->
                 IsLast (senv_of_ins ins ++ senv_of_decls outs) x2 ->
                 rename_in_var (Env.from_list (map fst x)) x1 = rename_in_var (Env.from_list (map fst x)) x2 ->
                 x1 = x2) as Inj.
      { intros * L1 L2 Ren. simpl_In.
        destruct L1 as [L1|L1]; [eapply senv_of_ins_NoLast in L1 as []|inv L1].
        destruct L2 as [L2|L2]; [eapply senv_of_ins_NoLast in L2 as []|inv L2]. simpl_In.
        destruct o as [(?&?)|], o0 as [(?&?)|]; simpl in *; try congruence.
        eapply rename_in_var_of_list_inj; eauto.
        + eapply fresh_idents_NoDup in H. rewrite fst_NoDupMembers, map_map in H.
          erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
        + clear Hin. eapply fresh_idents_In in H as (?&?); solve_In. simpl; eauto.
        + clear Hin0. eapply fresh_idents_In in H as (?&?); solve_In. simpl; eauto.
      }
      assert (forall y y0 ty ck e, In (y, y0, (ty, ck, e)) x -> ~IsVar (senv_of_ins ins ++ senv_of_decls outs) y0) as Hdisj.
      { intros * In1 V. inv V. rewrite fst_InMembers in H2.
        eapply fresh_idents_prefixed in H. simpl_Forall. subst.
        eapply contradict_AtomOrGensym; eauto using last_not_in_elab_prefs. }

      cases_eqn EQ; repeat inv_bind.
      - apply is_nil_spec in EQ; subst.
        eapply delast_block_sem with (Hi:=Hi) in H0; eauto using incl_refl, dom_dom_ub.
        + intros * L. exfalso.
          eapply NoLast_app; [clear L|eauto]. split; eauto using senv_of_ins_NoLast.
          intros * L. inv L. simpl_In. destruct o as [(?&?)|]; simpl in *; try congruence.
          eapply fresh_idents_In in H as (?&[]). solve_In. simpl; eauto.
        + eapply dom_ub_incl; [|eauto]; eauto using incl_appr', incl_map, st_follows_incl, fresh_idents_st_follows.
      - econstructor.
        pose (Hi2:=FEnv.of_list (map (fun '(x, lx, _) => (Var lx, or_default (Streams.const absent) (Hi (Last x)))) x)).

        assert (dom Hi2 (@senv_of_decls exp (map (fun '(_, lx, (ty, ck, _)) => (lx, (ty, ck, 1%positive, None))) x))) as Dom'.
        { subst Hi2. unfold dom. setoid_rewrite FEnv.of_list_In.
          clear - x. split; intros *; (split; intros In; [|inv In]; simpl_In; try congruence; try econstructor; solve_In).
          split; [|solve_In]. auto. }

        assert (forall x vs, sem_var Hi (Var x) vs -> sem_var (Hi' + Hi2) (Var x) vs) as Vars'.
        { intros * V. eapply sem_var_union2; eauto.
          intros * In. subst Hi2. apply FEnv.of_list_In in In. simpl_In.
          eapply Hdisj; eauto. apply Dom; eauto using sem_var_In. }

        assert (NoDupMembers (map fst x)) as ND3.
        { eapply fresh_idents_NoDupMembers; eauto.
          apply NoDupMembers_map_filter.
          - intros; destruct_conjs; auto. destruct o as [(?&?)|]; simpl in *; auto.
          - apply NoDupMembers_senv_of_decls; eauto using NoDupMembers_app_r. }

        assert (forall x2 vs,
                   IsLast (senv_of_ins ins ++ senv_of_decls outs) x2 ->
                   sem_var Hi (Last x2) vs ->
                   sem_var (Hi' + Hi2) (Var (rename_in_var (Env.from_list (map fst x)) x2)) vs) as Lasts'.
        { intros * L V. eapply sem_var_union3'.
          apply IsLast_app in L as [L|L]; inv L; simpl_In; try congruence.
          destruct o as [(?&?)|]; simpl in *; try congruence.
          subst Hi2. inv V.
          econstructor; eauto. eapply FEnv.of_list_In_find.
          1:{ eapply fresh_idents_NoDup in H. rewrite fst_NoDupMembers, map_map in H.
              erewrite fst_NoDupMembers, map_map, map_ext, <-map_map. eapply FinFun.Injective_map_NoDup with (f:=Var); eauto.
              intros ?? Eq; now inv Eq.
              intros; destruct_conjs; auto. }
          assert (Fresh:=H). eapply fresh_idents_In in H as (?&In). 2:solve_In; simpl; eauto.
          unfold rename_in_var.
          erewrite Env.find_In_from_list; eauto. 2:solve_In.
          solve_In. f_equal. now rewrite H3.
        }

        eapply Sscope with (Hi':=Hi2); eauto. 3:apply Forall_app; split.
        + simpl_Forall. constructor.
        + subst Hi2. split; intros * Ck.
          2:{ intros * L. exfalso. inv L. simpl_In. congruence. }
          intros V. apply sem_var_union in V as [V|V].
          1:{ exfalso. apply sem_var_In, Ub2 in V.
              inv Ck. inv V. simpl_In.
              apply in_app_iff in Hin as [Hin|Hin].
              - eapply Hdisj; eauto. econstructor. solve_In.
              - apply fresh_idents_nIn_ids in H. simpl_Forall. eapply H. solve_In.
          }
          inv V. eapply FEnv.of_list_find_In in H2; simpl_In. inv Ck. simpl_In.
          assert (Eq:=H). eapply fresh_idents_NoDup, NoDupMembers_det in Eq. 2:solve_In. 2:clear Hin1; solve_In. inv Eq. clear Hin1.
          eapply fresh_idents_In' in H; eauto. simpl_In.
          assert (FEnv.In (Last i1) Hi) as (?&Find).
          { eapply Dom. apply IsLast_app, or_intror. econstructor; solve_In. simpl. congruence. }
          rewrite Find in H3; simpl in *. rewrite H3.
          eapply sem_clock_refines, Sc. 4:econstructor; eauto; reflexivity.
          2,3:simpl_In; right; econstructor; solve_In; simpl; congruence.
          clear - Dom Hdisj Vars. apply var_history_refines'.
          intros * V1. eapply sem_var_union2; eauto.
          intros In. apply FEnv.of_list_In in In. simpl_In.
          eapply Hdisj; eauto. apply Dom; eauto using sem_var_In.
        +{ simpl_Forall. eapply fresh_idents_In' in H; eauto. simpl_In. simpl_Forall. inv ScL.
           do 2 econstructor; repeat constructor.
           - eapply Sfby with (s0ss:=[[_]]) (sss:=[[_]]) (os:=[_]); simpl; repeat rewrite app_nil_r.
             3:constructor; [|constructor]; eauto.
             1,2:repeat constructor; eauto.
             rewrite FEnv.union_empty in H7; eauto using EqStrel_Reflexive.
             eapply sem_ref_sem_exp, rename_in_exp_sem; eauto with ltyping.
           - simpl. constructor; auto.
             eapply Lasts' in H12. 2:simpl_In; right; econstructor; solve_In; simpl; congruence.
             unfold rename_in_var in H12. erewrite Env.find_In_from_list in H12; eauto.
             solve_In.
         }
        + simpl_Forall.
          eapply delast_block_sem with (Hi:=Hi); eauto using incl_refl, dom_dom_ub.
          * simpl_Forall; auto.
          * unfold dom_ub. setoid_rewrite fresh_idents_st_senv; eauto. rewrite app_assoc.
            eapply local_hist_dom_ub; eauto.
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
        eapply sem_node_ck_cons1' in H4 as (Blk&Lasts); eauto. clear H3.
        2:{ inv Hord1. destruct H7 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }

        replace {| types := types G1; nodes := nodes G1 |} with G1 in * by (destruct G1; auto).
        pose proof (n_nodup n0) as (Hnd1&Hnd2).
        pose proof (n_good n0) as (Hgood1&Hgood2&_).
        inv Hwc. destruct H4 as (Hwc&_); simpl in Hwc.
        inv Hwt. destruct H4 as (Hwt&_); simpl in Hwt.
        destruct H5 as (Hdom1&Hsc1).

        pose (Hi':=fun x => match x with Var x => H (Var x) | _ => None end).
        assert (forall x vs, sem_var H (Var x) vs -> sem_var Hi' (Var x) vs) as Vars.
        { subst Hi'. intros * V. inv V. econstructor; eauto. }
        assert (forall x vs, sem_var Hi' (Var x) vs -> sem_var H (Var x) vs) as Vars'.
        { subst Hi'. intros * V. inv V. econstructor; eauto. }

        eapply delast_outs_and_block_sem with (Hi':=Hi') in Blk;
          eauto using node_NoDupLocals, dom_dom_ub. 8:apply surjective_pairing.
        eapply Snode with (H:=Hi'); eauto.
        + erewrite find_node_now; eauto.
        + simpl_Forall. eauto.
        + simpl_Forall. eauto.
        + simpl_Forall. simpl_In. constructor.
        + apply sem_block_ck_cons2; simpl...
          2:{ eapply find_node_not_Is_node_in in Hord2.
            2:erewrite find_node_now; eauto. contradict Hord2. now right. }
          destruct G2; eauto.
        + simpl. constructor; simpl; auto.
          * subst Hi'.
            split; unfold FEnv.In; simpl.
            2:{ split; intros; destruct_conjs; try congruence.
                exfalso. eapply NoLast_app; [|eauto]; split; eauto using senv_of_ins_NoLast.
                intros * L'. inv L'. simpl_In. congruence. }
            intros. destruct Hdom1 as (D1&_). setoid_rewrite D1. rewrite 2 IsVar_app.
            apply or_iff_compat_l.
            split; intros * V; clear - V; inv V; simpl_In; econstructor; solve_In.
          * split; intros * Ck.
            2:{ intros * L. exfalso.
                eapply NoLast_app; [|eauto]; split; eauto using senv_of_ins_NoLast.
                intros * L'. inv L'. simpl_In. congruence. }
            intros * V. eapply sem_clock_refines; eauto using var_history_refines'.
            eapply Vars', Hsc1 in V; eauto.
            clear - Ck. simpl_In. destruct Ck as [|Ck]; auto. right.
            inv Ck. simpl_In. econstructor. solve_In. auto.
        + apply node_NoDupMembers.
        + now rewrite map_app, map_fst_senv_of_ins, map_fst_senv_of_decls.
        + unfold st_senv. rewrite init_st_anns, app_nil_r.
          subst Hi'. split; intros * In.
          * eapply Hdom1. inv In. econstructor; eauto.
          * exfalso. inv In. congruence.
        + inv Hwc. destruct G1; auto.
        + inv Hwt. destruct G1; auto.
        + inv Hwt. destruct G1; auto.
      - erewrite find_node_other in Hfind; eauto.
        eapply sem_node_ck_cons2...
        destruct G2; apply HGref.
        eapply sem_node_ck_cons1' in H4 as (?&?); eauto using find_node_later_not_Is_node_in.
        destruct G1; econstructor...
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
