From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Omega.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax Lustre.LClocking.
From Velus Require Import Lustre.InlineLocal.InlineLocal.

Module Type ILCLOCKING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (Import DL  : INLINELOCAL Ids Op OpAux Cks Syn).

  Section rename.
    Variable sub : Env.t ident.

    Variable vars vars' : list (ident * clock).

    Hypothesis Hsub : forall x y ck,
        Env.find x sub = Some y ->
        In (x, ck) vars ->
        In (y, rename_in_clock sub ck) vars'.

    Hypothesis Hnsub : forall x ck,
        Env.find x sub = None ->
        In (x, ck) vars ->
        In (x, rename_in_clock sub ck) vars'.

    Lemma rename_in_var_wc : forall x ck,
        In (x, ck) vars ->
        In (rename_in_var sub x, rename_in_clock sub ck) vars'.
    Proof.
      intros * Hin.
      unfold rename_in_var.
      destruct (Env.find _ _) eqn:Hfind; eauto.
    Qed.

    Lemma rename_in_clock_wc : forall ck,
        wc_clock vars ck ->
        wc_clock vars' (rename_in_clock sub ck).
    Proof.
      induction ck; intros * Hwc; inv Hwc; auto.
      simpl. constructor; eauto using rename_in_var_wc.
    Qed.

    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Lemma rename_in_exp_clockof : forall e,
        clockof (rename_in_exp sub e) = map (rename_in_clock sub) (clockof e).
    Proof.
      induction e using exp_ind2; simpl; auto. 4:destruct x.
      1-6:repeat rewrite map_map; simpl.
      1-6:eapply map_ext; eauto.
    Qed.

    Corollary rename_in_exp_clocksof : forall es,
        clocksof (map (rename_in_exp sub) es) = map (rename_in_clock sub) (clocksof es).
    Proof.
      induction es; simpl; auto.
      rewrite map_app. f_equal; auto using rename_in_exp_clockof.
    Qed.

    Lemma rename_in_exp_nclockof : forall e,
        nclockof (rename_in_exp sub e) = map (rename_in_nclock sub) (nclockof e).
    Proof.
      induction e using exp_ind2; simpl; auto. 4:destruct x.
      1-6:repeat rewrite map_map; simpl.
      1-6:eapply map_ext; eauto.
    Qed.

    Corollary rename_in_exp_nclocksof : forall es,
        nclocksof (map (rename_in_exp sub) es) = map (rename_in_nclock sub) (nclocksof es).
    Proof.
      induction es; simpl; auto.
      rewrite map_app. f_equal; auto using rename_in_exp_nclockof.
    Qed.

    Lemma rename_in_nclock_WellInstantiated : forall bck sub0 sub xck nck,
        WellInstantiated bck sub0 xck nck ->
        WellInstantiated (rename_in_clock sub bck) (fun x => option_map (rename_in_var sub) (sub0 x)) xck (rename_in_nclock sub nck).
    Proof.
      intros ??? (x&ck) (ck'&name) (Hw1&Hw2). split; simpl in *.
      - rewrite Hw1. destruct name; simpl; auto.
      - clear Hw1. revert ck' Hw2.
        induction ck; intros * Hw2; simpl in *.
        + inv Hw2; auto.
        + cases_eqn Heq; inv Hw2; simpl in *.
          * inv Heq2; simpl.
            specialize (IHck _ eq_refl). now inv IHck.
          * congruence.
          * specialize (IHck _ eq_refl). congruence.
    Qed.

    Lemma rename_in_exp_wc : forall e,
        wc_exp G vars e ->
        wc_exp G vars' (rename_in_exp sub e).
    Proof.
      intros * Hwc; induction e using exp_ind2; inv Hwc; simpl;
        econstructor; eauto using rename_in_var_wc.
      1-34:try solve [rewrite Forall_map, Forall_forall in *; intros; eauto].
      1-26:try rewrite rename_in_exp_clockof; simpl.
      1-26:try rewrite rename_in_exp_clocksof; simpl.
      1-26:try (rewrite map_rename_in_ann_clock; rewrite Forall2_eq in *; congruence).
      - now rewrite H3.
      - now rewrite H5.
      - now rewrite H6.
      - rewrite Forall_map. eapply Forall_impl; [|eauto]; intros (?&(?&?)) Hun.
        inv Hun; simpl in *; subst. constructor.
      - rewrite Forall_map. eapply Forall_impl; [|eauto]; intros (?&(?&?)) Hun.
        inv Hun; simpl in *; subst. constructor.
      - rewrite Forall_map. eapply Forall_impl; [|eauto]; intros; subst; auto.
      - now rewrite map_length.
      - contradict H4. apply map_eq_nil in H4; auto.
      - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite Forall_map.
        specialize (H _ Hin). specialize (H5 _ Hin).
        rewrite Forall_forall in *; eauto.
      - rewrite Forall_map. rewrite Forall_forall; intros (?&?) Hin; simpl.
        rewrite rename_in_exp_clocksof, Forall_map.
        eapply Forall_forall in H6; eauto; simpl in H6.
        eapply Forall_impl; [|eauto]; intros; subst; auto.
      - rewrite Forall_map. eapply Forall_impl; [|eapply H7]; eauto; intros (?&?) ?; simpl in *.
        now rewrite rename_in_exp_clocksof, map_length.
      - now rewrite H6.
      - contradict H7. apply map_eq_nil in H7; auto.
      - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite Forall_map.
        specialize (H _ Hin). specialize (H8 _ Hin).
        rewrite Forall_forall in *; eauto.
      - rewrite Forall_map. rewrite Forall_forall; intros (?&?) Hin; simpl.
        rewrite rename_in_exp_clocksof, Forall_map.
        eapply Forall_forall in H9; eauto; simpl in H9.
        eapply Forall_impl; [|eauto]; intros; subst; auto.
      - rewrite Forall_map. eapply Forall_impl; [|eapply H10]; eauto; intros (?&?) ?; simpl in *.
        now rewrite rename_in_exp_clocksof, map_length.
      - intros ? Hopt. eapply option_map_inv in Hopt as (?&?&?); subst; simpl in *.
        specialize (H11 _ eq_refl).
        rewrite Forall_map. rewrite Forall_forall in *; eauto.
      - intros ? Hopt. eapply option_map_inv in Hopt as (?&?&?); subst; simpl in *.
        specialize (H12 _ eq_refl).
        rewrite rename_in_exp_clocksof, Forall_map. eapply Forall_impl; [|eauto]; intros; subst; auto.
      - intros ? Hopt. eapply option_map_inv in Hopt as (?&?&?); subst; simpl in *.
        specialize (H13 _ eq_refl).
        now rewrite rename_in_exp_clocksof, map_length.
      - rewrite rename_in_exp_nclocksof, Forall2_map_2.
        eapply Forall2_impl_In; [|eauto]; intros.
        eapply rename_in_nclock_WellInstantiated; eauto.
      - rewrite 2 Forall2_map_2. rewrite Forall2_map_2 in H9.
        eapply Forall2_impl_In; [|eauto]; intros.
        eapply rename_in_nclock_WellInstantiated; eauto.
      - rewrite Forall_map. eapply Forall_impl; [|eauto]; intros ? (?&Hck).
        rewrite rename_in_exp_clockof, Hck; simpl; eauto.
    Qed.

    Lemma rename_in_equation_wc : forall eq,
        wc_equation G vars eq ->
        wc_equation G vars' (rename_in_equation sub eq).
    Proof.
      intros (?&?) (Hwc1&Hwc2&Hwc3).
      repeat split.
      - rewrite Forall_map.
        eapply Forall_impl; [|eauto]; intros; eauto using rename_in_exp_wc.
      - rewrite rename_in_exp_nclocksof, Forall2_map_1, Forall2_map_2.
        eapply Forall2_impl_In; [|eauto]; intros ? (?&[|]) ???; simpl in *; subst; auto.
      - rewrite rename_in_exp_clocksof, Forall2_map_1, Forall2_map_2.
        eapply Forall2_impl_In; [|eauto]; intros; eauto using rename_in_var_wc.
    Qed.

  End rename.

  Import Fresh Facts Tactics.

  Fact In_sub1 : forall (vars1 vars2 vars3 : list (ident * _)) sub,
      (forall x, InMembers x vars1 -> ~InMembers x vars2) ->
      (forall x, Env.In x sub <-> InMembers x vars2) ->
      (forall x y ck, Env.find x sub = Some y -> In (x, ck) vars2 -> In (y, rename_in_clock sub ck) vars3) ->
      forall x y ck, Env.find x sub = Some y -> In (x, ck) (vars1 ++ vars2) -> In (y, rename_in_clock sub ck) (vars1 ++ vars3).
  Proof.
    intros * Hnd Hsubin Hsub * Hfind Hin.
    rewrite in_app_iff in *. destruct Hin as [Hin|Hin]; eauto.
    exfalso. eapply In_InMembers, Hnd in Hin.
    eapply Hin, Hsubin. econstructor; eauto.
  Qed.

  Fact rename_in_clock_idem vars sub : forall ck,
      (forall x, InMembers x vars -> ~Env.In x sub) ->
      wc_clock vars ck ->
      rename_in_clock sub ck = ck.
  Proof.
    induction ck; intros * Hnin Hwc; inv Hwc; simpl; auto.
    rewrite IHck; eauto. f_equal; auto.
    unfold rename_in_var.
    destruct (Env.find i sub) eqn:Hfind; auto.
    exfalso.
    eapply Hnin; eauto using In_InMembers.
    econstructor; eauto.
  Qed.

  Fact In_sub2 : forall (vars1 vars2 vars3 : list (ident * _)) sub,
      wc_env vars1 ->
      (forall x, InMembers x vars1 -> ~InMembers x vars2) ->
      (forall x, Env.In x sub <-> InMembers x vars2) ->
      (forall x y ck, Env.find x sub = Some y -> In (x, ck) vars2 -> In (y, rename_in_clock sub ck) vars3) ->
      forall x ck, Env.find x sub = None -> In (x, ck) (vars1 ++ vars2) -> In (x, rename_in_clock sub ck) (vars1 ++ vars3).
  Proof.
    intros * Hwenv Hnin Hsubin Hsub * Hfind Hin.
    rewrite in_app_iff in *. destruct Hin as [Hin|Hin]; eauto.
    - erewrite rename_in_clock_idem; eauto.
      + intros. rewrite Hsubin; eauto.
      + eapply Forall_forall in Hwenv; eauto. eauto.
    - exfalso. eapply In_InMembers, Hsubin in Hin as (?&?).
      congruence.
  Qed.

  Hint Resolve In_sub1 In_sub2.

  Fact mmap_inlinelocal_block_wc {PSyn prefs} (G: @global PSyn prefs) sub vars vars' : forall blks blks' st st',
      Forall (fun blk => forall sub vars' blks' st st',
                  (forall x, InMembers x vars -> ~InMembers x vars') ->
                  (forall x, Env.In x sub <-> InMembers x vars') ->
                  (forall x y ck, Env.find x sub = Some y -> In (x, ck) vars' -> In (y, rename_in_clock sub ck) (idck (st_anns st))) ->
                  (forall x y, Env.MapsTo x y sub -> exists n, y = gensym local (Some x) n) ->
                  NoDupLocals (map fst vars++map fst vars') blk ->
                  GoodLocals elab_prefs blk ->
                  wc_env vars ->
                  wc_env (vars++vars') ->
                  wc_block G (vars++vars') blk ->
                  Forall (wc_clock (vars ++ idck (st_anns st))) (map snd (idck (st_anns st))) ->
                  st_valid_after st local PS.empty ->
                  inlinelocal_block sub blk st = (blks', st') ->
                  Forall (wc_block G (vars ++ idck (st_anns st'))) blks' /\
                  Forall (wc_clock (vars ++ idck (st_anns st'))) (map snd (idck (st_anns st')))) blks ->
      (forall x, InMembers x vars -> ~InMembers x vars') ->
      (forall x, Env.In x sub <-> InMembers x vars') ->
      (forall x y ck, Env.find x sub = Some y -> In (x, ck) vars' -> In (y, rename_in_clock sub ck) (idck (st_anns st))) ->
      (forall x y, Env.MapsTo x y sub -> exists n, y = gensym local (Some x) n) ->
      Forall (NoDupLocals (map fst vars++map fst vars')) blks ->
      Forall (GoodLocals elab_prefs) blks ->
      wc_env vars ->
      wc_env (vars++vars') ->
      Forall (wc_block G (vars++vars')) blks ->
      Forall (wc_clock (vars ++ idck (st_anns st))) (map snd (idck (st_anns st))) ->
      st_valid_after st local PS.empty ->
      mmap (inlinelocal_block sub) blks st = (blks', st') ->
      Forall (wc_block G (vars ++ idck (st_anns st'))) (concat blks') /\
      Forall (wc_clock (vars ++ idck (st_anns st'))) (map snd (idck (st_anns st'))).
  Proof.
    induction blks; intros * Hf Hnin Hsubin Hsub Hsubgensym Hnd Hgood Hwenv Hwenv2 Hwc Hwcc Hvalid Hmmap;
      inv Hf; inv Hnd; inv Hgood; inv Hwc; repeat inv_bind; simpl; auto.
    assert (Hdl:=H). eapply H1 in H as (?&?); eauto.
    assert (Hmap:=H0). eapply IHblks in H0 as (?&?); eauto.
    2:{ intros * Hfind Hin.
        eapply incl_map; [|eauto]. eapply st_follows_incl; eauto. }
    2:eapply inlinelocal_block_st_valid_after; eauto.
    constructor; auto.
    apply Forall_app. split; eauto.
    eapply Forall_impl; [|eauto]; intros.
    eapply wc_block_incl; [|eauto]. eapply incl_appr', incl_map, st_follows_incl, mmap_st_follows; eauto.
    eapply Forall_forall; eauto.
  Qed.

  Hint Resolve -> fst_InMembers.
  Hint Resolve <- fst_InMembers.
  Hint Resolve in_or_app In_InMembers.

  Lemma inlinelocal_block_wc {PSyn prefs} (G: @global PSyn prefs) vars : forall blk sub vars' blks' st st',
      (forall x, InMembers x vars -> ~InMembers x vars') ->
      (forall x, Env.In x sub <-> InMembers x vars') ->
      (forall x y ck, Env.find x sub = Some y -> In (x, ck) vars' -> In (y, rename_in_clock sub ck) (idck (st_anns st))) ->
      (forall x y, Env.MapsTo x y sub -> exists n, y = gensym local (Some x) n) ->
      NoDupLocals (map fst vars++map fst vars') blk ->
      GoodLocals elab_prefs blk ->
      wc_env vars ->
      wc_env (vars++vars') ->
      wc_block G (vars++vars') blk ->
      Forall (wc_clock (vars++idck (st_anns st))) (map snd (idck (st_anns st))) ->
      st_valid_after st local PS.empty ->
      inlinelocal_block sub blk st = (blks', st') ->
      Forall (wc_block G (vars++idck (st_anns st'))) blks' /\
      Forall (wc_clock (vars++idck (st_anns st'))) (map snd (idck (st_anns st'))).
  Proof.
    induction blk using block_ind2; intros * Hnin Hsubin Hsub Hsubgensym Hgood Hnd Hwenv Hwenv2 Hwc Hwcc Hvalid Hdl;
      inv Hnd; inv Hgood; inv Hwc; repeat inv_bind.
    - (* equation *)
      split; auto.
      do 2 constructor; auto.
      eapply rename_in_equation_wc; [| |eauto]; eauto using in_or_app.
    - (* reset *)
      repeat econstructor; eauto.
      + eapply mmap_inlinelocal_block_wc; eauto.
      + eapply rename_in_exp_wc; [| |eauto]; eauto using in_or_app.
        eapply In_sub1; eauto. 2:eapply In_sub2; eauto.
        1,2:(intros; eapply incl_map; [|eauto];
             eapply st_follows_incl, mmap_st_follows; eauto;
             eapply Forall_forall; eauto).
      + rewrite rename_in_exp_clockof, H7; simpl; eauto.
      + eapply mmap_inlinelocal_block_wc; eauto.
    - (* local *)
      assert (forall x, Env.In x x0 <-> InMembers x locs) as Hsubin'.
      { intros. split; intros * Hin.
        - eapply fresh_idents_rename_sub1 in Hin; [|eauto].
          unfold idty in *. erewrite fst_InMembers, 2 map_map, map_ext, <-fst_InMembers in Hin; eauto.
          intros (?&(?&?)&?); auto.
        - eapply fresh_idents_rename_sub2 in H0.
          unfold idty in *. erewrite fst_InMembers, 2 map_map, map_ext, <-fst_InMembers in H0; eauto.
          2:intros (?&(?&?)&?); auto.
          apply H0 in Hin as (?&?&?&_); eauto. econstructor; eauto.
      }
      assert (forall x, InMembers x (st_anns st) -> ~InMembers x locs) as Hdisj.
      { intros * Hinm1 Hinm2. rewrite fst_InMembers in Hinm1. rewrite fst_InMembers in Hinm2.
        eapply st_valid_after_AtomOrGensym_nIn in Hinm1; eauto using local_not_in_elab_prefs.
        eapply Forall_forall; eauto. }
      assert (forall x : Env.key, Env.In x sub -> ~Env.In x x0) as Hsub1.
      { intros ?. rewrite Hsubin, Hsubin'. intros Hin1 Hin2.
        eapply H7; eauto. }
      assert (forall x y, Env.MapsTo x y sub -> ~ Env.In y x0) as Hsub2.
      { intros ??. rewrite Hsubin'. intros Hin1 Hin2.
        eapply Hsubgensym in Hin1 as (?&Hgen); subst.
        eapply fst_InMembers, Forall_forall in Hin2; eauto.
        eapply contradict_AtomOrGensym in Hin2; eauto using local_not_in_elab_prefs.
      }
      eapply mmap_inlinelocal_block_wc in H1. 1,2,8,9,11:eauto.
      + rewrite <-app_assoc in H8; eauto.
      + intros ? Hin. rewrite InMembers_app, not_or', InMembers_idck, InMembers_idty.
        split; auto. intro contra.
        eapply H7; eauto.
      + intros. rewrite Env.union_In, InMembers_app, Hsubin.
        apply or_iff_compat_l.
        rewrite InMembers_idck, InMembers_idty; auto.
      + intros * Hfind Hin.
        eapply in_app_or in Hin as [Hin|Hin].
        * assert (Env.find x3 x0 = None) as Hnone.
          { eapply In_InMembers in Hin. rewrite fst_InMembers in Hin.
            destruct (Env.find x3 x0) eqn:Hfind'; eauto.
            exfalso. eapply H7; eauto. eapply fst_InMembers.
            eapply fresh_idents_rename_sub1 in H0. 2:econstructor; eauto.
            erewrite fst_InMembers, map_map, map_ext, map_fst_idty in H0; eauto.
            intros (?&?&?); auto. }
          eapply Env.union_find4 in Hfind as [Hfind|Hfind]; try congruence.
          eapply incl_map; eauto using st_follows_incl, fresh_idents_rename_st_follows.
          erewrite <-disjoint_union_rename_in_clock, rename_in_clock_idem; eauto.
          2:eapply rename_in_clock_wc with (vars:=vars++vars'); eauto using wc_env_var.
          instantiate (1:=[]); simpl.
          intros ?. rewrite Hsubin', InMembers_app. intros [Hinm1|Hinm1] Hinm2.
          -- eapply H7; eauto.
          -- rewrite InMembers_idck in Hinm1. eapply Hdisj; eauto.
        * erewrite fresh_idents_rename_anns; [|eauto].
          rewrite idck_app. apply in_or_app, or_introl.
          assert (Hfresh:=H0). eapply fresh_idents_rename_sub2 in H0 as ((?&?&Hmap&_)&_).
          { eapply In_InMembers in Hin. rewrite InMembers_idck, InMembers_idty, fst_InMembers in Hin.
            unfold idty. erewrite fst_InMembers, 2 map_map, map_ext; eauto.
            intros (?&(?&?)&?); auto. }
          unfold Env.MapsTo in *. erewrite Env.union_find3' in Hfind; [|eauto]. inv Hfind.
          eapply fresh_idents_rename_ids in Hfresh. rewrite Hfresh.
          2:{ unfold idty. erewrite fst_NoDupMembers, 2 map_map, map_ext, <-fst_NoDupMembers; auto.
              intros (?&(?&?)&?); auto. }
          eapply In_idck_exists in Hin as (?&Hin). eapply In_idty_exists in Hin as (?&Hin).
          unfold idty, idck. rewrite 3 map_map. eapply in_map_iff.
          do 2 esplit; eauto. simpl.
          rewrite Hmap; simpl; auto.
          f_equal.
          apply disjoint_union_rename_in_clock; auto.
      + intros ?? Hfind. eapply Env.union_find4 in Hfind as [Hfind|Hfind]; eauto.
        eapply fresh_idents_rename_sub_gensym in Hfind; eauto.
      + rewrite map_app, map_fst_idck, map_fst_idty, app_assoc; auto.
      + rewrite app_assoc.
        eapply Forall_app; split.
        * eapply Forall_impl; [|eauto]; intros (?&?) ?.
          eapply wc_clock_incl; [|eauto]. solve_incl_app.
        * rewrite Forall_map in H9.
          eapply Forall_impl; [|eauto]; intros (?&?) ?; eauto.
      + erewrite fresh_idents_rename_anns; [|eauto].
        rewrite idck_app, map_app.
        apply Forall_app; split.
        * assert (Hfresh:=H0). eapply fresh_idents_rename_ids in H0. rewrite H0.
          2:{ unfold idty. erewrite fst_NoDupMembers, 2 map_map, map_ext, <-fst_NoDupMembers; auto.
              intros (?&(?&?)&?); auto. }
          unfold idty at 2. repeat rewrite map_map.
          unfold idck, idty in *. repeat rewrite map_map in *.
          rewrite Forall_map in H9. rewrite Forall_map.
          eapply Forall_impl; [|eauto]; intros (?&(?&?)&?) Hwc; simpl in *.
          eapply rename_in_clock_wc, rename_in_clock_wc with (vars':=vars++(map (fun '(x, (_, ck, _)) => (x, rename_in_clock sub ck)) locs)++idck (st_anns st)). 5:eauto.
          4:{ intros ?? Hfind Hin. repeat rewrite in_app_iff in *. destruct Hin as [[Hin|Hin]|Hin]; auto.
              - left. erewrite rename_in_clock_idem; eauto. 2:eapply wc_env_var in Hin; eauto.
                intros * Hinm. rewrite Hsubin; eauto.
              - exfalso. eapply In_InMembers, Hsubin in Hin as (?&?). congruence.
              - right; left. eapply in_map_iff in Hin as ((?&(?&?)&?)&Heq&Hin); inv Heq.
                eapply in_map_iff. do 2 esplit; eauto; auto. }
          3:{ intros ??? Hfind Hin. repeat rewrite in_app_iff in *. destruct Hin as [[Hin|]|Hin]; eauto.
              - exfalso. eapply In_InMembers, Hnin in Hin.
                eapply Hin, Hsubin. econstructor; eauto.
              - exfalso. eapply In_InMembers in Hin. rewrite fst_InMembers, map_map, <-fst_InMembers in Hin.
                eapply H7; eauto.
                eapply in_or_app, or_intror, fst_InMembers.
                eapply Hsubin. econstructor; eauto. }
          2:{ intros ?? Hfind Hin. repeat rewrite in_app_iff in *. destruct Hin as [|[Hin|]]; auto.
              - left. erewrite rename_in_clock_idem; eauto. 2:eapply wc_env_var in H5; eauto.
                intros ? Hinm. rewrite Hsubin'. intros contra.
                eapply H7; eauto.
              - exfalso. eapply In_InMembers in Hin.
                erewrite fst_InMembers, map_map, map_ext, <-fst_InMembers in Hin. 2:intros (?&(?&?)&?); auto.
                eapply Hsubin' in Hin as (?&?). congruence.
              - do 2 right. erewrite rename_in_clock_idem; eauto.
                2:{ eapply Forall_forall in Hwcc; eauto.
                    eapply In_idck_exists in H5 as (?&?); eauto.
                    eapply in_map_iff. do 2 esplit; eauto. auto. }
                intros ? Hinm. rewrite Hsubin'. intros contra.
                eapply InMembers_app in Hinm as [Hinm|Hinm].
                + eapply H7; eauto.
                + rewrite fst_InMembers, map_map, <-fst_InMembers in Hinm.
                  eapply Hdisj; eauto.
          }
          { intros ??? Hfind Hin.
            eapply fresh_idents_rename_sub1 in Hfresh. 2:econstructor; eauto.
            erewrite fst_InMembers, map_map, map_ext, <-fst_InMembers in Hfresh.
            2:intros (?&(?&?)&?); auto.
            repeat rewrite in_app_iff in *. destruct Hin as [Hin|[Hin|Hin]]; auto.
            - exfalso. eapply H7; eauto.
            - right; left.
              eapply in_map_iff in Hin as ((?&(?&?)&?)&Heq&Hin); inv Heq.
              eapply in_map_iff. do 2 esplit; eauto.
              simpl. rewrite Hfind; auto.
            - exfalso. eapply In_InMembers in Hin. rewrite InMembers_idck in Hin.
              eapply Hdisj; eauto.
          }
        * eapply Forall_impl; [|eauto]; intros.
          eapply wc_clock_incl; [|eauto]; solve_incl_app.
      + eapply fresh_idents_rename_st_valid; eauto.
  Qed.

  Lemma inlinelocal_topblock_wc {PSyn prefs} (G: @global PSyn prefs) vars : forall blk blks' locs' st st',
      NoDupLocals (map fst vars) blk ->
      GoodLocals elab_prefs blk ->
      wc_env vars ->
      wc_block G vars blk ->
      Forall (wc_clock (vars++idck (st_anns st))) (map snd (idck (st_anns st))) ->
      st_valid_after st local PS.empty ->
      inlinelocal_topblock blk st = (blks', locs', st') ->
      Forall (wc_block G (vars++idck (idty locs'++st_anns st'))) blks' /\
      Forall (wc_clock (vars++idck (idty locs'++st_anns st'))) (map snd (idck (idty locs'++st_anns st'))).
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hnd Hgood Hwenv Hwc Hwcck Hvalid Hil; repeat inv_bind; simpl.
    1,2:eapply inlinelocal_block_wc with (vars':=[]); try rewrite app_nil_r; eauto.
    7:inv Hnd; inv Hgood; inv Hwc; eapply mmap_inlinelocal_block_wc with (vars0:=vars++idck (idty locs')) (vars':=[]) in H as (Hwc1&Hwc2); try rewrite app_nil_r; eauto.
    1,4,9:intros *; rewrite Env.Props.P.F.empty_in_iff; split; intros [].
    1,3,7:intros * Hfind [].
    1,2,5:intros * Hfind; eapply Env.Props.P.F.empty_mapsto_iff in Hfind as [].
    - rewrite idck_app, map_app, Forall_app. rewrite <-app_assoc in Hwc1, Hwc2.
      repeat split; auto.
      eapply Forall_impl; [|eauto]; intros.
      eapply wc_clock_incl; [|eauto]; solve_incl_app.
    - eapply Forall_forall; intros; eauto using inlinelocal_block_wc.
    - now rewrite map_app, map_fst_idck, map_fst_idty.
    - eapply Forall_app; split.
      + eapply Forall_impl; [|eauto]; intros (?&?) ?.
        eapply wc_clock_incl; [|eauto]; solve_incl_app.
      + rewrite Forall_map in H9. eapply Forall_impl; [|eauto]; intros (?&?); auto.
    - eapply Forall_app; split.
      + eapply Forall_impl; [|eauto]; intros (?&?) ?.
        eapply wc_clock_incl; [|eauto]; solve_incl_app.
      + rewrite Forall_map in H9. eapply Forall_impl; [|eauto]; intros (?&?); auto.
    - eapply Forall_impl; [|eauto]; intros.
      eapply wc_clock_incl; [|eauto]; solve_incl_app.
    Transparent inlinelocal_block.
  Qed.

  Lemma inlinelocal_node_wc {PSyn} : forall G1 G2 (n : @node PSyn _),
      global_iface_eq G1 G2 ->
      wc_node G1 n ->
      wc_node G2 (inlinelocal_node n).
  Proof.
    unfold inlinelocal_node, wc_node; simpl.
    intros * Hiface (Hwc1&Hwc2&Hwc3).
    pose proof (n_nodup n) as (_&Hnd2).
    pose proof (n_good n) as (_&Hgood&_).
    destruct (inlinelocal_topblock _ _) as ((?&?)&?) eqn:Hdl.
    repeat split; auto.
    eapply inlinelocal_topblock_wc in Hdl as (?&?); try rewrite app_nil_r. 4:eapply Hwc2. 1-6:eauto.
    - repeat constructor; simpl; eauto;
        repeat rewrite idty_app in *; repeat rewrite idck_app in *; repeat rewrite map_app in *.
      2:rewrite Forall_app in H0; destruct H0 as (Hwc4&Hwc5).
      2:rewrite Forall_app; split.
      + eapply Forall_impl; [|eauto]; intros.
        eapply iface_eq_wc_block; eauto.
        repeat rewrite idty_app in *. repeat rewrite idck_app in *.
        unfold idck at 4, idty at 4.
        repeat rewrite map_map; simpl; eauto.
      + eapply Forall_impl; [|eauto]; intros.
        unfold idck at 4, idty at 4. repeat rewrite map_map; simpl; eauto.
      + repeat setoid_rewrite Forall_map in Hwc5. repeat setoid_rewrite Forall_map.
        eapply Forall_impl; [|eauto]; intros (?&?&?) ?; simpl in *.
        unfold idck at 4, idty at 4. repeat rewrite map_map; simpl; eauto.
    - rewrite map_fst_idck, map_fst_idty.
      eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
    - rewrite init_st_anns; simpl; auto.
    - eapply init_st_valid; eauto using local_not_in_elab_prefs, PS_For_all_empty.
  Qed.

  Theorem inlinelocal_global_wc : forall G,
      wc_global G ->
      wc_global (inlinelocal_global G).
  Proof.
    unfold wc_global, inlinelocal_global.
    intros * Hwc.
    eapply CommonTyping.transform_units_wt_program; eauto.
    intros ?? Hwc'.
    eapply inlinelocal_node_wc; eauto. eapply inlinelocal_global_iface_eq.
  Qed.

End ILCLOCKING.

Module ILClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (IL  : INLINELOCAL Ids Op OpAux Cks Syn)
       <: ILCLOCKING Ids Op OpAux Cks Syn Clo IL.
  Include ILCLOCKING Ids Op OpAux Cks Syn Clo IL.
End ILClockingFun.
