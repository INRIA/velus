From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LClocking.
From Velus Require Import Lustre.InlineLocal.InlineLocal.

Module Type ILCLOCKING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import DL  : INLINELOCAL Ids Op OpAux Cks Senv Syn).

  Section rename.
    Variable sub : Env.t ident.
    Variable Γ Γ' : static_env.

    Hypothesis NoLast : forall x, ~IsLast Γ x.

    Hypothesis Hsub : forall x y ck,
        Env.find x sub = Some y ->
        HasClock Γ x ck ->
        HasClock Γ' y (rename_in_clock sub ck).

    Hypothesis Hnsub : forall x ck,
        Env.find x sub = None ->
        HasClock Γ x ck ->
        HasClock Γ' x (rename_in_clock sub ck).

    Lemma rename_in_var_wc : forall x ck,
        HasClock Γ x ck ->
        HasClock Γ' (rename_in_var sub x) (rename_in_clock sub ck).
    Proof.
      intros * Hin.
      unfold rename_in_var.
      destruct (Env.find _ _) eqn:Hfind; eauto.
    Qed.

    Lemma rename_in_clock_wc : forall ck,
        wc_clock (idck Γ) ck ->
        wc_clock (idck Γ') (rename_in_clock sub ck).
    Proof.
      induction ck; intros * Hwc; inv Hwc; auto with clocks.
      simpl. constructor; eauto.
      simpl_In. assert (HasClock Γ i a.(clo)) as Hck by eauto with senv.
      apply rename_in_var_wc in Hck; auto. inv Hck. solve_In.
      congruence.
    Qed.

    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Lemma rename_in_exp_clockof : forall e,
        clockof (rename_in_exp sub e) = map (rename_in_clock sub) (clockof e).
    Proof.
      induction e using exp_ind2; simpl; auto; destruct_conjs.
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

    Lemma rename_in_clock_instck : forall sub1 sub0 bck ck ck',
        instck bck sub0 ck = Some ck' ->
        instck (rename_in_clock sub1 bck) (fun x0 => option_map (rename_in_var sub1) (sub0 x0)) ck = Some (rename_in_clock sub1 ck').
    Proof.
      induction ck; intros * Hinst; simpl in *.
      - inv Hinst; auto.
      - cases_eqn Heq; inv Hinst; simpl in *.
        + inv Heq2; simpl.
          specialize (IHck _ eq_refl). now inv IHck.
        + congruence.
        + specialize (IHck _ eq_refl). congruence.
    Qed.

    Lemma rename_in_nclock_WellInstantiated1 : forall bck sub0 sub xck nck,
        WellInstantiated bck sub0 xck nck ->
        WellInstantiated (rename_in_clock sub bck) (fun x => option_map (rename_in_var sub) (sub0 x)) xck (rename_in_nclock sub nck).
    Proof.
      intros ??? (x&ck) (ck'&name) (Hw1&Hw2). split; simpl in *.
      - rewrite Hw1. destruct name; simpl; auto.
      - apply rename_in_clock_instck; auto.
    Qed.

    Lemma rename_in_nclock_WellInstantiated2 : forall bck sub0 sub xck ck,
        WellInstantiated bck sub0 xck (ck, None) ->
        WellInstantiated (rename_in_clock sub bck) (fun x => option_map (rename_in_var sub) (sub0 x)) xck (rename_in_clock sub ck, None).
    Proof.
      intros ??? (x&ck) ck' (Hw1&Hw2). split; simpl in *.
      - rewrite Hw1. reflexivity.
      - apply rename_in_clock_instck; auto.
    Qed.

    Lemma rename_in_exp_wc : forall e,
        wc_exp G Γ e ->
        wc_exp G Γ' (rename_in_exp sub e).
    Proof.
      intros * Hwc; induction e using exp_ind2; inv Hwc; simpl;
        econstructor; eauto using rename_in_var_wc.
      1,2:take (IsLast _ _) and eapply NoLast in it as [].
      1-31:try solve [rewrite Forall_map, Forall_forall in *; intros; eauto].
      1-24:try rewrite rename_in_exp_clockof; simpl.
      1-24:try rewrite rename_in_exp_clocksof; simpl.
      1-24:try (rewrite map_rename_in_ann_clock; rewrite Forall2_eq in *; congruence).
      - now rewrite H3.
      - now rewrite H5.
      - now rewrite H6.
      - rewrite Forall_map. eapply Forall_impl; [|eauto]; intros ? Hun.
        inv Hun; simpl in *; subst. constructor.
      - now rewrite map_length.
      - contradict H4. apply map_eq_nil in H4; auto.
      - simpl_Forall; eauto.
      - rewrite Forall_map. rewrite Forall_forall; intros (?&?) Hin; simpl.
        rewrite rename_in_exp_clocksof, Forall_map.
        simpl_Forall; subst; auto.
      - rewrite Forall_map. eapply Forall_impl; [|eapply H7]; eauto; intros (?&?) ?; simpl in *.
        now rewrite rename_in_exp_clocksof, map_length.
      - now rewrite H6.
      - contradict H7. apply map_eq_nil in H7; auto.
      - simpl_Forall; eauto.
      - rewrite Forall_map. rewrite Forall_forall; intros (?&?) Hin; simpl.
        rewrite rename_in_exp_clocksof. simpl_Forall; subst; auto.
      - rewrite Forall_map. eapply Forall_impl; [|eapply H10]; eauto; intros (?&?) ?; simpl in *.
        now rewrite rename_in_exp_clocksof, map_length.
      - intros ? Hopt. eapply option_map_inv in Hopt as (?&?&?); subst; simpl in *.
        specialize (H11 _ eq_refl). simpl_Forall; eauto.
      - intros ? Hopt. eapply option_map_inv in Hopt as (?&?&?); subst; simpl in *.
        specialize (H12 _ eq_refl).
        rewrite rename_in_exp_clocksof, Forall_map. eapply Forall_impl; [|eauto]; intros; subst; auto.
      - intros ? Hopt. eapply option_map_inv in Hopt as (?&?&?); subst; simpl in *.
        specialize (H13 _ eq_refl).
        now rewrite rename_in_exp_clocksof, map_length.
      - rewrite rename_in_exp_nclocksof. simpl_Forall.
        eapply rename_in_nclock_WellInstantiated1; eauto.
      - simpl_Forall.
        eapply rename_in_nclock_WellInstantiated2; eauto.
      - rewrite Forall_map. eapply Forall_impl; [|eauto]; intros ? (?&Hck).
        rewrite rename_in_exp_clockof, Hck; simpl; eauto.
    Qed.

    Lemma rename_in_equation_wc : forall eq,
        wc_equation G Γ eq ->
        wc_equation G Γ' (rename_in_equation sub eq).
    Proof.
      intros (?&?) Hwc. inv Hwc; simpl.
      - (* app *)
        econstructor; eauto.
        + simpl_Forall; eauto using rename_in_exp_wc.
        + simpl_Forall; eauto using rename_in_exp_wc.
        + rewrite rename_in_exp_nclocksof. simpl_Forall.
          eapply rename_in_nclock_WellInstantiated1; eauto.
        + rewrite 2 Forall3_map_2, Forall3_map_3. rewrite Forall3_map_2 in H5.
          eapply Forall3_impl_In; [|eauto]; intros (?&?) (?&?) ? _ _ _ ?; simpl.
          eapply rename_in_nclock_WellInstantiated1 in H; eauto. eapply H.
        + rewrite Forall_map. eapply Forall_impl; [|eauto]; intros ? (?&Hck).
          rewrite rename_in_exp_clockof, Hck; simpl; eauto.
        + simpl_Forall; eauto using rename_in_var_wc.
      - (* general case *)
        econstructor; eauto.
        + simpl_Forall; eauto using rename_in_exp_wc.
        + rewrite rename_in_exp_clocksof. simpl_Forall; eauto using rename_in_var_wc.
    Qed.

  End rename.

  Import Fresh Facts Tactics.

  Fact In_sub1 : forall vars1 vars2 vars3 sub,
      (forall x, InMembers x vars1 -> ~InMembers x vars2) ->
      (forall x, Env.In x sub <-> InMembers x vars2) ->
      (forall x y ck, Env.find x sub = Some y -> HasClock vars2 x ck -> HasClock vars3 y (rename_in_clock sub ck)) ->
      forall x y ck, Env.find x sub = Some y -> HasClock (vars1 ++ vars2) x ck -> HasClock (vars1 ++ vars3) y (rename_in_clock sub ck) .
  Proof.
    intros * Hnd Hsubin Hsub * Hfind Hin.
    rewrite HasClock_app in *. destruct Hin as [Hin|Hin]; eauto.
    exfalso. inv Hin. eapply Hnd; eauto using In_InMembers.
    eapply Hsubin. econstructor; eauto.
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

  Fact In_sub2 : forall vars1 vars2 vars3 sub,
      wc_env (idck vars1) ->
      (forall x, InMembers x vars1 -> ~InMembers x vars2) ->
      (forall x, Env.In x sub <-> InMembers x vars2) ->
      (forall x y ck, Env.find x sub = Some y -> HasClock vars2 x ck -> HasClock vars3 y (rename_in_clock sub ck)) ->
      forall x ck, Env.find x sub = None -> HasClock (vars1 ++ vars2) x ck -> HasClock (vars1 ++ vars3) x (rename_in_clock sub ck).
  Proof.
    intros * Hwenv Hnin Hsubin Hsub * Hfind Hin.
    rewrite HasClock_app in *. destruct Hin as [Hin|Hin]; eauto.
    - erewrite rename_in_clock_idem with (vars:=idck vars1); eauto.
      + intros. rewrite Hsubin; eauto. eapply Hnin.
        erewrite fst_InMembers in H. rewrite fst_InMembers. solve_In.
      + inv Hin. eapply Forall_forall in Hwenv; eauto. 2:solve_In. auto.
    - exfalso. inv Hin. eapply In_InMembers, Hsubin in H as (?&?).
      congruence.
  Qed.

  Local Hint Resolve In_sub1 In_sub2 : lclocking.

  Definition st_senv st := senv_of_tyck (st_anns st).

  Fact mmap_inlinelocal_block_wc {PSyn prefs} (G: @global PSyn prefs) sub Γ Γ' : forall blks blks' st st',
      Forall (fun blk => forall sub Γ' blks' st st',
                  (forall x, ~IsLast (Γ++Γ') x) ->
                  (forall x, InMembers x Γ -> ~InMembers x Γ') ->
                  (forall x, Env.In x sub <-> InMembers x Γ') ->
                  (forall x y ck, Env.find x sub = Some y -> HasClock Γ' x ck -> HasClock (st_senv st) y (rename_in_clock sub ck)) ->
                  (forall x y, Env.MapsTo x y sub -> exists n, y = gensym local (Some x) n) ->
                  noswitch_block blk ->
                  NoDupLocals (map fst Γ++map fst Γ') blk ->
                  GoodLocals switch_prefs blk ->
                  wc_env (idck Γ) ->
                  wc_env (idck (Γ++Γ')) ->
                  wc_block G (Γ++Γ') blk ->
                  Forall (wc_clock (idck (Γ ++ st_senv st))) (map (fun '(_, (_, ck)) => ck) (st_anns st)) ->
                  st_valid_after st local PS.empty ->
                  inlinelocal_block sub blk st = (blks', st') ->
                  Forall (wc_block G (Γ ++ st_senv st')) blks' /\
                  Forall (wc_clock (idck (Γ ++ st_senv st'))) (map (fun '(_, (_, ck)) => ck) (st_anns st'))) blks ->
      (forall x, ~IsLast (Γ++Γ') x) ->
      (forall x, InMembers x Γ -> ~InMembers x Γ') ->
      (forall x, Env.In x sub <-> InMembers x Γ') ->
      (forall x y ck, Env.find x sub = Some y -> HasClock Γ' x ck -> HasClock (st_senv st) y (rename_in_clock sub ck)) ->
      (forall x y, Env.MapsTo x y sub -> exists n, y = gensym local (Some x) n) ->
      Forall noswitch_block blks ->
      Forall (NoDupLocals (map fst Γ++map fst Γ')) blks ->
      Forall (GoodLocals switch_prefs) blks ->
      wc_env (idck Γ) ->
      wc_env (idck (Γ++Γ')) ->
      Forall (wc_block G (Γ++Γ')) blks ->
      Forall (wc_clock (idck (Γ ++ st_senv st))) (map (fun '(_, (_, ck)) => ck) (st_anns st)) ->
      st_valid_after st local PS.empty ->
      mmap (inlinelocal_block sub) blks st = (blks', st') ->
      Forall (wc_block G (Γ ++ st_senv st')) (concat blks') /\
      Forall (wc_clock (idck (Γ ++ st_senv st'))) (map (fun '(_, (_, ck)) => ck) (st_anns st')).
  Proof.
    induction blks; intros * Hf Hnl Hnin Hsubin Hsub Hsubgensym Hns Hnd Hgood Hwenv Hwenv2 Hwc Hwcc Hvalid Hmmap;
      inv Hf; inv Hns; inv Hnd; inv Hgood; inv Hwc; repeat inv_bind; simpl; auto.
    assert (Hdl:=H). eapply H1 in H as (?&?); eauto.
    assert (Hmap:=H0). eapply IHblks in H0 as (?&?); eauto.
    2:{ intros * Hfind Hin.
        eapply HasClock_incl; eauto. eapply incl_map, st_follows_incl; eauto with fresh. }
    2:eapply inlinelocal_block_st_valid_after; eauto.
    constructor; auto.
    apply Forall_app. split; eauto.
    eapply Forall_impl; [|eauto]; intros.
    assert (st_follows x0 st') as Hfollows.
    { eapply mmap_st_follows; eauto. simpl_Forall; eauto with fresh. }
    eapply wc_block_incl; [| |eauto].
    - intros * Hty. rewrite HasClock_app in *. destruct Hty; auto; right.
      eapply HasClock_incl; eauto. eapply incl_map, st_follows_incl; eauto.
    - intros * Hty. rewrite IsLast_app in *. destruct Hty; auto; right.
      eapply IsLast_incl; eauto. eapply incl_map, st_follows_incl; eauto.
  Qed.

  Global Hint Resolve -> fst_InMembers : datatypes.
  Global Hint Resolve <- fst_InMembers : datatypes.
  Global Hint Resolve in_or_app In_InMembers : datatypes.

  Lemma inlinelocal_block_wc {PSyn prefs} (G: @global PSyn prefs) Γ : forall blk sub Γ' blks' st st',
      (forall x, ~IsLast (Γ++Γ') x) ->
      (forall x, InMembers x Γ -> ~InMembers x Γ') ->
      (forall x, Env.In x sub <-> InMembers x Γ') ->
      (forall x y ck, Env.find x sub = Some y -> HasClock Γ' x ck -> HasClock (st_senv st) y (rename_in_clock sub ck)) ->
      (forall x y, Env.MapsTo x y sub -> exists n, y = gensym local (Some x) n) ->
      noswitch_block blk ->
      NoDupLocals (map fst Γ++map fst Γ') blk ->
      GoodLocals switch_prefs blk ->
      wc_env (idck Γ) ->
      wc_env (idck (Γ++Γ')) ->
      wc_block G (Γ++Γ') blk ->
      Forall (wc_clock (idck (Γ++st_senv st))) (map (fun '(_, (_, ck)) => ck) (st_anns st)) ->
      st_valid_after st local PS.empty ->
      inlinelocal_block sub blk st = (blks', st') ->
      Forall (wc_block G (Γ++st_senv st')) blks' /\
      Forall (wc_clock (idck (Γ++st_senv st'))) (map (fun '(_, (_, ck)) => ck) (st_anns st')).
  Proof.
    induction blk using block_ind2; intros * Hnl Hnin Hsubin Hsub Hsubgensym Hns Hgood Hnd Hwenv Hwenv2 Hwc Hwcc Hvalid Hdl;
      inv Hns; inv Hnd; inv Hgood; inv Hwc; repeat inv_bind.

    - (* equation *)
      split; auto.
      do 2 constructor; auto.
      eapply rename_in_equation_wc; [| | |eauto]; eauto with lclocking.

    - (* reset *)
      repeat econstructor; eauto.
      + eapply mmap_inlinelocal_block_wc; eauto.
      + eapply rename_in_exp_wc; [| | |eauto]; eauto using in_or_app.
        eapply In_sub1; eauto. 2:eapply In_sub2; eauto.
        1,2:(intros; eapply HasClock_incl; [|eauto];
             eapply incl_map, st_follows_incl, mmap_st_follows; eauto with lclocking;
             eapply Forall_forall; eauto with fresh).
      + rewrite rename_in_exp_clockof, H8; simpl; eauto.
      + eapply mmap_inlinelocal_block_wc; eauto.

    - (* local *)
      assert (forall x, Env.In x x0 <-> InMembers x locs) as Hsubin'.
      { intros. split; intros * Hin.
        - eapply fresh_idents_rename_sub1 in Hin; [|eauto].
          unfold idty in *. erewrite fst_InMembers, map_map, map_ext, <-fst_InMembers in Hin; eauto.
          intros; destruct_conjs; auto.
        - eapply fresh_idents_rename_sub2 in H0.
          unfold idty in *. erewrite fst_InMembers, map_map, map_ext, <-fst_InMembers in H0; eauto.
          2:intros; destruct_conjs; auto.
          apply H0 in Hin as (?&?&?&_); eauto. econstructor; eauto.
      }
      assert (forall x, InMembers x (st_anns st) -> ~InMembers x locs) as Hdisj.
      { intros * Hinm1 Hinm2. rewrite fst_InMembers in Hinm1. rewrite fst_InMembers in Hinm2.
        eapply st_valid_after_AtomOrGensym_nIn in Hinm1; eauto using local_not_in_switch_prefs.
        eapply Forall_forall; eauto. }
      assert (forall x : Env.key, Env.In x sub -> ~Env.In x x0) as Hsub1.
      { intros ?. rewrite Hsubin, Hsubin'. intros Hin1 Hin2.
        eapply H9; eauto with datatypes. }
      assert (forall x y, Env.MapsTo x y sub -> ~ Env.In y x0) as Hsub2.
      { intros ??. rewrite Hsubin'. intros Hin1 Hin2.
        eapply Hsubgensym in Hin1 as (?&Hgen); subst.
        eapply fst_InMembers, Forall_forall in Hin2; eauto.
        eapply contradict_AtomOrGensym in Hin2; eauto using local_not_in_switch_prefs.
      }
      eapply mmap_inlinelocal_block_wc with (Γ':=Γ'++senv_of_locs locs) in H1. 1-15:eauto.
      + rewrite app_assoc, NoLast_app. split; auto.
        intros * Hl. inv Hl; simpl_In. simpl_Forall. subst; simpl in *; congruence.
      + intros ? Hin. rewrite InMembers_app, not_or', InMembers_senv_of_locs.
        split; auto. intro contra.
        eapply H9; eauto with datatypes.
      + intros. rewrite Env.union_In, InMembers_app, InMembers_senv_of_locs, Hsubin.
        apply or_iff_compat_l; auto.
      + intros * Hfind Hin.
        eapply HasClock_app in Hin as [Hin|Hin].
        * assert (Env.find x3 x0 = None) as Hnone.
          { inv Hin. eapply In_InMembers, fst_InMembers in H7.
            destruct (Env.find x3 x0) eqn:Hfind'; eauto.
            exfalso. eapply H9; eauto with datatypes. eapply fst_InMembers.
            eapply fresh_idents_rename_sub1 in H0. 2:econstructor; eauto.
            erewrite fst_InMembers, map_map, map_ext in H0; eauto.
            intros; destruct_conjs; auto with datatypes. }
          eapply Env.union_find4 in Hfind as [Hfind|Hfind]; try congruence.
          eapply HasClock_incl; eauto using incl_map, st_follows_incl, fresh_idents_rename_st_follows.
          erewrite <-disjoint_union_rename_in_clock, rename_in_clock_idem; eauto.
          2:eapply rename_in_clock_wc with (Γ:=Γ++Γ'), wc_env_var; eauto with lclocking; eauto with datatypes.
          2:eapply In_sub1; eauto. 2:eapply In_sub2; eauto.
          2:{ inv Hin. solve_In; eauto using in_or_app. auto. }
          intros ?. simpl_app. rewrite Hsubin', InMembers_app. intros [Hinm1|Hinm1] Hinm2.
          -- eapply H9; eauto with datatypes. apply InMembers_In in Hinm1 as (?&?); simpl_In.
             apply in_or_app, or_introl; solve_In.
          -- eapply Hdisj; eauto. rewrite fst_InMembers in Hinm1. rewrite fst_InMembers. solve_In.
        * unfold st_senv. erewrite fresh_idents_rename_anns; [|eauto].
          unfold senv_of_tyck. simpl_app. apply HasClock_app, or_introl. inv Hin; simpl_In.
          assert (Hfresh:=H0). eapply fresh_idents_rename_sub2 in H0 as ((?&?&Hmap&_)&_).
          { eapply In_InMembers. solve_In. }
          unfold Env.MapsTo in *. erewrite Env.union_find3' in Hfind; [|eauto]. inv Hfind.
          eapply fresh_idents_rename_ids in Hfresh. rewrite Hfresh.
          2:{ apply nodupmembers_map; auto. intros; destruct_conjs; auto. }
          econstructor. solve_In. rewrite Hmap; simpl. eauto. simpl.
          apply disjoint_union_rename_in_clock; auto.
      + intros ?? Hfind. eapply Env.union_find4 in Hfind as [Hfind|Hfind]; eauto.
        eapply fresh_idents_rename_sub_gensym in Hfind; eauto.
      + rewrite map_app, map_fst_senv_of_locs, app_assoc; auto.
      + simpl_app. rewrite app_assoc.
        eapply Forall_app; split.
        * eapply Forall_impl; [|eauto]; intros (?&?) ?.
          eapply wc_clock_incl; [|eauto]. solve_incl_app.
        * simpl_Forall. simpl_app. auto.
      + rewrite app_assoc; auto.
      + erewrite fresh_idents_rename_anns; [|eauto]. simpl_app.
        apply Forall_app; split.
        * assert (Hfresh:=H0). eapply fresh_idents_rename_ids in H0. rewrite H0.
          2:{ apply nodupmembers_map; auto. intros; destruct_conjs; auto. }
          simpl_Forall. rewrite <-map_app.
          eapply rename_in_clock_wc, rename_in_clock_wc
            with (Γ':=Γ++map (fun '(x, a) => (x, ann_with_clock a (rename_in_clock sub a.(clo)))) (senv_of_locs locs)++st_senv st).
          5:repeat rewrite <-map_app in H12; eauto.
          4:{ intros ?? Hfind Hin. repeat rewrite HasClock_app in *. destruct Hin as [Hin|[Hin|Hin]]; auto.
              - left. erewrite rename_in_clock_idem with (vars:=idck Γ); eauto.
                2:{ inv Hin. eapply wc_env_var; eauto. solve_In. }
                intros * Hinm. rewrite Hsubin; eauto.
                apply Hnin. rewrite fst_InMembers in Hinm. rewrite fst_InMembers. solve_In.
              - exfalso. inv Hin. eapply In_InMembers, Hsubin in H11 as (?&?). congruence.
              - right; left. inv Hin; simpl_In. econstructor; solve_In. auto. }
          3:{ intros ??? Hfind Hin. repeat rewrite HasClock_app in *. destruct Hin as [Hin|[Hin|Hin]]; eauto.
              - exfalso. inv Hin. eapply In_InMembers, Hnin in H11.
                eapply H11, Hsubin. econstructor; eauto.
              - exfalso. inv Hin. simpl_In.
                eapply H9; eauto using In_InMembers.
                eapply in_or_app, or_intror, fst_InMembers.
                eapply Hsubin. econstructor; eauto. }
          2:{ unfold st_senv. apply fresh_idents_rename_anns in Hfresh. rewrite Hfresh.
              unfold senv_of_tyck. simpl_app.
              intros ?? Hfind Hin. repeat rewrite HasClock_app in *. destruct Hin as [Hin|[Hin|Hin]]; auto.
              - left. erewrite rename_in_clock_idem with (vars:=idck Γ); eauto.
                2:{ inv Hin. eapply wc_env_var; eauto. solve_In. }
                intros ? Hinm. rewrite Hsubin'. intros contra. rewrite fst_InMembers in Hinm.
                eapply H9; eauto. rewrite in_app_iff. left. solve_In.
              - exfalso. inv Hin; simpl_In.
                eapply In_InMembers, Hsubin' in Hin0 as (?&?). congruence.
              - do 2 right. inv Hin. simpl_In.
                erewrite rename_in_clock_idem; eauto. econstructor; solve_In. auto.
                2:{ simpl_Forall. eauto. }
                intros ? Hinm. rewrite Hsubin'. intros contra.
                eapply InMembers_app in Hinm as [Hinm|Hinm]; rewrite fst_InMembers in Hinm.
                + eapply H9; eauto with datatypes. apply in_or_app, or_introl. solve_In.
                + simpl_In.
                  eapply Hdisj; eauto using In_InMembers.
          }
          { intros ??? Hfind Hin.
            unfold st_senv. erewrite fresh_idents_rename_anns; [|eauto].
            unfold senv_of_tyck. simpl_app.
            eapply fresh_idents_rename_sub1 in Hfresh. 2:econstructor; eauto.
            erewrite fst_InMembers, map_map, map_ext, <-fst_InMembers in Hfresh.
            2:intros; destruct_conjs; auto.
            repeat rewrite HasClock_app in *. destruct Hin as [Hin|[Hin|Hin]]; auto.
            - exfalso. eapply H9; eauto.
              apply in_or_app, or_introl. inv Hin; solve_In.
            - right; left. inv Hin; simpl_In. econstructor; solve_In.
              rewrite Hfind; auto. auto.
            - exfalso. inv Hin. simpl_In.
              eapply Hdisj; eauto using In_InMembers.
          }
        * eapply Forall_impl; [|eauto]; intros.
          eapply wc_clock_incl; [|eauto]; solve_incl_app.
          apply incl_map, incl_map, st_follows_incl; eauto using fresh_idents_rename_st_follows.
      + eapply fresh_idents_rename_st_valid; eauto.
  Qed.

  Lemma inlinelocal_topblock_wc {PSyn prefs} (G: @global PSyn prefs) Γ : forall blk blks' locs' st st',
      (forall x, ~IsLast Γ x) ->
      noswitch_block blk ->
      NoDupLocals (map fst Γ) blk ->
      GoodLocals switch_prefs blk ->
      wc_env (idck Γ) ->
      wc_block G Γ blk ->
      Forall (wc_clock (idck (Γ++st_senv st))) (map (fun '(_, (_, ck)) => ck) (st_anns st)) ->
      st_valid_after st local PS.empty ->
      inlinelocal_topblock blk st = (blks', locs', st') ->
      Forall (wc_block G (Γ++senv_of_locs locs'++st_senv st')) blks' /\
      Forall (wc_clock (idck (Γ++senv_of_locs locs'++st_senv st')))
             (map (fun '(_, (_, ck, _, _)) => ck) locs'++map (fun '(_, (_, ck)) => ck) (st_anns st')).
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hnl Hns Hnd Hgood Hwenv Hwc Hwcck Hvalid Hil; repeat inv_bind; simpl.
    3:inv Hns.
    1,2:eapply inlinelocal_block_wc with (Γ':=[]); try rewrite app_nil_r; eauto.
    7:inv Hns; inv Hnd; inv Hgood; inv Hwc; eapply mmap_inlinelocal_block_wc with (Γ:=Γ++senv_of_locs locs') (Γ':=[]) in H as (Hwc1&Hwc2); try rewrite app_nil_r; eauto.
    1,4,10:intros *; rewrite Env.Props.P.F.empty_in_iff; split; intros [].
    1,3,8:intros * Hfind _; rewrite Env.gempty in Hfind; try congruence.
    1,2,6:intros * Hfind; eapply Env.Props.P.F.empty_mapsto_iff in Hfind as [].
    - simpl_app. split; auto. rewrite Forall_app; split; simpl_Forall; auto.
      eapply wc_clock_incl; [|eauto]. solve_incl_app.
    - eapply Forall_forall; intros; eauto using inlinelocal_block_wc.
    - rewrite NoLast_app. split; auto.
      intros * Hl. inv Hl. simpl_In. simpl_Forall. subst; simpl in *; congruence.
    - now rewrite map_app, map_fst_senv_of_locs.
    - simpl_app. eapply Forall_app; split.
      + eapply Forall_impl; [|eauto]; intros (?&?) ?.
        eapply wc_clock_incl; [|eauto]; solve_incl_app.
      + simpl_Forall; auto.
    - simpl_app. eapply Forall_app; split.
      + eapply Forall_impl; [|eauto]; intros (?&?) ?.
        eapply wc_clock_incl; [|eauto]; solve_incl_app.
      + simpl_Forall; auto.
    - simpl_Forall.
      eapply wc_clock_incl; [|eauto]; solve_incl_app.
    Transparent inlinelocal_block.
  Qed.

  Lemma inlinelocal_node_wc : forall G1 G2 n,
      global_iface_eq G1 G2 ->
      wc_node G1 n ->
      wc_node G2 (inlinelocal_node n).
  Proof.
    unfold inlinelocal_node, wc_node; simpl.
    intros * Hiface (Hwc1&Hwc2&Hwc3).
    pose proof (n_nodup n) as (_&Hnd2).
    pose proof (n_good n) as (_&Hgood&_).
    pose proof (n_syn n) as Hsyn.
    destruct (inlinelocal_topblock _ _) as ((?&?)&?) eqn:Hdl.
    repeat split; auto.
    assert (Hinl:=Hdl). eapply inlinelocal_topblock_wc
                          with (Γ:=senv_of_inout (n_in n ++ n_out n)) in Hdl as (?&?); try rewrite app_nil_r; eauto.
    - repeat econstructor; simpl; eauto;
        repeat rewrite idty_app in *; repeat rewrite idck_app in *; repeat rewrite map_app in *.
      2:rewrite Forall_app in H0; destruct H0 as (Hwc4&Hwc5).
      2:rewrite Forall_app; split.
      + simpl_Forall. unfold st_senv, senv_of_tyck in *.
        eapply iface_eq_wc_block, wc_block_incl; [eauto| | |eauto]; intros * ?.
        * eapply HasClock_incl; [|eauto].
          simpl_app. solve_incl_app. erewrite map_map, map_ext. reflexivity.
          intros; destruct_conjs; auto.
        * eapply IsLast_incl; [|eauto].
          simpl_app. solve_incl_app. erewrite map_map, map_ext. reflexivity.
          intros; destruct_conjs; auto.
      + simpl_Forall. unfold st_senv, senv_of_tyck in *.
        eapply wc_clock_incl; eauto.
        simpl_app. solve_incl_app. erewrite 3 map_map, map_ext. reflexivity.
        intros; destruct_conjs; auto.
      + simpl_Forall. unfold st_senv, senv_of_tyck in *.
        eapply wc_clock_incl; eauto.
        simpl_app. solve_incl_app. erewrite 3 map_map, map_ext. reflexivity.
        intros; destruct_conjs; auto.
      + simpl_Forall. apply in_app_iff in H1 as [|]; simpl_In; auto.
        eapply inlinelocal_topblock_nolast in Hinl; eauto.
        simpl_Forall. subst; simpl; auto.
    - apply senv_of_inout_NoLast.
    - now rewrite map_fst_senv_of_inout.
    - unfold idck, senv_of_inout. erewrite map_map, map_ext; eauto.
      intros; destruct_conjs; auto.
    - rewrite init_st_anns; simpl; auto.
    - eapply init_st_valid; eauto using local_not_in_switch_prefs, PS_For_all_empty.
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
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (IL  : INLINELOCAL Ids Op OpAux Cks Senv Syn)
       <: ILCLOCKING Ids Op OpAux Cks Senv Syn Clo IL.
  Include ILCLOCKING Ids Op OpAux Cks Senv Syn Clo IL.
End ILClockingFun.
