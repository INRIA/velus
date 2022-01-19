From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Lustre.ClockSwitch.ClockSwitch.

Module Type CSCLOCKING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (Import CS : CLOCKSWITCH Ids Op OpAux Cks Syn).

  Section subclock.
    Variable bck : clock.
    Variable sub : Env.t ident.
    Variable vars vars' : list (ident * clock).

    Hypothesis Hsub : forall x y ck,
        Env.find x sub = Some y ->
        In (x, ck) vars ->
        In (y, subclock_clock bck sub ck) vars'.

    Hypothesis Hnsub : forall x ck,
        Env.find x sub = None ->
        In (x, ck) vars ->
        In (x, subclock_clock bck sub ck) vars'.

    Lemma rename_var_wc : forall x ck,
        In (x, ck) vars ->
        In (rename_var sub x, subclock_clock bck sub ck) vars'.
    Proof.
      unfold rename_var.
      intros * Hin.
      destruct (Env.find _ _) eqn:Hfind; simpl in *; eauto.
    Qed.

    Context {PSyn : block -> Prop} {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Hypothesis Hwbck : wc_clock vars' bck.

    Lemma subclock_clock_wc : forall ck,
        wc_clock vars ck ->
        wc_clock vars' (subclock_clock bck sub ck).
    Proof.
      induction ck; intros * Hwc; inv Hwc; simpl; auto.
      constructor; eauto using rename_var_wc.
    Qed.

    Lemma add_whens_wc : forall e ty,
        clockof e = [Cbase] ->
        wc_exp G vars' [] e ->
        wc_exp G vars' [] (add_whens e ty bck).
    Proof.
      clear Hsub Hnsub.
      induction bck as [|??? (?&?)]; intros * Hbase Hwc; inv Hwbck;
        simpl in *; auto.
      econstructor; eauto; simpl; rewrite app_nil_r.
      1,2:rewrite add_whens_clockof; auto.
    Qed.

    Lemma subclock_clock_instck : forall sub1 sub0 bck' ck ck',
        instck bck' sub0 ck = Some ck' ->
        instck (subclock_clock bck sub1 bck') (fun x0 => option_map (rename_var sub1) (sub0 x0)) ck = Some (subclock_clock bck sub1 ck').
    Proof.
      induction ck; intros * Hinst; simpl in *.
      - inv Hinst; auto.
      - cases_eqn Heq; inv Hinst; simpl in *.
        + inv Heq2; simpl.
          specialize (IHck _ eq_refl). now inv IHck.
        + congruence.
        + specialize (IHck _ eq_refl). congruence.
    Qed.

    Lemma subclock_nclock_WellInstantiated1 : forall bck' sub0 sub xck nck,
        WellInstantiated bck' sub0 xck nck ->
        WellInstantiated (subclock_clock bck sub bck') (fun x => option_map (rename_var sub) (sub0 x)) xck (subclock_nclock bck sub nck).
    Proof.
      intros ??? (x&ck) (ck'&name) (Hw1&Hw2). split; simpl in *.
      - rewrite Hw1. destruct name; simpl; auto.
      - apply subclock_clock_instck; auto.
    Qed.

    Lemma subclock_nclock_WellInstantiated2 : forall bck' sub0 sub xck ck,
        WellInstantiated bck' sub0 xck (ck, None) ->
        WellInstantiated (subclock_clock bck sub bck') (fun x => option_map (rename_var sub) (sub0 x)) xck (subclock_clock bck sub ck, None).
    Proof.
      intros ??? (x&ck) ck' (Hw1&Hw2). split; simpl in *.
      - rewrite Hw1. reflexivity.
      - apply subclock_clock_instck; auto.
    Qed.

    Lemma subclock_exp_wc : forall e,
        wc_exp G vars [] e ->
        wc_exp G vars' [] (subclock_exp bck sub e).
    Proof with eauto with lclocking.
      induction e using exp_ind2; intros * Hwc; inv Hwc; simpl in *.
      3-12:econstructor; simpl in *; eauto using rename_var_wc with lclocking.
      1-33:try solve [rewrite Forall_map, Forall_forall in *; intros; eauto].
      1-26:try rewrite subclock_exp_clockof.
      1-26:try rewrite subclock_exp_clocksof.
      1-26:try (rewrite map_subclock_ann_clock; rewrite Forall2_eq in *; congruence).
      - apply add_whens_wc...
      - apply add_whens_wc...
      - take (clockof e = [_]) and rewrite it; auto.
      - take (clockof e1 = [_]) and rewrite it; auto.
      - take (clockof e2 = [_]) and rewrite it; auto.
      - rewrite Forall_map. eapply Forall_impl; [|eauto]; intros ??; subst; auto.
      - rewrite map_length; auto.
      - contradict H4. apply map_eq_nil in H4; auto.
      - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite Forall_map.
        specialize (H _ Hin). specialize (H5 _ Hin).
        rewrite Forall_forall in *; eauto.
      - rewrite Forall_map. rewrite Forall_forall; intros (?&?) Hin; simpl.
        rewrite subclock_exp_clocksof, Forall_map.
        eapply Forall_forall in H6; eauto; simpl in H6.
        eapply Forall_impl; [|eauto]; intros; subst; auto.
      - rewrite Forall_map. eapply Forall_impl; [|eapply H7]; eauto; intros (?&?) ?; simpl in *.
        now rewrite subclock_exp_clocksof, map_length.
      - now rewrite H6.
      - contradict H7. apply map_eq_nil in H7; auto.
      - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite Forall_map.
        specialize (H _ Hin). specialize (H8 _ Hin).
        rewrite Forall_forall in *; eauto.
      - rewrite Forall_map. rewrite Forall_forall; intros (?&?) Hin; simpl.
        rewrite subclock_exp_clocksof, Forall_map.
        eapply Forall_forall in H9; eauto; simpl in H9.
        eapply Forall_impl; [|eauto]; intros; subst; auto.
      - rewrite Forall_map. eapply Forall_impl; [|eapply H10]; eauto; intros (?&?) ?; simpl in *.
        now rewrite subclock_exp_clocksof, map_length.
      - intros ? Hopt. eapply option_map_inv in Hopt as (?&?&?); subst; simpl in *.
        specialize (H11 _ eq_refl).
        rewrite Forall_map. rewrite Forall_forall in *; eauto.
      - intros ? Hopt. eapply option_map_inv in Hopt as (?&?&?); subst; simpl in *.
        specialize (H12 _ eq_refl).
        rewrite subclock_exp_clocksof, Forall_map. eapply Forall_impl; [|eauto]; intros; subst; auto.
      - intros ? Hopt. eapply option_map_inv in Hopt as (?&?&?); subst; simpl in *.
        specialize (H13 _ eq_refl).
        now rewrite subclock_exp_clocksof, map_length.
      - rewrite subclock_exp_nclocksof, Forall2_map_2.
        eapply Forall2_impl_In; [|eauto]; intros.
        eapply subclock_nclock_WellInstantiated1; eauto.
      - rewrite 2 Forall2_map_2. rewrite Forall2_map_2 in H9.
        eapply Forall2_impl_In; [|eauto]; intros (?&?) (?&?) _ _ ?; simpl in *.
        eapply subclock_nclock_WellInstantiated2; eauto.
      - rewrite Forall_map. eapply Forall_impl; [|eauto]; intros ? (?&Hck).
        rewrite subclock_exp_clockof, Hck; simpl; eauto.
    Qed.

    Lemma subclock_equation_wc : forall eq,
        wc_equation G vars [] eq ->
        wc_equation G vars' [] (subclock_equation bck sub eq).
    Proof.
      intros (?&?) Hwc. inv Hwc; simpl.
      - (* app *)
        econstructor; eauto.
        + rewrite Forall_map.
          eapply Forall_impl; [|eauto]; intros; eauto using subclock_exp_wc.
        + rewrite Forall_map.
          eapply Forall_impl; [|eapply H2]; intros; eauto using subclock_exp_wc.
        + rewrite subclock_exp_nclocksof, Forall2_map_2.
          eapply Forall2_impl_In; [|eauto]; intros.
          eapply subclock_nclock_WellInstantiated1; eauto.
        + rewrite 2 Forall3_map_2, Forall3_map_3. rewrite Forall3_map_2 in H5.
          eapply Forall3_impl_In; [|eauto]; intros (?&?) (?&?) ? _ _ _ ?; simpl.
          eapply subclock_nclock_WellInstantiated1 in H; eauto. eapply H.
        + rewrite Forall_map. eapply Forall_impl; [|eauto]; intros ? (?&Hck).
          rewrite subclock_exp_clockof, Hck; simpl; eauto.
        + rewrite Forall2_map_1, 2 Forall2_map_2. rewrite Forall2_map_2 in H7.
          eapply Forall2_impl_In; [|eauto]; intros. eapply rename_var_wc; eauto.
      - (* general case *)
        econstructor; eauto.
        + rewrite Forall_map.
          eapply Forall_impl; [|eauto]; intros; eauto using subclock_exp_wc.
        + rewrite subclock_exp_clocksof, Forall2_map_1, Forall2_map_2.
          eapply Forall2_impl_In; [|eauto]; intros; eauto using rename_var_wc.
    Qed.

  End subclock.

  Import Fresh Facts Tactics.

  Section switch_block.

    Context {PSyn : block -> Prop} {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Hypothesis HwG : wc_global G.

    Import Permutation.

    Lemma cond_eq_wc vars : forall e ty ck x xcs eqs' st st',
        wc_exp G vars [] e ->
        clockof e = [ck] ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        Forall (wc_equation G (vars++idck xcs) []) eqs'.
    Proof.
      intros * Hwc Hck Hcond; destruct e; repeat inv_bind.
      3:destruct a; repeat inv_bind; auto.
      1-11:constructor; auto; rewrite Permutation_app_comm; simpl.
      1-11:(constructor; [constructor; auto; eapply wc_exp_incl; eauto; eauto with datatypes|]).
      1-11:simpl; try rewrite app_nil_r.
      1-11:take (_ = [_]) and rewrite it; eauto.
    Qed.

    Lemma cond_eq_wc_clock vars : forall e ty ck x xcs eqs' st st',
        wc_clock vars ck ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        Forall (wc_clock vars) (map snd (idck xcs)).
    Proof.
      intros * Hck Hcond; destruct e; repeat inv_bind; simpl; auto.
      destruct a; repeat inv_bind; simpl; auto.
    Qed.

    Lemma cond_eq_In vars : forall e ty ck x xcs eqs' st st',
        wc_exp G vars [] e ->
        clockof e = [ck] ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        In (x, ck) (vars ++ idck xcs).
    Proof.
      intros * Hwc Hck Hcond; destruct e; repeat inv_bind; simpl in *; auto with datatypes.
      inv Hwc. repeat inv_bind.
      inv Hck; auto with datatypes.
    Qed.

    Lemma new_idents_wc vars' : forall ck x ty k ids ids' st st',
        wc_clock vars' ck ->
        In (x, ck) vars' ->
        new_idents ck x ty k ids st = (ids', st') ->
        Forall (wc_clock vars') (map snd (idck (idty (idty (map (fun '(_, x1, (ty, ck0)) => (x1, (ty, ck0, xH, @None (exp * ident)))) ids'))))).
    Proof.
      intros * Hck Hin Hni.
      unfold new_idents in *. eapply mmap_values, Forall2_ignore1 in Hni.
      simpl_Forall. simpl_In. simpl_Forall. repeat inv_bind.
      econstructor; eauto.
    Qed.

    Lemma when_free_wc vars : forall x y ty ck cx tx k,
        In (x, ck) vars ->
        In (y, Con ck cx (tx, k)) vars ->
        In (cx, ck) vars ->
        wc_block G vars [] (when_free x y ty ck cx tx k).
    Proof.
      intros.
      repeat constructor; simpl; auto.
    Qed.

    Lemma merge_defs_wc vars : forall sub y ty ck x tx xcs,
        In (x, ck) vars ->
        In (rename_var sub y, ck) vars ->
        xcs <> [] ->
        Forall (fun '(k, sub) => In (rename_var sub y, Con ck x (tx, k)) vars) xcs ->
        wc_block G vars [] (merge_defs sub y ty ck x tx xcs).
    Proof.
      intros * Hin1 Hin2 Hcon Hnnil.
      repeat constructor; auto.
      - destruct xcs; simpl in *; try congruence.
      - rewrite Forall_map. eapply Forall_impl; [|eauto]; intros (?&?) ?.
        repeat constructor; auto.
      - rewrite Forall_map. eapply Forall_forall; intros (?&?) Hin; simpl.
        repeat constructor.
      - rewrite Forall_map. eapply Forall_forall; intros (?&?) Hin; simpl; auto.
    Qed.

    Lemma new_idents_In : forall x ck cx ty k ids1 ids2 nids1 nids2 st1 st2 st3 st4,
        NoDupMembers (ids1++ids2) ->
        InMembers x (ids1++ids2) ->
        new_idents ck cx ty k ids1 st1 = (nids1, st2) ->
        new_idents ck cx ty k ids2 st3 = (nids2, st4) ->
        In (rename_var (Env.from_list (map (fun '(x, y, _) => (x, y)) (nids1 ++ nids2))) x, Con ck cx (ty, k))
           (map (fun '(_, x, (_, ck)) => (x, ck)) (nids1++nids2)).
    Proof.
      intros * Hnd Hinm Hni1 Hni2.
      assert (NoDupMembers (map (fun '(x, y, _) => (x, y)) (nids1 ++ nids2))) as Hnd'.
      { erewrite fst_NoDupMembers, map_map, map_ext, map_app, 2 new_idents_old; eauto.
        rewrite <-map_app, <-fst_NoDupMembers; auto.
        intros ((?&?)&?&?); auto. }
      eapply mmap_values, Forall2_ignore2 in Hni1.
      eapply mmap_values, Forall2_ignore2 in Hni2.
      apply InMembers_In in Hinm as ((?&?)&Hin).
      apply in_app_iff in Hin as [Hin|Hin]; eapply Forall_forall in Hin; eauto; simpl in *.
      1,2:destruct Hin as (((?&?)&?&?)&Hin&?&?&?); repeat inv_bind.
      - eapply in_map_iff. do 2 esplit; eauto with datatypes; simpl.
        f_equal; auto.
        unfold rename_var. erewrite Env.find_In_from_list; eauto.
        2:eapply in_map_iff; do 2 esplit; eauto with datatypes; auto. auto.
      - eapply in_map_iff. do 2 esplit; eauto with datatypes; simpl.
        f_equal; auto.
        unfold rename_var. erewrite Env.find_In_from_list; eauto.
        2:eapply in_map_iff; do 2 esplit; eauto with datatypes; auto. auto.
    Qed.

    Fact switch_blocks_wc' : forall bck sub vars vars' blks blks' st st',
        Forall
          (fun blk => forall bck sub vars vars' blk' st st',
               (forall x, Env.In x sub -> InMembers x vars) ->
               (forall x y ck, Env.find x sub = Some y -> In (x, ck) (idck vars) -> In (y, subclock_clock bck sub ck) vars') ->
               (forall x ck, Env.find x sub = None -> In (x, ck) (idck vars) -> In (x, subclock_clock bck sub ck) vars') ->
               NoDupMembers vars ->
               wc_env (idck vars) ->
               wc_clock vars' bck ->
               nolast_block blk ->
               NoDupLocals (map fst vars) blk ->
               wc_block G (idck vars) [] blk ->
               switch_block vars bck sub blk st = (blk', st') ->
               wc_block G vars' [] blk') blks ->
        (forall x, Env.In x sub -> InMembers x vars) ->
        (forall x y ck, Env.find x sub = Some y -> In (x, ck) (idck vars) -> In (y, subclock_clock bck sub ck) vars') ->
        (forall x ck, Env.find x sub = None -> In (x, ck) (idck vars) -> In (x, subclock_clock bck sub ck) vars') ->
        NoDupMembers vars ->
        wc_env (idck vars) ->
        wc_clock vars' bck ->
        Forall nolast_block blks ->
        Forall (NoDupLocals (map fst vars)) blks ->
        Forall (wc_block G (idck vars) []) blks ->
        mmap (switch_block vars bck sub) blks st = (blks', st') ->
        Forall (wc_block G vars' []) blks'.
    Proof.
      induction blks; intros * Hf Hsubin Hsub Hnsub Hnd1 Hwenv Hbck Hnl Hnd2 Hwc Hmmap;
        inv Hf; inv Hnl; inv Hnd2; inv Hwc; repeat inv_bind; eauto.
    Qed.

    Lemma new_idents_In_inv_ck : forall ck cx tx k ids nids st st' x y ck1 ty,
        new_idents ck cx tx k ids st = (nids, st') ->
        In (x, y, (ty, ck1)) nids ->
        ck1 = Con ck cx (tx, k).
    Proof.
      intros * Hni Hin.
      eapply mmap_values, Forall2_ignore1, Forall_forall in Hni; eauto.
      destruct Hni as ((?&?&?)&?&?&?&?); repeat inv_bind; eauto.
    Qed.

    Lemma switch_block_wc : forall blk bck sub vars vars' blk' st st',
        (forall x, Env.In x sub -> InMembers x vars) ->
        (forall x y ck, Env.find x sub = Some y -> In (x, ck) (idck vars) -> In (y, subclock_clock bck sub ck) vars') ->
        (forall x ck, Env.find x sub = None -> In (x, ck) (idck vars) -> In (x, subclock_clock bck sub ck) vars') ->
        NoDupMembers vars ->
        wc_env (idck vars) ->
        wc_clock vars' bck ->
        nolast_block blk ->
        NoDupLocals (map fst vars) blk ->
        wc_block G (idck vars) [] blk ->
        switch_block vars bck sub blk st = (blk', st') ->
        wc_block G vars' [] blk'.
    Proof.
      induction blk using block_ind2; intros * Hsubin Hsub Hnsub Hnd1 Hwenv Hbck Hnl Hnd2 Hwc Hsw;
        inv Hnl; inv Hnd2; inv Hwc; repeat inv_bind; simpl in *.
      - (* equation *)
        constructor. eapply subclock_equation_wc; eauto.

      - (* reset *)
        econstructor; eauto using subclock_exp_wc.
        2:rewrite subclock_exp_clockof, H8; simpl; eauto.
        eapply switch_blocks_wc'; eauto.

      - (* switch *)
        destruct (partition _ _) eqn:Hpart; repeat inv_bind.
        apply partition_Partition in Hpart.
        destruct x; repeat inv_bind.
        assert (wc_clock vars' (subclock_clock bck sub ck)) as Hck'.
        { eapply subclock_clock_wc; eauto.
          eapply wc_exp_clockof in H4; eauto. 2:constructor.
          rewrite H5 in H4. apply Forall_singl in H4; auto. }
        rewrite subclock_exp_clockof, H5 in *; simpl in *.

        assert (In (i, subclock_clock bck sub ck)
                   (vars' ++ map (fun '(x4, (_, ck0, _, _)) => (x4, ck0))
                          (map (fun '(xc, (ty, ck0)) => (xc, (ty, ck0, 1%positive, @None (exp * ident)))) l1))) as Hini.
        { eapply cond_eq_In in H0; eauto using subclock_exp_wc.
          2:rewrite subclock_exp_clockof, H5; simpl; auto.
          clear - H0. unfold idck, idty in *. repeat rewrite map_app. repeat rewrite map_map.
          erewrite map_ext; eauto. intros (?&?&?); auto. }

        assert (NoDupMembers (filter (fun '(_, (_, ck')) => ck' ==b ck) l0 ++ l)) as Hnd'.
        { rewrite Permutation_app_comm.
          eapply switch_block_NoDupMembers_env; eauto. }

        econstructor; eauto; repeat rewrite idty_app; repeat rewrite idck_app; repeat rewrite map_app; repeat rewrite Forall_app; repeat split.
        + rewrite Forall_map. apply Forall_forall; intros (?&?&?) Hin.
          rewrite map_filter_nil.
          2:{ simpl_Forall. apply in_app_iff in H9 as [|]; simpl_In; auto. }
          eapply merge_defs_wc; eauto.
          * rewrite app_assoc. apply in_or_app; auto.
          * apply in_or_app; left.
            eapply rename_var_wc; eauto.
            assert (Is_defined_in i0 (Bswitch ec branches)) as Hdef.
            { eapply vars_defined_Is_defined_in.
              eapply Partition_Forall1, Forall_forall in Hpart; eauto; simpl in *.
              apply PSF.mem_2; auto. }
            inv Hdef. simpl_Exists.
            eapply Is_defined_in_wx_In in H12; [|eapply wc_block_wx_block; simpl_Forall; eauto].
            simpl_In. eapply H7 in Hin2 as (?&?); solve_In.
          * apply mmap_length in H2. destruct x, branches; simpl in *; try congruence.
          * eapply mmap_values, Forall2_ignore1 in H2. simpl_Forall.
            rewrite 2 in_app_iff. do 2 right. repeat inv_bind.
            eapply new_idents_In with (ids1:=filter _ _) in H13; eauto.
            2:eapply InMembers_app, or_intror, In_InMembers; eauto.
            solve_In; auto.
        + eapply CS.mmap2_values in H8. eapply mmap_values, Forall3_ignore3' with (zs:=x3) in H2.
          2:{ eapply Forall3_length in H8 as (?&?); congruence. }
          2:{ eapply mmap_length in H2; eauto. }
          eapply Forall3_Forall3 in H2; eauto. clear H8.
          eapply Forall_concat, Forall_forall; intros ? Hinblks.
          eapply Forall3_ignore12, Forall_forall in H2 as ((?&?)&?&Hin2&Hin3&(?&?&?)&?&?&?); eauto.
          repeat inv_bind.

          assert (forall x, InMembers x (map (fun '(x, y, _) => (x, y)) (x10 ++ x12)) ->
                       InMembers x (filter (fun '(_, (_, ck')) => ck' ==b ck) l0 ++ l)) as Hinminv.
          { intros ? Hinm. rewrite fst_InMembers in Hinm. rewrite fst_InMembers.
            erewrite map_app, <-2 new_idents_old, <-map_app; eauto.
            erewrite map_map, map_ext in Hinm; eauto. intros ((?&?)&(?&?)); auto.
          }

          apply Forall_app; split.
          *{ repeat (take (Forall _ branches) and eapply Forall_forall in it; eauto).
             eapply switch_blocks_wc' in H2; eauto.
             - erewrite map_filter_nil; eauto.
               simpl_Forall. apply in_app_iff in H as [|]; simpl_In; auto.
             - intros ? Hin. erewrite Env.In_from_list in Hin.
               erewrite Permutation_app_comm, fst_InMembers, map_map, map_ext, <-fst_InMembers; auto.
               intros (?&?&?); auto.
             - intros ??? Hfind Hin. simpl_In.
               eapply new_idents_In with (ids1:=filter _ _) in H9; eauto.
               2:{ eapply Env.find_In, Env.In_from_list in Hfind; eauto. }
               unfold rename_var in H9; eauto. rewrite Hfind in H9. simpl_In.
               repeat rewrite in_app_iff. do 2 right. solve_In; auto.
             - intros ?? Hfind Hin. exfalso.
               assert (Hnin:=Hfind). rewrite <-Env.Props.P.F.not_find_in_iff, Env.In_from_list in Hnin.
               eapply Hnin. simpl_In.
               erewrite fst_InMembers, map_map, map_ext, map_app, 2 new_idents_old; eauto.
               2:intros ((?&?)&(?&?)); auto.
               rewrite Permutation_app_comm, <-map_app. solve_In.
             - erewrite fst_NoDupMembers, map_map, <-map_ext, <-fst_NoDupMembers; eauto. 2:intros (?&?&?); auto.
               now rewrite Permutation_app_comm.
             - apply Forall_map, Forall_map, Forall_forall; intros (?&?&?) ?; simpl; auto with clocks.
             - constructor.
               + eapply wc_clock_incl; eauto. solve_incl_app.
               + rewrite app_assoc. apply in_or_app; auto.
             - eapply Forall_impl; [|eapply it1]. intros ? Hnd.
               eapply NoDupLocals_incl; eauto.
               apply Partition_Permutation in Hpart. rewrite Hpart.
               rewrite map_map, 2 map_app.
               apply incl_app; [apply incl_appl|apply incl_appr].
               + erewrite map_ext; try reflexivity. intros (?&?&?); auto.
               + erewrite map_ext; try eapply incl_map, incl_filter', incl_refl.
                 intros (?&?&?); auto.
             - eapply Forall_impl; [|eapply it0]; intros.
               eapply wc_block_incl; eauto. intros (?&?) Hin.
               + eapply H7 in Hin as (Hin&?); subst. simpl_In.
                 apply Partition_Permutation in Hpart. rewrite Hpart in Hin0.
                 solve_In.
                 2:apply in_app_iff in Hin0 as [Hin|Hin]; eauto with datatypes.
                 simpl; auto.
                 apply in_or_app, or_intror, filter_In. split; auto.
                 apply equiv_decb_refl.
               + destruct Γl' as [|(?&?)]; try reflexivity.
                 exfalso. eapply H10; eauto with datatypes.
           }
          *{ rewrite Forall_map. apply Forall_forall; intros ((?&?)&?&?) Hin.
             rewrite map_filter_nil.
             2:{ simpl_Forall. apply in_app_iff in H12 as [|]; simpl_In; auto. }
             eapply when_free_wc.
             - eapply in_or_app, or_introl, rename_var_wc; eauto.
               eapply new_idents_In_inv in Hin as (?&Hin); eauto.
               eapply filter_In in Hin as (Hin&Hfilter).
               rewrite equiv_decb_equiv in Hfilter. inv Hfilter.
               apply Partition_Permutation in Hpart. rewrite Hpart, idck_app.
               apply in_or_app, or_intror. solve_In.
             - rewrite 2 in_app_iff. do 2 right. solve_In; eauto with datatypes.
               eapply new_idents_In_inv_ck in H8; eauto. subst; reflexivity.
             - rewrite app_assoc. apply in_or_app; auto.
           }
        + rewrite Forall_map.
          eapply cond_eq_wc in H0; eauto using subclock_exp_wc.
          2:repeat rewrite subclock_exp_clockof, H5; simpl; auto.
          eapply Forall_impl; [|eauto]; intros ? Hwc.
          constructor. eapply wc_equation_incl; eauto.
          * apply incl_app; [solve_incl_app|]. apply incl_appr, incl_appl.
            unfold idck, idty. erewrite map_map, map_ext; eauto. reflexivity.
            intros (?&?&?); auto.
          * rewrite map_filter_nil. reflexivity.
            simpl_Forall. apply in_app_iff in H9 as [|]; simpl_In; auto.
        + eapply cond_eq_wc_clock in H0; eauto.
          unfold idty, idck. simpl_Forall.
          eapply Forall_forall in H0; [|solve_In].
          eapply wc_clock_incl; eauto. solve_incl_app.
        + eapply cond_eq_In in H0; eauto using subclock_exp_wc.
          2:{ rewrite subclock_exp_clockof, H5; simpl; auto. }
          clear - H0 H2 H5 Hck'.
          eapply Forall_impl. intros ??.
          1:{ eapply wc_clock_incl with (vars:=vars'++idck l1); eauto.
              apply incl_app; [solve_incl_app|].
              apply incl_appr, incl_appl.
              unfold idck, idty. repeat rewrite map_map. erewrite map_ext. reflexivity.
              intros (?&?&?); eauto. }
          eapply mmap_values in H2.
          induction H2 as [|(?&?) (((?&?)&?)&?)]; simpl; auto.
          rewrite 2 idty_app, idck_app, map_app. apply Forall_app; split; auto.
          clear - H0 H H5 Hck'. destruct H as (?&?&?); repeat inv_bind.
          rewrite map_app, 2 idty_app, idck_app, map_app.
          apply Forall_app; split.
          1,2:eapply new_idents_wc; [| |eauto]; eauto.
          1,2:eapply wc_clock_incl; eauto; solve_incl_app.
        + simpl_Forall; auto.
        + simpl_Forall; simpl_In; auto.
      - (* local *)
        econstructor; eauto.
        + rewrite map_filter_nil.
          2:{ simpl_Forall; subst; auto. }
          eapply switch_blocks_wc' in H0; eauto.
          * intros ? Hin. apply InMembers_app; auto.
          * intros ??? Hfind Hin. rewrite idck_app in Hin.
            repeat rewrite in_app_iff in *. destruct Hin as [Hin|Hin]; eauto.
            exfalso. eapply Env.find_In, Hsubin, fst_InMembers, H7 in Hfind; eauto.
            eapply In_InMembers in Hin. now rewrite InMembers_idck, 2 InMembers_idty in Hin.
          * intros ?? Hfind Hin. rewrite idck_app in Hin.
            repeat rewrite in_app_iff in *. destruct Hin as [Hin|Hin]; eauto.
            right. clear - Hin. unfold idck, idty in *. repeat rewrite map_map in *.
            solve_In.
          * apply NoDupMembers_app; auto. now rewrite 2 NoDupMembers_idty.
            intros ? Hinm1. rewrite 2 InMembers_idty in Hinm1. rewrite fst_InMembers. auto.
          * rewrite idck_app.
            apply Forall_app; split; auto.
            -- simpl_Forall.
               rewrite Permutation_app_comm. simpl_app.
               erewrite 2 map_map, map_ext with (l:=locs); eauto. intros; destruct_conjs; auto.
            -- simpl_Forall. simpl_In. eapply Forall_forall in Hwenv; [|solve_In].
               eapply wc_clock_incl; eauto. solve_incl_app.
          * eapply wc_clock_incl; eauto; solve_incl_app.
          * rewrite map_app, 2 map_fst_idty.
            simpl_Forall. now rewrite Permutation_app_comm.
          * simpl_Forall.
            take (wc_block _ _ _ _) and rewrite map_filter_nil in it.
            2:{ simpl_Forall; subst; auto. }
            rewrite idck_app, Permutation_app_comm.
            simpl_app. erewrite 2 map_map, map_ext with (l:=locs); eauto. intros; destruct_conjs; auto.
        + unfold idck, idty in *. simpl_Forall; subst.
          eapply subclock_clock_wc; eauto.
          * intros ??? Hfind Hin. rewrite in_app_iff in *. repeat rewrite map_map in *; simpl in *.
            destruct Hin as [Hin|Hin]; eauto.
            exfalso. simpl_In.
            eapply Env.find_In, Hsubin, fst_InMembers, H7 in Hfind; eauto.
            eapply In_InMembers; eauto.
          * intros ?? Hfind Hin. rewrite in_app_iff in *. repeat rewrite map_map in *; simpl in *.
            destruct Hin as [Hin|Hin]; eauto.
            right. clear - Hin. solve_In.
          * eapply wc_clock_incl; eauto; repeat solve_incl_app.
        + simpl_Forall; subst; auto.
    Qed.

  End switch_block.

  Fact subclock_clock_idem : forall ck,
    subclock_clock Cbase (Env.empty ident) ck = ck.
  Proof.
    induction ck; simpl; auto.
    unfold rename_var. rewrite Env.gempty; simpl.
    f_equal; auto.
  Qed.

  Lemma switch_node_wc G1 G2 : forall n,
      wc_global G1 ->
      global_iface_eq G1 G2 ->
      wc_node G1 n ->
      wc_node G2 (switch_node n).
  Proof.
    intros * HwG Heq (Hwc1&Hwc2&Hwc3).
    repeat split; simpl; auto.
    eapply iface_eq_wc_block; eauto.
    eapply switch_block_wc in Hwc3; eauto with clocks. 7:eapply surjective_pairing.
    - intros ? Hin. apply Env.Props.P.F.empty_in_iff in Hin. inv Hin.
    - intros ??? Hfind. rewrite Env.gempty in Hfind. congruence.
    - intros ?? _ Hin. rewrite subclock_clock_idem; auto.
    - rewrite NoDupMembers_idty. apply n_nodup.
    - apply n_syn.
    - rewrite map_fst_idty. apply n_nodup.
  Qed.

  Lemma switch_global_wc : forall G,
      wc_global G ->
      wc_global (switch_global G).
  Proof.
    intros (enums&nds). unfold wc_global, CommonTyping.wt_program; simpl.
    induction nds; intros * Hwc; simpl; inv Hwc; auto with datatypes.
    destruct H1.
    constructor; [constructor|].
    - eapply switch_node_wc; eauto.
      2:eapply switch_global_iface_eq.
      eapply H2; eauto.
    - rewrite Forall_map. eapply Forall_impl; [|eapply H0]; intros.
      simpl; eauto.
    - eapply IHnds; eauto.
  Qed.

End CSCLOCKING.

Module CSClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (CS  : CLOCKSWITCH Ids Op OpAux Cks Syn)
       <: CSCLOCKING Ids Op OpAux Cks Syn Clo CS.
  Include CSCLOCKING Ids Op OpAux Cks Syn Clo CS.
End CSClockingFun.
