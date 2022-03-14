From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Lustre.ClockSwitch.ClockSwitch.
From Velus Require Import Lustre.SubClock.SCClocking.

Module Type CSCLOCKING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import CS : CLOCKSWITCH Ids Op OpAux Cks Senv Syn).

  Module Import SCC := SCClockingFun Ids Op OpAux Cks Senv Syn Clo SC. Import SC.

  Import Fresh Facts Tactics.

  Section switch_block.

    Context {PSyn : block -> Prop} {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Hypothesis HwG : wc_global G.

    Import Permutation.

    Lemma cond_eq_wc Γ : forall e ty ck x xcs eqs' st st',
        wc_exp G Γ e ->
        clockof e = [ck] ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        Forall (wc_equation G (Γ++senv_of_tyck xcs)) eqs'.
    Proof.
      intros * Hwc Hck Hcond; destruct e; repeat inv_bind.
      3:destruct a; repeat inv_bind; auto.
      1-11:constructor; auto; rewrite Permutation_app_comm; simpl.
      1-11:(constructor; [constructor; auto; eapply wc_exp_incl in Hwc; eauto;
                          intros * Hl; inv Hl; econstructor; eauto with datatypes|]).
      1-11:simpl; try take (_ = [_]) and rewrite it; try rewrite app_nil_r; eauto.
      1-11:constructor; eauto with senv datatypes.
    Qed.

    Lemma cond_eq_wc_clock Γ : forall e ty ck x xcs eqs' st st',
        wc_clock Γ ck ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        Forall (wc_clock Γ) (map snd (Common.idck xcs)).
    Proof.
      intros * Hck Hcond; destruct e; repeat inv_bind; simpl; auto.
      destruct a; repeat inv_bind; simpl; auto.
    Qed.

    Lemma cond_eq_In Γ : forall e ty ck x xcs eqs' st st',
        wc_exp G Γ e ->
        clockof e = [ck] ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        HasClock (Γ ++ senv_of_tyck xcs) x ck.
    Proof.
      intros * Hwc Hck Hcond; destruct e; repeat inv_bind; simpl in *; eauto with senv datatypes.
      inv Hwc. repeat inv_bind.
      inv Hck; eauto with senv datatypes.
    Qed.

    Lemma new_idents_wc Γ' : forall ck x ty k ids ids' st st',
        wc_clock Γ' ck ->
        In (x, ck) Γ' ->
        new_idents ck x ty k ids st = (ids', st') ->
        Forall (fun '(_, _, (_, ck)) => wc_clock Γ' ck) ids'.
    Proof.
      intros * Hck Hin Hni.
      unfold new_idents in *. eapply mmap_values, Forall2_ignore1 in Hni.
      simpl_Forall. simpl_In. simpl_Forall. repeat inv_bind.
      econstructor; eauto.
    Qed.

    Lemma when_free_wc Γ : forall x y ty ck cx tx k,
        HasClock Γ x ck ->
        HasClock Γ y (Con ck cx (tx, k)) ->
        HasClock Γ cx ck ->
        wc_block G Γ (when_free x y ty ck cx tx k).
    Proof.
      intros.
      repeat constructor; simpl; auto.
    Qed.

    Lemma merge_defs_wc Γ : forall sub y ty ck x tx xcs,
        HasClock Γ x ck ->
        HasClock Γ (rename_var sub y) ck ->
        xcs <> [] ->
        Forall (fun '(k, sub) => HasClock Γ (rename_var sub y) (Con ck x (tx, k))) xcs ->
        wc_block G Γ (merge_defs sub y ty ck x tx xcs).
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
      apply InMembers_In in Hinm as (?&Hin).
      apply in_app_iff in Hin as [Hin|Hin]; eapply Forall_forall in Hin; eauto; simpl in *.
      1,2:destruct Hin as (((?&?)&?&?)&Hin&?&?&?); repeat inv_bind.
      - eapply in_map_iff. do 2 esplit; eauto with datatypes; simpl.
        f_equal; auto.
        unfold rename_var. erewrite Env.find_In_from_list; eauto.
        2:solve_In; eauto with datatypes; auto. auto.
      - eapply in_map_iff. do 2 esplit; eauto with datatypes; simpl.
        f_equal; auto.
        unfold rename_var. erewrite Env.find_In_from_list; eauto.
        2:eapply in_map_iff; do 2 esplit; eauto with datatypes; auto. auto.
    Qed.

    Lemma new_idents_In_inv_ck : forall ck cx tx k ids nids st st' x y ck1 ty,
        new_idents ck cx tx k ids st = (nids, st') ->
        In (x, y, (ty, ck1)) nids ->
        ck1 = Con ck cx (tx, k).
    Proof.
      intros * Hni Hin.
      eapply mmap_values, Forall2_ignore1, Forall_forall in Hni; eauto.
      destruct Hni as ((?&?)&?&?&?&?); repeat inv_bind; eauto.
    Qed.

    Lemma switch_block_wc : forall blk bck sub Γ Γ' blk' st st',
        (forall x, ~IsLast Γ x) ->
        (forall x, Env.In x sub -> InMembers x Γ) ->
        (forall x y ck, Env.find x sub = Some y -> HasClock Γ x ck -> HasClock Γ' y (subclock_clock bck sub ck)) ->
        (forall x ck, Env.find x sub = None -> HasClock Γ x ck -> HasClock Γ' x (subclock_clock bck sub ck)) ->
        NoDupMembers Γ ->
        wc_env (idck Γ) ->
        wc_clock (idck Γ') bck ->
        noauto_block blk ->
        NoDupLocals (map fst Γ) blk ->
        wc_block G Γ blk ->
        switch_block Γ bck sub blk st = (blk', st') ->
        wc_block G Γ' blk'.
    Proof.
      induction blk using block_ind2; intros * Hnl1 Hsubin Hsub Hnsub Hnd1 Hwenv Hbck Hnl2 Hnd2 Hwc Hsw;
        inv Hnl2; inv Hnd2; inv Hwc; repeat inv_bind; simpl in *.
      - (* equation *)
        constructor. eapply subclock_equation_wc; eauto.

      - (* reset *)
        econstructor; eauto using subclock_exp_wc.
        2:rewrite subclock_exp_clockof, H7; simpl; eauto.
        apply mmap_values, Forall2_ignore1 in H0.
        simpl_Forall. eapply H; eauto.

      - (* switch *)
        destruct (partition _ _) eqn:Hpart; repeat inv_bind.
        apply partition_Partition in Hpart.
        destruct x; repeat inv_bind.
        assert (wc_clock (idck Γ') (subclock_clock bck sub ck)) as Hck'.
        { eapply subclock_clock_wc; eauto.
          eapply wc_exp_clockof in H4; eauto.
          rewrite H5 in H4. apply Forall_singl in H4; auto. }
        rewrite subclock_exp_clockof, H5 in *; simpl in *.

        assert (HasClock (Γ' ++ senv_of_tyck l1) i (subclock_clock bck sub ck)) as Hini.
        { eapply cond_eq_In in H0; eauto using subclock_exp_wc.
          rewrite subclock_exp_clockof, H5; simpl; auto. }

        assert (NoDupMembers (filter (fun '(_, ann) => ann.(clo) ==b ck) l0 ++ l)) as Hnd'.
        { rewrite Permutation_app_comm.
          eapply switch_block_NoDupMembers_env; eauto. }

        econstructor; eauto; repeat rewrite idty_app; repeat rewrite idck_app; repeat rewrite map_app; repeat rewrite Forall_app; repeat split.
        + rewrite Forall_map. apply Forall_forall; intros (?&?) Hin.
          eapply merge_defs_wc; eauto.
          * simpl_app. repeat rewrite HasClock_app in *. destruct Hini as [Hini|Hini]; eauto.
            right; left; inv Hini; simpl_In. econstructor; solve_In; auto.
          * rewrite HasClock_app; left.
            eapply rename_var_wc; eauto.
            assert (Is_defined_in i0 (Bswitch ec branches)) as Hdef.
            { eapply vars_defined_Is_defined_in.
              eapply Partition_Forall1, Forall_forall in Hpart; eauto; simpl in *.
              apply PSF.mem_2; auto. }
            inv Hdef. simpl_Exists.
            eapply Is_defined_in_wx_In in H12; [|eapply wc_block_wx_block; simpl_Forall; eauto].
            apply fst_InMembers in H12; simpl_In.
            eapply H7; eauto with senv.
          * apply mmap_length in H2. destruct x, branches; simpl in *; try congruence.
          * eapply mmap_values, Forall2_ignore1 in H2. simpl_Forall.
            simpl_app. rewrite 2 HasClock_app. do 2 right. repeat inv_bind.
            eapply new_idents_In with (ids1:=filter _ _) in H13; eauto.
            2:eapply InMembers_app, or_intror, In_InMembers; eauto.
            simpl_In. econstructor; solve_In; eauto.
        + eapply CS.mmap2_values in H8. eapply mmap_values, Forall3_ignore3' with (zs:=x3) in H2.
          2:{ eapply Forall3_length in H8 as (?&?); congruence. }
          2:{ eapply mmap_length in H2; eauto. }
          eapply Forall3_Forall3 in H2; eauto. clear H8.
          eapply Forall_concat, Forall_forall; intros ? Hinblks.
          eapply Forall3_ignore12, Forall_forall in H2 as ((?&?)&?&Hin2&Hin3&(?&?&?)&?&?&?); eauto.
          repeat inv_bind.

          assert (forall x, InMembers x (map (fun '(x, y, _) => (x, y)) (x10 ++ x12)) ->
                       InMembers x (filter (fun '(_, ann) => ann.(clo) ==b ck) l0 ++ l)) as Hinminv.
          { intros ? Hinm. rewrite fst_InMembers in Hinm. rewrite fst_InMembers.
            erewrite map_app, <-2 new_idents_old, <-map_app; eauto.
            erewrite map_map, map_ext in Hinm; eauto. intros ((?&?)&(?&?)); auto.
          }

          apply Forall_app; split.
          *{ apply mmap_values, Forall2_ignore1 in H2. simpl_Forall.
             eapply H in H13; eauto.
             - intros * Hnl. eapply Hnl1. inv Hnl; simpl_In.
               econstructor.
               apply Partition_Permutation in Hpart. rewrite Hpart.
               rewrite in_app_iff in *. destruct Hin; simpl_In; eauto. auto.
             - intros ? Hin. erewrite Env.In_from_list in Hin.
               erewrite Permutation_app_comm, fst_InMembers, map_map, map_ext, <-fst_InMembers; auto.
               intros (?&?); auto.
             - intros * Hfind Hin. inv Hin. simpl_In.
               eapply new_idents_In with (ids1:=filter _ _) in H11; eauto.
               2:{ eapply Env.find_In, Env.In_from_list in Hfind; eauto. }
               unfold rename_var in H11. rewrite Hfind in H11. simpl_In.
               simpl_app. rewrite 2 HasClock_app. do 2 right. econstructor; solve_In; eauto; simpl.
             - intros ?? Hfind Hin. exfalso.
               assert (Hnin:=Hfind). rewrite <-Env.Props.P.F.not_find_in_iff, Env.In_from_list in Hnin.
               eapply Hnin. inv Hin. simpl_In.
               erewrite fst_InMembers, map_map, map_ext, map_app, 2 new_idents_old; eauto.
               2:intros ((?&?)&(?&?)); auto.
               rewrite Permutation_app_comm, <-map_app. solve_In.
             - erewrite fst_NoDupMembers, map_map, <-map_ext, <-fst_NoDupMembers; eauto. 2:intros (?&?); auto.
               now rewrite Permutation_app_comm.
             - apply Forall_map, Forall_map, Forall_forall; intros (?&?) ?; simpl; auto with clocks.
             - constructor.
               + eapply wc_clock_incl; eauto. solve_incl_app.
               + simpl_app. repeat rewrite in_app_iff; auto.
                 apply HasClock_app in Hini as [Hini|Hini]; inv Hini; [left|right;left]; solve_In.
                 congruence.
             - eapply NoDupLocals_incl; eauto.
               apply Partition_Permutation in Hpart. rewrite Hpart.
               rewrite map_map, 2 map_app.
               apply incl_app; [apply incl_appl|apply incl_appr].
               + erewrite map_ext; try reflexivity. intros (?&?); auto.
               + erewrite map_ext; try eapply incl_map, incl_filter', incl_refl.
                 intros (?&?); auto.
             - eapply wc_block_incl; [| |eauto]; intros * Hin.
               + eapply H7 in Hin as (Hin&?); subst.
                 apply Partition_Permutation in Hpart. rewrite Hpart, HasClock_app in Hin.
                 rewrite map_app, HasClock_app.
                 destruct Hin as [Hin|Hin]; inv Hin; [left|right]; econstructor; solve_In.
                 1,3:reflexivity. apply equiv_decb_refl.
               + exfalso. eapply Hnl1; eauto.
           }
          *{ rewrite Forall_map. apply Forall_forall; intros ((?&?)&?&?) Hin.
             eapply when_free_wc.
             - eapply HasClock_app, or_introl, rename_var_wc; eauto.
               eapply new_idents_In_inv in Hin as (?&Hin&?); eauto; subst.
               simpl_In. rewrite equiv_decb_equiv in Hf. inv Hf.
               apply Partition_Permutation in Hpart. rewrite Hpart.
               apply HasClock_app; eauto with senv.
             - simpl_app. rewrite 2 HasClock_app. do 2 right.
               eapply new_idents_In_inv_ck in H8; eauto. rewrite <-H8; clear H8.
               econstructor; solve_In; eauto with datatypes. simpl; auto. auto.
             - simpl_app. repeat rewrite HasClock_app in *. destruct Hini as [Hini|Hini]; eauto.
               right; left; inv Hini; simpl_In. econstructor; solve_In; auto.
           }
        + rewrite Forall_map.
          eapply cond_eq_wc in H0; eauto using subclock_exp_wc.
          2:repeat rewrite subclock_exp_clockof, H5; simpl; auto.
          eapply Forall_impl; [|eauto]; intros ? Hwc.
          constructor. eapply wc_equation_incl; [| |eauto]; intros * Hin.
          * simpl_app. repeat rewrite HasClock_app in *. destruct Hin as [|Hin]; [|right;left]; auto.
            inv Hin; simpl_In; econstructor; solve_In. auto.
          * rewrite IsLast_app in *. destruct Hin as [|Hin]; auto.
            exfalso. inv Hin. simpl_In. congruence.
        + eapply cond_eq_wc_clock in H0; eauto.
          unfold idty, idck. simpl_Forall.
          eapply Forall_forall in H0; [|solve_In].
          eapply wc_clock_incl; eauto. solve_incl_app.
        + eapply cond_eq_In in H0; eauto using subclock_exp_wc.
          2:{ rewrite subclock_exp_clockof, H5; simpl; auto. }
          clear - H0 H2 H5 Hck'.
          eapply Forall_impl. intros ??.
          1:{ eapply wc_clock_incl with (vars:=idck (Γ'++senv_of_tyck l1)); eauto.
              simpl_app. apply incl_appr', incl_appl.
              intros ? Hin; solve_In. }
          eapply mmap_values, Forall2_ignore1 in H2. inv H0.
          simpl_Forall. simpl_In. simpl_Forall. repeat inv_bind.
          apply in_app_iff in Hin0 as [Hin0|Hin0].
          * eapply new_idents_wc in H2. simpl_Forall; eauto.
            2:solve_In; eauto; congruence.
            eapply wc_clock_incl; eauto. solve_incl_app.
          * eapply new_idents_wc in H3. simpl_Forall; eauto.
            2:solve_In; eauto; congruence.
            eapply wc_clock_incl; eauto. solve_incl_app.
        + simpl_Forall; auto.
        + simpl_Forall; simpl_In; auto.

      - (* local *)
        econstructor; eauto.
        + apply mmap_values, Forall2_ignore1 in H0. simpl_Forall.
          eapply H in H5; eauto.
          * apply NoLast_app. split; auto.
            intros * Hnl. inv Hnl. simpl_In; simpl_Forall; subst; simpl in *. congruence.
          * intros ? Hin. apply InMembers_app; auto.
          * intros * Hfind Hin.
            repeat rewrite HasClock_app in *. destruct Hin as [Hin|Hin]; eauto.
            exfalso. eapply Env.find_In, Hsubin, fst_InMembers, H7 in Hfind; eauto.
            inv Hin; simpl_In. eauto using In_InMembers.
          * intros * Hfind Hin.
            repeat rewrite HasClock_app in *. destruct Hin as [Hin|Hin]; eauto.
            right. inv Hin; simpl_In. econstructor; solve_In. auto.
          * apply NoDupMembers_app; auto. apply NoDupMembers_senv_of_locs; auto.
            intros ? Hinm1. rewrite InMembers_senv_of_locs in Hinm1. rewrite fst_InMembers. auto.
          * simpl_app.
            apply Forall_app; split; auto.
            -- simpl_Forall.
               rewrite Permutation_app_comm. simpl_app.
               erewrite map_map in *. erewrite map_ext with (l:=locs); eauto.
            -- simpl_Forall. simpl_In. eapply Forall_forall in Hwenv; [|solve_In].
               eapply wc_clock_incl; eauto. solve_incl_app.
          * eapply wc_clock_incl; eauto; solve_incl_app.
          * now rewrite map_app, map_fst_senv_of_locs, Permutation_app_comm.
          * now rewrite Permutation_app_comm.
        + simpl_Forall; subst.
          eapply subclock_clock_wc; eauto.
          * intros * Hfind Hin. rewrite HasClock_app in *. destruct Hin as [Hin|Hin]; eauto.
            exfalso. simpl_In.
            eapply Env.find_In, Hsubin, fst_InMembers, H7 in Hfind; eauto.
            inv Hin; simpl_In; eauto using In_InMembers.
          * intros * Hfind Hin. rewrite HasClock_app in *. destruct Hin as [Hin|Hin]; eauto.
            right. inv Hin; simpl_In; econstructor. solve_In. auto.
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
      global_iface_incl G1 G2 ->
      wc_node G1 n ->
      wc_node G2 (switch_node n).
  Proof.
    intros * HwG Heq (Hwc1&Hwc2&Hwc3).
    repeat split; simpl; auto.
    eapply iface_incl_wc_block; eauto.
    eapply switch_block_wc in Hwc3; eauto with clocks. 9:eapply surjective_pairing.
    - apply senv_of_inout_NoLast.
    - intros ? Hin. apply Env.Props.P.F.empty_in_iff in Hin. inv Hin.
    - intros ??? Hfind. rewrite Env.gempty in Hfind. congruence.
    - intros ?? _ Hin. rewrite subclock_clock_idem; auto.
    - apply nodupmembers_map, n_nodup. intros; destruct_conjs; auto.
    - unfold idck, senv_of_inout. erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
    - apply n_syn.
    - rewrite map_fst_senv_of_inout. apply n_nodup.
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
      2:eapply iface_eq_iface_incl, switch_global_iface_eq.
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
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (CS  : CLOCKSWITCH Ids Op OpAux Cks Senv Syn)
       <: CSCLOCKING Ids Op OpAux Cks Senv Syn Clo CS.
  Include CSCLOCKING Ids Op OpAux Cks Senv Syn Clo CS.
End CSClockingFun.
