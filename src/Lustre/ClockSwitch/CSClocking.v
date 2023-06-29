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

    Context {PSyn : list decl -> block -> Prop} {prefs : PS.t}.
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
      all:constructor; auto; rewrite Permutation_app_comm; simpl.
      all:(constructor; [constructor; auto; eapply wc_exp_incl in Hwc; eauto;
                         intros * Hl; inv Hl; econstructor; eauto with datatypes|]).
      all:simpl; try take (_ = [_]) and rewrite it; try rewrite app_nil_r; eauto.
      all:constructor; eauto with senv datatypes.
    Qed.

    Lemma cond_eq_wc_clock Γ : forall e ty ck x xcs eqs' st st',
        wc_clock Γ ck ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        Forall (wc_clock Γ) (map snd (idsnd xcs)).
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

    Lemma when_freel_wc Γ subl : forall x y ty ck cx tx k,
        (Env.find x subl = None -> HasClock Γ x ck /\ IsLast Γ x) ->
        HasClock Γ cx ck ->
        HasClock Γ y (Con ck cx (tx, k)) ->
        (forall y, Env.find x subl = Some y -> HasClock Γ y ck) ->
        wc_block G Γ (when_freel subl x y ty ck cx tx k).
    Proof.
      intros.
      repeat (constructor; eauto); simpl.
      - unfold rename_last. cases_eqn Eq.
        + econstructor; eauto.
        + edestruct H; eauto with lclocking.
      - unfold rename_last; cases; simpl; auto.
      - unfold rename_last; cases; simpl; auto.
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

    Lemma new_idents_Inl : forall x ty ck cx k ids1 nids1 st1 st2,
        NoDupMembers ids1 ->
        InMembers x ids1 ->
        new_idents ck cx ty k ids1 st1 = (nids1, st2) ->
        In (rename_var (Env.from_list (map (fun '(x, y, _) => (x, y)) nids1)) x, Con ck cx (ty, k))
           (map (fun '(_, x, (_, ck)) => (x, ck)) nids1).
    Proof.
      intros * Hnd Hinm Hni1.
      assert (NoDupMembers (map (fun '(x, y, _) => (x, y)) nids1)) as Hnd'.
      { erewrite fst_NoDupMembers, map_map, map_ext, new_idents_old; eauto.
        rewrite <-fst_NoDupMembers; auto.
        intros ((?&?)&?&?); auto. }
      eapply mmap_values, Forall2_ignore2 in Hni1.
      simpl_In. simpl_Forall; repeat inv_bind.
      - solve_In.
        f_equal; auto.
        unfold rename_var. erewrite Env.find_In_from_list; eauto.
        2:solve_In. auto.
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

    Lemma switch_scope_wc {A} P_na P_ld P_nd P_wc f_switch :
      forall locs (blk: A) bck sub subl ls Γck Γck' s' st st',
        (forall x, Env.In x sub \/ Env.In x subl -> InMembers x Γck) ->
        (forall x, Env.In x subl -> ~In x ls) ->
        (forall x ck, Env.find x sub = None -> HasClock Γck x ck -> HasClock Γck' x (subclock_clock bck sub ck)) ->
        (forall x ck, Env.find x subl = None -> HasClock Γck x ck -> IsLast Γck x -> HasClock Γck' x (subclock_clock bck sub ck) /\ IsLast Γck' x) ->
        (forall x y ck, Env.find x sub = Some y -> HasClock Γck x ck -> HasClock Γck' y (subclock_clock bck sub ck)) ->
        (forall x y ck, Env.find x subl = Some y -> HasClock Γck x ck -> HasClock Γck' y (subclock_clock bck sub ck)) ->
        NoDupMembers Γck ->
        wc_env (idck Γck) ->
        wc_clock (idck Γck') bck ->
        noauto_scope P_na (Scope locs blk) ->
        LastsDefinedScope P_ld (Scope locs blk) ls ->
        NoDupScope P_nd (map fst Γck) (Scope locs blk) ->
        wc_scope P_wc G Γck (Scope locs blk) ->
        switch_scope f_switch Γck bck sub (Scope locs blk) st = (s', st') ->
        (forall ls Γck Γck' blk' st st',
            (forall x, Env.In x sub \/ Env.In x subl -> InMembers x Γck) ->
            (forall x, Env.In x subl -> ~In x ls) ->
            (forall x ck, Env.find x sub = None -> HasClock Γck x ck -> HasClock Γck' x (subclock_clock bck sub ck)) ->
            (forall x ck, Env.find x subl = None -> HasClock Γck x ck -> IsLast Γck x -> HasClock Γck' x (subclock_clock bck sub ck) /\ IsLast Γck' x) ->
            (forall x y ck, Env.find x sub = Some y -> HasClock Γck x ck -> HasClock Γck' y (subclock_clock bck sub ck)) ->
            (forall x y ck, Env.find x subl = Some y -> HasClock Γck x ck -> HasClock Γck' y (subclock_clock bck sub ck)) ->
            NoDupMembers Γck ->
            wc_env (idck Γck) ->
            wc_clock (idck Γck') bck ->
            P_na blk ->
            P_ld blk ls ->
            P_nd (map fst Γck) blk ->
            P_wc Γck blk ->
            f_switch Γck blk st = (blk', st') ->
            P_wc Γck' blk') ->
        wc_scope P_wc G Γck' s'.
    Proof.
      intros * Hsubin Hsublin Hck Hl Hsub Hsubl Hnd1 Hwenv Hbck LD Hnl2 Hnd3 Hwt Hswitch Hind;
        inv Hnl2; inv Hnd3; inv Hwt; inv LD; subst Γ'; repeat inv_bind; simpl in *.
      take (forall x, InMembers x locs -> ~_) and rename it into Hdisj.
      econstructor; eauto.
      - simpl_Forall; subst.
        eapply subclock_clock_wc; eauto.
        * intros * ? Hin. rewrite HasClock_app in *. destruct Hin as [Hin|Hin]; eauto.
          right. inv Hin; simpl_In; econstructor. solve_In. auto.
        * intros * Hfind Hin. rewrite HasClock_app in *. destruct Hin as [Hin|Hin]; eauto.
          exfalso. simpl_In.
          eapply Env.find_In, or_introl, Hsubin, fst_InMembers, Hdisj in Hfind; eauto.
          inv Hin; solve_In.
        * eapply wc_clock_incl; eauto; repeat solve_incl_app.
      - eapply Hind with (ls:=ls++lasts_of_decls locs) (Γck:=Γck++senv_of_decls _); eauto.
        + intros ? Hin. apply InMembers_app; auto.
        + intros * In1 In2. apply in_app_iff in In2 as [In2|In2].
          * eapply Hsublin; eauto.
          * eapply or_intror, Hsubin in In1.
            unfold lasts_of_decls in *.
            eapply Hdisj, fst_InMembers; eauto. solve_In.
        + intros ?? Hfind Hin.
          repeat rewrite HasClock_app in *. destruct Hin as [Hin|Hin]; eauto.
          right. inv Hin. simpl_In. econstructor; solve_In; auto.
        + intros * Find Ck L. rewrite HasClock_app, IsLast_app.
          apply HasClock_IsLast_app in Ck as [(?&?)|(Ck'&L')]; eauto using NoDupScope_NoDupMembers.
          * edestruct Hl; eauto.
          * inv Ck'. inv L'. simpl_In.
            eapply NoDupMembers_det in Hin0; eauto. inv Hin0.
            split; right; simpl_In; econstructor; solve_In; simpl; auto.
        + intros ??? Hfind Hin.
          repeat rewrite HasClock_app in *. destruct Hin as [Hin|Hin]; eauto.
          exfalso. eapply Env.find_In, or_introl, Hsubin, fst_InMembers in Hfind; eauto.
          inv Hin. simpl_In.
          assert (HasClock Γck x0 a.(clo)) as Hty by eauto with senv. inv Hty.
          eapply Hdisj; eauto using In_InMembers. solve_In.
        + intros ??? Hfind Hin.
          repeat rewrite HasClock_app in *. destruct Hin as [Hin|Hin]; eauto.
          exfalso. eapply Env.find_In, or_intror, Hsubin, fst_InMembers in Hfind; eauto.
          inv Hin. simpl_In.
          assert (HasClock Γck x0 a.(clo)) as Hty by eauto with senv. inv Hty.
          eapply Hdisj; eauto using In_InMembers. solve_In.
        + apply NoDupMembers_app; auto. rewrite NoDupMembers_senv_of_decls; auto.
          intros ? Hinm1 Hinm2. simpl_In.
          eapply Hdisj; solve_In.
        + simpl_app. apply wc_env_app; auto.
          simpl_Forall; auto.
        + eapply wc_clock_incl; [|eauto]. solve_incl_app.
        + rewrite map_app, map_fst_senv_of_decls. auto.
    Qed.

    Lemma switch_block_wc : forall blk bck sub subl ls Γ Γ' blk' st st',
        (forall x, Env.In x sub \/ Env.In x subl -> InMembers x Γ) ->
        (forall x, Env.In x subl -> ~In x ls) ->
        (forall x ck, Env.find x sub = None -> HasClock Γ x ck -> HasClock Γ' x (subclock_clock bck sub ck)) ->
        (forall x ck, Env.find x subl = None -> HasClock Γ x ck -> IsLast Γ x -> HasClock Γ' x (subclock_clock bck sub ck) /\ IsLast Γ' x) ->
        (forall x y ck, Env.find x sub = Some y -> HasClock Γ x ck -> HasClock Γ' y (subclock_clock bck sub ck)) ->
        (forall x y ck, Env.find x subl = Some y -> HasClock Γ x ck -> HasClock Γ' y (subclock_clock bck sub ck)) ->
        NoDupMembers Γ ->
        wc_env (idck Γ) ->
        wc_clock (idck Γ') bck ->
        noauto_block blk ->
        LastsDefined blk ls ->
        NoDupLocals (map fst Γ) blk ->
        wc_block G Γ blk ->
        switch_block Γ bck sub subl blk st = (blk', st') ->
        wc_block G Γ' blk'.
    Proof.
      Opaque switch_scope.
      induction blk using block_ind2; intros * Hsubin Hsublin Hck Hl Hsub Hsubl Hnd1 Hwenv Hbck LD Hnl2 Hnd2 Hwc Hsw;
        inv Hnl2; inv Hnd2; inv Hwc; inv LD; repeat inv_bind; simpl in *.
      - (* equation *)
        constructor. eapply subclock_equation_wc; eauto.

      - (* last *)
        edestruct Hl as (Ck'&L'); eauto.
        1:{ apply Env.Props.P.F.not_find_in_iff. intros ?.
            eapply Hsublin; eauto. }
        econstructor; eauto using subclock_exp_wc.
        take (clockof _ = _) and now rewrite subclock_exp_clockof, it.

      - (* reset *)
        econstructor; eauto using subclock_exp_wc.
        2:rewrite subclock_exp_clockof, H7; simpl; eauto.
        apply mmap_values, Forall2_ignore1 in H0.
        simpl_Forall. inv_VarsDefined. eapply H with (ls:=xs0); eauto.
        + intros * Sub1 In. eapply Hsublin; eauto using in_concat'.

      - (* switch *)
        destruct (partition _ _) eqn:Hpart; repeat inv_bind.
        apply partition_Partition in Hpart.
        destruct x; repeat inv_bind.
        assert (wc_clock (idck Γ') (subclock_clock bck sub ck)) as Hck'.
        { eapply subclock_clock_wc; eauto.
          take (wc_exp _ _ _) and eapply wc_exp_clockof in it; eauto.
          rewrite H6 in it. simpl_Forall. eauto. }
        rewrite subclock_exp_clockof, H6 in *; simpl in *.

        assert (HasClock (Γ' ++ senv_of_tyck l1) i (subclock_clock bck sub ck)) as Hini.
        { eapply cond_eq_In in H0; eauto using subclock_exp_wc.
          rewrite subclock_exp_clockof, H6; simpl; auto. }

        assert (NoDupMembers (filter (fun '(_, ann) => ann.(clo) ==b ck) l0 ++ l)) as Hnd'.
        { rewrite Permutation_app_comm.
          eapply switch_block_NoDupMembers_env; eauto. }

        assert (forall x a, In (x, a) (filter (fun '(_, ann) => clo ann ==b ck) l0) -> HasClock Γ x ck) as FreeCk.
        { intros * In.
          apply Partition_Permutation in Hpart.
          rewrite Hpart, HasClock_app. right.
          simpl_In. econstructor. solve_In; eauto.
          rewrite equiv_decb_equiv in Hf. auto. }

        assert (forall x a, In (x, a) l -> HasClock Γ x ck) as DefCk.
        { intros * In.
          assert (Is_defined_in (FunctionalEnvironment.Var x4) (Bswitch ec branches)) as Hdef.
          { eapply vars_defined_Is_defined_in.
            eapply Partition_Forall1, Forall_forall in Hpart; eauto; simpl in *.
            apply PSF.mem_2; auto. }
          inv Hdef. simpl_Exists. simpl_Forall.
          repeat (Syn.inv_branch || Clo.inv_branch). simpl_Exists. simpl_Forall.
          take (Is_defined_in _ _) and eapply wc_block_Is_defined_in in it; eauto.
          simpl_In.
          eapply H8; eauto with senv.
        }

        do 2 econstructor; eauto; repeat rewrite idfst_app; repeat rewrite idsnd_app; repeat rewrite map_app; repeat rewrite Forall_app; repeat split.
        + eapply cond_eq_wc_clock in H0; eauto.
          unfold idty, idck. simpl_Forall.
          eapply Forall_forall in H0; [|solve_In].
          eapply wc_clock_incl; eauto. solve_incl_app.
        + eapply cond_eq_In in H0; eauto using subclock_exp_wc.
          2:{ rewrite subclock_exp_clockof, H6; simpl; auto. }
          clear - H0 H9 H6 Hck'.
          eapply Forall_impl. intros ??.
          1:{ eapply wc_clock_incl with (vars:=idck (Γ'++senv_of_tyck l1)); eauto.
              simpl_app. apply incl_appr', incl_appl.
              intros ? Hin; solve_In. }
          eapply mmap_values, Forall2_ignore1 in H9. inv H0.
          simpl_Forall. simpl_In. simpl_Forall. repeat inv_bind.
          rewrite ? in_app_iff in Hin0. destruct Hin0 as [|[|]].
          * eapply new_idents_wc in H2. simpl_Forall; eauto.
            2:solve_In; eauto; congruence.
            eapply wc_clock_incl; eauto. solve_incl_app.
          * eapply new_idents_wc in H3. simpl_Forall; eauto.
            2:solve_In; eauto; congruence.
            eapply wc_clock_incl; eauto. solve_incl_app.
          * eapply new_idents_wc in H4. simpl_Forall; eauto.
            2:solve_In; eauto; congruence.
            eapply wc_clock_incl; eauto. solve_incl_app.
        + simpl_Forall.
          eapply merge_defs_wc; eauto.
          * simpl_app. repeat rewrite HasClock_app in *. destruct Hini as [Hini|Hini]; eauto.
            right; left; inv Hini; simpl_In. econstructor; solve_In; auto.
          * rewrite HasClock_app; left.
            eapply rename_var_wc; eauto.
          * apply mmap_length in H9. destruct x, branches; simpl in *; try congruence.
          * eapply mmap_values, Forall2_ignore1 in H9. simpl_Forall.
            simpl_app. rewrite 2 HasClock_app. do 2 right. repeat inv_bind.
            eapply new_idents_In with (ids1:=filter _ _) in H16; eauto.
            2:eapply InMembers_app, or_intror, In_InMembers; eauto.
            simpl_In. econstructor; solve_In.
            2:{ rewrite app_assoc, in_app_iff. left. eauto. }
            simpl; rewrite map_app; auto. auto.
        + eapply CS.mmap2_values in H12. eapply mmap_values, Forall3_ignore3' with (zs:=x3) in H9.
          2:{ eapply Forall3_length in H12 as (?&?); congruence. }
          2:{ eapply mmap_length in H9; eauto. }
          eapply Forall3_Forall3 in H9; eauto. clear H12.
          apply Forall_concat. eapply Forall3_ignore12 in H9. simpl_Forall.
          repeat inv_branch. repeat inv_bind.

          assert (forall x, InMembers x (map (fun '(x, y, _) => (x, y)) (l4 ++ l3)) ->
                       InMembers x (filter (fun '(_, ann) => ann.(clo) ==b ck) l0 ++ l)) as Hinminv.
          { intros ? Hinm. rewrite fst_InMembers in Hinm. rewrite fst_InMembers.
            erewrite map_app, <-2 new_idents_old, <-map_app; eauto.
            erewrite map_map, map_ext in Hinm; eauto. intros ((?&?)&(?&?)); auto.
          }

          assert (forall x, InMembers x (map (fun '(x, y, _) => (x, y)) l2) ->
                       InMembers x (filter (fun '(_, ann0) => isSome (causl_last ann0)) (filter (fun '(_, ann) => ann.(clo) ==b ck) l0 ++ l))) as Hinminv2.
          { intros ? Hinm. rewrite fst_InMembers in Hinm. rewrite fst_InMembers.
            simpl_In. eapply new_idents_In_inv in H18 as (?&?&?); eauto.
            solve_In. }

          take (In _ (_ ++ _ ++ _)) and rewrite 2 in_app_iff in it; destruct it as [Hinblks|[Hinblks|Hinblks]]; simpl_In; simpl_Forall.
          *{ eapply mmap_values, Forall2_ignore1 in H14.
             repeat (Syn.inv_branch || Clo.inv_branch). simpl_Forall.
             eapply H with (ls:=[]) in H3; eauto.
             - intros ? Hin. erewrite 2 Env.In_from_list in Hin. destruct Hin as [Hin|Hin].
               + erewrite Permutation_app_comm, fst_InMembers, map_map, map_ext, <-fst_InMembers; auto.
                 intros (?&?); auto.
               + eapply Hinminv2 in Hin.
                 rewrite ? map_app, <-? filter_app, InMembers_app in *. destruct Hin; [right|left]; solve_In.
             - intros ?? Hfind Hin; exfalso.
               assert (Hnin:=Hfind). rewrite <-Env.Props.P.F.not_find_in_iff, Env.In_from_list in Hnin.
               eapply Hnin. inv Hin.
               erewrite fst_InMembers, map_map, map_ext, map_app, 2 new_idents_old; eauto.
               2:intros; destruct_conjs; auto.
               rewrite Permutation_app_comm, <-map_app. solve_In.
             - intros ?? Hfind Ck L. exfalso.
               inv Ck. inv L. simpl_In.
               eapply NoDupMembers_det in Hin0; eauto; subst. 2:now rewrite Permutation_app_comm.
               assert (Hnin:=Hfind). rewrite <-Env.Props.P.F.not_find_in_iff, Env.In_from_list in Hnin.
               eapply Hnin.
               erewrite fst_InMembers, map_map, map_ext, new_idents_old; eauto.
               2:intros; destruct_conjs; auto.
               rewrite Permutation_app_comm. solve_In. destruct (causl_last a0); auto.
             - intros * Hfind Hin. inv Hin. simpl_In.
               eapply new_idents_In with (ids1:=filter _ _) in H15; eauto.
               2:{ eapply Env.find_In, Env.In_from_list in Hfind; eauto. }
               unfold rename_var in H15. rewrite Hfind in H15. simpl_In. simpl_app. simpl_In.
               do 2 right. econstructor. solve_In; eauto.
               2:{ rewrite app_assoc, in_app_iff; eauto. } auto. auto.
             - intros * Hfind Hin. inv Hin. simpl_In.
               eapply new_idents_Inl with (ids1:=filter _ _) in H18; eauto using NoDupMembers_filter.
               2:{ eapply Env.find_In, Env.In_from_list in Hfind; eauto. }
               unfold rename_var in H18. rewrite Hfind in H18. simpl_In. simpl_app. simpl_In.
               do 2 right. econstructor. solve_In; eauto.
               2:{ rewrite app_assoc, in_app_iff; eauto. } auto. auto.
             - erewrite fst_NoDupMembers, map_map, <-map_ext, <-fst_NoDupMembers; eauto. 2:intros (?&?); auto.
               now rewrite Permutation_app_comm.
             - apply Forall_map, Forall_map, Forall_forall; intros (?&?) ?; simpl; auto with clocks.
             - constructor.
               + eapply wc_clock_incl; eauto. solve_incl_app.
               + simpl_app. repeat rewrite in_app_iff; auto.
                 destruct Hini as [Hini|Hini]; inv Hini; [left|right;left]; solve_In.
                 congruence.
             - eapply NoDupLocals_incl; eauto.
               apply Partition_Permutation in Hpart. rewrite Hpart.
               rewrite map_map, 2 map_app.
               apply incl_app; [apply incl_appl|apply incl_appr].
               + erewrite map_ext; try reflexivity. intros (?&?); auto.
               + erewrite map_ext; try eapply incl_map, incl_filter', incl_refl.
                 intros (?&?); auto.
             - eapply wc_block_incl; [| |eauto]; intros * Hin.
               + eapply H8 in Hin as (Hin&?); subst.
                 apply Partition_Permutation in Hpart. rewrite Hpart, HasClock_app in Hin.
                 rewrite map_app, HasClock_app.
                 destruct Hin as [Hin|Hin]; inv Hin; [left|right]; econstructor; solve_In.
                 1,3:reflexivity. apply equiv_decb_refl.
               + assert (HasClock Γ x15 ck) as Ck.
                 { inv Hin. edestruct H8; eauto with senv. } eapply H10 in Hin.
                 inv Hin. inv Ck. eapply NoDupMembers_det in H14; eauto; subst.
                 apply Partition_Permutation in Hpart. rewrite Hpart, in_app_iff in H22.
                 rewrite map_app, IsLast_app.
                 destruct H22 as [Hin|Hin]; [left|right]; econstructor; solve_In.
                 2:apply equiv_decb_refl.
                 1,2:destruct e0; simpl in *; auto.
           }
          *{ simpl_Forall.
             eapply when_free_wc.
             - eapply HasClock_app, or_introl, rename_var_wc; eauto.
               eapply new_idents_In_inv in H11 as (?&?&?); eauto; subst.
             - simpl_app. rewrite 2 HasClock_app. do 2 right.
               eapply new_idents_In_inv_ck in H11; eauto. rewrite <-H11; clear H11.
               econstructor; solve_In; eauto with datatypes. simpl; auto. auto.
             - simpl_app. repeat rewrite HasClock_app in *. destruct Hini as [Hini|Hini]; eauto.
               right; left; inv Hini; simpl_In. econstructor; solve_In; auto.
           }
          *{ assert (HasClock Γ i0 ck) as Ck.
             { eapply new_idents_In_inv in H18 as (?&Hin'&?); eauto; subst. simpl_In.
               apply in_app_iff in Hin0 as [|]; eauto.
             }
             assert (IsLast Γ i0) as L.
             { eapply new_idents_In_inv in H18 as (?&Hin'&?); eauto; subst. simpl_In.
               apply isSome_true in Hf as (?&?).
               apply Partition_Permutation in Hpart. rewrite Hpart, IsLast_app.
               apply in_app_iff in Hin0 as [|]; simpl_In; [right|left]; econstructor; eauto; congruence. }
             eapply when_freel_wc.
             - intros * Hnone. edestruct Hl; eauto.
               rewrite HasClock_app, IsLast_app. eauto.
             - simpl_app. repeat rewrite HasClock_app in *. destruct Hini as [Hini|Hini]; eauto.
               right; left; inv Hini; simpl_In. econstructor; solve_In; auto.
             - simpl_app. rewrite 2 HasClock_app. do 2 right.
               eapply new_idents_In_inv_ck in H18; eauto. rewrite <-H18; clear H18.
               econstructor; solve_In; eauto with datatypes. simpl; auto. auto.
             - intros * Hfind. rewrite HasClock_app; eauto.
           }

        + simpl_Forall.
          eapply cond_eq_wc in H0; eauto using subclock_exp_wc. simpl_Forall.
          2:repeat rewrite subclock_exp_clockof, H6; simpl; auto.
          constructor. eapply wc_equation_incl; [| |eauto]; intros * Hin.
          * simpl_app. repeat rewrite HasClock_app in *. destruct Hin as [|Hin]; [|right;left]; auto.
            inv Hin; simpl_In; econstructor; solve_In. auto.
          * rewrite IsLast_app in *. destruct Hin as [|Hin]; auto.
            exfalso. inv Hin. simpl_In. congruence.

      - (* local *)
        constructor.
        eapply switch_scope_wc; eauto.
        intros; simpl in *.
        apply mmap_values, Forall2_ignore1 in H18. simpl_Forall. inv_VarsDefined.
        eapply H with (ls:=xs); eauto. intros * ??.
        eapply H6; eauto. take (Permutation _ _) and rewrite <-it. eauto using in_concat'.
        Transparent switch_scope.
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
    intros * HwG Heq Wc. inv Wc.
    pose proof (n_syn n) as Hsyn. inv Hsyn.
    pose proof (n_lastd n) as (?&Hlast&_).
    constructor; auto.
    - eapply iface_incl_wc_block; eauto.
      eapply switch_block_wc with (sub:=Env.empty _) (subl:=Env.empty _) in H1; eauto using node_NoDupMembers, node_NoDupLocals with clocks.
      + intros * [In|In]; apply Env.Props.P.F.empty_in_iff in In; inv In.
      + intros * In; apply Env.Props.P.F.empty_in_iff in In; inv In.
      + intros * _ Ck. now rewrite subclock_clock_idem.
      + intros * Ck L. now rewrite subclock_clock_idem.
      + intros ??? Hfind. rewrite Env.gempty in Hfind. congruence.
      + intros ??? Hfind. rewrite Env.gempty in Hfind. congruence.
      + unfold idck, senv_of_ins, senv_of_decls. erewrite map_app, 2 map_map, map_ext, map_ext with (l:=n_out n); eauto.
        1,2:unfold decl; intros; destruct_conjs; auto.
      + eapply surjective_pairing.
  Qed.

  Lemma switch_global_wc : forall G,
      wc_global G ->
      wc_global (switch_global G).
  Proof.
    intros []. unfold wc_global, CommonTyping.wt_program; simpl.
    induction nodes0; intros * Hwc; simpl; inv Hwc; auto with datatypes.
    destruct H1.
    constructor; [constructor|].
    - eapply switch_node_wc; eauto.
      2:eapply iface_eq_iface_incl, switch_global_iface_eq.
      eapply H2; eauto.
    - rewrite Forall_map. eapply Forall_impl; [|eapply H0]; intros.
      simpl; eauto.
    - eapply IHnodes0; eauto.
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
