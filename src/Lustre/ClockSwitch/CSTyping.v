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
From Velus Require Import Lustre.LTyping.
From Velus Require Import Lustre.ClockSwitch.ClockSwitch.
From Velus Require Import Lustre.SubClock.SCTyping.

Module Type CSTYPING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import CS : CLOCKSWITCH Ids Op OpAux Cks Senv Syn).

  Module Import SCT := SCTypingFun Ids Op OpAux Cks Senv Syn Typ SC. Import SC.

  Import Fresh Facts Tactics.

  Section switch_block.

    Context {PSyn : list decl -> block -> Prop} {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Import Permutation.

    Lemma cond_eq_wt vars : forall e ty ck x xcs eqs' st st',
        wt_exp G vars e ->
        typeof e = [ty] ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        Forall (wt_equation G (vars++senv_of_tyck xcs)) eqs'.
    Proof.
      intros * Hwt Hck Hcond; destruct e; destruct_conjs; repeat inv_bind.
      all:constructor; auto; rewrite Permutation_app_comm; simpl.
      all:(constructor; [constructor; auto; eapply wt_exp_incl in Hwt; eauto;
                          intros * Hl; inv Hl; econstructor; eauto with datatypes|]).
      all:try take (_ = [_]) and rewrite it; try rewrite app_nil_r; eauto.
      all:constructor; auto; eauto with senv datatypes.
    Qed.

    Lemma cond_eq_wt_clock vars : forall e ty ck x xcs eqs' st st',
        wt_clock G.(types) vars ck ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        Forall (wt_clock G.(types) vars) (map snd (idsnd xcs)).
    Proof.
      intros * Hck Hcond; destruct e; repeat inv_bind; simpl; auto.
      destruct a; repeat inv_bind; simpl; auto.
    Qed.

    Lemma cond_eq_wt_type : forall e ty ck x xcs eqs' st st',
        wt_type G.(types) ty ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        Forall (wt_type G.(types)) (map snd (idfst xcs)).
    Proof.
      intros * Hck Hcond; destruct e; repeat inv_bind; simpl; auto.
      destruct a; repeat inv_bind; simpl; auto.
    Qed.

    Lemma cond_eq_In Γ : forall e ty ck x xcs eqs' st st',
        wt_exp G Γ e ->
        typeof e = [ty] ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        HasType (Γ ++ senv_of_tyck xcs) x ty.
    Proof.
      intros * Hwt Hck Hcond; destruct e; repeat inv_bind; simpl in *; eauto with senv datatypes.
      inv Hwt. repeat inv_bind.
      inv Hck; eauto with senv datatypes.
    Qed.

    Lemma new_idents_wt_clock Γ' : forall ck x tx tn k ids ids' st st',
        In (Tenum tx tn) G.(types) ->
        k < length tn ->
        wt_clock G.(types) Γ' ck ->
        HasType Γ' x (Tenum tx tn) ->
        new_idents ck x (Tenum tx tn) k ids st = (ids', st') ->
        Forall (fun '(_, _, (_, ck)) => wt_clock G.(types) Γ' ck) ids'.
    Proof.
      intros * Hen Hk Hck Hin Hni.
      unfold new_idents in *. eapply mmap_values, Forall2_ignore1 in Hni.
      repeat setoid_rewrite Forall_map.
      eapply Forall_impl; [|eauto]; intros ((?&?)&?&?) ((?&?)&?&?&?&?); repeat inv_bind.
      econstructor; eauto.
    Qed.

    Lemma new_idents_wt_type : forall ck x tx tn k ids ids' st st',
        Forall (wt_type G.(types)) (map (fun '(_, ann) => ann.(typ)) ids) ->
        new_idents ck x (Tenum tx tn) k ids st = (ids', st') ->
        Forall (fun '(_, _, (ty, _)) => wt_type G.(types) ty) ids'.
    Proof.
      intros * Hwt Hni.
      unfold new_idents in *. eapply mmap_values, Forall2_ignore1 in Hni.
      simpl_Forall. simpl_In. simpl_Forall. repeat inv_bind. auto.
    Qed.

    Lemma when_free_wt Γ : forall x y ty ck cx tx tn k,
        HasType Γ x ty ->
        HasType Γ y ty ->
        HasType Γ cx (Tenum tx tn) ->
        k < length tn ->
        In (Tenum tx tn) G.(types) ->
        wt_clock G.(types) Γ ck ->
        wt_block G Γ (when_free x y ty ck cx (Tenum tx tn) k).
    Proof.
      intros.
      repeat (econstructor; simpl; eauto).
    Qed.

    Lemma when_freel_wt Γ subl : forall x y ty ck cx tx tn k,
        HasType Γ y ty ->
        HasType Γ x ty ->
        IsLast Γ x ->
        (forall y, Env.find x subl = Some y -> HasType Γ y ty) ->
        HasType Γ cx (Tenum tx tn) ->
        k < length tn ->
        In (Tenum tx tn) G.(types) ->
        wt_clock G.(types) Γ ck ->
        wt_block G Γ (when_freel subl x y ty ck cx (Tenum tx tn) k).
    Proof.
      intros.
      repeat (econstructor; simpl; eauto).
      1,2:unfold rename_last; cases_eqn Eq; auto.
      1,2:econstructor; eauto.
    Qed.

    Lemma merge_defs_wt Γ : forall sub y ty ck x tx tn xcs,
        HasType Γ x (Tenum tx tn) ->
        In (Tenum tx tn) G.(types) ->
        HasType Γ (rename_var sub y) ty ->
        wt_clock G.(types) Γ ck ->
        xcs <> [] ->
        Permutation (map fst xcs) (seq 0 (length tn)) ->
        Forall (fun '(k, sub) => HasType Γ (rename_var sub y) ty) xcs ->
        wt_block G Γ (merge_defs sub y ty ck x (Tenum tx tn) xcs).
    Proof.
      intros * Hin1 Htn Hin2 Hck Hnnil Hperm Hf.
      repeat constructor; auto.
      - erewrite map_map, map_ext; eauto. intros (?&?); auto.
      - contradict Hnnil. apply map_eq_nil in Hnnil; auto.
      - rewrite Forall_map. eapply Forall_impl_In; [|eauto]; intros (?&?) Hin ?.
        repeat constructor; auto.
        eapply In_InMembers, fst_InMembers in Hin. rewrite Hperm in Hin.
        apply in_seq in Hin as (?&?); auto.
      - rewrite Forall_map. eapply Forall_forall; intros (?&?) Hin; simpl; auto.
    Qed.

    Lemma new_idents_In : forall x ty ck cx tx k ids1 ids2 nids1 nids2 st1 st2 st3 st4,
        NoDupMembers (ids1++ids2) ->
        HasType (ids1++ids2) x ty ->
        new_idents ck cx tx k ids1 st1 = (nids1, st2) ->
        new_idents ck cx tx k ids2 st3 = (nids2, st4) ->
        In (rename_var (Env.from_list (map (fun '(x, y, _) => (x, y)) (nids1 ++ nids2))) x, ty)
           (map (fun '(_, x, (ty, _)) => (x, ty)) (nids1++nids2)).
    Proof.
      intros * Hnd Hinm Hni1 Hni2.
      assert (NoDupMembers (map (fun '(x, y, _) => (x, y)) (nids1 ++ nids2))) as Hnd'.
      { erewrite fst_NoDupMembers, map_map, map_ext, map_app, 2 new_idents_old; eauto.
        rewrite <-map_app, <-fst_NoDupMembers; auto.
        intros ((?&?)&?&?); auto. }
      eapply mmap_values, Forall2_ignore2 in Hni1.
      eapply mmap_values, Forall2_ignore2 in Hni2. simpl_In.
      destruct Hinm as [Hin|Hin]; inv Hin; simpl_Forall; repeat inv_bind.
      - solve_In; eauto with datatypes.
        f_equal; auto.
        unfold rename_var. erewrite Env.find_In_from_list; eauto.
        2:solve_In; eauto with datatypes. 1,2:reflexivity.
      - solve_In; eauto with datatypes.
        f_equal; auto.
        unfold rename_var. erewrite Env.find_In_from_list; eauto.
        2:solve_In; eauto with datatypes. 1,2:reflexivity.
    Qed.

    Lemma new_idents_Inl : forall x ty ck cx tx k ids1 nids1 st1 st2,
        NoDupMembers ids1 ->
        HasType ids1 x ty ->
        new_idents ck cx tx k ids1 st1 = (nids1, st2) ->
        In (rename_var (Env.from_list (map (fun '(x, y, _) => (x, y)) nids1)) x, ty)
           (map (fun '(_, x, (ty, _)) => (x, ty)) nids1).
    Proof.
      intros * Hnd Hinm Hni1.
      assert (NoDupMembers (map (fun '(x, y, _) => (x, y)) nids1)) as Hnd'.
      { erewrite fst_NoDupMembers, map_map, map_ext, new_idents_old; eauto.
        rewrite <-fst_NoDupMembers; auto.
        intros ((?&?)&?&?); auto. }
      eapply mmap_values, Forall2_ignore2 in Hni1. simpl_In.
      inv Hinm; simpl_Forall; repeat inv_bind.
      - solve_In; eauto with datatypes.
        f_equal; auto.
        unfold rename_var. erewrite Env.find_In_from_list; eauto.
        2:solve_In; eauto with datatypes. reflexivity.
    Qed.

    Lemma switch_scope_wt {A} P_na P_nd P_wt f_switch :
      forall locs (blk: A) bck sub subl Γck Γty Γty' s' st st',
        (forall x, Env.In x sub \/ Env.In x subl -> InMembers x Γck) ->
        (forall x ty, HasType Γty x ty -> HasType Γty' x ty) ->
        (forall x, IsLast Γty x -> IsLast Γty' x) ->
        (forall x y ty, Env.find x sub = Some y -> HasType Γty x ty -> HasType Γty' y ty)->
        (forall x y ty, Env.find x subl = Some y -> HasType Γty x ty -> HasType Γty' y ty) ->
        (forall x ty, HasType Γck x ty -> HasType Γty x ty) ->
        (forall x, IsLast Γck x -> IsLast Γty x) ->
        NoDupMembers Γty ->
        NoDupMembers Γck ->
        Forall (wt_type G.(types)) (map (fun '(_, a) => a.(typ)) Γty) ->
        wt_clock G.(types) Γty' bck ->
        noauto_scope P_na (Scope locs blk) ->
        NoDupScope P_nd (map fst Γty) (Scope locs blk) ->
        wt_scope P_wt G Γty (Scope locs blk) ->
        switch_scope f_switch Γck bck sub (Scope locs blk) st = (s', st') ->
        (forall Γty Γck Γty' blk' st st',
            (forall x, Env.In x sub \/ Env.In x subl -> InMembers x Γck) ->
            (forall x ty, HasType Γty x ty -> HasType Γty' x ty) ->
            (forall x, IsLast Γty x -> IsLast Γty' x) ->
            (forall x y ty, Env.find x sub = Some y -> HasType Γty x ty -> HasType Γty' y ty)->
            (forall x y ty, Env.find x subl = Some y -> HasType Γty x ty -> HasType Γty' y ty) ->
            (forall x ty, HasType Γck x ty -> HasType Γty x ty) ->
            (forall x, IsLast Γck x -> IsLast Γty x) ->
            NoDupMembers Γty ->
            NoDupMembers Γck ->
            Forall (wt_type G.(types)) (map (fun '(_, a) => a.(typ)) Γty) ->
            wt_clock G.(types) Γty' bck ->
            P_na blk ->
            P_nd (map fst Γty) blk ->
            P_wt Γty blk ->
            f_switch Γck blk st = (blk', st') ->
            P_wt Γty' blk') ->
        wt_scope P_wt G Γty' s'.
    Proof.
      intros * Hsubin Hty Hl Hsub Hsubl Hincl HinclL Hnd1 Hnd2 Hwenv Hbck Hnl2 Hnd3 Hwt Hswitch Hind;
        inv Hnl2; inv Hnd3; inv Hwt; repeat inv_bind; subst Γ'; simpl in *.
      econstructor; eauto.
      - unfold wt_clocks, idfst, senv_of_decls in *.
        simpl_Forall. subst.
        eapply subclock_clock_wt with (Γ:=Γty++_); eauto.
        + intros * Hin. rewrite HasType_app in *.
          destruct Hin as [Hin|Hin]; eauto.
          inv Hin. simpl_In. right. econstructor. solve_In. auto.
        + intros * Hfind Hin. rewrite HasType_app in *.
          destruct Hin as [Hin|Hin]; eauto.
          exfalso. simpl_In.
          eapply Env.find_In, or_introl, Hsubin, fst_InMembers in Hfind. inv Hin; simpl_In.
          eapply H5; eauto using In_InMembers.
          simpl_In. assert (HasType Γck x0 a.(typ)) as Ht by eauto with senv.
          apply Hincl in Ht. inv Ht. solve_In.
        + eapply wt_clock_incl; [|eauto]. intros *. rewrite HasType_app. auto.
      - simpl_Forall; auto.
      - eapply Hind with (Γty:=Γty++senv_of_decls _) (Γck:=Γck++senv_of_decls _); eauto.
        + intros ? Hin. apply InMembers_app; auto.
        + intros ?? Hin.
          repeat rewrite HasType_app in *. destruct Hin as [Hin|Hin]; eauto.
          right. inv Hin. simpl_In. econstructor; solve_In; auto.
        + intros * L. rewrite IsLast_app in *. destruct L as [L|L]; auto.
          inv L. simpl_In. right. econstructor. solve_In. simpl; auto.
        + intros ??? Hfind Hin.
          repeat rewrite HasType_app in *. destruct Hin as [Hin|Hin]; eauto.
          exfalso. eapply Env.find_In, or_introl, Hsubin, fst_InMembers in Hfind; eauto.
          inv Hin. simpl_In.
          assert (HasType Γck x0 a.(typ)) as Ht by eauto with senv.
          apply Hincl in Ht. inv Ht.
          eapply H5; eauto using In_InMembers. solve_In.
        + intros ??? Hfind Ty.
          rewrite HasType_app. apply HasType_app in Ty as [Ty|Ty]; eauto using NoDupScope_NoDupMembers.
          right.
          exfalso. eapply Env.find_In, or_intror, Hsubin, fst_InMembers in Hfind; eauto.
          inv Ty. simpl_In.
          assert (HasType Γck x0 a.(typ)) as Ht by eauto with senv.
          apply Hincl in Ht. inv Ht.
          eapply H5; eauto using In_InMembers. solve_In.
        + intros * Hin. rewrite HasType_app in *.
          destruct Hin as [Hin|Hin]; auto.
        + intros * L. rewrite IsLast_app in *. destruct L as [|]; auto.
        + apply NoDupMembers_app; auto. rewrite NoDupMembers_senv_of_decls; auto.
          intros ? Hinm1 Hinm2. rewrite InMembers_senv_of_decls in Hinm2. rewrite fst_InMembers in Hinm1.
          eapply H5; eauto.
        + apply NoDupMembers_app; auto. apply NoDupMembers_map; auto. intros; destruct_conjs; auto.
          intros ? Hinm1 Hinm2. rewrite InMembers_senv_of_decls in Hinm2.
          eapply H5; eauto.
          eapply InMembers_In in Hinm1 as (?&Hin1).
          assert (HasType Γck x0 x1.(typ)) as Ht by eauto with senv.
          apply Hincl in Ht. inv Ht; solve_In.
        + rewrite map_app, Forall_app. split; auto. simpl_Forall; simpl_In; simpl_Forall; auto.
        + eapply wt_clock_incl; [|eauto]. intros *. rewrite HasType_app; auto.
        + rewrite map_app, map_fst_senv_of_decls. auto.
    Qed.

    Lemma switch_block_wt : forall blk bck sub subl Γck Γty Γty' blk' st st',
        wt_global G ->
        (forall x, Env.In x sub \/ Env.In x subl -> InMembers x Γck) ->
        (forall x ty, HasType Γty x ty -> HasType Γty' x ty) ->
        (forall x, IsLast Γty x -> IsLast Γty' x) ->
        (forall x y ty, Env.find x sub = Some y -> HasType Γty x ty -> HasType Γty' y ty) ->
        (forall x y ty, Env.find x subl = Some y -> HasType Γty x ty -> HasType Γty' y ty) ->
        (forall x ty, HasType Γck x ty -> HasType Γty x ty) ->
        (forall x, IsLast Γck x -> IsLast Γty x) ->
        NoDupMembers Γty ->
        NoDupMembers Γck ->
        Forall (wt_type G.(types)) (map (fun '(_, a) => a.(typ)) Γty) ->
        wt_clock G.(types) Γty' bck ->
        noauto_block blk ->
        NoDupLocals (map fst Γty) blk ->
        wt_block G Γty blk ->
        switch_block Γck bck sub subl blk st = (blk', st') ->
        wt_block G Γty' blk'.
    Proof.
      Opaque switch_scope.
      induction blk using block_ind2; intros * HwtG Hsubin Hty Hl Hsub Hsubl Hincl HinclL Hnd1 Hnd2 Hwenv Hbck Hnl2 Hnd3 Hwt Hsw;
        inv Hnl2; inv Hnd3; inv Hwt; repeat inv_bind; simpl in *.
      - (* equation *)
        constructor. eapply subclock_equation_wt; eauto.

      - (* last *)
        econstructor; eauto using subclock_exp_wt.
        rewrite subclock_exp_typeof; eauto.

      - (* reset *)
        econstructor; eauto using subclock_exp_wt.
        2:rewrite subclock_exp_typeof; eauto.
        simpl_Forall. eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall.
        eapply H; eauto. simpl_Forall; auto.

      - (* switch *)
        destruct (partition _ _) eqn:Hpart; repeat inv_bind.
        apply partition_Partition in Hpart.
        destruct x; repeat inv_bind.

        assert (length (clockof ec) = 1) as Hlck.
        { rewrite length_clockof_numstreams, <-length_typeof_numstreams, H5; auto. }
        remember (clockof ec) as ck; symmetry in Heqck. singleton_length. rename c into ck.
        assert (wt_clock G.(types) Γty' (subclock_clock bck sub ck)) as Hck'.
        { eapply subclock_clock_wt; eauto.
          eapply wt_exp_clockof in H4; eauto. rewrite Heqck in H4. apply Forall_singl in H4; auto. }

        rewrite subclock_exp_typeof, H5 in *; simpl in *.
        rewrite subclock_exp_clockof, Heqck in *; simpl in *.

        assert (HasType (Γty' ++ senv_of_tyck l1) i (Tenum tx tn)) as Hini.
        { eapply cond_eq_In in H0; eauto using subclock_exp_wt.
          now rewrite subclock_exp_typeof. }

        assert (NoDupMembers (filter (fun '(_, ann) => ann.(clo) ==b ck) l0 ++ l)) as Hnd'.
        { rewrite Permutation_app_comm.
          eapply switch_block_NoDupMembers_env; eauto. }

        do 2 econstructor; eauto; unfold wt_clocks, senv_of_decls; repeat rewrite idfst_app; repeat rewrite idsnd_app;
        repeat rewrite map_app; repeat rewrite Forall_app; repeat split.
        + eapply cond_eq_wt_clock in H0; eauto.
          unfold idfst, idsnd in *. simpl_Forall.
          eapply wt_clock_incl; [|eauto]. intros *. rewrite HasType_app; auto.
        + assert (Forall (fun k => k < length tn) (map fst branches)) as Hlt.
          { rewrite H7. apply Forall_forall; intros ? Hin.
            apply in_seq in Hin as (?&?); auto. }
          clear - Hini H2 H6 Hlt Hck'.
          simpl_Forall. simpl_In.
          eapply wt_clock_incl with (Γ:=Γty'++senv_of_tyck l1).
          1:{ intros. simpl_app. rewrite app_assoc, HasType_app. left. erewrite map_map, map_ext; eauto.
              intros; destruct_conjs; auto. }
          eapply mmap_values, Forall2_ignore1 in H2. simpl_Forall. repeat inv_bind.
          repeat
            (take (new_idents _ _ _ _ _ _ = _) and eapply new_idents_wt_clock with (Γ':=Γty'++_) in it; eauto;
             [|eapply wt_clock_incl; [|eauto]; intros *; rewrite HasType_app; auto|eapply HasType_app; eauto]).
          rewrite ? in_app_iff in Hin0. destruct Hin0 as [|[|]]; simpl_Forall; auto.
        + eapply cond_eq_wt_type in H0; eauto.
          2:{ apply wt_exp_wt_type in H4; auto.
              take (typeof ec = _) and rewrite it in H4. now inv H4. }
          clear - H0.
          unfold idfst in *. simpl_Forall; auto.
        + assert (Forall (wt_type G.(types)) (map (fun '(_, ann) => ann.(typ)) Γck)) as Hwenv2.
          { simpl_Forall.
            assert (HasType Γck k a.(typ)) as Ht by eauto with senv.
            eapply Hincl in Ht. inv Ht. simpl_Forall; auto. congruence. }
          apply Partition_Permutation in Hpart. rewrite Hpart, map_app, Forall_app in Hwenv2.
          clear - Hwenv2 H2 Hck'. destruct Hwenv2 as (Hwenv1&Hwenv2).
          eapply mmap_values in H2.
          induction H2 as [|(?&?) (((?&?)&?)&?)]; simpl in *; auto.
          rewrite 3 map_app. apply Forall_app; split; auto.
          destruct H as (?&?&?); repeat inv_bind.
          repeat (take (new_idents _ _ _ _ _ _ = _) and eapply new_idents_wt_type in it;
                  [|clear it; simpl_Forall; simpl_In; simpl_Forall; eauto]).
          2:{ apply in_app_iff in Hin as [|]; simpl_In; simpl_Forall; eauto. }
          rewrite ? map_app, ?Forall_app.
          repeat split; simpl_Forall; eauto.
        + simpl_Forall.
          eapply merge_defs_wt; eauto.
          * eapply HasType_incl; [|eauto]. apply incl_appr'.
            simpl_app. apply incl_appl. intros ??. solve_In.
          * apply HasType_app. left.
            eapply rename_var_wt; eauto.
            assert (Is_defined_in (FunctionalEnvironment.Var i0) (Bswitch ec branches)) as Hdef.
            { eapply vars_defined_Is_defined_in.
              eapply Partition_Forall1, Forall_forall in Hpart; eauto; simpl in *.
              apply PSF.mem_2; auto. }
            inv Hdef. simpl_Exists.
            eapply Hincl.
            apply Partition_Permutation in Hpart. rewrite Hpart.
            apply HasType_app; eauto with senv.
          * eapply wt_clock_incl; [|eauto]. intros *. rewrite HasType_app; eauto.
          * apply mmap_length in H2. destruct x, branches; simpl in *; try congruence; auto.
          * rewrite <-H7.
            replace (map fst (map _ x)) with (map fst branches). reflexivity.
            clear - H2. apply mmap_values in H2.
            induction H2 as [|(?&?) (((?&?)&?)&?)]; simpl; auto.
            destruct H as (?&?&?); repeat inv_bind.
            f_equal; auto.
          * eapply mmap_values, Forall2_ignore1 in H2. simpl_Forall; repeat inv_bind.
            simpl_app. rewrite 2 HasType_app. do 2 right.
            eapply new_idents_In with (ids1:=filter _ _) in H14; eauto.
            2:{ rewrite HasType_app. right. eauto with senv. } simpl in *.
            simpl_In. econstructor. solve_In.
            2:{ rewrite app_assoc, in_app_iff. left. eauto. }
            simpl; rewrite map_app; auto. auto.
        + eapply CS.mmap2_values in H8. eapply mmap_values, Forall3_ignore3' with (zs:=x3) in H2.
          2:{ eapply Forall3_length in H8 as (?&?); congruence. }
          2:{ eapply mmap_length in H2; eauto. }
          eapply Forall3_Forall3 in H2; eauto. clear H8.
          apply Forall_concat. apply Forall3_ignore12 in H2. simpl_Forall.
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
            simpl_In. eapply new_idents_In_inv in H16 as (?&?&?); eauto.
            solve_In. }

          rewrite 2 in_app_iff in H14. destruct H14 as [Hinblks|[Hinblks|Hinblks]]; simpl_In; simpl_Forall.
          *{ eapply mmap_values, Forall2_ignore1 in H12.
             repeat (Syn.inv_branch || Typ.inv_branch). simpl_Forall.
             eapply H with (Γty:=Γty) in H3; eauto.
             - intros ? Hin. erewrite 2 Env.In_from_list in Hin. destruct Hin as [Hin|Hin].
               + erewrite Permutation_app_comm, fst_InMembers, map_map, map_ext, <-fst_InMembers; auto.
                 intros (?&?); auto.
               + eapply Hinminv2 in Hin.
                 rewrite ? map_app, <-? filter_app, InMembers_app in *. destruct Hin; [right|left]; solve_In.
             - intros. rewrite HasType_app; auto.
             - intros. rewrite IsLast_app; auto.
             - intros * Hfind Hin.
               assert (HasType (filter (fun '(_, ann) => ann.(clo) ==b ck) l0 ++ l) x15 ty) as Hin'.
               { eapply Env.find_In, Env.In_from_list, Hinminv in Hfind; eauto.
                 eapply InMembers_In in Hfind as (ann'&?).
                 assert (HasType Γty x15 ann'.(typ)) as Hin'.
                 { eapply Hincl.
                   apply Partition_Permutation in Hpart. rewrite Hpart.
                   econstructor; eauto. rewrite in_app_iff in *. destruct H12; eauto. right; simpl_In; eauto. }
                 inv Hin. inv Hin'. eapply NoDupMembers_det in H17; eauto; subst.
                 econstructor; eauto.
               }
               eapply new_idents_In with (ids1:=filter _ _) in H13; eauto. clear Hin'.
               simpl_In. do 2 right. econstructor; solve_In.
               2:{ rewrite app_assoc, in_app_iff; eauto. }
               unfold rename_var. destruct (Env.find _ _); try congruence. rewrite Hfind; auto. auto.
             - intros * Hfind Hin.
               assert (HasType (filter (fun '(_, ann0) => isSome (causl_last ann0)) (filter (fun '(_, ann) => ann.(clo) ==b ck) l0 ++ l)) x15 ty) as Hin'.
               { eapply Env.find_In, Env.In_from_list, Hinminv2 in Hfind; eauto.
                 eapply InMembers_In in Hfind as (ann'&Hin2).
                 assert (HasType Γty x15 ann'.(typ)) as Hin'.
                 { eapply Hincl.
                   apply Partition_Permutation in Hpart. rewrite Hpart.
                   econstructor; eauto. rewrite <-? filter_app, in_app_iff in *.
                   destruct Hin2 as [|]; [right|left]; simpl_In; eauto. }
                 inv Hin. inv Hin'. eapply NoDupMembers_det in H12; eauto; subst.
                 econstructor; eauto.
               }
               eapply new_idents_Inl with (ids1:=filter _ _) in H16; eauto. clear Hin'.
               2:{ apply NoDupMembers_filter; eauto using NoDupMembers_app_l. }
               simpl_In. do 2 right. econstructor; solve_In.
               2:{ rewrite app_assoc, in_app_iff; eauto. }
               unfold rename_var. destruct (Env.find _ _); try congruence. rewrite Hfind; auto. auto.
             - intros * Hin. simpl_In. eapply Hincl.
               apply Partition_Permutation in Hpart. rewrite Hpart.
               rewrite map_app in Hin. rewrite HasType_app in *.
               destruct Hin as [Hin|Hin]; inv Hin; simpl_In; eauto with senv.
             - intros * Hin. simpl_In. eapply HinclL.
               apply Partition_Permutation in Hpart. rewrite Hpart.
               rewrite map_app in Hin. rewrite IsLast_app in *.
               destruct Hin as [Hin|Hin]; inv Hin; simpl_In; eauto with senv.
             - erewrite fst_NoDupMembers, map_map, <-map_ext, <-fst_NoDupMembers; eauto. 2:intros (?&?); auto.
               now rewrite Permutation_app_comm.
             - simpl_Forall; auto.
             - constructor; auto.
               + eapply HasType_incl; [|eapply HasType_app; eauto]. apply incl_appr'.
                 simpl_app. apply incl_appl. intros ??. solve_In.
               + take (In _ branches) and eapply In_InMembers, fst_InMembers in it;
                   rewrite H7 in it; apply in_seq in it as (?&?); auto.
               + eapply wt_clock_incl; [|eauto]. intros *. rewrite HasType_app; auto.
           }
          *{ simpl_Forall.
             eapply when_free_wt; eauto.
             - eapply HasType_app, or_introl, rename_var_wt; eauto.
               eapply new_idents_In_inv in H10 as (?&Hin'&?); eauto; subst. simpl_In.
               rewrite equiv_decb_equiv in Hf. inv Hf.
               eapply Hincl.
               apply Partition_Permutation in Hpart. rewrite Hpart, HasType_app; eauto with senv.
             - simpl_app. rewrite 2 HasType_app. do 2 right. econstructor; solve_In; eauto with datatypes. 1,2:auto.
             - simpl_app. rewrite app_assoc, HasType_app. left. erewrite map_map, map_ext; simpl_In; eauto.
               intros; destruct_conjs; auto.
             - take (In _ branches) and eapply In_InMembers, fst_InMembers in it;
                   rewrite H7 in it; apply in_seq in it as (?&?); auto.
             - eapply wt_clock_incl; [|eauto]. intros *. rewrite HasType_app; auto.
           }
          *{ simpl_Forall.
             assert (HasType Γty i0 t) as Ty.
             { eapply new_idents_In_inv in H16 as (?&Hin'&?); eauto; subst. simpl_In.
               eapply Hincl.
               apply Partition_Permutation in Hpart. rewrite Hpart, HasType_app.
               apply in_app_iff in Hin0 as [|]; simpl_In; eauto with senv. }
             assert (IsLast Γty i0) as L.
             { eapply new_idents_In_inv in H16 as (?&Hin'&?); eauto; subst. simpl_In.
               apply isSome_true in Hf as (?&?).
               eapply HinclL.
               apply Partition_Permutation in Hpart. rewrite Hpart, IsLast_app.
               apply in_app_iff in Hin0 as [|]; simpl_In; [right|left]; econstructor; eauto; congruence. }

             eapply when_freel_wt; eauto.
             - rewrite 2 HasType_app. do 2 right. econstructor; solve_In; eauto with datatypes. 1,2:auto.
             - rewrite HasType_app. eauto.
             - rewrite IsLast_app. eauto.
             - intros * Find. rewrite HasType_app. eauto.
             - simpl_app. rewrite app_assoc, HasType_app. left. erewrite map_map, map_ext; simpl_In; eauto.
               intros; destruct_conjs; auto.
             - take (In _ branches) and eapply In_InMembers, fst_InMembers in it;
                   rewrite H7 in it; apply in_seq in it as (?&?); auto.
             - eapply wt_clock_incl; [|eauto]. intros *. rewrite HasType_app; auto.
           }
        + simpl_Forall.
          eapply cond_eq_wt in H0; eauto using subclock_exp_wt.
          2:rewrite subclock_exp_typeof; auto.
          simpl_Forall. constructor.
          eapply wt_equation_incl in H0; eauto.
          1,2:intros *; unfold senv_of_tyck; simpl_app; erewrite app_assoc, map_map, map_ext; intros.
          rewrite HasType_app; eauto. 2:rewrite IsLast_app; eauto.
          1,2:intros; destruct_conjs; auto.

      - (* local *)
        constructor.
        eapply switch_scope_wt; eauto.
        intros; simpl in *.
        eapply mmap_values, Forall2_ignore1 in H18. simpl_Forall.
        eapply H; eauto. simpl_Forall; auto.
    Qed.

  End switch_block.

  Fact subclock_clock_idem : forall ck,
    subclock_clock Cbase (Env.empty ident) ck = ck.
  Proof.
    induction ck; simpl; auto.
    unfold rename_var. rewrite Env.gempty; simpl.
    f_equal; auto.
  Qed.

  Lemma switch_node_wt G1 G2 : forall n,
      wt_global G1 ->
      global_iface_incl G1 G2 ->
      wt_node G1 n ->
      wt_node G2 (switch_node n).
  Proof.
    intros * Hwt1 Heq Wc. inv Wc; subst Γ.
    pose proof (n_syn n) as Hsyn. inv Hsyn.
    econstructor; simpl; auto.
    1-3:unfold wt_clocks in *; simpl_Forall; eauto with ltyping.
    - eapply iface_incl_wt_block; eauto.
      eapply switch_block_wt in H2; eauto using node_NoDupMembers, node_NoDupLocals, surjective_pairing.
      + intros ? [Hin|Hin]; apply Env.Props.P.F.empty_in_iff in Hin; inv Hin.
      + intros ??? Hfind. rewrite Env.gempty in Hfind. congruence.
      + intros ??? Hfind. rewrite Env.gempty in Hfind. congruence.
      + simpl_Forall. simpl_In. simpl_Forall. auto.
      + constructor.
  Qed.

  Lemma switch_global_wt : forall G,
      wt_global G ->
      wt_global (switch_global G).
  Proof.
    intros [] (Hbool&Hwt). unfold wt_global, CommonTyping.wt_program in *; simpl.
    constructor; auto.
    induction nodes0; simpl; inv Hwt; auto with datatypes.
    destruct H1.
    constructor; [constructor|].
    - eapply switch_node_wt; eauto.
      + econstructor; eauto.
      + eapply iface_eq_iface_incl, switch_global_iface_eq.
    - rewrite Forall_map. eapply Forall_impl; [|eapply H0]; intros.
      simpl; eauto.
    - eapply IHnodes0; eauto.
  Qed.

End CSTYPING.

Module CSTypingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (CS  : CLOCKSWITCH Ids Op OpAux Cks Senv Syn)
       <: CSTYPING Ids Op OpAux Cks Senv Syn Typ CS.
  Include CSTYPING Ids Op OpAux Cks Senv Syn Typ CS.
End CSTypingFun.
