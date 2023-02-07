From Coq Require Import List Permutation.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LClocking.
From Velus Require Import Lustre.Complete.Complete.

Module Type COMPCLOCKING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import Comp: COMPLETE Ids Op OpAux Cks Senv Syn).

  Fact HasClock_idck_incl : forall Γ1 Γ2,
      (forall x ck, HasClock Γ1 x ck -> HasClock Γ2 x ck) ->
      incl (idck Γ1) (idck Γ2).
  Proof.
    intros * InclCk ? In.
    unfold idck in *. simpl_In.
    assert (HasClock Γ2 i0 a0.(clo)) as Ck by eauto with senv.
    inv Ck. solve_In. congruence.
  Qed.

  Section complete_node_wc.
    Variable G1 : @global (fun _ _ => True) elab_prefs.
    Variable G2 : @global complete elab_prefs.

    Hypothesis Iface : global_iface_incl G1 G2.

    Lemma complete_block_wc : forall blk env Γ xs,
        (* (forall x ty, IsLast Γ x -> HasType Γ x ty -> exists ck, Env.find x env = Some (ty, ck)) -> *)
        VarsDefined blk xs ->
        NoDupMembers Γ ->
        (forall x, IsVar xs x -> IsVar Γ x) ->
        (forall x, IsLast xs x -> IsLast Γ x) ->
        NoDupLocals (map fst Γ) blk ->
        wc_block G1 Γ blk ->
        wc_block G2 Γ (complete_block env blk).
    Proof.
      induction blk using block_ind2; intros * (* Env  *)VD ND1 InclV InclL ND Wc;
        assert (VD':=VD); inv VD'; assert (ND':=ND); inv ND'; assert (Wc':=Wc); inv Wc'.
      - (* equation *)
        constructor; eauto with lclocking.

      - (* reset *)
        econstructor; eauto with lclocking.
        simpl_Forall. inv_VarsDefined.
        eapply H; eauto.
        + intros. eapply InclV. eapply IsVar_incl; [|eauto]; eauto using incl_map, incl_concat.
        + intros. eapply InclL. eapply IsLast_incl; [|eauto]; eauto using incl_map, incl_concat.

      - (* switch *)
        eapply wc_Bswitch
          with (Γ':=map_filter (fun '(x, ann) => if ann.(clo) ==b ck then Some (x, ann_with_clock ann Cbase) else None) Γ);
          eauto with lclocking.
        1:{ contradict H7. now apply map_eq_nil in H7. }
        1:{ intros * Ck. inv Ck. simpl_In.
            cases_eqn Eq; try congruence. inv Hf.
            rewrite equiv_decb_equiv in Eq. inv Eq.
            split; auto. econstructor; eauto. }
        1:{ intros * L. inv L. simpl_In. cases. inv Hf.
            econstructor; eauto. }
        take (Forall (fun _ => wc_branch _ _) _) and rename it into Wc'. rewrite Forall_forall in Wc'.
        simpl_Forall. repeat (Syn.inv_branch || inv_branch).
        assert (incl (map fst ys') (map fst Γ)) as Incl1.
        { etransitivity; [|eauto using IsVar_incl_fst]. take (Permutation _ xs) and rewrite <-it. solve_incl_app. }
        assert (incl (map fst ysl) (map fst Γ)) as Incl2.
        { etransitivity; [|eapply IsVar_incl_fst; eauto]. take (Permutation _ xs) and rewrite <-it. solve_incl_app. }
        assert (forall x, IsLast ys' x -> IsLast Γ x) as InclL1.
        { intros * L. apply InclL. take (Permutation _ xs) and rewrite <-it. apply IsLast_app; auto. }
        assert (forall x, IsLast ysl x -> IsLast Γ x) as InclL2.
        { intros * L. apply InclL. take (Permutation _ xs) and rewrite <-it. apply IsLast_app; auto. }
        simpl. econstructor. apply Forall_app; split.
        + simpl_Forall.
          apply In_PS_elements, PS.diff_spec in H4 as (In&nIn).
          eapply vars_defined_Is_defined_in with (blk:=Bswitch ec _) in In.
          assert (IsVar ysl x0) as V.
          { eapply VarsDefined_Is_defined' in In; eauto using NoDupLocals_incl, incl_map, IsVar_incl_fst.
            rewrite map_vars_defined_spec, <-Exists_VarsDefined_spec in nIn; eauto.
            2:{ simpl_Forall. eapply NoDupLocals_incl; [|eauto].
                take (Permutation (concat x) _) and now rewrite it. }
            constructor. take (Permutation _ xs) and rewrite <-it in In.
            apply InMembers_app in In as [In|]; auto.
            take (Permutation _ ys') and rewrite <-it in In. contradiction.
          }
          eapply H10, InclL2 in V. inversion_clear V as [??? InL Caus].
          assert (IsVar Γ' x0) as V'.
          { inv In. simpl_Exists. repeat Syn.inv_branch.
            simpl_Exists. specialize (Wc' _ Hin). inv_branch. simpl_Forall.
            take (Is_defined_in _ _) and eapply wc_block_Is_defined_in in it; eauto with senv. }
          inv V'. simpl_In. edestruct H9 as (Ck&Base); eauto with senv.
          inversion_clear Ck as [???? InCk]; subst.
          eapply NoDupMembers_det in InL; eauto. subst.
          repeat constructor; simpl; eauto with senv.
          1-3:clear - InCk Caus Base; econstructor; solve_In; simpl.
          all:try rewrite equiv_decb_refl; eauto.
        + apply Forall_forall in Wc'. simpl_Forall. inv_VarsDefined.
          repeat inv_branch. simpl_Forall.
          assert (NoDupLocals (map fst xs0) x0) as NDL.
          { eapply NoDupLocals_incl; [|eauto].
            etransitivity; [|eapply Incl1]. take (Permutation _ ys') and rewrite <-it.
            eauto using incl_map, incl_concat. }
          eapply H; eauto.
          * apply NoDupMembers_map_filter; auto.
            intros. cases; simpl; auto.
          * intros * V. inv V.
            eapply VarsDefined_Is_defined in Hdef; eauto.
            eapply wc_block_Is_defined_in in Hdef; eauto.
            simpl_In. edestruct H9 as (Ck&?); eauto with senv; subst.
            clear - Ck. inv Ck. econstructor. solve_In. 2:rewrite equiv_decb_refl; eauto. auto.
          * intros * L. inv L.
            eapply VarsDefined_Is_defined in Hdef; eauto using In_InMembers.
            eapply wc_block_Is_defined_in in Hdef; eauto.
            simpl_In. edestruct H9 as (Ck&?); eauto with senv; subst.
            assert (IsLast Γ x1) as L'.
            { eapply InclL1. take (Permutation _ ys') and rewrite <-it.
              eapply IsLast_incl; eauto using incl_concat with senv. }
            clear - Ck L' ND1. inv Ck. inv L'. eapply NoDupMembers_det in H; eauto; subst.
            econstructor. solve_In. simpl. rewrite equiv_decb_refl; eauto. auto.
          * clear NDL. eapply NoDupLocals_incl; [|eauto].
            intros ? In. simpl_In. cases; inv Hf. solve_In.
          * eapply wc_block_incl; [| |eauto]; eauto using map_filter_clo_HasClock1, map_filter_clo_IsLast1.

      - (* automaton *)
        eapply wc_Bauto
          with (Γ':=map_filter (fun '(x, ann) => if ann.(clo) ==b ck then Some (x, ann_with_clock ann Cbase) else None) Γ);
          eauto with lclocking.
        1:{ contradict H9. now apply map_eq_nil in H9. }
        1:{ intros * Ck. inv Ck. simpl_In.
            cases_eqn Eq; try congruence. inv Hf.
            rewrite equiv_decb_equiv in Eq. inv Eq.
            split; auto. econstructor; eauto. }
        1:{ intros * L. inv L. simpl_In. cases. inv Hf.
            econstructor; eauto. }
        1:{ simpl_Forall. split; auto.
            eauto using wc_exp_incl, iface_incl_wc_exp, map_filter_clo_HasClock1, map_filter_clo_IsLast1. }
        take (Forall (fun _ => wc_branch _ _) _) and rename it into Wc'. assert (Wc'':=Wc'); rewrite Forall_forall in Wc'.
        simpl_Forall. repeat (Syn.inv_branch || inv_branch). repeat (Syn.inv_scope || inv_scope). subst Γ'0.
        econstructor. split; auto.
        1:{ simpl_Forall. split; auto.
            eauto using wc_exp_incl, iface_incl_wc_exp, map_filter_clo_HasClock1, map_filter_clo_IsLast1. }
        assert (incl (map fst ys') (map fst Γ)) as Incl1.
        { etransitivity; [|eauto using IsVar_incl_fst]. take (Permutation _ xs) and rewrite <-it. solve_incl_app. }
        assert (incl (map fst ysl) (map fst Γ)) as Incl2.
        { etransitivity; [|eapply IsVar_incl_fst; eauto]. take (Permutation _ xs) and rewrite <-it. solve_incl_app. }
        assert (forall x, IsLast ys' x -> IsLast Γ x) as InclL1.
        { intros * L. apply InclL. take (Permutation _ xs) and rewrite <-it. apply IsLast_app; auto. }
        assert (forall x, IsLast ysl x -> IsLast Γ x) as InclL2.
        { intros * L. apply InclL. take (Permutation _ xs) and rewrite <-it. apply IsLast_app; auto. }
        econstructor; eauto. 3:split.
        1:{ simpl_Forall. eapply wc_clock_incl; [|eauto].
            eapply HasClock_idck_incl. intros * Ck. rewrite HasClock_app in *.
            destruct Ck; eauto using map_filter_clo_HasClock1. }
        1:{ simpl_Forall. destruct o as [(?&?)|]; simpl in *; destruct_conjs; auto. split; auto.
            eapply wc_exp_incl; [| |eauto using iface_incl_wc_exp].
            1,2:intros * In; rewrite HasClock_app in *||rewrite IsLast_app in *;
            destruct In; eauto using map_filter_clo_HasClock1, map_filter_clo_IsLast1. }
        2:{ simpl_Forall. split; auto.
            eapply wc_exp_incl; [| |eauto using iface_incl_wc_exp].
            1,2:intros * In; rewrite HasClock_app in *||rewrite IsLast_app in *;
            destruct In; eauto using map_filter_clo_HasClock1, map_filter_clo_IsLast1. }
        apply Forall_app; split.
        + simpl_Forall.
          apply In_PS_elements, PS.diff_spec in H17 as (In&nIn).
          apply vars_defined_Is_defined_in with (blk:=Bauto type ck (ini0, oth) _) in In.
          assert (IsVar ysl x0) as V.
          { eapply VarsDefined_Is_defined' in In; eauto using NoDupLocals_incl, IsVar_incl_fst.
            rewrite PS.filter_spec, map_vars_defined_spec, <-Exists_VarsDefined_spec, Bool.negb_true_iff, mem_assoc_ident_false_iff in nIn; eauto.
            2:{ simpl_Forall. eapply NoDupLocals_incl; [|eauto].
                take (Permutation (concat x) _) and rewrite it, map_app, map_fst_senv_of_decls.
                apply incl_appl'; eauto. }
            2:{ intros ?? Eq. now inv Eq. }
            constructor. take (Permutation _ xs) and rewrite <-it in In.
            apply InMembers_app in In as [In|]; auto.
            exfalso. apply nIn. split.
            - take (Permutation (concat x) _) and rewrite it. apply InMembers_app; auto.
            - intros ?. eapply H22; eauto.
              now apply Incl1, fst_InMembers.
          }
          eapply H3, InclL2 in V. inversion_clear V as [??? InL Caus].
          assert (IsVar Γ' x0) as V'.
          { inv In. simpl_Exists. Syn.inv_branch.
            specialize (Wc' _ Hin). inv_branch. destruct s.
            take (Is_defined_in_scope _ _ _) and eapply wc_scope_Is_defined_in in it; eauto with senv.
            intros. destruct_conjs. eapply Exists_Is_defined_in_wx_In; [|eauto].
            simpl_Forall; eauto with lclocking.
          }
          inv V'. simpl_In. edestruct H11 as (Ck&Base); eauto with senv.
          inversion_clear Ck as [???? InCk]; subst.
          eapply NoDupMembers_det in InL; eauto. subst.
          repeat constructor; simpl; eauto with senv.
          1-3:clear - InCk Caus Base; apply HasClock_app||apply IsLast_app; left; econstructor; solve_In; simpl.
          all:try rewrite equiv_decb_refl; eauto.
        + simpl_Forall. inv_VarsDefined.
          assert (NoDupLocals (map fst xs0) x0) as NDL.
          { eapply NoDupLocals_incl; [|eauto].
            etransitivity; [eauto using incl_map, incl_concat|]. take (Permutation (concat _) _) and rewrite it.
            rewrite map_app, map_fst_senv_of_decls. now apply incl_appl'. }
          eapply H; eauto.
          * apply NoDupScope_NoDupMembers; eauto.
            -- apply NoDupMembers_map_filter; auto. intros. cases; simpl; auto.
            -- intros * In1 In2. simpl_In. cases; inv Hf.
               eapply H22; eauto using In_InMembers. solve_In.
          * intros * V. inv V. apply IsVar_app.
            eapply VarsDefined_Is_defined in Hdef; eauto.
            eapply wc_block_Is_defined_in, InMembers_app in Hdef as [Hdef|Hdef]; eauto.
            2:{ right. now constructor. }
            simpl_In. edestruct H11 as (Ck&?); eauto with senv; subst.
            clear - Ck. inv Ck. left. econstructor. solve_In. 2:rewrite equiv_decb_refl; eauto. auto.
          * intros * L. inversion_clear L as [??? InL Caus]. rewrite IsLast_app.
            eapply VarsDefined_Is_defined in Hdef; eauto using In_InMembers.
            eapply wc_block_Is_defined_in, InMembers_app in Hdef as [Hdef|Hdef]; eauto.
            2:{ eapply incl_concat in InL; [|eauto]. take (Permutation (concat x) _) and rewrite it in InL.
                apply in_app_iff in InL as [In|In].
                - exfalso. simpl_In. eapply H22; eauto using In_InMembers.
                  apply Incl1. solve_In.
                - right. clear - In Caus. econstructor; eauto. }
            simpl_In. edestruct H11 as (Ck&?); eauto with senv; subst.
            assert (IsLast Γ x1) as L'.
            { eapply InclL1. eapply incl_concat in InL; eauto. take (Permutation (concat x) _) and rewrite it in InL.
              apply in_app_iff in InL as [InL|InL]; [econstructor; eauto|].
              exfalso. inv Ck. simpl_In. eapply H22; eauto using In_InMembers. solve_In. }
            clear - Ck L' ND1. inv Ck. inv L'. eapply NoDupMembers_det in H; eauto; subst.
            left. econstructor. solve_In. simpl. rewrite equiv_decb_refl; eauto. auto.
          * clear NDL. eapply NoDupLocals_incl; [|eauto].
            rewrite map_app, map_fst_senv_of_decls. apply incl_appl'.
            intros ? In. simpl_In. cases; inv Hf. solve_In.
          * eapply wc_block_incl; [| |eauto].
            1,2:intros * In; rewrite HasClock_app in *||rewrite IsLast_app in *;
            destruct In; eauto using map_filter_clo_HasClock1, map_filter_clo_IsLast1.

      - (* scope *)
        repeat (Syn.inv_scope || inv_scope). subst Γ'.
        do 2 econstructor; auto.
        + simpl_Forall. destruct o as [(?&?)|]; simpl in *; auto.
          destruct_conjs; split; eauto with lclocking.
        + simpl_Forall. inv_VarsDefined.
          eapply H; eauto using NoDupScope_NoDupMembers.
          * intros * In. eapply IsVar_incl in In; [|eauto using incl_concat].
            take (Permutation (concat x) _) and rewrite it in In. rewrite IsVar_app in *. destruct In; auto.
          * intros * In. eapply IsLast_incl in In; [|eauto using incl_concat].
            take (Permutation (concat x) _) and rewrite it in In. rewrite IsLast_app in *. destruct In; auto.
          * now rewrite map_app, map_fst_senv_of_decls.
    Qed.

    Lemma complete_node_wc : forall (n : @node _ _),
        wc_node G1 n ->
        wc_node G2 (complete_node n).
    Proof.
      intros * Wc. inversion_clear Wc as [??? Wc1 Wc2 Wc3]. subst Γ.
      pose proof (n_defd n) as (?&Vars&Perm).
      repeat econstructor; simpl; eauto.
      - simpl_Forall. destruct o as [(?&?)|]; simpl in *; destruct_conjs; auto. split; eauto with lclocking.
      - eapply complete_block_wc; eauto using node_NoDupMembers, node_NoDupLocals.
        1,2:intros *; rewrite Perm, ?IsVar_app, ?IsLast_app; auto.
    Qed.
  End complete_node_wc.

  Theorem complete_global_wc : forall G,
      wc_global G ->
      wc_global (complete_global G).
  Proof.
    unfold wc_global, complete_global.
    intros * Wc.
    eapply CommonTyping.transform_units_wt_program; eauto.
    intros ?? Hwc'.
    eapply complete_node_wc; eauto. eapply iface_eq_iface_incl, complete_global_iface_eq.
  Qed.


End COMPCLOCKING.

Module CompClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Comp: COMPLETE Ids Op OpAux Cks Senv Syn)
       <: COMPCLOCKING Ids Op OpAux Cks Senv Syn Clo Comp.
  Include COMPCLOCKING Ids Op OpAux Cks Senv Syn Clo Comp.
End CompClockingFun.
