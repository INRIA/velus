From Coq Require Import List Permutation.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping.
From Velus Require Import Lustre.Complete.Complete.

Module Type COMPTYPING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import Comp: COMPLETE Ids Op OpAux Cks Senv Syn).

  Section complete_node_wt.
    Variable G1 : @global (fun _ _ => True) elab_prefs.
    Variable G2 : @global complete elab_prefs.

    Hypothesis Iface : global_iface_incl G1 G2.

    Lemma local_env : forall env Γ (locs: list decl),
        NoDupMembers locs ->
        (forall x : ident, InMembers x locs -> ~ In x (map fst Γ)) ->
        (forall x ty, IsLast Γ x -> HasType Γ x ty -> Env.find x env = Some ty) ->
        (forall x ty,
            IsLast (Γ ++ senv_of_decls locs) x ->
            HasType (Γ ++ senv_of_decls locs) x ty ->
            Env.find x
              (Env.adds' (map_filter (fun '(x0, (ty0, _, _, o)) => if isSome o then Some (x0, ty0) else None) locs)
                 env) = Some ty).
    Proof.
      intros * ND1 ND Env * L Ty. simpl_In.
      destruct L as [L|L]; destruct Ty as [Ty|Ty].
      - rewrite Env.gsso'; eauto.
        intros contra. simpl_In. cases; inv Hf. inv L.
        eapply ND; eauto using In_InMembers. solve_In.
      - exfalso. inv L. inv Ty. simpl_In.
        eapply ND; eauto using In_InMembers. solve_In.
      - exfalso. inv L. inv Ty. simpl_In.
        eapply ND; eauto using In_InMembers. solve_In.
      - inv L. inv Ty. simpl_In.
        eapply NoDupMembers_det in Hin0; eauto. inv Hin0. destruct o0; simpl in *; try congruence.
        erewrite Env.In_find_adds'; eauto. 2:solve_In; simpl; eauto.
        apply NoDupMembers_map_filter; auto.
        intros; destruct_conjs; auto. destruct o as [(?&?)|]; simpl; auto.
    Qed.

    Lemma complete_block_wt : forall blk env Γ xs,
        (forall x ty, IsLast Γ x -> HasType Γ x ty -> Env.find x env = Some ty) ->
        VarsDefined blk xs ->
        incl xs Γ ->
        NoDupLocals (map fst Γ) blk ->
        wt_block G1 Γ blk ->
        wt_block G2 Γ (complete_block env blk).
    Proof.
      induction blk using block_ind2; intros * Env VD Incl ND Wt;
        assert (VD':=VD); inv VD'; assert (ND':=ND); inv ND'; assert (Wt':=Wt); inv Wt'.
      - (* equation *)
        constructor; eauto with ltyping.

      - (* reset *)
        constructor; eauto with ltyping.
        simpl_Forall. inv_VarsDefined.
        eapply H; eauto. etransitivity; eauto using incl_concat.

      - (* switch *)
        econstructor; eauto with ltyping.
        1:{ destruct Iface as (?&_); eauto. }
        1:{ erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto. }
        1:{ contradict H7. now apply map_eq_nil in H7. }
        simpl_Forall. repeat (Syn.inv_branch || inv_branch).
        assert (incl ys' Γ) as Incl1.
        { etransitivity; [|eauto]. take (Permutation _ xs) and rewrite <-it. solve_incl_app. }
        assert (incl ysl Γ) as Incl2.
        { etransitivity; [|apply Incl]. take (Permutation _ xs) and rewrite <-it. solve_incl_app. }
        simpl. econstructor. apply Forall_app; split.
        + simpl_Forall.
          assert (IsVar ysl x0) as V.
          { apply In_PS_elements, PS.diff_spec in H4 as (In&nIn).
            eapply vars_defined_Is_defined_in with (blk:=Bswitch ec _), VarsDefined_Is_defined' in In;
              eauto using NoDupLocals_incl, incl_map.
            rewrite map_vars_defined_spec, <-Exists_VarsDefined_spec in nIn; eauto.
            2:{ simpl_Forall. eapply NoDupLocals_incl; [|eauto].
                apply incl_map.
                take (Permutation (concat x) _) and now rewrite it. }
            constructor. take (Permutation _ xs) and rewrite <-it in In.
            apply InMembers_app in In as [In|]; auto.
            take (Permutation _ ys') and rewrite <-it in In. contradiction.
          }
          eapply H10, IsLast_incl in V; [|eauto]. inversion V; subst.
          erewrite Env; eauto with senv.
          repeat constructor; eauto with senv.
        + simpl_Forall. inv_VarsDefined.
          eapply H; eauto.
          * etransitivity; eauto using incl_concat.
            take (Permutation (concat x) _) and now rewrite it.

      - (* automaton (weak) *)
        econstructor; eauto with ltyping.
        1:{ simpl_Forall. split; [|split]; eauto with ltyping.
            erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto. }
        1:{ erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto. }
        1:{ erewrite map_length, map_map with (l:=states), map_ext with (l:=states); eauto.
            intros; destruct_conjs; auto. }
        1:{ erewrite map_map with (l:=states), map_ext with (l:=states); eauto.
            intros; destruct_conjs; auto. }
        1:{ contradict H14. now apply map_eq_nil in H14. }
        simpl_Forall. repeat (Syn.inv_branch || inv_branch). repeat (Syn.inv_scope || inv_scope).
        econstructor. split; auto.
        assert (incl ys' Γ) as Incl1.
        { etransitivity; [|eauto]. take (Permutation _ xs) and rewrite <-it. solve_incl_app. }
        assert (incl ysl Γ) as Incl2.
        { etransitivity; [|apply Incl]. take (Permutation _ xs) and rewrite <-it. solve_incl_app. }
        econstructor; eauto. 4:split.
        1:{ unfold wt_clocks in *. simpl_Forall. eauto with ltyping. }
        1:{ simpl_Forall. eauto with ltyping. }
        1:{ simpl_Forall. destruct o as [(?&?)|]; simpl in *; auto.
            destruct_conjs; split; eauto with ltyping. }
        2:{ simpl_Forall. split; [|split]; eauto with ltyping.
            erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto. }
        apply Forall_app; split.
        + simpl_Forall.
           assert (IsVar ysl x0) as V.
          { apply In_PS_elements, PS.diff_spec in H16 as (In&nIn).
            eapply vars_defined_Is_defined_in with (blk:=Bauto Weak ck (ini0, oth) _), VarsDefined_Is_defined' in In;
              eauto using NoDupLocals_incl, incl_map.
            rewrite PS.filter_spec, map_vars_defined_spec, <-Exists_VarsDefined_spec, Bool.negb_true_iff, mem_assoc_ident_false_iff in nIn; eauto.
            2:{ simpl_Forall. eapply NoDupLocals_incl; [|eauto].
                take (Permutation (concat x) _) and rewrite it, map_app, map_fst_senv_of_decls.
                apply incl_appl', incl_map; eauto. }
            2:{ intros ?? Eq. now inv Eq. }
            constructor. take (Permutation _ xs) and rewrite <-it in In.
            apply InMembers_app in In as [In|]; auto.
            exfalso. apply nIn. split.
            - take (Permutation (concat x) _) and rewrite it. apply InMembers_app; auto.
            - intros ?. eapply H22; eauto.
              eapply incl_map; [|eapply fst_InMembers; eauto]. eauto.
          }
          eapply H3, IsLast_incl in V; [|eauto]. inversion V; subst.
          erewrite Env; eauto with senv.
          repeat constructor; eauto with senv. 1-3:autorewrite with list; eauto with senv.
        + simpl_Forall. inv_VarsDefined.
          eapply H; eauto.
          * eapply local_env; eauto.
          * etransitivity; eauto using incl_concat.
            take (Permutation _ _) and rewrite it. eauto using incl_appl'.
          * now rewrite map_app, map_fst_senv_of_decls.

      - (* automaton (strong) *)
        econstructor; eauto with ltyping.
        1:{ erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto. }
        1:{ erewrite map_length, map_map with (l:=states), map_ext with (l:=states); eauto.
            intros; destruct_conjs; auto. }
        1:{ erewrite map_map with (l:=states), map_ext with (l:=states); eauto.
            intros; destruct_conjs; auto. }
        1:{ contradict H14. now apply map_eq_nil in H14. }
        simpl_Forall. repeat (Syn.inv_branch || inv_branch). repeat (Syn.inv_scope || inv_scope).
        econstructor. split; auto.
        1:{ simpl_Forall. split; [|split]; eauto with ltyping.
            erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto. }
        assert (incl ys' Γ) as Incl1.
        { etransitivity; [|eauto]. take (Permutation _ xs) and rewrite <-it. solve_incl_app. }
        assert (incl ysl Γ) as Incl2.
        { etransitivity; [|apply Incl]. take (Permutation _ xs) and rewrite <-it. solve_incl_app. }
        econstructor; eauto. 4:split; auto.
        1:{ unfold wt_clocks in *. simpl_Forall. eauto with ltyping. }
        1:{ simpl_Forall. eauto with ltyping. }
        1:{ simpl_Forall. destruct o as [(?&?)|]; simpl in *; auto.
            destruct_conjs; split; eauto with ltyping. }
        apply Forall_app; split.
        + simpl_Forall.
           assert (IsVar ysl x0) as V.
          { apply In_PS_elements, PS.diff_spec in H15 as (In&nIn).
            eapply vars_defined_Is_defined_in with (blk:=Bauto Strong ck ([], oth) _), VarsDefined_Is_defined' in In;
              eauto using NoDupLocals_incl, incl_map.
            rewrite PS.filter_spec, map_vars_defined_spec, <-Exists_VarsDefined_spec, Bool.negb_true_iff, mem_assoc_ident_false_iff in nIn; eauto.
            2:{ simpl_Forall. eapply NoDupLocals_incl; [|eauto].
                take (Permutation (concat x) _) and rewrite it, map_app, map_fst_senv_of_decls.
                apply incl_appl', incl_map; eauto. }
            2:{ intros ?? Eq. now inv Eq. }
            constructor. take (Permutation _ xs) and rewrite <-it in In.
            apply InMembers_app in In as [In|]; auto.
            exfalso. apply nIn. split.
            - take (Permutation (concat x) _) and rewrite it. apply InMembers_app; auto.
            - intros ?. eapply H22; eauto.
              eapply incl_map; [|eapply fst_InMembers; eauto]. eauto.
          }
          eapply H3, IsLast_incl in V; [|eauto]. inversion V; subst.
          erewrite Env; eauto with senv.
          repeat constructor; eauto with senv. 1-3:autorewrite with list; eauto with senv.
        + simpl_Forall. inv_VarsDefined.
          eapply H; eauto.
          * eapply local_env; eauto.
          * etransitivity; eauto using incl_concat.
            take (Permutation _ _) and rewrite it. eauto using incl_appl'.
          * now rewrite map_app, map_fst_senv_of_decls.

      - (* scope *)
        repeat (Syn.inv_scope || inv_scope).
        do 2 econstructor.
        + unfold wt_clocks in *. simpl_Forall. eauto with ltyping.
        + simpl_Forall. eauto using iface_incl_wt_type.
        + simpl_Forall. destruct o as [(?&?)|]; simpl in *; auto.
          destruct_conjs; split; eauto with ltyping.
        + simpl_Forall. inv_VarsDefined.
          eapply H; eauto using incl_appl', local_env.
          * etransitivity; eauto using incl_concat.
            take (Permutation (concat x) _) and rewrite it. eauto using incl_appl'.
          * now rewrite map_app, map_fst_senv_of_decls.
    Qed.
    
    Lemma complete_node_wt : forall (n : @node _ _),
        wt_node G1 n ->
        wt_node G2 (complete_node n).
    Proof.
      intros * Wt. inversion_clear Wt as [??? Wt1 Wt2 Wt3 Wt4]. subst Γ.
      pose proof (n_defd n) as (?&Vars&Perm).
      repeat econstructor; simpl; eauto.
      1-4:unfold wt_clocks, senv_of_decls in *; simpl_Forall; eauto with ltyping.
      - destruct o as [(?&?)|]; simpl in *; destruct_conjs; auto. split; eauto with ltyping.
      - eapply complete_block_wt; eauto.
        + intros * L Ty. inv L. inv Ty.
          eapply NoDupMembers_det in H0; eauto using node_NoDupMembers. subst.
          apply in_app_iff in H2 as [In|In]; simpl_In. congruence.
          destruct o as [(?&?)|]; simpl in *; try congruence.
          erewrite Env.find_In_from_list; eauto.
          * solve_In.
          * apply NoDupMembers_map_filter; eauto.
            2:apply NoDupMembers_senv_of_decls; eauto using node_NoDupMembers, NoDupMembers_app_r.
            intros; destruct_conjs. destruct o as [(?&?)|]; simpl; auto.
        + rewrite Perm. solve_incl_app.
        + apply node_NoDupLocals.
    Qed.
  End complete_node_wt.

  Theorem complete_global_wt : forall G,
      wt_global G ->
      wt_global (complete_global G).
  Proof.
    unfold wt_global, complete_global.
    intros * (?&Hwt).
    split; auto.
    eapply CommonTyping.transform_units_wt_program; eauto.
    intros ?? Hwt'.
    eapply complete_node_wt; eauto. eapply iface_eq_iface_incl, complete_global_iface_eq.
  Qed.

End COMPTYPING.

Module CompTypingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Comp: COMPLETE Ids Op OpAux Cks Senv Syn)
       <: COMPTYPING Ids Op OpAux Cks Senv Syn Typ Comp.
  Include COMPTYPING Ids Op OpAux Cks Senv Syn Typ Comp.
End CompTypingFun.
