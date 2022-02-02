From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping.
From Velus Require Import Lustre.DeLast.DeLast.

Module Type DLTYPING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Clo : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import IL  : DELAST Ids Op OpAux Cks Senv Syn).

  Section rename.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Variable sub : Env.t ident.

    Section rename_in_exp.
      Variable Γ Γ' : static_env.

      Hypothesis Hvar : forall x ty, HasType Γ x ty -> HasType Γ' x ty.
      Hypothesis Hlast : forall x ty, HasType Γ x ty -> IsLast Γ x -> HasType Γ' (rename_in_var sub x) ty.

      Lemma rename_in_exp_typeof : forall e,
          typeof (rename_in_exp sub e) = typeof e.
      Proof.
        induction e using exp_ind2; destruct_conjs; simpl; auto.
      Qed.

      Corollary rename_in_exp_typesof : forall es,
          typesof (map (rename_in_exp sub) es) = typesof es.
      Proof.
        induction es; simpl; auto.
        f_equal; auto using rename_in_exp_typeof.
      Qed.

      Lemma rename_in_exp_wt : forall e,
          wt_exp G Γ e ->
          wt_exp G Γ' (rename_in_exp sub e).
      Proof.
        intros * Hwc; induction e using exp_ind2; inv Hwc; simpl;
          econstructor; eauto using in_or_app; simpl_Forall; eauto;
          match goal with
          | |- wt_clock _ _ _ => eapply wt_clock_incl; eauto
          | |- typeof _ = _ => rewrite rename_in_exp_typeof; auto
          | |- typesof _ = _ => rewrite rename_in_exp_typesof; auto
          | |- context [map fst (map _ _)] =>
              erewrite map_map, map_ext; eauto; intros; destruct_conjs; auto
          | _ => idtac
          end.
        - intros contra. apply map_eq_nil in contra; subst. contradiction.
        - intros contra. apply map_eq_nil in contra; subst. contradiction.
        - erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; eauto.
          intros; destruct_conjs; auto.
        - intros contra. apply map_eq_nil in contra; subst. contradiction.
        - rewrite rename_in_exp_typesof; auto.
      Qed.

      Lemma rename_in_equation_wt : forall eq,
          wt_equation G Γ eq ->
          wt_equation G Γ' (rename_in_equation sub eq).
      Proof.
        intros (?&?) (Hwt1&Hwt2).
        simpl. constructor.
        - rewrite Forall_map. eapply Forall_impl; eauto using rename_in_exp_wt.
        - rewrite rename_in_exp_typesof; auto.
          simpl_Forall; auto using in_or_app.
      Qed.

    End rename_in_exp.

  End rename.

  Import Fresh Facts Tactics.

  Lemma delast_block_wt {PSyn prefs} (G: @global PSyn prefs) : forall blk sub Γ Γ' blk' st st',
      (forall x ty, HasType Γ x ty -> HasType Γ' x ty) ->
      (forall x ty, HasType Γ x ty -> IsLast Γ x -> HasType Γ' (rename_in_var sub x) ty) ->
      (forall x, Env.In x sub -> IsLast Γ x) ->
      NoDupLocals (map fst Γ) blk ->
      wt_block G Γ blk ->
      delast_block sub blk st = (blk', st') ->
      wt_block G Γ' blk'.
  Proof.
    induction blk using block_ind2; intros * Hvar Hlast Hsubin Hnd Hwt Hdl;
      inv Hnd; inv Hwt; repeat inv_bind.

    - (* equation *)
      constructor.
      eapply rename_in_equation_wt; eauto.

    - (* reset *)
      constructor.
      + eapply mmap_values, Forall2_ignore1 in H0; eauto.
        simpl_Forall; eauto.
      + eapply rename_in_exp_wt; eauto.
      + now rewrite rename_in_exp_typeof.

    - (* switch *)
      econstructor; eauto.
      + eapply rename_in_exp_wt; eauto.
      + now rewrite rename_in_exp_typeof.
      + assert (map fst x = map fst branches) as Heq. 2:setoid_rewrite Heq; auto.
        apply mmap_values in H0. clear - H0.
        induction H0; destruct_conjs; simpl; auto; repeat inv_bind. auto.
      + apply mmap_values in H0. inv H0; auto. congruence.
      + eapply mmap_values, Forall2_ignore1 in H0; eauto.
        simpl_Forall; eauto. repeat inv_bind.
        eapply mmap_values, Forall2_ignore1 in H7; eauto.
        simpl_Forall; eauto.

    - (* local *)
      assert (forall y, Env.In y (Env.from_list (map fst x)) -> IsLast (senv_of_locs locs) y) as Hsubin'.
      { intros *. rewrite Env.In_from_list.
        eapply fresh_idents_InMembers in H0. erewrite <-H0, fst_InMembers.
        intros; simpl_In. econstructor; solve_In. simpl. congruence. }
      assert (forall x2 ty,
                 HasType (Γ ++ senv_of_locs locs) x2 ty ->
                 HasType
                   (Γ' ++ @senv_of_locs exp
                       (map (fun '(x3, (ty0, ck, cx, _)) => (x3, (ty0, ck, cx, None))) locs ++
                            map (fun '(_, lx, (ty0, ck, _)) => (lx, (ty0, ck, 1%positive, None))) x)) x2 ty) as Hvar'.
      { intros *. rewrite 2 HasType_app. intros [|Hty]; auto.
        right. inv Hty; simpl_In.
        econstructor. solve_In. 2:apply in_app_iff, or_introl; solve_In.
        1,2:eauto.
      }
      assert (forall x2 ty,
                 HasType (Γ ++ senv_of_locs locs) x2 ty ->
                 IsLast (Γ ++ senv_of_locs locs) x2 ->
                 HasType
                   (Γ' ++
                       @senv_of_locs exp
                       (map (fun '(x3, (ty0, ck, cx, _)) => (x3, (ty0, ck, cx, None))) locs ++
                            map (fun '(_, lx, (ty0, ck, _)) => (lx, (ty0, ck, 1%positive, None))) x))
                   (rename_in_var (Env.union sub (Env.from_list (map fst x))) x2) ty) as Hlast'.
      { intros *. rewrite 2 HasType_app, IsLast_app.
        intros [Hty|Hty] [Hl|Hl]; eauto.
        - left. rewrite not_in_union_rename2; eauto.
          intro contra. apply Hsubin' in contra.
          inv Hl. inv contra. simpl_In.
          eapply H5; eauto using In_InMembers. solve_In.
        - exfalso.
          inv Hty. inv Hl. simpl_In.
          eapply H5; eauto using In_InMembers. solve_In.
        - exfalso.
          inv Hty. inv Hl. simpl_In.
          eapply H5; eauto using In_InMembers. solve_In.
        - right. simpl_app. apply HasType_app. right.
          inv Hty. inv Hl. simpl_In. eapply NoDupMembers_det in Hin0; eauto; inv_equalities.
          destruct o0 as [(?&?)|]; simpl in *; try congruence.
          eapply fresh_idents_In_rename in H0. 3:solve_In; simpl; auto.
          2:{ apply nodupmembers_map_filter; auto. intros; destruct_conjs; auto.
              destruct o as [(?&?)|]; simpl in *; auto. }
          econstructor. solve_In. rewrite not_in_union_rename1; eauto. 2:reflexivity.
          intro contra. apply Hsubin in contra.
          inv contra. eapply H5; eauto using In_InMembers. solve_In.
      }
      econstructor; eauto. rewrite Forall_app; split.
      + simpl_Forall. repeat constructor; simpl.
        * eapply fresh_idents_In' in H3; eauto. simpl_In. simpl_Forall.
          eapply rename_in_exp_wt in H3; eauto.
        * eapply fresh_idents_In' in H3; eauto. simpl_In.
          econstructor. simpl_app. repeat rewrite in_app_iff. right; left; solve_In. auto.
        * eapply fresh_idents_In' in H3; eauto. simpl_In.
          eapply Forall_forall in H7; [|solve_In]; simpl in *.
          eapply wt_clock_incl; eauto.
        * rewrite rename_in_exp_typeof, app_nil_r.
          eapply fresh_idents_In' in H3; eauto. simpl_In. simpl_Forall. auto.
        * eapply fresh_idents_In' in H3; eauto. simpl_In.
          eapply Forall_forall in H7; [|solve_In]; simpl in *.
          eapply wt_clock_incl; eauto.
        * simpl_app. repeat rewrite HasType_app. right; right. econstructor; solve_In. auto.
      + eapply mmap_values(* _valid *), Forall2_ignore1 in H1; eauto.
        simpl_Forall.
        eapply H; eauto.
        * intros * Hin. rewrite IsLast_app. apply Env.union_In in Hin as [|]; eauto.
        * rewrite map_app, map_fst_senv_of_locs; auto.
      + simpl_app. unfold wt_clocks in *. apply Forall_app; split; auto.
        * simpl_Forall. eapply wt_clock_incl; eauto.
        * eapply mmap_values, Forall2_ignore1 in H0; simpl_Forall.
          repeat inv_bind. simpl_In.
          simpl_Forall. eapply wt_clock_incl; eauto.
      + simpl_app. apply Forall_app; split; auto.
        * simpl_Forall; auto.
        * eapply mmap_values, Forall2_ignore1 in H0; simpl_Forall.
          repeat inv_bind. simpl_In.
          simpl_Forall; eauto.
      + apply Forall_app; split; simpl_Forall; auto.
  Qed.

  (** Typing of the node *)

  Lemma delast_node_wt : forall G1 G2 (n : @node _ _),
      global_iface_eq G1 G2 ->
      wt_node G1 n ->
      wt_node G2 (delast_node n).
  Proof.
    intros * Hiface (Hwt1&Hwt2&Hwt3&Hwt4).
    pose proof (n_nodup n) as (_&Hnd2).
    pose proof (n_good n) as (_&Hgood&_).
    pose proof (n_syn n) as Hsyn.
    repeat econstructor; simpl; eauto.
    1,2:destruct Hiface as (Heq&_); rewrite <-Heq; auto.
    - eapply Forall_impl; [|eauto]; intros; eauto using iface_eq_wt_enum.
    - eapply delast_block_wt in Hwt4. 6:apply surjective_pairing.
      + eapply iface_eq_wt_block, Hwt4; eauto.
      + auto.
      + intros * _ Hl. apply senv_of_inout_NoLast in Hl as [].
      + intros. rewrite Env.Props.P.F.empty_in_iff in H. inv H.
      + rewrite map_fst_senv_of_inout; auto.
  Qed.

  Theorem delast_global_wt : forall G,
      wt_global G ->
      wt_global (delast_global G).
  Proof.
    unfold wt_global, delast_global.
    intros * (?&Hwt).
    split; auto.
    eapply CommonTyping.transform_units_wt_program; eauto.
    intros ?? Hwt'.
    eapply delast_node_wt; eauto. eapply delast_global_iface_eq.
  Qed.

End DLTYPING.

Module DLTypingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LTYPING Ids Op OpAux Cks Senv Syn)
       (IL  : DELAST Ids Op OpAux Cks Senv Syn)
       <: DLTYPING Ids Op OpAux Cks Senv Syn Clo IL.
  Include DLTYPING Ids Op OpAux Cks Senv Syn Clo IL.
End DLTypingFun.
