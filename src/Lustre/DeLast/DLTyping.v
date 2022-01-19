From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.LSyntax Lustre.LTyping.
From Velus Require Import Lustre.DeLast.DeLast.

Module Type DLTYPING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (Import Clo : LTYPING Ids Op OpAux Cks Syn)
       (Import IL  : DELAST Ids Op OpAux Cks Syn).

  Lemma rename_in_sub : forall x y (ty : Op.type) sub xs,
      Env.find x sub = Some y ->
      In (x, ty) xs ->
      In (y, ty) (map (fun '(x, ty) => (rename_in_var sub x, ty)) xs).
  Proof.
    intros * Hfind Hin.
    solve_In.
    unfold rename_in_var. now rewrite Hfind.
  Qed.

  Lemma rename_in_nsub : forall x (ty : Op.type) sub xs,
      Env.find x sub = None ->
      In (x, ty) xs ->
      In (x, ty) (map (fun '(x, ty) => (rename_in_var sub x, ty)) xs).
  Proof.
    intros * Hfind Hin.
    solve_In.
    unfold rename_in_var. now rewrite Hfind.
  Qed.

  Section rename.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Variable sub : Env.t ident.

    Section rename_in_exp.
      Variable Γ Γl : list (ident * Op.type).

      Lemma rename_in_last_wt : forall x ty,
          In (x, ty) Γl ->
          In (rename_in_var sub x, ty) (map (fun '(x, ty) => (rename_in_var sub x, ty)) Γl).
      Proof.
        intros * Hin.
        unfold rename_in_var.
        destruct (Env.find _ _) eqn:Hfind; eauto using rename_in_sub, rename_in_nsub.
      Qed.

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
          wt_exp G Γ Γl e ->
          wt_exp G (Γ++map (fun '(x, ty) => (rename_in_var sub x, ty)) Γl) [] (rename_in_exp sub e).
      Proof.
        intros * Hwc; induction e using exp_ind2; inv Hwc; simpl;
          econstructor; eauto using in_or_app; simpl_Forall; eauto;
          match goal with
          | |- wt_clock _ (_ ++ _) _ => eapply wt_clock_incl; [|eauto]; apply incl_appl, incl_refl
          | |- typeof _ = _ => rewrite rename_in_exp_typeof; auto
          | |- typesof _ = _ => rewrite rename_in_exp_typesof; auto
          | |- context [map fst (map _ _)] =>
              erewrite map_map, map_ext; eauto; intros; destruct_conjs; auto
          | _ => idtac
          end.
        - apply in_or_app, or_intror. apply rename_in_last_wt; auto.
        - intros contra. apply map_eq_nil in contra; subst. contradiction.
        - intros contra. apply map_eq_nil in contra; subst. contradiction.
        - erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; eauto.
          intros; destruct_conjs; auto.
        - intros contra. apply map_eq_nil in contra; subst. contradiction.
        - rewrite rename_in_exp_typesof; auto.
      Qed.

      Lemma rename_in_equation_wt : forall eq,
          wt_equation G Γ Γl eq ->
          wt_equation G (Γ++map (fun '(x, ty) => (rename_in_var sub x, ty)) Γl) [] (rename_in_equation sub eq).
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

  Lemma delast_block_wt {PSyn prefs} (G: @global PSyn prefs) : forall blk sub Γ Γl blk' st st',
      (forall x, Env.In x sub -> InMembers x Γl) ->
      NoDupLocals (map fst Γl) blk ->
      wt_block G Γ Γl blk ->
      delast_block sub blk st = (blk', st') ->
      wt_block G (Γ++map (fun '(x, ty) => (rename_in_var sub x, ty)) Γl) [] blk'.
  Proof.
    induction blk using block_ind2; intros * Hsubin Hnd Hwt Hdl;
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
      assert (forall y, Env.In y (Env.from_list (map fst x)) <->
                   InMembers y (map_filter (fun '(x, (ty, ck, _, o)) => option_map (fun '(e, _) => (x, (ty, ck, e))) o) locs)) as Hsubin'.
      { intros. rewrite Env.In_from_list.
        eapply fresh_idents_InMembers in H0. erewrite H0, 2 fst_InMembers.
        split; intros; solve_In. }
      assert (incl
                ((Γ ++ map (fun '(x6, (ty, _, _, _)) => (x6, ty)) locs)
                   ++ map (fun '(x6, ty) => (rename_in_var (Env.union sub (Env.from_list (map fst x))) x6, ty)) (Γl ++ map_filter (fun '(x6, (ty, _, _, o)) => option_map (fun _ : exp * ident => (x6, ty)) o) locs))
                ((Γ ++ map (fun '(x6, ty) => (rename_in_var sub x6, ty)) Γl)
                   ++ map (fun '(x6, (ty, _, _, _)) => (x6, ty)) (map (fun '(x6, (ty, ck, cx, _)) => (x6, (ty, ck, cx, @None (exp * ident)))) locs ++ map (fun '(_, lx, (ty, ck, _)) => (lx, (ty, ck, 1%positive, None))) x))
             ) as Hincl.
      { simpl_app.
        apply incl_appr', incl_app;
          [apply incl_appr, incl_appl; erewrite map_map, map_ext; try reflexivity;
           intros; destruct_conjs; auto|].
        apply incl_app; [apply incl_appl|apply incl_appr, incl_appr].
        - intros ? Hin; solve_In. rewrite not_in_union_rename2; auto.
          erewrite Hsubin'. intros contra. apply fst_InMembers in contra. simpl_In.
          eapply H5; eauto using In_InMembers. solve_In.
        - intros ? Hin; simpl_In.
          assert (Hfresh:=H0). eapply fresh_idents_In in H0 as (?&Hin'). 2:solve_In; simpl; eauto.
          solve_In.
          rewrite not_in_union_rename1.
          2:{ intros Hsub. eapply H5; eauto using In_InMembers.
              rewrite <-fst_InMembers; eauto. }
          unfold rename_in_var. erewrite fresh_idents_sub; eauto. 3:solve_In. auto.
          apply nodupmembers_map_filter; auto. intros; destruct_conjs; destruct o as [(?&?)|]; simpl; auto.
      }
      econstructor; eauto. rewrite Forall_app; split.
      + rewrite map_filter_nil; simpl.
        2:{ apply Forall_app; split; simpl_Forall; auto. }
        simpl_Forall. repeat constructor; simpl.
        * eapply fresh_idents_In' in H3; eauto. simpl_In. simpl_Forall.
          eapply rename_in_exp_wt in H3. eapply wt_exp_incl; [|reflexivity|eauto]. eauto.
        * eapply fresh_idents_In' in H3; eauto. simpl_In.
          simpl_app. repeat rewrite in_app_iff. right; right; left; solve_In.
        * eapply fresh_idents_In' in H3; eauto. simpl_In.
          eapply Forall_forall in H8; [|solve_In]; simpl in *.
          eapply wt_clock_incl; [|eauto]. simpl_app.
          apply incl_appr', incl_appr, incl_appl.
          erewrite map_map, map_ext; try reflexivity. intros; destruct_conjs; auto.
        * rewrite rename_in_exp_typeof, app_nil_r.
          eapply fresh_idents_In' in H3; eauto. simpl_In. simpl_Forall. auto.
        * eapply fresh_idents_In' in H3; eauto. simpl_In.
          eapply Forall_forall in H8; [|solve_In]; simpl in *.
          eapply wt_clock_incl; [|eauto]. simpl_app.
          apply incl_appr', incl_appr, incl_appl.
          erewrite map_map, map_ext; try reflexivity. intros; destruct_conjs; auto.
        * simpl_app. repeat rewrite in_app_iff. right; right; right. solve_In.
      + eapply mmap_values(* _valid *), Forall2_ignore1 in H1; eauto.
        simpl_Forall.
        rewrite map_filter_nil.
        2:{ apply Forall_app; split; simpl_Forall; auto. }
        eapply H with (sub:=Env.union _ _) in H7; eauto.
        * eapply wt_block_incl; [|reflexivity|eauto]. eauto.
        * intros * Hin. rewrite InMembers_app. apply Env.union_In in Hin as [|Hin]; eauto.
          right.
          rewrite Hsubin' in Hin. rewrite fst_InMembers in Hin. rewrite fst_InMembers. solve_In. auto.
        * rewrite map_app. eapply NoDupLocals_incl; [|eauto].
          apply incl_appr'. intros ? Hin. solve_In.
      + simpl_app. unfold wt_clocks in *. apply Forall_app; split; auto.
        * simpl_Forall. eapply wt_clock_incl; [|eauto].
          apply incl_appr', incl_appr, incl_appl.
          erewrite map_map, map_ext; try reflexivity. intros; destruct_conjs; auto.
        * eapply mmap_values, Forall2_ignore1 in H0; simpl_Forall.
          repeat inv_bind. simpl_In.
          simpl_Forall. eapply wt_clock_incl; [|eauto].
          apply incl_appr', incl_appr, incl_appl.
          erewrite map_map, map_ext; try reflexivity. intros; destruct_conjs; auto.
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
    - eapply delast_block_wt in Hwt4. 4:apply surjective_pairing.
      + rewrite app_nil_r in Hwt4. eapply iface_eq_wt_block, Hwt4; eauto.
      + intros. rewrite Env.Props.P.F.empty_in_iff in H. inv H.
      + eapply NoDupLocals_incl; eauto. apply incl_nil'.
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
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (Clo : LTYPING Ids Op OpAux Cks Syn)
       (IL  : DELAST Ids Op OpAux Cks Syn)
       <: DLTYPING Ids Op OpAux Cks Syn Clo IL.
  Include DLTYPING Ids Op OpAux Cks Syn Clo IL.
End DLTypingFun.
