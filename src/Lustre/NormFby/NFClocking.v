From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LClocking.
From Velus Require Import Lustre.NormFby.NormFby.
From Velus Require Import Lustre.SubClock.SCClocking.

Module Type NFCLOCKING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import NF : NORMFBY Ids Op OpAux Cks Senv Syn).

  Import Fresh Fresh.Facts Fresh.Tactics.

  Module Import SCC := SCClockingFun Ids Op OpAux Cks Senv Syn Clo SC. Import SC.

  Fact fby_iteexp_clockof : forall e0 e ann es' eqs' st st',
      fby_iteexp e0 e ann st = (es', eqs', st') ->
      clockof es' = [(snd ann)].
  Proof.
    intros ?? [ty cl] es' eqs' st st' Hfby; simpl in *.
    destruct (is_constant e0); repeat inv_bind; reflexivity.
  Qed.

  (** ** Preservation of clocking through second pass *)

  Ltac solve_incl :=
    match goal with
    | H : wc_clock ?l1 ?cl |- wc_clock ?l2 ?cl =>
      eapply wc_clock_incl; [|eauto]; intros
    | H : wc_exp ?G ?l1 ?e |- wc_exp ?G ?l2 ?e =>
      eapply wc_exp_incl; [| |eauto]; intros
    | H : wc_equation ?G ?l1 ?eq |- wc_equation ?G ?l2 ?eq =>
      eapply wc_equation_incl; [| |eauto]; intros
    | H : wc_block ?G ?l1 ?eq |- wc_block ?G ?l2 ?eq =>
      eapply wc_block_incl; [| |eauto]; intros
    | H : In ?i ?l1 |- In ?i ?l2 =>
      assert (incl l1 l2) by repeat solve_incl; eauto
    | |- incl (st_anns ?st1) (st_anns _) =>
        eapply st_follows_incl; repeat solve_st_follows
    | |- incl ?l1 ?l1 => reflexivity
    | |- incl ?l1 (?l1 ++ ?l2) =>
      eapply incl_appl; reflexivity
    | |- incl (?l1 ++ ?l2) (?l1 ++ ?l3) => apply incl_appr'
    | |- incl ?l1 (?l2 ++ ?l3) => eapply incl_appr
    | |- incl ?l1 (?a::?l2) => eapply incl_tl
    | |- incl _ _ => apply incl_map
    | H : HasClock ?l1 ?x ?ty |- HasClock ?l2 ?x ?ty =>
        eapply HasClock_incl; [|eauto]
    | H : IsLast ?l1 ?x |- IsLast ?l2 ?x =>
        eapply IsLast_incl; [|eauto]
    end; auto.

  Section normfby_node_wc.
    Variable G1 : @global normlast last_prefs.
    Variable G2 : @global normalized fby_prefs.

    Hypothesis Hiface : global_iface_incl G1 G2.
    Local Hint Resolve iface_incl_wc_exp : norm.

    Fact fby_iteexp_wc_exp : forall vars e0 e ty ck e' eqs' st st' ,
        wc_exp G1 (vars++st_senv st) e0 ->
        wc_exp G1 (vars++st_senv st) e ->
        clockof e0 = [ck] ->
        clockof e = [ck] ->
        fby_iteexp e0 e (ty, ck) st = (e', eqs', st') ->
        wc_exp G2 (vars++st_senv st') e'.
    Proof with eauto with fresh.
      intros * Hwc1 Hwc2 Hck1 Hck2 Hfby.
      unfold fby_iteexp in Hfby; simpl in *.
      assert (st_follows st st') as Hfollows.
      { eapply (fby_iteexp_st_follows _ _ (ty, ck)) in Hfby; eauto. }
      repeat inv_bind.
      econstructor; repeat constructor; simpl; try congruence...
      1-5:try rewrite app_nil_r.
      - apply HasClock_app, or_intror.
        apply init_var_for_clock_In in H; simpl in *.
        eapply st_follows_incl in H... econstructor; solve_In. auto.
      - eapply iface_incl_wc_exp; eauto. repeat solve_incl.
      - apply HasClock_app, or_intror.
        eapply fresh_ident_In in H0... econstructor; solve_In; auto.
      - rewrite Hck1; auto.
      - now rewrite Hck1.
    Qed.

    Fact arrow_iteexp_wc_exp : forall vars e0 e ty ck e' eqs' st st' ,
        wc_exp G1 (vars++st_senv st) e0 ->
        wc_exp G1 (vars++st_senv st) e ->
        clockof e0 = [ck] ->
        clockof e = [ck] ->
        arrow_iteexp e0 e (ty, ck) st = (e', eqs', st') ->
        wc_exp G2 (vars++st_senv st') e'.
    Proof with eauto.
      intros * Hwc1 Hwc2 Hck1 Hck2 Hfby.
      unfold arrow_iteexp in Hfby; simpl in *; repeat inv_bind.
      assert (st_follows st st') as Hfollows by (eapply init_var_for_clock_st_follows; eauto).
      econstructor; repeat constructor; simpl; try congruence...
      1-7:try rewrite app_nil_r.
      4-7:try rewrite Hck1; try rewrite Hck2; auto.
      - apply HasClock_app, or_intror.
        apply init_var_for_clock_In in H; simpl in *.
        econstructor; solve_In. auto.
      - eapply iface_incl_wc_exp; eauto. repeat solve_incl.
      - eapply iface_incl_wc_exp; eauto. repeat solve_incl.
    Qed.

    Fact fresh_ident_wc_env : forall pref hint vars ty ck id (st st': fresh_st pref _),
        wc_env (idck (vars++st_senv st)) ->
        wc_clock (idck (vars++st_senv st)) ck ->
        fresh_ident hint (ty, ck) st = (id, st') ->
        wc_env (idck (vars++st_senv st')).
    Proof.
      intros * Hwenv Hwc Hfresh.
      apply fresh_ident_anns in Hfresh.
      unfold wc_env, st_senv, idck in *. rewrite Hfresh; simpl.
      rewrite <- Permutation.Permutation_middle.
      constructor; simpl.
      - repeat solve_incl.
      - eapply Forall_impl; [|eauto].
        intros; simpl in *. repeat solve_incl.
    Qed.

    Fact init_var_for_clock_wc_env : forall vars ck id eqs' st st' ,
        wc_env (idck (vars++st_senv st)) ->
        wc_clock (idck (vars++st_senv st)) ck ->
        init_var_for_clock ck st = (id, eqs', st') ->
        wc_env (idck (vars++st_senv st')).
    Proof with eauto.
      intros * Hwenv Hwc Hinit.
      unfold init_var_for_clock in Hinit.
      destruct fresh_ident eqn:Hfresh. inv Hinit.
      eapply fresh_ident_wc_env in Hfresh...
    Qed.

    Fact fby_iteexp_wc_env : forall vars e0 e ty ck es' eqs' st st' ,
        wc_env (idck (vars++st_senv st)) ->
        wc_clock (idck (vars++st_senv st)) ck ->
        fby_iteexp e0 e (ty, ck) st = (es', eqs', st') ->
        wc_env (idck (vars++st_senv st')).
    Proof with eauto.
      intros ???? ck es' eqs' st st' Hwenv Hwc Hfby.
      unfold fby_iteexp in Hfby; repeat inv_bind...
      eapply fresh_ident_wc_env in H0... 2:repeat solve_incl.
      eapply init_var_for_clock_wc_env in H... eapply init_var_for_clock_st_follows in H...
    Qed.

    Fact init_var_for_clock_wc_eq : forall vars ck id eqs' st st' ,
        wc_clock (idck (vars++st_senv st)) ck ->
        init_var_for_clock ck st = (id, eqs', st') ->
        Forall (wc_equation G2 (vars++st_senv st')) eqs'.
    Proof with eauto with norm lclocking.
      intros * Hwc Hinit.
      unfold init_var_for_clock in Hinit.
      destruct fresh_ident eqn:Hfresh; repeat inv_bind.
      simpl in *; repeat econstructor; simpl...
      1,2:apply add_whens_wc... 1-2:repeat solve_incl.
      1,2:rewrite app_nil_r, add_whens_clockof...
      apply fresh_ident_In in Hfresh.
      apply in_or_app; right.
      unfold st_senv, idck, idty;
        simpl_In; eexists; split; eauto; eauto. auto.
    Qed.

    Fact normalized_lexp_wc_exp_clockof : forall vars e,
        normalized_lexp e ->
        wc_env (idck vars) ->
        wc_exp G2 vars e ->
        Forall (wc_clock (idck vars)) (clockof e).
    Proof with eauto.
      intros vars e Hnormed Hwenv Hwc.
      induction Hnormed; inv Hwc; simpl; repeat constructor...
      - inv H0. eapply Forall_forall in Hwenv; eauto. 2:solve_In. auto.
      - inv H1. eapply Forall_forall in Hwenv; eauto. 2:solve_In. auto.
      - eapply IHHnormed in H1. rewrite H4 in H1. inv H1...
      - eapply IHHnormed1 in H3. rewrite H6 in H3. inv H3...
      - apply Forall_singl in H5.
        eapply IHHnormed in H5.
        simpl in H7. rewrite app_nil_r in H7. symmetry in H7.
        singleton_length.
        inv H6. inv H5...
      - inv H3. solve_In.
    Qed.

    Fact fby_iteexp_wc_eq : forall vars e0 e ty ck e' eqs' st st' ,
        normalized_lexp e0 ->
        wc_env (idck (vars++st_senv st)) ->
        wc_exp G1 (vars++st_senv st) e0 ->
        wc_exp G1 (vars++st_senv st) e ->
        clockof e0 = [ck] ->
        clockof e = [ck] ->
        fby_iteexp e0 e (ty, ck) st = (e', eqs', st') ->
        Forall (wc_equation G2 (vars++st_senv st')) eqs'.
    Proof with eauto with norm lclocking.
      intros * Hnormed Henv Hwc1 Hwc2 Hcl1 Hcl2 Hfby.
      assert (wc_clock (idck (vars++st_senv st)) ck) as Hwck.
      { eapply iface_incl_wc_exp, normalized_lexp_wc_exp_clockof in Hwc1...
        rewrite Hcl1 in Hwc1; inv Hwc1; auto. }
      unfold fby_iteexp in Hfby; simpl in *.
      repeat inv_bind; repeat constructor; simpl...
      - eapply add_whens_wc...
        2,3:destruct ty; simpl...
        eapply init_var_for_clock_st_follows in H. repeat solve_incl.
      - eapply init_var_for_clock_st_follows in H.
        eapply iface_incl_wc_exp; eauto. repeat solve_incl.
      - rewrite app_nil_r, add_whens_clockof...
        destruct ty; simpl...
      - rewrite app_nil_r. rewrite Hcl2...
      - eapply fresh_ident_In in H0.
        apply HasClock_app; right. econstructor; solve_In. auto.
      - eapply init_var_for_clock_wc_eq in H...
        simpl_Forall; repeat solve_incl.
    Qed.

    Fact normfby_equation_wc lasts : forall vars to_cut eq eqs' st st' ,
        unnested_equation lasts eq ->
        wc_env (idck (vars++st_senv st)) ->
        wc_equation G1 (vars++st_senv st) eq ->
        normfby_equation to_cut eq st = (eqs', st') ->
        (Forall (wc_equation G2 (vars++st_senv st')) eqs' /\ wc_env (idck (vars++st_senv st'))).
    Proof with eauto.
      intros * Hunt Hwenv Hwc Hfby.
      inv_normfby_equation Hfby to_cut eq; try destruct x2 as [ty ck].
      - (* fby (constant) *)
        destruct PS.mem; repeat inv_bind; auto.
        2:{ split; auto. inv Hwc.
            do 2 constructor; auto.
            simpl_Forall; eauto with lclocking. }
        inv Hwc. rename H2 into Hwc. rename H3 into Hins.
        apply Forall_singl in Hwc. apply Forall2_singl in Hins.
        assert (Hwc':=Hwc). inv Hwc'.
        apply Forall_singl in H3; apply Forall_singl in H4.
        assert (wc_clock (idck (vars ++ st_senv st)) ck).
        { inv Hins. eapply wc_env_var; eauto. solve_In. }
        repeat (constructor; eauto).
        + eapply fresh_ident_In in H.
          eapply HasClock_app, or_intror. econstructor; solve_In. auto.
        + repeat solve_incl.
        + eapply iface_incl_wc_exp... repeat solve_incl.
        + eapply iface_incl_wc_exp... repeat solve_incl.
        + eapply fresh_ident_In in H.
          eapply HasClock_app, or_intror. econstructor; solve_In. auto.
        + eapply fresh_ident_wc_env in H; eauto.
      - (* fby *)
        assert (st_follows st st') as Hfollows by (eapply fby_iteexp_st_follows with (ann:=(ty, ck)) in H; eauto).
        inv Hwc. rename H2 into Hwc. rename H3 into Hins.
        apply Forall_singl in Hwc. apply Forall2_singl in Hins.
        inv Hwc.
        simpl in *; rewrite app_nil_r in *.
        apply Forall_singl in H3; apply Forall_singl in H4.
        rewrite Forall2_eq in H5, H6.
        assert (Hwce:=H). eapply fby_iteexp_wc_exp in Hwce; eauto.
        assert (Hck:=H). eapply (fby_iteexp_clockof _ _ (ty, ck)) in Hck; eauto.
        assert (Hwceq:=H). eapply fby_iteexp_wc_eq in Hwceq; eauto.
        2:(clear - Hunt; inv Hunt; eauto; inv H0; inv H).
        assert (wc_clock (idck (vars ++ st_senv st)) ck).
        { inv Hins. eapply wc_env_var; eauto. solve_In. }
        eapply (fby_iteexp_wc_env _ _ _ ty ck) in H...
        repeat constructor; auto; simpl; rewrite app_nil_r.
        rewrite Hck. repeat constructor.
        repeat solve_incl.
      - (* arrow *)
        inv Hwc. rename H2 into Hwc. rename H3 into Hins.
        apply Forall_singl in Hwc. apply Forall2_singl in Hins.
        inv Hwc.
        simpl in *; rewrite app_nil_r in *.
        apply Forall_singl in H3; apply Forall_singl in H4.
        rewrite Forall2_eq in H5, H6.
        assert (Hwce:=H). eapply arrow_iteexp_wc_exp in Hwce; eauto.
        assert (wc_clock (idck (vars ++ st_senv st)) ck).
        { inv Hins. eapply wc_env_var; eauto. solve_In. }
        repeat inv_bind.
        assert (Hwce':=H). eapply init_var_for_clock_wc_env in Hwce'; eauto.
        split; eauto.
        assert (st_follows st st') as Hfollows.
        { eapply init_var_for_clock_st_follows; eauto. }
        repeat (constructor; auto); try congruence.
        + repeat solve_incl.
        + eapply init_var_for_clock_wc_eq in H...
      - (* others *)
        split; auto. constructor; auto.
        eapply iface_incl_wc_equation; eauto.
    Qed.

    Fact normfby_block_wc lasts : forall vars to_cut d blocks' st st' ,
        normlast_block lasts d ->
        wc_env (idck (vars++st_senv st)) ->
        wc_block G1 (vars++st_senv st) d ->
        normfby_block to_cut d st = (blocks', st') ->
        Forall (wc_block G2 (vars++st_senv st')) blocks' /\ wc_env (idck (vars++st_senv st')).
    Proof.
      induction d using block_ind2; intros * Hunt Henv Hwc Hfby;
        unfold normfby_blocks in *; repeat inv_bind; simpl; eauto using iface_incl_wc_block.
      - (* equation *)
        inv Hunt. inv Hwc.
        eapply normfby_equation_wc in H as (?&?); eauto.
        split; auto. simpl_Forall.
        constructor; auto.
      - (* reset *)
        simpl in Hfby.
        inv Hunt. inv Hwc.
        cases; repeat inv_bind.
        apply Forall_singl in H3. inv H6. apply Forall_singl in H.
        assert (Hnorm1:=H0). eapply H in H0 as (?&?); eauto.
        split; auto.
        rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
        econstructor; simpl; eauto.
        eapply iface_incl_wc_exp; eauto.
        repeat solve_incl.
        1,2:eapply normfby_block_st_follows; eauto.
    Qed.

    Corollary normfby_blocks_wc lasts : forall vars to_cut blocks blocks' st st' ,
        Forall (normlast_block lasts) blocks ->
        wc_env (idck (vars++st_senv st)) ->
        Forall (wc_block G1 (vars++st_senv st)) blocks ->
        normfby_blocks to_cut blocks st = (blocks', st') ->
        Forall (wc_block G2 (vars++st_senv st')) blocks' /\ wc_env (idck (vars++st_senv st')).
    Proof.
      induction blocks; intros * Hunt Henv Hwc Hfby;
        unfold normfby_blocks in *; repeat inv_bind; simpl; auto.
      inv Hunt. inv Hwc.
      assert (normfby_blocks to_cut blocks x1 = (concat x2, st')) as Hnorm.
      { unfold normfby_blocks. repeat inv_bind; eauto. }
      assert (H':=H). eapply normfby_block_wc in H as [Hwc' Henv']; auto. 2-4:eauto.
      apply IHblocks in Hnorm as [Hwc'' Henv'']; auto.
      2:simpl_Forall; repeat solve_incl; eapply normfby_block_st_follows in H'; eauto.
      rewrite Forall_app; repeat split; eauto.
      simpl_Forall; repeat solve_incl.
    Qed.

    Lemma normfby_node_wc : forall n,
        wc_node G1 n ->
        wc_node G2 (normfby_node n).
    Proof.
      intros * Wc. inversion_clear Wc as [? Hin Hout Hblk].
      pose proof (n_syn n) as Hsyn. inversion Hsyn as [??? _ Hsyn2 _].
      repeat constructor; simpl; auto. rewrite <-H0.
      inv Hblk. inv_scope; subst Γ'.
      destruct (normfby_blocks _ _ _) as (eqs'&st') eqn:Heqres.
      eapply normfby_blocks_wc in Heqres as (Hres1&Henv').
      3,4:unfold st_senv; rewrite init_st_anns, app_nil_r. 4:eauto.
      3:{ unfold wc_env in *. simpl_app.
          repeat rewrite Forall_app in *.
          repeat split; simpl_Forall.
          1-3:eapply wc_clock_incl; [|eauto]. 3:reflexivity.
          1,2:repeat rewrite map_map. erewrite map_ext. eapply incl_appl, incl_refl.
          2:erewrite map_ext, map_ext with (l:=n_out n). 2:eapply incl_appr', incl_appl, incl_refl.
          all:unfold decl; intros; destruct_conjs; auto. }
      2:eauto.
      do 2 econstructor; eauto.
      - simpl_app.
        unfold wc_env in Henv'.
        repeat rewrite Forall_app in Henv'. destruct Henv' as (_&_&_&Henv').
        eapply Forall_app. split; simpl_Forall; simpl_app; solve_incl.
        1,2:repeat rewrite map_map. 2:erewrite map_ext with (l:=st_anns _). 1,2:eapply incl_appr', incl_appr'. apply incl_appl, incl_refl. apply incl_refl.
        intros; destruct_conjs; auto.
      - simpl_Forall.
        simpl_app. erewrite map_map, map_ext with (l:=st_anns _); eauto. intros; destruct_conjs; auto.
    Qed.

  End normfby_node_wc.

  Lemma normfby_global_wc : forall G,
      wc_global G ->
      wc_global (normfby_global G).
  Proof.
    intros []. unfold wc_global, CommonTyping.wt_program; simpl.
    induction nodes0; intros * Hwc; simpl;
      inversion_clear Hwc as [|?? (?&?)]; auto with datatypes.
    constructor; [constructor|].
    - eapply normfby_node_wc; eauto.
      eapply iface_eq_iface_incl, normfby_global_eq.
    - simpl. eapply normfby_nodes_names; eauto.
    - eapply IHnodes0; eauto.
  Qed.

End NFCLOCKING.

Module NFClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (NF  : NORMFBY Ids Op OpAux Cks Senv Syn)
       <: NFCLOCKING Ids Op OpAux Cks Senv Syn Clo NF.
  Include NFCLOCKING Ids Op OpAux Cks Senv Syn Clo NF.
End NFClockingFun.
