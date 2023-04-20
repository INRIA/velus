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
From Velus Require Import Lustre.SubClock.SubClock.

Module Type SCCLOCKING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import SC : SUBCLOCK Ids Op OpAux Cks Senv Syn).

  Section subclock.
    Variable bck : clock.
    Variable sub : Env.t ident.
    Variable Γ Γ' : static_env.

    Hypothesis NoLast : forall x, ~IsLast Γ x.

    Hypothesis Hsub : forall x y ck,
        Env.find x sub = Some y ->
        HasClock Γ x ck ->
        HasClock Γ' y (subclock_clock bck sub ck).

    Hypothesis Hnsub : forall x ck,
        Env.find x sub = None ->
        HasClock Γ x ck ->
        HasClock Γ' x (subclock_clock bck sub ck).

    Lemma rename_var_wc : forall x ck,
        HasClock Γ x ck ->
        HasClock Γ' (rename_var sub x) (subclock_clock bck sub ck).
    Proof.
      unfold rename_var.
      intros * Hin.
      destruct (Env.find _ _) eqn:Hfind; simpl in *; eauto.
    Qed.

    Context {PSyn : list decl -> block -> Prop} {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Hypothesis Hwbck : wc_clock (idck Γ') bck.

    Lemma subclock_clock_wc : forall ck,
        wc_clock (idck Γ) ck ->
        wc_clock (idck Γ') (subclock_clock bck sub ck).
    Proof.
      induction ck; intros * Hwc; inv Hwc; simpl; auto.
      constructor; eauto.
      simpl_In. assert (HasClock Γ i a.(clo)) as Hck by eauto with senv.
      eapply rename_var_wc in Hck. inv Hck. solve_In. congruence.
    Qed.

    Lemma add_whens_wc : forall e ty,
        clockof e = [Cbase] ->
        wc_exp G Γ' e ->
        wc_exp G Γ' (add_whens e ty bck).
    Proof.
      clear Hsub Hnsub.
      induction bck as [|??? (?&?)]; intros * Hbase Hwc; inv Hwbck;
        simpl in *; auto. simpl_In.
      eapply wc_Ewhen; eauto; simpl; try rewrite app_nil_r.
      - econstructor; solve_In; eauto.
      - rewrite add_whens_clockof; auto.
      - rewrite add_whens_clockof; auto.
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
        wc_exp G Γ e ->
        wc_exp G Γ' (subclock_exp bck sub e).
    Proof with eauto with lclocking.
      induction e using exp_ind2; intros * Hwc; inv Hwc; simpl in *.
      3-13:econstructor; simpl in *; eauto using rename_var_wc with lclocking.
      3,4:take (IsLast _ _) and eapply NoLast in it as [].
      all:try solve [rewrite Forall_map, Forall_forall in *; intros; eauto].
      all:try rewrite subclock_exp_clockof.
      all:try rewrite subclock_exp_clocksof.
      all:try (rewrite map_subclock_ann_clock; rewrite Forall2_eq in *; congruence).
      - apply add_whens_wc...
      - apply add_whens_wc...
      - take (clockof e = [_]) and rewrite it; auto.
      - take (clockof e1 = [_]) and rewrite it; auto.
      - take (clockof e2 = [_]) and rewrite it; auto.
      - simpl_Forall; subst; auto.
      - contradict H5. eapply map_eq_nil; eauto.
      - simpl_Forall; subst; auto.
      - rewrite map_length; auto.
      - contradict H4. apply map_eq_nil in H4; auto.
      - simpl_Forall. auto.
      - rewrite Forall_map. rewrite Forall_forall; intros (?&?) Hin; simpl.
        rewrite subclock_exp_clocksof, Forall_map.
        eapply Forall_forall in H6; eauto; simpl in H6.
        eapply Forall_impl; [|eauto]; intros; subst; auto.
      - simpl_Forall.
        now rewrite subclock_exp_clocksof, map_length.
      - now rewrite H6.
      - contradict H7. apply map_eq_nil in H7; auto.
      - simpl_Forall; auto.
      - rewrite Forall_map. rewrite Forall_forall; intros (?&?) Hin; simpl.
        rewrite subclock_exp_clocksof, Forall_map.
        eapply Forall_forall in H9; eauto; simpl in H9.
        eapply Forall_impl; [|eauto]; intros; subst; auto.
      - simpl_Forall.
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
      - rewrite subclock_exp_nclocksof. simpl_Forall.
        eapply subclock_nclock_WellInstantiated1; eauto.
      - simpl_Forall.
        eapply subclock_nclock_WellInstantiated2; eauto.
      - simpl_Forall.
        rewrite subclock_exp_clockof, H2; simpl; eauto.
    Qed.

    Lemma subclock_equation_wc : forall eq,
        wc_equation G Γ eq ->
        wc_equation G Γ' (subclock_equation bck sub eq).
    Proof.
      intros (?&?) Hwc. inv Hwc; simpl.
      - (* app *)
        econstructor; eauto.
        + simpl_Forall; eauto using subclock_exp_wc.
        + simpl_Forall; eauto using subclock_exp_wc.
        + rewrite subclock_exp_nclocksof. simpl_Forall.
          eapply subclock_nclock_WellInstantiated1; eauto.
        + rewrite 2 Forall3_map_2, Forall3_map_3. rewrite Forall3_map_2 in H5.
          eapply Forall3_impl_In; [|eauto]; intros (?&?) (?&?) ? _ _ _ ?; simpl.
          eapply subclock_nclock_WellInstantiated1 in H; eauto. eapply H.
        + simpl_Forall.
          rewrite subclock_exp_clockof, H0; simpl; eauto.
        + simpl_Forall. eapply rename_var_wc; eauto.
      - (* general case *)
        econstructor; eauto.
        + simpl_Forall; eauto using subclock_exp_wc.
        + rewrite subclock_exp_clocksof. simpl_Forall; eauto using rename_var_wc.
    Qed.

  End subclock.

End SCCLOCKING.

Module SCClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (SC  : SUBCLOCK Ids Op OpAux Cks Senv Syn)
       <: SCCLOCKING Ids Op OpAux Cks Senv Syn Clo SC.
  Include SCCLOCKING Ids Op OpAux Cks Senv Syn Clo SC.
End SCClockingFun.
