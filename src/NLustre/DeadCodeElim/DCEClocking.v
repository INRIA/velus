From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Recdef.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Environment.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import NLustre.DeadCodeElim.DCE.

Module Type DCECLOCKING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Import CEF   : CEISFREE        Ids Op OpAux Cks CESyn)
       (Import CEClo : CECLOCKING      Ids Op OpAux Cks CESyn)
       (Import Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Import Free  : ISFREE          Ids Op OpAux Cks CESyn Syn CEF)
       (Import Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (Import Def   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Import Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Import Clo   : NLCLOCKING      Ids Op OpAux Cks CESyn Syn Ord Mem Def CEClo)
       (Import DCE   : DCE             Ids Op OpAux Cks CESyn CEF Syn Free Mem Def).

  Lemma wc_clock_free : forall vars ck x,
    wc_clock vars ck ->
    Is_free_in_clock x ck ->
    InMembers x vars.
  Proof.
    induction ck; intros * Hwc Hfree;
      inv Hwc; inv Hfree; eauto using In_InMembers.
  Qed.

  Lemma wc_exp_free : forall vars e ck x,
      wc_exp vars e ck ->
      Is_free_in_exp x e ->
      InMembers x vars.
  Proof.
    induction e; intros * Hwc Hfree;
      inv Hwc; inv Hfree; eauto using In_InMembers.
    destruct H1; eauto.
  Qed.

  Lemma wc_cexp_free : forall vars e ck x,
      wc_cexp vars e ck ->
      Is_free_in_cexp x e ->
      InMembers x vars.
  Proof.
    induction e using cexp_ind2'; intros * Hwc Hfree;
      inv Hwc; inv Hfree; eauto using wc_exp_free, In_InMembers.
    - eapply Forall2_ignore1 in H6.
      simpl_Exists; simpl_Forall; eauto.
    - simpl_Exists; simpl_Forall; eauto.
      subst; simpl in *; eauto.
  Qed.

  Lemma wc_rhs_free : forall vars e x ck,
      wc_rhs vars e ck ->
      Is_free_in_rhs x e ->
      InMembers x vars.
  Proof.
    intros * Wt Free; inv Wt; inv Free; eauto using wc_cexp_free.
    simpl_Exists; simpl_Forall; eauto using wc_exp_free.
  Qed.

  Lemma wc_equation_def_free : forall G vars eq x,
      wc_env vars ->
      wc_equation G vars eq ->
      Is_defined_in_eq x eq \/ Is_free_in_eq x eq ->
      InMembers x vars.
  Proof.
    induction eq; intros * Hwenv Hwc Hdeff; inv Hwc.
    - destruct Hdeff as [Hdef|Hfree].
      + inv Hdef; eauto using In_InMembers.
      + inv Hfree. inv H2; eauto using wc_rhs_free, wc_clock_free, wc_env_var.
    - destruct Hdeff as [Hdef|Hfree].
      + inv Hdef. eapply Forall2_ignore1, Forall_forall in H6; eauto.
        destruct H6 as ((?&?&?)&?&?&?&?&?); simpl; eauto using In_InMembers.
      + inv Hfree. destruct H1 as [Hfree|Hex].
        * inv Hfree; eauto.
          -- simpl_Exists.
             eapply Forall2_ignore1, Forall_forall in H5 as ((?&?&?)&?&?&?&?&?); eauto using wc_exp_free.
          -- pose proof (node_in_not_nil n) as Hnnil.
             inv H5; try congruence. clear H0 H2.
             destruct x0 as (?&?&?). destruct H1 as (?&?&Hwc&Hinst).
             apply wc_clock_exp in Hwc; eauto.
             apply instck_parent in Hinst as [|Hpar]; subst; eauto using wc_clock_free.
             eapply wc_clock_parent in Hpar; eauto using wc_clock_free.
        * simpl_Exists; simpl_Forall.
          destruct Hex; subst; eauto using In_InMembers.
          eapply wc_clock_free; [|eauto]. eapply wc_env_var; eauto.
    - destruct Hdeff as [Hdef|Hfree].
      + inv Hdef; eauto using In_InMembers.
      + inv Hfree. destruct H1 as [Hfree|Hex].
        * inv Hfree; eauto using wc_exp_free.
          eapply wc_clock_exp in H5; eauto using wc_clock_free.
        * simpl_Exists; simpl_Forall.
          destruct Hex; subst; eauto using In_InMembers.
          eapply wc_clock_free; [|eauto]. eapply wc_env_var; eauto.
  Qed.

  Section wc_node.
    Variable G1 G2 : global.
    Hypothesis HG : global_iface_eq G1 G2.
    Hypothesis HwG2 : wc_global G2.

    Lemma wc_clock_restrict : forall vars vars' ck,
        (forall x ty, In (x, ty) vars -> Is_free_in_clock x ck -> In (x, ty) vars') ->
        wc_clock vars ck ->
        wc_clock vars' ck.
    Proof.
      induction ck; intros * Hincl Hwc; inv Hwc; constructor; auto with nlfree.
    Qed.

    Lemma wc_exp_restrict : forall vars vars' e ck,
        (forall x ty, In (x, ty) vars -> Is_free_in_exp x e -> In (x, ty) vars') ->
        wc_exp vars e ck ->
        wc_exp vars' e ck.
    Proof.
      induction e; intros * Hincl Hwc; inv Hwc; auto with nlclocking nlfree.
      constructor; auto with nlclocking nlfree.
    Qed.
    Local Hint Resolve wc_exp_restrict : nlclocking.

    Lemma wc_cexp_restrict : forall vars vars' e ck,
        (forall x ty, In (x, ty) vars -> Is_free_in_cexp x e -> In (x, ty) vars') ->
        wc_cexp vars e ck ->
        wc_cexp vars' e ck.
    Proof with eauto with nlclocking nlfree.
      induction e using cexp_ind2'; intros * Hincl Hwc; inv Hwc...
      - econstructor...
        + eapply Forall2_impl_In; [|eauto]; intros; simpl in *.
          rewrite Forall_forall in *; intros.
          eapply H; eauto.
          intros. eapply Hincl; eauto. constructor. solve_Exists.
      - econstructor...
        intros ? Hin. eapply Forall_forall in H; eauto; simpl in *.
        eapply H; eauto. intros. eapply Hincl; eauto.
        eapply FreeEcase_branches. solve_Exists.
    Qed.
    Local Hint Resolve wc_cexp_restrict : nlclocking.

    Lemma wc_rhs_restrict : forall vars vars' e ck,
        (forall x ty, In (x, ty) vars -> Is_free_in_rhs x e -> In (x, ty) vars') ->
        wc_rhs vars e ck ->
        wc_rhs vars' e ck.
    Proof with eauto with nlclocking nlfree.
      intros * Hincl Wt; inv Wt; econstructor; simpl_Forall...
      - eapply wc_exp_restrict; [|eauto].
        intros. eapply Hincl; eauto.
        constructor. solve_Exists.
    Qed.

    Lemma wc_equation_restrict : forall vars vars' eq,
        (forall x ty, In (x, ty) vars -> Is_defined_in_eq x eq \/ Is_free_in_eq x eq -> In (x, ty) vars') ->
        wc_equation G1 vars eq ->
        wc_equation G2 vars' eq.
    Proof with eauto with nlclocking nlfree nldef.
      intros * Hincl Hwc. inv Hwc.
      - econstructor...
        + eapply wc_rhs_restrict with (vars:=vars)...
      - destruct HG as (?&?&Hf). specialize (Hf f). rewrite H in Hf; inv Hf. destruct H7 as (Hname&Hin&Hout).
        econstructor...
        + rewrite <-Hin. simpl_Forall. repeat esplit; eauto.
          eapply wc_exp_restrict with (vars:=vars); eauto.
          intros. eapply Hincl; eauto. right. constructor; left. econstructor. solve_Exists.
        + rewrite <-Hout. simpl_Forall. repeat esplit...
        + simpl_Forall.
          eapply Hincl; eauto. right. constructor; right.
          solve_Exists.
      - econstructor...
        + eapply wc_exp_restrict with (vars:=vars); eauto 8 with nlfree.
        + simpl_Forall.
          eapply Hincl; eauto. right; constructor.
          right. solve_Exists.
    Qed.

    Corollary wc_equations_restrict : forall vars vars' eqs,
        (forall x ty, In (x, ty) vars -> Exists (fun eq => Is_defined_in_eq x eq \/ Is_free_in_eq x eq) eqs -> In (x, ty) vars') ->
        Forall (wc_equation G1 vars) eqs ->
        Forall (wc_equation G2 vars') eqs.
    Proof.
      intros * Hincl Hwc.
      simpl_Forall.
      eapply wc_equation_restrict; [|eauto].
      intros. eapply Hincl; eauto. solve_Exists.
    Qed.

    Lemma wc_equations_has_def : forall vars eqs,
        Forall (wc_equation G1 vars) eqs ->
        Forall (fun eq : equation => exists x0 : ident, Is_defined_in_eq x0 eq) eqs.
    Proof.
      intros * Hwc.
      eapply Forall_impl; [|eauto]; intros ? Hwc'.
      inv Hwc'; eauto with nldef.
      esplit. eapply Is_defined_in_EqApp with (d:=xH).
      pose proof (n_outgt0 n) as Hgt.
      apply Forall2_length in H1. congruence.
    Qed.

    Lemma wc_equation_free_in_clock : forall vars eq x y ck,
        NoDupMembers vars ->
        wc_equation G2 vars eq ->
        Is_defined_in_eq x eq ->
        In (x, ck) vars ->
        Is_free_in_clock y ck ->
        Is_defined_in_eq y eq \/ Is_free_in_eq y eq.
    Proof with eauto with nlfree nldef.
      intros * Hnd Hwc Hdef Hxck Hfree; inv Hwc; inv Hdef.
      - (* def *)
        eapply NoDupMembers_det in Hxck; eauto; subst...
      - (* app *)
        assert (Hf2:=H1). eapply Forall2_ignore1, Forall_forall in H1 as ((?&?&?)&Hin&Hsub&?&Hvars&Hinst); eauto.
        eapply NoDupMembers_det in Hxck; eauto; subst.
        eapply instck_inv in Hinst as [|(?&Hsub'&Hfree')]...
        assert (wc_env (idsnd (n_in n ++ n_out n))) as Hwenv.
        { eapply wc_find_node in H as (?&?&_&?&?&?); eauto. }
        eapply wc_env_var in Hwenv; [|eapply in_map_iff; do 2 esplit; eauto with datatypes]. simpl in *.
        eapply wc_clock_free, InMembers_idsnd, InMembers_In in Hfree' as ((?&?)&Hin'); [|eauto].
        apply in_app_iff in Hin' as [Hin'|Hin'].
        + eapply Forall2_ignore2, Forall_forall in H0 as (?&?&Hv); eauto; simpl in *.
          destruct Hv as (Hv&_). rewrite Hsub' in Hv. inv Hv.
          right. constructor. do 2 left. solve_Exists...
        + eapply Forall2_ignore2, Forall_forall in Hf2 as (?&Hin1&Hv); eauto; simpl in *.
          destruct Hv as (Hsub1&_). rewrite Hsub1 in Hsub'; inv Hsub'...
      - (* fby *)
        eapply NoDupMembers_det in Hxck; eauto; subst...
    Qed.

    Import Permutation.

    Lemma dce_node_wc : forall n,
        wc_node G1 n ->
        wc_node G2 (dce_node n).
    Proof.
      intros ? (Hwc1&Hwc2&Hwc3&Hwc4).
      remember (fst (dce_eqs (PSP.of_list (map fst (n_out n))) (n_vars n) (n_eqs n))) as vars'.
      remember (snd (dce_eqs (PSP.of_list (map fst (n_out n))) (n_vars n) (n_eqs n))) as eqs'.
      assert
        (forall x ck,
            In (x, ck) (idsnd (n_in n ++ n_vars n ++ n_out n)) ->
            Exists (fun eq : equation => Is_defined_in_eq x eq \/ Is_free_in_eq x eq) eqs' ->
            In (x, ck) (idsnd (n_in n ++ vars' ++ n_out n))) as Hstable.
      { intros * Hin Hex.
        assert (InMembers x (n_in n ++ vars' ++ n_out n)) as Hinm.
        eapply dce_eqs_stable with (ins:=n_in n) (eqs:=n_eqs n); eauto. 6:subst; reflexivity.
        - apply NoDup_var_defined_n_eqs.
        - intros ? Hinm1 Hinm2.
          pose proof (n_nodup n) as Hnd. eapply NoDupMembers_app_r, NoDupMembers_app_InMembers in Hnd; eauto.
        - intros ?. rewrite fst_InMembers, <-n_defd.
          symmetry. apply Is_defined_in_vars_defined.
        - eapply wc_equations_has_def; eauto.
        - intros ? Hdef. simpl_Exists; simpl_Forall.
          eapply InMembers_idsnd, wc_equation_def_free; eauto.
        - eapply InMembers_In in Hinm as ((?&?)&?).
          eapply in_map_iff in Hin as ((?&?&?)&Heq&Hin); inv Heq.
        eapply NoDupMembers_det in Hin. 2:apply n_nodup.
        2:{ eapply incl_app; [| |eapply H]. solve_incl_app.
            apply incl_appr, incl_app; [apply incl_appl, incl_filter', incl_refl|solve_incl_app].
        }
        inv Hin. solve_In.
      }
      assert (Forall (wc_equation G2 (idsnd (n_in n ++ vars' ++ n_out n))) eqs') as Hwc'.
      { subst. eapply wc_equations_restrict; eauto.
        eapply Forall_incl; [eauto|apply incl_filter', incl_refl].
      } subst.
      repeat split; auto; simpl.
      - rewrite (Permutation_app_comm (filter _ _)), app_assoc, idsnd_app.
        apply Forall_app; split.
        + eapply Forall_impl; [|eauto]; intros (?&?) ?.
          eapply wc_clock_incl; [|eauto]. solve_incl_app.
        + eapply Forall_forall; intros (?&?) Hin.
          eapply in_map_iff in Hin as ((?&?&?)&Heq&Hin); inv Heq.
          rewrite (Permutation_app_comm (n_vars _)), app_assoc, idsnd_app in Hwc3.
          apply Forall_app in Hwc3 as (_&Hwc3). eapply Forall_forall in Hwc3.
          2:{ eapply filter_In in Hin as (Hin&_). eapply in_map_iff; eauto. }
          simpl in *.
          rewrite <-idsnd_app, <-app_assoc, (Permutation_app_comm (n_out n)) in *.
          eapply wc_clock_restrict; [|eauto].
          intros.
          eapply Hstable; eauto.
          remember (filter _ (n_eqs n)) as eqs'. assert (Is_defined_in i eqs') as Hvd.
          { subst. apply Is_defined_in_vars_defined. rewrite dce_vars_defined. 4:reflexivity.
            - rewrite map_app. apply in_or_app, or_introl, in_map_iff. do 2 esplit; eauto. auto.
            - eapply NoDupMembers_app_r, n_nodup.
            - apply n_defd. }
          eapply Exists_exists in Hvd as (?&Hineq&Hdef).
          solve_Exists.
          eapply wc_equation_free_in_clock; eauto.
          2:(subst; eapply Forall_forall in Hwc'; eauto).
          * apply NoDupMembers_idsnd, dce_NoDupMembers_filter, n_nodup.
          * eapply in_map_iff. do 2 esplit; eauto with datatypes. auto.
    Qed.

  End wc_node.

  Theorem dce_wc : forall G,
    wc_global G ->
    wc_global (dce_global G).
  Proof.
    intros.
    unfold wc_global in *; simpl.
    induction H; simpl; constructor; auto.
    eapply dce_node_wc in H; eauto.
    apply dce_global_iface_eq.
  Qed.

End DCECLOCKING.

Module DCEClockingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CESyn : CESYNTAX        Ids Op OpAux Cks)
       (CEF   : CEISFREE        Ids Op OpAux Cks CESyn)
       (CEClo : CECLOCKING        Ids Op OpAux Cks CESyn)
       (Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Free  : ISFREE          Ids Op OpAux Cks CESyn Syn CEF)
       (Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (Def   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Clo   : NLCLOCKING        Ids Op OpAux Cks CESyn Syn Ord Mem Def CEClo)
       (DCE   : DCE             Ids Op OpAux Cks CESyn CEF Syn Free Mem Def)
<: DCECLOCKING Ids Op OpAux Cks CESyn CEF CEClo Syn Free Mem Def Ord Clo DCE.
  Include DCECLOCKING Ids Op OpAux Cks CESyn CEF CEClo Syn Free Mem Def Ord Clo DCE.
End DCEClockingFun.
