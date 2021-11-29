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
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLTyping.
From Velus Require Import NLustre.DeadCodeElim.DCE.

Module Type DCETYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Import CEF   : CEISFREE        Ids Op OpAux Cks CESyn)
       (Import CETyp : CETYPING        Ids Op OpAux Cks CESyn)
       (Import Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Import Free  : ISFREE          Ids Op OpAux Cks CESyn Syn CEF)
       (Import Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (Import Def   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Import Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Import Typ   : NLTYPING        Ids Op OpAux Cks CESyn Syn Ord CETyp)
       (Import DCE   : DCE             Ids Op OpAux Cks CESyn CEF Syn Free Mem Def).

  Lemma wt_clock_free : forall enums vars ck x,
    wt_clock enums vars ck ->
    Is_free_in_clock x ck ->
    InMembers x vars.
  Proof.
    induction ck; intros * Hwt Hfree;
      inv Hwt; inv Hfree; eauto using In_InMembers.
  Qed.

  Lemma wt_exp_free : forall enums vars e x,
      wt_exp enums vars e ->
      Is_free_in_exp x e ->
      InMembers x vars.
  Proof.
    induction e; intros * Hwt Hfree;
      inv Hwt; inv Hfree; eauto using In_InMembers.
    destruct H1; eauto.
  Qed.

  Lemma wt_cexp_free : forall enums vars e x,
      wt_cexp enums vars e ->
      Is_free_in_cexp x e ->
      InMembers x vars.
  Proof.
    induction e using cexp_ind2'; intros * Hwt Hfree;
      inv Hwt; inv Hfree; eauto using wt_exp_free, In_InMembers.
    - eapply Exists_exists in H2 as (?&?&?).
      repeat rewrite Forall_forall in *; eauto.
    - eapply Exists_exists in H2 as (?&?&(?&?&?)); subst.
      repeat rewrite Forall_forall in *; eauto.
      specialize (H _ H0). simpl in *; eauto.
  Qed.

  Lemma wt_equation_def_free : forall G vars eq x,
      wt_equation G vars eq ->
      Is_defined_in_eq x eq \/ Is_free_in_eq x eq ->
      InMembers x vars.
  Proof.
    induction eq; intros * Hwt Hdeff; inv Hwt.
    - destruct Hdeff as [Hdef|Hfree].
      + inv Hdef; eauto using In_InMembers.
      + inv Hfree. inv H1; eauto using wt_clock_free, wt_cexp_free.
    - destruct Hdeff as [Hdef|Hfree].
      + inv Hdef. eapply Forall2_ignore2, Forall_forall in H5; eauto.
        destruct H5 as ((?&?&?)&?&?); simpl; eauto using In_InMembers.
      + inv Hfree. destruct H1 as [Hfree|Hex].
        * inv Hfree; eauto using wt_clock_free.
          eapply Exists_exists in H as (?&?&?).
          eapply Forall_forall in H8; eauto using wt_exp_free.
        * eapply Exists_exists in Hex as ((?&?)&?&?); subst.
          eapply Forall_forall in H9 as (?&?); [|eapply in_map_iff; do 2 esplit; eauto].
          eapply Forall_forall in H10; [|eapply in_map_iff; do 2 esplit; eauto].
          destruct H0; subst; eauto using In_InMembers, wt_clock_free.
    - destruct Hdeff as [Hdef|Hfree].
      + inv Hdef; eauto using In_InMembers.
      + inv Hfree. destruct H1 as [Hfree|Hex].
        * inv Hfree; eauto using wt_clock_free, wt_exp_free.
        * eapply Exists_exists in Hex as ((?&?)&?&?); subst.
          eapply Forall_forall in H8 as (?&?); [|eapply in_map_iff; do 2 esplit; eauto].
          eapply Forall_forall in H9; [|eapply in_map_iff; do 2 esplit; eauto].
          destruct H0; subst; eauto using In_InMembers, wt_clock_free.
  Qed.

  Section wt_node.
    Variable G1 G2 : global.
    Hypothesis HG : global_iface_eq G1 G2.

    Lemma wt_clock_restrict : forall vars vars' ck,
        (forall x ty, In (x, ty) vars -> Is_free_in_clock x ck -> In (x, ty) vars') ->
        wt_clock G1.(enums) vars ck ->
        wt_clock G2.(enums) vars' ck.
    Proof.
      induction ck; intros * Hincl Hwt; inv Hwt; constructor; auto.
      destruct HG. congruence.
    Qed.

    Lemma wt_exp_restrict : forall vars vars' e,
        (forall x ty, In (x, ty) vars -> Is_free_in_exp x e -> In (x, ty) vars') ->
        wt_exp G1.(enums) vars e ->
        wt_exp G2.(enums) vars' e.
    Proof.
      induction e; intros * Hincl Hwt; inv Hwt; auto.
      - constructor; auto. destruct HG; congruence.
      - econstructor; eauto. destruct HG; congruence.
      - econstructor; eauto.
    Qed.

    Lemma wt_cexp_restrict : forall vars vars' e,
        (forall x ty, In (x, ty) vars -> Is_free_in_cexp x e -> In (x, ty) vars') ->
        wt_cexp G1.(enums) vars e ->
        wt_cexp G2.(enums) vars' e.
    Proof.
      induction e using cexp_ind2'; intros * Hincl Hwt; inv Hwt; eauto using wt_exp_restrict.
      - econstructor; eauto.
        + destruct HG; congruence.
        + rewrite Forall_forall in *; intros.
          eapply H; eauto.
          intros. eapply Hincl; eauto. constructor. eapply Exists_exists; eauto.
      - econstructor; eauto using wt_exp_restrict.
        + destruct HG; congruence.
        + intros ? Hin. eapply Forall_forall in H; eauto; simpl in *.
          eapply H; eauto. intros. eapply Hincl; eauto.
          eapply FreeEcase_branches. apply Exists_exists. do 2 esplit; eauto.
    Qed.

    Lemma wt_equation_restrict : forall vars vars' eq,
        (forall x ty, In (x, ty) vars -> Is_defined_in_eq x eq \/ Is_free_in_eq x eq -> In (x, ty) vars') ->
        wt_equation G1 vars eq ->
        wt_equation G2 vars' eq.
    Proof.
      intros * Hincl Hwt. inv Hwt.
      - econstructor; eauto.
        + eapply wt_clock_restrict with (vars:=vars); eauto.
        + eapply wt_cexp_restrict with (vars:=vars); eauto.
      - destruct HG as (?&Hf). specialize (Hf f). rewrite H in Hf; inv Hf. destruct H9 as (Hname&Hin&Hout).
        econstructor; eauto.
        + rewrite <-Hout. eapply Forall2_impl_In; [|eauto].
          intros ? (?&?&?) Hin1 Hin2 ?; simpl in *; eauto.
        + rewrite <-Hin. eapply Forall2_impl_In; [|eauto].
          intros ? (?&?&?) Hin1 Hin2 ?; simpl in *; eauto.
        + eapply wt_clock_restrict with (vars:=vars); eauto 8.
        + rewrite Forall_forall in *; intros.
          eapply wt_exp_restrict with (vars:=vars); eauto.
          intros. eapply Hincl; eauto.
          right; constructor; left.
          constructor. eapply Exists_exists; eauto.
        + eapply Forall_impl_In; [|eauto]; intros ? Hin' (?&?).
          split; try congruence.
          eapply Hincl; eauto. right; constructor.
          eapply in_map_iff in Hin' as ((?&?)&?&?); subst.
          right. eapply Exists_exists; do 2 esplit; eauto. simpl; auto.
        + eapply Forall_impl_In; [|eauto]; intros ? Hin' ?.
          eapply in_map_iff in Hin' as ((?&?)&?&?); subst.
          eapply wt_clock_restrict with (vars:=vars); eauto.
          intros. eapply Hincl; eauto.
          right; constructor; right.
          eapply Exists_exists; do 2 esplit; eauto. simpl; auto.
      - econstructor; eauto.
        + destruct HG; congruence.
        + eapply wt_clock_restrict with (vars:=vars); eauto 8.
        + eapply wt_exp_restrict with (vars:=vars); eauto 8.
        + eapply Forall_impl_In; [|eauto]; intros ? Hin' (?&?).
          split.
          * destruct HG; congruence.
          * eapply Hincl; eauto. right; constructor.
            eapply in_map_iff in Hin' as ((?&?)&?&?); subst.
            right. eapply Exists_exists; do 2 esplit; eauto. simpl; auto.
        + eapply Forall_impl_In; [|eauto]; intros ? Hin' ?.
          eapply in_map_iff in Hin' as ((?&?)&?&?); subst.
          eapply wt_clock_restrict with (vars:=vars); eauto.
          intros. eapply Hincl; eauto.
          right; constructor; right.
          eapply Exists_exists; do 2 esplit; eauto. simpl; auto.
    Qed.

    Corollary wt_equations_restrict : forall vars vars' eqs,
        (forall x ty, In (x, ty) vars -> Exists (fun eq => Is_defined_in_eq x eq \/ Is_free_in_eq x eq) eqs -> In (x, ty) vars') ->
        Forall (wt_equation G1 vars) eqs ->
        Forall (wt_equation G2 vars') eqs.
    Proof.
      intros * Hincl Hwt.
      eapply Forall_impl_In; [|eauto]; intros.
      eapply wt_equation_restrict; [|eauto].
      intros. eapply Hincl; eauto. eapply Exists_exists; eauto.
    Qed.

    Lemma wt_equations_has_def : forall vars eqs,
        Forall (wt_equation G1 vars) eqs ->
        Forall (fun eq : equation => exists x0 : ident, Is_defined_in_eq x0 eq) eqs.
    Proof.
      intros * Hwt.
      eapply Forall_impl; [|eauto]; intros ? Hwt'.
      inv Hwt'; eauto.
      esplit. eapply Is_defined_in_EqApp with (d:=xH).
      pose proof (n_outgt0 n) as Hgt.
      apply Forall2_length in H0. congruence.
    Qed.

    Lemma dce_node_wt : forall n,
        wt_node G1 n ->
        wt_node G2 (dce_node n).
    Proof.
      intros ? (Hwt1&Hwt2).
      constructor; simpl.
      - eapply wt_equations_restrict.
        2:eapply Forall_incl; [eauto|apply incl_filter', incl_refl].
        intros ?? Hin Hex.
        eapply dce_eqs_stable with (ins:=n_in n) in Hex. 7:reflexivity.
        + eapply InMembers_In in Hex as ((?&?)&?).
          eapply in_map_iff in Hin as ((?&?&?)&Heq&Hin); inv Heq.
          eapply NoDupMembers_det in Hin. 2:apply n_nodup.
          2:{ eapply incl_app; [| |eapply H]. solve_incl_app.
              apply incl_appr, incl_app; [apply incl_appl, incl_filter', incl_refl|solve_incl_app].
          } inv Hin.
          eapply in_map_iff; do 2 esplit; eauto. simpl; auto.
        + apply NoDup_var_defined_n_eqs.
        + intros ? Hinm1 Hinm2.
          pose proof (n_nodup n) as Hnd. eapply NoDupMembers_app_r, NoDupMembers_app_InMembers in Hnd; eauto.
        + intros ?. rewrite fst_InMembers, <-n_defd.
          symmetry. apply Is_defined_in_vars_defined.
        + eapply wt_equations_has_def; eauto.
        + intros ? Hdef. eapply Exists_exists in Hdef as (?&?&?).
          eapply Forall_forall in Hwt1; eauto.
          eapply InMembers_idty, wt_equation_def_free; eauto.
      - intros x tn Hin. specialize (Hwt2 x tn).
        repeat rewrite idty_app, in_app_iff in Hin, Hwt2.
        destruct HG as (Henums&_). rewrite <-Henums.
        destruct Hin as [|[Hin|]]; auto.
        apply Hwt2; right; left.
        apply in_map_iff in Hin as ((?&?)&Heq&Hin); inv Heq.
        apply filter_In in Hin as (?&?).
        apply in_map_iff. do 2 esplit; eauto. reflexivity.
    Qed.

  End wt_node.

  Theorem dce_wt : forall G,
    wt_global G ->
    wt_global (dce_global G).
  Proof.
    intros.
    eapply CommonTyping.transform_units_wt_program; eauto.
    intros. eapply dce_node_wt; eauto using dce_global_iface_eq.
  Qed.

End DCETYPING.

Module DCETypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CESyn : CESYNTAX        Ids Op OpAux Cks)
       (CEF   : CEISFREE        Ids Op OpAux Cks CESyn)
       (CETyp : CETYPING        Ids Op OpAux Cks CESyn)
       (Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Free  : ISFREE          Ids Op OpAux Cks CESyn Syn CEF)
       (Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (Def   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Typ   : NLTYPING        Ids Op OpAux Cks CESyn Syn Ord CETyp)
       (DCE   : DCE             Ids Op OpAux Cks CESyn CEF Syn Free Mem Def)
<: DCETYPING Ids Op OpAux Cks CESyn CEF CETyp Syn Free Mem Def Ord Typ DCE.
  Include DCETYPING Ids Op OpAux Cks CESyn CEF CETyp Syn Free Mem Def Ord Typ DCE.
End DCETypingFun.
