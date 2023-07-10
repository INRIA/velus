From Coq Require Import List Permutation.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CommonProgram.
From Velus Require Import Fresh.

From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import Stc.StcClocking.
From Velus Require Import Stc.CutCycles.CC.

Module Type CCCLOCKING
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX   Ids Op)
  (Import Cks   : CLOCKS          Ids Op OpAux)
  (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
  (Import Syn   : STCSYNTAX       Ids Op OpAux Cks CESyn)
  (Import Ord   : STCORDERED      Ids Op OpAux Cks CESyn Syn)
  (Import CEClo : CECLOCKING      Ids Op OpAux Cks CESyn)
  (Import Clo   : STCCLOCKING     Ids Op OpAux Cks CESyn Syn Ord CEClo)
  (Import ECC   : EXT_CC          Ids Op OpAux Cks CESyn Syn)
  (Import CC    : CC              Ids Op OpAux Cks CESyn Syn ECC).

  Section rename.
    Variable Γ Γ' : list (ident * (clock * bool)).
    Variable (x : var_last) (y : ident).

    Hypothesis Incl : forall xty,
        In xty Γ -> In xty Γ'.
    Hypothesis SubL : forall x' ty,
        x = Last x' -> In (x', (ty, true)) Γ -> In (y, (ty, false)) Γ'.
    Hypothesis SubN : forall x' ty islast,
        x = Var x' -> In (x', (ty, islast)) Γ -> In (y, (ty, false)) Γ'.

    Lemma rename_exp_wc : forall e ck,
        wc_exp Γ e ck ->
        wc_exp Γ' (rename_exp x y e) ck.
    Proof.
      induction e; intros * Wc; inv Wc; simpl.
      - (* const *) constructor.
      - (* enum *) constructor; auto.
      - (* var *)
        unfold rename_var. cases_eqn Eq; econstructor; eauto.
        rewrite equiv_decb_equiv in Eq0. inv Eq0. eauto.
      - (* last *)
        cases_eqn Eq; econstructor; eauto.
        rewrite equiv_decb_equiv in Eq0. inv Eq0. eauto.
      - (* when *)
        econstructor; eauto.
      - (* unop *)
        constructor; auto.
      - (* binop *)
        constructor; auto.
    Qed.

    Lemma rename_cexp_wc : forall e ck,
        wc_cexp Γ e ck ->
        wc_cexp Γ' (rename_cexp x y e) ck.
    Proof.
      induction e using cexp_ind2'; intros * Wc; inv Wc; simpl.
      - (* merge *)
        econstructor; eauto.
        + intros ?. take (l <> []) and eapply it, map_eq_nil; eauto.
        + rewrite map_length. simpl_Forall; eauto.
      - (* case *)
        econstructor; eauto using rename_exp_wc.
        + intros ?. take (l <> []) and eapply it, map_eq_nil; eauto.
        + intros * In. simpl_In. repeat take (forall e, In _ l -> _) and specialize (it _ Hin).
          simpl_Forall. auto.
      - (* exp *)
        econstructor; eauto using rename_exp_wc.
    Qed.

    Lemma rename_rhs_wc : forall e ck,
        wc_rhs Γ e ck ->
        wc_rhs Γ' (rename_rhs x y e) ck.
    Proof.
      intros * Wc. inv Wc; simpl.
      - (* extcall *)
        econstructor; eauto; simpl_Forall; eauto using rename_exp_wc.
      - constructor; auto using rename_cexp_wc.
    Qed.

  End rename.

  Lemma rename_trconstr_wc {prefs} (P: @program prefs) Γ Γ' i x y : forall tc,
      (forall xty, In xty Γ -> In xty Γ') ->
      (forall x' ty, x = Last x' -> In (x', (ty, true)) Γ -> In (y, (ty, false)) Γ') ->
      (forall x' ty islast, x = Var x' -> In (x', (ty, islast)) Γ -> In (y, (ty, false)) Γ') ->
      wc_trconstr P Γ tc ->
      wc_trconstr P Γ' (rename_trconstr i x y tc).
  Proof.
    intros * Incl SubL SubN Wc; inv Wc; simpl.
    - (* Def *)
      cases; econstructor; simpl; eauto using rename_rhs_wc, wc_rhs_incl.
    - (* Reset State *)
      econstructor; eauto using wc_clock_incl.
    - (* Update Last *)
      cases; econstructor; eauto using rename_cexp_wc, wc_cexp_incl.
    - (* Update Next *)
      cases; econstructor; eauto using rename_exp_wc, wc_exp_incl.
    - (* Reset Inst *)
      econstructor; eauto using cut_cycles_find_system, wc_clock_incl.
    - (* Update Inst *)
      cases; econstructor; eauto; simpl_Forall;
        eauto using rename_exp_wc; split; eauto using wc_exp_incl.
      + take (SameVar _ _) and inv it; [constructor|].
        simpl. unfold rename_var. constructor; auto.
      + do 2 esplit; eauto.
        eapply rename_exp_wc; eauto.
  Qed.

  Fact cut_cycles_wc_trconstr : forall P Γ tc,
      wc_trconstr P Γ tc ->
      wc_trconstr (cut_cycles P) Γ tc.
  Proof.
    intros * Wc; inv Wc; econstructor; eauto using cut_cycles_find_system.
  Qed.

  Import Fresh.

  Lemma cut_cycles_wc_system : forall P s,
      wc_system P s ->
      wc_system (cut_cycles P) (cut_cycles_system s).
  Proof.
    intros * Wc.
    (* pose proof (wc_system_wc_clock _ _ Wc Wc) as Wccks. apply Forall_app in Wccks as (Cks1&Cks2). *)
    destruct Wc as (Wc1&Wc2&Wc3&Wc4). unfold cut_cycles_system.
    pose proof (s_nodup s) as ND.
    rewrite ? app_assoc, <- ? map_app, <- ? app_assoc in ND.
    repeat split; auto; simpl.
    - destruct (cut_cycles_tcs _ _ _ _) as (tcs'&st') eqn:Htcs.
      unfold wc_env in *. rewrite <-Forall_map in *.
      eapply Forall_incl. eapply Forall_impl, Wc3.
      + intros * Wc. eapply Cks.wc_clock_incl; [|eauto].
        intros ??. simpl_app. rewrite ? in_app_iff in *. firstorder.
      + intros ??. simpl_app. rewrite ? in_app_iff in *. firstorder.
        simpl_In. do 3 right.
        unfold cut_cycles_tcs in *. repeat Fresh.Tactics.inv_bind.
        eapply fresh_idents_In_anns2' in H0; eauto. simpl_Forall.
        apply in_app_iff in H0 as [|]; [left|right]; solve_In; cases.
    - destruct (cut_cycles_tcs _ _ _ _) as (tcs'&st') eqn:Htcs.
      unfold cut_cycles_tcs in *. repeat Fresh.Tactics.inv_bind.
      eapply CC.fresh_idents_In_anns2 in H0 as InSt; eauto.
      apply Forall_app in InSt as (InSt1&InSt2).
      rewrite ? Forall_app. repeat split; simpl_Forall.
      + eapply fresh_idents_In' in H as In'; eauto.
        repeat constructor; simpl.
        all:rewrite ? map_app, ? in_app_iff.
        * left. right. left. right. solve_In.
        * right. left. simpl_In. cases. inv Hf. solve_In.
      + eapply fresh_idents_In' in H0 as In'; eauto.
        repeat constructor; simpl. 2:econstructor.
        1,2:rewrite ? map_app, ? in_app_iff.
        * left. right. left. right. solve_In.
        * right. right. simpl_In. cases. inv Hf. solve_In.
      + rewrite ? map_fold_rename in H1. simpl_In. simpl_Forall.
        remember (map _ _ ++ map _ _ ++ map _ _) as Γ.
        remember (map _ (_ ++ (_ ++ _) ++ _) ++ map _ _ ++ map _ _) as Γ'.
        eapply fold_left_ind with (Pb:=fun '(x, lx, (_, _)) => forall ty islast, In (x, (ty, islast)) Γ' -> In (lx, (ty, false)) Γ').
        2:eapply fold_left_ind with (Pb:=fun '(x, lx, (_, _)) => forall ty, In (x, (ty, true)) Γ' -> In (lx, (ty, false)) Γ').
        3:eapply wc_trconstr_incl, cut_cycles_wc_trconstr; eauto.
        * intros * Wt Incl'; destruct_conjs. eapply rename_trconstr_wc; eauto.
          1,2:intros * Eq; inv Eq; eauto.
        * intros * Wt Incl'; destruct_conjs. eapply rename_trconstr_wc; eauto.
          1,2:intros * Eq; inv Eq; eauto.
        * subst. intros * In. rewrite ? map_app, ? in_app_iff in *. firstorder.
        * simpl_Forall. intros * In. subst.
          rewrite ? in_app_iff in In. destruct In as [In|[In|In]]; simpl_In.
          rewrite ? map_app, ? in_app_iff. left. right. left. right.
          eapply fresh_idents_In' in H1; eauto. simpl_In. cases. inv Hf.
          eapply NoDupMembers_det in Hin; eauto using s_nodup_lasts. inv Hin.
          solve_In.
        * simpl_Forall. intros * In. subst.
          rewrite ? map_app, ? in_app_iff. left. right. left. right.
          eapply fresh_idents_In' in H1; eauto. simpl_In. cases. inv Hf.
          rewrite <-app_assoc, Permutation_app_comm with (l:=map _ (st_anns _)) in In.
          rewrite ? app_assoc, map_app, <- ? app_assoc in In.
          rewrite ? in_app_iff in In. destruct In as [In|[In|[In|In]]]; simpl_In.
          1:{ exfalso. eapply NoDup_app_In in ND; [|solve_In].
              eapply ND, in_app_iff, or_intror. solve_In. }
          1:{ exfalso. eapply Facts.st_valid_AtomOrGensym_nIn; eauto using stc_not_in_lustre_prefs.
              2:apply in_map_iff; eauto.
              simpl. pose proof (s_good s) as (_&_&Good&_). now simpl_Forall. }
          1:{ exfalso. eapply NoDup_app_r, NoDup_app_In in ND; [|solve_In].
              eapply ND. solve_In. }
          eapply NoDupMembers_det in Hin; eauto using s_nodup_nexts. inv Hin.
          solve_In.
  Qed.

  Lemma cut_cycles_wc_program : forall P,
      wc_program P ->
      wc_program (cut_cycles P).
  Proof.
    intros []; induction systems0 as [|s]; intros * Wc; inv Wc;
      unfold cut_cycles; simpl; constructor; intuition.
    - simpl in *.
      take (wc_system _ _) and apply cut_cycles_wc_system in it as WC; auto.
  Qed.

End CCCLOCKING.

Module CCClockingFun
  (Ids   : IDS)
  (Op    : OPERATORS)
  (OpAux : OPERATORS_AUX   Ids Op)
  (Cks   : CLOCKS          Ids Op OpAux)
  (CESyn : CESYNTAX        Ids Op OpAux Cks)
  (Syn   : STCSYNTAX       Ids Op OpAux Cks CESyn)
  (Ord   : STCORDERED      Ids Op OpAux Cks CESyn Syn)
  (CEClo : CECLOCKING      Ids Op OpAux Cks CESyn)
  (Clo   : STCCLOCKING     Ids Op OpAux Cks CESyn Syn Ord CEClo)
  (ECC   : EXT_CC          Ids Op OpAux Cks CESyn Syn)
  (CC    : CC              Ids Op OpAux Cks CESyn Syn ECC)
<: CCCLOCKING Ids Op OpAux Cks CESyn Syn Ord CEClo Clo ECC CC.
  Include CCCLOCKING Ids Op OpAux Cks CESyn Syn Ord CEClo Clo ECC CC.
End CCClockingFun.
