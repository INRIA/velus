From Coq Require Import List Permutation.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Environment.
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
    Variable subl subn : Env.t ident.

    Hypothesis Incl : forall xty,
        In xty Γ -> In xty Γ'.
    Hypothesis SubL : forall x y ty,
        Env.find x subl = Some y -> In (x, (ty, true)) Γ -> In (y, (ty, false)) Γ'.
    Hypothesis SubN : forall x y ty islast,
        Env.find x subn = Some y -> In (x, (ty, islast)) Γ -> In (y, (ty, false)) Γ'.

    Lemma rename_exp_wc : forall e ck,
        wc_exp Γ e ck ->
        wc_exp Γ' (rename_exp subl subn e) ck.
    Proof.
      induction e; intros * Wc; inv Wc; simpl.
      - (* const *) constructor.
      - (* enum *) constructor; auto.
      - (* var *)
        unfold rename_var, or_default.
        cases_eqn Eq; econstructor; eauto.
      - (* last *)
        cases_eqn Eq; econstructor; eauto.
      - (* when *)
        econstructor; eauto.
      - (* unop *)
        constructor; auto.
      - (* binop *)
        constructor; auto.
    Qed.

    Lemma rename_cexp_wc : forall e ck,
        wc_cexp Γ e ck ->
        wc_cexp Γ' (rename_cexp subl subn e) ck.
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
        wc_rhs Γ' (rename_rhs subl subn e) ck.
    Proof.
      intros * Wc. inv Wc; simpl.
      - (* extcall *)
        econstructor; eauto; simpl_Forall; eauto using rename_exp_wc.
      - constructor; auto using rename_cexp_wc.
    Qed.

  End rename.

  Lemma rename_trconstr_wc P Γ Γ' subl subn : forall tc,
      (forall xty, In xty Γ -> In xty Γ') ->
      (forall x y ty, Env.find x subl = Some y -> In (x, (ty, true)) Γ -> In (y, (ty, false)) Γ') ->
      (forall x y ty islast, Env.find x subn = Some y -> In (x, (ty, islast)) Γ -> In (y, (ty, false)) Γ') ->
      wc_trconstr P Γ tc ->
      wc_trconstr (cut_cycles P) Γ' (rename_trconstr subl subn tc).
  Proof.
    intros * Incl SubL SubN Wc; inv Wc; simpl.
    - (* Def *)
      econstructor; simpl; eauto using rename_rhs_wc.
    - (* Reset State *)
      econstructor; eauto using wc_clock_incl.
    - (* Update Last *)
      econstructor; eauto using rename_cexp_wc.
    - (* Update Next *)
      econstructor; eauto using rename_exp_wc.
    - (* Reset Inst *)
      econstructor; eauto using cut_cycles_find_system, wc_clock_incl.
    - (* Update Inst *)
      econstructor; eauto using cut_cycles_find_system; simpl_Forall;
        eauto using rename_exp_wc.
      split.
      + take (SameVar _ _) and inv it; [constructor|].
        simpl. unfold rename_var. rewrite Env.gempty; constructor; auto.
      + do 2 esplit; eauto.
        eapply rename_exp_wc; eauto.
        intros * Find. rewrite Env.gempty in Find. inv Find.
  Qed.

  Import Fresh.

  (* Lemma fresh_idents_In_anns2' {prefs A} : forall xs1 xs2 xs1' xs2' st1 st2, *)
  (*     @fresh_idents prefs A xs1 init_st = (xs1', st1) -> *)
  (*     @fresh_idents prefs A xs2 st1 = (xs2', st2) -> *)
  (*     Forall (fun '(lx, ann) => exists x, In (x, ann) (xs1 ++ xs2)) (st_anns st2). *)
  (* Proof. *)
  (*   intros * Fr1 Fr2. *)
  (*   do 2 (erewrite fresh_idents_anns; eauto). *)
  (*   rewrite init_st_anns, app_nil_r. *)
  (*   apply Forall_app; split; simpl_Forall. *)
  (*   - eapply fresh_idents_In' in Fr2; eauto with datatypes. *)
  (*   - eapply fresh_idents_In' in Fr1; eauto with datatypes. *)
  (* Qed. *)

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
        apply in_app_iff in H0 as [|]; [left|right]; solve_In.
    - destruct (cut_cycles_tcs _ _ _ _) as (tcs'&st') eqn:Htcs.
      unfold cut_cycles_tcs in *. repeat Fresh.Tactics.inv_bind.
      eapply CC.fresh_idents_In_anns2 in H0 as InSt; eauto.
      apply Forall_app in InSt as (InSt1&InSt2).
      rewrite ? Forall_app. repeat split; simpl_Forall.
      + eapply fresh_idents_In' in H as In'; eauto.
        repeat constructor; simpl.
        all:rewrite ? map_app, ? in_app_iff.
        * left. right. left. right. solve_In.
        * right. left. solve_In.
      + eapply fresh_idents_In' in H0 as In'; eauto.
        repeat constructor; simpl. 2:econstructor.
        1,2:rewrite ? map_app, ? in_app_iff.
        * left. right. left. right. solve_In.
        * right. right. solve_In.
      + eapply rename_trconstr_wc in Wc4; eauto.
        * intros * In. rewrite ? map_app, ? in_app_iff in *. firstorder.
        * intros * Find In.
          rewrite ? in_app_iff in In. destruct In as [In|[In|In]]; simpl_In.
          rewrite ? map_app, ? in_app_iff. left. right. left. right.
          apply Env.from_list_find_In in Find. simpl_In. simpl_Forall.
          eapply fresh_idents_In' in Hin0; eauto. simpl_In.
          eapply NoDupMembers_det in Hin; eauto using s_nodup_lasts. inv Hin.
          solve_In.
        * intros * Find In.
          rewrite ? map_app, ? in_app_iff. left. right. left. right.
          apply Env.from_list_find_In in Find. simpl_In. simpl_Forall.
          eapply fresh_idents_In' in Hin; eauto. simpl_In.
          rewrite ? in_app_iff in In. destruct In as [In|[In|In]]; simpl_In.
          1:{ exfalso. eapply NoDup_app_In in ND; [|solve_In].
              eapply ND, in_app_iff, or_intror. solve_In. }
          1:{ exfalso. eapply NoDup_app_r, NoDup_app_In in ND; [|solve_In].
              eapply ND. solve_In. }
          eapply NoDupMembers_det in Hin0; eauto using s_nodup_nexts. inv Hin0.
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
