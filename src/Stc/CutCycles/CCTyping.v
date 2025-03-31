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
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import Stc.StcTyping.
From Velus Require Import Stc.StcClocking.
From Velus Require Import Stc.CutCycles.CC.

Module Type CCTYPING
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX   Ids Op)
  (Import Cks   : CLOCKS          Ids Op OpAux)
  (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
  (Import Syn   : STCSYNTAX       Ids Op OpAux Cks CESyn)
  (Import Ord   : STCORDERED      Ids Op OpAux Cks CESyn Syn)
  (Import CETyp : CETYPING        Ids Op OpAux Cks CESyn)
  (Import Typ   : STCTYPING       Ids Op OpAux Cks CESyn Syn CETyp)
  (Import CEClo : CECLOCKING      Ids Op OpAux Cks CESyn)
  (Import Clo   : STCCLOCKING     Ids Op OpAux Cks CESyn Syn Ord CEClo)
  (Import ECC   : EXT_CC          Ids Op OpAux Cks CESyn Syn)
  (Import CC    : CC              Ids Op OpAux Cks CESyn Syn ECC).

  (* Necessary lemma: find that all clocks are wt *)

  Lemma wt_system_wt_clock {prefs} (P : @program prefs) : forall s,
      wt_system P s ->
      wc_system P s ->
      Forall (fun '(x, (_, _, ck)) =>
                wt_clock P.(types) (map (fun '(x, (ty, _)) => (x, (ty, false))) (s_in s ++ s_vars s ++ s_out s) ++
                                    map (fun '(x, (_, ty, _)) => (x, (ty, true))) (s_lasts s) ++
                                    map (fun '(x, (_, ty, _)) => (x, (ty, false))) (s_nexts s)) ck)
        (s_lasts s ++ s_nexts s).
  Proof.
    intros * (Wt1&_&_) (_&_&_&Wc1).
    pose proof (s_nodup s) as ND.
    rewrite ? app_assoc, <- ? map_app, <- ? app_assoc in ND.
    apply Forall_app; split.
    - simpl_Forall.
      assert (In i (map fst (s_lasts s))) as InM by solve_In.
      rewrite s_lasts_in_tcs, <-lasts_of_In in InM. unfold Is_update_last_in in *.
      simpl_Exists. simpl_Forall. inv InM. inv Wt1. inv Wc1.
      rewrite ? in_app_iff in *. repeat take (_ \/ _ \/ _) and destruct it as [|[|]]; simpl_In.
      eapply NoDupMembers_det in H; eauto using s_nodup_lasts; inv H; auto.
    - simpl_Forall.
      assert (In i (map fst (s_nexts s))) as InM by solve_In.
      rewrite s_nexts_in_tcs, <-nexts_of_In in InM. unfold Is_update_next_in in *.
      simpl_Exists. simpl_Forall. inv InM. inv Wt1. inv Wc1.
      rewrite ? in_app_iff in *. repeat take (_ \/ _ \/ _) and destruct it as [|[|]]; simpl_In.
      1-3:exfalso; eapply NoDup_app_In in ND; [|solve_In]; eapply ND, in_app_iff; right; solve_In.
      eapply NoDupMembers_det in H; eauto using s_nodup_nexts; inv H; auto.
  Qed.

  Section rename.
    Variable Γ Γ' : list (ident * (type * bool)).
    Variable subl subn : Env.t ident.

    Hypothesis Incl : forall xty,
        In xty Γ -> In xty Γ'.
    Hypothesis SubL : forall x y ty,
        Env.find x subl = Some y -> In (x, (ty, true)) Γ -> In (y, (ty, false)) Γ'.
    Hypothesis SubN : forall x y ty islast,
        Env.find x subn = Some y -> In (x, (ty, islast)) Γ -> In (y, (ty, false)) Γ'.

    Lemma rename_exp_wt tys : forall e,
        wt_exp tys Γ e ->
        wt_exp tys Γ' (rename_exp subl subn e).
    Proof.
      induction e; intros * Wt; inv Wt; simpl.
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
        constructor; auto. now rewrite rename_exp_typeof.
      - (* binop *)
        constructor; auto. now rewrite 2 rename_exp_typeof.
    Qed.

    Lemma rename_cexp_wt tys : forall e,
        wt_cexp tys Γ e ->
        wt_cexp tys Γ' (rename_cexp subl subn e).
    Proof.
      induction e using cexp_ind2'; intros * Wt; inv Wt; simpl.
      - (* merge *)
        econstructor; simpl_Forall; eauto.
        + now rewrite length_map.
        + now rewrite rename_cexp_typeofc.
      - (* case *)
        econstructor; simpl_Forall; eauto using rename_exp_wt.
        + now rewrite rename_exp_typeof.
        + now rewrite length_map.
        + intros * In. simpl_In. repeat take (forall e, In _ l -> _) and specialize (it _ Hin).
          now rewrite 2 rename_cexp_typeofc.
        + intros * In. simpl_In. repeat take (forall e, In _ l -> _) and specialize (it _ Hin).
          simpl_Forall. auto.
      - (* exp *)
        econstructor; eauto using rename_exp_wt.
    Qed.

    Lemma rename_rhs_wt tys exts : forall e,
        wt_rhs tys exts Γ e ->
        wt_rhs tys exts Γ' (rename_rhs subl subn e).
    Proof.
      intros * Wt. inv Wt; simpl.
      - (* extcall *)
        econstructor; eauto; simpl_Forall; eauto using rename_exp_wt.
        now rewrite rename_exp_typeof.
      - constructor; auto using rename_cexp_wt.
    Qed.
  End rename.

  Lemma rename_trconstr_wt P Γ Γ' subl subn : forall tc,
      (forall xty, In xty Γ -> In xty Γ') ->
      (forall x y ty, Env.find x subl = Some y -> In (x, (ty, true)) Γ -> In (y, (ty, false)) Γ') ->
      (forall x y ty islast, Env.find x subn = Some y -> In (x, (ty, islast)) Γ -> In (y, (ty, false)) Γ') ->
      wt_trconstr P Γ tc ->
      wt_trconstr (cut_cycles P) Γ' (rename_trconstr subl subn tc).
  Proof.
    intros * Incl SubL SubN Wt; inv Wt; simpl.
    - (* Def *)
      econstructor; simpl; eauto using wt_clock_incl, rename_rhs_wt.
      + rewrite rename_rhs_typeofr; auto.
    - (* Reset State *)
      econstructor; eauto using wt_clock_incl.
    - (* Update Last *)
      econstructor; eauto using wt_clock_incl, rename_cexp_wt.
      + rewrite rename_cexp_typeofc; auto.
    - (* Update Next *)
      econstructor; eauto using wt_clock_incl, rename_exp_wt.
      + rewrite rename_exp_typeof; auto.
    - (* Reset Inst *)
      econstructor; eauto using cut_cycles_find_system, wt_clock_incl.
    - (* Update Inst *)
      econstructor; eauto using cut_cycles_find_system; simpl_Forall;
        eauto using wt_clock_incl, rename_exp_wt.
      + rewrite rename_exp_typeof; auto.
      + eapply rename_exp_wt; eauto.
        intros * Find. rewrite Env.gempty in Find. congruence.
  Qed.

  Import Fresh.

  Lemma cut_cycles_wt_system : forall P s,
      wt_system P s ->
      wc_system P s ->
      wt_system (cut_cycles P) (cut_cycles_system s).
  Proof.
    intros * Wt Wc.
    pose proof (wt_system_wt_clock _ _ Wt Wc) as Wtcks. apply Forall_app in Wtcks as (Cks1&Cks2).
    destruct Wt as (Wt1&Wt2&Wt3). unfold cut_cycles_system.
    pose proof (s_nodup s) as ND.
    rewrite ? app_assoc, <- ? map_app, <- ? app_assoc in ND.
    repeat split; auto; simpl.
    - destruct (cut_cycles_tcs _ _ _ _) as (tcs'&st') eqn:Htcs.
      unfold cut_cycles_tcs in *. repeat Fresh.Tactics.inv_bind.
      eapply CC.fresh_idents_In_anns2 in H0 as InSt; eauto.
      apply Forall_app in InSt as (InSt1&InSt2).
      rewrite ? Forall_app. repeat split; simpl_Forall.
      + eapply fresh_idents_In' in H as In'; eauto.
        repeat constructor; simpl.
        1,3:rewrite ? map_app, ? in_app_iff.
        * left. right. left. right. solve_In.
        * right. left. solve_In.
        * simpl_In. simpl_Forall.
          eapply wt_clock_incl; [|eauto].
          intros * In. rewrite ? map_app, ? in_app_iff in *. firstorder.
      + eapply fresh_idents_In' in H0 as In'; eauto.
        repeat constructor; simpl. 3:econstructor.
        1,3:rewrite ? map_app, ? in_app_iff.
        * left. right. left. right. solve_In.
        * right. right. solve_In.
        * simpl_In. simpl_Forall.
          eapply wt_clock_incl; [|eauto].
          intros * In. rewrite ? map_app, ? in_app_iff in *. firstorder.
      + eapply rename_trconstr_wt in Wt1; eauto.
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
    - intros * In.
      destruct (cut_cycles_tcs _ _ _ _) as (tcs'&st') eqn:Htcs.
      unfold cut_cycles_tcs in *. repeat Fresh.Tactics.inv_bind.
      unfold idfst, idsnd in *.
      rewrite <- ? app_assoc, ? map_app, ? in_app_iff in In.
      firstorder.
      all:try now (eapply Wt3; rewrite ? map_app, ? in_app_iff; eauto).
      simpl_In.
      eapply fresh_idents_In_anns2' in H0; eauto. simpl_Forall. rewrite <-map_app, filter_app in *.
      eapply Wt3, in_app_iff. right. solve_In.
  Qed.

  Lemma cut_cycles_wt_program : forall P,
      wt_program P ->
      wc_program P ->
      wt_program (cut_cycles P).
  Proof.
    intros []; induction systems0 as [|s]; intros * Wt Wc; inv Wt; inv Wc;
      unfold cut_cycles; simpl; constructor; intuition.
    - simpl in *.
      take (wt_system _ _) and apply cut_cycles_wt_system in it as WT; auto.
    - simpl_Forall. auto.
  Qed.

End CCTYPING.

Module CCTypingFun
  (Ids   : IDS)
  (Op    : OPERATORS)
  (OpAux : OPERATORS_AUX   Ids Op)
  (Cks   : CLOCKS          Ids Op OpAux)
  (CESyn : CESYNTAX        Ids Op OpAux Cks)
  (Syn   : STCSYNTAX       Ids Op OpAux Cks CESyn)
  (Ord   : STCORDERED      Ids Op OpAux Cks CESyn Syn)
  (CETyp : CETYPING        Ids Op OpAux Cks CESyn)
  (Typ   : STCTYPING       Ids Op OpAux Cks CESyn Syn CETyp)
  (CEClo : CECLOCKING      Ids Op OpAux Cks CESyn)
  (Clo   : STCCLOCKING     Ids Op OpAux Cks CESyn Syn Ord CEClo)
  (ECC   : EXT_CC          Ids Op OpAux Cks CESyn Syn)
  (CC    : CC              Ids Op OpAux Cks CESyn Syn ECC)
<: CCTYPING Ids Op OpAux Cks CESyn Syn Ord CETyp Typ CEClo Clo ECC CC.
  Include CCTYPING Ids Op OpAux Cks CESyn Syn Ord CETyp Typ CEClo Clo ECC CC.
End CCTypingFun.
