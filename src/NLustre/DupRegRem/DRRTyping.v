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
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLTyping.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.DupRegRem.DRR.

Module Type DRRTYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Import CETyp : CETYPING        Ids Op OpAux Cks CESyn)
       (Import Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Import Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Import Typ   : NLTYPING        Ids Op OpAux Cks CESyn Syn Ord CETyp)
       (Import DRR   : DRR             Ids Op OpAux Cks CESyn Syn).

  Section rename.
    Variable sub : Env.t ident.

    Variable inouts : list (ident * type).
    Variable vars vars' : list (ident * type).

    Hypothesis Hsub : forall x y ty,
        Env.find x sub = Some y ->
        In (x, ty) (inouts ++ vars) ->
        In (y, ty) (inouts ++ vars').

    Hypothesis Hnsub : forall x ty,
        Env.find x sub = None ->
        In (x, ty) (inouts ++ vars) ->
        In (x, ty) (inouts ++ vars').

    Lemma rename_in_var_wt : forall x ty,
        In (x, ty) (inouts++vars) ->
        In (rename_in_var sub x, ty) (inouts++vars').
    Proof.
      intros * Hin.
      unfold rename_in_var.
      destruct (Env.find _ _) eqn:Hfind; eauto.
    Qed.
    Local Hint Resolve rename_in_var_wt : nltyping.

    Variable (G : global).

    Lemma rename_in_clock_wt : forall ck,
        wt_clock G.(enums) (inouts++vars) ck ->
        wt_clock G.(enums) (inouts++vars') (rename_in_clock sub ck).
    Proof.
      induction ck; intros * Hwt; inv Hwt; auto with nltyping.
      simpl. constructor; eauto with nltyping.
    Qed.

    Lemma rename_in_exp_wt : forall e,
        wt_exp G.(enums) (inouts++vars) e ->
        wt_exp G.(enums) (inouts++vars') (rename_in_exp sub e).
    Proof.
      intros * Hwt; induction Hwt;
        simpl; econstructor; eauto with nltyping.
      1,2:repeat rewrite rename_in_exp_typeof; auto.
    Qed.

    Lemma rename_in_cexp_wt : forall e,
        wt_cexp G.(enums) (inouts++vars) e ->
        wt_cexp G.(enums) (inouts++vars') (rename_in_cexp sub e).
    Proof.
      induction e using cexp_ind2'; intros * Hwt; inv Hwt;
        simpl; econstructor; eauto using rename_in_var_wt, rename_in_exp_wt.
      1,5:rewrite map_length; auto.
      - rewrite Forall_map. eapply Forall_impl; [|eapply H6]; intros.
        rewrite rename_in_cexp_typeofc; auto.
      - rewrite Forall_map. eapply Forall_impl_In; [|eapply H7]; intros.
        eapply Forall_forall in H; eauto.
      - rewrite rename_in_exp_typeof; eauto.
      - intros.
        eapply in_map_iff in H0 as (?&Hsome&Hin).
        eapply option_map_inv in Hsome as (?&?&?); subst.
        rewrite 2 rename_in_cexp_typeofc; auto.
      - intros.
        eapply in_map_iff in H0 as (?&Hsome&Hin).
        eapply option_map_inv in Hsome as (?&?&?); subst.
        eapply Forall_forall in H; eauto.
        simpl in H; eauto.
    Qed.

    Local Hint Resolve rename_in_var_wt rename_in_clock_wt rename_in_exp_wt rename_in_cexp_wt : nltyping.

    Lemma rename_in_equation_wt : forall equ,
        (forall x, In x (var_defined equ) -> Env.find x sub = None) ->
        wt_equation G (inouts++vars) equ ->
        wt_equation G (inouts++vars') (rename_in_equation sub equ).
    Proof with eauto with nltyping.
      intros * Hdef Hwt; inv Hwt; simpl in *.
      - constructor...
        rewrite rename_in_cexp_typeofc; auto.
      - econstructor...
        + eapply Forall2_impl_In; [|eauto]; intros ? (?&?&?) ? _ ?; auto.
        + rewrite Forall2_map_1.
          eapply Forall2_impl_In; [|eauto]; intros ? (?&?&?) _ _ Hty.
          rewrite rename_in_exp_typeof; auto.
        + rewrite Forall_map.
          eapply Forall_impl_In; [|eapply H3]; intros...
        + rewrite Forall_map in *. unfold rename_in_reset.
          rewrite Forall_map. eapply Forall_impl; [|eapply H4]; intros (?&?) (?&?).
          simpl in *...
        + rewrite Forall_map in *. unfold rename_in_reset.
          rewrite Forall_map. eapply Forall_impl; [|eapply H5]; intros (?&?) ?.
          simpl in *...
      - constructor...
        + rewrite rename_in_exp_typeof; auto.
        + rewrite rename_in_exp_typeof; auto.
        + rewrite Forall_map in *. unfold rename_in_reset.
          rewrite Forall_map. eapply Forall_impl; [|eapply H3]; intros (?&?) (?&?).
          simpl in *...
        + rewrite Forall_map in *. unfold rename_in_reset.
          rewrite Forall_map. eapply Forall_impl; [|eapply H4]; intros (?&?) ?.
          simpl in *...
    Qed.

  End rename.

  Lemma remove_dup_regs_once_wt : forall G inouts vars eqs,
      NoDupMembers (inouts++idty vars) ->
      NoDup (vars_defined eqs) ->
      (forall x eq, In eq eqs -> In x (var_defined eq) -> is_fby eq = true -> ~InMembers x inouts) ->
      Forall (wt_equation G (inouts++idty vars)) eqs ->
      let (vars', eqs') := remove_dup_regs_eqs_once vars eqs in
      Forall (wt_equation G (inouts++idty vars')) eqs'.
  Proof.
    intros * Hndv Hnd Hinouts Hwt.
    destruct (remove_dup_regs_eqs_once _) eqn:Honce. inv Honce.
    unfold subst_and_filter_equations.
    rewrite Forall_map, Forall_filter. eapply Forall_impl_In; eauto.
    intros ? Hineq Hwt' Hfilter.
    eapply rename_in_equation_wt; [| | |eauto].
    - intros * Hfind Hin.
      assert (~InMembers x inouts) as Hnx.
      { apply find_duplicates_spec in Hfind as (?&?&?&?&?&Hin1&_&_).
        eapply Hinouts in Hin1; eauto. simpl; auto. }
      assert (~InMembers y inouts) as Hny.
      { apply find_duplicates_spec in Hfind as (?&?&?&?&?&_&Hin2&_).
        eapply Hinouts in Hin2; eauto. simpl; auto. }
      rewrite in_app_iff in *. destruct Hin as [Hin|Hin].
      1:(exfalso; eauto using In_InMembers).
      right.
      rewrite In_idty_exists in *. destruct Hin as (?&Hin).
      assert (Hfind':=Hfind).
      eapply find_duplicates_spec in Hfind as (?&?&?&?&?&Hwt1&Hwt2&_).
      eapply Forall_forall in Hwt1; eauto. eapply Forall_forall in Hwt2; eauto.
      inv Hwt1. inv Hwt2.
      rewrite in_app_iff in H4, H10.
      destruct H4 as [Hin1|Hin1], H10 as [Hin2|Hin2].
      1-3:(exfalso; eauto using In_InMembers).
      eapply In_idty_exists in Hin1 as (?&Hin1).
      eapply In_idty_exists in Hin2 as (ck&Hin2).
      eapply NoDupMembers_det in Hin; eauto. 2:eapply NoDupMembers_app_r, NoDupMembers_idty in Hndv; eauto.
      inv Hin. exists (rename_in_clock (find_duplicates eqs) ck); simpl.
      unfold subst_and_filter_vars.
      erewrite in_map_iff. exists (y, (typeof x3, ck)); split; auto.
      eapply filter_In; split; auto.
      eapply find_duplicates_irrefl in Hfind'; eauto.
      apply Env.Props.P.F.not_mem_in_iff in Hfind'. rewrite Hfind'; auto.
    - intros * Hfind Hin.
      rewrite in_app_iff in *. destruct Hin as [Hin|Hin]; auto.
      right.
      rewrite In_idty_exists in *. destruct Hin as (ck&Hin).
      exists (rename_in_clock (find_duplicates eqs) ck).
      apply in_map_iff. exists (x, (ty, ck)); split; auto.
      apply filter_In; split; auto.
      rewrite Env.mem_find, Hfind; auto.
    - intros * Hindef.
      destruct (Env.find _ _) eqn:Hfind; auto. exfalso.
      apply Env.find_In in Hfind.
      assert (Hisfby:=Hindef). eapply find_duplicates_is_fby in Hisfby; eauto.
      destruct a; simpl in *; try congruence.
      inv Hindef; auto.
      rewrite Bool.negb_true_iff, <-Env.Props.P.F.not_mem_in_iff in Hfilter.
      congruence.
  Qed.

  Lemma remove_dup_regs_eqs_wt : forall G inouts vars eqs vars' eqs',
      NoDupMembers (inouts ++ idty vars) ->
      NoDup (vars_defined eqs) ->
      (forall x eq, In eq eqs -> In x (var_defined eq) -> is_fby eq = true -> ~InMembers x inouts) ->
      Forall (wt_equation G (inouts ++ idty vars)) eqs ->
      remove_dup_regs_eqs vars eqs = (vars', eqs') ->
      Forall (wt_equation G (inouts ++ idty vars')) eqs'.
  Proof.
    intros until eqs.
    functional induction (remove_dup_regs_eqs vars eqs); intros * Hndv Hnd Hinouts Hwt Hrem.
    - eapply remove_dup_regs_once_wt in Hwt; eauto.
      rewrite e in Hwt. inv e.
      eapply IHp; eauto using subst_and_filter_equations_NoDup.
      + clear - Hndv.
        apply NoDupMembers_app; eauto using NoDupMembers_app_l.
        * apply NoDupMembers_app_r, NoDupMembers_idty in Hndv.
          apply NoDupMembers_idty, subst_and_filter_vars_NoDupMembers; auto.
        * intros ? Hin.
          eapply NoDupMembers_app_InMembers in Hndv; eauto.
          contradict Hndv.
          rewrite InMembers_idty in *; eauto using subst_and_filter_vars_InMembers.
      + intros ?? Hin1 Hin2 Hisfby.
        eapply in_map_iff in Hin1 as (?&?&Hin1); subst. apply in_filter in Hin1.
        destruct x0; simpl in *; try congruence. destruct Hin2 as [Hin2|Hin2]; inv Hin2.
        eapply Hinouts; eauto. simpl; auto.
    - inv Hrem; auto.
  Qed.

  Lemma remove_dup_regs_node_wt : forall G n,
      wt_node G n ->
      wt_node (remove_dup_regs G) (remove_dup_regs_node n).
  Proof.
    intros * (Hwteq&Henums).
    constructor.
    - simpl.
      destruct (remove_dup_regs_eqs _ _) as (vars'&eqs') eqn:Hrem.
      eapply remove_dup_regs_eqs_wt with (G:=G) (inouts:=idty (n_in n ++ n_out n)) (vars:=(n_vars n)) in Hrem; eauto.
      + eapply Forall_impl; [|eauto]. intros ? Hwt.
        eapply global_iface_eq_wt_eq; eauto using remove_dup_regs_iface_eq.
        eapply wt_equation_incl; eauto. clear -n. intros ? Hin.
        repeat rewrite idty_app in *. repeat rewrite <-filter_app in Hin.
        repeat rewrite in_app_iff in *.
        destruct Hin as [[Hin|Hin]|Hin]; auto.
      + rewrite <-idty_app, <-app_assoc, (Permutation.Permutation_app_comm (n_out _)).
        apply NoDupMembers_idty, n_nodup.
      + apply NoDup_var_defined_n_eqs.
      + intros. intros contra. rewrite idty_app, InMembers_app in contra. destruct contra as [contra|contra].
        * rewrite InMembers_idty in contra.
          assert (In x (vars_defined (n_eqs n))) as Hdef.
          { unfold vars_defined. apply in_flat_map.
            eexists; split; eauto. }
          rewrite n_defd in Hdef. apply fst_InMembers in Hdef.
          eapply NoDupMembers_app_InMembers in contra. eapply contra; eauto.
          eapply n_nodup.
        * rewrite fst_InMembers, map_fst_idty in contra.
          apply n_vout in contra. apply contra.
          unfold vars_defined. apply in_flat_map.
          eexists; split; eauto.
          apply filter_In; auto.
      + eapply Forall_impl; [|eauto]. intros ? Hwt.
        eapply wt_equation_incl; eauto. clear -n. intros (?&?) Hin.
        rewrite <-idty_app, <-app_assoc, (Permutation.Permutation_app_comm (n_out _)).
        assumption.
    - intros; simpl in *. eapply Henums with (x:=x).
      repeat rewrite idty_app, in_app_iff in *.
      destruct H as [?|[Hin|?]]; auto.
      right; left.
      clear - Hin.
      revert Hin.
      functional induction (remove_dup_regs_eqs (n_vars n) (n_eqs n)); intros; auto.
      apply IHp in Hin.
      inv e. clear - Hin.
      induction vars as [|(?&?&?)]; simpl in *; auto.
      unfold subst_and_filter_vars in Hin; simpl in Hin.
      destruct (negb _); simpl; auto.
      inv Hin; auto.
  Qed.

  Theorem remove_dup_regs_wt : forall G,
      wt_global G ->
      wt_global (remove_dup_regs G).
  Proof.
    intros.
    eapply CommonTyping.transform_units_wt_program; eauto.
    intros. eapply remove_dup_regs_node_wt; eauto.
  Qed.

End DRRTYPING.

Module DrrTypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CESyn : CESYNTAX        Ids Op OpAux Cks)
       (CETyp : CETYPING        Ids Op OpAux Cks CESyn)
       (Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Typ   : NLTYPING        Ids Op OpAux Cks CESyn Syn Ord CETyp)
       (DRR   : DRR             Ids Op OpAux Cks CESyn Syn)
  <: DRRTYPING Ids Op OpAux Cks CESyn CETyp Syn Ord Typ DRR.
  Include DRRTYPING Ids Op OpAux Cks CESyn CETyp Syn Ord Typ DRR.
End DrrTypingFun.
