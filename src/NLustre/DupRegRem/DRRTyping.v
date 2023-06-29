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

    Variable inouts : list (ident * (type * bool)).
    Variable vars vars' : list (ident * (type * bool)).

    Hypothesis Hsub : forall x y ty islast,
        Env.find x sub = Some y ->
        In (x, (ty, islast)) (inouts ++ vars) ->
        In (y, (ty, islast)) (inouts ++ vars').

    Hypothesis Hnsub : forall x ty islast,
        Env.find x sub = None ->
        In (x, (ty, islast)) (inouts ++ vars) ->
        In (x, (ty, islast)) (inouts ++ vars').

    Hypothesis Hlast : forall x ty,
        In (x, (ty, true)) (inouts ++ vars) ->
        In (x, (ty, true)) (inouts ++ vars').

    Lemma rename_in_var_wt : forall x ty islast,
        In (x, (ty, islast)) (inouts++vars) ->
        In (rename_in_var sub x, (ty, islast)) (inouts++vars').
    Proof.
      intros * Hin.
      unfold rename_in_var.
      destruct (Env.find _ _) eqn:Hfind; eauto.
    Qed.
    Local Hint Resolve rename_in_var_wt : nltyping.

    Variable (G : global).

    Lemma rename_in_clock_wt : forall ck,
        wt_clock G.(types) (inouts++vars) ck ->
        wt_clock G.(types) (inouts++vars') (rename_in_clock sub ck).
    Proof.
      induction ck; intros * Hwt; inv Hwt; auto with nltyping.
      simpl. econstructor; eauto with nltyping.
    Qed.

    Lemma rename_in_exp_wt : forall e,
        wt_exp G.(types) (inouts++vars) e ->
        wt_exp G.(types) (inouts++vars') (rename_in_exp sub e).
    Proof.
      intros * Hwt; induction Hwt;
        simpl; econstructor; eauto with nltyping.
      1,2:repeat rewrite rename_in_exp_typeof; auto.
    Qed.

    Lemma rename_in_cexp_wt : forall e,
        wt_cexp G.(types) (inouts++vars) e ->
        wt_cexp G.(types) (inouts++vars') (rename_in_cexp sub e).
    Proof.
      induction e using cexp_ind2'; intros * Hwt; inv Hwt;
        simpl; econstructor; eauto using rename_in_var_wt, rename_in_exp_wt.
      1,5:rewrite map_length; auto.
      - simpl_Forall.
        rewrite rename_in_cexp_typeofc; auto.
      - simpl_Forall. eauto.
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

    Lemma rename_in_rhs_wt : forall e,
        wt_rhs G.(types) G.(externs) (inouts++vars) e ->
        wt_rhs G.(types) G.(externs) (inouts++vars') (rename_in_rhs sub e).
    Proof.
      intros * Hwt; inv Hwt; econstructor; eauto;
        simpl_Forall; eauto using rename_in_exp_wt, rename_in_cexp_wt.
      now rewrite rename_in_exp_typeof.
    Qed.

    Local Hint Resolve rename_in_var_wt rename_in_clock_wt rename_in_exp_wt rename_in_cexp_wt rename_in_rhs_wt : nltyping.

    Lemma rename_in_equation_wt : forall equ,
        (forall x, In x (var_defined equ) -> Env.find x sub = None) ->
        wt_equation G (inouts++vars) equ ->
        wt_equation G (inouts++vars') (rename_in_equation sub equ).
    Proof with eauto with nltyping.
      intros * Hdef Hwt; inv Hwt; simpl in *.
      - econstructor...
        rewrite rename_in_rhs_typeofr; eauto.
      - econstructor...
        unfold rename_in_reset. simpl_Forall.
        repeat (split; eauto with nltyping).
        simpl_In. eapply rename_in_var_wt in Hin; solve_In.
      - econstructor; eauto; simpl_Forall...
        + now rewrite rename_in_exp_typeof.
        + unfold rename_in_reset in *. simpl_In. simpl_Forall; repeat (split; eauto with nltyping).
          simpl_In. eapply rename_in_var_wt in Hin0; solve_In.
        + unfold rename_in_reset in *. simpl_In. simpl_Forall...
      - constructor...
        + rewrite rename_in_exp_typeof; auto.
        + rewrite rename_in_exp_typeof; auto.
        + unfold rename_in_reset. simpl_Forall; repeat (split; eauto with nltyping).
          simpl_In. eapply rename_in_var_wt in Hin; solve_In.
    Qed.

  End rename.

  Definition idty (vars : list (ident * (type * clock * bool))) :=
    map (fun x => (fst x, (fst (fst (snd x)), snd (snd x)))) vars.

  Lemma remove_dup_regs_once_wt : forall G inouts vars eqs,
      NoDup (map fst inouts++map fst vars) ->
      NoDup (vars_defined eqs) ->
      Forall (fun x => ~InMembers x inouts) (vars_defined (filter is_fby eqs)) ->
      Forall (fun '(x, (_, _, islast)) => islast = true -> ~In x (vars_defined (filter is_fby eqs))) vars ->
      Forall (wt_equation G (inouts++idty vars)) eqs ->
      let (vars', eqs') := remove_dup_regs_eqs_once vars eqs in
      Forall (wt_equation G (inouts++idty vars')) eqs'.
  Proof.
    intros * Hndv Hnd Hinouts Hlasts Hwt.
    destruct (remove_dup_regs_eqs_once _) eqn:Honce. inv Honce.
    unfold subst_and_filter_equations.
    rewrite Forall_map, Forall_filter. eapply Forall_impl_In; eauto.
    intros ? Hineq Hwt' Hfilter.
    eapply rename_in_equation_wt; [| | | |eauto].
    - intros * Hfind Hin.
      assert (~InMembers x inouts) as Hnx.
      { apply find_duplicates_spec in Hfind as (?&?&?&?&?&Hin1&_&_).
        apply Forall_flat_map, Forall_filter in Hinouts. simpl_Forall.
        specialize (Hinouts eq_refl). simpl_Forall. auto. }
      assert (~InMembers y inouts) as Hny.
      { apply find_duplicates_spec in Hfind as (?&?&?&?&?&_&Hin2&_).
        apply Forall_flat_map, Forall_filter in Hinouts. simpl_Forall.
        specialize (Hinouts eq_refl). simpl_Forall. auto. }
      rewrite in_app_iff in *. destruct Hin as [Hin|Hin].
      1:(exfalso; eauto using In_InMembers).
      right.
      assert (Hfind':=Hfind).
      eapply find_duplicates_spec in Hfind as (?&?&?&?&?&Hwt1&Hwt2&_).
      eapply Forall_forall in Hwt1; eauto. eapply Forall_forall in Hwt2; eauto.
      inv Hwt1. inv Hwt2.
      rewrite in_app_iff in H4, H9.
      destruct H4 as [Hin1|Hin1], H9 as [Hin2|Hin2].
      1-3:(exfalso; eauto using In_InMembers).
      simpl_In.
      eapply NoDupMembers_det in Hin1; eauto. 2:apply fst_NoDupMembers; eauto using NoDup_app_r.
      inv Hin1.
      unfold idty, subst_and_filter_vars. solve_In.
      eapply find_duplicates_irrefl in Hfind'; eauto.
      apply Env.Props.P.F.not_mem_in_iff in Hfind'. rewrite Hfind'; auto.
    - intros * Hfind Hin.
      rewrite in_app_iff in *. destruct Hin as [Hin|Hin]; auto.
      right. unfold idty, subst_and_filter_vars in *. solve_In.
      rewrite Env.mem_find, Hfind; auto.
    - intros * In.
      rewrite in_app_iff in *. destruct In as [In|In]; auto.
      right. unfold idty, subst_and_filter_vars. solve_In.
      simpl_Forall.
      apply Bool.negb_true_iff, Env.Props.P.F.not_mem_in_iff.
      intros ?; eapply Hlasts; eauto using find_duplicates_In.
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
      NoDup (map fst inouts ++ map fst vars) ->
      NoDup (vars_defined eqs) ->
      Forall (fun x => ~InMembers x inouts) (vars_defined (filter is_fby eqs)) ->
      Forall (fun '(x, (_, _, islast)) => islast = true -> ~In x (vars_defined (filter is_fby eqs))) vars ->
      Forall (wt_equation G (inouts ++ idty vars)) eqs ->
      remove_dup_regs_eqs vars eqs = (vars', eqs') ->
      Forall (wt_equation G (inouts ++ idty vars')) eqs'.
  Proof.
    intros until eqs.
    functional induction (remove_dup_regs_eqs vars eqs); intros * Hndv Hnd Hinouts Hlasts Hwt Hrem.
    - eapply remove_dup_regs_once_wt in Hwt; eauto.
      rewrite e in Hwt. inv e.
      eapply IHp; eauto using subst_and_filter_equations_NoDup.
      + clear - Hndv.
        apply NoDup_app'; eauto using NoDup_app_l.
        * apply NoDup_app_r in Hndv. rewrite <-fst_NoDupMembers in *.
          apply subst_and_filter_vars_NoDupMembers; auto.
        * simpl_Forall.
          eapply NoDup_app_In in Hndv; [|solve_In].
          contradict Hndv. rewrite <-fst_InMembers in *.
          eauto using subst_and_filter_vars_InMembers.
      + eapply Forall_incl; [|eapply remove_dup_regs_eqs_once_fby_incl with (vars:=vars)]; eauto.
      + unfold subst_and_filter_vars. simpl_Forall. simpl_In. simpl_Forall.
        intros L In. eapply Hlasts; eauto.
        eapply remove_dup_regs_eqs_once_fby_incl with (vars:=vars); eauto.
    - inv Hrem; auto.
  Qed.

  Definition idty' (vars : list (ident * (type * clock))) :=
    map (fun x => (fst x, (fst (snd x), false))) vars.

  Lemma remove_dup_regs_node_wt : forall G n,
      wt_node G n ->
      wt_node (remove_dup_regs G) (remove_dup_regs_node n).
  Proof.
    intros * (Hwteq&Henums).
    assert (NoDup (map fst (idty' (n_in n ++ n_out n)) ++ map fst (n_vars n))) as Nd.
    { unfold idty'.
      rewrite map_map, map_app, <-app_assoc, Permutation.Permutation_app_comm with (l':=map _ (n_vars _)).
      apply n_nodup. }
    constructor.
    - simpl.
      destruct (remove_dup_regs_eqs _ _) as (vars'&eqs') eqn:Hrem.
      eapply remove_dup_regs_eqs_wt with (G:=G) (inouts:=idty' (n_in n ++ n_out n)) (vars:=(n_vars n)) in Hrem; eauto.
      + simpl_Forall.
        eapply global_iface_eq_wt_eq; eauto using remove_dup_regs_iface_eq.
        unfold idty', idty in Hrem.
        erewrite map_ext with (l:=_++_), map_ext with (l:=vars'); eauto.
        all:intros; destruct_conjs; auto.
      + apply NoDup_var_defined_n_eqs.
      + simpl_Forall. rewrite fst_InMembers. intros In'.
        eapply NoDup_app_In; eauto using vars_defined_fby_vars.
      + simpl_Forall. intros Eq; subst.
        eapply n_lastfby.
        rewrite n_lastd1. solve_In.
      + simpl_Forall.
        unfold idty', idty.
        erewrite map_ext with (l:=_++_), map_ext with (l:=n_vars _); eauto.
        all:intros; destruct_conjs; auto.
    - intros; simpl in *. eapply Henums with (x:=x).
      repeat rewrite idfst_app, in_app_iff in *.
      destruct H as [?|[Hin|?]]; auto.
      right; left.
      clear - Hin. revert Hin.
      functional induction (remove_dup_regs_eqs (n_vars n) (n_eqs n)); intros; auto.
      apply IHp in Hin; auto.
      inv e. clear - Hin.
      unfold subst_and_filter_vars in Hin. solve_In.
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
