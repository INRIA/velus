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
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.DupRegRem.DRR.

Module Type DRRCLOCKING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Import CEClo : CECLOCKING      Ids Op OpAux Cks CESyn)
       (Import Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Import Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Import Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (Import IsD   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Import Clo   : NLCLOCKING      Ids Op OpAux Cks CESyn Syn Ord Mem IsD CEClo)
       (Import DRR   : DRR             Ids Op OpAux Cks CESyn Syn).

  Section rename.
    Variable sub : Env.t ident.

    Variable inouts : list (ident * (clock * bool)).
    Variable vars vars' : list (ident * (clock * bool)).

    Hypothesis Hsub : forall x y ck islast,
        Env.find x sub = Some y ->
        In (x, (ck, islast)) (inouts ++ vars) ->
        In (y, (rename_in_clock sub ck, islast)) (inouts ++ vars').

    Hypothesis Hnsub : forall x ck islast,
        Env.find x sub = None ->
        In (x, (ck, islast)) (inouts ++ vars) ->
        In (x, (rename_in_clock sub ck, islast)) (inouts ++ vars').

    Hypothesis Hlast : forall x ck,
        In (x, (ck, true)) (inouts ++ vars) ->
        In (x, (rename_in_clock sub ck, true)) (inouts ++ vars').

    Lemma rename_in_var_wc : forall x ck islast,
        In (x, (ck, islast)) (inouts ++ vars) ->
        In (rename_in_var sub x, (rename_in_clock sub ck, islast)) (inouts ++ vars').
    Proof.
      intros * Hin.
      unfold rename_in_var.
      destruct (Env.find _ _) eqn:Hfind; eauto.
    Qed.

    Variable (G : global).

    Lemma rename_in_clock_wc : forall ck,
        wc_clock (idfst (inouts ++ vars)) ck ->
        wc_clock (idfst (inouts ++ vars')) (rename_in_clock sub ck).
    Proof.
      induction ck; intros * Hwc; inv Hwc; auto with clocks.
      simpl. constructor; eauto.
      solve_In; [|eapply rename_in_var_wc; eauto]. reflexivity.
    Qed.

    Lemma rename_in_exp_wc : forall e ck,
        wc_exp (inouts ++ vars) e ck ->
        wc_exp (inouts ++ vars') (rename_in_exp sub e) (rename_in_clock sub ck).
    Proof.
      intros * Hwc; induction Hwc;
        simpl; econstructor; eauto using rename_in_var_wc.
    Qed.

    Lemma rename_in_cexp_wc : forall e ck,
        wc_cexp (inouts ++ vars) e ck ->
        wc_cexp (inouts ++ vars') (rename_in_cexp sub e) (rename_in_clock sub ck).
    Proof.
      induction e using cexp_ind2'; intros * Hwc; inv Hwc;
        simpl; econstructor; eauto using rename_in_var_wc, rename_in_exp_wc.
      - contradict H5.
        eapply map_eq_nil; eauto.
      - rewrite map_length, Forall2_map_2.
        eapply Forall2_impl_In; [|eauto]; intros; simpl in *.
        eapply Forall_forall in H; eauto. eapply H in H2; eauto.
      - contradict H4.
        eapply map_eq_nil; eauto.
      - intros ? Hin.
        eapply in_map_iff in Hin as (?&Hopt&Hin).
        eapply option_map_inv in Hopt as (?&?&?); subst.
        eapply Forall_forall in H; eauto. simpl in *.
        eapply H in H7; eauto.
    Qed.

    Lemma rename_in_rhs_wc : forall e ck,
        wc_rhs (inouts ++ vars) e ck ->
        wc_rhs (inouts ++ vars') (rename_in_rhs sub e) (rename_in_clock sub ck).
    Proof.
      intros * Hwc; inv Hwc; econstructor; simpl_Forall; eauto using rename_in_exp_wc, rename_in_cexp_wc.
    Qed.

    Lemma instck_rename_in_clock : forall ck sub0 bck ck',
      instck bck sub0 ck = Some ck' ->
      instck (rename_in_clock sub bck) (fun x => option_map (fun x1 => rename_in_var sub x1) (sub0 x)) ck =
      Some (rename_in_clock sub ck').
    Proof.
      induction ck; intros * Hinst1; simpl in *.
      - inv Hinst1; auto.
      - destruct (instck bck sub0 ck) eqn:Hinst. 2:inv Hinst1.
        eapply IHck in Hinst. rewrite Hinst.
        destruct (sub0 i); inv Hinst1; simpl. reflexivity.
    Qed.

    Local Hint Resolve rename_in_var_wc rename_in_clock_wc rename_in_exp_wc rename_in_cexp_wc rename_in_rhs_wc : nlclocking.

    Lemma rename_in_equation_wc : forall equ,
        (forall x, In x (var_defined equ) -> Env.find x sub = None) ->
        wc_equation G (inouts ++ vars) equ ->
        wc_equation G (inouts ++ vars') (rename_in_equation sub equ).
    Proof with eauto with nlclocking.
      intros * Hdef Hwc; inv Hwc; simpl in *...
      - econstructor...
      - econstructor...
        unfold rename_in_reset. simpl_Forall...
      - eapply CEqApp with (sub:=fun x => option_map (fun x => rename_in_var sub x) (sub0 x)) (* ? *)...
        + simpl_Forall.
          repeat esplit...
          * inv H5; simpl; constructor.
          * apply instck_rename_in_clock; auto.
        + simpl_Forall.
          repeat (esplit; eauto).
          * rewrite H5; simpl.
            unfold rename_in_var. rewrite Hdef; eauto.
          * eapply instck_rename_in_clock; eauto.
        + unfold rename_in_reset. simpl_Forall...
      - constructor...
        unfold rename_in_reset. simpl_Forall...
    Qed.

  End rename.

  Definition idck (vars : list (ident * (type * clock * bool))) :=
    map (fun x => (fst x, (snd (fst (snd x)), snd (snd x)))) vars.

  Lemma remove_dup_regs_once_wc : forall G inouts vars eqs,
      NoDup (map fst inouts ++ map fst vars) ->
      NoDup (vars_defined eqs) ->
      Forall (fun x => ~InMembers x inouts) (vars_defined (filter is_fby eqs)) ->
      Forall (fun '(x, (_, _, islast)) => islast = true -> ~In x (vars_defined (filter is_fby eqs))) vars ->
      wc_env (idfst inouts) ->
      Forall (wc_equation G (inouts ++ idck vars)) eqs ->
      let (vars', eqs') := remove_dup_regs_eqs_once vars eqs in
      Forall (wc_equation G (inouts ++ idck vars')) eqs'.
  Proof.
    intros * Hndv Hnd Hinouts Hlasts Hwinouts Hwc.
    destruct (remove_dup_regs_eqs_once _ _) eqn:Honce. inv Honce.
    unfold subst_and_filter_equations.
    rewrite Forall_map, Forall_filter. eapply Forall_impl_In; eauto.
    intros ? Hineq Hwc' Hfilter.
    assert (Forall (fun '(x, (ck, islast)) => rename_in_clock (find_duplicates eqs) ck = ck) inouts) as Idem.
    { simpl_Forall.
      assert (forall x, Env.In x (find_duplicates eqs) -> ~InMembers x inouts) as Hninouts.
      { intros ? Hindup.
        eapply find_duplicates_In in Hindup. now simpl_Forall.
      }
      eapply wc_env_var in Hwinouts; [|solve_In]; simpl in *.
      clear - Hwinouts Hninouts.
      induction Hwinouts; simpl; auto.
      f_equal; auto.
      unfold rename_in_var. destruct (Env.find _ _) eqn:Hfind; auto.
      apply Env.find_In, Hninouts in Hfind.
      exfalso. eapply Hfind. solve_In.
    }
    eapply rename_in_equation_wc; [| | | |eauto].
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
      rewrite in_app_iff in H2, H3.
      destruct H2 as [Hin1|Hin1], H3 as [Hin2|Hin2].
      1-3:(exfalso; eauto using In_InMembers).
      simpl_In.
      eapply NoDupMembers_det in Hin1; eauto. 2:apply fst_NoDupMembers; eauto using NoDup_app_r.
      inv Hin1.
      unfold idck, subst_and_filter_vars. solve_In.
      eapply find_duplicates_irrefl in Hfind'; eauto.
      apply Env.Props.P.F.not_mem_in_iff in Hfind'. rewrite Hfind'; auto.
    - intros * Hfind Hin.
      rewrite in_app_iff in *. destruct Hin as [Hin|Hin]; auto.
      + left. simpl_Forall. now rewrite Idem.
      + right. unfold idck, subst_and_filter_vars. solve_In.
        rewrite Env.mem_find, Hfind; auto.
    - intros * In.
      rewrite in_app_iff in *. destruct In as [In|In]; auto.
      + left. simpl_Forall. now rewrite Idem.
      + right. unfold idck, subst_and_filter_vars. solve_In.
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

  Lemma remove_dup_regs_once_wc_env : forall G inouts vars eqs vars' eqs',
      NoDup (map fst inouts ++ map fst vars) ->
      NoDup (vars_defined eqs) ->
      Forall (fun x => ~InMembers x inouts) (vars_defined (filter is_fby eqs)) ->
      wc_env (idfst inouts) ->
      wc_env (idfst (inouts ++ idck vars)) ->
      Forall (wc_equation G (inouts ++ idck vars)) eqs ->
      remove_dup_regs_eqs_once vars eqs = (vars', eqs') ->
      wc_env (idfst (inouts ++ idck vars')).
  Proof.
    intros * Hndv Hnd Hinouts Hwc1 Hwc2 Hwceq Hrem.
    inv Hrem. unfold idfst. rewrite map_app.
    eapply Forall_app; split.
    - eapply Forall_impl; [|eauto]; intros (?&?) ?.
      eapply Cks.wc_clock_incl; eauto. apply incl_appl, incl_refl.
    - unfold idfst, idck in Hwc2. rewrite map_app in Hwc2. eapply Forall_app in Hwc2 as (?&Hwc2).
      simpl_Forall. simpl_In. simpl_Forall.
      rewrite <-map_app in *.
      eapply rename_in_clock_wc; eauto; intros * Hfind Hin'.
      + assert (~InMembers x inouts) as Hnx.
        { apply Env.find_In, find_duplicates_In in Hfind.
          now simpl_Forall. }
        assert (~InMembers y inouts) as Hny.
        { apply find_duplicates_spec in Hfind as (?&?&?&?&?&_&Hin2&_).
          eapply Forall_forall in Hinouts; eauto. unfold vars_defined; solve_In; simpl; auto. }
        rewrite in_app_iff in *. destruct Hin' as [|].
        1:(exfalso; eauto using In_InMembers).
        right.
        assert (Hfind':=Hfind).
        eapply find_duplicates_spec in Hfind as (?&?&?&?&?&Hwt1&Hwt2&_).
        eapply Forall_forall in Hwt1; eauto. eapply Forall_forall in Hwt2; eauto.
        inv Hwt1. inv Hwt2.
        rewrite in_app_iff in H4, H5.
        destruct H4 as [Hin1|Hin1], H5 as [Hin2|Hin2].
        1-3:(exfalso; eauto using In_InMembers).
        simpl_In.
        eapply NoDupMembers_det in Hin0; eauto. 2:apply fst_NoDupMembers; eauto using NoDup_app_r.
        inv Hin0.
        unfold idck, subst_and_filter_vars. solve_In.
        eapply find_duplicates_irrefl in Hfind'; eauto.
        apply Env.Props.P.F.not_mem_in_iff in Hfind'. rewrite Hfind'; auto.
      + rewrite in_app_iff in *. destruct Hin' as [|]; auto.
        * replace (rename_in_clock _ ck) with ck; auto.
          simpl_Forall.
          assert (forall x, Env.In x (find_duplicates eqs) -> ~InMembers x inouts) as Hninouts.
          { intros ? Hindup.
            eapply find_duplicates_In in Hindup. now simpl_Forall.
          }
          eapply wc_env_var in Hwc1; [|solve_In]; simpl in *.
          clear - Hwc1 Hninouts.
          induction Hwc1; simpl; auto.
          f_equal; auto.
          unfold rename_in_var. destruct (Env.find _ _) eqn:Hfind; auto.
          apply Env.find_In, Hninouts in Hfind.
          exfalso. eapply Hfind. solve_In.
        * right.
          unfold idck, subst_and_filter_vars. solve_In.
          rewrite Env.mem_find, Hfind; auto.
  Qed.

  Lemma remove_dup_regs_eqs_wc : forall G inouts vars eqs vars' eqs',
      NoDup (map fst inouts ++ map fst vars) ->
      NoDup (vars_defined eqs) ->
      Forall (fun x => ~InMembers x inouts) (vars_defined (filter is_fby eqs)) ->
      Forall (fun '(x, (_, _, islast)) => islast = true -> ~In x (vars_defined (filter is_fby eqs))) vars ->
      wc_env (idfst inouts) ->
      wc_env (idfst (inouts ++ idck vars)) ->
      Forall (wc_equation G (inouts ++ idck vars)) eqs ->
      remove_dup_regs_eqs vars eqs = (vars', eqs') ->
      Forall (wc_equation G (inouts ++ idck vars')) eqs' /\ wc_env (idfst (inouts ++ idck vars')).
  Proof.
    intros until eqs.
    functional induction (remove_dup_regs_eqs vars eqs); intros * Hndv Hnd Hinouts Hlasts Hwinouts Hwenv Hwc Hrem.
    - eapply remove_dup_regs_once_wc_env in Hwenv; eauto.
      eapply remove_dup_regs_once_wc in Hwc; eauto.
      rewrite e in Hwc. inv e.
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

  Definition idck' (vars : list (ident * (type * clock))) :=
    map (fun x => (fst x, (snd (snd x), false))) vars.

  Lemma remove_dup_regs_node_wc : forall G n,
      wc_node G n ->
      wc_node (remove_dup_regs G) (remove_dup_regs_node n).
  Proof.
    intros * (Hwci&Hwco&Hwcv&Hwceq).
    assert (NoDup (map fst (idck' (n_in n ++ n_out n)) ++ map fst (n_vars n))) as Nd.
    { unfold idck'.
      rewrite map_map, map_app, <-app_assoc, Permutation.Permutation_app_comm with (l':=map _ (n_vars _)).
      apply n_nodup. }
    destruct (remove_dup_regs_eqs (n_vars n) (n_eqs n)) as (vars'&eqs') eqn:Hrem.
    destruct (remove_dup_regs_eqs_wc G (idck' (n_in n ++ n_out n)) (n_vars n) (n_eqs n) vars' eqs')
      as (Hwc'&Hwenv'); eauto.
    - apply NoDup_var_defined_n_eqs.
    - simpl_Forall. rewrite fst_InMembers. intros In'.
      eapply NoDup_app_In; eauto using vars_defined_fby_vars.
    - simpl_Forall. intros Eq; subst.
      eapply n_lastfby.
      rewrite n_lastd1. solve_In.
    - unfold idfst, idck'. now rewrite map_map.
    - clear - Hwcv. unfold idck', idck. simpl_app.
      repeat rewrite map_map in *. simpl in *.
      now rewrite Permutation.Permutation_app_comm with (l':=map _ (n_vars _)).
    - simpl_Forall.
      unfold idck', idck.
      erewrite map_ext with (l:=_++_), map_ext with (l:=n_vars _); eauto.
      all:intros; destruct_conjs; auto.
    - repeat (split; auto).
      1,2:simpl; rewrite Hrem.
      + clear - Hwenv'. unfold idck', idck in *. simpl_app.
      repeat rewrite map_map in *. simpl in *.
      now rewrite Permutation.Permutation_app_comm with (l':=map _ (n_out _)).
      + simpl_Forall.
        eapply global_iface_eq_wc_eq; eauto using remove_dup_regs_iface_eq.
        clear - Hwc'. unfold idck', idck in *.
        erewrite map_ext with (l:=_++_), map_ext with (l:=vars'); eauto.
        all:intros; destruct_conjs; auto.
  Qed.

  Theorem remove_dup_regs_wc : forall G,
      wc_global G ->
      wc_global (remove_dup_regs G).
  Proof.
    intros.
    unfold wc_global in *; simpl.
    induction H; simpl; constructor; auto.
    eapply remove_dup_regs_node_wc in H; auto.
  Qed.

End DRRCLOCKING.

Module DrrClockingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CESyn : CESYNTAX        Ids Op OpAux Cks)
       (CEClo : CECLOCKING      Ids Op OpAux Cks CESyn)
       (Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (IsD   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Clo   : NLCLOCKING      Ids Op OpAux Cks CESyn Syn Ord Mem IsD CEClo)
       (DRR   : DRR             Ids Op OpAux Cks CESyn Syn)
  <: DRRCLOCKING Ids Op OpAux Cks CESyn CEClo Syn Ord Mem IsD Clo DRR.
  Include DRRCLOCKING Ids Op OpAux Cks CESyn CEClo Syn Ord Mem IsD Clo DRR.
End DrrClockingFun.
