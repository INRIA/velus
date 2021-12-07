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

    Variable inouts : list (ident * clock).
    Variable vars vars' : list (ident * clock).

    Hypothesis Hsub : forall x y ck,
        Env.find x sub = Some y ->
        In (x, ck) (inouts ++ vars) ->
        In (y, rename_in_clock sub ck) (inouts ++ vars').

    Hypothesis Hnsub : forall x ck,
        Env.find x sub = None ->
        In (x, ck) (inouts ++ vars) ->
        In (x, rename_in_clock sub ck) (inouts ++ vars').

    Lemma rename_in_var_wc : forall x ck,
        In (x, ck) (inouts ++ vars) ->
        In (rename_in_var sub x, rename_in_clock sub ck) (inouts ++ vars').
    Proof.
      intros * Hin.
      unfold rename_in_var.
      destruct (Env.find _ _) eqn:Hfind; eauto.
    Qed.

    Variable (G : global).

    Lemma rename_in_clock_wc : forall ck,
        wc_clock (inouts ++ vars) ck ->
        wc_clock (inouts ++ vars') (rename_in_clock sub ck).
    Proof.
      induction ck; intros * Hwc; inv Hwc; auto with clocks.
      simpl. constructor; eauto using rename_in_var_wc with clocks.
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

    Local Hint Resolve rename_in_var_wc rename_in_clock_wc rename_in_exp_wc rename_in_cexp_wc : nlclocking.

    Lemma rename_in_equation_wc : forall equ,
        (forall x, In x (var_defined equ) -> Env.find x sub = None) ->
        wc_equation G (inouts ++ vars) equ ->
        wc_equation G (inouts ++ vars') (rename_in_equation sub equ).
    Proof with eauto with nlclocking.
      intros * Hdef Hwc; inv Hwc; simpl in *...
      - constructor...
      - eapply CEqApp with (sub:=fun x => option_map (fun x => rename_in_var sub x) (sub0 x)) (* ? *)...
        + rewrite Forall2_map_2. eapply Forall2_impl_In; [|eauto]; intros (?&?&?) ? _ _ (?&?&?&?).
          repeat esplit...
          * inv H3; simpl; constructor.
          * apply instck_rename_in_clock; auto.
        + eapply Forall2_impl_In; [|eauto]; intros (?&?&?) ? _ Hin2 (?&?&?&?).
          repeat (esplit; eauto).
          * rewrite H3; simpl.
            unfold rename_in_var. rewrite Hdef; eauto.
          * eapply instck_rename_in_clock; eauto.
        + unfold rename_in_reset.
          rewrite Forall_map. eapply Forall_impl; [|eauto]; intros (?&?) ?...
      - constructor...
        unfold rename_in_reset.
          rewrite Forall_map. eapply Forall_impl; [|eauto]; intros (?&?) ?...
    Qed.

  End rename.

  Lemma remove_dup_regs_once_wc : forall G inouts vars eqs,
      NoDupMembers (inouts ++ idck vars) ->
      NoDup (vars_defined eqs) ->
      (forall x eq, In eq eqs -> In x (var_defined eq) -> is_fby eq = true -> ~InMembers x inouts) ->
      wc_env inouts ->
      Forall (wc_equation G (inouts ++ idck vars)) eqs ->
      let (vars', eqs') := remove_dup_regs_eqs_once vars eqs in
      Forall (wc_equation G (inouts ++ idck vars')) eqs'.
  Proof.
    intros * Hndv Hnd Hinouts Hwinouts Hwc.
    destruct (remove_dup_regs_eqs_once _ _) eqn:Honce. inv Honce.
    unfold subst_and_filter_equations.
    rewrite Forall_map, Forall_filter. eapply Forall_impl_In; eauto.
    intros ? Hineq Hwc' Hfilter.
    eapply rename_in_equation_wc; [| | |eauto].
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
      rewrite In_idck_exists in *. destruct Hin as (?&Hin).
      assert (Hfind':=Hfind).
      eapply find_duplicates_spec in Hfind as (?&?&?&?&?&Hwt1&Hwt2&_).
      eapply Forall_forall in Hwt1; eauto. eapply Forall_forall in Hwt2; eauto.
      inv Hwt1. inv Hwt2.
      rewrite in_app_iff in H2, H3.
      destruct H2 as [Hin1|Hin1], H3 as [Hin2|Hin2].
      1-3:(exfalso; eauto using In_InMembers).
      eapply In_idck_exists in Hin1 as (?&Hin1).
      eapply In_idck_exists in Hin2 as (ty&Hin2).
      eapply NoDupMembers_det in Hin; eauto. 2:eapply NoDupMembers_app_r, NoDupMembers_idck in Hndv; eauto.
      inv Hin. exists ty; simpl.
      eapply in_map_iff. exists (y, (ty, ck)); split; auto.
      eapply filter_In; split; auto.
       eapply find_duplicates_irrefl in Hfind'; eauto.
       apply Env.Props.P.F.not_mem_in_iff in Hfind'. rewrite Hfind'; auto.
    - intros * Hfind Hin.
      rewrite in_app_iff in *. destruct Hin as [Hin|Hin]; auto.
      + assert (forall x, Env.In x (find_duplicates eqs) -> ~InMembers x inouts) as Hninouts.
        { clear Hfind. intros ? Hindup.
          rewrite Env.In_find in Hindup. destruct Hindup as (?&Hfind).
          eapply find_duplicates_spec in Hfind as (?&?&?&?&?&Hin1&_).
          eapply Hinouts; eauto. simpl; auto.
        }
        assert (rename_in_clock (find_duplicates eqs) ck = ck); repeat rewrite H; auto.
        eapply wc_env_var in Hin; eauto.
        clear - Hin Hwinouts Hninouts.
        induction Hin; simpl; auto.
        f_equal; auto.
        unfold rename_in_var. destruct (Env.find _ _) eqn:Hfind; auto.
        apply Env.find_In, Hninouts in Hfind.
        exfalso; eauto using In_InMembers.
      + right.
        rewrite In_idck_exists in *. destruct Hin as (ty&Hin).
        exists ty.
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

  Lemma remove_dup_regs_once_wc_env : forall G inouts vars eqs vars' eqs',
      NoDupMembers (inouts ++ idck vars) ->
      NoDup (vars_defined eqs) ->
      (forall x eq, In eq eqs -> In x (var_defined eq) -> is_fby eq = true -> ~InMembers x inouts) ->
      wc_env inouts ->
      wc_env (inouts ++ idck vars) ->
      Forall (wc_equation G (inouts ++ idck vars)) eqs ->
      remove_dup_regs_eqs_once vars eqs = (vars', eqs') ->
      wc_env (inouts ++ idck vars').
  Proof.
    intros * Hndv Hnd Hinouts Hwc1 Hwc2 Hwceq Hrem.
    inv Hrem.
    eapply Forall_app; split.
    - eapply Forall_impl; [|eauto]; intros (?&?) ?.
      eapply wc_clock_incl; eauto. apply incl_appl, incl_refl.
    - eapply Forall_app in Hwc2 as (?&Hwc2).
      unfold idck in *.
      rewrite Forall_map in *. eapply Forall_map, Forall_filter.
      eapply Forall_impl_In; [|eauto]. intros (?&?&?) ? Hwc Hmem; simpl in *.
      eapply rename_in_clock_wc; eauto; intros * Hfind Hin.
      + assert (~InMembers x inouts) as Hnx.
        { apply find_duplicates_spec in Hfind as (?&?&?&?&?&Hin1&_&_).
          eapply Hinouts in Hin1; eauto. simpl; auto. }
        assert (~InMembers y inouts) as Hny.
        { apply find_duplicates_spec in Hfind as (?&?&?&?&?&_&Hin2&_).
          eapply Hinouts in Hin2; eauto. simpl; auto. }
        rewrite in_app_iff in *. destruct Hin as [Hin|Hin].
        1:(exfalso; eauto using In_InMembers).
        right.
        rewrite in_map_iff in *. destruct Hin as ((?&ty0&?)&Heq&Hin); inv Heq; simpl in *.
        assert (Hfind':=Hfind).
        eapply find_duplicates_spec in Hfind as (?&?&?&?&?&Hwt1&Hwt2&_).
        eapply Forall_forall in Hwt1; eauto. eapply Forall_forall in Hwt2; eauto.
        inv Hwt1. inv Hwt2.
        rewrite in_app_iff in H4, H5.
        destruct H4 as [Hin1|Hin1], H5 as [Hin2|Hin2].
        1-3:(exfalso; eauto using In_InMembers).
        eapply In_idck_exists in Hin1 as (?&Hin1).
        eapply In_idck_exists in Hin2 as (ty&Hin2).
        eapply NoDupMembers_det in Hin; eauto. inv Hin. 2:eapply NoDupMembers_app_r, NoDupMembers_idck in Hndv; eauto.
        exists (y, (ty, rename_in_clock (find_duplicates eqs) ck)); simpl; split; auto.
        apply in_map_iff. exists (y, (ty, ck)); split; auto.
        eapply filter_In; split; auto.
        eapply find_duplicates_irrefl in Hfind'; eauto.
        apply Env.Props.P.F.not_mem_in_iff in Hfind'. rewrite Hfind'; auto.
      + rewrite in_app_iff in *. destruct Hin as [Hin|Hin]; auto.
        * assert (forall x, Env.In x (find_duplicates eqs) -> ~InMembers x inouts) as Hninouts.
          { clear Hfind. intros ? Hindup.
            rewrite Env.In_find in Hindup. destruct Hindup as (?&Hfind).
            eapply find_duplicates_spec in Hfind as (?&?&?&?&?&Hin1&_).
            eapply Hinouts; eauto. simpl; auto.
          }
          assert (rename_in_clock (find_duplicates eqs) ck = ck) as Hck; repeat rewrite Hck; auto.
          eapply wc_env_var in Hin; eauto.
          clear - Hin Hwc1 Hninouts.
          induction Hin; simpl; auto.
          f_equal; auto.
          unfold rename_in_var. destruct (Env.find _ _) eqn:Hfind; auto.
          apply Env.find_In, Hninouts in Hfind.
          exfalso; eauto using In_InMembers.
        * right.
          rewrite in_map_iff in *. destruct Hin as ((x0&ty0&ck0)&Heq&Hin); inv Heq; simpl in *.
          exists (x, (ty0, rename_in_clock (find_duplicates eqs) ck)); simpl; split; auto.
          apply in_map_iff. exists (x, (ty0, ck)); split; auto.
          apply filter_In; split; auto.
          rewrite Env.mem_find, Hfind; auto.
  Qed.

  Lemma remove_dup_regs_eqs_wc : forall G inouts vars eqs vars' eqs',
      NoDupMembers (inouts ++ idck vars) ->
      NoDup (vars_defined eqs) ->
      (forall x eq, In eq eqs -> In x (var_defined eq) -> is_fby eq = true -> ~InMembers x inouts) ->
      wc_env inouts ->
      wc_env (inouts ++ idck vars) ->
      Forall (wc_equation G (inouts ++ idck vars)) eqs ->
      remove_dup_regs_eqs vars eqs = (vars', eqs') ->
      Forall (wc_equation G (inouts ++ idck vars')) eqs' /\ wc_env (inouts ++ idck vars').
  Proof.
    intros until eqs.
    functional induction (remove_dup_regs_eqs vars eqs); intros * Hndv Hnd Hinouts Hwinouts Hwenv Hwc Hrem.
    - eapply remove_dup_regs_once_wc_env in Hwenv; eauto.
      eapply remove_dup_regs_once_wc in Hwc; eauto.
      rewrite e in Hwc. inv e.
      eapply IHp; eauto using subst_and_filter_equations_NoDup.
      + clear - Hndv.
        apply NoDupMembers_app; eauto using NoDupMembers_app_l.
        * apply NoDupMembers_app_r, NoDupMembers_idck in Hndv.
          apply NoDupMembers_idck, subst_and_filter_vars_NoDupMembers; auto.
        * intros ? Hin.
          eapply NoDupMembers_app_InMembers in Hndv; eauto.
          contradict Hndv.
          rewrite InMembers_idck in *; eauto using subst_and_filter_vars_InMembers.
      + intros ?? Hin1 Hin2 Hisfby.
        eapply in_map_iff in Hin1 as (?&?&Hin1); subst. apply in_filter in Hin1.
        destruct x0; simpl in *; try congruence. destruct Hin2 as [Hin2|Hin2]; inv Hin2.
        eapply Hinouts; eauto. simpl; auto.
    - inv Hrem; auto.
  Qed.

  Lemma remove_dup_regs_node_wc : forall G n,
      wc_node G n ->
      wc_node (remove_dup_regs G) (remove_dup_regs_node n).
  Proof.
    intros * (Hwci&Hwco&Hwcv&Hwceq).
    destruct (remove_dup_regs_eqs (n_vars n) (n_eqs n)) as (vars'&eqs') eqn:Hrem.
    destruct (remove_dup_regs_eqs_wc G (idck (n_in n ++ n_out n)) (n_vars n) (n_eqs n) vars' eqs')
      as (Hwc'&Hwenv'); eauto.
    - rewrite <-idck_app, <-app_assoc, (Permutation.Permutation_app_comm (n_out _)).
      apply NoDupMembers_idck, n_nodup.
    - apply NoDup_var_defined_n_eqs.
    - intros. intros contra. rewrite idck_app, InMembers_app in contra. destruct contra as [contra|contra].
      + rewrite InMembers_idck in contra.
        assert (In x (vars_defined (n_eqs n))) as Hdef.
        { unfold vars_defined. apply in_flat_map.
          eexists; split; eauto. }
        rewrite n_defd in Hdef. apply fst_InMembers in Hdef.
        eapply NoDupMembers_app_InMembers in contra. eapply contra; eauto.
        eapply n_nodup.
      + rewrite fst_InMembers, map_fst_idck in contra.
        apply n_vout in contra. apply contra.
        unfold vars_defined. apply in_flat_map.
        eexists; split; eauto.
        apply filter_In; auto.
    - rewrite <-idck_app, <-app_assoc, (Permutation.Permutation_app_comm (n_out _)); auto.
    - eapply Forall_impl; [|eauto]. intros ? Hwt.
      eapply wc_equation_incl; eauto. clear -n. intros (?&?) Hin.
      rewrite <-idck_app, <-app_assoc, (Permutation.Permutation_app_comm (n_out _)).
      assumption.
    - split; [|split; [|split]]; simpl; auto.
      1,2:rewrite Hrem.
      + simpl. rewrite <-idck_app, <-app_assoc, (Permutation.Permutation_app_comm (n_out _)) in Hwenv'; auto.
      + eapply Forall_impl; [|eauto]. intros ? Hwt.
        eapply global_iface_eq_wc_eq; eauto using remove_dup_regs_iface_eq.
        eapply wc_equation_incl; eauto. clear -n. intros ? Hin.
        repeat rewrite idck_app in *. repeat rewrite <-filter_app in Hin.
        repeat rewrite in_app_iff in *.
        destruct Hin as [[Hin|Hin]|Hin]; auto.
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
