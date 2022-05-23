From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Recdef.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Environment.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLIndexedSemantics.
From Velus Require Import NLustre.DupRegRem.DRR.

Module Type DRRCORRECTNESS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX      Ids Op)
       (Import Cks   : CLOCKS             Ids Op OpAux)
       (Import Str   : INDEXEDSTREAMS     Ids Op OpAux Cks)
       (Import CESyn : CESYNTAX           Ids Op OpAux Cks)
       (Import CESem : CESEMANTICS        Ids Op OpAux Cks CESyn Str)
       (Import Syn   : NLSYNTAX           Ids Op OpAux Cks CESyn)
       (Import Ord   : NLORDERED          Ids Op OpAux Cks CESyn Syn)
       (Import Sem   : NLINDEXEDSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem)
       (Import DRR   : DRR                Ids Op OpAux Cks CESyn Syn).

  (** ** Preservation of Ordered_nodes *)

  Lemma remove_dup_regs_eqs_Is_node_in : forall f vars eqs,
    Is_node_in f (snd (remove_dup_regs_eqs vars eqs)) ->
    Is_node_in f eqs.
  Proof.
    intros *.
    functional induction (remove_dup_regs_eqs vars eqs); intros * Hin; auto.
    apply IHp in Hin. clear IHp.
    inv e. clear - Hin. revert Hin. generalize (find_duplicates eqs); intros.
    unfold subst_and_filter_equations, Is_node_in in *.
    rewrite Exists_map in Hin.
    induction eqs as [|[| |]]; simpl in *; auto.
    - inv Hin.
    - inv Hin; auto. inv H0.
    - inv Hin; auto.
      inv H0; auto. left. constructor.
    - destruct (negb _); auto.
      inv Hin; auto. inv H0.
  Qed.

  Theorem remove_dup_regs_Ordered : forall G,
    Ordered_nodes G ->
    Ordered_nodes (remove_dup_regs G).
  Proof.
    intros * Hord.
    eapply transform_units_Ordered_program; eauto.
    intros * Hin; simpl in *.
    eapply remove_dup_regs_eqs_Is_node_in; eauto.
  Qed.

  (** ** Preservation of semantics *)

  Section rename_instant.

    Variable (sub : Env.t ident).
    Variable (base : bool).
    Variable (R : env).

    Hypothesis Hsub : forall x y,
        Env.find x sub = Some y ->
        R x = R y.

    Lemma subst_sem_var_instant : forall x v,
        sem_var_instant R x v <->
        sem_var_instant R (rename_in_var sub x) v.
    Proof.
      intros *.
      unfold rename_in_var, sem_var_instant.
      destruct (Env.find x sub) eqn:Hfind; try reflexivity.
      apply Hsub in Hfind. now rewrite Hfind.
    Qed.
    Local Hint Resolve subst_sem_var_instant : nlsem.

    Lemma subst_sem_clock_instant : forall ck v,
        sem_clock_instant base R ck v <->
        sem_clock_instant base R (rename_in_clock sub ck) v.
    Proof.
      split; revert v.
      1,2:induction ck; intros * Hsem; simpl in *; inv Hsem.
      1,5:constructor; auto.
      1,4:eapply Son; eauto.
      3,5:eapply Son_abs1; eauto.
      5,6:eapply Son_abs2; eauto.
      1,3,5:rewrite <-subst_sem_var_instant; auto.
      1-3:apply subst_sem_var_instant; auto.
    Qed.
    Local Hint Resolve subst_sem_clock_instant : nlsem.

    Lemma subst_sem_clocked_var_instant : forall x ck,
        sem_clocked_var_instant base R x ck ->
        sem_clocked_var_instant base R (rename_in_var sub x) (rename_in_clock sub ck).
    Proof.
      intros * Hsem; inv Hsem.
      rewrite subst_sem_clock_instant in *.
      rewrite subst_sem_var_instant in *. setoid_rewrite subst_sem_var_instant in H.
      constructor; auto.
    Qed.

    Corollary subst_sem_clocked_vars_instant : forall xcks,
        sem_clocked_vars_instant base R xcks ->
        sem_clocked_vars_instant base R (rename_in_reset sub xcks).
    Proof.
      unfold rename_in_reset, sem_clocked_vars_instant.
      intros * Hsem.
      rewrite Forall_map.
      eapply Forall_impl; [|eauto]; intros (?&?) ?.
      eapply subst_sem_clocked_var_instant; eauto.
    Qed.

    Lemma subst_sem_exp_instant : forall e v,
        sem_exp_instant base R e v ->
        sem_exp_instant base R (rename_in_exp sub e) v.
    Proof.
      induction e; intros * Hsem; simpl; auto.
      - (* var *)
        inv Hsem. constructor. rewrite <-subst_sem_var_instant; auto.
      - (* when *)
        inv Hsem.
        + apply Swhen_eq; auto.
          rewrite <-subst_sem_var_instant; auto.
        + eapply Swhen_abs1; eauto.
          rewrite <-subst_sem_var_instant; auto.
        + eapply Swhen_abs; eauto.
          rewrite <-subst_sem_var_instant; auto.
      - (* unop *)
        inv Hsem; econstructor; eauto.
        rewrite rename_in_exp_typeof; auto.
      - (* binop *)
        inv Hsem; econstructor; eauto.
        rewrite 2 rename_in_exp_typeof; auto.
    Qed.
    Local Hint Resolve subst_sem_exp_instant : nlsem.

    Corollary subst_sem_aexp_instant : forall ck e v,
        sem_aexp_instant base R ck e v ->
        sem_aexp_instant base R (rename_in_clock sub ck) (rename_in_exp sub e) v.
    Proof.
      intros * Hsem; inv Hsem.
      1,2:constructor; auto with nlsem; rewrite <-subst_sem_clock_instant; auto.
    Qed.

    Corollary subst_sem_exps_instant : forall es vs,
        sem_exps_instant base R es vs ->
        sem_exps_instant base R (map (rename_in_exp sub) es) vs.
    Proof.
      unfold sem_exps_instant.
      intros * Hsem.
      rewrite Forall2_map_1.
      eapply Forall2_impl_In; [|eauto]; intros; eauto with nlsem.
    Qed.

    Lemma subst_sem_cexp_instant : forall e v,
        sem_cexp_instant base R e v ->
        sem_cexp_instant base R (rename_in_cexp sub e) v.
    Proof.
      induction e using cexp_ind2'; intros * Hsem; simpl; auto.
      - (* merge *)
        destruct x; simpl.
        inv Hsem; econstructor.
        2:rewrite map_app; simpl; auto.
        1-6:eauto.
        1,4:rewrite <-subst_sem_var_instant; auto.
        + now rewrite map_length.
        + apply Forall_app in H as (_&Hf). inv Hf; auto.
        + rewrite <-map_app, Forall_map.
          eapply Forall_impl_In; [|eauto]; intros; simpl in *.
          eapply Forall_forall with (x:=a) in H. 2:rewrite in_app_iff in *; simpl; destruct H0; auto.
          eauto.
        + rewrite Forall_map.
          eapply Forall_impl_In; [|eapply H6]; intros. eapply Forall_forall in H; eauto.
      - (* case *)
        inv Hsem; econstructor; eauto with nlsem.
        + rewrite Forall2_map_1. eapply Forall2_impl_In; [|eauto]; intros.
          eapply Forall_forall in H; eauto.
          destruct a; simpl in *; auto.
        + rewrite Forall_map. eapply Forall_impl_In; [|eauto]; intros.
          eapply Forall_forall in H; eauto.
          destruct a; simpl in *; eauto.
      - (* eexp *)
        inv Hsem. constructor; auto with nlsem.
    Qed.
    Local Hint Resolve subst_sem_cexp_instant : nlsem.

    Corollary subst_sem_caexp_instant : forall ck e v,
        sem_caexp_instant base R ck e v ->
        sem_caexp_instant base R (rename_in_clock sub ck) (rename_in_cexp sub e) v.
    Proof.
      intros * Hsem; inv Hsem.
      1,2:constructor; auto with nlsem; rewrite <-subst_sem_clock_instant; auto.
    Qed.

  End rename_instant.

  Section rename.
    Variable (sub : Env.t ident).

    Variable (G : global).
    Variable (base : cstream).
    Variable (H : history).

    Hypothesis Hsub : forall x y,
        Env.find x sub = Some y ->
        forall n, (H n) x = (H n) y.

    Lemma subst_sem_var : forall x vs,
        sem_var H x vs ->
        sem_var H (rename_in_var sub x) vs.
    Proof.
      intros * Hsem ?.
      rewrite <-subst_sem_var_instant; eauto.
    Qed.

    Lemma subst_sem_clock : forall ck vs,
        sem_clock base H ck vs ->
        sem_clock base H (rename_in_clock sub ck) vs.
    Proof.
      intros * Hsem ?.
      rewrite <-subst_sem_clock_instant; eauto.
    Qed.

    Lemma subst_sem_equation : forall equ,
        sem_equation G base H equ ->
        sem_equation G base H (rename_in_equation sub equ).
    Proof.
      intros * Hsem; inv Hsem; simpl.
      - (* def *)
        econstructor; eauto using subst_sem_var.
        intros ?; eapply subst_sem_caexp_instant; eauto.
      - (* app *)
        econstructor; eauto using subst_sem_clock.
        + intros ?; eapply subst_sem_exps_instant; eauto.
        + rewrite Forall2_map_1 in *.
          unfold rename_in_reset. rewrite Forall2_map_1.
          eapply Forall2_impl_In; [|eauto]; intros (?&?) ? _ _ ?; eauto using subst_sem_var.
      - (* fby *)
        econstructor; eauto.
        + intros ?; eapply subst_sem_aexp_instant; eauto.
        + rewrite Forall2_map_1 in *.
          unfold rename_in_reset. rewrite Forall2_map_1.
          eapply Forall2_impl_In; [|eauto]; intros (?&?) ? _ _ ?; eauto using subst_sem_var.
        + intros ?. eapply subst_sem_clocked_vars_instant; eauto.
    Qed.

  End rename.

  Section remove_dup_regs_eqs.
    Variable (G1 G2 : global).

    Hypothesis Hglob : forall f ins outs,
        sem_node G1 f ins outs -> sem_node G2 f ins outs.

    Variable (base : cstream).
    Variable (H : history).

    Lemma Forall2_bools : forall H xs vs rs,
        Forall2 (sem_var H) xs vs ->
        bools_ofs vs rs ->
        exists vs' , Forall2 (sem_var H) (PSP.to_list (PSP.of_list xs)) vs' /\
                bools_ofs vs' rs.
    Proof.
      intros * Vars Bools; simpl.
      assert (SameElements eq xs (PSP.to_list (PSP.of_list xs))) as Same.
      { eapply ps_of_list_ps_to_list_SameElements; eauto. }
      assert (Vars':=Vars). eapply @Forall2_SameElements_1 with (eqB:=eq) in Vars' as (vs'&Same'&?); eauto.
      1-3:auto.
      - rewrite Same' in Bools. eauto.
      - intros * Eq1 Eq2 Var. rewrite <-Eq1, <-Eq2; auto.
      - eauto using sem_var_det.
    Qed.

    Lemma ps_equal_Forall2_bools :
      forall H xs ys vs vs' rs rs',
        PS.Equal (PSP.of_list xs) (PSP.of_list ys) ->
        Forall2 (sem_var H) xs vs ->
        Forall2 (sem_var H) ys vs' ->
        bools_ofs vs rs ->
        bools_ofs vs' rs' ->
        rs = rs'.
    Proof.
      intros * Eq Vars Vars' Bools Bools'.
      assert (SameElements eq xs ys) as Same.
      { eapply SE_trans. eapply ps_of_list_ps_to_list_SameElements.
        symmetry. eapply SE_trans. eapply ps_of_list_ps_to_list_SameElements.
        eapply SE_perm. rewrite <-Eq. reflexivity. }
      eapply @Forall2_SameElements_1 with (eqB:=eq) in Vars as (vs''&Same'&Vars); eauto. 2:eauto.
      assert (vs' = vs''); subst.
      { eapply Forall2_swap_args in Vars'. eapply Forall2_trans_ex in Vars; eauto. clear - Vars.
        induction Vars as [|???? (?&_&Hv1&Hv2)]; subst; auto.
        eapply sem_var_det in Hv1; eauto; subst; auto. }
      rewrite Same' in Bools.
      eapply bools_ofs_det in Bools'; eauto.
      - intros * Eq1 Eq2 Var. rewrite <-Eq1, <-Eq2; auto.
      - eauto using sem_var_det.
    Qed.

    Lemma sem_EqFby_det : forall x y ck c0 e xr1 xr2,
        PS.Equal (PSP.of_list (map fst xr1)) (PSP.of_list (map fst xr2)) ->
        sem_equation G1 base H (EqFby x ck c0 e xr1) ->
        sem_equation G1 base H (EqFby y ck c0 e xr2) ->
        forall n, (H n) x = (H n) y.
    Proof.
      intros * Heq Hsem1 Hsem2.
      inv Hsem1. inv Hsem2.
      eapply sem_aexp_det in H6; eauto; subst.
      eapply ps_equal_Forall2_bools in H17; eauto; subst.
      intros n. specialize (H9 n). specialize (H14 n).
      rewrite H9, H14. reflexivity.
    Qed.

    Lemma remove_dup_regs_eqs_sem : forall vars eqs,
        Forall (sem_equation G1 base H) eqs ->
        Forall (sem_equation G2 base H) (snd (remove_dup_regs_eqs vars eqs)).
    Proof.
      intros * Hsem.
      functional induction (remove_dup_regs_eqs vars eqs).
      - apply IHp. clear IHp.
        inv e.
        unfold subst_and_filter_equations.
        rewrite Forall_map, Forall_filter.
        eapply Forall_impl; [|eauto]; intros * ? _.
        eapply subst_sem_equation; eauto.
        intros ?? Hfind.
        eapply find_duplicates_spec in Hfind as (?&?&?&?&?&Hfby1&Hfby2&Heq).
        eapply Forall_forall in Hfby1; eauto.
        eapply Forall_forall in Hfby2; eauto.
        eapply sem_EqFby_det; eauto.
      - clear - Hglob Hsem.
        eapply Forall_impl; [|eauto]; intros.
        inv H0; econstructor; eauto.
    Qed.

  End remove_dup_regs_eqs.

  Theorem remove_dup_regs_sem : forall G f ins outs,
      Ordered_nodes G ->
      sem_node G f ins outs ->
      sem_node (remove_dup_regs G) f ins outs.
  Proof.
    intros (enms&nds).
    unfold remove_dup_regs.
    induction nds; intros * Hord Hsem; simpl; auto.
    destruct (ident_eq_dec (n_name a) f).
    - inv Hsem. rewrite find_node_now in H1; inv H1; auto.
      econstructor; simpl; auto. rewrite find_node_now; eauto.
      1-3:simpl; eauto.
      eapply Forall_sem_equation_global_tl in H5; eauto.
      2:{ eapply not_Is_called_in_self in Hord; eauto.
          setoid_rewrite find_unit_now; eauto. simpl; eauto. }
      eapply Forall_sem_equation_global_tl'; eauto.
      1,2:eapply remove_dup_regs_Ordered in Hord; eauto.
      { eapply not_Is_called_in_self in Hord; eauto.
        setoid_rewrite find_unit_now; eauto. simpl; eauto. }
      eapply remove_dup_regs_eqs_sem in H5; [simpl;eauto|].
      inv Hord; eauto.
    - eapply sem_node_cons in Hsem; eauto.
      eapply sem_node_cons'; eauto.
      + eapply remove_dup_regs_Ordered in Hord; eauto.
      + inv Hord; eauto.
  Qed.

End DRRCORRECTNESS.

Module DrrCorrectnessFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX      Ids Op)
       (Cks   : CLOCKS             Ids Op OpAux)
       (Str   : INDEXEDSTREAMS     Ids Op OpAux Cks)
       (CESyn : CESYNTAX           Ids Op OpAux Cks)
       (CESem : CESEMANTICS        Ids Op OpAux Cks CESyn Str)
       (Syn   : NLSYNTAX           Ids Op OpAux Cks CESyn)
       (Ord   : NLORDERED          Ids Op OpAux Cks CESyn Syn)
       (Sem   : NLINDEXEDSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem)
       (DRR   : DRR                Ids Op OpAux Cks CESyn Syn)
<: DRRCORRECTNESS Ids Op OpAux Cks Str CESyn CESem Syn Ord Sem DRR.
  Include DRRCORRECTNESS Ids Op OpAux Cks Str CESyn CESem Syn Ord Sem DRR.
End DrrCorrectnessFun.
