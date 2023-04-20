From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LClocking.
From Velus Require Import Lustre.LOrdered Lustre.LSemantics.
From Velus Require Import Lustre.Complete.Complete Lustre.Complete.CompClocking.

Module Type COMPCORRECTNESS
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import Ord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (Import Comp: COMPLETE Ids Op OpAux Cks Senv Syn).

  Module Clocking := CompClockingFun Ids Op OpAux Cks Senv Syn Clo Comp.

  Lemma complete_block_defined1 : forall blk env x,
      Is_defined_in x blk ->
      Is_defined_in x (complete_block env blk).
  Proof.
    induction blk using block_ind2; intros * Def; inv Def; constructor; auto.

    - (* reset *)
      solve_Exists. simpl_Forall. eauto.

    - (* switch *)
      solve_Exists. Syn.inv_branch. constructor.
      apply Exists_app. solve_Exists. simpl_Forall. eauto.

    - (* automaton *)
      solve_Exists. Syn.inv_branch. Syn.inv_scope. do 2 constructor; auto.
      apply Exists_app. solve_Exists. simpl_Forall. eauto.

    - (* local *)
      Syn.inv_scope. constructor; auto.
      solve_Exists. simpl_Forall. eauto.
  Qed.

  Lemma complete_block_defined2 : forall blk env x,
      Is_defined_in x (complete_block env blk) ->
      Is_defined_in x blk.
  Proof.
    induction blk using block_ind2; intros * Def; simpl in *; inv Def; constructor; auto.

    - (* reset *)
      solve_Exists. simpl_Forall. eauto.

    - (* switch *)
      simpl_Exists. destruct b. simpl in *. Syn.inv_branch.
      apply Exists_app' in H1 as [Ex|Ex].
      + simpl_Exists. inv Ex. simpl in *. take (_ \/ _) and destruct it as [Eq|Eq]; inv Eq.
        apply In_PS_elements, PS.diff_spec in Hin0 as (In&_).
        apply vars_defined_Is_defined_in with (blk:=Bswitch ec _) in In.
        now inv In.
      + solve_Exists. constructor. solve_Exists; simpl_Forall; eauto.

    - (* automaton *)
      simpl_Exists. destruct b as [?(?&[?(?&?)])]. Syn.inv_branch. Syn.inv_scope.
      apply Exists_app' in H4 as [Ex|Ex].
      + simpl_Exists. inv Ex. simpl in *. take (_ \/ _) and destruct it as [Eq|Eq]; inv Eq.
        apply In_PS_elements, PS.diff_spec in Hin0 as (In&_).
        apply vars_defined_Is_defined_in with (blk:=Bauto type ck (l, e0) _) in In.
        now inv In.
      + solve_Exists. do 2 constructor; auto. solve_Exists. simpl_Forall. eauto.

    - (* local *)
      Syn.inv_scope. constructor; auto.
      solve_Exists. simpl_Forall. eauto.
  Qed.

  Ltac inv_branch := (Syn.inv_branch||Sem.inv_branch).
  Ltac inv_scope := (Syn.inv_scope||Sem.inv_scope).

  Section complete_node_sem.
    Variable (G1 : @global (fun _ _ => True) elab_prefs) (G2: @global complete elab_prefs).
    Hypothesis Gref : global_sem_refines G1 G2.

    Lemma complete_block_sem : forall blk env Γ Hi bs,
        wx_block Γ blk ->
        NoDupLocals (List.map fst Γ) blk ->
        sem_block G1 Hi bs blk ->
        sem_block G2 Hi bs (complete_block env blk).
    Proof.
      induction blk using block_ind2; intros * Wx ND Sem; assert (Wx':=Wx); inv Wx'; inv ND; inv Sem.
      - (* equation *)
        constructor; eauto using sem_ref_sem_equation.

      - (* last *)
        econstructor; eauto using sem_ref_sem_exp.

      - (* reset *)
        econstructor; eauto using sem_ref_sem_exp.
        intros k. specialize (H10 k). simpl_Forall; eauto.

      - (* switch *)
        econstructor; eauto using sem_ref_sem_exp.
        simpl_Forall. do 2 esplit; eauto. repeat inv_branch.
        constructor. apply Forall_app; split; simpl_Forall; eauto.
        + apply In_PS_elements, PS.diff_spec in H2 as (In&nIn).
          apply vars_defined_Is_defined_in with (blk:=Bswitch ec _) in In.
          rewrite map_vars_defined_spec in nIn.
          edestruct H13 as (?&V&L); eauto.
          do 2 econstructor. 1,2:simpl; repeat (constructor; eauto).
        + intros * Def NDef.
          eapply H13; eauto.
          * eapply complete_block_defined2; eauto.
          * contradict NDef. apply Exists_app.
            solve_Exists. eapply complete_block_defined1; eauto.

      - (* automaton (weak) *)
        econstructor; eauto using sem_ref_sem_transitions.
        simpl_Forall. specialize (H16 k). destruct_conjs.
        do 2 esplit; eauto. repeat inv_branch. repeat inv_scope. subst Γ'.
        constructor. econstructor; eauto. simpl; split; [apply Forall_app; split; simpl_Forall; eauto|].
        + apply In_PS_elements, PS.diff_spec in H18 as (In&nIn).
          apply vars_defined_Is_defined_in with (blk:=Bauto Weak ck (ini0, oth) _) in In.
          rewrite PS.filter_spec, map_vars_defined_spec, Bool.negb_true_iff, mem_assoc_ident_false_iff in nIn.
          2:{ intros ?? Eq; now inv Eq. }
          edestruct H17 as (?&V&L); eauto.
          1:{ contradict nIn. inv nIn. auto. }
          assert (~InMembers x0 locs) as nInM.
          { intros InM. eapply H11, fst_InMembers; eauto.
            eapply Is_defined_in_wx_In in In; eauto. }
          do 2 econstructor. 1,2:simpl; repeat (constructor; eauto).
          1,2:eapply sem_var_union2; [eauto|].
          1,2:contradict nInM; apply H21 in nInM; clear - nInM; inv nInM; solve_In.
        + eapply H with (Γ:=Γ++senv_of_decls locs); eauto.
          * now rewrite map_app, map_fst_senv_of_decls.
        + eauto using sem_ref_sem_transitions.
        + intros * Def NDef.
          eapply H17; eauto.
          * eapply complete_block_defined2; eauto.
          * contradict NDef. inv_scope. constructor; auto. apply Exists_app.
            solve_Exists. eapply complete_block_defined1; eauto.

      - (* automaton (strong) *)
        econstructor; eauto using sem_ref_sem_transitions.
        1:{ simpl_Forall. specialize (H15 k). destruct_conjs.
            do 2 esplit; eauto. repeat inv_branch. repeat inv_scope.
            constructor; eauto using sem_ref_sem_transitions.
            + intros * Def NDef.
              eapply H15; eauto.
              * eapply complete_block_defined2; eauto.
              * contradict NDef. inv_scope. constructor; auto. apply Exists_app.
                solve_Exists. eapply complete_block_defined1; eauto.
        }
        simpl_Forall. specialize (H16 k). destruct_conjs.
        do 2 esplit; eauto. repeat inv_branch. repeat inv_scope. subst Γ'.
        constructor. econstructor; eauto. apply Forall_app; split; simpl_Forall; eauto.
        + apply In_PS_elements, PS.diff_spec in H11 as (In&nIn).
          apply vars_defined_Is_defined_in with (blk:=Bauto Strong ck ([], oth) _) in In.
          rewrite PS.filter_spec, map_vars_defined_spec, Bool.negb_true_iff, mem_assoc_ident_false_iff in nIn.
          2:{ intros ?? Eq; now inv Eq. }
          edestruct H16 as (?&V&L); eauto.
          1:{ contradict nIn. inv nIn. auto. }
          assert (~InMembers x0 locs) as nInM.
          { intros InM. eapply H10, fst_InMembers; eauto.
            eapply Is_defined_in_wx_In in In; eauto. }
          do 2 econstructor. 1,2:simpl; repeat (constructor; eauto).
          1,2:eapply sem_var_union2; [eauto|].
          1,2:contradict nInM; apply H20 in nInM; clear - nInM; inv nInM; solve_In.
        + eapply H with (Γ:=Γ++senv_of_decls locs); eauto.
          * now rewrite map_app, map_fst_senv_of_decls.
        + intros * Def NDef.
          eapply H16; eauto.
          * eapply complete_block_defined2; eauto.
          * contradict NDef. inv_scope. constructor; auto. apply Exists_app.
            solve_Exists. eapply complete_block_defined1; eauto.

      - (* local *)
        repeat inv_scope.
        do 2 econstructor; eauto.
        + simpl_Forall.
          eapply H with (Γ:=Γ++senv_of_decls locs); eauto.
          * now rewrite map_app, map_fst_senv_of_decls.
    Qed.

    Lemma complete_node_sem : forall f n ins outs,
        wc_global (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        Ordered_nodes (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(types) G2.(externs) ((complete_node n)::G2.(nodes))) ->
        sem_node (Global G1.(types) G1.(externs) (n::G1.(nodes))) f ins outs ->
        sem_node (Global G2.(types) G2.(externs) ((complete_node n)::G2.(nodes))) f ins outs.
    Proof with eauto.
      intros * Hwc Hord1 Hord2 Hsem.

      inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
      - erewrite find_node_now in Hfind; eauto. inv Hfind.
        (*The semantics of equations can be given according to G only *)
        assert (~Is_node_in_block (n_name n0) (n_block n0)) as Blk.
        { inv Hord1. destruct H5 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }
        eapply sem_block_cons1 in Blk; eauto. clear H3.

        replace {| types := types G1; nodes := nodes G1 |} with G1 in * by (destruct G1; auto).
        pose proof (n_nodup n0) as (Hnd1&Hnd2).

        inv Hwc. destruct H4 as (Hwc&_); simpl in Hwc. inversion_clear Hwc as [? _ _ Wc].

        eapply complete_block_sem with (Hi:=H) in Blk;
          eauto using node_NoDupLocals with lclocking.
        econstructor.
        + erewrite find_node_now; eauto.
        + simpl_Forall. eauto.
        + simpl_Forall. eauto.
        + apply sem_block_cons2; simpl...
          2:{ eapply find_node_not_Is_node_in in Hord2.
            2:erewrite find_node_now; eauto. eapply Hord2. }
          destruct G2; eauto.
      - erewrite find_node_other in Hfind; eauto.
        eapply sem_node_cons2...
        destruct G2; apply Gref.
        destruct G1; econstructor...
        eapply sem_block_cons1; eauto using find_node_later_not_Is_node_in.
    Qed.

  End complete_node_sem.

  Lemma complete_global_refines : forall G,
      wc_global G ->
      global_sem_refines G (complete_global G).
  Proof.
    intros [].
    induction nodes0; intros * Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      apply global_sem_ref_cons with (f:=n_name a); eauto.
      1,2:eapply wl_global_Ordered_nodes, wc_global_wl_global; eauto.
      + eapply Clocking.complete_global_wc; eauto.
      + inv Hwc. eapply IHnodes0; eauto.
      + intros ins outs Hsem; simpl in *.
        change types0 with ((Global types0 externs0 (List.map complete_node nodes0)).(types)).
        eapply complete_node_sem with (G1:=Global types0 externs0 nodes0); eauto.
        1-3:inv Hwc; eauto using wc_global_wl_global, wl_global_Ordered_nodes.
        eapply wl_global_Ordered_nodes, wc_global_wl_global; eauto.
        eapply Clocking.complete_global_wc in Hwc'; eauto.
  Qed.

  Theorem complete_global_sem : forall G f ins outs,
      wc_global G ->
      sem_node G f ins outs ->
      sem_node (complete_global G) f ins outs.
  Proof.
    intros.
    eapply complete_global_refines in H; eauto.
    specialize (H f ins outs); auto.
  Qed.

End COMPCORRECTNESS.

Module CompCorrectnessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Ord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (Comp: COMPLETE Ids Op OpAux Cks Senv Syn)
       <: COMPCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Clo Ord Sem Comp.
  Include COMPCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Clo Ord Sem Comp.
End CompCorrectnessFun.
