From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import IndexedStreams.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import Stc.StcClocking.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import Stc.StcSemantics.
From Velus Require Import CoreExpr.CEClockingSemantics.
From Coq Require Import List.

(** * Link (static) clocking predicates to (dynamic) semantic model *)

(**

These results confirm the correctness of the clocking predicates wrt the
semantics. In particular, they are useful for relating static invariants to
dynamic properties. They hold essentially due to the "additional" clocking
constraints in the NLustre semantic model.

 *)

Module Type STCCLOCKINGSEMANTICS
       (Import Ids      : IDS)
       (Import Op       : OPERATORS)
       (Import OpAux    : OPERATORS_AUX       Ids Op)
       (Import Cks      : CLOCKS              Ids Op OpAux)
       (Import CESyn    : CESYNTAX            Ids Op OpAux Cks)
       (Import Syn      : STCSYNTAX           Ids Op OpAux Cks CESyn)
       (Import Str      : INDEXEDSTREAMS      Ids Op OpAux Cks)
       (Import Ord      : STCORDERED          Ids Op OpAux Cks CESyn Syn)
       (Import CESem    : CESEMANTICS         Ids Op OpAux Cks CESyn               Str)
       (Import Sem      : STCSEMANTICS        Ids Op OpAux Cks CESyn Syn Ord Str CESem)
       (Import CEClo    : CECLOCKING          Ids Op OpAux Cks CESyn)
       (Import Clkg     : STCCLOCKING         Ids Op OpAux Cks CESyn Syn Ord CEClo)
       (Import CECloSem : CECLOCKINGSEMANTICS Ids Op OpAux Cks CESyn Str CESem              CEClo).

  Lemma sem_clocked_var_instant_tc {prefs}:
    forall (P: @program prefs) base R S I S' vars x ck islast tc,
      Ordered_systems P ->
      wc_program P ->
      NoDupMembers vars ->
      sem_trconstr P base R S I S' tc ->
      wc_trconstr P vars tc ->
      Is_defined_in_tc x tc \/ Is_update_next_in_tc x tc ->
      In (x, (ck, islast)) vars ->
      sem_clocked_var_instant base R (Var x) ck
      /\ if islast then sem_clocked_var_instant base R (Last x) ck else True.
  Proof.
    intros * Ord WCP Nodup Sem WC Def Hin.
    revert dependent ck; revert dependent x; revert dependent vars; revert dependent islast.
    eapply sem_trconstr_mult with
      (P_trconstr := fun base R S I S' tc =>
                       forall vars x ck islast,
                         NoDupMembers vars ->
                         wc_trconstr P vars tc ->
                         Is_defined_in_tc x tc \/ Is_update_next_in_tc x tc ->
                         In (x, (ck, islast)) vars ->
                         sem_clocked_var_instant base R (Var x) ck /\ (if islast then sem_clocked_var_instant base R (Last x) ck else True))
      (P_system := fun f S xs ys S' =>
                     forall base R s P',
                       find_system f P = Some (s, P') ->
                       base = clock_of_instant xs ->
                       sem_vars_instant R (map fst s.(s_in)) xs ->
                       sem_vars_instant R (map fst s.(s_out)) ys ->
                       sem_clocked_vars_instant base R (map (fun '(x, (_, ck)) => (x, (ck, false))) s.(s_in)) ->
                       sem_clocked_vars_instant base R (map (fun '(x, (_, ck)) => (x, (ck, false))) s.(s_out)))
      in Sem; subst. intros; eauto.

    - (* TcDef *)
      intros * _ _ _ * Hexp Hvar * ? WC Def ?.
      inv WC. destruct Def as [Def|Def]; inv Def.
      match goal with H1:In (x, _) vars, H2:In (x, _) vars |- _ =>
                        eapply NoDupMembers_det with (2:=H1) in H2; eauto; subst end.
      inv_equalities. split; auto.
      unfold sem_clocked_var_instant.
      inv Hexp; eauto; intuition; eauto; by_sem_det.

    - (* TcReset State *)
      intros * _ * ??? * ? WC Def ?.
      destruct Def as [Def|Def]; inv Def.

    - (* TcUpdate Last *)
      intros * ? Find Hexp ??? * ? WC Def ?.
      inv WC. destruct Def as [Def|Def]; inv Def.
      match goal with H1:In (x, _) vars, H2:In (x, _) vars |- _ =>
                    eapply NoDupMembers_det with (2:=H1) in H2; eauto; subst end.
      inv_equalities.
      unfold sem_clocked_var_instant.
      inv Hexp; eauto; intuition; eauto; by_sem_det.

    - (* TcUpdate Next *)
      intros * ? Find Hexp ??? * ? WC Def ?.
      inv WC. destruct Def as [Def|Def]; inv Def.
      match goal with H1:In (x, _) vars, H2:In (x, _) vars |- _ =>
                    eapply NoDupMembers_det with (2:=H1) in H2; eauto; subst end.
      inv_equalities. split; auto.
      unfold sem_clocked_var_instant.
      inv Hexp; eauto; intuition; eauto; by_sem_det.

    - (* TcReset Inst *)
      intros * ? * ? * ??? * ? WC Def ?.
      destruct Def as [Def|Def]; inv Def.

    - (* TcUpdate Inst *)
      intros * Hexps Clock Rst Find System Vars Sub IH * ? WC Def Hin.
      inversion WC as [| | | | |?????? bl' ? sub Hfind' Hfai Hfao]; subst. destruct Def as [Def|Def]; inv Def.
      inversion_clear System as [?????? R' ?? Hfind Hvi Hvo Hsck].
      specialize (IH _ _ _ _ Hfind eq_refl Hvi Hvo).
      assert (Hvi' := Hvi).
      rewrite <-map_fst_idsnd in Hvi'.
      specialize (IH Hsck).
      rewrite Hfind in Hfind'; inv Hfind'.

      assert (forall x y ys,
                 InMembers x (idsnd (bl'.(s_in) ++ bl'.(s_out))) ->
                 sub x = Some y ->
                 sem_var_instant R' (Var x) ys ->
                 sem_var_instant R0 (Var y) ys) as Htranso.
      { setoid_rewrite InMembers_idsnd.
        intros; eapply sem_var_instant_transfer_out_instant
                  with (xin := s_in bl') (xout := s_out bl'); eauto.
        - pose proof bl'.(s_nodup) as Hnd.
          rewrite 2 app_assoc in Hnd; apply NoDup_app_weaken in Hnd.
          rewrite <-app_assoc, NoDup_swap, NoDup_app'_iff in Hnd.
          rewrite fst_NoDupMembers, map_app; intuition.
        - apply Forall2_impl_In with (2:=Hfai); intuition.
        - apply Forall2_impl_In with (2:=Hfao); intuition.
      }

      rewrite <-map_fst_idsnd in Hvo. unfold idsnd in Hvo. rewrite map_map in Hvo.
      unfold sem_vars_instant in Hvo.
      rewrite Forall2_map_1 in Hvo.
      apply Forall2_swap_args in Hfao.
      apply Forall2_trans_ex with (1:=Hfao) in Hvo.
      apply Forall2_swap_args in Vars.
      apply Forall2_trans_ex with (1:=Hvo) in Vars.
      apply Forall2_same in Vars.
      eapply Forall_forall in Vars
        as (s & Hins & ((x', (xty, xck)) & Hxin &
                       (Hotc & yck' & Hin' & Hinst) & Hsvx) & Hsvy); eauto.
      simpl in *.
      eapply NoDupMembers_det with (2:=Hin) in Hin'; eauto; inv Hin'.
      unfold idsnd in *. setoid_rewrite Forall_map in IH.
      eapply Forall_forall in IH; eauto; simpl in IH.
      apply wc_find_system with (1:=WCP) in Hfind as (WCi & WCo & WCv & WCtcs).
      assert (In (x', xck) (idsnd (bl'.(s_in) ++ bl'.(s_out)))) as Hxin'
        by (rewrite idsnd_app, in_app; right;
            apply In_idsnd_exists; eauto).
      apply wc_env_var with (1:=WCo) in Hxin'.
      destruct s.
      + eapply IH, sem_clock_instant_transfer_out_instant in Hsvx as Hck; eauto.
        split; auto.
        split; intuition; eauto; try by_sem_det.
        destruct_conjs. unfold sem_var_instant, var_env in *. congruence.
      + assert (exists c, sem_var_instant R' (Var x') (present c)) as Hsvx' by eauto.
        eapply IH, sem_clock_instant_transfer_out_instant in Hsvx'; eauto.
        split; auto.
        split; intuition; eauto; try by_sem_det.
        unfold sem_var_instant, var_env in *. congruence.

    - (* systems *)
      intros * Find Hins Houts Hvars Htcs ??? IH * Find' ? Hins' Houts' Hvars'; subst.
      assert (types P = types P')
        by (apply find_unit_equiv_program in Find; specialize (Find nil); inv Find; auto).
      assert (externs P = externs P')
        by (apply find_unit_equiv_program in Find; specialize (Find nil); inv Find; auto).
      rewrite Find' in Find; inv Find.
      unfold sem_clocked_vars_instant. simpl_Forall. split; auto.
      take (In _ (s_out _)) and assert (Hxin':=it); eapply in_map, system_output_defined_in_tcs in it.
      apply Is_defined_in_In in it as (tc' & Htcin & Hxtc).
      eapply Forall_forall in IH; eauto.
      pose proof Find' as Find; apply find_unit_spec in Find as (?&?&?&?); subst.
      apply wc_find_system with (1:=WCP) in Find' as (WCi & WCo & WCv & WCtcs).
      eapply Forall_forall in WCtcs; eauto.
      assert (NoDupMembers (map (fun '(x, (_, ck)) => (x, (ck, false))) (s_in s ++ s_vars s ++ s_out s)
                              ++ map (fun '(x, (_, _, ck)) => (x, (ck, true))) (s_lasts s)
                              ++ map (fun '(x, (_, _, ck)) => (x, (ck, false))) (s_nexts s)))
        as Hnd.
      { apply fst_NoDupMembers.
        erewrite 6 map_app, 5 map_map,
          map_ext with (l:=s_in _), map_ext with (l:=s_vars _), map_ext with (l:=s_out _),
          map_ext with (l:=s_lasts _), map_ext with (l:=s_nexts _),
          <-2 app_assoc.
        apply s_nodup. all:intros; destruct_conjs; auto.
      }
      eapply IH in Hnd; eauto.
      3:{ simpl_app. rewrite 3 in_app_iff; right; right; left. solve_In. }
      + simpl in *.
        unfold sem_vars_instant in Hins, Houts, Hins', Houts'.
        rewrite Forall2_map_1 in Hins', Houts'.
        apply Forall2_app with (2:=Houts') in Hins'.
        rewrite Forall2_map_1 in Hins, Houts.
        assert (Houts2:=Houts).
        apply Forall2_app with (1:=Hins) in Houts2.
        apply Forall2_Forall2 with (1:=Houts) in Houts'.
        apply Forall2_in_left with (2:=Hxin') in Houts' as (? & Hsin & Hvs & Hvs').
        destruct x0.
        * eapply Hnd in Hvs.
          eapply clock_vars_to_sem_clock_instant in Hins'; eauto with datatypes.
          split; intuition; eauto; try by_sem_det.
          destruct_conjs. unfold sem_var_instant, var_env in *. congruence.
        * assert (exists c, sem_var_instant R0 (Var i) (present c)) as Hvs'' by eauto.
          eapply Hnd in Hvs''.
          eapply clock_vars_to_sem_clock_instant in Hins'; eauto with datatypes.
          split; intuition; eauto; try by_sem_det.
          unfold sem_var_instant, var_env in *. simpl in *. congruence.
      + destruct P; simpl in *; subst.
        apply wc_trconstr_program_app; auto.
        apply wc_trconstr_program_cons; auto.
        * apply Ordered_systems_append in Ord; auto.
        * destruct P'; simpl; auto.
  Qed.

  Corollary sem_clocked_var_instant_tcs {prefs}:
    forall (P: @program prefs) base R S I S' inputs vars tcs,
      Ordered_systems P ->
      wc_program P ->
      NoDupMembers (inputs ++ vars) ->
      Forall (sem_trconstr P base R S I S') tcs ->
      Forall (wc_trconstr P (inputs ++ vars)) tcs ->
      Permutation.Permutation (defined tcs ++ map fst (nexts_of tcs)) (map fst vars) ->
      forall x xck islast,
        In (x, (xck, islast)) vars ->
        sem_clocked_var_instant base R (Var x) xck /\ if islast then sem_clocked_var_instant base R (Last x) xck else True.
  Proof.
    intros * OP WCP Hndup Hsem Hwc Hdef * Hin.
    assert (In x (defined tcs ++ map fst (nexts_of tcs))) as Hxin.
    { rewrite Hdef. solve_In. }
    rewrite in_app_iff, <-Is_defined_in_defined, <-nexts_of_In in Hxin.
    destruct Hxin as [Hxin|Hxin]; apply Exists_exists in Hxin as (?&Hxin&?); simpl_Forall.
    1,2:eapply sem_clocked_var_instant_tc; eauto.
    1,2:rewrite in_app; eauto.
  Qed.

End STCCLOCKINGSEMANTICS.

Module StcClockingSemanticsFun
       (Ids      : IDS)
       (Op       : OPERATORS)
       (OpAux    : OPERATORS_AUX       Ids Op)
       (Cks      : CLOCKS              Ids Op OpAux)
       (CESyn    : CESYNTAX            Ids Op OpAux Cks)
       (Syn      : STCSYNTAX           Ids Op OpAux Cks CESyn)
       (Str      : INDEXEDSTREAMS      Ids Op OpAux Cks)
       (Ord      : STCORDERED          Ids Op OpAux Cks CESyn Syn)
       (CESem    : CESEMANTICS         Ids Op OpAux Cks CESyn               Str)
       (Sem      : STCSEMANTICS        Ids Op OpAux Cks CESyn Syn Ord Str CESem)
       (CEClo    : CECLOCKING          Ids Op OpAux Cks CESyn)
       (Clkg     : STCCLOCKING         Ids Op OpAux Cks CESyn Syn Ord CEClo)
       (CECloSem : CECLOCKINGSEMANTICS Ids Op OpAux Cks CESyn Str CESem              CEClo)
<: STCCLOCKINGSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem Sem CEClo Clkg CECloSem.
  Include STCCLOCKINGSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem Sem CEClo Clkg CECloSem.
End StcClockingSemanticsFun.
