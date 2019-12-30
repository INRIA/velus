(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import IndexedStreams.
From Velus Require Import Stc.StcIsInit.
From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsDefined.
From Velus Require Import Stc.StcIsSystem.
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
       (Import OpAux    : OPERATORS_AUX           Op)
       (Import CESyn    : CESYNTAX                Op)
       (Import Syn      : STCSYNTAX           Ids Op       CESyn)
       (Import Str      : INDEXEDSTREAMS          Op OpAux)
       (Import Init     : STCISINIT           Ids Op       CESyn Syn)
       (Import Var      : STCISVARIABLE       Ids Op       CESyn Syn)
       (Import Def      : STCISDEFINED        Ids Op       CESyn Syn Var Init)
       (Import Syst     : STCISSYSTEM         Ids Op       CESyn Syn)
       (Import Ord      : STCORDERED          Ids Op       CESyn Syn Syst)
       (Import CESem    : CESEMANTICS         Ids Op OpAux CESyn               Str)
       (Import Sem      : STCSEMANTICS        Ids Op OpAux CESyn Syn Syst Ord Str CESem)
       (Import CEClo    : CECLOCKING          Ids Op       CESyn)
       (Import Clkg     : STCCLOCKING         Ids Op       CESyn Syn Init Var Def Syst Ord CEClo)
       (Import CECloSem : CECLOCKINGSEMANTICS Ids Op OpAux CESyn Str CESem                  CEClo).

  Lemma sem_clocked_var_instant_tc:
    forall P base R S I S' vars x ck tc,
      Ordered_systems P ->
      wc_program P ->
      NoDupMembers vars ->
      sem_trconstr P base R S I S' tc ->
      wc_trconstr P vars tc ->
      Is_defined_in_tc x tc ->
      In (x, ck) vars ->
      sem_clocked_var_instant base R x ck.
  Proof.
    intros ?????????? Ord WCP Nodup Sem WC Def Hin.
    revert dependent ck; revert dependent x; revert dependent vars.
    induction Sem as [????????? Hexp Hvar|
                      ?????????? Find Hvar Hexp Find'|
                      ?????????? Clock Find Init|
                      ??????????????? Hexps Clock Rst Find System Vars Sub IH|
                      ????????? Find Hins Houts Hvars Htcs ??? IH]
                       using sem_trconstr_mult with
        (P_system := fun f S xs ys S' =>
                       forall base R s P',
                         find_system f P = Some (s, P') ->
                         base = clock_of_instant xs ->
                         sem_vars_instant R (map fst s.(s_in)) xs ->
                         sem_vars_instant R (map fst s.(s_out)) ys ->
                         sem_clocked_vars_instant base R (idck s.(s_in)) ->
                         sem_clocked_vars_instant base R (idck s.(s_out)));
      intros; try inversion Def as [| |??????? Hyys];
      try inversion WC
        as [| | |?????? bl' ? sub Hfind' Hfai Hfao]; subst.

    - match goal with H1:In (x, _) vars, H2:In (x, _) vars |- _ =>
                      eapply NoDupMembers_det with (2:=H1) in H2; eauto; subst end.
      unfold sem_clocked_var_instant.
      inv Hexp; eauto; intuition; eauto; by_sem_det.

    - match goal with H1:In (x, _) vars, H2:In (x, _) vars |- _ =>
        eapply NoDupMembers_det with (2:=H1) in H2; eauto; subst end.
      unfold sem_clocked_var_instant.
      inv Hexp; eauto; intuition; eauto; by_sem_det.

    - inversion_clear System as [?????? R' ?? Hfind Hvi Hvo Hsck].
      specialize (IH _ _ _ _ Hfind eq_refl Hvi Hvo).
      assert (Hvi' := Hvi).
      rewrite <-map_fst_idck in Hvi'.
      specialize (IH Hsck).
      rewrite Hfind in Hfind'; inv Hfind'.

      assert (forall x y ys,
                 InMembers x (idck (bl'.(s_in) ++ bl'.(s_out))) ->
                 sub x = Some y ->
                 sem_var_instant R' x ys ->
                 sem_var_instant R y ys) as Htranso.
      { setoid_rewrite InMembers_idck.
        intros; eapply sem_var_instant_transfer_out_instant
                  with (xin := s_in bl') (xout := s_out bl'); eauto.
        - pose proof bl'.(s_nodup) as Hnd.
          rewrite 2 app_assoc in Hnd; apply NoDup_app_weaken in Hnd.
          rewrite <-app_assoc, NoDup_swap, NoDup_app'_iff in Hnd.
          rewrite fst_NoDupMembers, map_app; intuition.
        - apply Forall2_impl_In with (2:=Hfai); intuition.
        - apply Forall2_impl_In with (2:=Hfao); intuition.
      }

      rewrite <-map_fst_idck in Hvo. unfold idck in Hvo. rewrite map_map in Hvo.
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
      eapply NoDupMembers_det with (2:=Hin) in Hin'; eauto; subst yck'.
      unfold idck in *. setoid_rewrite Forall_map in IH.
      eapply Forall_forall in IH; eauto; simpl in IH.
      apply wc_find_system with (1:=WCP) in Hfind as (WCi & WCo & WCv & WCtcs).
      assert (In (x', xck) (idck (bl'.(s_in) ++ bl'.(s_out)))) as Hxin'
        by (rewrite idck_app, in_app; right;
            apply In_idck_exists; eauto).
      apply wc_env_var with (1:=WCo) in Hxin'.
      destruct s.
      + split; intuition; eauto; try by_sem_det;
          eapply IH, sem_clock_instant_transfer_out_instant in Hsvx; eauto; by_sem_det.
      + split; intuition; eauto; try by_sem_det.
        * eapply sem_clock_instant_transfer_out_instant; eauto; eapply IH; eauto.
        * assert (exists c, sem_var_instant R' x' (present c)) as Hsvx' by eauto.
          eapply IH, sem_clock_instant_transfer_out_instant in Hsvx'; eauto; by_sem_det.

    - (* systems *)
      rename H2 into Find'; rename H4 into Hins'; rename H5 into Houts'.
      rewrite Find' in Find; inv Find.
      apply Forall_forall; unfold idck.
      intros (x, xck) Hxin.
      apply In_idck_exists in Hxin as (xty & Hxin). assert (Hxin' := Hxin).
      apply in_map with (f:=fst), system_output_defined_in_tcs in Hxin.
      apply Is_defined_in_In in Hxin as (tc & Htcin & Hxtc).
      eapply Forall_forall in IH; eauto.
      pose proof Find' as Find; apply find_system_app in Find as (?&?&?); subst.
      apply wc_find_system with (1:=WCP) in Find' as (WCi & WCo & WCv & WCtcs).
      eapply Forall_forall in WCtcs; eauto.
      assert (NoDupMembers (idck (s_in s ++ s_vars s ++ s_out s) ++ idck (s_inits s)))
        as Hnd.
      { apply fst_NoDupMembers.
        rewrite map_app, 2 map_fst_idck, 2 map_app, <-2 app_assoc.
        apply s_nodup.
      }
      apply IH with (x:=x) (ck:=xck) in Hnd; eauto.
      + simpl in *.
        unfold sem_vars_instant in Hins, Houts, Hins', Houts'.
        rewrite Forall2_map_1 in Hins', Houts'.
        apply Forall2_app with (2:=Houts') in Hins'.
        rewrite Forall2_map_1 in Hins, Houts.
        assert (Houts2:=Houts).
        apply Forall2_app with (1:=Hins) in Houts2.
        apply Forall2_Forall2 with (1:=Houts) in Houts'.
        apply Forall2_in_left with (2:=Hxin') in Houts' as (? & Hsin & Hvs & Hvs').
        destruct x1.
      (* * split; intuition; eauto; try by_sem_det. *)
        * split; intuition; eauto; try by_sem_det.
          -- eapply Hnd in Hvs.
             eapply clock_vars_to_sem_clock_instant with (Hn' := R) in H2; eauto; try by_sem_det.
             eapply in_app; eauto.
          -- eapply clock_vars_to_sem_clock_instant; eauto.
             ++ eapply in_app; eauto.
             ++ apply Hnd; auto.
        * split; intuition; eauto; try by_sem_det;
          assert (exists c, sem_var_instant R x (present c)) as Hvs'' by eauto.
          -- eapply clock_vars_to_sem_clock_instant; eauto.
             ++ eapply in_app; eauto.
             ++ apply Hnd; auto.
          -- eapply Hnd in Hvs''.
             eapply clock_vars_to_sem_clock_instant with (Hn' := R0) in Hvs''; eauto; try by_sem_det.
             eapply in_app; eauto.
      + apply wc_trconstr_program_app; auto.
        apply wc_trconstr_program_cons; auto.
        apply Ordered_systems_append in Ord; auto.
      + rewrite in_app; left; apply In_idck_exists.
        exists xty; rewrite 2 in_app; auto.
  Qed.

  Corollary sem_clocked_var_instant_tcs:
    forall P base R S I S' inputs vars tcs,
      Ordered_systems P ->
      wc_program P ->
      NoDupMembers (inputs ++ vars) ->
      Forall (sem_trconstr P base R S I S') tcs ->
      Forall (wc_trconstr P (inputs ++ vars)) tcs ->
      Permutation.Permutation (defined tcs) (map fst vars) ->
      forall x xck,
        In (x, xck) vars ->
        sem_clocked_var_instant base R x xck.
  Proof.
    intros * OP WCP Hndup Hsem Hwc Hdef x xck Hin.
    assert (In x (defined tcs)) as Hxin
        by (now rewrite Hdef; apply in_map with (f:=fst) in Hin).
    apply Is_defined_in_defined, Is_defined_in_In in Hxin
      as (tc & Hitc & Hdtc).
    eapply Forall_forall in Hsem; eauto.
    eapply Forall_forall in Hwc; eauto.
    eapply sem_clocked_var_instant_tc; eauto.
    rewrite in_app; auto.
  Qed.

End STCCLOCKINGSEMANTICS.

Module StcClockingSemanticsFun
       (Import Ids      : IDS)
       (Import Op       : OPERATORS)
       (Import OpAux    : OPERATORS_AUX           Op)
       (Import CESyn    : CESYNTAX                Op)
       (Import Syn      : STCSYNTAX           Ids Op       CESyn)
       (Import Str      : INDEXEDSTREAMS          Op OpAux)
       (Import Init     : STCISINIT           Ids Op       CESyn Syn)
       (Import Var      : STCISVARIABLE       Ids Op       CESyn Syn)
       (Import Def      : STCISDEFINED        Ids Op       CESyn Syn Var Init)
       (Import Syst     : STCISSYSTEM         Ids Op       CESyn Syn)
       (Import Ord      : STCORDERED          Ids Op       CESyn Syn Syst)
       (Import CESem    : CESEMANTICS         Ids Op OpAux CESyn               Str)
       (Import Sem      : STCSEMANTICS        Ids Op OpAux CESyn Syn Syst Ord Str CESem)
       (Import CEClo    : CECLOCKING          Ids Op       CESyn)
       (Import Clkg     : STCCLOCKING         Ids Op       CESyn Syn Init Var Def Syst Ord CEClo)
       (Import CECloSem : CECLOCKINGSEMANTICS Ids Op OpAux CESyn Str CESem                  CEClo)
<: STCCLOCKINGSEMANTICS Ids Op OpAux CESyn Syn Str Init Var Def Syst Ord CESem Sem CEClo Clkg CECloSem.
  Include STCCLOCKINGSEMANTICS Ids Op OpAux CESyn Syn Str Init Var Def Syst Ord CESem Sem CEClo Clkg CECloSem.
End StcClockingSemanticsFun.
