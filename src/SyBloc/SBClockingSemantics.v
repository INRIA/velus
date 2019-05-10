From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.Stream.
From Velus Require Import SyBloc.SBIsLast.
From Velus Require Import SyBloc.SBIsVariable.
From Velus Require Import SyBloc.SBIsDefined.
From Velus Require Import SyBloc.SBIsBlock.
From Velus Require Import SyBloc.SBOrdered.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import SyBloc.SBSyntax.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import SyBloc.SBClocking.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import SyBloc.SBSemantics.
From Velus Require Import CoreExpr.CEClockingSemantics.
From Coq Require Import List.

(** * Link (static) clocking predicates to (dynamic) semantic model *)

(**

These results confirm the correctness of the clocking predicates wrt the
semantics. In particular, they are useful for relating static invariants to
dynamic properties. They hold essentially due to the "additional" clocking
constraints in the NLustre semantic model.

 *)

Module Type SBCLOCKINGSEMANTICS
       (Import Ids      : IDS)
       (Import Op       : OPERATORS)
       (Import OpAux    : OPERATORS_AUX           Op)
       (Import CESyn    : CESYNTAX                Op)
       (Import Syn      : SBSYNTAX            Ids Op       CESyn)
       (Import Str      : STREAM                  Op OpAux)
       (Import Last     : SBISLAST            Ids Op       CESyn Syn)
       (Import Var      : SBISVARIABLE        Ids Op       CESyn Syn)
       (Import Def      : SBISDEFINED         Ids Op       CESyn Syn Var Last)
       (Import Block    : SBISBLOCK           Ids Op       CESyn Syn)
       (Import Ord      : SBORDERED           Ids Op       CESyn Syn Block)
       (Import CESem    : CESEMANTICS         Ids Op OpAux CESyn               Str)
       (Import Sem      : SBSEMANTICS         Ids Op OpAux CESyn Syn Block Ord Str CESem)
       (Import CEClo    : CECLOCKING          Ids Op       CESyn)
       (Import Clkg     : SBCLOCKING          Ids Op       CESyn Syn Last Var Def Block Ord CEClo)
       (Import CECloSem : CECLOCKINGSEMANTICS Ids Op OpAux CESyn Str CESem                  CEClo).

  Lemma clock_match_instant_block_eqs:
    forall P,
      Ordered_blocks P ->
      wc_program P ->
      (forall base R S I S' eq,
          sem_equation P base R S I S' eq ->
          forall iface x ck,
            NoDupMembers iface ->
            wc_equation P iface eq ->
            Is_defined_in_eq x eq ->
            In (x, ck) iface ->
            clock_match_instant base R (x, ck))
      /\
      (forall f S xs ys S',
          sem_block P f S xs ys S' ->
          forall base R b P',
            find_block f P = Some (b, P') ->
            base = clock_of_instant xs ->
            sem_vars_instant R (map fst b.(b_in)) xs ->
            sem_vars_instant R (map fst b.(b_out)) ys ->
            Forall (clock_match_instant base R) (idck b.(b_in)) ->
            Forall (clock_match_instant base R) (idck b.(b_out))).
  Proof.
    intros * Hord WCP; apply sem_equation_block_ind;
      [intros ????????? Hexp Hvar|
       intros ?????????? Find Hvar Hexp Find'|
       intros ?????????? Clock Find Init|
       intros ??????????????? Hexps Clock Rst Find Block Vars Sub IH|
       intros ????????? Find Ins Outs CkVars Heqs Closed Trans Closed' IH].

    - intros iface y yck Hnd Hwc Hdef Hin.
      inv Hdef; inv Hwc.
      match goal with H1:In (x, _) iface, H2:In (x, _) iface |- _ =>
        apply NoDupMembers_det with (1:=Hnd) (2:=H1) in H2; subst end.
      inv Hexp; unfold clock_match_instant; eauto.

    - intros iface y yck Hnd Hwc Hdef Hin.
      inv Hdef; inv Hwc.
      match goal with H1:In (x, _) iface, H2:In (x, _) iface |- _ =>
        apply NoDupMembers_det with (1:=Hnd) (2:=H1) in H2; subst end.
      inv Hexp; unfold clock_match_instant; eauto.

    - intros iface y yck Hnd Hwc Hdef Hin.
      inv Hdef; inv Hwc.

    - intros iface z zck Hndup Hwc Hdef Hiface.
      inversion_clear Hdef as [| |??????? Hyys].
      inversion_clear Block as [?????? R' ?? Hfind Hvi Hvo].
      specialize (IH _ _ _ _ Hfind eq_refl Hvi Hvo).
      assert (Hvi' := Hvi).
      rewrite <-map_fst_idck in Hvi'.
      eapply sem_clocked_vars_instant_clock_match_instant in Hvi'; eauto.
      specialize (IH Hvi').
      inversion_clear Hwc
        as [| | |?????? bl' ? Hfind' (isub & osub & Hfai & Hfao & Hfno)].
      rewrite Hfind in Hfind'; inv Hfind'.

      assert (forall x y ys,
                 InMembers x (bl'.(b_in) ++ bl'.(b_out)) ->
                 orelse isub osub x = Some y ->
                 sem_var_instant R' x ys ->
                 sem_var_instant R y ys) as Htranso.
      { intros; eapply sem_var_instant_transfer_out_instant
                  with (xin := b_in bl') (xout := b_out bl'); eauto.
        - pose proof bl'.(b_nodup) as Hnd.
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
        as (? & Hin & ((x', (xty, xck)) & Hxin &
                       (Hoeq & yck' & Hiface' & Hinst) & Hsvx) & Hsvy); eauto.
      unfold dck in Hinst. simpl in *.
      apply NoDupMembers_det with (1:=Hndup) (2:=Hiface) in Hiface'.
      rewrite <-Hiface' in *.
      unfold idck in *. rewrite Forall_map in IH.
      eapply Forall_forall in IH; eauto; simpl in IH.
      apply wc_find_block with (1:=WCP) in Hfind as (WCi & WCo & WCv & WCeqs).
      assert (In (x', xck) (idck (bl'.(b_in) ++ bl'.(b_out)))) as Hxin'
        by (rewrite idck_app, in_app; right;
            apply In_idck_exists; eauto).
      apply wc_env_var with (1:=WCo) in Hxin'.
      destruct IH as [(Hv & Hc)|((c & Hv) & Hc)].
      + left; split.
        * apply sem_var_instant_det with (1:=Hsvx) in Hv. subst; auto.
        * eapply sem_clock_instant_transfer_out_instant; eauto.
          now setoid_rewrite InMembers_idck; eauto.
      + right; split.
        * exists c; apply sem_var_instant_det with (1:=Hsvx) in Hv. now subst.
        * eapply sem_clock_instant_transfer_out_instant; eauto.
          now setoid_rewrite InMembers_idck; eauto.

    - (* blocks *)
      intros * Find' ? Hin' Hout' Hcm'.
      rewrite Find' in Find; inv Find.
      apply Forall_forall; unfold idck.
      intros (x, xck) Hxin.
      apply In_idck_exists in Hxin as (xty & Hxin). assert (Hxin' := Hxin).
      apply in_map with (f:=fst), block_output_defined_in_eqs in Hxin.
      apply Is_defined_in_In in Hxin as (eq & Heqin & Hxeq).
      eapply Forall_forall in IH; eauto.
      pose proof Find' as Find; apply find_block_app in Find as (?&?&?); subst.
      apply wc_find_block with (1:=WCP) in Find' as (WCi & WCo & WCv & WCeqs).
      eapply Forall_forall in WCeqs; eauto.
      assert (NoDupMembers (idck (b_in bl ++ b_vars bl ++ b_out bl) ++ idck (b_lasts bl)))
        as Hnd.
      { apply fst_NoDupMembers.
        rewrite map_app, 2 map_fst_idck, 2 map_app, <-2 app_assoc.
        apply b_nodup.
      }
      apply IH with (x:=x) (ck:=xck) in Hnd; eauto.
      + simpl in *.
        unfold sem_vars_instant in Ins, Outs, Hin', Hout'.
        rewrite Forall2_map_1 in Hin', Hout'.
        apply Forall2_app with (2:=Hout') in Hin'.
        rewrite Forall2_map_1 in Ins, Outs.
        assert (Hout2:=Outs).
        apply Forall2_app with (1:=Ins) in Hout2.
        apply Forall2_Forall2 with (1:=Outs) in Hout'.
        apply Forall2_in_left with (2:=Hxin') in Hout' as (s & Hsin & Hvs & Hvs').
        destruct Hnd as [(Hv & Hc)|((c & Hv) & Hc)]; simpl in *.
        *{ left; split.
           - apply sem_var_instant_det with (1:=Hvs) in Hv. now subst.
           - eapply clock_vars_to_sem_clock_instant
               with (1:=Hout2) (2:=Hin') in WCo; eauto.
             eapply in_app; eauto.
         }
        *{ right; split.
           - exists c; apply sem_var_instant_det with (1:=Hvs) in Hv. now subst.
           - eapply clock_vars_to_sem_clock_instant
               with (1:=Hout2) (2:=Hin') in WCo; eauto.
             eapply in_app; eauto.
         }
      + apply wc_equation_program_app; auto.
        apply wc_equation_program_cons; auto.
        apply Ordered_blocks_append in Hord; auto.
      + rewrite in_app; left; apply In_idck_exists.
        exists xty; rewrite 2 in_app; auto.
  Qed.


  (* When a block's inputs match their clocks, then so do its outputs.
     This is a consequence (by induction throughout the node hierarchy) of
     the constraints relating streams to their clocks for each case of
     [sem_equation]. *)
  Corollary clock_match_instant_block:
    forall P f S xs ys S' base R b P',
      Ordered_blocks P ->
      wc_program P ->
      sem_block P f S xs ys S' ->
      find_block f P = Some (b, P') ->
      base = clock_of_instant xs ->
      sem_vars_instant R (map fst b.(b_in)) xs ->
      sem_vars_instant R (map fst b.(b_out)) ys ->
      Forall (clock_match_instant base R) (idck b.(b_in)) ->
      Forall (clock_match_instant base R) (idck b.(b_out)).
  Proof.
    intros ?????????? Ord WCP; intros.
    eapply (proj2 (clock_match_instant_block_eqs P Ord WCP)); eauto.
  Qed.

  (* A "version" of [clock_match_node] for "within" a node. *)
  Corollary clock_match_instant_eq:
    forall P base R S I S' iface x ck eq,
      Ordered_blocks P ->
      wc_program P ->
      NoDupMembers iface ->
      sem_equation P base R S I S' eq ->
      wc_equation P iface eq ->
      Is_defined_in_eq x eq ->
      In (x, ck) iface ->
      clock_match_instant base R (x, ck).
  Proof.
    intros ?????????? Ord WCP; intros.
    eapply (proj1 (clock_match_instant_block_eqs P Ord WCP)); eauto.
  Qed.

  Corollary clock_match_instant_eqs:
    forall P base R S I S' inputs vars eqs,
      Ordered_blocks P ->
      wc_program P ->
      NoDupMembers (inputs ++ vars) ->
      Forall (sem_equation P base R S I S') eqs ->
      Forall (wc_equation P (inputs ++ vars)) eqs ->
      Permutation.Permutation (defined eqs) (map fst vars) ->
      forall x xck,
        In (x, xck) vars ->
        clock_match_instant base R (x, xck).
  Proof.
    intros * OP WCP Hndup Hsem Hwc Hdef x xck Hin.
    assert (In x (defined eqs)) as Hxin
        by (now rewrite Hdef; apply in_map with (f:=fst) in Hin).
    apply Is_defined_in_defined, Is_defined_in_In in Hxin
      as (eq & Hieq & Hdeq).
    eapply Forall_forall in Hsem; eauto.
    eapply Forall_forall in Hwc; eauto.
    eapply clock_match_instant_eq; eauto.
    rewrite in_app; auto.
  Qed.

End SBCLOCKINGSEMANTICS.

Module SBClockingSemanticsFun
       (Import Ids      : IDS)
       (Import Op       : OPERATORS)
       (Import OpAux    : OPERATORS_AUX           Op)
       (Import CESyn    : CESYNTAX                Op)
       (Import Syn      : SBSYNTAX            Ids Op       CESyn)
       (Import Str      : STREAM                  Op OpAux)
       (Import Last     : SBISLAST            Ids Op       CESyn Syn)
       (Import Var      : SBISVARIABLE        Ids Op       CESyn Syn)
       (Import Def      : SBISDEFINED         Ids Op       CESyn Syn Var Last)
       (Import Block    : SBISBLOCK           Ids Op       CESyn Syn)
       (Import Ord      : SBORDERED           Ids Op       CESyn Syn Block)
       (Import CESem    : CESEMANTICS         Ids Op OpAux CESyn               Str)
       (Import Sem      : SBSEMANTICS         Ids Op OpAux CESyn Syn Block Ord Str CESem)
       (Import CEClo    : CECLOCKING          Ids Op       CESyn)
       (Import Clkg     : SBCLOCKING          Ids Op       CESyn Syn Last Var Def Block Ord CEClo)
       (Import CECloSem : CECLOCKINGSEMANTICS Ids Op OpAux CESyn Str CESem                  CEClo)
<: SBCLOCKINGSEMANTICS Ids Op OpAux CESyn Syn Str Last Var Def Block Ord CESem Sem CEClo Clkg CECloSem.
  Include SBCLOCKINGSEMANTICS Ids Op OpAux CESyn Syn Str Last Var Def Block Ord CESem Sem CEClo Clkg CECloSem.
End SBClockingSemanticsFun.
