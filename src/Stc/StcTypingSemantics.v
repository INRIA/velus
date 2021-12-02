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


From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import VelusMemory.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import IndexedStreams.
From Velus Require Import Stc.StcIsSystem.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import CoreExpr.CETypingSemantics.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import Stc.StcSemantics.
From Velus Require Import Stc.StcTyping.
From Velus Require Import Stc.StcMemoryCorres.
From Velus Require Import Stc.StcIsDefined.
From Velus Require Import Stc.StcIsNext.
From Velus Require Import Stc.StcIsReset.
From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsFree.
From Velus Require Import Stc.StcWellDefined.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCTYPINGSEMANTICS
       (Import Ids      : IDS)
       (Import Op       : OPERATORS)
       (Import OpAux    : OPERATORS_AUX     Ids Op)
       (Import ComTyp   : COMMONTYPING      Ids Op OpAux)
       (Import Cks      : CLOCKS            Ids Op OpAux)
       (Import CESyn    : CESYNTAX          Ids Op OpAux        Cks)
       (Import Syn      : STCSYNTAX         Ids Op OpAux        Cks CESyn)
       (Import CETyp    : CETYPING          Ids Op OpAux        Cks CESyn)
       (Import StcTyp   : STCTYPING         Ids Op OpAux        Cks CESyn Syn CETyp)
       (Import Str      : INDEXEDSTREAMS    Ids Op OpAux        Cks)
       (Import Next     : STCISNEXT         Ids Op OpAux        Cks CESyn Syn)
       (Import Reset    : STCISRESET        Ids Op OpAux        Cks CESyn Syn)
       (Import Syst     : STCISSYSTEM       Ids Op OpAux        Cks CESyn Syn)
       (Import Var      : STCISVARIABLE     Ids Op OpAux        Cks CESyn Syn)
       (Import Def      : STCISDEFINED      Ids Op OpAux        Cks CESyn Syn Var Next)
       (Import CEIsF    : CEISFREE          Ids Op OpAux        Cks CESyn)
       (Import Free     : STCISFREE         Ids Op OpAux        Cks CESyn Syn CEIsF)
       (Import Ord      : STCORDERED        Ids Op OpAux        Cks CESyn Syn Syst)
       (Import CESem    : CESEMANTICS       Ids Op OpAux        Cks CESyn              Str)
       (Import CETypSem : CETYPINGSEMANTICS Ids Op OpAux ComTyp Cks CESyn        CEIsF Str CESem CETyp)
       (Import Sem      : STCSEMANTICS      Ids Op OpAux        Cks CESyn Syn Syst Ord Str CESem)
       (Import Wdef     : STCWELLDEFINED    Ids Op OpAux        Cks CESyn Syn Syst Ord Var Reset Next CEIsF Free)
       (Import Corres   : STCMEMORYCORRES   Ids Op OpAux        Cks Str CESyn Syn Reset Next Syst Ord CESem Sem).

  Fixpoint insts_of (tcs: list trconstr) : list (ident * ident) :=
    match tcs with
    | [] => []
    | TcStep s _ _ _ b _ :: tcs
    | TcInstReset s _ b :: tcs => (s, b) :: insts_of tcs
    | _ :: tcs => insts_of tcs
    end.

  Lemma insts_of_app:
    forall tcs tcs',
      insts_of (tcs ++ tcs') = insts_of tcs ++ insts_of tcs'.
  Proof.
    induction tcs as [|[]]; simpl; auto; setoid_rewrite IHtcs; auto.
  Qed.

  Lemma reset_nexts_wt_env:
    forall p s S,
      reset_nexts s S ->
      wt_nexts p s.(s_nexts) ->
      wt_env (values S) (map (fun x => (fst x, snd (fst (snd x)))) (s_nexts s)).
  Proof.
    intros * Reset WT.
    apply Forall_forall; intros * Hin.
    apply in_map_iff in Hin as ((?&((?&?)&?))&?& Hin); simpl in *; subst; simpl.
    eapply Forall_forall in WT; eauto; simpl in WT.
    apply Reset in Hin; unfold find_val in Hin.
    rewrite Hin.
    eapply wt_value_const; eauto.
  Qed.

  Corollary initial_state_wt_memory:
    forall S p f s p',
      wt_program p ->
      initial_state p f S ->
      find_system f p = Some (s, p') ->
      wt_memory S p' (mems_of_nexts (s_nexts s)) s.(s_subs).
  Proof.
    induction S as [? IH] using memory_ind'; intros * WT Init Find.
    inversion_clear Init as [??????? Subs].
    match goal with H: find_system f p = _, H': find_system f p = _ |- _ => rewrite H in H'; inv H' end.
    eapply wt_program_find_unit in WT as ((?&?&?)&?); eauto.
    constructor.
    - eapply reset_nexts_wt_env; eauto.
    - apply Forall_forall; intros (?&?) Hin.
      apply Subs in Hin as (Si&?& Init).
      inversion Init; subst.
      eright; eauto.
      eapply IH; eauto.
  Qed.

  Section Trconstr_wt.

    Variables (p: program)
              (R: env)
              (base: bool)
              (S I S': state)
              (Γv Γm: tenv)
              (inputs: list ident)
              (memset: PS.t)
              (insts: list (ident * ident)).

    Hypotheses (WTp: wt_program p)
               (Ord: Ordered_systems p)
               (Ndpenv: NoDupMembers (Γv ++ Γm))
               (Ndpinsts: NoDupMembers insts)
               (WTS: wt_memory S p Γm insts).

    Hypothesis IHp:
      forall f S xs ys S' s p',
        sem_system p f S xs ys S' ->
        find_system f p = Some (s, p') ->
        Forall2 (fun xt v => wt_svalue v (fst (snd xt))) s.(s_in) xs ->
        wt_memory S p (mems_of_nexts (s_nexts s)) s.(s_subs) ->
        wt_memory S' p' (mems_of_nexts (s_nexts s)) s.(s_subs)
        /\ Forall2 (fun xt v => wt_svalue v (fst (snd xt))) s.(s_out) ys.

    Lemma trconstr_cons_wt:
      forall tc tcs vars M,
        sem_trconstr p base R S I S' tc ->
        wt_trconstr p Γv Γm tc ->
        NoDupMembers (nexts_of (tc :: tcs)) ->
        NoDupMembers (steps_of (tc :: tcs)) ->
        incl (nexts_of (tc :: tcs)) Γm ->
        incl (insts_of (tc :: tcs)) insts ->
        incl vars Γv ->
        (forall x, InMembers x vars <-> In x (variables (tc :: tcs))) ->
        (forall x t, In x (variables tcs) -> In (x, t) Γv -> wt_env_svalue R (x, t)) ->
        (forall x t, In (x, t) (nexts_of tcs) -> wt_env_svalue R (x, t)) ->
        (forall x t, Is_free_in_tc x tc -> In (x, t) (Γv ++ Γm) -> wt_env_svalue R (x, t)) ->
        reset_consistency (tc :: tcs) ->
        ireset_consistency (tc :: tcs) ->
        reset_clocks_have_sem base R (tc :: tcs) ->
        ireset_clocks_have_sem base R (tc :: tcs) ->
        Is_well_sch inputs memset (tc :: tcs) ->
        Memory_Corres R base tcs S I S' M ->
        wt_memory M p Γm insts ->
        wt_synchronous_env R (vars ++ nexts_of (tc :: tcs))
        /\ exists M',
            Memory_Corres R base (tc :: tcs) S I S' M'
            /\ wt_memory M' p Γm insts.
    Proof.
      intros * Sem WT NoDupNext NoDupStep Specmems Specinsts Specvars
             Eqvars WTvars WTnexts WTfree NextReset StepIReset ResetCks IResetCks Wsch Corres WTM.
      assert (NoDupMembers Γv) by (eapply NoDupMembers_app_l; eauto).
      assert (NoDupMembers Γm) by (eapply NoDupMembers_app_r; eauto).
      cut ((forall y t, (In y (variables (tc :: tcs)) /\ In (y, t) Γv) \/ In (y, t) (nexts_of (tc :: tcs)) -> wt_env_svalue R (y, t))
           /\ exists M', Memory_Corres R base (tc :: tcs) S I S' M' /\ wt_memory M' p Γm insts).
      { intros []; split; auto.
        apply Forall_forall; intros (y, t) Hin; apply in_app in Hin as [Hin|]; auto.
        assert (In y (variables (tc :: tcs))) as Var by (eapply Eqvars, In_InMembers; eauto).
        apply Specvars in Hin; auto.
      }
      inversion Sem as [????????? Hexp Hvar|
                        ??????|
                        ????????????? Hexp Hvar |
                        ??????????? FindI Init|
                        ??????????????? ClockR Find_I Hexps Hck Hsystem Hvars];
        subst; simpl in *.

      - (* TcDef *)
        split.
        + intros * [[Var Hin]|]; [|now apply WTnexts].
          destruct Var; [|now apply WTvars].
          inv WT; eapply NoDupMembers_det in Hin; eauto; subst.
          unfold sem_var_instant in Hvar; rewrite Hvar.
          eapply sem_caexp_instant_wt; eauto.
          apply Forall_filter.
          apply Forall_forall; intros (y' & t') Hin' Free.
          apply free_in_cexp_spec' in Free.
          assert (Is_free_in_tc y' (TcDef y ck ce)) as Free' by now do 2 constructor.
          now apply WTfree.
        + exists M; split; auto.
          apply Memory_Corres_Def; auto.

      - (* TcReset *)
        split.
        + intros * [[Var Hin]|]; [now apply WTvars|now apply WTnexts].
        + destruct r.
          * eexists; split.
            -- eapply Memory_Corres_Reset_present; eauto.
               eapply Is_well_sch_Reset_Next; eauto.
            -- inv WT; eapply wt_memory_add_val; eauto. inv H9.
               ++ constructor; auto using wt_cvalue_cconst.
               ++ constructor; auto.
          * eexists; split.
            -- eapply Memory_Corres_Reset_absent; eauto.
            -- assumption.

      - (* TcNext *)
        split.
        + intros * [[]|Hin]; [now apply WTvars|].
          destruct Hin as [E|]; [|now apply WTnexts].
          inv E.
          unfold sem_var_instant in Hvar; rewrite Hvar; simpl.
          destruct v'; simpl; auto.
          assert (Forall (fun ckr : clock => exists r : bool, sem_clock_instant base R ckr r) ckrs) as Ckr.
          { eapply ResetCks; left; eauto. }
          eapply reset_or_not_reset_dec' in Ckr as [Reset|NotReset].
          * inversion_clear WTS as [???? WTmems].
            apply incl_cons' in Specmems as [].
            eapply Forall_forall in WTmems; eauto; simpl in *.
            unfold find_val in H1. rewrite H1 in WTmems; eauto.
          * assert (~ Is_next_in y tcs /\ (exists ck : clock, Is_reset_in y ck tcs /\ sem_clock_instant base R ck true)) as NotReset'.
            { split.
              - inv NoDupNext.
                rewrite nexts_of_In, <- fst_InMembers; auto.
              - eapply Exists_exists in NotReset as (?&?&?); repeat esplit; eauto.
                eapply NextReset in H4; eauto. 2:left; constructor.
                inv H4; auto. inv H7.
            }
            eapply Corres in NotReset'. rewrite NotReset' in H2.
            inversion_clear WTM as [???? WTmems].
            apply incl_cons' in Specmems as [].
            eapply Forall_forall in WTmems; eauto; simpl in *.
            unfold find_val in H2. rewrite H2 in WTmems; eauto.
        + inv Hexp; eexists; split.
          * apply Memory_Corres_Next_present; eauto.
          * eapply wt_memory_add_val; eauto.
            -- apply Specmems; left; auto.
            -- inv WT.
               take (sem_exp_instant _ _ _ _) and eapply sem_exp_instant_wt in it; eauto.
               apply Forall_filter.
               apply Forall_forall; intros (y' & t') Hin' Free.
               apply free_in_exp_spec' in Free.
               assert (Is_free_in_tc y' (TcNext x ck ckrs e)) as Free' by now do 2 constructor.
               now apply WTfree.
          * eapply Memory_Corres_Next_absent; eauto; try congruence.
            eapply ResetCks; left; eauto.
          * assumption.

      - split.
        + intros * [[]|]; [now apply WTvars|now apply WTnexts].
        + destruct r.
          * eexists; split.
            -- eapply Memory_Corres_InstReset_present; eauto; try reflexivity.
               eapply Is_well_sch_IReset_Step; eauto.
            -- pose proof Init; inv Init.
               eapply wt_memory_add_inst; eauto.
               ++ apply Specinsts; left; auto.
               ++ eapply initial_state_wt_memory; eauto.
          * exists M; split; auto.
            eapply Memory_Corres_InstReset_absent; try symmetry; eauto.

      - (* TcStep *)
        assert (In (i, f) insts) by (apply Specinsts; now left).
        pose proof Hsystem as Hsystem'; inversion Hsystem'; inv WT.
        match goal with H: find_system _ _ = _, H': find_system _ _ = _ |- _ => rewrite H in H'; inv H' end.
        eapply IHp in Hsystem' as [WTS' WTouts]; eauto.
        + split.
          * intros * [[Var Hin]|]; [|now apply WTnexts].
            apply in_app in Var as [Var|]; [|now apply WTvars].
            apply Forall2_swap_args in WTouts.
            eapply Forall2_trans_ex with (2 := WTouts) in Hvars; eauto.
            eapply Forall2_Forall2 in Hvars; eauto.
            eapply Forall2_in_left in Hvars as ((?&(t',?)) & ? & Hin' & v & Hinv & Hvar & WTv); eauto; simpl in *.
            unfold sem_var_instant in Hvar; rewrite Hvar.
            eapply NoDupMembers_det in Hin; eauto; subst; auto.
          * destruct (clock_of_instant xs) eqn: E.
            -- eexists; split.
               ++ eapply Memory_Corres_Step_present; eauto; reflexivity.
               ++ eapply wt_memory_add_inst; eauto.
            -- assert (absent_list xs) by (apply clock_of_instant_false; auto).
               apply sem_system_absent in Hsystem as (? & ?); auto.
               exists M; split; auto.
               eapply Memory_Corres_Step_absent; eauto.
               eapply IResetCks; left; eauto.
        + apply Forall2_swap_args in Hexps.
          take (Forall2 _ _ (s_in _)) and rename it into Eexps.
          eapply Forall2_trans_ex with (2 := Eexps) in Hexps; eauto.
          take (Forall _ es) and rename it into WTexps.
          clear - WTvars WTnexts WTfree Ndpenv Hexps WTexps.
          induction Hexps as [|? (?&(t',?)) ?? (?&?& Hexp & E)]; constructor; auto.
          simpl; subst.
          eapply Forall_forall in WTexps; eauto.
          eapply sem_exp_instant_wt; eauto.
          apply Forall_filter.
          apply Forall_forall; intros (y & t') Hin' Free.
          apply free_in_exp_spec' in Free.
          assert (Is_free_in_tc y (TcStep i ys ck ckrs f es)) as Free' by (do 2 constructor; apply Exists_exists; eauto).
          now apply WTfree.
        + eapply wt_memory_chained; eauto.
          assert (In (i, f) insts) by (apply Specinsts; now left).
          assert (Forall (fun ckr : clock => exists r : bool, sem_clock_instant base R ckr r) ckrs) as Ckr.
          { eapply IResetCks; left; eauto. }
          eapply reset_or_not_reset_dec' in Ckr as [NotReset|Reset].
          (* destruct rst. *)
          * assert (exists Ii', Ii' ≋ Ii /\ find_inst i S = Some Ii') as (? & <- &?)
                by (apply orel_find_inst_Some; auto).
            inversion_clear WTS as [????? WTinsts].
            eapply Forall_forall in WTinsts; eauto.
            inv WTinsts; try congruence.
            match goal with H: find_inst i S = _, H': find_inst i S = _ |- _ => rewrite H in H'; inv H' end.
            match goal with H: find_system _ _ = _, H': find_unit _ _ = _ |- _ => setoid_rewrite H in H'; inv H' end; auto.
          * assert (~ Is_step_in i tcs /\ (exists ck : clock, Is_ireset_in i ck tcs /\ sem_clock_instant base R ck true)) as Reset'.
            { split.
              - inv NoDupStep.
                rewrite steps_of_In, <- fst_InMembers; auto.
              - eapply Exists_exists in Reset as (?&?&?); repeat esplit; eauto.
                eapply StepIReset in H12; eauto. 2:left; constructor.
                inv H12; auto. inv H15.
            }
            eapply Corres in Reset'.
            unfold state_corres in Reset'.
            rewrite Find_I in Reset'; symmetry in Reset'.
            assert (exists Ii', Ii' ≋ Ii /\ find_inst i M = Some Ii') as (? & <- &?)
                by (apply orel_find_inst_Some; auto).
            inversion_clear WTM as [????? WTinsts].
            eapply Forall_forall in WTinsts; eauto.
            inv WTinsts; try congruence.
            match goal with H: find_inst i M = _, H': find_inst i M = _ |- _ => rewrite H in H'; inv H' end.
            match goal with H: find_system _ _ = _, H': find_unit _ _ = _ |- _ => setoid_rewrite H in H'; inv H' end; auto.
    Qed.

    Lemma sem_trconstrs_nexts_of:
      forall tcs P base R S I S' x v,
        Forall (sem_trconstr P base R S I S') tcs ->
        InMembers x (nexts_of tcs) ->
        sem_var_instant R x (present v) ->
        find_val x I = Some v.
    Proof.
      induction tcs as [|[]]; inversion_clear 1 as [|?? Sem]; simpl;
        intros * Hin Hvar; try contradiction; eauto.
      destruct Hin; eauto; subst.
      inv Sem; cases; try congruence.
    Qed.

    Corollary trconstrs_app_wt:
      forall tcs' tcs vars,
        let alltcs := tcs ++ tcs' in
        Forall (sem_trconstr p base R S I S') alltcs ->
        Forall (wt_trconstr p Γv Γm) alltcs ->
        NoDup (variables alltcs) ->
        NoDupMembers (nexts_of alltcs) ->
        NoDupMembers (steps_of alltcs) ->
        incl (insts_of alltcs) insts ->
        incl (nexts_of alltcs) Γm ->
        incl vars Γv ->
        (forall x, InMembers x vars <-> In x (variables tcs')) ->
        (forall x, PS.mem x memset = true -> InMembers x (nexts_of alltcs)) ->
        (forall x t, In x inputs -> In (x, t) (Γv ++ Γm) -> wt_env_svalue R (x, t)) ->
        reset_consistency alltcs ->
        ireset_consistency alltcs ->
        reset_clocks_have_sem base R alltcs ->
        ireset_clocks_have_sem base R alltcs ->
        Is_well_sch inputs memset alltcs ->
        wt_synchronous_env R (vars ++ nexts_of tcs')
        /\ exists M',
            Memory_Corres R base tcs' S I S' M'
            /\ wt_memory M' p Γm insts.
    Proof.
      induction tcs' as [|tc];
        intros * Semtcs WTtcs Ndpvars NdpNext NdpStep Specinsts Specmems Specvars Eqvars
                 Specmemset WTinputs NextReset StepIReset ResetCks IResetCks WSCH.
      - subst; simpl.
        rewrite app_nil_r; split.
        + apply Forall_forall; intros (x&?) Hin.
          apply In_InMembers, Eqvars in Hin; contradiction.
        + eexists; split; eauto.
          now apply Memory_Corres_empty_equal_memory.
      - subst alltcs.
        pose proof WSCH as WSCH'; apply Forall'_app_r in WSCH'.
        pose proof NextReset as NextReset'; eapply reset_consistency_app in NextReset'; eauto.
        pose proof StepIReset as StepIReset'; eapply ireset_consistency_app in StepIReset'; eauto.
        pose proof ResetCks as ResetCks'; eapply reset_clocks_have_sem_app in ResetCks'; eauto.
        pose proof IResetCks as IResetCks'; eapply ireset_clocks_have_sem_app in IResetCks'; eauto.
        pose proof Semtcs as Semtcs'; apply Forall_app_weaken in Semtcs'; inversion_clear Semtcs' as [|?? Semtc].
        pose proof WTtcs as WTtcs'; apply Forall_app_weaken in WTtcs'; inversion_clear WTtcs' as [|?? WTtc].
        pose proof Specmems as Specmems'; rewrite nexts_of_app in Specmems'; apply incl_app' in Specmems' as [].
        pose proof Specinsts as Specinsts'; rewrite insts_of_app in Specinsts'; apply incl_app' in Specinsts' as [].
        pose proof Ndpvars as Ndpvars'.
        unfold variables in Ndpvars'.
        rewrite flat_map_app in Ndpvars'.
        apply NoDup_app'_iff in Ndpvars' as (?& Ndpvars' &?); simpl in Ndpvars'.
        rewrite Permutation.Permutation_app_comm in Ndpvars'.
        apply NoDup_app'_iff in Ndpvars' as (?&?& Ndpvars').
        pose proof NdpNext as NdpNext'. rewrite nexts_of_app in NdpNext'. apply NoDupMembers_app_r in NdpNext'.
        pose proof NdpStep as NdpStep'. rewrite steps_of_app in NdpStep'. apply NoDupMembers_app_r in NdpStep'.
        rewrite List_shift_first in WSCH, Semtcs, WTtcs, Specmems, Ndpvars, NdpNext, NdpStep, Specmemset, Specinsts,
                                    NextReset, StepIReset, ResetCks, IResetCks.
        assert (exists vars', incl vars' Γv /\ forall x, InMembers x vars' <-> In x (variables tcs')) as (vars' & Specvars' & Eqvars').
        { exists (filter (fun xt => negb (is_variable_in_tc_b (fst xt) tc)) vars); split; [apply incl_filter'; auto|].
          split; intros * Hin.
          - apply InMembers_In in Hin as (?&Hin).
            apply filter_In in Hin as [Hin Nvar].
            apply In_InMembers, Eqvars in Hin. unfold variables in Hin; simpl in Hin.
            apply in_app in Hin as [Hin|]; auto.
            apply Bool.negb_true_iff, Bool.not_true_iff_false in Nvar.
            rewrite <-Is_variable_in_tc_reflect, Is_variable_in_tc_variables_tc in Nvar.
            contradiction.
          - eapply Forall_forall in Ndpvars'; eauto.
            apply filter_InMembers.
            assert (In x (variables (tc :: tcs'))) as Hin'
                by (unfold variables; simpl; apply in_app; auto).
            apply Eqvars, InMembers_In in Hin'; destruct Hin' as (t&?).
            exists t; split; auto.
            rewrite Bool.negb_true_iff, <-Bool.not_true_iff_false,
            <-Is_variable_in_tc_reflect, Is_variable_in_tc_variables_tc; auto.
        }
        edestruct IHtcs' as (WTR' & M' & Corres & WTM'); eauto.
        eapply trconstr_cons_wt; eauto.
        + intros * Hinvars Hin; apply Forall_app in WTR' as [WT].
          assert (In (x, t) vars').
          { apply Eqvars', InMembers_In in Hinvars.
            destruct Hinvars as (t' & Hinvars).
            pose proof Hinvars.
            apply Specvars' in Hinvars.
            assert (NoDupMembers Γv) by (eapply NoDupMembers_app_l; eauto).
            eapply NoDupMembers_det in Hinvars; eauto; subst; auto.
          }
          eapply Forall_forall in WT; eauto.
        + intros; apply Forall_app in WTR' as [? WT].
          eapply Forall_forall in WT; eauto.
        + inversion_clear WSCH' as [|?? [FreeSpec]].
          intros y t Free Hin.
          assert (Free':=Free). apply FreeSpec in Free.
          cases_eqn E.
          -- apply Specmemset in E.
             assert (In (y, t) Γm).
             { apply in_app in Hin as [Hin|]; auto.
               apply In_InMembers in Hin; contradict Hin.
               eapply NoDupMembers_app_InMembers_l; eauto.
               apply InMembers_In in E as (?&E); apply Specmems in E.
               eapply In_InMembers; eauto.
             }
             simpl.
             destruct (Env.find y R) as [[|v]|] eqn: Find; simpl; auto.
             assert (sem_var_instant R y (present v)) as Hvar by auto.
             eapply sem_trconstrs_nexts_of with (1 := Semtcs) in Hvar; eauto.

             assert (Is_next_in y (tcs ++ [tc])) as Next.
             { rewrite fst_InMembers, <-nexts_of_In in E.
               eapply Exists_app' in E as [?|?]; eauto. exfalso.
               eapply Is_well_sch_free_Next; eauto. }
             eapply Exists_exists in Next as (?&Hin'&Next). inv Next.
             assert (Forall (fun ckr : clock => exists r : bool, sem_clock_instant base R ckr r) ckrs) as Ckr.
             { eapply ResetCks. eapply Exists_app'; left.
               eapply Exists_exists; eauto. }
             eapply reset_or_not_reset_dec' in Ckr as [Reset|NotReset].
             ++ eapply Forall_app in Semtcs as (Semtcs&_).
                eapply Forall_forall in Semtcs; eauto. inv Semtcs.
                rewrite <-H16 in H22; rewrite H22 in Hvar; auto.
                inversion_clear WTS as [???? WTmems].
                eapply Forall_forall in WTmems; eauto; simpl in *.
                now unfold find_val in Hvar; rewrite Hvar in WTmems.
             ++ assert (~ Is_next_in y tcs' /\ (exists ck : clock, Is_reset_in y ck tcs' /\ sem_clock_instant base R ck true)) as NotReset'.
                { split; auto.
                  - eapply Exists_exists in NotReset as (?&?&?); repeat esplit; eauto.
                    eapply NextReset in H12; eauto.
                    2:eapply Exists_app'; left; eapply Exists_exists; eauto.
                    apply Exists_app' in H12 as [?|?]; auto.
                    exfalso.
                    eapply Is_well_sch_free_Reset in Free'; eauto.
                }
                eapply Corres in NotReset'. rewrite NotReset' in Hvar.
                inversion_clear WTM' as [???? WTmems].
                eapply Forall_forall in WTmems; eauto; simpl in *.
                now unfold find_val in Hvar; rewrite Hvar in WTmems.
          -- destruct Free as [Var|].
             ++ assert (In (y, t) vars').
                { rewrite Is_variable_in_variables, <-Eqvars' in Var.
                  apply InMembers_In in Var as (t' & Var).
                  assert (t = t') as ->; auto.
                  eapply NoDupMembers_det; [|eauto|]; eauto.
                  apply in_app; left; apply Specvars'; auto.
                }
                apply Forall_app in WTR' as [WT].
                eapply Forall_forall in WT; eauto.
             ++ now apply WTinputs.
    Qed.

    Corollary trconstrs_wt:
      forall tcs vars,
        Forall (sem_trconstr p base R S I S') tcs ->
        Forall (wt_trconstr p Γv Γm) tcs ->
        NoDup (variables tcs) ->
        NoDupMembers (nexts_of tcs) ->
        NoDupMembers (steps_of tcs) ->
        incl (insts_of tcs) insts ->
        incl (nexts_of tcs) Γm ->
        incl vars Γv ->
        (forall x, InMembers x vars <-> In x (variables tcs)) ->
        (forall x, PS.mem x memset = true -> InMembers x (nexts_of tcs)) ->
        (forall x t, In x inputs -> In (x, t) (Γv ++ Γm) -> wt_env_svalue R (x, t)) ->
        Is_well_sch inputs memset tcs ->
        reset_consistency tcs ->
        ireset_consistency tcs ->
        reset_clocks_have_sem base R tcs ->
        ireset_clocks_have_sem base R tcs ->
        wt_synchronous_env R (vars ++ nexts_of tcs)
        /\ exists M',
            Memory_Corres R base tcs S I S' M'
            /\ wt_memory M' p Γm insts.
    Proof.
      intros; eapply trconstrs_app_wt with (tcs := []); eauto.
    Qed.

  End Trconstr_wt.

  Lemma wt_program_Ordered_systems:
    forall p,
      wt_program p ->
      Ordered_systems p.
  Proof.
    intros; eapply wt_program_Ordered_program; eauto.
    intros * [WTtcs] Hin.
    rewrite s_subs_steps_of in Hin.
    induction WTtcs as [|[]]; simpl in Hin; try contradiction; auto.
    destruct Hin; subst; auto.
    take (wt_trconstr _ _ _ _) and inv it.
    take (find_system _ _ = _) and setoid_rewrite it.
    discriminate.
  Qed.

  Fact s_insts_of_subs:
    forall s, incl (insts_of (s_tcs s)) (s_subs s).
  Proof.
    intros; rewrite s_subs_steps_of.
    intros ? Hin.
    rewrite incl_in_app; eauto using s_ireset_incl.
    induction (s_tcs s) as [|[]]; simpl in *; try contradiction; auto;
      destruct Hin as [|Hin]; auto.
    - subst; apply in_app; right; left; auto.
    - apply IHl, in_app in Hin as [|]; apply in_app; auto.
      right; right; auto.
  Qed.

  Lemma sem_system_wt:
    forall p f S xs ys S' s p',
      wt_program p ->
      Well_scheduled p ->
      sem_system p f S xs ys S' ->
      find_system f p = Some (s, p') ->
      wt_memory S p (mems_of_nexts (s_nexts s)) s.(s_subs) ->
      Forall2 (fun xt v => wt_svalue v (fst (snd xt))) s.(s_in) xs ->
      wt_memory S' p' (mems_of_nexts (s_nexts s)) s.(s_subs)
      /\ Forall2 (fun xt v => wt_svalue v (fst (snd xt))) s.(s_out) ys.
  Proof.
    intros (? & p); induction p as [|s']; intros * WTp Wsch Sem Find WTS WTins;
      try now inversion Find.
    pose proof WTp as WTp'; inversion_clear WTp as [|?? [[WTtcs]]].
    inv Wsch.
    apply wt_program_Ordered_systems in WTp'; auto.
    pose proof Find as Find'; eapply find_unit_cons in Find as [[E Find]|[E Find]]; simpl in *; eauto.
    - inv Find.
      inversion_clear Sem as [????????????? Semtcs].
      take (find_system _ _ = _) and eapply find_unit_cons in it as [[E Find]|[E Find]];
        simpl; eauto; try contradiction.
      inv Find.
      assert (~ Is_system_in (s_name s') (s_tcs s')) as Notin by (eapply find_system_not_Is_system_in; eauto).
      apply sem_trconstrs_cons in Semtcs; auto.
      assert (Forall (fun oc => snd oc <> s_name s') (s_subs s')).
      { apply Forall_forall; intros * Hin; apply in_map with (f := snd) in Hin.
        intro E'; rewrite E' in Hin.
        rewrite steps_iresets_of_Is_system_in, map_app, in_app_comm,
        <-incl_in_app, <-s_subs_steps_of in Notin; try contradiction.
        apply incl_map, s_ireset_incl.
      }
      take (wt_memory _ _ _ _) and eapply wt_memory_other in it; simpl in *; eauto.
      assert (NoDupMembers (idty (s_in s' ++ s_vars s' ++ s_out s') ++ mems_of_nexts (s_nexts s'))) as Ndp.
      { pose proof (s_nodup s') as Ndp.
        rewrite ? idty_app, <- ? app_assoc.
        apply fst_NoDupMembers.
        rewrite ? map_app, ? map_fst_idty.
        replace (map fst (mems_of_nexts (s_nexts s'))) with (map fst (s_nexts s')); auto.
        clear; induction (s_nexts s'); simpl; auto; f_equal; auto.
      }
      inv WTp'.
      edestruct trconstrs_wt with (7 := Semtcs) (vars := idty (s_vars s' ++ s_out s')) as (WTR & M' & Corres & WTM');
        eauto using s_nodup_variables, s_reset_consistency, s_ireset_consistency,
        s_nodup_subs, s_nexts_of_mems_of_nexts, s_insts_of_subs; auto.
      + rewrite fst_NoDupMembers, <-s_nexts_in_tcs_fst, <-fst_NoDupMembers. apply s_nodup_nexts.
      + rewrite <-s_subs_steps_of. apply s_nodup_subs.
      + rewrite ? idty_app; apply incl_appr, incl_refl.
      + intro; rewrite <- s_vars_out_in_tcs, fst_InMembers, idty_app, map_app, ? map_fst_idty; reflexivity.
      + intro; setoid_rewrite ps_from_list_In.
        rewrite <- s_nexts_in_tcs.
        clear; induction (s_nexts s'); simpl; intuition auto.
      + intros y t Hin Hin'.
        assert (exists ck, In (y, (t, ck)) (s_in s')) as (?&?).
        { apply fst_InMembers, InMembers_idty in Hin.
          rewrite ? idty_app, <- ? app_assoc in Ndp, Hin'.
          eapply NoDupMembers_app_InMembers in Ndp; eauto.
          apply in_app in Hin' as [Hin'|Hin'].
          - now apply In_idty_exists.
          - apply In_InMembers in Hin'; contradiction.
        }
        take (sem_vars_instant _ _ xs) and rename it into Semins.
        setoid_rewrite Forall2_map_1 in Semins.
        eapply Forall2_Forall2 in WTins; eauto.
        eapply Forall2_in_left in WTins as (?&?& Hvar & WT); eauto; simpl in *.
        now unfold sem_var_instant in Hvar; rewrite Hvar.
      + eapply sem_trconstrs_reset_clocks; eauto using s_reset_consistency.
      + eapply sem_trconstrs_ireset_clocks; eauto using s_ireset_consistency.
      + split.
        * take (state_closed _ _ S) and inv it.
          take (state_closed _ _ S') and inv it.
          repeat match goal with H: find_system _ _ = _, H': find_system _ _ = _ |- _ => rewrite H in H'; inv H' end.
          eapply Memory_Corres_equal_memory in Corres as <-; eauto; intros; eauto.
          -- now rewrite nexts_of_In, s_nexts_in_tcs_fst.
          -- rewrite s_nexts_in_tcs_fst. apply s_reset_incl, resets_of_In; eauto.
          -- now rewrite fst_InMembers, s_subs_steps_of, steps_of_In.
          -- eapply steps_of_In, incl_map. eapply s_ireset_incl.
             eapply iresets_of_In; eauto.
        * rewrite ? idty_app, <- ? app_assoc in WTR.
          repeat setoid_rewrite Forall_app in WTR.
          destruct WTR as (?& WTouts &?).
          take (sem_vars_instant _ _ ys) and rename it into Semouts.
          setoid_rewrite Forall2_map_1 in Semouts.
          clear - Semouts WTouts.
          induction Semouts as [|???? Sem]; inversion_clear WTouts as [|?? WTout];
            constructor; simpl in *; auto.
          now unfold sem_var_instant in Sem; rewrite Sem in WTout.
    - assert (Forall (fun oc => snd oc <> s_name s') (s_subs s)).
      { eapply find_unit_other_not_Is_called_in in WTp'; simpl; eauto; simpl; eauto.
        apply Forall_forall; intros * Hin; apply in_map with (f := snd) in Hin.
        intro E'; rewrite E' in Hin; contradiction.
      }
      take (wt_memory _ _ _ _) and eapply wt_memory_other in it; simpl; eauto.
      eapply IHp; eauto.
      eapply sem_system_cons; eauto.
  Qed.

End STCTYPINGSEMANTICS.

Module StcTypingSemanticsFun
   (Ids      : IDS)
   (Op       : OPERATORS)
   (OpAux    : OPERATORS_AUX     Ids Op)
   (ComTyp   : COMMONTYPING      Ids Op OpAux)
   (Cks      : CLOCKS            Ids Op OpAux)
   (CESyn    : CESYNTAX          Ids Op OpAux        Cks)
   (Syn      : STCSYNTAX         Ids Op OpAux        Cks CESyn)
   (CETyp    : CETYPING          Ids Op OpAux        Cks CESyn)
   (StcTyp   : STCTYPING         Ids Op OpAux        Cks CESyn Syn CETyp)
   (Str      : INDEXEDSTREAMS    Ids Op OpAux        Cks)
   (Next     : STCISNEXT         Ids Op OpAux        Cks CESyn Syn)
   (Reset    : STCISRESET        Ids Op OpAux        Cks CESyn Syn)
   (Syst     : STCISSYSTEM       Ids Op OpAux        Cks CESyn Syn)
   (Var      : STCISVARIABLE     Ids Op OpAux        Cks CESyn Syn)
   (Def      : STCISDEFINED      Ids Op OpAux        Cks CESyn Syn Var Next)
   (CEIsF    : CEISFREE          Ids Op OpAux        Cks CESyn)
   (Free     : STCISFREE         Ids Op OpAux        Cks CESyn Syn CEIsF)
   (Ord      : STCORDERED        Ids Op OpAux        Cks CESyn Syn Syst)
   (CESem    : CESEMANTICS       Ids Op OpAux        Cks CESyn              Str)
   (CETypSem : CETYPINGSEMANTICS Ids Op OpAux ComTyp Cks CESyn        CEIsF Str CESem CETyp)
   (Sem      : STCSEMANTICS      Ids Op OpAux        Cks CESyn Syn Syst Ord Str CESem)
   (Wdef     : STCWELLDEFINED    Ids Op OpAux        Cks CESyn Syn Syst Ord Var Reset Next CEIsF Free)
   (Corres   : STCMEMORYCORRES   Ids Op OpAux        Cks Str CESyn Syn Reset Next Syst Ord CESem Sem)
<: STCTYPINGSEMANTICS Ids Op OpAux ComTyp Cks CESyn Syn CETyp StcTyp Str Next Reset Syst Var Def CEIsF Free Ord CESem CETypSem Sem Wdef Corres.
  Include STCTYPINGSEMANTICS Ids Op OpAux ComTyp Cks CESyn Syn CETyp StcTyp Str Next Reset Syst Var Def CEIsF Free Ord CESem CETypSem Sem Wdef Corres.
End StcTypingSemanticsFun.
