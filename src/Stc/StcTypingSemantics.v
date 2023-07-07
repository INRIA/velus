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
From Velus Require Import FunctionalEnvironment.
From Velus Require Import IndexedStreams.
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
       (Import CEIsF    : CEISFREE          Ids Op OpAux        Cks CESyn)
       (Import Free     : STCISFREE         Ids Op OpAux        Cks CESyn Syn CEIsF)
       (Import Ord      : STCORDERED        Ids Op OpAux        Cks CESyn Syn)
       (Import CESem    : CESEMANTICS       Ids Op OpAux        Cks CESyn              Str)
       (Import CETypSem : CETYPINGSEMANTICS Ids Op OpAux ComTyp Cks CESyn        CEIsF Str CESem CETyp)
       (Import Sem      : STCSEMANTICS      Ids Op OpAux        Cks CESyn Syn Ord Str CESem)
       (Import Wdef     : STCWELLDEFINED    Ids Op OpAux        Cks CESyn Syn Ord CEIsF Free)
       (Import Corres   : STCMEMORYCORRES   Ids Op OpAux        Cks Str CESyn Syn Ord CESem Sem).

  Fixpoint insts_of (tcs: list trconstr) : list (ident * ident) :=
    match tcs with
    | [] => []
    | TcReset _ (ResInst s b) :: tcs
    | TcUpdate _ _ (UpdInst s _ b _) :: tcs => (s, b) :: insts_of tcs
    | _ :: tcs => insts_of tcs
    end.

  Lemma insts_of_app:
    forall tcs tcs',
      insts_of (tcs ++ tcs') = insts_of tcs ++ insts_of tcs'.
  Proof.
    induction tcs as [|[|? []|?? []]]; simpl; auto; setoid_rewrite IHtcs; auto.
  Qed.

  Lemma reset_states_wt_env {prefs}:
    forall (p: @program prefs) (s: @system prefs) S,
      reset_states s S ->
      wt_states p (s.(s_lasts) ++ s.(s_nexts)) ->
      wt_env (values S) (map (fun x => (fst x, snd (fst (snd x)))) (s_lasts s ++ s_nexts s)).
  Proof.
    intros * Reset WT.
    unfold wt_env, wt_states in *.
    simpl_Forall.
    apply Reset in H; unfold find_val in H.
    rewrite H.
    eapply wt_value_const; eauto.
  Qed.

  Corollary initial_state_wt_memory {prefs}:
    forall S (p: @program prefs) f s p',
      wt_program p ->
      initial_state p f S ->
      find_system f p = Some (s, p') ->
      wt_memory S p' (mems_of_states (s_lasts s ++ s_nexts s)) s.(s_subs).
  Proof.
    induction S as [? IH] using memory_ind'; intros * WT Init Find.
    inversion_clear Init as [??????? Subs].
    match goal with H: find_system f p = _, H': find_system f p = _ |- _ => rewrite H in H'; inv H' end.
    eapply wt_program_find_unit in WT as ((?&?&?)&?); eauto.
    constructor.
    - eapply reset_states_wt_env; eauto.
    - apply Forall_forall; intros (?&?) Hin.
      apply Subs in Hin as (Si&?& Init).
      inversion Init; subst.
      eright; eauto.
      eapply IH; eauto.
  Qed.

  Section Trconstr_wt.
    Context {prefs : PS.t}.

    Variables (p: @program prefs)
              (R: env)
              (base: bool)
              (S I S': state)
              (Γ: list (ident * (type * bool)))
              (inputs: list ident)
              (insts: list (ident * ident)).

    Hypotheses (WTp: wt_program p)
               (Ord: Ordered_systems p)
               (Ndpenv: NoDupMembers Γ)
               (Ndpinsts: NoDupMembers insts)
               (WTS: wt_memory S p (idfst Γ) insts).

    Hypothesis IHp:
      forall f S xs ys S' s p',
        sem_system p f S xs ys S' ->
        find_system f p = Some (s, p') ->
        Forall2 (fun xt v => wt_svalue v (fst (snd xt))) s.(s_in) xs ->
        wt_memory S p (mems_of_states (s_lasts s ++ s_nexts s)) s.(s_subs) ->
        wt_memory S' p' (mems_of_states (s_lasts s ++ s_nexts s)) s.(s_subs)
        /\ Forall2 (fun xt v => wt_svalue v (fst (snd xt))) s.(s_out) ys.

    Definition types_nolast (Γ: tenv) := map (fun '(x, ty) => (x, (ty, false))) Γ.
    Definition types_last (Γ: tenv) := map (fun '(x, ty) => (x, (ty, true))) Γ.
    Hint Unfold types_nolast types_last : list.

    Lemma trconstr_cons_wt mems:
      forall tc tcs defs M,
        sem_trconstr p base R S I S' tc ->
        wt_trconstr p Γ tc ->
        NoDupMembers (lasts_of (tc :: tcs) ++ nexts_of (tc :: tcs)) ->
        NoDupMembers (Syn.insts_of (tc :: tcs)) ->
        incl (lasts_of (tc :: tcs)) (idfst Γ) ->
        incl (nexts_of (tc :: tcs)) (idfst Γ) ->
        incl (insts_of (tc :: tcs)) insts ->
        incl defs (idfst Γ) ->
        (forall x, InMembers x defs <-> In x (defined (tc :: tcs))) ->
        (forall x t islast, In x (defined tcs) -> In (x, (t, islast)) Γ -> wt_env_svalue R (Var x) t) ->
        (forall x t, In (x, t) (lasts_of tcs) -> wt_env_svalue R (Last x) t) ->
        (forall x t, In (x, t) (nexts_of tcs) -> wt_env_svalue R (Var x) t) ->
        (forall x t islast, Is_free_in_tc (Var x) tc -> In (x, (t, islast)) Γ -> wt_env_svalue R (Var x) t) ->
        (forall x t, Is_free_in_tc (Last x) tc -> In (x, (t, true)) Γ -> wt_env_svalue R (Last x) t) ->
        last_consistency (tc :: tcs) ->
        next_consistency (tc :: tcs) ->
        inst_consistency (tc :: tcs) ->
        last_reset_clocks_have_sem base (var_env R) (tc :: tcs) ->
        next_reset_clocks_have_sem base (var_env R) (tc :: tcs) ->
        inst_reset_clocks_have_sem base (var_env R) (tc :: tcs) ->
        Is_well_sch inputs mems (tc :: tcs) ->
        Memory_Corres R base tcs S I S' M ->
        wt_memory M p (idfst Γ) insts ->
        wt_synchronous_env R (types_nolast defs ++ types_last (lasts_of (tc :: tcs)) ++ types_nolast (nexts_of (tc :: tcs)))
        /\ exists M',
            Memory_Corres R base (tc :: tcs) S I S' M'
            /\ wt_memory M' p (idfst Γ) insts.
    Proof.
      intros * Sem WT NoDupStates NoDupStep Speclasts Specnexts Specinsts Specdefs
             Eqdefs WTdefs WTlasts WTnexts WTfree WTfreel LastReset NextReset InstReset
             LResetCks NResetCks IResetCks Wsch Corres WTM.
      (* assert (NoDupMembers Γv) by (eapply NoDupMembers_app_l; eauto). *)
      (* assert (NoDupMembers Γm) by (eapply NoDupMembers_app_r; eauto). *)
      cut (((forall y t islast, (In y (defined (tc :: tcs)) /\ In (y, (t, islast)) Γ) \/ In (y, t) (nexts_of (tc :: tcs)) -> wt_env_svalue R (Var y) t)
            /\ (forall y t, In (y, t) (lasts_of (tc :: tcs)) -> wt_env_svalue R (Last y) t))
           /\ exists M', Memory_Corres R base (tc :: tcs) S I S' M' /\ wt_memory M' p (idfst Γ) insts).
      { intros ((Vars&Lasts)&Mem); split; auto.
        apply Forall_forall; intros (y, t) Hin.
        rewrite 2 in_app_iff in Hin. destruct Hin as [|[|]]; simpl_In. all:split; auto.
        + assert (In y (defined (tc :: tcs))) as Var by (eapply Eqdefs, In_InMembers; eauto).
          apply Specdefs in Hin. simpl_In.
          eapply Vars; eauto.
        + apply Speclasts in Hin as Hin'. simpl_In.
          eapply Vars; eauto. left. split; eauto.
          apply incl_defined_lasts with (tcs:=tc::tcs). solve_In.
        + eapply Vars with (islast:=true); eauto.
      }
      inversion Sem as [????????? Hexp Hvar|
                        ??????|
                        ??????????? FindI Init|
                        ??????????? FindS FindI Hexp Hlast Hvar FindS' |
                        ??????????? FindS FindI Hexp Hvar FindS' |
                        ??????????????? ClockR Find_I Hexps Hck Hsystem Hdefs];
        subst; simpl in *.

      - (* TcDef *)
        split; [split|]; auto.
        + intros * [[[|Var] Hin]|]; [| |now apply WTnexts]; eauto; subst.
          inv WT; eapply NoDupMembers_det in Hin; eauto; inv Hin.
          unfold sem_var_instant in Hvar. unfold wt_env_svalue. rewrite Hvar.
          eapply sem_arhs_instant_wt; eauto with stcfree.
        + exists M; split; auto.
          apply Memory_Corres_Def; auto.

      - (* Reset Last *)
        split; [split|]; eauto.
        + intros * [[Var Hin]|]; [now eapply WTdefs; eauto|now apply WTnexts].
        + destruct r; eauto using Memory_Corres_Reset_absent.
          eexists; split.
          * eapply Memory_Corres_Reset_present; eauto using Is_well_sch_Reset_Last, Is_well_sch_Reset_Next.
          * inv WT; eapply wt_memory_add_val; eauto.
            -- now apply NoDupMembers_idfst.
            -- solve_In.
            -- take (wt_const _ _ _) and inv it; constructor; auto using wt_cvalue_cconst.

      - (* Reset Inst *)
        split; [split|]; auto.
        + intros * [[Var Hin]|]; [now eapply WTdefs; eauto|now apply WTnexts].
        + destruct r; eauto using Memory_Corres_InstReset_absent.
          eexists; split.
          * eapply Memory_Corres_InstReset_present; eauto; try reflexivity.
            eapply Is_well_sch_Reset_Inst; eauto.
          * pose proof Init. inv Init.
            eapply wt_memory_add_inst; eauto.
            -- apply Specinsts; left; auto.
            -- eapply initial_state_wt_memory; eauto.

      - (* Update Last *)
        split; [split|]; auto.
        + intros * [[[] Hin]|]; eauto; subst.
          unfold wt_env_svalue. unfold sem_var_instant in Hvar; rewrite Hvar.
          inv WT; eapply NoDupMembers_det in Hin; eauto; inv Hin.
          eapply sem_caexp_instant_wt; eauto with stcfree.
        + intros * [Eq|]; eauto; inv Eq.
          unfold wt_env_svalue. unfold sem_var_instant in Hlast; rewrite Hlast.
          destruct v'; simpl; auto.
          assert (Forall (fun ckr : clock => exists r : bool, sem_clock_instant base (var_env R) ckr r) ckrs) as Ckr.
          { eapply LResetCks; left; eauto with stcsyntax. }
          eapply reset_or_not_reset_dec' in Ckr as [Reset|NotReset].
          * inversion_clear WTS as [???? WTmems].
            apply incl_cons' in Speclasts as [].
            eapply Forall_forall in WTmems; eauto; simpl in *.
            unfold find_val in FindS. rewrite FindS in WTmems; eauto.
          * assert (~ Is_update_last_in y tcs /\ ~ Is_update_next_in y tcs
                    /\ (exists ck : clock, Is_reset_state_in y ck tcs /\ sem_clock_instant base (var_env R) ck true)) as NotReset'.
            { split; [|split].
              - inv NoDupStates.
                rewrite lasts_of_In, <- fst_InMembers. rewrite InMembers_app in *. auto.
              - inv NoDupStates.
                rewrite nexts_of_In, <- fst_InMembers. rewrite InMembers_app in *. auto.
              - eapply Exists_exists in NotReset as (?&?&?); repeat esplit; eauto.
                take (In _ ckrs) and eapply LastReset in it; eauto. 2:left; constructor.
                inv it; auto. take (Is_reset_state_in_tc _ _ _) and inv it.
            }
            eapply Corres in NotReset'. rewrite NotReset' in FindI.
            inversion_clear WTM as [???? WTmems].
            apply incl_cons' in Speclasts as [].
            eapply Forall_forall in WTmems; eauto; simpl in *.
            unfold find_val in FindI. rewrite FindI in WTmems; eauto.
        + inv Hexp; eexists; split.
          * apply Memory_Corres_Last_present; eauto.
          * eapply wt_memory_add_val; eauto.
            -- now apply NoDupMembers_idfst.
            -- apply Speclasts; left; auto.
            -- inv WT.
               take (sem_cexp_instant _ _ _ _) and eapply sem_cexp_instant_wt in it; eauto with stcfree.
          * eapply Memory_Corres_Last_absent; eauto; try congruence.
            eapply LResetCks; left; eauto with stcsyntax.
          * assumption.

      - (* Update Next *)
        split; [split|]; auto.
        + intros * [[? Hin]|[]]; eauto; subst. inv H.
          unfold wt_env_svalue. unfold sem_var_instant in Hvar; rewrite Hvar; simpl.
          destruct v'; simpl; auto.
          assert (Forall (fun ckr : clock => exists r : bool, sem_clock_instant base (var_env R) ckr r) ckrs) as Ckr.
          { eapply NResetCks; left; eauto with stcsyntax. }
          eapply reset_or_not_reset_dec' in Ckr as [Reset|NotReset].
          * inversion_clear WTS as [???? WTmems].
            apply incl_cons' in Specnexts as [].
            eapply Forall_forall in WTmems; eauto; simpl in *.
            unfold find_val in FindS. rewrite FindS in WTmems; eauto.
          * assert (~ Is_update_last_in y tcs /\ ~ Is_update_next_in y tcs
                    /\ (exists ck : clock, Is_reset_state_in y ck tcs /\ sem_clock_instant base (var_env R) ck true)) as NotReset'.
            { split; [|split].
              - rewrite lasts_of_In, <- fst_InMembers. intros contra.
                eapply NoDupMembers_app_InMembers in NoDupStates; eauto.
                apply NoDupStates; simpl; auto.
              - apply NoDupMembers_app_r in NoDupStates. inv NoDupStates.
                rewrite nexts_of_In, <- fst_InMembers. auto.
              - eapply Exists_exists in NotReset as (?&?&?); repeat esplit; eauto.
                take (In _ ckrs) and eapply NextReset in it; eauto. 2:left; constructor.
                inv it; auto. take (Is_reset_state_in_tc _ _ _) and inv it.
            }
            eapply Corres in NotReset'. rewrite NotReset' in FindI.
            inversion_clear WTM as [???? WTmems].
            apply incl_cons' in Specnexts as [].
            eapply Forall_forall in WTmems; eauto; simpl in *.
            unfold find_val in FindI. rewrite FindI in WTmems; eauto.
        + inv Hexp; eexists; split.
          * apply Memory_Corres_Next_present; eauto.
          * eapply wt_memory_add_val; eauto.
            -- now apply NoDupMembers_idfst.
            -- apply Specnexts; left; auto.
            -- inv WT.
               take (sem_exp_instant _ _ _ _) and eapply sem_exp_instant_wt in it; eauto with stcfree.
          * eapply Memory_Corres_Next_absent; eauto; try congruence.
            eapply NResetCks; left; eauto with stcsyntax.
          * assumption.

      - (* Update Inst *)
        assert (In (i, f) insts) by (apply Specinsts; now left).
        pose proof Hsystem as Hsystem'; inversion Hsystem'; inv WT.
        match goal with H: find_system _ _ = _, H': find_system _ _ = _ |- _ => rewrite H in H'; inv H' end.
        eapply IHp in Hsystem' as [WTS' WTouts]; eauto.
        + split; [split|]; auto.
          * intros * [[Var Hin]|]; eauto.
            apply in_app in Var as [Var|]; eauto.
            apply Forall2_swap_args in WTouts.
            eapply Forall2_trans_ex with (2 := WTouts) in Hdefs; eauto.
            eapply Forall2_Forall2 in Hdefs; eauto.
            eapply Forall2_in_left in Hdefs as ((?&(t',?)) & ? & Hin' & v & Hinv & Hvar & WTv); eauto; simpl in *.
            unfold wt_env_svalue. unfold sem_var_instant, var_env in Hvar; rewrite Hvar.
            eapply NoDupMembers_det in Hin; eauto; inv Hin; auto.
          * destruct (clock_of_instant xs) eqn: E.
            -- eexists; split.
               ++ eapply Memory_Corres_Step_present; eauto; reflexivity.
               ++ eapply wt_memory_add_inst; eauto.
            -- assert (absent_list xs) by (apply clock_of_instant_false; auto).
               apply sem_system_absent in Hsystem as (? & ?); auto.
               exists M; split; auto.
               eapply Memory_Corres_Step_absent; eauto.
               eapply IResetCks; left; eauto with stcsyntax.
        + apply Forall2_swap_args in Hexps.
          take (Forall2 _ _ (s_in _)) and rename it into Eexps.
          eapply Forall2_trans_ex with (2 := Eexps) in Hexps; eauto.
          take (Forall _ es) and rename it into WTexps.
          clear - WTdefs WTlasts WTfree WTfreel Ndpenv Hexps WTexps.
          induction Hexps as [|? (?&(t',?)) ?? (?&?& Hexp & E)]; constructor; auto.
          simpl; subst.
          eapply Forall_forall in WTexps; eauto.
          eapply sem_exp_instant_wt; eauto; intros; [eapply WTfree|eapply WTfreel]; eauto.
          1,2:constructor; left; solve_Exists.
        + eapply wt_memory_chained; eauto.
          assert (In (i, f) insts) by (apply Specinsts; now left).
          assert (Forall (fun ckr : clock => exists r : bool, sem_clock_instant base (var_env R) ckr r) ckrs) as Ckr.
          { eapply IResetCks; left; eauto with stcsyntax. }
          eapply reset_or_not_reset_dec' in Ckr as [NotReset|Reset].
          (* destruct rst. *)
          * assert (exists Ii', Ii' ≋ Ii /\ find_inst i S = Some Ii') as (? & <- &?)
                by (apply orel_find_inst_Some; auto).
            inversion_clear WTS as [????? WTinsts].
            eapply Forall_forall in WTinsts; eauto.
            inv WTinsts; try congruence.
            match goal with H: find_inst i S = _, H': find_inst i S = _ |- _ => rewrite H in H'; inv H' end.
            match goal with H: find_system _ _ = _, H': find_unit _ _ = _ |- _ => setoid_rewrite H in H'; inv H' end; auto.
          * assert (~ Is_update_inst_in i tcs /\ (exists ck, Is_reset_inst_in i ck tcs /\ sem_clock_instant base (var_env R) ck true)) as Reset'.
            { split.
              - inv NoDupStep.
                rewrite insts_of_In, <- fst_InMembers; auto.
              - eapply Exists_exists in Reset as (?&?&?); repeat esplit; eauto.
                take (In _ ckrs) and eapply InstReset in it; eauto. 2:left; constructor.
                inv it; auto. take (Is_reset_inst_in_tc _ _ _) and inv it.
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

    Lemma sem_trconstrs_lasts_of:
      forall tcs base R S I S' x v,
        Forall (sem_trconstr p base R S I S') tcs ->
        InMembers x (lasts_of tcs) ->
        sem_var_instant R (Last x) (present v) ->
        find_val x I = Some v.
    Proof.
      induction tcs as [|[|? []|?? []]]; inversion_clear 1 as [|?? Sem]; simpl;
        intros * Hin Hvar; try contradiction; eauto.
      destruct Hin; eauto; subst.
      inv Sem; cases; try congruence.
    Qed.

    Lemma sem_trconstrs_nexts_of:
      forall tcs base R S I S' x v,
        Forall (sem_trconstr p base R S I S') tcs ->
        InMembers x (nexts_of tcs) ->
        sem_var_instant R (Var x) (present v) ->
        find_val x I = Some v.
    Proof.
      induction tcs as [|[|? []|?? []]]; inversion_clear 1 as [|?? Sem]; simpl;
        intros * Hin Hvar; try contradiction; eauto.
      destruct Hin; eauto; subst.
      inv Sem; cases; try congruence.
    Qed.

    (* TODO this could be simplified ? *)
    Corollary trconstrs_app_wt mems:
      forall tcs' tcs defs,
        let alltcs := tcs ++ tcs' in
        Forall (sem_trconstr p base R S I S') alltcs ->
        Forall (wt_trconstr p Γ) alltcs ->
        NoDup (variables alltcs) ->
        NoDupMembers (lasts_of alltcs ++ nexts_of alltcs) ->
        NoDupMembers (Syn.insts_of alltcs) ->
        incl (insts_of alltcs) insts ->
        incl (lasts_of alltcs) (idfst Γ) ->
        incl (nexts_of alltcs) (idfst Γ) ->
        incl defs (idfst Γ) ->
        (forall x, InMembers x defs <-> In x (defined tcs')) ->
        (forall x t, In (x, (t, true)) Γ -> In (x, t) (lasts_of alltcs)) ->
        (forall x, In x mems -> InMembers x (nexts_of alltcs)) ->
        (forall x t islast, In x inputs -> In (x, (t, islast)) Γ -> wt_env_svalue R (Var x) t) ->
        last_consistency alltcs ->
        next_consistency alltcs ->
        inst_consistency alltcs ->
        last_reset_clocks_have_sem base (var_env R) alltcs ->
        next_reset_clocks_have_sem base (var_env R) alltcs ->
        inst_reset_clocks_have_sem base (var_env R) alltcs ->
        Is_well_sch inputs mems alltcs ->
        wt_synchronous_env R (types_nolast defs ++ types_last (lasts_of tcs') ++ types_nolast (nexts_of tcs'))
        /\ exists M',
            Memory_Corres R base tcs' S I S' M'
            /\ wt_memory M' p (idfst Γ) insts.
    Proof.
      induction tcs' as [|tc];
        intros * Semtcs WTtcs Ndpdefs NdpLast NdpInst Specinsts Speclasts Specnexts Specdefs
                   Eqdefs Eqlasts Specmems
                   WTinputs LastReset NextReset InstReset LResetCks NResetCks IResetCks WSCH.
      - subst; simpl.
        rewrite app_nil_r; split.
        + apply Forall_forall; intros (x&?&?) Hin.
          simpl_In. apply In_InMembers, Eqdefs in Hin0 as [].
        + eexists; split; eauto.
          now apply Memory_Corres_empty_equal_memory.
      - subst alltcs.
        pose proof WSCH as WSCH'; apply Forall'_app_r in WSCH'.
        pose proof LastReset as LastReset'; eapply last_consistency_app in LastReset'; eauto.
        pose proof NextReset as NextReset'; eapply next_consistency_app in NextReset'; eauto.
        pose proof InstReset as InstReset'; eapply inst_consistency_app in InstReset'; eauto.
        pose proof LResetCks as LResetCks'; eapply last_reset_clocks_have_sem_app in LResetCks'; eauto.
        pose proof NResetCks as NResetCks'; eapply next_reset_clocks_have_sem_app in NResetCks'; eauto.
        pose proof IResetCks as IResetCks'; eapply inst_reset_clocks_have_sem_app in IResetCks'; eauto.
        pose proof Semtcs as Semtcs'; apply Forall_app_weaken in Semtcs'; inversion_clear Semtcs' as [|?? Semtc].
        pose proof WTtcs as WTtcs'; apply Forall_app_weaken in WTtcs'; inversion_clear WTtcs' as [|?? WTtc].
        pose proof Speclasts as Speclasts'; rewrite lasts_of_app in Speclasts'. apply incl_app' in Speclasts' as [].
        pose proof Specnexts as Specnexts'; rewrite nexts_of_app in Specnexts'. apply incl_app' in Specnexts' as [].
        pose proof Specinsts as Specinsts'; rewrite insts_of_app in Specinsts'; apply incl_app' in Specinsts' as [].
        pose proof Ndpdefs as Ndpdefs'.
        unfold variables in Ndpdefs'.
        rewrite flat_map_app in Ndpdefs'.
        apply NoDup_app'_iff in Ndpdefs' as (?& Ndpdefs' &?); simpl in Ndpdefs'.
        rewrite Permutation.Permutation_app_comm in Ndpdefs'.
        apply NoDup_app'_iff in Ndpdefs' as (?&?& Ndpdefs').
        pose proof NdpLast as NdpLast'. (* rewrite lasts_of_app in NdpLast'. apply NoDupMembers_app_r in NdpLast'. *)
        pose proof NdpInst as NdpInst'. rewrite Syn.insts_of_app in NdpInst'. apply NoDupMembers_app_r in NdpInst'.
        rewrite List_shift_first in WSCH, Semtcs, WTtcs, Speclasts, Specnexts, Specmems, Ndpdefs, NdpLast, NdpInst, Specinsts,
                                    LastReset, NextReset, InstReset, LResetCks, NResetCks, IResetCks, Eqlasts.
        assert (exists defs', incl defs' (idfst Γ) /\ forall x, InMembers x defs' <-> In x (defined tcs')) as (defs' & Specdefs' & Eqdefs').
        { exists (idfst (filter (fun '(x, _) => mem_ident x (defined tcs')) Γ)).
          split; [now apply incl_map, incl_filter'|].
          split; intros * Hin.
          - simpl_In. apply mem_ident_spec in Hf; auto.
          - clear - WTtcs Hin. apply Forall_app in WTtcs as (_&WTtcs).
            assert (InMembers x Γ) as InG.
            { apply Is_defined_in_defined in Hin as Hin'. unfold Is_defined_in in Hin'.
              simpl_Exists. simpl_Forall. inv Hin'; inv WTtcs.
              1-2:solve_In.
              eapply Forall2_ignore2 in H7. simpl_Forall. solve_In. }
            solve_In; now apply mem_ident_spec.
        }
        edestruct IHtcs' as (WTR' & M' & Corres & WTM'); eauto.
        eapply trconstr_cons_wt; eauto.
        + clear - NdpLast'. rewrite lasts_of_app, nexts_of_app in *.
          solve_NoDupMembers_app.
        + intros * Hinvars Hin; apply Forall_app in WTR' as [WT].
          assert (In (x, t) defs').
          { apply Eqdefs', InMembers_In in Hinvars.
            destruct Hinvars as (t' & Hinvars).
            pose proof Hinvars.
            apply Specdefs' in Hinvars. simpl_In.
            eapply NoDupMembers_det in Hin0; eauto; inv Hin0; auto.
          }
          eapply Forall_forall in WT; [|solve_In]. destruct_conjs; auto.
        + intros; apply Forall_app in WTR' as [? WT].
          eapply Forall_forall in WT; [|apply in_app; left; solve_In]. destruct_conjs; auto.
        + intros; apply Forall_app in WTR' as [? WT].
          eapply Forall_forall in WT; [|apply in_app; right; solve_In]. destruct_conjs; auto.
        + inversion_clear WSCH' as [|?? (FreeSpec&_&NextSpec&_)].
          intros * Free Hin. assert (Free':=Free). apply FreeSpec in Free' as [Def|[Def|Def]]; eauto.
          * apply Is_defined_in_defined, Eqdefs', InMembers_In in Def as (?&Def).
            eapply Forall_forall in WTR'; [|clear - Def; apply in_app_iff; left; solve_In].
            apply Specdefs' in Def. simpl_In.
            eapply NoDupMembers_det in Hin; eauto. inv Hin; auto.
          * unfold wt_env_svalue.
            destruct (R (Var x0)) as [[|v]|] eqn: Find; simpl; auto.
            assert (sem_var_instant R (Var x0) (present v)) as Hvar by auto.
            eapply Specmems in Def as Def. eapply sem_trconstrs_nexts_of in Def as V; eauto.

             assert (Is_update_next_in x0 (tcs ++ [tc])) as Next.
             { rewrite fst_InMembers, <-nexts_of_In in Def.
               eapply Exists_app' in Def as [?|?]; eauto. exfalso.
               eapply NextSpec; eauto. }
             clear Def.

             apply nexts_of_In in Next as InNext. apply fst_InMembers in InNext.
             eapply Exists_exists in Next as (?&Hin'&Next). inv Next.
             assert (Forall (fun ckr : clock => exists r : bool, sem_clock_instant base (var_env R) ckr r) ckrs) as Ckr.
             { eapply NResetCks. eapply Exists_app'; left.
               eapply Exists_exists; eauto with stcsyntax. }
             eapply reset_or_not_reset_dec' in Ckr as [Reset|NotReset].
             ++ eapply Forall_app in Semtcs as (Semtcs&_).
                eapply Forall_forall in Semtcs; eauto. inv Semtcs.
                rewrite V in H22; inv H22.
                inversion_clear WTS as [???? WTmems].
                eapply Forall_forall in WTmems; eauto; simpl in *. 2:solve_In. simpl in *.
                now unfold find_val in H16; rewrite H16 in WTmems.
             ++ assert (~Is_update_last_in x0 tcs' /\ ~Is_update_next_in x0 tcs' /\
                          (exists ck, Is_reset_state_in x0 ck tcs' /\ sem_clock_instant base (var_env R) ck true)) as NotReset'.
                { split; [|split]; auto.
                  - rewrite lasts_of_In, <-fst_InMembers. intros contra.
                    eapply NoDupMembers_app_InMembers in NdpLast.
                    + apply NdpLast. rewrite nexts_of_app, InMembers_app; eauto.
                    + rewrite lasts_of_app, InMembers_app; auto.
                  - eapply Exists_exists in NotReset as (?&?&?); repeat esplit; eauto.
                    eapply NextReset in H12; eauto.
                    2:eapply Exists_app'; left; eapply Exists_exists; eauto with stcsyntax.
                    apply Exists_app' in H12 as [?|?]; auto.
                    exfalso.
                    eapply Is_well_sch_free_Reset in Free; eauto.
                }
                eapply Corres in NotReset'. rewrite NotReset' in V.
                inversion_clear WTM' as [???? WTmems].
                eapply Forall_forall in WTmems; [|solve_In]; simpl in *.
                now unfold find_val, wt_env_value in *; rewrite V in WTmems.
        + inversion_clear WSCH' as [|?? (_&FreelSpec&_)].
          intros * Free Hin. assert (Free':=Free). apply FreelSpec in Free.
          unfold wt_env_svalue.
          destruct (R (Last x)) as [[|v]|] eqn: Find; simpl; auto.
          assert (sem_var_instant R (Last x) (present v)) as Hvar by auto.
          eapply sem_trconstrs_lasts_of with (1 := Semtcs) in Hvar; eauto.
          2:eapply In_InMembers, Eqlasts; eauto.

          assert (Is_update_last_in x (tcs ++ [tc])) as Last.
          { apply Eqlasts, In_InMembers, fst_InMembers, lasts_of_In in Hin.
            eapply Exists_app' in Hin as [?|?]; eauto using Is_last_in_Is_defined_in.
            exfalso. eapply Free; eauto using Is_last_in_Is_defined_in. }
          eapply Exists_exists in Last as (?&Hin'&Last). inv Last.
          assert (Forall (fun ckr : clock => exists r : bool, sem_clock_instant base (var_env R) ckr r) ckrs) as Ckr.
          { eapply LResetCks. eapply Exists_app'; left.
            eapply Exists_exists; eauto with stcsyntax. }
          eapply reset_or_not_reset_dec' in Ckr as [Reset|NotReset].
          * eapply Forall_app in Semtcs as (Semtcs&_).
            eapply Forall_forall in Semtcs; eauto. inv Semtcs.
            rewrite H17 in Hvar; inv Hvar.
            inversion_clear WTS as [???? WTmems].
            eapply Forall_forall in WTmems; eauto.
            unfold wt_env_value in *. simpl in *.
            now take (_ -> find_val x S = _) and unfold find_val in it; rewrite it in WTmems.
          * assert (~Is_update_last_in x tcs' /\ ~Is_update_next_in x tcs' /\
                      (exists ck, Is_reset_state_in x ck tcs' /\ sem_clock_instant base (var_env R) ck true)) as NotReset'.
            { split; [|split]; auto.
              - rewrite nexts_of_In, <-fst_InMembers. intros contra.
                eapply NoDupMembers_app_InMembers in NdpLast.
                + apply NdpLast. rewrite nexts_of_app, InMembers_app; eauto.
                + rewrite lasts_of_app, InMembers_app. left.
                  rewrite fst_InMembers, <-lasts_of_In. unfold Is_update_last_in. solve_Exists. constructor.
              - eapply Exists_exists in NotReset as (?&?&?); repeat esplit; eauto.
                take (In _ ckrs) and eapply LastReset in it; eauto.
                2:eapply Exists_app'; left; eapply Exists_exists; eauto with stcsyntax.
                apply Exists_app' in it as [?|?]; auto.
                exfalso.
                eapply Is_well_sch_free_ResetLast in Free'; eauto.
            }
            eapply Corres in NotReset'. rewrite NotReset' in Hvar.
            inversion_clear WTM' as [???? WTmems].
            eapply Forall_forall in WTmems; [|solve_In].
            unfold wt_env_value, find_val in *; simpl in *. now rewrite Hvar in WTmems.
    Qed.

    Corollary trconstrs_wt mems:
      forall tcs defs,
        Forall (sem_trconstr p base R S I S') tcs ->
        Forall (wt_trconstr p Γ) tcs ->
        NoDup (variables tcs) ->
        NoDupMembers (lasts_of tcs ++ nexts_of tcs) ->
        NoDupMembers (Syn.insts_of tcs) ->
        incl (insts_of tcs) insts ->
        incl (lasts_of tcs) (idfst Γ) ->
        incl (nexts_of tcs) (idfst Γ) ->
        incl defs (idfst Γ) ->
        (forall x, InMembers x defs <-> In x (defined tcs)) ->
        (forall x t, In (x, (t, true)) Γ -> In (x, t) (lasts_of tcs)) ->
        (forall x, In x mems -> InMembers x (nexts_of tcs)) ->
        (forall x t islast, In x inputs -> In (x, (t, islast)) Γ -> wt_env_svalue R (Var x) t) ->
        Is_well_sch inputs mems tcs ->
        last_consistency tcs ->
        next_consistency tcs ->
        inst_consistency tcs ->
        last_reset_clocks_have_sem base (var_env R) tcs ->
        next_reset_clocks_have_sem base (var_env R) tcs ->
        inst_reset_clocks_have_sem base (var_env R) tcs ->
        wt_synchronous_env R (types_nolast defs ++ types_last (lasts_of tcs) ++ types_nolast (nexts_of tcs))
        /\ exists M',
            Memory_Corres R base tcs S I S' M'
            /\ wt_memory M' p (idfst Γ) insts.
    Proof.
      intros; eapply trconstrs_app_wt with (tcs := []); eauto.
    Qed.

  End Trconstr_wt.

  Lemma wt_program_Ordered_systems {prefs} :
    forall (p: @program prefs),
      wt_program p ->
      Ordered_systems p.
  Proof.
    intros; eapply wt_program_Ordered_program; eauto.
    intros * [WTtcs] Hin.
    rewrite s_subs_insts_of in Hin.
    induction WTtcs as [|[|? []|?? []]]; simpl in Hin; try contradiction; auto.
    destruct Hin; subst; auto.
    take (wt_trconstr _ _ _) and inv it.
    take (find_system _ _ = _) and setoid_rewrite it.
    discriminate.
  Qed.

  Fact s_insts_of_subs {prefs} :
    forall (s: @system prefs), incl (insts_of (s_tcs s)) (s_subs s).
  Proof.
    intros; rewrite s_subs_insts_of.
    intros ? Hin.
    rewrite incl_in_app; eauto using s_inst_reset_incl.
    induction (s_tcs s) as [|[|? []|?? []]]; simpl in *; try contradiction; auto;
      destruct Hin as [|Hin]; auto.
    - subst; apply in_app; right; left; auto.
    - apply IHl, in_app in Hin as [|]; apply in_app; auto.
      right; right; auto.
  Qed.

  Lemma sem_system_wt {prefs} :
    forall (p: @program prefs) f S xs ys S' s p',
      wt_program p ->
      Well_scheduled p ->
      sem_system p f S xs ys S' ->
      find_system f p = Some (s, p') ->
      wt_memory S p (mems_of_states (s_lasts s ++ s_nexts s)) s.(s_subs) ->
      Forall2 (fun xt v => wt_svalue v (fst (snd xt))) s.(s_in) xs ->
      wt_memory S' p' (mems_of_states (s_lasts s ++ s_nexts s)) s.(s_subs)
      /\ Forall2 (fun xt v => wt_svalue v (fst (snd xt))) s.(s_out) ys.
  Proof.
    intros []; induction systems0 as [|s']; intros * WTp Wsch Sem Find WTS WTins;
      try now inversion Find.
    pose proof WTp as WTp'; inversion_clear WTp as [|?? [WTs]]. inversion WTs as [WTtcs].
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
        <-incl_in_app, <-s_subs_insts_of in Notin; try contradiction.
        apply incl_map, s_inst_reset_incl.
      }
      take (wt_memory _ _ _ _) and eapply wt_memory_other in it; simpl in *; eauto.
      assert (NoDupMembers (idfst (s_in s' ++ s_vars s' ++ s_out s') ++ mems_of_states (s_lasts s' ++ s_nexts s'))) as Ndp.
      { pose proof (s_nodup s') as Ndp. clear - Ndp.
        rewrite ? idfst_app, <- ? app_assoc.
        apply fst_NoDupMembers.
        rewrite ? map_app, ? map_fst_idfst, mems_of_states_fst, map_app. auto.
      }
      inv WTp'.
      edestruct (@trconstrs_wt prefs) with
        (7 := Semtcs)
        (defs := idfst (s_vars s' ++ s_out s') ++ mems_of_states (s_lasts s'))
        as (WTR & M' & Corres & WTM');
        eauto using s_nodup_variables, s_last_consistency, s_next_consistency, s_inst_consistency,
        s_nodup_subs, s_insts_of_subs; auto.
      + erewrite fst_NoDupMembers, ? map_app, ? map_map, <-? app_assoc,
          map_ext with (l:=s_in _), map_ext with (l:=s_vars _), map_ext with (l:=s_out _),
                map_ext with (l:=s_lasts _), map_ext with (l:=s_nexts _).
        apply s_nodup.
        all:intros; destruct_conjs; auto.
      + take (state_closed _ _ S) and clear - Find' Ndp it it0.
        inv it. rewrite Find' in H; inv H.
        inv it0. split; auto.
        unfold wt_env, mems_of_states in *.
        rewrite idfst_app, Forall_app. split.
        * simpl_Forall. simpl_In.
          enough (find_val i S = None) as Find. unfold find_val in *; now rewrite Find.
          apply None_eq_dne. intro contra. apply H0 in contra.
          eapply NoDupMembers_app_InMembers; eauto. 1,2:solve_In.
        * simpl_Forall. simpl_In. rewrite Forall_app in *. destruct H.
          apply in_app_iff in Hin as [Hin|Hin]; simpl_In; simpl_Forall; auto.
      + rewrite fst_NoDupMembers, map_app, <-s_lasts_in_tcs, <-s_nexts_in_tcs, <-map_app, <-fst_NoDupMembers.
        apply s_nodup_lasts_nexts.
      + rewrite <-s_subs_insts_of. apply s_nodup_subs.
      + rewrite ? idfst_app; apply incl_appr, incl_appl.
        unfold idfst. erewrite map_map, map_ext. eapply s_lasts_of_mems_of_states; eauto.
        intros; destruct_conjs; auto.
      + rewrite ? idfst_app; apply incl_appr, incl_appr.
        unfold idfst. erewrite map_map, map_ext. eapply s_nexts_of_mems_of_states; eauto.
        intros; destruct_conjs; auto.
      + clear - s'. unfold mems_of_states. simpl_app. rewrite ? map_map.
        apply incl_appr. rewrite ? app_assoc with (n:=map _ (s_nexts _)). apply incl_appl.
        erewrite
          map_ext with (l:=s_vars _), map_ext with (l:=s_out _), map_ext with (l:=s_lasts _). reflexivity.
        all:intros; destruct_conjs; auto.
      + intros ?. rewrite fst_InMembers, map_app, map_fst_idfst, mems_of_states_fst, s_lasts_in_tcs,
          s_defined, <-s_vars_out_in_tcs, map_app.
        reflexivity.
      + intros * In. rewrite ? in_app_iff in In. destruct In as [|[|]]; simpl_In.
        eapply s_l
      + intros. eapply s_lasts_of_mems_of_states_iff; eauto.
        unfold mems_of_states. solve_In.
      + intros. now rewrite fst_InMembers, <-s_nexts_in_tcs.
      + intros * Hin Hin'.
        assert (exists ck, In (x0, (t, ck)) (s_in s')) as (?&?).
        { apply fst_InMembers, InMembers_idfst in Hin.
          clear - Hin Hin' Ndp. simpl_app. simpl_In.
          eapply NoDupMembers_app_InMembers in Ndp; eauto. 2:solve_In.
          apply in_app in Hin' as [Hin'|Hin']; simpl_In; eauto.
          exfalso. eapply Ndp. unfold mems_of_states. rewrite ? map_app, ? in_app_iff in *.
           destruct Hin' as [|[|[|]]]; [left|right;left|right;right;left|do 3 right]; solve_In.
        }
        take (sem_vars_instant _ _ xs) and rename it into Semins.
        setoid_rewrite Forall2_map_1 in Semins.
        eapply Forall2_Forall2 in WTins; eauto.
        eapply Forall2_in_left in WTins as (?&?& Hvar & WT); eauto; simpl in *.
        unfold wt_env_svalue. now unfold var_env, sem_var_instant in Hvar; rewrite Hvar.
      + eapply sem_trconstrs_last_reset_clocks; eauto using s_last_consistency.
      + eapply sem_trconstrs_next_reset_clocks; eauto using s_next_consistency.
      + eapply sem_trconstrs_inst_reset_clocks; eauto using s_inst_consistency.
      + split.
        * take (state_closed _ _ S) and inv it.
          take (state_closed _ _ S') and inv it.
          repeat match goal with H: find_system _ _ = _, H': find_system _ _ = _ |- _ => rewrite H in H'; inv H' end.
          eapply Memory_Corres_equal_memory in Corres as <-; eauto; intros; eauto.
          -- clear - WTM'. inv WTM'; split; auto.
             unfold wt_env, mems_of_states, idfst in *. rewrite ? map_app, ? Forall_app in *. destruct H as (?&?&?).
             split; simpl_Forall; auto.
          -- now rewrite map_app, in_app_iff, lasts_of_In, s_lasts_in_tcs, nexts_of_In, s_nexts_in_tcs.
          -- rewrite map_app, s_lasts_in_tcs, s_nexts_in_tcs, <-map_app.
             apply s_state_reset_incl, reset_states_of_In; eauto.
          -- now rewrite fst_InMembers, s_subs_insts_of, insts_of_In.
          -- eapply insts_of_In, incl_map. eapply s_inst_reset_incl.
             eapply reset_insts_of_In; eauto.
        * unfold types_nolast in *. rewrite ? idfst_app, 2 map_app, <- ? app_assoc in WTR.
          repeat setoid_rewrite Forall_app in WTR.
          destruct WTR as (_& WTouts &_).
          take (sem_vars_instant _ _ ys) and rename it into Semouts.
          clear - Semouts WTouts.
          unfold sem_vars_instant, idfst in *. simpl_Forall.
          unfold sem_var_instant, var_env, wt_env_svalue in *. now rewrite H1 in H2.
    - assert (Forall (fun oc => snd oc <> s_name s') (s_subs s)).
      { eapply find_unit_other_not_Is_called_in in WTp'; simpl; eauto; simpl; eauto.
        apply Forall_forall; intros * Hin; apply in_map with (f := snd) in Hin.
        intro E'; rewrite E' in Hin; contradiction.
      }
      take (wt_memory _ _ _ _) and eapply wt_memory_other in it; simpl; eauto.
      eapply IHsystems0; eauto.
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
   (CEIsF    : CEISFREE          Ids Op OpAux        Cks CESyn)
   (Free     : STCISFREE         Ids Op OpAux        Cks CESyn Syn CEIsF)
   (Ord      : STCORDERED        Ids Op OpAux        Cks CESyn Syn)
   (CESem    : CESEMANTICS       Ids Op OpAux        Cks CESyn              Str)
   (CETypSem : CETYPINGSEMANTICS Ids Op OpAux ComTyp Cks CESyn        CEIsF Str CESem CETyp)
   (Sem      : STCSEMANTICS      Ids Op OpAux        Cks CESyn Syn Ord Str CESem)
   (Wdef     : STCWELLDEFINED    Ids Op OpAux        Cks CESyn Syn Ord CEIsF Free)
   (Corres   : STCMEMORYCORRES   Ids Op OpAux        Cks Str CESyn Syn Ord CESem Sem)
<: STCTYPINGSEMANTICS Ids Op OpAux ComTyp Cks CESyn Syn CETyp StcTyp Str CEIsF Free Ord CESem CETypSem Sem Wdef Corres.
  Include STCTYPINGSEMANTICS Ids Op OpAux ComTyp Cks CESyn Syn CETyp StcTyp Str CEIsF Free Ord CESem CETypSem Sem Wdef Corres.
End StcTypingSemanticsFun.
