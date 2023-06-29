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
From Velus Require Import Operators.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import Clocks.

From Velus Require Import VelusMemory.

From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import Stc.StcSemantics.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCMEMORYCORRES
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX  Ids Op)
       (Import Cks   : CLOCKS         Ids Op OpAux)
       (Import Str   : INDEXEDSTREAMS Ids Op OpAux Cks)
       (Import CESyn : CESYNTAX       Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX      Ids Op OpAux Cks CESyn)
       (Import Ord   : STCORDERED     Ids Op OpAux Cks CESyn Syn)
       (Import CESem : CESEMANTICS    Ids Op OpAux Cks CESyn Str)
       (Import Sem   : STCSEMANTICS   Ids Op OpAux Cks CESyn Syn Ord Str CESem).

  Definition state := memory value.
  Definition menv := memory value.

  Definition value_corres (x: ident) (S: state) (me: menv) : Prop :=
    find_val x S = find_val x me.

  Definition state_corres (s: ident) (S: state) (me: menv) : Prop :=
    find_inst s S ⌈≋⌉ find_inst s me.

  Definition Memory_Corres
             (R: env)
             (b: bool)
             (tcs: list trconstr)
             (S I S': state)
             (me: menv) : Prop :=
    (forall x,
        (~Is_update_last_in x tcs /\ ~Is_update_next_in x tcs /\
         (forall ck, Is_reset_state_in x ck tcs -> sem_clock_instant b (var_env R) ck false) ->
         value_corres x S me)
        /\
        (~Is_update_last_in x tcs /\ ~Is_update_next_in x tcs /\
         (exists ck, Is_reset_state_in x ck tcs /\ sem_clock_instant b (var_env R) ck true) ->
         value_corres x I me)
        /\
        (Is_update_last_in x tcs \/ Is_update_next_in x tcs -> value_corres x S' me))
    /\ (forall s,
        (~ Is_update_inst_in s tcs /\
         (forall ck, Is_reset_inst_in s ck tcs -> sem_clock_instant b (var_env R) ck false) ->
         state_corres s S me)
        /\
        (~ Is_update_inst_in s tcs /\
         (exists ck, Is_reset_inst_in s ck tcs /\ sem_clock_instant b (var_env R) ck true) ->
         state_corres s I me)
        /\
        (Is_update_inst_in s tcs -> state_corres s S' me)).

  Lemma value_corres_equal_memory:
    forall x S M,
      S ≋ M ->
      value_corres x S M.
  Proof.
    intros * E; unfold value_corres; now rewrite E.
  Qed.

  Lemma state_corres_equal_memory:
    forall s S M,
      S ≋ M ->
      state_corres s S M.
  Proof.
    intros * E; unfold state_corres; now rewrite E.
  Qed.

  Lemma Memory_Corres_empty_equal_memory:
    forall R b S I S' me,
      S ≋ me ->
      Memory_Corres R b [] S I S' me.
  Proof.
    split.
    - repeat split.
      + intros _. now apply value_corres_equal_memory; auto.
      + intros (_&_&(?&Reset&_)). inv Reset.
      + intros [Up|Up]; inv Up.
    - repeat split.
      + intros _. now apply state_corres_equal_memory.
      + intros (_&(?&Res&_)). inv Res.
      + intros Step. inv Step.
  Qed.

  Lemma state_reset_or_not_reset_dec {prefs} :
    forall (P: @program prefs) b R S I S' x tcs,
      Forall (sem_trconstr P b R S I S') tcs ->
      (forall ck, Is_reset_state_in x ck tcs -> sem_clock_instant b (var_env R) ck false) \/
      (exists ck, Is_reset_state_in x ck tcs /\ sem_clock_instant b (var_env R) ck true).
  Proof.
    induction tcs; intros * Sems; inv Sems.
    - left. intros ? Hin. inv Hin.
    - specialize (IHtcs H2) as [NotReset|(ck&Reset&Clock)].
      + inv H1.
        all:setoid_rewrite Is_reset_state_in_reflect; simpl.
        2:destruct (ident_eqb x x0); simpl.
        2:setoid_rewrite Bool.orb_true_iff; setoid_rewrite clock_eq_spec.
        all:setoid_rewrite <-Is_reset_state_in_reflect; auto.
        destruct r; eauto.
        left. intros ck' [?|?]; subst; eauto.
      + right. exists ck; split; auto. right; auto.
  Qed.

  Lemma inst_reset_or_not_reset_dec {prefs} :
    forall (P: @program prefs) b R S I S' i tcs,
      Forall (sem_trconstr P b R S I S') tcs ->
      (forall ck, Is_reset_inst_in i ck tcs -> sem_clock_instant b (var_env R) ck false) \/
      (exists ck, Is_reset_inst_in i ck tcs /\ sem_clock_instant b (var_env R) ck true).
  Proof.
    induction tcs; intros * Sems; inv Sems.
    - left. intros ? Hin. inv Hin.
    - specialize (IHtcs H2) as [NotReset|(ck&Reset&Clock)].
      + inv H1.
        all:setoid_rewrite Is_reset_inst_in_reflect; simpl.
        3:destruct (ident_eqb i i0); simpl.
        3:setoid_rewrite Bool.orb_true_iff; setoid_rewrite clock_eq_spec.
        all:try setoid_rewrite <-Is_reset_inst_in_reflect; auto.
        destruct r; eauto.
        left. intros ck' [?|?]; subst; eauto.
      + right. exists ck; split; auto. right; auto.
  Qed.

  Lemma Memory_Corres_equal_memory {prefs} :
    forall (P: @program prefs) tcs R b S I S' me resets subs,
      Forall (sem_trconstr P b R S I S') tcs ->
      Memory_Corres R b tcs S I S' me ->
      state_closed_states resets S ->
      state_closed_insts P subs S ->
      state_closed_states resets S' ->
      state_closed_insts P subs S' ->
      (forall x, In x resets <-> Is_update_last_in x tcs \/ Is_update_next_in x tcs) ->
      (forall x ck, Is_reset_state_in x ck tcs -> In x resets) ->
      (forall i, InMembers i subs <-> Is_update_inst_in i tcs) ->
      (forall i ck, Is_reset_inst_in i ck tcs -> Is_update_inst_in i tcs) ->
      me ≋ S'.
  Proof.
    intros * Sems (States & Insts) ResetClosed InstsClosed ResetClosed' InstsClosed'
           SpecReset ResetState SpecStep ResetStep.
    split.
    - intro x.
      destruct (Is_update_last_in_dec x tcs) as [Last|NLast]. 1:eapply or_introl, States in Last; auto.
      destruct (Is_update_next_in_dec x tcs) as [Next|NNext]. 1:eapply or_intror, States in Next; auto.
      assert (~In x resets) as Nin.
      { intros contra. apply SpecReset in contra as [|]; eauto. }
      assert (find_val x S = None).
      { apply not_Some_is_None; intros * Find.
        apply Nin, ResetClosed, not_None_is_Some; eauto.
      }
      assert (find_val x S' = None) as E'.
      { apply not_Some_is_None; intros * Find.
        apply Nin, ResetClosed', not_None_is_Some; eauto.
      }
      unfold value_corres, find_val in *.
      assert (~exists ck, Is_reset_state_in x ck tcs) as NReset.
      { intros (?&contra). apply ResetState in contra. apply SpecReset in contra as [|]; auto. }
      rewrite E', <-H. symmetry.
      apply States; split; [|split]; auto.
      intros ? Reset. contradict NReset; eauto.
    - split.
      + setoid_rewrite Env.In_find; intro i.
        destruct (Is_update_inst_in_dec i tcs) as [Step|Nstep].
        * apply Insts in Step.
          unfold state_corres, find_inst in Step.
          split; intros (?& Find); rewrite Find in Step.
          -- apply orel_find_inst_Some in Step as (?&?&?); eauto.
          -- symmetry in Step; apply orel_find_inst_Some in Step as (?&?&?); eauto.
        * eapply inst_reset_or_not_reset_dec with (i:=i) in Sems as [NotReset|(?&Rst&Clock)].
          -- assert (state_corres i S me) as Corres
                by (apply Insts; auto).
             assert (find_inst i S = None).
             { apply not_Some_is_None; intros * Find.
               apply Nstep, SpecStep.
               eapply state_closed_insts_InMembers in InstsClosed; eauto.
             }
             assert (find_inst i S' = None) as E'.
             { apply not_Some_is_None; intros * Find.
               apply Nstep, SpecStep.
               eapply state_closed_insts_InMembers in InstsClosed'; eauto.
             }
             assert (find_inst i me = None) as E.
             { apply not_Some_is_None; intros * Find.
               unfold state_corres in Corres; rewrite Find in Corres.
               apply orel_find_inst_Some in Corres as (?&?&?).
               congruence.
             }
             setoid_rewrite E'; setoid_rewrite E; reflexivity.
          -- apply ResetStep in Rst; contradiction.
      + setoid_rewrite Env.Props.P.F.find_mapsto_iff.
        intros i me_i Si' Find Find'.
        destruct (Is_update_inst_in_dec i tcs) as [Step|Nstep].
        * apply Insts in Step.
          unfold state_corres, find_inst in Step.
          rewrite Find, Find' in Step.
          inv Step; symmetry; auto.
        * eapply inst_reset_or_not_reset_dec with (i:=i) in Sems as [NotReset|(?&Rst&Clock)].
          -- exfalso.
             apply Nstep, SpecStep.
             eapply state_closed_insts_InMembers in InstsClosed'; eauto.
          -- apply ResetStep in Rst; contradiction.
  Qed.

  Section Preservation.

    Variable (R: env) (b : bool).
    Variables (tcs: list trconstr) (S I S': state) (me: menv).
    Hypothesis MemCorres:  Memory_Corres R b tcs S I S' me.

    Lemma Memory_Corres_Def:
      forall x ck ce,
        Memory_Corres R b (TcDef x ck ce :: tcs) S I S' me.
    Proof.
      destruct MemCorres as (Lasts & Insts); intros; split; (split; [|split]).
      - intros (NLast&NNext&NReset).
        apply not_Is_update_last_in_cons in NLast as (?&?).
        apply not_Is_update_next_in_cons in NNext as (?&?).
        apply Lasts; split; [|split]; auto.
        intros ? Reset; apply NReset; right; auto.
      - intros (NLast&NNext&(?&NReset&ClockR)).
        apply not_Is_update_last_in_cons in NLast as (?&?).
        apply not_Is_update_next_in_cons in NNext as (?&?).
        inv NReset. inv H4.
        apply Lasts; eauto.
      - intros [NLast|NLast]; inversion_clear NLast as [?? Last|].
        1,3:inv Last.
        1,2:apply Lasts; auto.
      - intros (Nstep & Nrst).
        apply Insts; split.
        + intro; apply Nstep; right; auto.
        + intros * Rst; apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&ClockR)).
        apply Insts; split.
        + intro; apply Nstep; right; auto.
        + inversion_clear Rst as [?? IsSt|]; eauto.
          inv IsSt.
      - intros Step.
        apply Insts; inversion_clear Step as [?? IsSt|]; auto.
        inv IsSt.
    Qed.

    Lemma Memory_Corres_Reset_present :
      forall x ck ty c0 v v0,
        sem_clock_instant b (var_env R) ck true ->
        find_val x S = Some v ->
        find_val x I = Some v0 ->
        ~Is_update_last_in x tcs -> (* Scheduling *)
        ~Is_update_next_in x tcs -> (* itou *)
        Memory_Corres R b (TcReset ck (ResState x ty c0) :: tcs) S I S' (add_val x v0 me).
    Proof.
      destruct MemCorres as (Lasts & Insts); intros * Clock Hfind1 Hfind2 Hnlast Hnnext;
        split; (split; [|split]).
      - intros (NLast&NNext&NReset).
        apply not_Is_update_last_in_cons in NLast as (Last&NLast).
        apply not_Is_update_next_in_cons in NNext as (Next&NNext).
        assert (x0 <> x).
        { intro; subst.
          eapply sem_clock_instant_det in Clock; [|eapply NReset]; try congruence.
          left; constructor. }
        unfold value_corres.
        rewrite find_val_gso; auto.
        apply Lasts; split; [|split]; auto.
        intros ? Reset. apply NReset; right; auto.
      - intros (NLast&NNext&(ckr&NReset&ClockR)).
        apply not_Is_update_last_in_cons in NLast as (Last&NLast).
        apply not_Is_update_next_in_cons in NNext as (Next&NNext).
        inversion_clear NReset as [?? Reset|].
        + inv Reset.
          unfold value_corres.
          rewrite find_val_gss; auto.
        + unfold value_corres.
          destruct (ident_eq_dec x x0); subst.
          * rewrite find_val_gss; auto.
          * rewrite find_val_gso; auto.
            apply Lasts; split; eauto.
      - intros [NLast|NLast]; inversion_clear NLast as [?? Last|].
        1,3:inv Last.
        1,2:destruct (ident_eq_dec x x0); subst; [contradiction|].
        1,2:(unfold value_corres; rewrite find_val_gso; auto; apply Lasts; auto).
      - intros (Nstep & Nrst).
        assert (~ Is_update_inst_in s tcs) by (intro; apply Nstep; right; auto).
        unfold state_corres; setoid_rewrite find_inst_add_val;
          apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&ClockR)).
        assert (~ Is_update_inst_in s tcs) by (intro; apply Nstep; right; auto).
        inv Rst. inv H1.
        apply Insts; split; eauto.
      - intros Step.
        assert (Is_update_inst_in s tcs)
          by (inversion_clear Step as [?? IsSt|]; auto; inv IsSt).
        unfold state_corres; setoid_rewrite find_inst_add_val;
          apply Insts; auto.
    Qed.

    Lemma Memory_Corres_Reset_absent:
      forall x ck ty c0,
        sem_clock_instant b (var_env R) ck false ->
        Memory_Corres R b (TcReset ck (ResState x ty c0) :: tcs) S I S' me.
    Proof.
      destruct MemCorres as (Lasts & Insts); intros * Clock;
        split; (split; [|split]).
      - intros (NLast&NNext&NReset).
        apply not_Is_update_last_in_cons in NLast as (Last&NLast).
        apply not_Is_update_next_in_cons in NNext as (Next&NNext).
        apply Lasts; split; [|split]; auto.
        intros ? Reset. apply NReset. right; auto.
      - intros (NLast&NNext&(ckr&NReset&ClockR)).
        apply not_Is_update_last_in_cons in NLast as (Last&NLast).
        apply not_Is_update_next_in_cons in NNext as (Next&NNext).
        inversion_clear NReset as [?? Reset|].
        + inv Reset.
          exfalso. eapply sem_clock_instant_det in Clock; eauto.
          congruence.
        + apply Lasts; split; [|split]; eauto.
      - intros [NLast|NLast]; inversion_clear NLast as [?? Last|].
        1,3:inv Last.
        1,2:apply Lasts; auto.
      - intros (Nstep & Nrst).
        assert (~ Is_update_inst_in s tcs) by (intro; apply Nstep; right; auto).
        apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&ClockR)).
        assert (~ Is_update_inst_in s tcs) by (intro; apply Nstep; right; auto).
        inv Rst. inv H1.
        apply Insts; split; eauto.
      - intros Step.
        assert (Is_update_inst_in s tcs)
          by (inversion_clear Step as [?? IsSt|]; auto; inv IsSt).
        apply Insts; auto.
    Qed.

    Lemma reset_or_not_reset_dec' : forall b R ckrs,
        Forall (fun ckr => exists r, sem_clock_instant b R ckr r) ckrs ->
        Forall (fun ckr => sem_clock_instant b R ckr false) ckrs \/
        Exists (fun ckr => sem_clock_instant b R ckr true) ckrs.
    Proof.
      intros * Hf.
      induction Hf as [|??([|]&?)]; auto.
      destruct IHHf; auto.
    Qed.

    Lemma Memory_Corres_Last_present:
      forall x ck ckrs e c,
        find_val x S' = Some c ->
        Memory_Corres R b (TcUpdate ck ckrs (UpdLast x e) :: tcs) S I S' (add_val x c me).
    Proof.
      destruct MemCorres as (States & Insts); intros; split; (split; [|split]).
      - intros (NLast&NNext&NReset).
        apply not_Is_update_last_in_cons in NLast as (Last&NLast).
        apply not_Is_update_next_in_cons in NNext as (Next&NNext).
        assert (x0 <> x)
          by (intro; subst; apply Last; constructor).
        unfold value_corres.
        rewrite find_val_gso; auto.
        apply States; split; [|split]; eauto.
        intros * Reset. apply NReset; right; auto.
      - intros (NLast&NNext&(?&NReset&ClockR)).
        apply not_Is_update_last_in_cons in NLast as (Last&NLast).
        apply not_Is_update_next_in_cons in NNext as (Next&NNext).
        inversion_clear NReset as [?? Reset|].
        + inv Reset.
        + assert (x0 <> x)
            by (intro; subst; apply Last; constructor).
          unfold value_corres.
          rewrite find_val_gso; auto.
          apply States; eauto.
      - intros [NLast|NLast]; inversion_clear NLast as [?? Last|].
        all:unfold value_corres.
        1,3:inv Last; rewrite H, find_val_gss; auto.
        1,2:(destruct (ident_eq_dec x x0); subst;
             [rewrite find_val_gss|rewrite find_val_gso]; auto; apply States; auto).
      - intros (Nstep & Nrst).
        assert (~ Is_update_inst_in s tcs) by (intro; apply Nstep; right; auto).
        unfold state_corres; setoid_rewrite find_inst_add_val;
          apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&ClockR)).
        assert (~ Is_update_inst_in s tcs) by (intro; apply Nstep; right; auto).
        inv Rst. inv H2.
        apply Insts; split; eauto.
      - intros Step.
        assert (Is_update_inst_in s tcs)
          by (inversion_clear Step as [?? IsSt|]; auto; inv IsSt).
        unfold state_corres; setoid_rewrite find_inst_add_val;
          apply Insts; auto.
    Qed.

    Lemma Memory_Corres_Last_absent:
      forall x ck ckrs e c,
        last_consistency (TcUpdate ck ckrs (UpdLast x e) :: tcs) ->
        Forall (fun ckr => exists r, sem_clock_instant b (var_env R) ckr r) ckrs ->
        (Forall (fun ckr : clock => sem_clock_instant b (var_env R) ckr false) ckrs -> find_val x S = Some c) ->
        find_val x I = Some c ->
        find_val x S' = Some c ->
        Memory_Corres R b (TcUpdate ck ckrs (UpdLast x e) :: tcs) S I S' me.
    Proof.
      destruct MemCorres as (States & Insts); intros * SpecReset ClockR Eq1 Eq2 Eq3; split; (split; [|split]).
      - intros (NLast&NNext&NReset).
        apply not_Is_update_last_in_cons in NLast as (Last&NLast).
        apply not_Is_update_next_in_cons in NNext as (Next&NNext).
        apply States; split; [|split]; auto.
        intros. apply NReset. right; auto.
      - intros (NLast&NNext&(?&Reset&Clock)).
        apply not_Is_update_last_in_cons in NLast as (Last&NLast).
        apply not_Is_update_next_in_cons in NNext as (Next&NNext).
        inversion_clear Reset as [?? NReset|].
        + inv NReset.
        + apply States; eauto.
      - intros [NLast|NNext].
        + destruct (Is_update_last_in_dec x0 tcs); [eapply States; eauto|].
          destruct (Is_update_next_in_dec x0 tcs); [eapply States; eauto|].
          inversion_clear NLast as [?? Last|?? Last]; [|contradiction].
          inv Last.
          assert (Last_with_reset_in x ckrs (TcUpdate ck ckrs (UpdLast x e) :: tcs)) as SpecLast by (left; constructor).
          apply SpecReset in SpecLast.
          setoid_rewrite Is_reset_state_in_reflect in SpecLast. simpl in SpecLast. setoid_rewrite <-Is_reset_state_in_reflect in SpecLast.
          apply reset_or_not_reset_dec' in ClockR as [Reset|NotReset].
          * specialize (Eq1 Reset).
            unfold value_corres. rewrite Eq3, <-Eq1.
            apply States; split; [|split]; auto.
            intros ? IReset. eapply SpecLast, Forall_forall in IReset; eauto.
            assumption.
          * unfold value_corres. rewrite Eq3, <-Eq2.
            apply States; split; [|split]; auto.
            apply Exists_exists in NotReset as (ckr&Hsem&Hin).
            exists ckr. rewrite <-SpecLast. auto.
        + inversion_clear NNext as [?? []|?? Next].
          eapply States; eauto.
      - intros (Nstep & Nrst).
        assert (~ Is_update_inst_in s tcs) by (intro; apply Nstep; right; auto).
        apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&Clock)).
        assert (~ Is_update_inst_in s tcs) by (intro; apply Nstep; right; auto).
        inv Rst. inv H1.
        apply Insts; split; eauto.
      - intros Step.
        assert (Is_update_inst_in s tcs)
          by (inversion_clear Step as [?? IsSt|]; auto; inv IsSt).
        apply Insts; auto.
    Qed.

    Lemma Memory_Corres_Next_present:
      forall x ck ckrs e c,
        find_val x S' = Some c ->
        Memory_Corres R b (TcUpdate ck ckrs (UpdNext x e) :: tcs) S I S' (add_val x c me).
    Proof.
      destruct MemCorres as (States & Insts); intros; split; (split; [|split]).
      - intros (NLast&NNext&NReset).
        apply not_Is_update_last_in_cons in NLast as (Last&NLast).
        apply not_Is_update_next_in_cons in NNext as (Next&NNext).
        assert (x0 <> x)
          by (intro; subst; apply Next; constructor).
        unfold value_corres.
        rewrite find_val_gso; auto.
        apply States; split; [|split]; eauto.
        intros * Reset. apply NReset; right; auto.
      - intros (NLast&NNext&(?&NReset&ClockR)).
        apply not_Is_update_last_in_cons in NLast as (Last&NLast).
        apply not_Is_update_next_in_cons in NNext as (Next&NNext).
        inversion_clear NReset as [?? Reset|].
        + inv Reset.
        + assert (x0 <> x)
            by (intro; subst; apply Next; constructor).
          unfold value_corres.
          rewrite find_val_gso; auto.
          apply States; eauto.
      - intros [NLast|NLast]; inversion_clear NLast as [?? Last|].
        all:unfold value_corres.
        1,3:inv Last; rewrite H, find_val_gss; auto.
        1,2:(destruct (ident_eq_dec x x0); subst;
             [rewrite find_val_gss|rewrite find_val_gso]; auto; apply States; auto).
      - intros (Nstep & Nrst).
        assert (~ Is_update_inst_in s tcs) by (intro; apply Nstep; right; auto).
        unfold state_corres; setoid_rewrite find_inst_add_val;
          apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&ClockR)).
        assert (~ Is_update_inst_in s tcs) by (intro; apply Nstep; right; auto).
        inv Rst. inv H2.
        apply Insts; split; eauto.
      - intros Step.
        assert (Is_update_inst_in s tcs)
          by (inversion_clear Step as [?? IsSt|]; auto; inv IsSt).
        unfold state_corres; setoid_rewrite find_inst_add_val;
          apply Insts; auto.
    Qed.

    Lemma Memory_Corres_Next_absent:
      forall x ck ckrs e c,
        next_consistency (TcUpdate ck ckrs (UpdNext x e) :: tcs) ->
        Forall (fun ckr => exists r, sem_clock_instant b (var_env R) ckr r) ckrs ->
        (Forall (fun ckr : clock => sem_clock_instant b (var_env R) ckr false) ckrs -> find_val x S = Some c) ->
        find_val x I = Some c ->
        find_val x S' = Some c ->
        Memory_Corres R b (TcUpdate ck ckrs (UpdNext x e) :: tcs) S I S' me.
    Proof.
      destruct MemCorres as (States & Insts); intros * SpecReset ClockR Eq1 Eq2 Eq3; split; (split; [|split]).
      - intros (NLast&NNext&NReset).
        apply not_Is_update_last_in_cons in NLast as (Last&NLast).
        apply not_Is_update_next_in_cons in NNext as (Next&NNext).
        apply States; split; [|split]; auto.
        intros. apply NReset. right; auto.
      - intros (NLast&NNext&(?&Reset&Clock)).
        apply not_Is_update_last_in_cons in NLast as (Last&NLast).
        apply not_Is_update_next_in_cons in NNext as (Next&NNext).
        inversion_clear Reset as [?? NReset|].
        + inv NReset.
        + apply States; eauto.
      - intros [NLast|NNext].
        + inversion_clear NLast as [?? []|?? Next].
          eapply States; eauto.
        + destruct (Is_update_last_in_dec x0 tcs); [eapply States; eauto|].
          destruct (Is_update_next_in_dec x0 tcs); [eapply States; eauto|].
          inversion_clear NNext as [?? Last|?? Last]; [|contradiction].
          inv Last.
          assert (Next_with_reset_in x ckrs (TcUpdate ck ckrs (UpdNext x e) :: tcs)) as SpecLast by (left; constructor).
          apply SpecReset in SpecLast.
          setoid_rewrite Is_reset_state_in_reflect in SpecLast. simpl in SpecLast. setoid_rewrite <-Is_reset_state_in_reflect in SpecLast.
          apply reset_or_not_reset_dec' in ClockR as [Reset|NotReset].
          * specialize (Eq1 Reset).
            unfold value_corres. rewrite Eq3, <-Eq1.
            apply States; split; [|split]; auto.
            intros ? IReset. eapply SpecLast, Forall_forall in IReset; eauto.
            assumption.
          * unfold value_corres. rewrite Eq3, <-Eq2.
            apply States; split; [|split]; auto.
            apply Exists_exists in NotReset as (ckr&Hsem&Hin).
            exists ckr. rewrite <-SpecLast. auto.
      - intros (Nstep & Nrst).
        assert (~ Is_update_inst_in s tcs) by (intro; apply Nstep; right; auto).
        apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&Clock)).
        assert (~ Is_update_inst_in s tcs) by (intro; apply Nstep; right; auto).
        inv Rst. inv H1.
        apply Insts; split; eauto.
      - intros Step.
        assert (Is_update_inst_in s tcs)
          by (inversion_clear Step as [?? IsSt|]; auto; inv IsSt).
        apply Insts; auto.
    Qed.

    Lemma Memory_Corres_InstReset_present:
      forall s ck f Is me',
        sem_clock_instant b (var_env R) ck true ->
        find_inst s I = Some Is ->
        me' ≋ Is ->
        ~ Is_update_inst_in s tcs -> (* Scheduling *)
        Memory_Corres R b (TcReset ck (ResInst s f) :: tcs) S I S' (add_inst s me' me).
    Proof.
      destruct MemCorres as (Resets & Insts); intros ????? ClockR Find1 E NStep; split; (split; [|split]).
      - intros (NLast&NNext&NReset).
        apply not_Is_update_last_in_cons in NLast as (Last&NLast).
        apply not_Is_update_next_in_cons in NNext as (Next&NNext).
        apply Resets; split; [|split]; auto.
        intros. apply NReset. right; auto.
      - intros (NLast&NNext&(?&Reset&Clock)).
        apply not_Is_update_last_in_cons in NLast as (Last&NLast).
        apply not_Is_update_next_in_cons in NNext as (Next&NNext).
        inversion_clear Reset as [?? NReset|].
        + inv NReset.
        + apply Resets; eauto.
      - intros [NLast|NLast]; inversion_clear NLast as [?? Last|].
        1,3:inv Last.
        1,2:apply Resets; auto.
      - intros (Nstep & Nrst).
        assert (s0 <> s).
        { intro; subst.
          eapply sem_clock_instant_det in ClockR; [|eapply Nrst]. congruence.
          left; constructor. }
        assert (~ Is_update_inst_in s0 tcs) by (intro; apply Nstep; right; auto).
        unfold state_corres; rewrite find_inst_gso; auto.
        apply Insts; split; auto.
        intros ? Rst. apply Nrst. right; auto.
      - intros (Nstep & (?&Rst&Clock)).
        unfold state_corres.
        inversion_clear Rst as [?? Rst'|].
        + inv Rst'.
          setoid_rewrite find_inst_gss.
          rewrite E; apply orel_eq_weaken; auto with memory.
        + destruct (ident_eq_dec s0 s).
          * subst; rewrite find_inst_gss.
            rewrite E; apply orel_eq_weaken; auto with memory.
          * assert (~ Is_update_inst_in s0 tcs) by (intro; apply Nstep; right; auto).
            rewrite find_inst_gso; auto.
            apply (proj1 (proj2 (Insts s0))); eauto.
      - intros Step.
        inversion_clear Step as [?? Step'|].
        + inv Step'.
        + unfold state_corres.
          destruct (ident_eq_dec s0 s).
          * subst; intuition.
          * rewrite find_inst_gso; auto; apply Insts; auto.
    Qed.

    Lemma Memory_Corres_InstReset_absent:
      forall s ck f,
        sem_clock_instant b (var_env R) ck false ->
        Memory_Corres R b (TcReset ck (ResInst s f) :: tcs) S I S' me.
    Proof.
      destruct MemCorres as (States & Insts); intros * ClockR; split; (split; [|split]).
      - intros (NLast&NNext&NReset).
        apply not_Is_update_last_in_cons in NLast as (?&?).
        apply not_Is_update_next_in_cons in NNext as (?&?).
        apply States; split; [|split]; auto.
        intros ? Reset; apply NReset; right; auto.
      - intros (NLast&NNext&(?&Reset&Clock)).
        apply not_Is_update_last_in_cons in NLast as (?&?).
        apply not_Is_update_next_in_cons in NNext as (?&?).
        inversion_clear Reset as [?? NReset|].
        + inv NReset.
        + apply States; eauto.
      - intros [NLast|NLast]; inversion_clear NLast as [?? Last|].
        1,3:inv Last.
        1,2:apply States; auto.
      - intros (Nstep & Nrst).
        assert (~ Is_update_inst_in s0 tcs) by (intro; apply Nstep; right; auto).
        apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&Clock)).
        assert (~ Is_update_inst_in s0 tcs) by (intro; apply Nstep; right; auto).
        inv Rst. inv H1.
        + exfalso. eapply sem_clock_instant_det in ClockR; eauto.
          congruence.
        + apply Insts; eauto.
      - intros Step.
        assert (Is_update_inst_in s0 tcs)
          by (inversion_clear Step as [?? IsSt|]; auto; inv IsSt).
        apply Insts; auto.
    Qed.

    Lemma Memory_Corres_Step_present:
      forall s ys ck ckrs f es Ss' me',
        find_inst s S' = Some Ss' ->
        me' ≋ Ss' ->
        Memory_Corres R b (TcUpdate ck ckrs (UpdInst s ys f es) :: tcs) S I S' (add_inst s me' me).
    Proof.
      destruct MemCorres as (States & Insts); intros * Find' Eq; split; (split; [|split]).
      - intros (NLast&NNext&NReset).
        apply not_Is_update_last_in_cons in NLast as (?&?).
        apply not_Is_update_next_in_cons in NNext as (?&?).
        apply States; split; [|split]; auto.
        intros ? Reset; apply NReset; right; auto.
      - intros (NLast&NNext&(?&Reset&Clock)).
        apply not_Is_update_last_in_cons in NLast as (?&?).
        apply not_Is_update_next_in_cons in NNext as (?&?).
        inversion_clear Reset as [?? NReset|].
        + inv NReset.
        + apply States; eauto.
      - intros [NLast|NLast]; inversion_clear NLast as [?? Last|].
        1,3:inv Last.
        1,2:apply States; auto.
      - intros (Nstep & Nrst).
        assert (~ Is_update_inst_in s0 tcs) by (intro; apply Nstep; right; auto).
        assert (s0 <> s) as Hneq.
        { intros ?; subst. apply Nstep. left; constructor. }
        unfold state_corres.
        rewrite find_inst_gso; auto.
        apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&Clock)).
        assert (~ Is_update_inst_in s0 tcs) by (intro; apply Nstep; right; auto).
        inv Rst. inv H1.
        assert (s0 <> s) as Hneq.
        { intros ?; subst. apply Nstep. left; constructor. }
        unfold state_corres.
        rewrite find_inst_gso; auto.
        apply Insts; eauto.
      - intros Nstep.
        unfold state_corres.
        inversion_clear Nstep as [?? Step|].
        + inv Step.
          rewrite find_inst_gss, Find', Eq. reflexivity.
        + destruct (ident_eq_dec s s0); subst.
          * rewrite find_inst_gss, Find', Eq. reflexivity.
          * rewrite find_inst_gso; auto.
            apply Insts; auto.
    Qed.

    Lemma Memory_Corres_Step_absent:
      forall s ys ck ckrs f es Is Ss',
        inst_consistency (TcUpdate ck ckrs (UpdInst s ys f es) :: tcs) ->
        Forall (fun ckr => exists r, sem_clock_instant b (var_env R) ckr r) ckrs ->
        (Forall (fun ckr : clock => sem_clock_instant b (var_env R) ckr false) ckrs -> find_inst s S ⌈≋⌉ Some Is) ->
        find_inst s I = Some Is ->
        find_inst s S' = Some Ss' ->
        Ss' ≋ Is ->
        Memory_Corres R b (TcUpdate ck ckrs (UpdInst s ys f es) :: tcs) S I S' me.
    Proof.
      destruct MemCorres as (States & Insts); intros * SpecReset ClockR1 ClockR2 FindI Find' Eq; split; (split; [|split]).
      - intros (NLast&NNext&NReset).
        apply not_Is_update_last_in_cons in NLast as (?&?).
        apply not_Is_update_next_in_cons in NNext as (?&?).
        apply States; split; [|split]; auto.
        intros ? Reset; apply NReset; right; auto.
      - intros (NLast&NNext&(?&Reset&Clock)).
        apply not_Is_update_last_in_cons in NLast as (?&?).
        apply not_Is_update_next_in_cons in NNext as (?&?).
        inversion_clear Reset as [?? NReset|].
        + inv NReset.
        + apply States; eauto.
      - intros [NLast|NLast]; inversion_clear NLast as [?? Last|].
        1,3:inv Last.
        1,2:apply States; auto.
      - intros (Nstep & Nrst).
        assert (~ Is_update_inst_in s0 tcs) by (intro; apply Nstep; right; auto).
        apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&Clock)).
        assert (~ Is_update_inst_in s0 tcs) by (intro; apply Nstep; right; auto).
        inv Rst. inv H1.
        apply Insts; eauto.
      - intros Nstep.
        destruct (Is_update_inst_in_dec s0 tcs).
        + apply Insts; auto.
        + inversion_clear Nstep as [?? Step|]. 2:contradiction.
          inv Step.
          unfold state_corres.
          assert (Inst_with_reset_in s ckrs (TcUpdate ck ckrs (UpdInst s ys f es) :: tcs)) as SpecStep by (left; constructor).
          apply SpecReset in SpecStep.
          apply reset_or_not_reset_dec' in ClockR1 as [NotReset|Reset].
          * rewrite Find', Eq, <-ClockR2; auto.
            eapply Insts; split; eauto.
            intros ? Res.
            eapply Forall_forall in NotReset; [eauto|].
            rewrite SpecStep. right; auto.
          * rewrite Find', Eq, <-FindI.
            eapply Exists_exists in Reset as (?&Hin&?).
            rewrite SpecStep in Hin. inv Hin. inv H1.
            eapply Insts; split; eauto.
    Qed.

  End Preservation.

End STCMEMORYCORRES.

Module StcMemoryCorresFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (Cks   : CLOCKS         Ids Op OpAux)
       (Str   : INDEXEDSTREAMS Ids Op OpAux Cks)
       (CESyn : CESYNTAX       Ids Op OpAux Cks)
       (Syn   : STCSYNTAX      Ids Op OpAux Cks CESyn)
       (Ord   : STCORDERED     Ids Op OpAux Cks CESyn Syn)
       (CESem : CESEMANTICS    Ids Op OpAux Cks CESyn Str)
       (Sem   : STCSEMANTICS   Ids Op OpAux Cks CESyn Syn Ord Str CESem)
<: STCMEMORYCORRES Ids Op OpAux Cks Str CESyn Syn Ord CESem Sem.
  Include STCMEMORYCORRES Ids Op OpAux Cks Str CESyn Syn Ord CESem Sem.
End StcMemoryCorresFun.
