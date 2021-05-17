From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Clocks.

From Velus Require Import VelusMemory.

From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcIsReset.
From Velus Require Import Stc.StcIsNext.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCMEMORYCORRES
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX  Op)
       (Import Str   : INDEXEDSTREAMS Op OpAux)
       (Import CESyn : CESYNTAX       Op)
       (Import Syn   : STCSYNTAX Ids  Op CESyn)
       (Import Reset : STCISRESET Ids  Op CESyn Syn)
       (Import Next  : STCISNEXT Ids  Op CESyn Syn).

  Definition state := memory val.
  Definition menv := memory val.

  Definition value_corres (x: ident) (S: state) (me: menv) : Prop :=
    find_val x S = find_val x me.

  Definition state_corres (s: ident) (S: state) (me: menv) : Prop :=
    find_inst s S ⌈≋⌉ find_inst s me.

  Definition Memory_Corres
             (R: env)
             (tcs: list trconstr)
             (S I S': state)
             (me: menv) : Prop :=
    (forall x,
        (~ Is_next_in x tcs /\
         (forall ck, Is_reset_in x ck tcs -> sem_clock_instant true R ck false) ->
         value_corres x S me)
        /\
        (~Is_next_in x tcs /\
         (exists ck, Is_reset_in x ck tcs /\ sem_clock_instant true R ck true) ->
         value_corres x I me)
        /\
        (Is_next_in x tcs -> value_corres x S' me))
    /\
    (forall s,
        (~ Is_step_in s tcs /\
         (forall ck, Is_ireset_in s ck tcs -> sem_clock_instant true R ck false) ->
         state_corres s S me)
        /\
        (~ Is_step_in s tcs /\
         (exists ck, Is_ireset_in s ck tcs /\ sem_clock_instant true R ck true) ->
         state_corres s I me)
        /\
        (Is_step_in s tcs -> state_corres s S' me)).

  Section Preservation.

    Variable (R: env).
    Variables (tcs: list trconstr) (S I S': state) (me: menv).
    Hypothesis MemCorres:  Memory_Corres R tcs S I S' me.

    Lemma Memory_Corres_Def:
      forall x ck ce,
        Memory_Corres R (TcDef x ck ce :: tcs) S I S' me.
    Proof.
      destruct MemCorres as (Resets & Insts); intros; split; (split; [|split]).
      - intros (NNext&NReset).
        rewrite not_Is_next_in_cons in NNext.
        destruct NNext.
        apply Resets; split; auto.
        intros ? Reset; apply NReset; right; auto.
      - intros (NNext&(?&NReset&ClockR)).
        apply not_Is_next_in_cons in NNext as (?&?).
        inv NReset. inv H2.
        apply Resets; eauto.
      - intros NNext. inversion_clear NNext as [?? Next|].
        + inv Next.
        + apply Resets; auto.
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
      forall x ck c0 v v0,
        sem_clock_instant true R ck true ->
        find_val x S = Some v ->
        find_val x I = Some v0 ->
        ~Is_next_in x tcs -> (* Scheduling *)
        Memory_Corres R (TcReset x ck c0 :: tcs) S I S' (add_val x v0 me).
    Proof.
      destruct MemCorres as (Resets & Insts); intros * Clock Hfind1 Hfind2 Hnnext;
        split; (split; [|split]).
      - intros (NNext&NReset).
        apply not_Is_next_in_cons in NNext as (Next&NNext).
        assert (x0 <> x).
        { intro; subst.
          eapply sem_clock_instant_det in Clock; [|eapply NReset]; try congruence.
          left; constructor. }
        unfold value_corres.
        rewrite find_val_gso; auto.
        apply Resets; split; auto.
        intros ? Reset. apply NReset; right; auto.
      - intros (NNext&(ckr&NReset&ClockR)).
        apply not_Is_next_in_cons in NNext as (Next&NNext).
        inversion_clear NReset as [?? Reset|].
        + inv Reset.
          unfold value_corres.
          rewrite find_val_gss; auto.
        + unfold value_corres.
          destruct (ident_eq_dec x x0); subst.
          * rewrite find_val_gss; auto.
          * rewrite find_val_gso; auto.
            apply Resets; split; eauto.
      - intros NNext. inversion_clear NNext as [?? Next|].
        + inv Next.
        + destruct (ident_eq_dec x x0); subst.
          * contradiction.
          * unfold value_corres.
            rewrite find_val_gso; auto.
            apply Resets; auto.
      - intros (Nstep & Nrst).
        assert (~ Is_step_in s tcs) by (intro; apply Nstep; right; auto).
        unfold state_corres; setoid_rewrite find_inst_add_val;
          apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&ClockR)).
        assert (~ Is_step_in s tcs) by (intro; apply Nstep; right; auto).
        inv Rst. inv H1.
        apply Insts; split; eauto.
      - intros Step.
        assert (Is_step_in s tcs)
          by (inversion_clear Step as [?? IsSt|]; auto; inv IsSt).
        unfold state_corres; setoid_rewrite find_inst_add_val;
          apply Insts; auto.
    Qed.

    Lemma Memory_Corres_Reset_absent:
      forall x ck c0,
        sem_clock_instant true R ck false ->
        Memory_Corres R (TcReset x ck c0 :: tcs) S I S' me.
    Proof.
      destruct MemCorres as (Resets & Insts); intros * Clock;
        split; (split; [|split]).
      - intros (NNext&NReset).
        apply not_Is_next_in_cons in NNext as (Next&NNext).
        apply Resets; split; auto.
        intros ? Reset. apply NReset. right; auto.
      - intros (NNext&(ckr&NReset&ClockR)).
        apply not_Is_next_in_cons in NNext as (Next&NNext).
        inversion_clear NReset as [?? Reset|].
        + inv Reset.
          exfalso. eapply sem_clock_instant_det in Clock; eauto.
          congruence.
        + apply Resets; split; eauto.
      - intros NNext. inversion_clear NNext as [?? Next|].
        + inv Next.
        + apply Resets; auto.
      - intros (Nstep & Nrst).
        assert (~ Is_step_in s tcs) by (intro; apply Nstep; right; auto).
        apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&ClockR)).
        assert (~ Is_step_in s tcs) by (intro; apply Nstep; right; auto).
        inv Rst. inv H1.
        apply Insts; split; eauto.
      - intros Step.
        assert (Is_step_in s tcs)
          by (inversion_clear Step as [?? IsSt|]; auto; inv IsSt).
        apply Insts; auto.
    Qed.

    Lemma Memory_Corres_Next_present:
      forall x ck ckrs e c,
        find_val x S' = Some c ->
        Memory_Corres R (TcNext x ck ckrs e :: tcs) S I S' (add_val x c me).
    Proof.
      destruct MemCorres as (Resets & Insts); intros; split; (split; [|split]).
      - intros (NNext&NReset).
        rewrite not_Is_next_in_cons in NNext.
        destruct NNext as (Next&?).
        assert (x0 <> x)
          by (intro; subst; apply Next; constructor).
        unfold value_corres.
        rewrite find_val_gso; auto.
        apply Resets; split; eauto.
        intros * Reset. apply NReset; right; auto.
      - intros (NNext&(?&NReset&ClockR)).
        rewrite not_Is_next_in_cons in NNext. destruct NNext as (Next&?).
        inversion_clear NReset as [?? Reset|].
        + inv Reset.
        + assert (x0 <> x)
            by (intro; subst; apply Next; constructor).
          unfold value_corres.
          rewrite find_val_gso; auto.
          apply Resets; eauto.
      - intros NNext. inversion_clear NNext as [?? Next|].
        + inv Next.
          unfold value_corres.
          rewrite H, find_val_gss; auto.
        + unfold value_corres.
          destruct (ident_eq_dec x x0); subst.
          * rewrite find_val_gss; auto.
          * rewrite find_val_gso; auto.
            apply Resets; auto.
      - intros (Nstep & Nrst).
        assert (~ Is_step_in s tcs) by (intro; apply Nstep; right; auto).
        unfold state_corres; setoid_rewrite find_inst_add_val;
          apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&ClockR)).
        assert (~ Is_step_in s tcs) by (intro; apply Nstep; right; auto).
        inv Rst. inv H2.
        apply Insts; split; eauto.
      - intros Step.
        assert (Is_step_in s tcs)
          by (inversion_clear Step as [?? IsSt|]; auto; inv IsSt).
        unfold state_corres; setoid_rewrite find_inst_add_val;
          apply Insts; auto.
    Qed.

    Lemma reset_or_not_reset_dec : forall b R ckrs,
        Forall (fun ckr => exists r, sem_clock_instant b R ckr r) ckrs ->
        Forall (fun ckr => sem_clock_instant b R ckr false) ckrs \/
        Exists (fun ckr => sem_clock_instant b R ckr true) ckrs.
    Proof.
      intros * Hf.
      induction Hf as [|??([|]&?)]; auto.
      destruct IHHf; auto.
    Qed.

    Lemma Memory_Corres_Next_absent:
      forall x ck ckrs e c,
        reset_consistency (TcNext x ck ckrs e :: tcs) ->
        Forall (fun ckr => exists r, sem_clock_instant true R ckr r) ckrs ->
        (Forall (fun ckr : clock => sem_clock_instant true R ckr false) ckrs -> find_val x S = Some c) ->
        find_val x I = Some c ->
        find_val x S' = Some c ->
        Memory_Corres R (TcNext x ck ckrs e :: tcs) S I S' me.
    Proof.
      destruct MemCorres as (Resets & Insts); intros * SpecReset ClockR Eq1 Eq2 Eq3; split; (split; [|split]).
      - intros (NNext&NReset).
        apply not_Is_next_in_cons in NNext as (NNext1&NNext2).
        apply Resets; split; auto.
        intros. apply NReset. right; auto.
      - intros (NNext&(?&Reset&Clock)).
        apply not_Is_next_in_cons in NNext as (NNext1&NNext2).
        inversion_clear Reset as [?? NReset|].
        + inv NReset.
        + apply Resets; split; eauto.
      - intros NNext.
        destruct (Is_next_in_dec x0 tcs). apply Resets; auto.
        inversion_clear NNext as [?? Next|]. 2:contradiction.
        inv Next.
        assert (Next_with_reset_in x ckrs (TcNext x ck ckrs e :: tcs)) as SpecNext by (left; constructor).
        apply SpecReset in SpecNext.
        setoid_rewrite Is_reset_in_reflect in SpecNext. simpl in SpecNext. setoid_rewrite <-Is_reset_in_reflect in SpecNext.
        apply reset_or_not_reset_dec in ClockR as [Reset|NotReset].
        + specialize (Eq1 Reset).
          unfold value_corres. rewrite Eq3, <-Eq1.
          apply Resets; split; auto.
          intros ? IReset. eapply SpecNext, Forall_forall in IReset; eauto.
          assumption.
        + unfold value_corres. rewrite Eq3, <-Eq2.
          apply Resets; split; auto.
          apply Exists_exists in NotReset as (ckr&Hsem&Hin).
          exists ckr. rewrite <-SpecNext. auto.
      - intros (Nstep & Nrst).
        assert (~ Is_step_in s tcs) by (intro; apply Nstep; right; auto).
        apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&Clock)).
        assert (~ Is_step_in s tcs) by (intro; apply Nstep; right; auto).
        inv Rst. inv H1.
        apply Insts; split; eauto.
      - intros Step.
        assert (Is_step_in s tcs)
          by (inversion_clear Step as [?? IsSt|]; auto; inv IsSt).
        apply Insts; auto.
    Qed.

    Lemma Memory_Corres_InstReset_present:
      forall s ck b Is me',
        sem_clock_instant true R ck true ->
        find_inst s I = Some Is ->
        me' ≋ Is ->
        ~ Is_step_in s tcs -> (* Scheduling *)
        Memory_Corres R (TcInstReset s ck b :: tcs) S I S' (add_inst s me' me).
    Proof.
      destruct MemCorres as (Resets & Insts); intros ????? ClockR Find1 E NStep; split; (split; [|split]).
      - intros (NNext&NReset).
        apply not_Is_next_in_cons in NNext as (NNext1&NNext2).
        apply Resets; split; auto.
        intros. apply NReset. right; auto.
      - intros (NNext&(?&Reset&Clock)).
        apply not_Is_next_in_cons in NNext as (NNext1&NNext2).
        inversion_clear Reset as [?? NReset|].
        + inv NReset.
        + apply Resets; eauto.
      - intros NNext.
        inversion_clear NNext as [?? Next|].
        + inv Next.
        + apply Resets; auto.
      - intros (Nstep & Nrst).
        assert (s0 <> s).
        { intro; subst.
          eapply sem_clock_instant_det in ClockR; [|eapply Nrst]. congruence.
          left; constructor. }
        assert (~ Is_step_in s0 tcs) by (intro; apply Nstep; right; auto).
        unfold state_corres; rewrite find_inst_gso; auto.
        apply Insts; split; auto.
        intros ? Rst. apply Nrst. right; auto.
      - intros (Nstep & (?&Rst&Clock)).
        unfold state_corres.
        inversion_clear Rst as [?? Rst'|].
        + inv Rst'.
          setoid_rewrite find_inst_gss.
          rewrite E; apply orel_eq_weaken; auto.
        + destruct (ident_eq_dec s0 s).
          * subst; rewrite find_inst_gss.
            rewrite E; apply orel_eq_weaken; auto.
          * assert (~ Is_step_in s0 tcs) by (intro; apply Nstep; right; auto).
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
      forall s ck b,
        sem_clock_instant true R ck false ->
        Memory_Corres R (TcInstReset s ck b :: tcs) S I S' me.
    Proof.
      destruct MemCorres as (Resets & Insts); intros * ClockR; split; (split; [|split]).
      - intros (NNext&NReset).
        apply not_Is_next_in_cons in NNext as (NNext1&NNext2).
        apply Resets; split; auto.
        intros. apply NReset. right; auto.
      - intros (NNext&(?&Reset&Clock)).
        apply not_Is_next_in_cons in NNext as (NNext1&NNext2).
        inversion_clear Reset as [?? NReset|].
        + inv NReset.
        + apply Resets; eauto.
      - intros NNext.
        inversion_clear NNext as [?? Next|].
        + inv Next.
        + apply Resets; auto.
      - intros (Nstep & Nrst).
        assert (~ Is_step_in s0 tcs) by (intro; apply Nstep; right; auto).
        apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&Clock)).
        assert (~ Is_step_in s0 tcs) by (intro; apply Nstep; right; auto).
        inv Rst. inv H1.
        + exfalso. eapply sem_clock_instant_det in ClockR; eauto.
          congruence.
        + apply Insts; eauto.
      - intros Step.
        assert (Is_step_in s0 tcs)
          by (inversion_clear Step as [?? IsSt|]; auto; inv IsSt).
        apply Insts; auto.
    Qed.

    Lemma Memory_Corres_Step_present:
      forall s ys ck ckrs b es Ss' me',
        find_inst s S' = Some Ss' ->
        me' ≋ Ss' ->
        Memory_Corres R (TcStep s ys ck ckrs b es :: tcs) S I S' (add_inst s me' me).
    Proof.
      destruct MemCorres as (Resets & Insts); intros * Find' Eq; split; (split; [|split]).
      - intros (NNext&NReset).
        apply not_Is_next_in_cons in NNext as (NNext1&NNext2).
        apply Resets; split; auto.
        intros. apply NReset. right; auto.
      - intros (NNext&(?&Reset&Clock)).
        apply not_Is_next_in_cons in NNext as (NNext1&NNext2).
        inversion_clear Reset as [?? NReset|].
        + inv NReset.
        + apply Resets; eauto.
      - intros NNext.
        inversion_clear NNext as [?? Next|].
        + inv Next.
        + apply Resets; auto.
      - intros (Nstep & Nrst).
        assert (~ Is_step_in s0 tcs) by (intro; apply Nstep; right; auto).
        assert (s0 <> s) as Hneq.
        { intros ?; subst. apply Nstep. left; constructor. }
        unfold state_corres.
        rewrite find_inst_gso; auto.
        apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&Clock)).
        assert (~ Is_step_in s0 tcs) by (intro; apply Nstep; right; auto).
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
          rewrite find_inst_gss, Find', Eq; auto.
        + destruct (ident_eq_dec s s0); subst.
          * rewrite find_inst_gss, Find', Eq; auto.
          * rewrite find_inst_gso; auto.
            apply Insts; auto.
    Qed.

    Lemma Memory_Corres_Step_absent:
      forall s ys ck ckrs b es Is Ss',
        ireset_consistency (TcStep s ys ck ckrs b es :: tcs) ->
        Forall (fun ckr => exists r, sem_clock_instant true R ckr r) ckrs ->
        (Forall (fun ckr : clock => sem_clock_instant true R ckr false) ckrs -> find_inst s S ⌈≋⌉ Some Is) ->
        find_inst s I = Some Is ->
        find_inst s S' = Some Ss' ->
        Ss' ≋ Is ->
        Memory_Corres R (TcStep s ys ck ckrs b es :: tcs) S I S' me.
    Proof.
      destruct MemCorres as (Resets & Insts); intros * SpecReset ClockR1 ClockR2 FindI Find' Eq; split; (split; [|split]).
      - intros (NNext&NReset).
        apply not_Is_next_in_cons in NNext as (NNext1&NNext2).
        apply Resets; split; auto.
        intros. apply NReset. right; auto.
      - intros (NNext&(?&Reset&Clock)).
        apply not_Is_next_in_cons in NNext as (NNext1&NNext2).
        inversion_clear Reset as [?? NReset|].
        + inv NReset.
        + apply Resets; eauto.
      - intros NNext.
        inversion_clear NNext as [?? Next|].
        + inv Next.
        + apply Resets; auto.
      - intros (Nstep & Nrst).
        assert (~ Is_step_in s0 tcs) by (intro; apply Nstep; right; auto).
        apply Insts; split; auto.
        intros * Rst. apply Nrst; right; auto.
      - intros (Nstep & (?&Rst&Clock)).
        assert (~ Is_step_in s0 tcs) by (intro; apply Nstep; right; auto).
        inv Rst. inv H1.
        apply Insts; eauto.
      - intros Nstep.
        destruct (Is_step_in_dec s0 tcs).
        + apply Insts; auto.
        + inversion_clear Nstep as [?? Step|]. 2:contradiction.
          inv Step.
          unfold state_corres.
          assert (Step_with_ireset_in s ckrs (TcStep s ys ck ckrs b es :: tcs)) as SpecStep by (left; constructor).
          apply SpecReset in SpecStep.
          apply reset_or_not_reset_dec in ClockR1 as [NotReset|Reset].
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
       (OpAux : OPERATORS_AUX  Op)
       (Str   : INDEXEDSTREAMS Op OpAux)
       (CESyn : CESYNTAX      Op)
       (Syn   : STCSYNTAX Ids Op CESyn)
       (Reset : STCISRESET Ids Op CESyn Syn)
       (Next  : STCISNEXT Ids Op CESyn Syn)
<: STCMEMORYCORRES Ids Op OpAux Str CESyn Syn Reset Next.
  Include STCMEMORYCORRES Ids Op OpAux Str CESyn Syn Reset Next.
End StcMemoryCorresFun.
