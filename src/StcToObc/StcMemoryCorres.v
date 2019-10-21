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
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Clocks.

From Velus Require Import VelusMemory.

From Velus Require Import Stc.StcIsLast.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCMEMORYCORRES
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX      Op)
       (Import Syn   : STCSYNTAX Ids Op CESyn)
       (Import Last  : STCISLAST Ids Op CESyn Syn).

  Definition state := memory val.
  Definition menv := memory val.

  Definition value_corres (x: ident) (S: state) (me: menv) : Prop :=
    find_val x S = find_val x me.

  Definition state_corres (s: ident) (S: state) (me: menv) : Prop :=
    find_inst s S ⌈≋⌉ find_inst s me.

  Definition Memory_Corres
             (tcs: list trconstr)
             (S I S': state)
             (me: menv) : Prop :=
    (forall x,
        (Is_last_in x tcs -> value_corres x S' me)
        /\
        (~ Is_last_in x tcs -> value_corres x S me))
    /\
    (forall s,
        (~ Step_in s tcs /\ ~ Reset_in s tcs ->
         state_corres s S me)
        /\
        (~ Step_in s tcs /\ Reset_in s tcs ->
         state_corres s I me)
        /\
        (Step_in s tcs ->
         state_corres s S' me)).

  Section Preservation.

    Variables (tcs: list trconstr) (S I S': state) (me: menv).
    Hypothesis MemCorres:  Memory_Corres tcs S I S' me.

    Lemma Memory_Corres_Def:
      forall x ck ce,
        Memory_Corres (TcDef x ck ce :: tcs) S I S' me.
    Proof.
      destruct MemCorres as (Lasts & Insts); intros; split; [split|split; [|split]].
      - inversion_clear 1 as [?? Last|]; eauto.
        + inv Last.
        + apply Lasts; auto.
      - intro NLast; apply Lasts.
        intro; apply NLast; right; auto.
      - intros (Nstep & Nrst).
        apply Insts; split.
        + intro; apply Nstep; right; auto.
        + intro; apply Nrst; right; auto.
      - intros (Nstep & Rst).
        apply Insts; split.
        + intro; apply Nstep; right; auto.
        + inversion_clear Rst as [?? IsSt|]; auto.
          inv IsSt.
      - intros Step.
        apply Insts; inversion_clear Step as [?? IsSt|]; auto.
        inv IsSt.
    Qed.

    Lemma Memory_Corres_Next_present:
      forall x ck e c,
        find_val x S' = Some c ->
        Memory_Corres (TcNext x ck e :: tcs) S I S' (add_val x c me).
    Proof.
      destruct MemCorres as (Lasts & Insts); intros; split; [split|split; [|split]].
      - inversion_clear 1 as [?? Last|?? Last]; eauto; unfold value_corres.
        + inv Last; rewrite find_val_gss; auto.
        + intros.
          destruct (ident_eq_dec x0 x).
          * subst; rewrite find_val_gss; auto.
          * rewrite find_val_gso; auto;
              apply Lasts with (1 := Last); auto.
      - intros NLast **; unfold value_corres.
        assert (x0 <> x)
          by (intro; subst; apply NLast; left; constructor).
        assert ( ~ Is_last_in x0 tcs)
          by (intro; apply NLast; right; auto).
        rewrite find_val_gso; auto;
          apply Lasts; auto.
      - intros (Nstep & Nrst).
        assert (~ Step_in s tcs) by (intro; apply Nstep; right; auto).
        assert (~ Reset_in s tcs) by (intro; apply Nrst; right; auto).
        unfold state_corres; setoid_rewrite find_inst_add_val;
          apply Insts; auto.
      - intros (Nstep & Rst).
        assert (~ Step_in s tcs) by (intro; apply Nstep; right; auto).
        assert (Reset_in s tcs)
          by (inversion_clear Rst as [?? IsSt|]; auto; inv IsSt).
        apply Insts; auto.
      - intros Step.
        assert (Step_in s tcs)
          by (inversion_clear Step as [?? IsSt|]; auto; inv IsSt).
        unfold state_corres; setoid_rewrite find_inst_add_val;
          apply Insts; auto.
    Qed.

    Lemma Memory_Corres_Next_absent:
      forall x ck e,
        find_val x S' = find_val x S ->
        Memory_Corres (TcNext x ck e :: tcs) S I S' me.
    Proof.
      destruct MemCorres as (Lasts & Insts); intros * Eq; split; [split|split; [|split]].
      - inversion_clear 1 as [?? Last|?? Last]; eauto; unfold value_corres.
        + inv Last.
          destruct (Is_last_in_dec x tcs).
          * apply Lasts; auto.
          * setoid_rewrite Eq; apply Lasts; auto.
        + apply Lasts; auto.
      - intros NLast.
        apply Lasts; intro; apply NLast; right; auto.
      - intros (Nstep & Nrst).
        apply Insts; split.
        + intro; apply Nstep; right; auto.
        + intro; apply Nrst; right; auto.
      - intros (Nstep & Rst).
        apply Insts; split.
        + intro; apply Nstep; right; auto.
        + inversion_clear Rst as [?? IsSt|]; auto.
          inv IsSt.
      - intros Step.
        apply Insts; inversion_clear Step as [?? IsSt|]; auto.
        inv IsSt.
    Qed.

    Lemma Memory_Corres_Reset_present:
      forall s ck b Is me',
        find_inst s I = Some Is ->
        me' ≋ Is ->
        ~ Step_in s tcs ->
        Memory_Corres (TcReset s ck b :: tcs) S I S' (add_inst s me' me).
    Proof.
      destruct MemCorres as (Lasts & Insts); intros ?????? E; split; [split|split; [|split]].
      - inversion_clear 1 as [?? Last|]; eauto.
        + inv Last.
        + apply Lasts; auto.
      - intro NLast; apply Lasts.
        intro; apply NLast; right; auto.
      - intros (Nstep & Nrst).
        assert (s0 <> s)
          by (intro; subst; apply Nrst; left; constructor).
        assert (~ Step_in s0 tcs) by (intro; apply Nstep; right; auto).
        assert (~ Reset_in s0 tcs) by (intro; apply Nrst; right; auto).
        unfold state_corres; rewrite find_inst_gso; auto;
          apply Insts; auto.
      - intros (Nstep & Rst).
        unfold state_corres.
        inversion_clear Rst as [?? Rst'|].
        + inv Rst'.
          setoid_rewrite find_inst_gss.
          rewrite E; apply orel_eq_weaken; auto.
        + destruct (ident_eq_dec s0 s).
          * subst; rewrite find_inst_gss.
            rewrite E; apply orel_eq_weaken; auto.
          * assert (~ Step_in s0 tcs) by (intro; apply Nstep; right; auto).
            rewrite find_inst_gso; auto;
              apply (proj1 (proj2 (Insts s0))); auto.
      - intros Step.
        inversion_clear Step as [?? Step'|].
        + inv Step'.
        + unfold state_corres.
          destruct (ident_eq_dec s0 s).
          * subst; intuition.
          * rewrite find_inst_gso; auto; apply Insts; auto.
    Qed.

    Lemma Memory_Corres_Reset_absent:
      forall s ck b Is Ss,
        find_inst s I = Some Is ->
        find_inst s S = Some Ss ->
        Is ≋ Ss ->
        ~ Reset_in s tcs ->
        Memory_Corres (TcReset s ck b :: tcs) S I S' me.
    Proof.
      destruct MemCorres as (Lasts & Insts); intros ????? Find_I Find_S E; split; [split|split; [|split]].
      - inversion_clear 1 as [?? Last|]; eauto.
        + inv Last.
        + apply Lasts; auto.
      - intro NLast; apply Lasts.
        intro; apply NLast; right; auto.
      - intros (Nstep & Nrst).
        apply Insts; split.
        + intro; apply Nstep; right; auto.
        + intro; apply Nrst; right; auto.
      - intros (Nstep & Rst).
        inversion_clear Rst as [?? Rst'|].
        + inv Rst'.
          assert (~ Step_in s tcs) by (intro; apply Nstep; right; auto).
          unfold state_corres.
          rewrite Find_I, E, <-Find_S.
          apply (proj1 (Insts s)); auto.
        + apply Insts; split; auto.
          intro; apply Nstep; right; auto.
      - intros Step.
        inversion_clear Step as [?? Step'|].
        + inv Step'.
        + apply Insts; eauto.
    Qed.

    Lemma Memory_Corres_Call_present:
      forall s ys ck (rst: bool) b es Ss' me',
        find_inst s S' = Some Ss' ->
        me' ≋ Ss' ->
        Memory_Corres (TcCall s ys ck rst b es :: tcs) S I S' (add_inst s me' me).
    Proof.
      destruct MemCorres as (Lasts & Insts); intros ???????? Find_S' E;
        split; [split|split; [|split]].
      - inversion_clear 1 as [?? Last|]; eauto.
        + inv Last.
        + apply Lasts; auto.
      - intro NLast; apply Lasts.
        intro; apply NLast; right; auto.
      - intros (Nstep & Nrst).
        assert (s0 <> s) as Neq
            by (intro; subst; apply Nstep; left; constructor).
        assert (~ Step_in s0 tcs) by (intro; apply Nstep; right; auto).
        assert (~ Reset_in s0 tcs) by (intro; apply Nrst; right; auto).
        unfold state_corres; rewrite find_inst_gso; auto;
          apply Insts; auto.
      - intros (Nstep & Rst).
        assert (s0 <> s) as Neq
            by (intro; subst; apply Nstep; left; constructor).
        assert (~ Step_in s0 tcs) by (intro; apply Nstep; right; auto).
        inversion_clear Rst as [?? Rst'|]; try inv Rst'.
        unfold state_corres; rewrite find_inst_gso; auto;
          apply Insts; auto.
      - intros Step.
        unfold state_corres.
        inversion_clear Step as [?? Step'|].
        + inv Step'.
          rewrite find_inst_gss.
          rewrite E; apply orel_eq_weaken; auto.
        + destruct (ident_eq_dec s0 s).
          * subst; rewrite find_inst_gss.
            rewrite E; apply orel_eq_weaken; auto.
          * rewrite find_inst_gso; auto; apply Insts; auto.
    Qed.

    Lemma Memory_Corres_Call_absent:
      forall s ys ck (rst: bool) b es Is Ss',
        find_inst s I = Some Is ->
        (rst = false -> find_inst s S ⌈≋⌉ Some Is) ->
        find_inst s S' = Some Ss' ->
        Ss' ≋ Is ->
        ~ Step_in s tcs /\ (if rst then Reset_in s tcs else ~ Reset_in s tcs) ->
        Memory_Corres (TcCall s ys ck rst b es :: tcs) S I S' me.
    Proof.
      destruct MemCorres as (Lasts & Insts); intros ???????? Find_I Find_S Find_S' E NstepRst;
        split; [split|split; [|split]].
      - inversion_clear 1 as [?? Last|]; eauto.
        + inv Last.
        + apply Lasts; auto.
      - intro NLast; apply Lasts.
        intro; apply NLast; right; auto.
      - intros (Nstep & Nrst).
        apply Insts; split.
        + intro; apply Nstep; right; auto.
        + intro; apply Nrst; right; auto.
      - intros (Nstep & Rst).
        apply Insts; split.
        + intro; apply Nstep; right; auto.
        + inversion_clear Rst as [?? Rst'|]; auto.
          inv Rst'.
      - intros Step.
        inversion_clear Step as [?? Step'|].
        + inv Step'.
          destruct rst; apply Insts in NstepRst; unfold state_corres in *.
          * rewrite <-NstepRst, Find_I, <-E.
            apply orel_eq_weaken; auto.
          * rewrite <-NstepRst, Find_S, <-E; auto.
            apply orel_eq_weaken; auto.
        + apply Insts; eauto.
    Qed.

  End Preservation.

End STCMEMORYCORRES.

Module StcMemoryCorresFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX      Op)
       (Syn   : STCSYNTAX Ids Op CESyn)
       (Last  : STCISLAST Ids Op CESyn Syn)
<: STCMEMORYCORRES Ids Op CESyn Syn Last.
  Include STCMEMORYCORRES Ids Op CESyn Syn Last.
End StcMemoryCorresFun.
