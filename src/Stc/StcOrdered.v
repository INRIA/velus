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
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcIsSystem.
From Velus Require Import Clocks.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCORDERED
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX        Op)
       (Import Syn   : STCSYNTAX   Ids Op CESyn)
       (Import Syst  : STCISSYSTEM Ids Op CESyn Syn).

  Inductive Ordered_systems: program -> Prop :=
  | Ordered_nil:
      Ordered_systems []
  | Ordered_cons:
      forall s P,
        Ordered_systems P ->
        Forall (fun xb =>
                  snd xb <> s.(s_name)
                  /\ exists s' P', find_system (snd xb) P = Some (s', P'))
               s.(s_subs) ->
        Forall (fun s' => s.(s_name) <> s'.(s_name))%type P ->
        Ordered_systems (s :: P).

  Remark Ordered_systems_split:
    forall P1 s P,
      Ordered_systems (P1 ++ s :: P) ->
      Forall (fun xb =>
                  find_system (snd xb) P1 = None
                  /\ snd xb <> s.(s_name)
                  /\ exists s' P', find_system (snd xb) P = Some (s', P'))
             s.(s_subs).
  Proof.
    induction P1; inversion_clear 1 as [|?? Ord]; apply Forall_Forall; auto.
    - apply Forall_forall; auto.
    - apply IHP1 in Ord; apply Forall_forall; intros.
      eapply Forall_forall in Ord as (?&?&(s' &?& Find)); eauto.
      rewrite find_system_other; auto.
      pose proof Find as Find'; apply find_system_name in Find'.
      apply find_system_In in Find.
      assert (In s' (P1 ++ s :: P)) as Hin
          by (apply in_app; right; right; auto).
      eapply Forall_forall in Hin; eauto.
      congruence.
    - apply IHP1 in Ord; apply Forall_forall; intros.
      eapply Forall_forall in Ord as (?&?&?); eauto.
  Qed.

  Lemma Ordered_systems_append:
    forall P P',
      Ordered_systems (P ++ P') ->
      Ordered_systems P'.
  Proof.
    induction P; [intuition|].
    intros * HnPP.
    apply IHP; inversion_clear HnPP; assumption.
  Qed.

  Lemma Ordered_systems_find_In_systems:
    forall P b s P',
      Ordered_systems P ->
      find_system b P = Some (s, P') ->
      forall x b,
        In (x, b) s.(s_subs) ->
        exists s P'', find_system b P' = Some (s, P'').
  Proof.
    induction P as [|system]; try now inversion 2.
    intros * Ord Find ?? Hin.
    inv Ord.
    simpl in Find.
    destruct (ident_eqb (s_name system) b) eqn: E; eauto.
    inv Find.
    eapply Forall_forall in Hin; eauto.
    destruct Hin; eauto.
  Qed.

  Lemma Ordered_systems_find_system:
    forall P b s P',
      Ordered_systems P ->
      find_system b P = Some (s, P') ->
      Ordered_systems P'.
  Proof.
    induction P as [|system]; try now inversion 2.
    intros * Ord Find.
    inv Ord.
    simpl in Find.
    destruct (ident_eqb (s_name system) b) eqn: E; eauto.
    inv Find; auto.
  Qed.
 Lemma find_system_later_not_Is_system_in:
    forall f s P s' P',
      Ordered_systems (s :: P) ->
      find_system f P = Some (s', P') ->
      ~ Is_system_in s.(s_name) s'.(s_tcs).
  Proof.
    intros * Hord Hfind Hini.
    apply find_system_app in Hfind as (?& E &?); rewrite E, app_comm_cons in Hord.
    pose proof Hord as Hord'; inversion_clear Hord' as [|??? Sub Hnin]; clear Sub.
    apply Ordered_systems_split in Hord.
    apply calls_resets_of_Is_system_in in Hini.
    apply s_subs_in_tcs, in_map_iff in Hini as (?&?& Hin).
    eapply Forall_forall in Hin; eauto; destruct Hin as (?&?&?&?& Find); simpl in Find.
    apply Forall_app_weaken in Hnin; inversion_clear Hnin as [|??? Hnin'].
    pose proof Find as Find'; apply find_system_name in Find'.
    apply find_system_In in Find.
    eapply Forall_forall in Find; eauto.
    congruence.
  Qed.

  Lemma find_system_not_Is_system_in:
    forall f s P P',
      Ordered_systems P ->
      find_system f P = Some (s, P') ->
      ~ Is_system_in s.(s_name) s.(s_tcs).
  Proof.
    intros * Hord Hfind Hini.
    apply find_system_app in Hfind as (?& E &?); rewrite E in Hord.
    apply Ordered_systems_split in Hord.
    apply calls_resets_of_Is_system_in in Hini.
    apply s_subs_in_tcs, in_map_iff in Hini as (?&?& Hin).
    eapply Forall_forall in Hin; eauto; destruct Hin as (?&?&?); auto.
  Qed.

End STCORDERED.

Module StcOrderedFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX        Op)
       (Syn   : STCSYNTAX   Ids Op CESyn)
       (Syst  : STCISSYSTEM Ids Op CESyn Syn)
<: STCORDERED Ids Op CESyn Syn Syst.
  Include STCORDERED Ids Op CESyn Syn Syst.
End StcOrderedFun.
