From Coq Require Import String.
From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.

From compcert Require Import common.Errors.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Lustre.LSyntax Lustre.LCausality.
From Velus Require Import Lustre.Normalization.Fresh.
From Velus Require Import Lustre.Normalization.Unnesting Lustre.Normalization.NormFby.

(** * Complete Normalization *)

Module Type NORMALIZATION
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Caus : LCAUSALITY Ids Op Syn).

  Module Export Unnesting := UnnestingFun Ids Op OpAux Syn.
  Module Export NormFby := NormFbyFun Ids Op OpAux Syn Unnesting.

  Definition normalize_global G :
    wl_global G ->
    Forall (fun n => n_prefixes n = elab_prefs) G ->
    res global.
  Proof.
    intros Hwl Hprefs.
    remember (unnest_global G Hwl Hprefs) as G'.
    refine (Errors.bind (check_causality G') _).
    intros _.
    refine (OK (normfby_global G' _ _)).
    - rewrite HeqG'. eapply unnest_global_unnested_global.
    - eapply unnest_global_prefixes; eauto.
  Defined.

  Lemma normalize_global_prefixes : forall G Hwl Hprefs G',
      normalize_global G Hwl Hprefs = OK G' ->
      Forall (fun n => PS.Equal (n_prefixes n) (PSP.of_list gensym_prefs)) G'.
  Proof.
    intros * Hnorm.
    unfold normalize_global in Hnorm.
    monadInv Hnorm.
    eapply Forall_impl; [|eauto]. 2:eapply normfby_global_prefixes; eauto.
    intros ? Heq; rewrite Heq.
    rewrite <- ps_adds_of_list. simpl.
    reflexivity.
  Qed.

  Lemma normalize_global_iface_eq : forall G Hwl Hprefs G',
      normalize_global G Hwl Hprefs = OK G' ->
      global_iface_eq G G'.
  Proof.
    intros * Hnorm.
    unfold normalize_global in Hnorm. monadInv Hnorm.
    etransitivity.
    eapply unnest_global_eq. eapply normfby_global_eq.
  Qed.

  Theorem normalize_global_normalized_global : forall G G' Hwl Hprefs,
      normalize_global G Hwl Hprefs = OK G' ->
      normalized_global G'.
  Proof.
    intros G * Hnorm.
    unfold normalize_global in Hnorm.
    destruct check_causality in Hnorm; inv Hnorm.
    eapply normfby_global_normalized_global.
  Qed.

  (** Helper for the l_to_nl function *)
  Program Definition normalize_global' (G : {G | wl_global G /\ Forall (fun n => n_prefixes n = elab_prefs) G}) :
    {G | match G with OK G => Forall (fun n => PS.Equal (n_prefixes n) (PSP.of_list gensym_prefs)) G | _ => True end } :=
    exist _ (normalize_global G _ _) _.
  Next Obligation.
    destruct (normalize_global _ _) eqn:Hglob; auto.
    eapply normalize_global_prefixes in Hglob; eauto.
  Qed.
End NORMALIZATION.

Module NormalizationFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Caus : LCAUSALITY Ids Op Syn)
       <: NORMALIZATION Ids Op OpAux Syn Caus.
  Include NORMALIZATION Ids Op OpAux Syn Caus.
End NormalizationFun.
