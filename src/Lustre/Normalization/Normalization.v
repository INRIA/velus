From Coq Require Import String.
From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.

From compcert Require Import common.Errors.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax Lustre.LCausality.
From Velus Require Import Lustre.Normalization.Fresh.
From Velus Require Import Lustre.Normalization.Unnesting Lustre.Normalization.NormFby.

(** * Complete Normalization *)

Module Type NORMALIZATION
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (Import Caus : LCAUSALITY Ids Op OpAux Cks Syn).

  Module Export Unnesting := UnnestingFun Ids Op OpAux Cks Syn.
  Module Export NormFby := NormFbyFun Ids Op OpAux Cks Syn Unnesting.

  Definition normalize_global G :=
    let G' := unnest_global G in
    do _ <- check_causality G';
    OK (normfby_global G').

  Lemma normalize_global_iface_eq : forall G G',
      normalize_global G = OK G' ->
      global_iface_eq G G'.
  Proof.
    intros * Hnorm.
    unfold normalize_global in Hnorm. monadInv Hnorm.
    eapply global_iface_eq_trans.
    eapply unnest_global_eq. eapply normfby_global_eq.
  Qed.

  Theorem normalize_global_normalized_global : forall G G',
      wl_global G ->
      normalize_global G = OK G' ->
      normalized_global G'.
  Proof.
    intros G * Hwl Hnorm.
    unfold normalize_global in Hnorm.
    destruct check_causality in Hnorm; inv Hnorm.
    eapply normfby_global_normalized_global.
    eapply unnest_global_unnested_global; auto.
  Qed.

End NORMALIZATION.

Module NormalizationFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (Caus : LCAUSALITY Ids Op OpAux Cks Syn)
       <: NORMALIZATION Ids Op OpAux Cks Syn Caus.
  Include NORMALIZATION Ids Op OpAux Cks Syn Caus.
End NormalizationFun.
