From Coq Require Import String.
From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.

From compcert Require Import common.Errors.
From Velus Require Import Common Ident.
From Velus Require Import Operators.
From Velus Require Import Lustre.LSyntax Lustre.LCausality.
From Velus Require Import Lustre.Normalization.Fresh.
From Velus Require Import Lustre.Normalization.Untuple Lustre.Normalization.NormFby.

(** * Normalization of a full norm *)

Local Set Warnings "-masking-absolute-name".
Module Type NORMALIZATION
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Caus : LCAUSALITY Ids Op Syn).

  Module Export Untuple := UntupleFun Ids Op OpAux Syn.
  Module Export NormFby := NormFbyFun Ids Op OpAux Syn Untuple.

  Definition normalize_global (G : { G : global | wl_global G }) : res global.
  Proof.
    destruct G as [G Hwl].
    remember (untuple_global G Hwl) as G'.
    refine (bind (check_causality G') _).
    intros _.
    refine (OK (normfby_global G' _)).
    rewrite HeqG'. eapply untuple_global_untupled_global.
  Defined.

  Theorem normalize_global_normalized_global : forall G G',
      normalize_global G = OK G' ->
      normalized_global G'.
  Proof.
    intros [G Hwl] * Hnorm.
    unfold normalize_global in Hnorm.
    destruct check_causality in Hnorm; inv Hnorm.
    eapply normfby_global_normalized_global.
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
