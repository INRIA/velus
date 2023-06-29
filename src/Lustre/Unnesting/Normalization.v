From Coq Require Import String.
From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.

From compcert Require Import common.Errors.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.Normalization.Unnesting Lustre.Normalization.NormFby.

(** * Complete Normalization *)

Module Type NORMALIZATION
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv).

  Module Export Unnesting := UnnestingFun Ids Op OpAux Cks Senv Syn.
  Module Export NormFby := NormFbyFun Ids Op OpAux Cks Senv Syn Unnesting.

  Definition normalize_global G :=
    normfby_global (unnest_global G).

  Lemma normalize_global_iface_eq : forall G,
      global_iface_eq G (normalize_global G).
  Proof.
    intros *.
    unfold normalize_global.
    eapply global_iface_eq_trans.
    eapply unnest_global_eq. eapply normfby_global_eq.
  Qed.

  Theorem normalize_global_normalized_global : forall G,
      wl_global G ->
      wx_global G ->
      normalized_global (normalize_global G).
  Proof.
    intros G * Hwl Hwx.
    eapply normfby_global_normalized_global.
    eapply unnest_global_unnested_global; auto.
  Qed.

End NORMALIZATION.

Module NormalizationFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       <: NORMALIZATION Ids Op OpAux Cks Senv Syn.
  Include NORMALIZATION Ids Op OpAux Cks Senv Syn.
End NormalizationFun.
