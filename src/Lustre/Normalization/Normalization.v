From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common Ident.
From Velus Require Import Operators.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping.
From Velus Require Import Lustre.Normalization.Fresh.
From Velus Require Import Lustre.Normalization.Untuple Lustre.Normalization.NormFby.

(** * Normalization of a full norm *)

Local Set Warnings "-masking-absolute-name".
Module Type NORMALIZATION
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op).

  Module Export Untuple := UntupleFun Ids Op OpAux Syn.
  Module Export NormFby := NormFbyFun Ids Op OpAux Syn Untuple.

  Definition normalize_global (G : global) (Hwl : wl_global G) : global.
  Proof.
    remember (untuple_global G Hwl) as G'.
    refine (normfby_global G' _).
    rewrite HeqG'. eapply untuple_global_untupled_global.
  Defined.

  Theorem normalize_global_normalized_global : forall G (Hwl : wl_global G),
      normalized_global (normalize_global G Hwl).
  Proof.
    intros *.
    unfold normalize_global.
    eapply normfby_global_normalized_global.
  Qed.
End NORMALIZATION.

Module NormalizationFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       <: NORMALIZATION Ids Op OpAux Syn.
  Include NORMALIZATION Ids Op OpAux Syn.
End NormalizationFun.
