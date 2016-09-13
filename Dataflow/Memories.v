Require Import Rustre.Common.
Require Import PArith.

Import List.ListNotations.
Open Scope list_scope.

Require Import Rustre.Dataflow.Syntax.

(** * Collecting memory cells *)

(** 

  The [memories] function collects the set of variables that will turn
  into heap variables after compilation, ie. variables denoting an
  [fby] equation.

  We (ought to) have the following equivalence:
    [forall x, PS.In x (memories eqs) <-> ~ Is_Variable x eqs]

 *)

Module Type MEMORIES
       (Ids : IDS)
       (Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op).

  Definition memory_eq (mems: PS.t) (eq: equation) : PS.t :=
    match eq with
    | EqFby x _ _ _ => PS.add x mems
    | _ => mems
    end.

  Definition memories (eqs: list equation) : PS.t :=
    List.fold_left memory_eq eqs PS.empty.

  (** ** Properties *)

  Lemma In_fold_left_memory_eq:
    forall x eqs m,
      PS.In x (List.fold_left memory_eq eqs m)
      <-> PS.In x (List.fold_left memory_eq eqs PS.empty) \/ PS.In x m.
  Proof.
    induction eqs as [|eq].
    - split; auto.
      destruct 1 as [H|].
      apply not_In_empty in H; contradiction.
      auto.
    - split.
      + intro H.
        simpl; rewrite IHeqs.
        simpl in H; apply IHeqs in H; destruct H; auto.
        destruct eq; auto.
        apply PS.add_spec in H.
        destruct H.
        rewrite H; left; right; apply PS.add_spec; intuition.
        intuition.
      + destruct 1 as [H|H].
        * simpl in H; rewrite IHeqs in H; apply IHeqs; destruct H; auto.
          right.
          destruct eq; try (apply not_In_empty in H; contradiction).
          simpl; apply PS.add_spec.
          apply PS.add_spec in H; destruct H;
          try apply not_In_empty in H; intuition.
        * apply IHeqs; right; destruct eq; auto.
          apply PS.add_spec; auto.
  Qed.

End MEMORIES.

Module MemoriesFun
       (Ids : IDS)
       (Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       <: MEMORIES Ids Op Syn.

  Include MEMORIES Ids Op Syn.
 
End MemoriesFun.

