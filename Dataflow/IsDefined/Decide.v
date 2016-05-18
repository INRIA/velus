Require Import PArith.
Require Import List.

Import List.ListNotations.
Open Scope list_scope.

Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.IsDefined.
Require Import Rustre.Dataflow.Memories.

(** * Defined variables : decision procedure *)

(**

Decision procedure for the [Is_defined_in] predicate. We show that it
is equivalent to its specification.

Remark: This development is not formally part of the correctness proof.

 *)

Definition defined_eq (eq: equation) : ident :=
  match eq with
  | EqDef x _ _   => x
  | EqApp x _ _ _ => x
  | EqFby x _ _ _ => x
  end.

Definition add_defined_eq (defs: PS.t) (eq: equation) : PS.t :=
  PS.add (defined_eq eq) defs.

Definition defined (eqs: list equation) : PS.t :=
  List.fold_left add_defined_eq eqs PS.empty.

(** ** Properties *)

Lemma defined_eq_Is_defined_in:
  forall x eq, defined_eq eq = x <-> Is_defined_in_eq x eq.
Proof.
  destruct eq;
  (split; intro H; [subst x; constructor|inversion_clear H; reflexivity]).
Qed.

Lemma In_fold_left_add_defined_eq:
  forall x eqs m,
    PS.In x (List.fold_left add_defined_eq eqs m)
    <-> PS.In x (List.fold_left add_defined_eq eqs PS.empty) \/ PS.In x m.
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
      destruct eq;
      apply PS.add_spec in H;
      destruct H;
      try (rewrite H; left; right; apply PS.add_spec); intuition.
    + destruct 1 as [H|H].
      * simpl in H; rewrite IHeqs in H; apply IHeqs; destruct H; auto.
        right.
        destruct eq;
        simpl; apply PS.add_spec;
        apply PS.add_spec in H; destruct H;
        intuition;
        apply not_In_empty in H; contradiction.
      * apply IHeqs; right; destruct eq;
        apply PS.add_spec; auto.
Qed.

Lemma Is_defined_in_defined:
  forall x eqs,
    PS.In x (defined eqs)
    <-> Is_defined_in_eqs x eqs.
Proof.
  unfold defined, Is_defined_in_eqs.
  induction eqs as [ | eq ].
  - rewrite List.Exists_nil; split; intro H;
    try apply not_In_empty in H; contradiction.
  - simpl.
    rewrite In_fold_left_add_defined_eq.
    split.
    + rewrite List.Exists_cons.
      destruct 1. intuition.
      destruct eq;
      (simpl in H; apply PS.add_spec in H; destruct H;
       [ rewrite H; left; constructor
       | apply not_In_empty in H; contradiction]).
    + intro H; apply List.Exists_cons in H; destruct H.
      inversion H; destruct eq; (right; apply PS.add_spec; intuition).
      left; apply IHeqs; apply H.
Qed.

Lemma Is_defined_in_eq_dec:
  forall x eq, {Is_defined_in_eq x eq}+{~Is_defined_in_eq x eq}.
Proof.
  intros x eq.
  apply Bool.reflect_dec with (b := ident_eqb (defined_eq eq) x).
  apply Bool.iff_reflect.
  rewrite ident_eqb_eq.
  symmetry.
  apply defined_eq_Is_defined_in.
Qed.

Lemma Is_defined_in_dec:
  forall x eqs, {Is_defined_in_eqs x eqs}+{~Is_defined_in_eqs x eqs}.
Proof.
  intros x eqs.
  apply Bool.reflect_dec with (b := PS.mem x (defined eqs)).
  apply Bool.iff_reflect.
  rewrite PS.mem_spec.
  symmetry.
  apply Is_defined_in_defined.
Qed.

