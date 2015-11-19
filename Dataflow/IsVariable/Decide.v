Require Import PArith.
Require Import List.

Import List.ListNotations.
Open Scope list_scope.

Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.IsVariable.

(** 

Decision procedure for the [IsVariable] predicate. We show that it is
equivalent to its specification.

Remark: This development is used once in the correctness proof, it is
not clear (to me) whether it is necessary.

 *)


Fixpoint variable_eq (vars: PS.t) (eq: equation) {struct eq} : PS.t :=
  match eq with
  | EqDef x _   => PS.add x vars
  | EqApp x _ _ => PS.add x vars
  | EqFby _ _ _ => vars
  end.

Definition variables (eqs: list equation) : PS.t :=
  List.fold_left variable_eq eqs PS.empty.


Lemma In_fold_left_variable_eq:
  forall x eqs m,
    PS.In x (List.fold_left variable_eq eqs m)
    <-> PS.In x (List.fold_left variable_eq eqs PS.empty) \/ PS.In x m.
Proof. (* TODO: There must be a way to get auto to do all of this? *)
  induction eqs as [|eq].
  - split; auto.
    destruct 1 as [H|].
    apply not_In_empty in H; contradiction.
    auto.
  - split; [ intro H; simpl; rewrite IHeqs
           | destruct 1 as [H|H]; apply IHeqs];
    solve [
        simpl in H; apply IHeqs in H; destruct H;
        [ intuition
        | destruct eq; try (apply PS.add_spec in H; destruct H);
          match goal with
          | H:x=_ |- _ => rewrite H; simpl; rewrite PS.add_spec; intuition
          | _ => apply not_In_empty in H; contradiction
          | _ => intuition
          end ]
      | right; destruct eq; try apply PS.add_spec; intuition
      ].
Qed.

Lemma Is_variable_in_variables:
  forall x eqs,
    PS.In x (variables eqs)
    <-> Is_variable_in x eqs.
Proof.
  unfold variables, Is_variable_in.
  induction eqs as [ eq | eq ].
  - rewrite List.Exists_nil; split; intro H;
    try apply not_In_empty in H; contradiction.
  - simpl.
    rewrite In_fold_left_variable_eq.
    split.
    + rewrite List.Exists_cons.
      destruct 1. intuition.
      destruct eq; try (apply not_In_empty in H; intuition);
      (simpl in H; apply PS.add_spec in H; destruct H;
       [ rewrite H; left; constructor
       | apply not_In_empty in H; contradiction ]).
    + intro H; apply List.Exists_cons in H; destruct H.
      destruct eq; try inversion H;
      (right; apply PS.add_spec; intuition).
      left; apply IHeqs; apply H.
Qed.

Lemma Is_variable_in_dec:
  forall x eqs, {Is_variable_in x eqs}+{~Is_variable_in x eqs}.
Proof.
  intros x eqs.
  apply Bool.reflect_dec with (b := PS.mem x (variables eqs)).
  apply Bool.iff_reflect.
  rewrite PS.mem_spec.
  symmetry.
  apply Is_variable_in_variables.
Qed.

