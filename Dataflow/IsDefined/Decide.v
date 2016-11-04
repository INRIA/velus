Require Import PArith.
Require Import List.

Import List.ListNotations.
Open Scope list_scope.

Require Import Rustre.Common.
Require Import Rustre.Operators.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.IsDefined.
Require Import Rustre.Dataflow.Memories.

(** * Defined variables : decision procedure *)

(**

Decision procedure for the [Is_defined_in] predicate. We show that it
is equivalent to its specification.

Remark: This development is not formally part of the correctness proof.

 *)

Module Type DECIDE
       (Ids : IDS)
       (Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (Import Mem : MEMORIES Ids Op Syn)
       (Import IsD : ISDEFINED Ids Op Syn Mem).

  Fixpoint defined_eq (defs: PS.t) (eq: equation) {struct eq} : PS.t :=
    match eq with
    | EqDef x _ _   => PS.add x defs
    | EqApp xs _ _ _ => ps_adds xs defs
    | EqFby x _ _ _ => PS.add x defs
    end.

  Definition defined (eqs: list equation) : PS.t :=
    List.fold_left defined_eq eqs PS.empty.


  (** ** Properties *)

  Lemma In_fold_left_defined_eq:
    forall x eqs m,
      PS.In x (List.fold_left defined_eq eqs m)
      <-> PS.In x (List.fold_left defined_eq eqs PS.empty) \/ PS.In x m.
  Proof.
    induction eqs as [|eq].
    - split; auto.
      destruct 1 as [H|].
      apply not_In_empty in H; contradiction.
      auto.
    - split.
      + intro H.
        simpl; rewrite IHeqs.
        simpl in H; apply IHeqs in H; destruct H; auto;
        destruct eq;
        (* XXX: this is Ltac p0rn *)
        match goal with
        | |- context[ EqApp _ _ _ _ ] => generalize ps_adds_spec; intro add_spec
        | _ => generalize PS.add_spec; intro add_spec
        end;
        apply add_spec in H;
        destruct H;
        match goal with
        | H: PS.In x ?m |- context [PS.In x ?m] => now intuition
        | H: x = _ |- _ => subst x
        | H: In x ?i |- context [EqApp ?i _ _ _] => idtac
        end;
        constructor(constructor(apply add_spec; intuition)).

      + destruct 1 as [H|H].
        * simpl in H; rewrite IHeqs in H; apply IHeqs; destruct H; auto.
          right.
          destruct eq;
            match goal with
            | |- context[ EqApp _ _ _ _ ] =>
              generalize ps_adds_spec; intro add_spec
            | _ =>
              generalize PS.add_spec; intro add_spec
            end;
            simpl; apply add_spec;
            apply add_spec in H; destruct H;
            intuition;
            apply not_In_empty in H; contradiction.
        * apply IHeqs; right; destruct eq;
            match goal with
            | |- context[ EqApp _ _ _ _ ] =>
              generalize ps_adds_spec; intro add_spec
            | _ =>
              generalize PS.add_spec; intro add_spec
            end;
            apply add_spec; auto.
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
      rewrite In_fold_left_defined_eq.
      split.
      + rewrite List.Exists_cons.
        destruct 1. intuition.
        destruct eq;
          match goal with
          | |- context[ EqApp _ _ _ _ ] =>
            generalize ps_adds_spec; intro add_spec
          | _ =>
            generalize PS.add_spec; intro add_spec
          end;
          (simpl in H; apply add_spec in H; destruct H;
           [ try rewrite H; left; constructor; auto
           | apply not_In_empty in H; contradiction]).
      + intro H; apply List.Exists_cons in H; destruct H.
        inversion H; destruct eq;
          match goal with
          | |- context[ EqApp _ _ _ _ ] =>
            generalize ps_adds_spec; intro add_spec
          | _ =>
            generalize PS.add_spec; intro add_spec
          end;
          (right; apply add_spec; intuition).
        left; apply IHeqs; apply H.
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

  Lemma In_memory_eq_In_defined_eq:
    forall x eq S,
      PS.In x (memory_eq S eq)
      -> PS.In x (defined_eq S eq).
  Proof.
    intros x eq S HH.
    destruct eq;
      match goal with
      | |- context[ EqApp _ _ _ _ ] =>
        generalize ps_adds_spec; intro add_spec
      | _ =>
        generalize PS.add_spec; intro add_spec
      end;
      try (apply add_spec; now intuition).
    apply add_spec in HH.
    destruct HH as [HH|HH].
    - rewrite HH; apply add_spec; left; reflexivity.
    - apply add_spec; right; exact HH.
  Qed.

  Lemma In_fold_left_memory_eq_defined_eq:
    forall x eqs S,
      PS.In x (List.fold_left memory_eq eqs S)
      -> PS.In x (List.fold_left defined_eq eqs S).
  Proof.
    intros x eqs.
    induction eqs as [|eq eqs IH]; [now intuition|].
    intros S HH.
    apply IH in HH; clear IH.
    apply In_fold_left_defined_eq in HH.
    simpl. apply In_fold_left_defined_eq.
    destruct HH as [HH|HH].
    - left; exact HH.
    - right; now apply In_memory_eq_In_defined_eq with (1:=HH).
  Qed.

End DECIDE.

Module Decide
       (Ids : IDS)
       (Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (Import Mem : MEMORIES Ids Op Syn)
       (Import IsD : ISDEFINED Ids Op Syn Mem)
       <: DECIDE Ids Op Syn Mem IsD.

  Include DECIDE Ids Op Syn Mem IsD.

End Decide.