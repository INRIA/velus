Require Import PArith.
Require Import List.

Import List.ListNotations.
Open Scope list_scope.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.NLustre.Syntax.
Require Import Velus.NLustre.IsVariable.
Require Import Velus.NLustre.IsDefined.
Require Import Velus.NLustre.Memories.

(** * Stack variables: decision procedure *)

(**

Decision procedure for the [IsVariable] predicate. We show that it is
equivalent to its specification.

 *)

Module Type DECIDE
       (Ids : IDS)
       (Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (Import Mem : MEMORIES Ids Op Syn)
       (Import IsD : ISDEFINED Ids Op Syn Mem)
       (Import IsV : ISVARIABLE Ids Op Syn Mem IsD).

  Fixpoint variable_eq (vars: PS.t) (eq: equation) {struct eq} : PS.t :=
    match eq with
    | EqDef x _ _   => PS.add x vars
    | EqApp xs _ _ _ => ps_adds xs vars
    | EqFby _ _ _ _ => vars
    end.

  Definition variables (eqs: list equation) : PS.t :=
    List.fold_left variable_eq eqs PS.empty.

  (** ** Properties *)

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
      first [
          simpl in H; apply IHeqs in H; destruct H;
          [ intuition
          | destruct eq;
            match goal with
            | |- context[ EqApp _ _ _ _ ] =>
              generalize ps_adds_spec; intro add_spec
            | _ =>
              generalize PS.add_spec; intro add_spec
            end;
            try (apply add_spec in H; destruct H);
            match goal with
            | H:x=_ |- _ => rewrite H; simpl; rewrite add_spec; intuition
            | H: In x ?i |- context [EqApp ?i _ _ _] => simpl; rewrite add_spec; intuition
            | _ => apply not_In_empty in H; contradiction
            | _ => intuition
            end ]
        | now
            right; destruct eq;
            match goal with
            | |- context[ EqApp _ _ _ _ ] =>
              generalize ps_adds_spec; intro add_spec
            | _ =>
              generalize PS.add_spec; intro add_spec
            end; try apply add_spec; intuition
        ].
  Qed.


  (* tactic definition needed in signature *)
  Ltac not_Is_variable x y :=
    match goal with
    | H: ~ Is_variable_in_eq x (EqDef y _ _) |- _ =>
      apply not_Is_variable_in_EqDef in H
    | H: ~ Is_variable_in_eq x (EqApp y _ _ _) |- _ =>
      apply not_Is_variable_in_EqApp in H
    end.

  Lemma Is_variable_in_eq_dec:
    forall x eq, {Is_variable_in_eq x eq}+{~Is_variable_in_eq x eq}.
  Proof.
    intros x eq.
    destruct eq as [y cae|y f lae|y v0 lae];
      try match goal with
      | |- context Is_variable_in_eq [EqFby _ _ _ _] =>
        right; inversion 1
      | |- context Is_variable_in_eq [EqApp _ _ _ _] =>
        edestruct in_dec as [ Hin_xy | Hnin_xy ];
          [ now apply ident_eq_dec
          | now constructor(constructor(eauto))
          | now right; intro; inversion 0; eauto]
      | _ =>
        destruct (ident_eq_dec x y) as [xeqy|xneqy];
          [ rewrite xeqy; left; constructor
          | right; inversion 1; auto]
      end.
  Qed.



  Lemma Is_variable_in_cons:
    forall x eq eqs,
      Is_variable_in_eqs x (eq :: eqs) ->
      Is_variable_in_eq x eq
      \/ (~Is_variable_in_eq x eq /\ Is_variable_in_eqs x eqs).
  Proof.
    intros x eq eqs Hdef.
    apply List.Exists_cons in Hdef.
    destruct (Is_variable_in_eq_dec x eq); intuition.
  Qed.

  Lemma not_Is_variable_in_cons:
    forall x eq eqs,
      ~Is_variable_in_eqs x (eq :: eqs)
      <-> ~Is_variable_in_eq x eq /\ ~Is_variable_in_eqs x eqs.
  Proof.
    intros x eq eqs. split.
    intro H0; unfold Is_variable_in_eqs in H0; auto.
    destruct 1 as [H0 H1]; intro H; apply Is_variable_in_cons in H; intuition.
  Qed.




  Lemma Is_variable_in_variables:
    forall x eqs,
      PS.In x (variables eqs)
      <-> Is_variable_in_eqs x eqs.
  Proof.
    unfold variables, Is_variable_in_eqs.
    induction eqs as [ eq | eq ].
    - rewrite List.Exists_nil; split; intro H;
      try apply not_In_empty in H; contradiction.
    - simpl.
      rewrite In_fold_left_variable_eq.
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
          try (apply not_In_empty in H; intuition);
          (simpl in H; apply add_spec in H; destruct H;
           [ try rewrite H; left; constructor; auto
           | apply not_In_empty in H; contradiction ]).
      + intro H; apply List.Exists_cons in H; destruct H.
        destruct eq;
          match goal with
          | |- context[ EqApp _ _ _ _ ] =>
            generalize ps_adds_spec; intro add_spec
          | _ =>
            generalize PS.add_spec; intro add_spec
          end; try inversion H;
            (right; apply add_spec; intuition).
        left; apply IHeqs; apply H.
  Qed.

  Lemma Is_variable_in_dec:
    forall x eqs, {Is_variable_in_eqs x eqs}+{~Is_variable_in_eqs x eqs}.
  Proof.
    intros x eqs.
    apply Bool.reflect_dec with (b := PS.mem x (variables eqs)).
    apply Bool.iff_reflect.
    rewrite PS.mem_spec.
    symmetry.
    apply Is_variable_in_variables.
  Qed.

  Lemma variable_eq_empty:
    forall x eq variables,
      PS.In x (variable_eq variables eq)
      <-> PS.In x (variable_eq PS.empty eq) \/ PS.In x variables.
  Proof.
    split; intro H.
    destruct eq;
      match goal with
      | |- context[ EqApp _ _ _ _ ] =>
        generalize ps_adds_spec; intro add_spec
      | _ =>
        generalize PS.add_spec; intro add_spec
      end;
      simpl in *;
        try (apply add_spec in H; destruct H; [try subst i|]);
        try (rewrite add_spec; auto).
        intuition.
    destruct eq eqn:Heq; simpl in *; destruct H;
      match goal with
      | _ : _ = EqApp _ _ _ _ |- _ =>
        generalize ps_adds_spec; intro add_spec
      | _ =>
        generalize PS.add_spec; intro add_spec
      end;
      try (apply add_spec in H; destruct H); try apply PS.empty_spec in H;
        try (rewrite ps_adds_spec; auto);
        intuition.
  Qed.

End DECIDE.

Module DecideFun
       (Ids : IDS)
       (Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (Import Mem : MEMORIES Ids Op Syn)
       (Import IsD : ISDEFINED Ids Op Syn Mem)
       (Import IsV : ISVARIABLE Ids Op Syn Mem IsD)
       <: DECIDE Ids Op Syn Mem IsD IsV.
  Include DECIDE Ids Op Syn Mem IsD IsV.
End DecideFun.
