Require Import PArith.
Require Import List.

Import List.ListNotations.
Open Scope list_scope.

Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.IsDefined.
Require Import Rustre.Dataflow.Memories.


(** * Stack variables *)

(**

  The [Is_variable] predicate identifies those variables that will
  stay on the stack after compilation, ie. anything not defined by an
  [fby].

 *)

Module Type ISVARIABLE
       (Op : OPERATORS)
       (Import Syn : SYNTAX Op)
       (Import Mem : MEMORIES Op Syn)
       (Import IsD : ISDEFINED Op Syn Mem).

  Inductive Is_variable_in_eq : ident -> equation -> Prop :=
  | VarEqDef: forall x ck e,   Is_variable_in_eq x (EqDef x ck e)
  | VarEqApp: forall x ck f e, Is_variable_in_eq x (EqApp x ck f e).

  Definition Is_variable_in_eqs (x: ident) (eqs: list equation) : Prop :=
    List.Exists (Is_variable_in_eq x) eqs.

  (** ** Properties *)

  Lemma not_Is_variable_in_EqDef: 
    forall x ck y e,
      ~ Is_variable_in_eq x (EqDef y ck e) -> x <> y.
  Proof.
    Hint Constructors Is_variable_in_eq. 
    intros ** Hxy. subst x. auto.
  Qed.

  Lemma not_Is_variable_in_EqApp: 
    forall x y ck f e,
      ~ Is_variable_in_eq x (EqApp y ck f e) -> x <> y.
  Proof.
    Hint Constructors Is_variable_in_eq. 
    intros ** Hxy. subst x. auto.
  Qed.

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
      match goal with
      | |- context Is_variable_in_eq [EqFby _ _ _ _] => right; inversion 1
      | _ => (destruct (ident_eq_dec x y) as [xeqy|xneqy];
              [ rewrite xeqy; left; constructor
              | right; inversion 1; auto])
      end.
  Qed.

  Lemma Is_variable_in_eqs_Is_defined_in_eqs:
    forall x eqs,
      Is_variable_in_eqs x eqs
      -> Is_defined_in_eqs x eqs.
  Proof.
    induction eqs as [|eq eqs IH]; [now inversion 1|].
    inversion_clear 1 as [Hin ? Hivi|]; [|constructor 2; intuition].
    destruct eq; inversion_clear Hivi; repeat constructor.
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

  Lemma not_Is_defined_in_eq_not_Is_variable_in_eq:
    forall x eq, ~Is_defined_in_eq x eq -> ~Is_variable_in_eq x eq.
  Proof.
    Hint Constructors Is_defined_in_eq.
    intros x eq Hnidi.
    destruct eq; inversion 1; subst; intuition.
  Qed.

  Lemma not_Is_defined_in_not_Is_variable_in:
    forall x eqs, ~Is_defined_in_eqs x eqs -> ~Is_variable_in_eqs x eqs.
  Proof.
    Hint Constructors Is_defined_in_eq.
    induction eqs as [|eq].
    - intro H; contradict H; inversion H.
    - intro H; apply not_Is_defined_in_cons in H; destruct H as [H0 H1].
      apply IHeqs in H1; apply not_Is_variable_in_cons.
      split; [ now apply not_Is_defined_in_eq_not_Is_variable_in_eq
             | now apply H1].
  Qed.

End ISVARIABLE.