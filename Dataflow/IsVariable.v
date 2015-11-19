Require Import PArith.
Require Import List.

Import List.ListNotations.
Open Scope list_scope.

Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.

(**
  The [Is_variable] predicate identifies those variables that will
  stay on the stack after compilation, ie. anything not defined by an
  [fby].

 *)

Fixpoint variable_eq (vars: PS.t) (eq: equation) {struct eq} : PS.t :=
  match eq with
  | EqDef x _   => PS.add x vars
  | EqApp x _ _ => PS.add x vars
  | EqFby _ _ _ => vars
  end.

Definition variables (eqs: list equation) : PS.t :=
  List.fold_left variable_eq eqs PS.empty.

Inductive Is_variable_in_eq : ident -> equation -> Prop :=
| VarEqDef: forall x e,   Is_variable_in_eq x (EqDef x e)
| VarEqApp: forall x f e, Is_variable_in_eq x (EqApp x f e).

Definition Is_variable_in (x: ident) (eqs: list equation) : Prop :=
  List.Exists (Is_variable_in_eq x) eqs.

Lemma Is_variable_in_eq_dec:
  forall x eq, {Is_variable_in_eq x eq}+{~Is_variable_in_eq x eq}.
Proof.
  intros x eq.
  destruct eq as [y cae|y f lae|y v0 lae];
    match goal with
    | |- context Is_variable_in_eq [EqFby _ _ _] => right; inversion 1
    | _ => (destruct (ident_eq_dec x y) as [xeqy|xneqy];
            [ rewrite xeqy; left; constructor
            | right; inversion 1; auto])
    end.
Qed.

Lemma Is_variable_in_Is_defined_in:
  forall x eqs,
    Is_variable_in x eqs
    -> Is_defined_in x eqs.
Proof.
  induction eqs as [|eq eqs IH]; [now inversion 1|].
  inversion_clear 1 as [Hin ? Hivi|]; [|constructor 2; intuition].
  destruct eq; inversion_clear Hivi; repeat constructor.
Qed.

Lemma Is_variable_in_cons:
  forall x eq eqs,
    Is_variable_in x (eq :: eqs) ->
    Is_variable_in_eq x eq
    \/ (~Is_variable_in_eq x eq /\ Is_variable_in x eqs).
Proof.
  intros x eq eqs Hdef.
  apply List.Exists_cons in Hdef.
  destruct (Is_variable_in_eq_dec x eq); intuition.
Qed.

Lemma not_Is_variable_in_cons:
  forall x eq eqs,
    ~Is_variable_in x (eq :: eqs)
    <-> ~Is_variable_in_eq x eq /\ ~Is_variable_in x eqs.
Proof.
  intros x eq eqs. split.
  intro H0; unfold Is_variable_in in H0; auto.
  destruct 1 as [H0 H1]; intro H; apply Is_variable_in_cons in H; intuition.
Qed.

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

Lemma not_Is_defined_in_eq_not_Is_variable_in_eq:
  forall x eq, ~Is_defined_in_eq x eq -> ~Is_variable_in_eq x eq.
Proof.
  Hint Constructors Is_defined_in_eq.
  intros x eq Hnidi.
  destruct eq; inversion 1; subst; intuition.
Qed.

Lemma not_Is_defined_in_not_Is_variable_in:
  forall x eqs, ~Is_defined_in x eqs -> ~Is_variable_in x eqs.
Proof.
  Hint Constructors Is_defined_in_eq.
  induction eqs as [|eq].
  - intro H; contradict H; inversion H.
  - intro H; apply not_Is_defined_in_cons in H; destruct H as [H0 H1].
    apply IHeqs in H1; apply not_Is_variable_in_cons.
    split; [ now apply not_Is_defined_in_eq_not_Is_variable_in_eq
           | now apply H1].
Qed.

Lemma Is_defined_in_memories:
  forall x eqs,
    PS.In x (memories eqs) -> Is_defined_in x eqs.
Proof.
  unfold memories, Is_defined_in.
  induction eqs as [ eq | eq ].
  - simpl; intro; not_In_empty.
  - intro HH; simpl in HH.
    apply In_fold_left_memory_eq in HH.
    rewrite List.Exists_cons.
    destruct HH as [HH|HH].
    + right; now apply IHeqs with (1:=HH).
    + left. apply In_memory_eq_In_defined_eq in HH.
      destruct eq; apply PS.add_spec in HH; destruct HH as [HH|HH];
      (rewrite HH; now constructor) || not_In_empty.
Qed.
