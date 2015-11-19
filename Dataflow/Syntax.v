Require Import Rustre.Common.
Require Import PArith.

Import List.ListNotations.
Open Scope list_scope.

(** * Dataflow language *)

Inductive clock : Set :=
| Cbase : clock                          (* base clock *)
| Con : clock -> ident -> bool -> clock. (* subclock *)

Implicit Type ck : clock.

(** ** Syntax *)

Inductive lexp : Type :=
  | Econst : const -> lexp
  | Evar : ident -> lexp
  | Ewhen : lexp -> ident -> bool -> lexp.
(* External operators are missing *)

Inductive laexp : Type :=
  | LAexp : clock -> lexp -> laexp.

Implicit Type le: lexp.
Implicit Type lae: laexp.

Inductive cexp : Type :=
  | Emerge : ident -> cexp -> cexp -> cexp 
  | Eexp : lexp -> cexp.

Inductive caexp : Type :=
  | CAexp : clock -> cexp -> caexp.

Implicit Type ce: cexp.
Implicit Type cae: caexp.

(** ** Equations *)

Inductive equation : Type :=
  | EqDef : ident -> caexp -> equation
  | EqApp : ident -> ident -> laexp -> equation
  | EqFby : ident -> const -> laexp -> equation.

Implicit Type eqn: equation.

(** ** Node *)

Record node : Type := mk_node {
  n_name : ident;
  n_input : ident;
  n_output : ident;
  n_eqs : list equation }.

Implicit Type N: node.

(** ** Program *)

Definition global := list node.

Implicit Type G: global.


Definition find_node (f : ident) : global -> option node :=
  List.find (fun n=> ident_eqb n.(n_name) f).




Fixpoint memory_eq (mems: PS.t) (eq: equation) {struct eq} : PS.t :=
  match eq with
  | EqFby x _ _ => PS.add x mems
  | _ => mems
  end.

Definition memories (eqs: list equation) : PS.t :=
  List.fold_left memory_eq eqs PS.empty.

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


Fixpoint defined_eq (defs: PS.t) (eq: equation) {struct eq} : PS.t :=
  match eq with
  | EqDef x _   => PS.add x defs
  | EqApp x _ _ => PS.add x defs
  | EqFby x _ _ => PS.add x defs
  end.

Definition defined (eqs: list equation) : PS.t :=
  List.fold_left defined_eq eqs PS.empty.

Inductive Is_defined_in_eq : ident -> equation -> Prop :=
| DefEqDef: forall x e,   Is_defined_in_eq x (EqDef x e)
| DefEqApp: forall x f e, Is_defined_in_eq x (EqApp x f e)
| DefEqFby: forall x v e, Is_defined_in_eq x (EqFby x v e).

Definition Is_defined_in (x: ident) (eqs: list equation) : Prop :=
  List.Exists (Is_defined_in_eq x) eqs.

Lemma Is_defined_in_eq_dec:
  forall x eq, {Is_defined_in_eq x eq}+{~Is_defined_in_eq x eq}.
Proof.
  intros x eq.
  destruct eq as [y cae|y f lae|y v0 lae];
    (destruct (ident_eq_dec x y) as [xeqy|xneqy];
     [ rewrite xeqy; left; constructor
     | right; inversion 1; auto]).
Qed.

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
    <-> Is_defined_in x eqs.
Proof.
  unfold defined, Is_defined_in.
  induction eqs as [ | eq ].
  - rewrite List.Exists_nil; split; intro H;
    try apply not_In_empty in H; contradiction.
  - simpl.
    rewrite In_fold_left_defined_eq.
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

Lemma Is_defined_in_dec:
  forall x eqs, {Is_defined_in x eqs}+{~Is_defined_in x eqs}.
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
  destruct eq; try (apply PS.add_spec; now intuition).
  apply PS.add_spec in HH.
  destruct HH as [HH|HH].
  - rewrite HH; apply PS.add_spec; left; reflexivity.
  - apply PS.add_spec; right; exact HH.
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

Lemma Is_defined_in_cons:
  forall x eq eqs,
    Is_defined_in x (eq :: eqs) ->
    Is_defined_in_eq x eq
    \/ (~Is_defined_in_eq x eq /\ Is_defined_in x eqs).
Proof.
  intros x eq eqs Hdef.
  apply List.Exists_cons in Hdef.
  destruct (Is_defined_in_eq_dec x eq); intuition.
Qed.

Lemma not_Is_defined_in_cons:
  forall x eq eqs,
    ~Is_defined_in x (eq :: eqs)
    <-> ~Is_defined_in_eq x eq /\ ~Is_defined_in x eqs.
Proof.
  intros x eq eqs. split.
  intro H0; unfold Is_defined_in in H0; auto.
  destruct 1 as [H0 H1]; intro H; apply Is_defined_in_cons in H; intuition.
Qed.

Lemma not_Is_defined_in_eq_EqDef:
  forall x i cae,
    ~ Is_defined_in_eq x (EqDef i cae) -> x <> i.
Proof.
  intros x i cae H0 xeqi.
  rewrite xeqi in H0.
  assert (Is_defined_in_eq i (EqDef i cae)) by constructor.
  contradiction.
Qed.

Lemma not_Is_defined_in_eq_EqApp:
  forall x i f lae,
    ~ Is_defined_in_eq x (EqApp i f lae) -> x <> i.
Proof.
  intros x i f lae H0 xeqi.
  rewrite xeqi in H0.
  assert (Is_defined_in_eq i (EqApp i f lae)) by constructor.
  contradiction.
Qed.

Lemma not_Is_defined_in_eq_EqFby:
  forall x i v0 lae,
    ~ Is_defined_in_eq x (EqFby i v0 lae) -> x <> i.
Proof.
  intros x i v0 lae H0 xeqi.
  rewrite xeqi in H0.
  assert (Is_defined_in_eq i (EqFby i v0 lae)) by constructor.
  contradiction.
Qed.


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

