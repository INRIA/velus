Require Import PArith.
Require Import List.

Import List.ListNotations.
Open Scope list_scope.

Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.Memories.

(** * Defined variables *)

(**

  The [Is_defined_in] predicate identifies the variables defined by a
  set of equations.

 *)

Module Type ISDEFINED
       (Ids : IDS)
       (Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (Import Mem : MEMORIES Ids Op Syn).

  Inductive Is_defined_in_eq : ident -> equation -> Prop :=
  | DefEqDef: forall x ck e,      Is_defined_in_eq x (EqDef x ck e)
  | DefEqApp: forall x ck f e ty, Is_defined_in_eq x (EqApp x ck f e ty)
  | DefEqFby: forall x ck v e,    Is_defined_in_eq x (EqFby x ck v e).

  (* definition is needed in signature *)
  Definition Is_defined_in_eqs (x: ident) (eqs: list equation) : Prop :=
    List.Exists (Is_defined_in_eq x) eqs.

  (** ** Properties *)

  Lemma Is_defined_in_eq_dec:
    forall x eq, {Is_defined_in_eq x eq}+{~Is_defined_in_eq x eq}.
  Proof.
    intros x eq.
    destruct eq as [y cae|y f lae|y v0 lae];
      (destruct (ident_eq_dec x y) as [xeqy|xneqy];
        [ rewrite xeqy; left; constructor
        | right; inversion 1; auto]).
  Qed.

  Lemma decidable_Is_defined_in_eqs:
    forall x eqs,
      Decidable.decidable (Is_defined_in_eqs x eqs).
  Proof.
    intros. apply decidable_Exists.
    intros eq Hin.
    destruct (Is_defined_in_eq_dec x eq); [left|right]; auto.
  Qed.

  Lemma Is_defined_in_cons:
    forall x eq eqs,
      Is_defined_in_eqs x (eq :: eqs) ->
      Is_defined_in_eq x eq
      \/ (~Is_defined_in_eq x eq /\ Is_defined_in_eqs x eqs).
  Proof.
    intros x eq eqs Hdef.
    apply List.Exists_cons in Hdef.
    destruct (Is_defined_in_eq_dec x eq); intuition.
  Qed.

  Lemma not_Is_defined_in_cons:
    forall x eq eqs,
      ~Is_defined_in_eqs x (eq :: eqs)
      <-> ~Is_defined_in_eq x eq /\ ~Is_defined_in_eqs x eqs.
  Proof.
    intros x eq eqs. split.
    intro H0; unfold Is_defined_in_eqs in H0; auto.
    destruct 1 as [H0 H1]; intro H; apply Is_defined_in_cons in H; intuition.
  Qed.

  Lemma not_Is_defined_in_eq_EqDef:
    forall x i ck ce,
      ~ Is_defined_in_eq x (EqDef i ck ce) -> x <> i.
  Proof.
    intros x i ck ce H0 xeqi.
    rewrite xeqi in H0.
    assert (Is_defined_in_eq i (EqDef i ck ce)) by constructor.
    contradiction.
  Qed.

  Lemma not_Is_defined_in_eq_EqApp:
    forall x i ck f le ty,
      ~ Is_defined_in_eq x (EqApp i ck f le ty) -> x <> i.
  Proof.
    intros x i ck f le ty H0 xeqi.
    rewrite xeqi in H0.
    assert (Is_defined_in_eq i (EqApp i ck f le ty)) by constructor.
    contradiction.
  Qed.

  Lemma not_Is_defined_in_eq_EqFby:
    forall x i ck v0 le,
      ~ Is_defined_in_eq x (EqFby i ck v0 le) -> x <> i.
  Proof.
    intros x i ck v0 le H0 xeqi.
    rewrite xeqi in H0.
    assert (Is_defined_in_eq i (EqFby i ck v0 le)) by constructor.
    contradiction.
  Qed.

  Lemma In_memory_eq_In_defined_eq_gen:
    forall x eq S,
      PS.In x (memory_eq S eq)
      -> Is_defined_in_eq x eq \/ PS.In x S.
  Proof.
    intros x eq S.
    destruct eq; simpl; intro HH; try intuition.
    apply PS.add_spec in HH; intuition.
    subst; left; constructor.
  Qed.

  Corollary In_memory_eq_Is_defined_eq:
    forall x eq,
      PS.In x (memory_eq PS.empty eq)
      -> Is_defined_in_eq x eq.
  Proof.
    intros.
    cut (Is_defined_in_eq x eq \/ PS.In x PS.empty).
    intro His_def; destruct His_def; auto; not_In_empty.
    apply In_memory_eq_In_defined_eq_gen; auto.
  Qed.

  Lemma Is_defined_in_memories:
    forall x eqs,
      PS.In x (memories eqs) -> Is_defined_in_eqs x eqs.
  Proof.
    unfold memories, Is_defined_in_eqs.
    induction eqs as [ eq | eq ].
    - simpl; intro; not_In_empty.
    - intro HH; simpl in HH.
      apply In_fold_left_memory_eq in HH.
      rewrite List.Exists_cons.
      destruct HH as [HH|HH].
      + right; now apply IHeqs with (1:=HH).
      + left. 
        apply In_memory_eq_Is_defined_eq in HH; auto.
  Qed.

  Lemma Is_defined_in_eqs_var_defined:
    forall x eq,
      Is_defined_in_eq x eq <-> var_defined eq = x.
  Proof.
    Hint Constructors Is_defined_in_eq.
    intros x eq.
    destruct eq; simpl;
      split; intro HH; subst; try inversion_clear HH; auto.
  Qed.

  Lemma Is_defined_in_var_defined:
    forall x eqs,
      Is_defined_in_eqs x eqs
      <-> In x (map var_defined eqs).
  Proof.
    induction eqs as [|eq eqs].
    now apply Exists_nil.
    split; intro HH.
    - inversion_clear HH as [? ? Hdef|? ? Hdef]; simpl; [left|right].
      + now apply Is_defined_in_eqs_var_defined in Hdef.
      + now apply IHeqs.
    - destruct HH as [Hdef|Hdef]; simpl; [left|right].
      + now apply Is_defined_in_eqs_var_defined in Hdef.
      + now apply IHeqs.
  Qed.
  
End ISDEFINED.

Module IsDefinedFun
       (Ids : IDS)
       (Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (Import Mem : MEMORIES Ids Op Syn)
       <: ISDEFINED Ids Op Syn Mem.

  Include ISDEFINED Ids Op Syn Mem.

End IsDefinedFun.

