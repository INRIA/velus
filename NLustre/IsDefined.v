Require Import PArith.
Require Import List.

Import List.ListNotations.
Open Scope list_scope.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.NLustre.Syntax.
Require Import Velus.NLustre.Memories.

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

  (** ** Logical predicates: *)

  Inductive Is_defined_in_eq : ident -> equation -> Prop :=
  | DefEqDef: forall x ck e,   Is_defined_in_eq x (EqDef x ck e)
  | DefEqApp: forall x xs ck f e, List.In x xs -> Is_defined_in_eq x (EqApp xs ck f e)
  | DefEqFby: forall x ck v e, Is_defined_in_eq x (EqFby x ck v e).

  (* definition is needed in signature *)
  Definition Is_defined_in_eqs (x: ident) (eqs: list equation) : Prop :=
    List.Exists (Is_defined_in_eq x) eqs.


  (** ** Properties *)

  Hint Constructors Is_defined_in_eq.

  Lemma not_Is_defined_in_eq_EqDef:
    forall x i ck ce,
      ~ Is_defined_in_eq x (EqDef i ck ce) -> x <> i.
  Proof.
    intros x i ck ce H0 xeqi.
    rewrite xeqi in H0.
    assert (Is_defined_in_eq i (EqDef i ck ce)) by auto.
    contradiction.
  Qed.

  Lemma not_Is_defined_in_eq_EqApp:
    forall x ys ck f le,
      ~ Is_defined_in_eq x (EqApp ys ck f le) -> ~ List.In x ys.
  Proof.
    intros ** H.
    assert (Is_defined_in_eq x (EqApp ys ck f le)) by eauto.
    contradiction.
  Qed.

  Lemma not_Is_defined_in_eq_EqFby:
    forall x i ck v0 le,
      ~ Is_defined_in_eq x (EqFby i ck v0 le) -> x <> i.
  Proof.
    intros x i ck v0 le H0 xeqi.
    rewrite xeqi in H0.
    assert (Is_defined_in_eq i (EqFby i ck v0 le)) by auto.
    contradiction.
  Qed.

  Lemma not_Is_defined_in_cons:
    forall x eq eqs,
      ~Is_defined_in_eqs x (eq :: eqs)
      <-> ~Is_defined_in_eq x eq /\ ~Is_defined_in_eqs x eqs.
  Proof.
    intros x eq eqs. split.
    - (* ==> *)
      intro Hndef; split; intro His_def;
        eapply Hndef; constructor(assumption).
    - (* <== *)
      intros [Hdef_eq Hdef_eqs] Hdef_all.
      inv Hdef_all; eauto.
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

  Lemma In_EqFby_Is_defined_in_eqs:
    forall x ck c0 e eqs,
      In (EqFby x ck c0 e) eqs ->
      Is_defined_in_eqs x eqs.
  Proof.
    induction eqs; inversion_clear 1; subst.
    now repeat constructor.
    constructor 2; intuition.
  Qed.

  Lemma Is_defined_in_vars_defined:
    forall x eqs,
      Is_defined_in_eqs x eqs ->
      In x (vars_defined eqs).
  Proof.
    induction eqs as [|eq eqs]; inversion_clear 1;
      unfold vars_defined; rewrite concatMap_cons; apply in_app.
    - left. inv H0; simpl; auto.
    - intuition.
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
