From Coq Require Import PArith.
From Coq Require Import List.

Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.Memories.

From Coq Require Import Sorting.Permutation.

(** * Stack variables *)

(**

  The [Is_variable] predicate identifies those variables that will
  stay on the stack after compilation, ie. anything not defined by an
  [fby].

 *)

Module Type ISVARIABLE
       (Ids          : IDS)
       (Op           : OPERATORS)
       (OpAux        : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Import Syn   : NLSYNTAX      Ids Op OpAux Cks CESyn)
       (Import Mem   : MEMORIES      Ids Op OpAux Cks CESyn Syn)
       (Import IsD   : ISDEFINED     Ids Op OpAux Cks CESyn Syn Mem).

  Inductive Is_variable_in_eq : ident -> equation -> Prop :=
  | VarEqDef: forall x ck e,   Is_variable_in_eq x (EqDef x ck e)
  | VarEqApp: forall x xs ck f e r, In x xs -> Is_variable_in_eq x (EqApp xs ck f e r).

  (* definition is needed in signature *)
  Definition Is_variable_in (x: ident) (eqs: list equation) : Prop :=
    List.Exists (Is_variable_in_eq x) eqs.

  Global Hint Constructors Is_variable_in_eq : nldef.

  (** ** Properties *)

  Lemma not_Is_variable_in_EqDef:
    forall x ck y e,
      ~ Is_variable_in_eq x (EqDef y ck e) -> x <> y.
  Proof.
    intros ** Hxy. subst x. auto with nldef.
  Qed.

  Lemma not_Is_variable_in_EqApp:
    forall x ys ck f e r,
      ~ Is_variable_in_eq x (EqApp ys ck f e r) -> ~ List.In x ys.
  Proof. eauto with nldef. Qed.


  Lemma Is_variable_in_eq_Is_defined_in_eq:
    forall x eq,
      Is_variable_in_eq x eq
      -> Is_defined_in_eq (Var x) eq.
  Proof.
    destruct eq; inversion_clear 1; auto with nldef.
  Qed.

  Lemma Is_variable_in_Is_defined_in:
    forall x eqs,
      Is_variable_in x eqs
      -> Is_defined_in (Var x) eqs.
  Proof.
    unfold Is_variable_in, Is_defined_in.
    intros * Var.
    solve_Exists. inv Var; now constructor.
  Qed.

  Global Hint Resolve Is_variable_in_eq_Is_defined_in_eq Is_variable_in_Is_defined_in : nldef.

  Lemma not_Is_defined_in_eq_not_Is_variable_in_eq:
    forall x eq, ~Is_defined_in_eq (Var x) eq -> ~Is_variable_in_eq x eq.
  Proof.
    intros * Hnidi.
    contradict Hnidi; eauto with nldef.
  Qed.

  Lemma not_Is_defined_in_not_Is_variable_in:
    forall x eqs, ~Is_defined_in (Var x) eqs -> ~Is_variable_in x eqs.
  Proof.
    intros * Hnidi.
    contradict Hnidi; eauto with nldef.
  Qed.

  Lemma Is_variable_in_var_defined:
    forall x eqs,
      Is_variable_in x eqs
      <-> In x (vars_defined (filter (notb is_fby) eqs)).
  Proof.
    intros. unfold Is_variable_in, vars_defined, notb.
    split; intros In.
    - simpl_Exists. solve_In.
      1,2:inv In; simpl; auto.
    - simpl_In. solve_Exists.
      destruct x0; simpl in *; try (take (_ \/ _) and destruct it); subst;
        try (now exfalso); auto with nldef.
  Qed.

  Lemma In_EqDef_Is_variable_in:
    forall x ck e eqs,
      In (EqDef x ck e) eqs ->
      Is_variable_in x eqs.
  Proof.
    induction eqs; inversion_clear 1; subst.
    now repeat constructor.
    constructor 2; intuition.
  Qed.

  Lemma In_EqApp_Is_variable_in:
    forall x xs ck f es eqs r,
      List.In x xs ->
      In (EqApp xs ck f es r) eqs ->
      Is_variable_in x eqs.
  Proof.
    induction eqs; inversion_clear 2.
    - now subst; repeat constructor.
    - constructor; eapply IHeqs; eauto.
  Qed.

  (** * Decision procedure *)

  Definition variable_eq (vars: PS.t) (eq: equation) : PS.t :=
    match eq with
    | EqDef x _ _   => PS.add x vars
    | EqApp xs _ _ _ _ => ps_adds xs vars
    | EqLast _ _ _ _ _
    | EqFby _ _ _ _ _ => vars
    end.

  Definition variables (eqs: list equation) : PS.t :=
    List.fold_left variable_eq eqs PS.empty.

  (** ** Properties *)

  Lemma In_variable_eq:
    forall x eq m,
      PS.In x (variable_eq m eq) <-> PS.In x m \/ PS.In x (variable_eq PS.empty eq).
  Proof.
    destruct eq; simpl; try setoid_rewrite PS.add_spec; try setoid_rewrite ps_adds_spec; intros m; split; auto.
    - intros [ H | H ]; auto.
    - intros [ H | [ H | H ] ]; auto.
      inversion H.
    - intros [ H | H ].
      + auto.
      + inversion H.
    - intros [ H | H ]; auto.
    - intros [ H | [ H | H ] ]; auto.
      inversion H.
    - intros [ H | H ].
      + auto.
      + inversion H.
  Qed.

  Lemma In_fold_left_variable_eq:
    forall x eqs m,
      PS.In x (List.fold_left variable_eq eqs m)
      <-> Exists (fun eq => PS.In x (variable_eq PS.empty eq)) eqs \/ PS.In x m.
  Proof.
    induction eqs as [|eq]; simpl.
    - split; auto.
      intros [Ex|]; auto. inv Ex.
    - intros ?. rewrite IHeqs, In_variable_eq.
      split; intros; repeat (take (_ \/ _) and destruct it); auto.
      inv H; auto.
  Qed.

  (* tactic definition needed in signature *)
  Ltac not_Is_variable x y :=
    match goal with
    | H: ~ Is_variable_in_eq x (EqDef y _ _) |- _ =>
      apply not_Is_variable_in_EqDef in H
    | H: ~ Is_variable_in_eq x (EqApp y _ _ _ _) |- _ =>
      apply not_Is_variable_in_EqApp in H
    end.

  Lemma Is_variable_in_eq_dec:
    forall x eq, {Is_variable_in_eq x eq}+{~Is_variable_in_eq x eq}.
  Proof.
    intros x eq.
    destruct eq as [y cae| |ys f lae|y v0 lae].
    - destruct (ident_eq_dec x y); subst; auto with nldef.
      right. inversion 1; subst; auto with nldef.
    - right. inversion 1.
    - destruct (in_dec ident_eq_dec x ys); auto with nldef.
      right. inversion 1; subst; auto with nldef.
    - right. inversion 1.
  Qed.

  Lemma Is_variable_in_cons:
    forall x eq eqs,
      Is_variable_in x (eq :: eqs) ->
      Is_variable_in_eq x eq
      \/ (~Is_variable_in_eq x eq /\ Is_variable_in x eqs).
  Proof.
    intros x eq eqs Hdef.
    apply List.Exists_cons in Hdef.
    destruct (Is_variable_in_eq_dec x eq); destruct Hdef; auto with *.
  Qed.

  Lemma not_Is_variable_in_cons:
    forall x eq eqs,
      ~Is_variable_in x (eq :: eqs)
      <-> ~Is_variable_in_eq x eq /\ ~Is_variable_in x eqs.
  Proof.
    intros x eq eqs. split.
    intro H0; unfold Is_variable_in in H0; auto.
    destruct 1 as [H0 H1]; intro H; apply Is_variable_in_cons in H.
    destruct H as [ H | [ H H' ] ]; auto.
  Qed.

  Lemma Is_variable_in_variables:
    forall x eqs,
      PS.In x (variables eqs)
      <-> Is_variable_in x eqs.
  Proof.
    intros. unfold variables, Is_variable_in.
    rewrite In_fold_left_variable_eq, PSF.empty_iff.
    split; [intros [Ex|[]]|intros Ex; left]; solve_Exists.
    - destruct x0; simpl in *;
        rewrite ?PS.add_spec, ?ps_adds_spec, ?PSF.empty_iff in Ex;
        try (take (_ \/ _) and destruct it); subst; auto with nldef; try now exfalso.
    - inv Ex; simpl; rewrite ?PS.add_spec, ?ps_adds_spec; auto.
  Qed.

End ISVARIABLE.

Module IsVariableFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Syn   : NLSYNTAX      Ids Op OpAux Cks CESyn)
       (Mem   : MEMORIES      Ids Op OpAux Cks CESyn Syn)
       (IsD   : ISDEFINED     Ids Op OpAux Cks CESyn Syn Mem)
       <: ISVARIABLE Ids Op OpAux Cks CESyn Syn Mem IsD.
  Include ISVARIABLE Ids Op OpAux Cks CESyn Syn Mem IsD.
End IsVariableFun.
