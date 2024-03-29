From Coq Require Import PArith.
From Coq Require Import List.

Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
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
      -> Is_defined_in_eq x eq.
  Proof.
    destruct eq; inversion_clear 1; auto with nldef.
  Qed.

  Lemma Is_variable_in_Is_defined_in:
    forall x eqs,
      Is_variable_in x eqs
      -> Is_defined_in x eqs.
  Proof.
    induction eqs as [|eq eqs IH]; [now inversion 1|].
    inversion_clear 1 as [Hin ? Hivi|]; [|constructor 2; intuition].
    apply Is_variable_in_eq_Is_defined_in_eq in Hivi.
    now constructor.
  Qed.

  Global Hint Resolve Is_variable_in_eq_Is_defined_in_eq Is_variable_in_Is_defined_in : nldef.

  Lemma not_Is_defined_in_eq_not_Is_variable_in_eq:
    forall x eq, ~Is_defined_in_eq x eq -> ~Is_variable_in_eq x eq.
  Proof.
    intros x eq Hnidi.
    destruct eq; inversion 1; subst; intuition.
  Qed.

  Lemma not_Is_defined_in_not_Is_variable_in:
    forall x eqs, ~Is_defined_in x eqs -> ~Is_variable_in x eqs.
  Proof.
    induction eqs as [|eq].
    - intro H; contradict H; inversion H.
    - intros Hndef Hvar.
      inv Hvar;
      eapply Hndef.
      + constructor; auto with nldef.
      + constructor 2;
            now apply Exists_exists in H0 as (eq' & ? & ?);
                apply Exists_exists; exists eq'; split; auto with nldef.
  Qed.

  Lemma Is_variable_in_var_defined:
    forall x eqs,
      Is_variable_in x eqs
      <-> In x (vars_defined (filter (notb is_fby) eqs)).
  Proof.
    unfold notb.
    induction eqs as [|eq eqs].
    now apply Exists_nil.
    split; intro HH.
    - inversion_clear HH as [? ? Hdef|? ? Hdef].
      + inversion_clear Hdef; simpl; try apply in_app; auto.
      + apply IHeqs in Hdef. simpl;
        destruct eq; simpl; intuition.
    - destruct eq; simpl in *.
      + destruct HH as [HH|HH].
        * subst; repeat constructor.
        * apply IHeqs in HH. now constructor 2.
      + unfold vars_defined in HH;
        apply in_app in HH.
        destruct HH as [HH|HH].
        * subst; constructor; auto with nldef.
        * apply IHeqs in HH. now constructor 2.
      + apply IHeqs in HH. now constructor 2.
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
    | EqFby _ _ _ _ _ => vars
    end.

  Definition variables (eqs: list equation) : PS.t :=
    List.fold_left variable_eq eqs PS.empty.

  (** ** Properties *)

  Lemma Subset_variable_eq:
    forall eq m1 m2,
      PS.Subset m1 m2 ->
      PS.Subset (variable_eq m1 eq) (variable_eq m2 eq).
  Proof.
    intros * Hsub.
    destruct eq; simpl; auto.
    - apply PSP.subset_add_3, PSP.subset_add_2; try apply PS.add_spec; auto.
    - now apply Subset_ps_adds.
  Qed.

  Lemma In_variable_eq:
    forall x eq m,
      PS.In x (variable_eq m eq) <-> PS.In x m \/ PS.In x (variable_eq PS.empty eq).
  Proof.
    destruct eq; simpl;
      try setoid_rewrite PS.add_spec; try setoid_rewrite ps_adds_spec; intuition.
  Qed.

  Lemma In_fold_left_variable_eq:
    forall x eqs m,
      PS.In x (List.fold_left variable_eq eqs m)
      <-> PS.In x (List.fold_left variable_eq eqs PS.empty) \/ PS.In x m.
  Proof.
    induction eqs as [|eq eqs IH]; simpl.
    now split; intro HH; auto; destruct HH as [HH|]; auto;
      apply not_In_empty in HH.
    setoid_rewrite IH; clear IH.
    setoid_rewrite In_variable_eq.
    split; intros [HH|HH]; auto; repeat (destruct HH as [HH|HH]; auto).
    now apply not_In_empty in HH.
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
    destruct eq as [y cae|ys f lae|y v0 lae].
    - destruct (ident_eq_dec x y); subst; auto with nldef.
      right. inversion 1; subst; auto with nldef.
    - destruct (in_dec ident_eq_dec x ys); auto with nldef.
      right. inversion 1; subst; auto with nldef.
    - right. inversion 1; subst; auto with nldef.
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

  Lemma Is_variable_in_variables:
    forall x eqs,
      PS.In x (variables eqs)
      <-> Is_variable_in x eqs.
  Proof.
    unfold variables, Is_variable_in.
    induction eqs as [ | eq ].
    - rewrite List.Exists_nil; split; intro H;
      try apply not_In_empty in H; contradiction.
    - simpl.
      rewrite In_fold_left_variable_eq.
      split.
      + rewrite List.Exists_cons.
        destruct 1. intuition.
        destruct eq;
          match goal with
          | |- context[ EqApp _ _ _ _ _ ] =>
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
          | |- context[ EqApp _ _ _ _ _ ] =>
            generalize ps_adds_spec; intro add_spec
          | _ =>
            generalize PS.add_spec; intro add_spec
          end; try inversion H;
            (right; apply add_spec; intuition).
        left; apply IHeqs; apply H.
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
