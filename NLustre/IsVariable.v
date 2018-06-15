Require Import PArith.
Require Import List.

Import List.ListNotations.
Open Scope list_scope.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.IsDefined.
Require Import Velus.NLustre.Memories.

Require Import Coq.Sorting.Permutation.

(** * Stack variables *)

(**

  The [Is_variable] predicate identifies those variables that will
  stay on the stack after compilation, ie. anything not defined by an
  [fby].

 *)

Module Type ISVARIABLE
       (Ids         : IDS)
       (Op          : OPERATORS)
       (Import Clks : CLOCKS    Ids)
       (Import Syn  : NLSYNTAX  Ids Op Clks)
       (Import Mem  : MEMORIES  Ids Op Clks Syn)
       (Import IsD  : ISDEFINED Ids Op Clks Syn Mem).

  Inductive Is_variable_in_eq : ident -> equation -> Prop :=
  | VarEqDef: forall x ck e,   Is_variable_in_eq x (EqDef x ck e)
  | VarEqApp: forall x xs ck f e r, List.In x xs -> Is_variable_in_eq x (EqApp xs ck f e r).

  (* definition is needed in signature *)
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
    forall x ys ck f e r,
      ~ Is_variable_in_eq x (EqApp ys ck f e r) -> ~ List.In x ys.
  Proof. eauto using Is_variable_in_eq. Qed.


  Lemma Is_variable_in_eq_Is_defined_in_eq:
    forall x eq,
      Is_variable_in_eq x eq
      -> Is_defined_in_eq x eq.
  Proof.
    destruct eq; inversion_clear 1; auto using Is_defined_in_eq.
  Qed.

  Lemma Is_variable_in_eqs_Is_defined_in_eqs:
    forall x eqs,
      Is_variable_in_eqs x eqs
      -> Is_defined_in_eqs x eqs.
  Proof.
    induction eqs as [|eq eqs IH]; [now inversion 1|].
    inversion_clear 1 as [Hin ? Hivi|]; [|constructor 2; intuition].
    apply Is_variable_in_eq_Is_defined_in_eq in Hivi.
    constructor (assumption).
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
    - intros Hndef Hvar.
      inv Hvar;
      eapply Hndef.
      + constructor(now apply Is_variable_in_eq_Is_defined_in_eq).
      + constructor(
            now apply Exists_exists in H0 as (eq' & ? & ?);
                apply Exists_exists; exists eq'; split; auto;
                apply Is_variable_in_eq_Is_defined_in_eq).
  Qed.

  Lemma Is_variable_in_var_defined:
    forall x eqs,
      Is_variable_in_eqs x eqs
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
        unfold vars_defined; rewrite concatMap_cons;
          eapply in_app; intuition.
    - destruct eq; simpl in *.
      + destruct HH as [HH|HH].
        * subst; repeat constructor.
        * apply IHeqs in HH. constructor (assumption).
      + unfold vars_defined in HH; rewrite concatMap_cons in HH;
        apply in_app in HH.
        destruct HH as [HH|HH].
        * subst; constructor; auto using Is_variable_in_eq.
        * apply IHeqs in HH. constructor (assumption).
      + apply IHeqs in HH. constructor (assumption).
  Qed.

  Lemma In_EqDef_Is_variable_in_eqs:
    forall x ck e eqs,
      In (EqDef x ck e) eqs ->
      Is_variable_in_eqs x eqs.
  Proof.
    induction eqs; inversion_clear 1; subst.
    now repeat constructor.
    constructor 2; intuition.
  Qed.

  Lemma In_EqApp_Is_variable_in_eqs:
    forall x xs ck f es eqs r,
      List.In x xs ->
      In (EqApp xs ck f es r) eqs ->
      Is_variable_in_eqs x eqs.
  Proof.
    induction eqs; inversion_clear 2.
    - now subst; repeat constructor.
    - constructor (eapply IHeqs; eauto).
  Qed.

  Lemma n_out_variable_in_eqs:
    forall n x,
      In x (map fst n.(n_out)) ->
      Is_variable_in_eqs x n.(n_eqs).
  Proof.
    intros.
    apply Is_variable_in_var_defined.
    eapply not_In_app; eauto using n.(n_vout).
    unfold vars_defined, concatMap.
    rewrite <- concat_app, <-map_app, Permutation_app_comm,
            filter_notb_app, n.(n_defd), map_app.
    now intuition.
  Qed.

  (** * Decision procedure *)

  Fixpoint variable_eq (vars: PS.t) (eq: equation) {struct eq} : PS.t :=
    match eq with
    | EqDef x _ _   => PS.add x vars
    | EqApp xs _ _ _ _ => ps_adds xs vars
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
            | |- context[ EqApp _ _ _ _ _ ] =>
              generalize ps_adds_spec; intro add_spec
            | _ =>
              generalize PS.add_spec; intro add_spec
            end;
            try (apply add_spec in H; destruct H);
            match goal with
            | H:x=_ |- _ => rewrite H; simpl; rewrite add_spec; intuition
            | H: In x ?i |- context [EqApp ?i _ _ _ _] => simpl; rewrite add_spec; intuition
            | _ => apply not_In_empty in H; contradiction
            | _ => intuition
            end ]
        | now
            right; destruct eq;
            match goal with
            | |- context[ EqApp _ _ _ _ _ ] =>
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
    | H: ~ Is_variable_in_eq x (EqApp y _ _ _ _) |- _ =>
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
      | |- context Is_variable_in_eq [EqApp _ _ _ _ _] =>
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
      | |- context[ EqApp _ _ _ _ _ ] =>
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
      | _ : _ = EqApp _ _ _ _ _ |- _ =>
        generalize ps_adds_spec; intro add_spec
      | _ =>
        generalize PS.add_spec; intro add_spec
      end;
      try (apply add_spec in H; destruct H); try apply PS.empty_spec in H;
        try (rewrite ps_adds_spec; auto);
        intuition.
  Qed.

End ISVARIABLE.

Module IsVariableFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Clks : CLOCKS Ids)
       (Syn  : NLSYNTAX  Ids Op Clks)
       (Mem  : MEMORIES  Ids Op Clks Syn)
       (IsD  : ISDEFINED Ids Op Clks Syn Mem)
       <: ISVARIABLE Ids Op Clks Syn Mem IsD.
  Include ISVARIABLE Ids Op Clks Syn Mem IsD.
End IsVariableFun.
