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
  | VarEqApp: forall x xs ck f e, List.In x xs -> Is_variable_in_eq x (EqApp xs ck f e).

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
    forall x ys ck f e,
      ~ Is_variable_in_eq x (EqApp ys ck f e) -> ~ List.In x ys.
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
    forall x xs ck f es eqs,
      List.In x xs ->
      In (EqApp xs ck f es) eqs ->
      Is_variable_in_eqs x eqs.
  Proof.
    induction eqs; inversion_clear 2.
    - now subst; repeat constructor.
    - constructor(apply IHeqs; eauto).
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
