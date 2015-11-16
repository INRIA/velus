Require Import Rustre.Common.
Require Import PArith.

Import List.ListNotations.
Open Scope list_scope.

(** * Dataflow language *)

Inductive clock : Set :=
| Cbase : clock                          (* base clock *)
| Con : clock -> ident -> bool -> clock. (* subclock *)

Record var_dec : Set := mk_var { v_name : ident;
                                 v_clock : clock }.

(** ** Syntax *)

(* TODO: laexp: would be nicer if it were a record *)
Inductive lexp : Type :=
  | Econst : const -> lexp
  | Evar : ident -> lexp
  | Ewhen : lexp -> ident -> bool -> lexp.
(* External operators are missing *)

Inductive laexp : Type :=
  | LAexp : clock -> lexp -> laexp.


(* TODO: caexp: would be nicer if it were a record *)
Inductive cexp : Type :=
  | Emerge : ident -> cexp -> cexp -> cexp (* currently only binary merge *)
  | Eexp : lexp -> cexp.

Inductive caexp : Type :=
  | CAexp : clock -> cexp -> caexp.

(** ** Equations *)

Inductive equation : Type :=
  | EqDef : ident -> caexp -> equation
  | EqApp : ident -> ident -> laexp -> equation
  | EqFby : ident -> const -> laexp -> equation.

Record node : Type := mk_node {
  n_name : ident;
  n_input : var_dec;
  n_output : var_dec;
  n_eqs : list equation }.

Definition global := list node.

Definition find_node (f : ident) : global -> option node :=
  List.find (fun n=> ident_eqb n.(n_name) f).

(** ** Predicates *)

(* TODO: free variables should include those in clock expressions.
         use auto for the proofs. *)

Fixpoint free_in_clock (ck : clock) (fvs: PS.t) : PS.t :=
  match ck with
  | Cbase => fvs
  | Con ck' x xc => free_in_clock ck' (PS.add x fvs)
  end.

Inductive Is_free_in_clock : ident -> clock -> Prop :=
| FreeCon1:
    forall x ck' xc,
      Is_free_in_clock x (Con ck' x xc)
| FreeCon2:
    forall x y ck' xc,
      Is_free_in_clock x ck'
      -> Is_free_in_clock x (Con ck' y xc).

Fixpoint free_in_lexp (e: lexp) (fvs: PS.t) : PS.t :=
  match e with
  | Econst c => fvs
  | Evar x => PS.add x fvs
  | Ewhen e x xc => free_in_lexp e (PS.add x fvs)
  end.

Definition free_in_laexp (lae : laexp) (fvs : PS.t) : PS.t :=
  match lae with
  | LAexp ck e => free_in_lexp e (free_in_clock ck fvs)
  end.

Inductive Is_free_in_lexp : ident -> lexp -> Prop :=
| FreeEvar: forall x, Is_free_in_lexp x (Evar x)
| FreeEwhen1: forall e c cv x,
    Is_free_in_lexp x e ->
    Is_free_in_lexp x (Ewhen e c cv)
| FreeEwhen2: forall e c cv,
    Is_free_in_lexp c (Ewhen e c cv).

Inductive Is_free_in_laexp : ident -> laexp -> Prop :=
| freeLAexp1: forall ck e x,
    Is_free_in_lexp x e ->
    Is_free_in_laexp x (LAexp ck e)
| freeLAexp2: forall ck e x,
    Is_free_in_clock x ck ->
    Is_free_in_laexp x (LAexp ck e).

Fixpoint free_in_cexp (ce: cexp) (fvs: PS.t) : PS.t :=
  match ce with
  | Emerge i t f => free_in_cexp f (free_in_cexp t (PS.add i fvs))
  | Eexp e => free_in_lexp e fvs
  end.

Definition free_in_caexp (cae: caexp) (fvs: PS.t) : PS.t :=
  match cae with
  | CAexp ck ce => free_in_cexp ce (free_in_clock ck fvs)
  end.

(* Definition free_in_caexp cae := free_in_caexp' cae PS.empty. *)

Inductive Is_free_in_cexp : ident -> cexp -> Prop :=
| FreeEmerge_cond: forall i t f,
    Is_free_in_cexp i (Emerge i t f)
| FreeEmerge_true: forall i t f x,
    Is_free_in_cexp x t ->
    Is_free_in_cexp x (Emerge i t f)
| FreeEmerge_false: forall i t f x,
    Is_free_in_cexp x f ->
    Is_free_in_cexp x (Emerge i t f)
| FreeEexp: forall e x,
    Is_free_in_lexp x e ->
    Is_free_in_cexp x (Eexp e).

Inductive Is_free_in_caexp : ident -> caexp -> Prop :=
| FreeCAexp1: forall ck ce x,
    Is_free_in_cexp x ce ->
    Is_free_in_caexp x (CAexp ck ce)
| FreeCAexp2: forall ck ce x,
    Is_free_in_clock x ck ->
    Is_free_in_caexp x (CAexp ck ce).

Fixpoint free_in_equation (eq: equation) (fvs: PS.t) : PS.t :=
  match eq with
  | EqDef _ cae => free_in_caexp cae fvs
  | EqApp _ f lae => free_in_laexp lae fvs
  | EqFby _ v lae => free_in_laexp lae fvs
  end.

Inductive Is_free_in_equation : ident -> equation -> Prop :=
| FreeEqDef:
    forall x cae i,
      Is_free_in_caexp i cae ->
      Is_free_in_equation i (EqDef x cae)
| FreeEqApp:
    forall x f lae i,
      Is_free_in_laexp i lae ->
      Is_free_in_equation i (EqApp x f lae)
| FreeEqFby:
    forall x v lae i,
      Is_free_in_laexp i lae ->
      Is_free_in_equation i (EqFby x v lae).

(* TODO: Why isn't this lemma already in the module PS? *)
Lemma not_In_empty: forall x : ident, ~(PS.In x PS.empty).
Proof.
  unfold PS.In; unfold PS.empty;
  intros; rewrite PS.mem_Leaf; apply Bool.diff_false_true.
Qed.

Ltac not_In_empty :=
  match goal with H:PS.In _ PS.empty |- _ => now apply not_In_empty in H end.

Lemma free_in_clock_spec:
  forall x ck m, PS.In x (free_in_clock ck m)
                 <-> Is_free_in_clock x ck \/ PS.In x m.
Proof.
  Hint Constructors Is_free_in_clock.
  induction ck.
  split; intuition;
  (match goal with H:Is_free_in_clock _ Cbase |- _ => inversion H end).
  split; intro H0.
  apply IHck in H0; destruct H0 as [H0|H0]; try apply PS.add_spec in H0;
  intuition; subst; intuition.
  apply IHck; destruct H0 as [H0|H0]; inversion H0;
  solve [right; apply PS.add_spec; intuition | intuition].
Qed.

Corollary free_in_clock_spec':
  forall x ck, PS.In x (free_in_clock ck PS.empty)
               <-> Is_free_in_clock x ck.
Proof.
  intros; pose proof (free_in_clock_spec x ck PS.empty) as H0;
  intuition not_In_empty.
Qed.

Lemma free_in_lexp_spec:
  forall x e m, PS.In x (free_in_lexp e m)
                <-> Is_free_in_lexp x e \/ PS.In x m.
Proof.
  Hint Constructors Is_free_in_lexp.
  intro x; induction e;
  intro m; (split;
  [
    intro H0; try apply IHe in H0
  | intro H0; try apply IHe
  ]);
  try destruct H0 as [H0|H0];
  try apply free_in_clock_spec in H0;
  try inversion H0;
  try apply PS.add_spec;
  solve [
      intuition
    | right; apply free_in_clock_spec; intuition
    | apply PS.add_spec in H1; destruct H1; subst; intuition
    | right; apply PS.add_spec; intuition ].
Qed.

Lemma free_in_lexp_spec':
  forall x e, PS.In x (free_in_lexp e PS.empty)
              <-> Is_free_in_lexp x e.
Proof.
  intros; pose proof (free_in_lexp_spec x e PS.empty);
  intuition not_In_empty.
Qed.

Lemma free_in_laexp_spec:
  forall x e m, PS.In x (free_in_laexp e m)
                <-> Is_free_in_laexp x e \/ PS.In x m.
Proof.
  Hint Constructors Is_free_in_laexp.
  destruct e; split; intros;
  repeat progress (match goal with
                   | H:_ \/ _ |- _ => destruct H as [H|H]
                   | H:PS.In _ _ |- _ => first [ apply free_in_lexp_spec in H
                                               | apply free_in_clock_spec in H ]
                   | |- context [free_in_laexp _ _] => apply free_in_lexp_spec
                   | H:Is_free_in_laexp _ _ |- _ => inversion_clear H
                   | _ => solve [right; apply free_in_clock_spec; intuition
                                | intuition]
                   end).
Qed.

Lemma free_in_laexp_spec':
  forall x e, PS.In x (free_in_laexp e PS.empty)
              <-> Is_free_in_laexp x e.
Proof.
  intros; pose proof (free_in_laexp_spec x e PS.empty);
  intuition not_In_empty.
Qed.

Ltac destruct_Is_free :=
  repeat match goal with
    | H: _ \/ _ |- _ => 
      destruct H

    | H: Is_free_in_cexp _ (Emerge _ _ _) |- _ => 
      inversion H; subst; clear H

    | H: Is_free_in_cexp _ (Eexp _) |- _ => 
      inversion H; subst; clear H

    | IHe: context[PS.In _ (free_in_cexp ?e _)],
      H:PS.In _ (free_in_cexp ?e _) |- _ => 
      apply IHe in H

    | H: PS.In _ (free_in_lexp _ _) |- _ => 
      apply free_in_lexp_spec in H

    | H: PS.In _ (PS.add _ _) |- _ => 
      apply PS.add_spec in H
  end.

Lemma free_in_cexp_spec:
  forall x e m, PS.In x (free_in_cexp e m)
                <-> Is_free_in_cexp x e \/ PS.In x m.
Proof.
  Hint Constructors Is_free_in_cexp.
  intro x;
    induction e;
    intro m; simpl; split; intro H0;
    destruct_Is_free;
    subst; auto;

  repeat match goal with
    (* Solve [PS.In x (free_in_cexp e2 (free_in_cexp e1 (PS.add i m)))] *)
    | |- PS.In ?i (PS.add ?i _) => 
      apply PS.add_spec; intuition
    | IHe: context[PS.In _ (free_in_cexp ?e _)],
      H: Is_free_in_cexp ?x ?e 
      |- PS.In ?x (free_in_cexp ?e _) => 
      apply IHe; auto
    | _: PS.In ?x ?m
      |- PS.In ?x (PS.add ?i ?m) => 
      apply PS.add_spec; auto
    | IHe: context[PS.In _ (free_in_cexp ?e _)]
      |- PS.In _ (free_in_cexp ?e _)  => 
      (* Keep peeling *)
      apply IHe; right

    (* Solve [PS.In x (free_in_lexp l m)] *)
    | H: Is_free_in_lexp _ _ 
      |- PS.In _ (free_in_lexp _ _) => 
      apply free_in_lexp_spec; auto
    | H: PS.In ?x ?m 
      |- PS.In ?x (free_in_lexp _ ?m) => 
      apply free_in_lexp_spec; auto
         end.
Qed.

Lemma free_in_cexp_spec':
  forall x e, PS.In x (free_in_cexp e PS.empty)
              <-> Is_free_in_cexp x e.
Proof.
  intros; pose proof (free_in_cexp_spec x e PS.empty);
  intuition not_In_empty.
Qed.

Lemma free_in_caexp_spec:
  forall x e m, PS.In x (free_in_caexp e m)
    <-> Is_free_in_caexp x e \/ PS.In x m.
Proof.
  Hint Constructors Is_free_in_caexp.
  destruct e; split; intros;
  repeat progress (match goal with
                   | H:_ \/ _ |- _ => destruct H as [H|H]
                   | H:PS.In _ _ |- _ => first [ apply free_in_cexp_spec in H
                                               | apply free_in_clock_spec in H ]
                   | |- context [free_in_caexp _ _] => apply free_in_cexp_spec
                   | H:Is_free_in_caexp _ _ |- _ => inversion_clear H
                   | _ => solve [right; apply free_in_clock_spec; intuition
                                | intuition]
                   end).
Qed.

Lemma free_in_caexp_spec':
  forall x e, PS.In x (free_in_caexp e PS.empty)
              <-> Is_free_in_caexp x e.
Proof.
  intros; rewrite (free_in_caexp_spec x e PS.empty).
  intuition not_In_empty.
Qed.


Lemma free_in_equation_spec:
  forall x eq m, PS.In x (free_in_equation eq m)
                 <-> (Is_free_in_equation x eq \/ PS.In x m).
Proof.
  Hint Constructors Is_free_in_equation.
  destruct eq; split; intro H;
  repeat progress (match goal with
                   | H:Is_free_in_equation _ _ |- _ => inversion_clear H
                   | H:PS.In _ (free_in_equation _ _) |- _ =>
                                                      apply free_in_caexp_spec in H
                                                   || apply free_in_laexp_spec in H
                   | |- PS.In _ (free_in_equation _ _) =>
                                                      apply free_in_caexp_spec
                                                   || apply free_in_laexp_spec
                   | _ => intuition
                   end).
Qed.

Lemma free_in_equation_spec':
  forall x eq, PS.In x (free_in_equation eq PS.empty)
               <-> Is_free_in_equation x eq.
Proof.
  intros; rewrite (free_in_equation_spec x eq PS.empty).
  intuition not_In_empty.
Qed.


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

Inductive no_dup_defs : list equation -> Prop :=
| NoDupDefs_nil : no_dup_defs nil
| NoDupDefs_cons : forall eq eqs,
                     (forall x, Is_defined_in_eq x eq
                                -> ~Is_defined_in x eqs)
                     -> no_dup_defs eqs
                     -> no_dup_defs (eq::eqs).

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

Inductive NoDup_defs : list equation -> Prop :=
| NDDNil: NoDup_defs nil
| NDDEqDef:
    forall x e eqs,
      NoDup_defs eqs ->
      ~Is_defined_in x eqs ->
      NoDup_defs (EqDef x e :: eqs)
| NDDEqApp:
    forall x f e eqs,
      NoDup_defs eqs ->
      ~Is_defined_in x eqs ->
      NoDup_defs (EqApp x f e :: eqs)
| NDDEqFby:
    forall x v e eqs,
      NoDup_defs eqs ->
      ~Is_defined_in x eqs ->
      NoDup_defs (EqFby x v e :: eqs).

Lemma NoDup_defs_cons:
  forall eq eqs,
    NoDup_defs (eq :: eqs) -> NoDup_defs eqs.
Proof.
  intros eq eqs Hndd.
  destruct eq; inversion_clear Hndd; assumption.
Qed.

Lemma not_Is_variable_in_memories:
  forall x eqs,
    PS.In x (memories eqs)
    -> NoDup_defs eqs
    -> ~Is_variable_in x eqs.
Proof.
  (* TODO: Too complicated! Find a simpler proof. *)
  intros x eqs Hinm Hndd.
  pose proof (Is_defined_in_memories _ _ Hinm) as Hdin.
  unfold memories, Is_variable_in in *.
  induction eqs as [eq|eq eqs IH].
  - simpl in *; intro; not_In_empty.
  - apply Is_defined_in_cons in Hdin.
    inversion Hndd
      as [|y e ? Hndds Hndi|y f e ? Hndds Hndi|y v0 e ? Hndds Hndi];
      subst; clear Hndd.
    + destruct Hdin as [Hdin|[Hndin Hdins]].
      simpl in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].
      apply Is_defined_in_memories in Hinm.
      inversion He; subst; clear He.
      contradiction.

      inversion Hdin; subst; clear Hdin.
      apply Is_variable_in_Is_defined_in in He.
      contradiction.

      simpl in Hinm.
      apply IH with (2:=Hndds) (3:=Hdins) in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].
      inversion He; subst; clear He.
      apply Hndin; now constructor.
      contradiction.
    + destruct Hdin as [Hdin|[Hndin Hdins]].
      simpl in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].
      apply Is_defined_in_memories in Hinm.
      inversion He; subst; clear He.
      contradiction.

      inversion Hdin; subst; clear Hdin.
      apply Is_variable_in_Is_defined_in in He.
      contradiction.

      simpl in Hinm.
      apply IH with (2:=Hndds) (3:=Hdins) in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].
      inversion He; subst; clear He.
      apply Hndin; now constructor.
      contradiction.
    + destruct Hdin as [Hdin|[Hndin Hdins]].
      simpl in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].
      inversion He; subst; clear He.
      inversion Hdin; subst; clear Hdin.

      apply Is_variable_in_Is_defined_in in He.
      contradiction.

      simpl in Hinm.
      apply In_fold_left_memory_eq in Hinm.
      destruct Hinm as [Hinm|Hinm].
      apply IH with (2:=Hndds) (3:=Hdins) in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].

      inversion He; subst; clear He.
      contradiction.

      apply PS.add_spec in Hinm.
      destruct Hinm as [Hinm|Hinm]; [|now not_In_empty].
      rewrite Hinm in *.
      exfalso; apply Hndin; now constructor.
Qed.

Inductive Is_node_in_eq : ident -> equation -> Prop :=
| INI: forall x f e, Is_node_in_eq f (EqApp x f e).

Definition Is_node_in (f: ident) (eqs: list equation) : Prop :=
  List.Exists (Is_node_in_eq f) eqs.

Inductive Ordered_nodes : global -> Prop :=
| ONnil: Ordered_nodes nil
| ONcons:
    forall nd nds,
      Ordered_nodes nds
      -> (forall f, Is_node_in f nd.(n_eqs) ->
                    f <> nd.(n_name)
                    /\ List.Exists (fun n=> f = n.(n_name)) nds)
      -> List.Forall (fun nd'=> nd.(n_name) <> nd'.(n_name)) nds
      -> Ordered_nodes (nd::nds).

Lemma not_Is_node_in_cons:
  forall n eq eqs,
    ~ Is_node_in n (eq::eqs) <-> ~Is_node_in_eq n eq /\ ~Is_node_in n eqs.
Proof.
  intros n eq eqs.
  split; intro HH.
  - split; intro; apply HH; unfold Is_node_in; intuition.
  - destruct HH; inversion_clear 1; intuition.
Qed.

Lemma Is_node_in_Forall:
  forall n eqs,
    ~Is_node_in n eqs <-> List.Forall (fun eq=>~Is_node_in_eq n eq) eqs.
Proof.
  induction eqs as [|eq eqs IH];
    [split; [now constructor|now inversion 2]|].
  split; intro HH.
  - apply not_Is_node_in_cons in HH.
    destruct HH as [Heq Heqs].
    constructor; [exact Heq|apply IH with (1:=Heqs)].
  - apply not_Is_node_in_cons.
    inversion_clear HH as [|? ? Heq Heqs].
    apply IH in Heqs.
    intuition.
Qed.

Lemma Ordered_nodes_append:
  forall G G',
    Ordered_nodes (G ++ G')
    -> Ordered_nodes G'.
Proof.
  induction G as [|nd G IH]; [intuition|].
  intros G' HnGG.
  apply IH; inversion_clear HnGG; assumption.
Qed.

Lemma find_node_Exists:
  forall f G, find_node f G <> None <-> List.Exists (fun n=> f = n.(n_name)) G.
Proof.
  induction G as [|node G IH].
  - split; intro Hfn.
    exfalso; apply Hfn; reflexivity.
    apply List.Exists_nil in Hfn; contradiction.
  - destruct (ident_eq_dec node.(n_name) f) as [He|Hne]; simpl.
    + assert (He' := He); apply BinPos.Pos.eqb_eq in He'.
      unfold ident_eqb; rewrite He'.
      split; intro HH; [clear HH|discriminate 1].
      constructor.
      symmetry; exact He.
    + assert (Hne' := Hne); apply BinPos.Pos.eqb_neq in Hne'.
      unfold ident_eqb; rewrite Hne'.
      split; intro HH; [ apply IH in HH; constructor 2; exact HH |].
      apply List.Exists_cons in HH.
      destruct HH as [HH|HH]; [symmetry in HH; contradiction|].
      apply IH; exact HH.
Qed.

Lemma find_node_tl:
  forall f node G,
    node.(n_name) <> f
    -> find_node f (node::G) = find_node f G.
Proof.
  intros f node G Hnf.
  unfold find_node.
  unfold List.find at 1.
  apply Pos.eqb_neq in Hnf.
  unfold ident_eqb.
  rewrite Hnf.
  reflexivity.
Qed.

Lemma find_node_split:
  forall f G node,
    find_node f G = Some node
    -> exists bG aG,
      G = bG ++ node :: aG.
Proof.
  induction G as [|nd G IH]; [unfold find_node, List.find; discriminate|].
  intro nd'.
  intro Hfind.
  unfold find_node in Hfind; simpl in Hfind.
  destruct (ident_eqb (n_name nd) f) eqn:Heq.
  - injection Hfind; intro He; rewrite <-He in *; clear Hfind He.
    exists []; exists G; reflexivity.
  - apply IH in Hfind.
    destruct Hfind as [bG [aG Hfind]].
    exists (nd::bG); exists aG; rewrite Hfind; reflexivity.
Qed.

Lemma Ordered_nodes_cons_find_node_None:
  forall node G,
    Ordered_nodes (node::G)
    -> find_node node.(n_name) G = None.
Proof.
  intros node G Hord.
  inversion_clear Hord as [|? ? Hord' H0 Hfa]; clear H0.
  induction G as [|eq G IH]; [trivial|].
  simpl.
  destruct (ident_eqb eq.(n_name) node.(n_name)) eqn:Heq;
    apply Forall_cons2 in Hfa;
    destruct Hfa as [Hneq H0].
  - apply Peqb_true_eq in Heq.
    rewrite Heq in Hneq.
    exfalso; apply Hneq; reflexivity.
  - apply IH; inversion_clear Hord'; assumption.
Qed.

Lemma find_node_later_names_not_eq:
  forall f nd G nd',
    Ordered_nodes (nd::G)
    -> find_node f (G) = Some nd'
    -> f <> nd.(n_name).
Proof.
  intros f nd G nd' Hord Hfind.
  pose proof (Ordered_nodes_cons_find_node_None _ _ Hord) as Hnone.
  intro Heq.
  rewrite Heq, Hnone in Hfind.
  discriminate.
Qed.

Lemma find_node_later_not_Is_node_in:
  forall f nd G nd',
    Ordered_nodes (nd::G)
    -> find_node f G = Some nd'
    -> ~Is_node_in nd.(n_name) nd'.(n_eqs).
Proof.
  intros f nd G nd' Hord Hfind Hini.
  apply find_node_split in Hfind.
  destruct Hfind as [bG [aG HG]].
  rewrite HG in Hord.
  inversion_clear Hord as [|? ? Hord' H0 Hnin]; clear H0.
  apply Ordered_nodes_append in Hord'.
  inversion_clear Hord' as [| ? ? Hord Heqs Hnin'].
  apply Heqs in Hini.
  destruct Hini as [H0 HH]; clear H0.
  rewrite Forall_app in Hnin.
  destruct Hnin as [H0 Hnin]; clear H0.
  inversion_clear Hnin as [|? ? H0 HH']; clear H0.
  apply List.Exists_exists in HH.
  destruct HH as [node [HaG Heq]].
  rewrite List.Forall_forall in HH'.
  apply HH' in HaG.
  contradiction.
Qed.

Lemma find_node_not_Is_node_in:
  forall f nd G,
    Ordered_nodes G
    -> find_node f G = Some nd
    -> ~Is_node_in nd.(n_name) nd.(n_eqs).
Proof.
  intros f nd G Hord Hfind.
  apply find_node_split in Hfind.
  destruct Hfind as [bG [aG HG]].
  rewrite HG in Hord.
  apply Ordered_nodes_append in Hord.
  inversion_clear Hord as [|? ? Hord' Heqs Hnin].
  intro Hini.
  apply Heqs in Hini.
  destruct Hini as [HH H0]; clear H0.
  apply HH; reflexivity.
Qed.

Lemma find_node_name:
  forall f G fnode,
    find_node f G = Some fnode -> fnode.(n_name) = f.
Proof.
  induction G as [|node G IH]; [now inversion 1|].
  destruct node as [name input output eqs].
  destruct (ident_eqb name f) eqn:Hfn;
    assert (Hfn':=Hfn);
    [apply Pos.eqb_eq in Hfn'; rewrite Hfn' in *|apply Pos.eqb_neq in Hfn'];
    simpl; rewrite Hfn.
  - injection 1; intro Heq; rewrite <-Heq; reflexivity.
  - intros fnode Hfnode.
    apply IH with (1:=Hfnode).
Qed.

