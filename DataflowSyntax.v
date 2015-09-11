Require Import Rustre.Common.


(** * Dataflow language *)

Inductive clock : Set :=
| Cbase : clock                          (* base clock *)
| Con : clock -> ident -> bool -> clock. (* subclock *)

Record var_dec : Set := mk_var { v_name : ident;
                                 v_clock : clock }.

(** ** Syntax *)

(* TODO: laexp: would be nicer if it were a record *)
Inductive laexp : Type :=
  | LAexp : clock -> lexp -> laexp
with lexp : Type :=
  | Econst : const -> lexp
  | Evar : ident -> lexp
  | Ewhen : laexp -> ident -> bool -> lexp.
(* External operators are missing *)

Scheme laexp_mult := Induction for laexp Sort Prop
with lexp_mult := Induction for lexp Sort Prop.

(* TODO: caexp: would be nicer if it were a record *)
Inductive caexp : Type :=
  | CAexp : clock -> cexp -> caexp
with cexp : Type :=
  | Emerge : ident -> caexp -> caexp -> cexp (* currently only binary merge *)
  | Eexp : lexp -> cexp.

Scheme caexp_mult := Induction for caexp Sort Prop
with cexp_mult := Induction for cexp Sort Prop.

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

(** ** Predicates *)

(* TODO: free variables should include those in clock expressions.
         use auto for the proofs. *)

Require Coq.MSets.MSets.

Module PS := Coq.MSets.MSetPositive.PositiveSet.

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
  | Ewhen ae x xc => free_in_laexp ae (PS.add x fvs)
  end
with free_in_laexp (lae : laexp) (fvs : PS.t) : PS.t :=
  match lae with
  | LAexp ck e => free_in_lexp e (free_in_clock ck fvs)
  end.

Inductive Is_free_in_lexp : ident -> lexp -> Prop :=
| FreeEvar: forall x, Is_free_in_lexp x (Evar x)
| FreeEwhen1: forall ae c cv x,
    Is_free_in_laexp x ae ->
    Is_free_in_lexp x (Ewhen ae c cv)
| FreeEwhen2: forall ae c cv,
    Is_free_in_lexp c (Ewhen ae c cv)
with Is_free_in_laexp : ident -> laexp -> Prop :=
| freeLAexp1: forall ck e x,
    Is_free_in_lexp x e ->
    Is_free_in_laexp x (LAexp ck e)
| freeLAexp2: forall ck e x,
    Is_free_in_clock x ck ->
    Is_free_in_laexp x (LAexp ck e).

Fixpoint free_in_caexp (cae: caexp) (fvs: PS.t) : PS.t :=
  match cae with
  | CAexp ck ce => free_in_cexp ce (free_in_clock ck fvs)
  end
with free_in_cexp (ce: cexp) (fvs: PS.t) : PS.t :=
  match ce with
  | Emerge i t f => free_in_caexp f (free_in_caexp t (PS.add i fvs))
  | Eexp e => free_in_lexp e fvs
  end.

(* Definition free_in_caexp cae := free_in_caexp' cae PS.empty. *)

Inductive Is_free_in_cexp : ident -> cexp -> Prop :=
| FreeEmerge_cond: forall i t f,
    Is_free_in_cexp i (Emerge i t f)
| FreeEmerge_true: forall i t f x,
    Is_free_in_caexp x t ->
    Is_free_in_cexp x (Emerge i t f)
| FreeEmerge_false: forall i t f x,
    Is_free_in_caexp x f ->
    Is_free_in_cexp x (Emerge i t f)
| FreeEexp: forall e x,
    Is_free_in_lexp x e ->
    Is_free_in_cexp x (Eexp e)
with Is_free_in_caexp : ident -> caexp -> Prop :=
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
  Hint Constructors Is_free_in_lexp Is_free_in_laexp.
  intro x; induction e using lexp_mult
  with (P:= fun e : laexp =>
               forall m,
                 PS.In x (free_in_laexp e m)
                 <-> (Is_free_in_laexp x e \/ PS.In x m));
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

Lemma free_in_cexp_spec:
  forall x e m, PS.In x (free_in_cexp e m)
                <-> Is_free_in_cexp x e \/ PS.In x m.
Proof.
  Hint Constructors Is_free_in_cexp Is_free_in_caexp.
  intro x;
    induction e as [c e IHe|i t IHet f IHef|]
                using cexp_mult
                with (P:= fun e : caexp =>
                            forall m,
                              PS.In x (free_in_caexp e m)
                              <-> (Is_free_in_caexp x e \/ PS.In x m));
    intro m; (split; [intro H0; simpl in H0 | intro H0; simpl]);
    repeat progress (
             match goal with
             | H:_\/_ |- _ => destruct H as [H|H]
             | H:PS.In _ (free_in_cexp _ _) |- _ => apply IHe in H
             | H:PS.In _ (free_in_caexp _ _) |- _ => apply IHet in H
                                                     || apply IHef in H
             | H:PS.In _ (PS.add _ _) |- _ => apply PS.add_spec in H
             | H:PS.In _ (free_in_lexp _ _) |- _ => apply free_in_lexp_spec in H
             | H:Is_free_in_caexp _ _ |- _ => inversion_clear H
             | |- PS.In _ (free_in_cexp _ _) => apply IHe
             | |- PS.In _ (free_in_caexp _ _) => apply IHet
                                                       || apply IHef
             | |- PS.In _ (free_in_lexp _ _) => apply free_in_lexp_spec
             | _ => apply free_in_clock_spec in H0
             | _ => intuition
             end);
    try (inversion H0; subst);
    solve [
        right; apply free_in_clock_spec; intuition
      | subst; intuition
      | inversion H0; subst; intuition
      | right; apply IHet; right; apply PS.add_spec; intuition
      | right; apply IHet; intuition ] || idtac.
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

Inductive Is_memory_in_eq : ident -> equation -> Prop :=
| MemEqFby: forall x v e, Is_memory_in_eq x (EqFby x v e).

Definition Is_memory_in (x: ident) (eqs: list equation) : Prop :=
  List.Exists (Is_memory_in_eq x) eqs.

Lemma Is_memory_in_eq_dec:
  forall x eq, {Is_memory_in_eq x eq}+{~Is_memory_in_eq x eq}.
Proof.
  destruct eq as [y cae|y f lae|y v0 lae];
  (destruct (ident_eq_dec x y) as [xeqy|xneqy];
     [ rewrite xeqy; left; constructor | right; inversion 1; auto])
   || (right; inversion_clear 1).
Qed.

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

Lemma Is_memory_in_memories:
  forall x eqs,
    PS.In x (memories eqs) <-> Is_memory_in x eqs.
Proof.
  unfold memories, Is_memory_in.
  induction eqs as [ eq | eq ].
  - rewrite List.Exists_nil; split; intro H;
    try apply not_In_empty in H; contradiction.
  - simpl.
    rewrite In_fold_left_memory_eq.
    split.
    + rewrite List.Exists_cons.
      destruct 1. intuition.
      destruct eq; try (apply not_In_empty in H; intuition).
      simpl in H; apply PS.add_spec in H; destruct H.
      rewrite H; left; constructor.
      apply not_In_empty in H; contradiction.
    + intro H; apply List.Exists_cons in H; destruct H.
      destruct eq; try inversion H.
      right; apply PS.add_spec; intuition.
      left; apply IHeqs; apply H.
Qed.

Lemma Is_memory_in_dec:
  forall x eqs, {Is_memory_in x eqs}+{~Is_memory_in x eqs}.
Proof.
  intros x eqs.
  apply Bool.reflect_dec with (b := PS.mem x (memories eqs)).
  apply Bool.iff_reflect.
  rewrite PS.mem_spec.
  symmetry.
  apply Is_memory_in_memories.
Qed.

Lemma Is_memory_in_EqFby:
  forall y v0 lae eqs,
    Is_memory_in y (EqFby y v0 lae :: eqs).
Proof.
  intros. repeat constructor.
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

Lemma Is_memory_in_defined_in:
  forall x eqs,
    Is_memory_in x eqs ->
    Is_defined_in x eqs.
Proof.
  induction eqs as [|eq].
  inversion 1.
  inversion_clear 1 as [? ? H0|? ? H0]; apply List.Exists_cons.
  - left; destruct eq; inversion_clear H0; constructor.
  - right; apply IHeqs; apply H0.
Qed.

Lemma Is_memory_in_cons:
  forall x eq eqs,
    Is_memory_in x (eq :: eqs) ->
    Is_memory_in_eq x eq
    \/ (~Is_memory_in_eq x eq /\ Is_memory_in x eqs).
Proof.
  intros x eq eqs Hdef.
  apply List.Exists_cons in Hdef.
  destruct (Is_memory_in_eq_dec x eq); intuition.
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

Lemma not_Is_defined_in_cons:
  forall x eq eqs,
    ~Is_defined_in x (eq :: eqs)
    <-> ~Is_defined_in_eq x eq /\ ~Is_defined_in x eqs.
Proof.
  intros x eq eqs. split.
  intro H0; unfold Is_defined_in in H0; auto.
  destruct 1 as [H0 H1]; intro H; apply Is_defined_in_cons in H; intuition.
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

Lemma not_Is_memory_in_cons:
  forall x eq eqs,
    ~Is_memory_in x (eq :: eqs)
    <-> ~Is_memory_in_eq x eq /\ ~Is_memory_in x eqs.
Proof.
  intros x eq eqs. split.
  intro H0; unfold Is_memory_in in H0; auto.
  destruct 1 as [H0 H1]; intro H; apply Is_memory_in_cons in H; intuition.
Qed.

Lemma not_Is_defined_in_not_Is_variable_in:
  forall x eqs, ~Is_defined_in x eqs -> ~Is_variable_in x eqs.
Proof.
  Hint Constructors Is_defined_in_eq.
  induction eqs as [|eq].
  - intro H; contradict H; inversion H.
  - intro H; apply not_Is_defined_in_cons in H; destruct H as [H0 H1].
    apply IHeqs in H1; apply not_Is_variable_in_cons.
    split; [ destruct eq;  inversion 1; subst; intuition
           | apply H1].
Qed.

Lemma not_Is_defined_in_not_Is_memory_in:
  forall x eqs, ~Is_defined_in x eqs -> ~Is_memory_in x eqs.
Proof.
  Hint Constructors Is_defined_in_eq.
  induction eqs as [|eq].
  - intro H; contradict H; inversion H.
  - intro H; apply not_Is_defined_in_cons in H; destruct H as [H0 H1].
    apply IHeqs in H1; apply not_Is_memory_in_cons.
    split; [ destruct eq;  inversion 1; subst; intuition
           | apply H1].
Qed.

Lemma Is_defined_in_not_mem_not_var:
  forall x eqs,
    ~Is_memory_in x eqs
    -> ~Is_variable_in x eqs
    -> ~Is_defined_in x eqs.
Proof.
  intros x eqs Hnmem Hnvar Hndef.
  induction eqs as [|eq].
  inversion Hndef.
  apply not_Is_memory_in_cons in Hnmem.
  apply not_Is_variable_in_cons in Hnvar.
  destruct Hnmem as [Hnmem1 Hnmem2].
  destruct Hnvar as [Hnvar1 Hnvar2].
  apply Is_defined_in_cons in Hndef.
  destruct Hndef as [Hndef|Hndef].
  destruct eq; (inversion Hndef; subst);
  solve [ apply Hnvar1; repeat constructor
        | apply Hnmem1; repeat constructor ].
  now apply IHeqs.
Qed.

Lemma not_Is_memory_in_eq_EqFby:
  forall x i v0 lae,
    ~ Is_memory_in_eq x (EqFby i v0 lae) -> x <> i.
Proof.
  intros x i v0 lae H0 xeqi.
  rewrite xeqi in H0.
  assert (Is_memory_in_eq i (EqFby i v0 lae)) by constructor.
  contradiction.
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

Lemma not_Is_variable_in_eq_EqDef:
  forall x i cae,
    ~ Is_variable_in_eq x (EqDef i cae) -> x <> i.
Proof.
  intros x i cae H0 xeqi.
  rewrite xeqi in H0.
  assert (Is_variable_in_eq i (EqDef i cae)) by constructor.
  contradiction.
Qed.

Lemma not_Is_variable_in_eq_EqApp:
  forall x i f lae,
    ~ Is_variable_in_eq x (EqApp i f lae) -> x <> i.
Proof.
  intros x i f lae H0 xeqi.
  rewrite xeqi in H0.
  assert (Is_variable_in_eq i (EqApp i f lae)) by constructor.
  contradiction.
Qed.

(** The map containing global definitions. *)
Require Coq.FSets.FMapPositive.
Definition global := FSets.FMapPositive.PositiveMap.t node.

