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

Fixpoint free_in_lexp (e : lexp) (fvs : PS.t) : PS.t :=
  match e with
    | Econst c => fvs
    | Evar x => PS.add x fvs
    | Ewhen ae c x => free_in_laexp ae fvs
  end
with free_in_laexp (lae : laexp) (fvs : PS.t) : PS.t :=
  match lae with
    | LAexp ck e => free_in_lexp e fvs
  end.

Inductive Is_free_in_lexp : ident -> lexp -> Prop :=
| FreeEvar: forall x, Is_free_in_lexp x (Evar x)
| FreeEwhen: forall ae ck cv x,
    Is_free_in_laexp x ae ->
    Is_free_in_lexp x (Ewhen ae ck cv)
with Is_free_in_laexp : ident -> laexp -> Prop :=
| freeLAexp: forall ck e x,
    Is_free_in_lexp x e ->
    Is_free_in_laexp x (LAexp ck e).

Fixpoint free_in_caexp (cae: caexp) (fvs: PS.t) : PS.t :=
  match cae with
  | CAexp ck ce => free_in_cexp ce fvs
  end
with free_in_cexp (ce: cexp) (fvs: PS.t) : PS.t :=
  match ce with
  | Emerge i t f => PS.add i (free_in_caexp f (free_in_caexp t fvs))
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
| FreeCAexp: forall ck ce x,
    Is_free_in_cexp x ce ->
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

Lemma not_In_empty: forall x : ident, ~(PS.In x PS.empty).
Proof.
  unfold PS.In; unfold PS.empty;
  intros; rewrite PS.mem_Leaf; apply Bool.diff_false_true.
Qed.

Lemma free_in_lexp_in:
  forall x e, PS.In x (free_in_lexp e PS.empty) <-> Is_free_in_lexp x e.
Proof.
  intro x.
  apply (lexp_mult
           (fun e : laexp =>
              PS.In x (free_in_laexp e PS.empty) <-> Is_free_in_laexp x e)
           (fun e : lexp =>
              PS.In x (free_in_lexp e PS.empty) <-> Is_free_in_lexp x e));
    simpl; constructor; intro H0.
  - constructor; apply H; assumption.
  - inversion H0; apply H; assumption.
  - apply not_In_empty in H0; contradiction.
  - inversion H0.
  - apply PS.add_spec in H0.
    destruct H0 as [H1|H2].
    rewrite H1; constructor.
    apply not_In_empty in H2; contradiction.
  - inversion H0; apply PS.add_spec; left; reflexivity.
  - apply H in H0; constructor; apply H0.
  - apply H; inversion H0; assumption.
Qed.

Lemma free_in_laexp_in:
  forall x e, PS.In x (free_in_laexp e PS.empty) <-> Is_free_in_laexp x e.
Proof.
  destruct e.
  simpl.
  constructor.
  intros H; apply free_in_lexp_in in H; apply freeLAexp; assumption.
  intros H; apply free_in_lexp_in; inversion H; assumption.
Qed.

Lemma free_in_lexp_or_acc:
  forall x e S,
    PS.In x (free_in_lexp e S)
    <-> (PS.In x (free_in_lexp e PS.empty) \/ PS.In x S).
Proof.
  intros x e S.
  generalize e.
  apply (lexp_mult
           (fun e : laexp =>
              PS.In x (free_in_laexp e S)
              <-> (PS.In x (free_in_laexp e PS.empty) \/ PS.In x S))
           (fun e : lexp =>
              PS.In x (free_in_lexp e S)
              <-> (PS.In x (free_in_lexp e PS.empty) \/ PS.In x S))).
  - trivial.
  - constructor; auto; destruct 1 as [H|].
    apply not_In_empty in H; contradiction.
    assumption.
  - constructor.
    + intro H; apply PS.add_spec in H; destruct H as [H1|H1].
      rewrite H1; left; apply PS.add_spec; auto.
      right; assumption.
    + destruct 1.
      apply PS.add_spec in H; destruct H.
      rewrite H; apply PS.add_spec; auto.
      apply not_In_empty in H; contradiction.
      apply PS.add_spec; auto.
  - constructor.
    apply H; destruct 1.
    apply H; auto.
Qed.

Lemma free_in_laexp_or_acc:
  forall x e S,
    PS.In x (free_in_laexp e S)
    <-> (PS.In x (free_in_laexp e PS.empty) \/ PS.In x S).
Proof.
  destruct e; apply free_in_lexp_or_acc.
Qed.

Lemma free_in_cexp_or_acc:
  forall x e S,
    PS.In x (free_in_cexp e S)
    <-> (PS.In x (free_in_cexp e PS.empty) \/ PS.In x S).
Proof.
  intros x.
  apply (cexp_mult
           (fun e : caexp =>
              forall S,
                (PS.In x (free_in_caexp e S)
                 <-> (PS.In x (free_in_caexp e PS.empty) \/ PS.In x S)))
           (fun e : cexp =>
              forall S,
                (PS.In x (free_in_cexp e S)
                 <-> (PS.In x (free_in_cexp e PS.empty) \/ PS.In x S)))).
  - trivial.
  - constructor. (* TODO: automate ! *)
    intro.
    simpl in H1.
    apply PS.add_spec in H1.
    destruct H1.
    rewrite H1.
    left.
    apply PS.add_spec.
    auto.

    apply H0 in H1.
    destruct H1.
    left.
    simpl.
    apply PS.add_spec.
    right.
    apply H0.
    auto.

    apply H in H1.
    destruct H1.
    left.
    simpl.
    apply PS.add_spec.
    right.
    apply H0.
    right.
    apply H1.
    auto.

    destruct 1.
    simpl.
    apply PS.add_spec.
    simpl in H1.
    apply PS.add_spec in H1.
    destruct H1.
    auto.
    right.

    apply H0.
    apply H0 in H1.
    destruct H1.
    auto.
    right.
    apply H.
    auto.

    simpl.
    apply PS.add_spec.
    right.
    apply H0.
    right.
    apply H.
    auto.
  - apply free_in_lexp_or_acc.
Qed.

Lemma free_in_caexp_or_acc:
  forall x e S,
    PS.In x (free_in_caexp e S)
    <-> (PS.In x (free_in_caexp e PS.empty) \/ PS.In x S).
Proof.
  induction e; apply free_in_cexp_or_acc.
Qed.

Lemma free_in_cexp_in:
  forall x e, PS.In x (free_in_cexp e PS.empty) <-> Is_free_in_cexp x e.
Proof.
  intro x.
  apply (cexp_mult
           (fun e : caexp =>
              PS.In x (free_in_caexp e PS.empty) <-> Is_free_in_caexp x e)
           (fun e : cexp =>
              PS.In x (free_in_cexp e PS.empty) <-> Is_free_in_cexp x e));
    simpl; constructor; intro H1.
  - constructor; apply H; assumption.
  - apply H; inversion H1; apply H3.
  - apply PS.add_spec in H1.
    destruct H1.
    rewrite H1; constructor.
    apply free_in_caexp_or_acc in H1.
    destruct H1.
    apply H0 in H1.
    apply FreeEmerge_false.
    apply H1.
    apply FreeEmerge_true.
    apply H.
    apply H1.
  - apply PS.add_spec.
    inversion H1.
    + auto.
    + right.
      apply free_in_caexp_or_acc.
      right.
      apply H.
      apply H4.
    + right.
      apply free_in_caexp_or_acc.
      left.
      apply H0.
      apply H4.
  - apply FreeEexp.
    apply free_in_lexp_in.
    apply H1.
  - apply free_in_lexp_in.
    inversion H1.
    apply H2.
Qed.

Lemma free_in_caexp_in:
  forall x e, PS.In x (free_in_caexp e PS.empty) <-> Is_free_in_caexp x e.
Proof.
  destruct e; constructor.
  - intro H; apply FreeCAexp; apply free_in_cexp_in; apply H.
  - destruct 1; apply free_in_cexp_in; apply H.
Qed.

Lemma free_in_equation_or_acc:
  forall x eq S,
    PS.In x (free_in_equation eq S)
    <-> (PS.In x (free_in_equation eq PS.empty) \/ PS.In x S).
Proof.
  destruct eq; apply free_in_caexp_or_acc || apply free_in_laexp_or_acc.
Qed.

Lemma free_in_equation_in:
  forall x eq, PS.In x (free_in_equation eq PS.empty)
               <-> Is_free_in_equation x eq.
Proof.
  destruct eq. (* TODO: rewrite using ltac *)
  - constructor.
    intro H; apply FreeEqDef; apply free_in_caexp_in; apply H.
    inversion 1; apply free_in_caexp_in; assumption.
  - constructor.
    intro H; apply FreeEqApp; apply free_in_laexp_in; apply H.
    inversion 1; apply free_in_laexp_in; assumption.
  - constructor.
    intro H; apply FreeEqFby; apply free_in_laexp_in; apply H.
    inversion 1; apply free_in_laexp_in; assumption.
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

Lemma Is_memory_in_cons:
  forall eq eqs x, Is_memory_in x eqs -> Is_memory_in x (eq :: eqs).
Proof. unfold Is_memory_in; auto using List.Exists_cons. Qed.

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

Fixpoint variable_eq (vars: PS.t) (eq: equation) : PS.t :=
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



Fixpoint defined_eq (defs: PS.t) (eq: equation) : PS.t :=
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


(** The map containing global definitions. *)
Require Coq.FSets.FMapPositive.
Definition global := FSets.FMapPositive.PositiveMap.t node.

