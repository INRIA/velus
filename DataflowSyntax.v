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

Fixpoint freevar_lexp' (e : lexp) (fvs : PS.t) : PS.t :=
  match e with
    | Econst c => fvs
    | Evar x => PS.add x fvs
    | Ewhen ae c x => freevar_laexp' ae fvs
  end
with freevar_laexp' (lae : laexp) (fvs : PS.t) : PS.t :=
  match lae with
    | LAexp ck e => freevar_lexp' e fvs
  end.

Inductive freevar_lexp : lexp -> ident -> Prop :=
| FreeEvar: forall x, freevar_lexp (Evar x) x
| FreeEwhen: forall ae ck cv x,
    freevar_laexp ae x ->
    freevar_lexp (Ewhen ae ck cv) x
with freevar_laexp : laexp -> ident -> Prop :=
| freeLAexp: forall ck e x,
    freevar_lexp e x ->
    freevar_laexp (LAexp ck e) x.

Fixpoint freevar_caexp' (cae: caexp) (fvs: PS.t) : PS.t :=
  match cae with
  | CAexp ck ce => freevar_cexp' ce fvs
  end
with freevar_cexp' (ce: cexp) (fvs: PS.t) : PS.t :=
  match ce with
  | Emerge i t f => PS.add i (freevar_caexp' f (freevar_caexp' t fvs))
  | Eexp e => freevar_lexp' e fvs
  end.

(* Definition freevar_caexp cae := freevar_caexp' cae PS.empty. *)

Inductive freevar_cexp : cexp -> ident -> Prop :=
| FreeEmerge_cond: forall i t f,
    freevar_cexp (Emerge i t f) i
| FreeEmerge_true: forall i t f x,
    freevar_caexp t x ->
    freevar_cexp (Emerge i t f) x
| FreeEmerge_false: forall i t f x,
    freevar_caexp f x ->
    freevar_cexp (Emerge i t f) x
| FreeEexp: forall e x,
    freevar_lexp e x ->
    freevar_cexp (Eexp e) x
with freevar_caexp : caexp -> ident -> Prop :=
| FreeCAexp: forall ck ce x,
    freevar_cexp ce x ->
    freevar_caexp (CAexp ck ce) x.

Fixpoint freevar_equation' (eq: equation) (fvs: PS.t) : PS.t :=
  match eq with
  | EqDef _ cae => freevar_caexp' cae fvs
  | EqApp _ f lae => freevar_laexp' lae fvs
  | EqFby _ v lae => freevar_laexp' lae fvs
  end.

Inductive freevar_equation : equation -> ident -> Prop :=
| FreeEqDef:
    forall x cae i,
      freevar_caexp cae i ->
      freevar_equation (EqDef x cae) i
| FreeEqApp:
    forall x f lae i,
      freevar_laexp lae i ->
      freevar_equation (EqApp x f lae) i
| FreeEqFby:
    forall x v lae i,
      freevar_laexp lae i ->
      freevar_equation (EqFby x v lae) i.

Lemma not_In_empty: forall x : ident, ~(PS.In x PS.empty).
Proof.
  unfold PS.In; unfold PS.empty;
  intros; rewrite PS.mem_Leaf; apply Bool.diff_false_true.
Qed.

Lemma freevar_lexp_in:
  forall x e, PS.In x (freevar_lexp' e PS.empty) <-> freevar_lexp e x.
Proof.
  intro x.
  apply (lexp_mult
           (fun e : laexp =>
              PS.In x (freevar_laexp' e PS.empty) <-> freevar_laexp e x)
           (fun e : lexp =>
              PS.In x (freevar_lexp' e PS.empty) <-> freevar_lexp e x));
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

Lemma freevar_laexp_in:
  forall x e, PS.In x (freevar_laexp' e PS.empty) <-> freevar_laexp e x.
Proof.
  destruct e.
  simpl.
  constructor.
  intros H; apply freevar_lexp_in in H; apply freeLAexp; assumption.
  intros H; apply freevar_lexp_in; inversion H; assumption.
Qed.

Lemma freevar_lexp'_or_acc:
  forall x e S,
    PS.In x (freevar_lexp' e S)
    <-> (PS.In x (freevar_lexp' e PS.empty) \/ PS.In x S).
Proof.
  intros x e S.
  generalize e.
  apply (lexp_mult
           (fun e : laexp =>
              PS.In x (freevar_laexp' e S)
              <-> (PS.In x (freevar_laexp' e PS.empty) \/ PS.In x S))
           (fun e : lexp =>
              PS.In x (freevar_lexp' e S)
              <-> (PS.In x (freevar_lexp' e PS.empty) \/ PS.In x S))).
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

Lemma freevar_laexp'_or_acc:
  forall x e S,
    PS.In x (freevar_laexp' e S)
    <-> (PS.In x (freevar_laexp' e PS.empty) \/ PS.In x S).
Proof.
  destruct e; apply freevar_lexp'_or_acc.
Qed.

Lemma freevar_cexp'_or_acc:
  forall x e S,
    PS.In x (freevar_cexp' e S)
    <-> (PS.In x (freevar_cexp' e PS.empty) \/ PS.In x S).
Proof.
  intros x.
  apply (cexp_mult
           (fun e : caexp =>
              forall S,
                (PS.In x (freevar_caexp' e S)
                 <-> (PS.In x (freevar_caexp' e PS.empty) \/ PS.In x S)))
           (fun e : cexp =>
              forall S,
                (PS.In x (freevar_cexp' e S)
                 <-> (PS.In x (freevar_cexp' e PS.empty) \/ PS.In x S)))).
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
  - apply freevar_lexp'_or_acc.
Qed.

Lemma freevar_caexp'_or_acc:
  forall x e S,
    PS.In x (freevar_caexp' e S)
    <-> (PS.In x (freevar_caexp' e PS.empty) \/ PS.In x S).
Proof.
  induction e; apply freevar_cexp'_or_acc.
Qed.

Lemma freevar_cexp_in:
  forall x e, PS.In x (freevar_cexp' e PS.empty) <-> freevar_cexp e x.
Proof.
  intro x.
  apply (cexp_mult
           (fun e : caexp =>
              PS.In x (freevar_caexp' e PS.empty) <-> freevar_caexp e x)
           (fun e : cexp =>
              PS.In x (freevar_cexp' e PS.empty) <-> freevar_cexp e x));
    simpl; constructor; intro H1.
  - constructor; apply H; assumption.
  - apply H; inversion H1; apply H4.
  - apply PS.add_spec in H1.
    destruct H1.
    rewrite H1; constructor.
    apply freevar_caexp'_or_acc in H1.
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
      apply freevar_caexp'_or_acc.
      right.
      apply H.
      apply H6.
    + right.
      apply freevar_caexp'_or_acc.
      left.
      apply H0.
      apply H6.
  - apply FreeEexp.
    apply freevar_lexp_in.
    apply H1.
  - apply freevar_lexp_in.
    inversion H1.
    apply H0.
Qed.

Lemma freevar_caexp_in:
  forall x e, PS.In x (freevar_caexp' e PS.empty) <-> freevar_caexp e x.
Proof.
  destruct e; constructor.
  - intro H; apply FreeCAexp; apply freevar_cexp_in; apply H.
  - destruct 1; apply freevar_cexp_in; apply H.
Qed.

Lemma freevar_equation'_or_acc:
  forall x eq S,
    PS.In x (freevar_equation' eq S)
    <-> (PS.In x (freevar_equation' eq PS.empty) \/ PS.In x S).
Proof.
  destruct eq; apply freevar_caexp'_or_acc || apply freevar_laexp'_or_acc.
Qed.
  
Lemma freevar_equation_in:
  forall x eq, PS.In x (freevar_equation' eq PS.empty) <-> freevar_equation eq x.
Proof.
  destruct eq. (* TODO: rewrite using ltac *)
  - constructor.
    intro H; apply FreeEqDef; apply freevar_caexp_in; apply H.
    inversion 1; apply freevar_caexp_in; assumption.
  - constructor.
    intro H; apply FreeEqApp; apply freevar_laexp_in; apply H.
    inversion 1; apply freevar_laexp_in; assumption.
  - constructor.
    intro H; apply FreeEqFby; apply freevar_laexp_in; apply H.
    inversion 1; apply freevar_laexp_in; assumption.
Qed.


Fixpoint memory_eq (mems: PS.t) (eq: equation) : PS.t :=
  match eq with
  | EqFby x _ _ => PS.add x mems
  | _ => mems
  end.

Definition memories (eqs: list equation) : PS.t :=
  List.fold_left memory_eq eqs PS.empty.

Inductive Is_memory_eq : ident -> equation -> Prop :=
| MemEqFby: forall x v e, Is_memory_eq x (EqFby x v e).

Definition Is_memory (eqs: list equation) (x: ident) : Prop :=
  List.Exists (Is_memory_eq x) eqs.



Fixpoint variable_eq (vars: PS.t) (eq: equation) : PS.t :=
  match eq with
  | EqDef x _   => PS.add x vars
  | EqApp x _ _ => PS.add x vars
  | EqFby _ _ _ => vars
  end.

Definition variables (eqs: list equation) : PS.t :=
  List.fold_left variable_eq eqs PS.empty.

Inductive Is_variable_eq : ident -> equation -> Prop :=
| VarEqDef: forall x e,   Is_variable_eq x (EqDef x e)
| VarEqApp: forall x f e, Is_variable_eq x (EqApp x f e).

Definition Is_variable (eqs: list equation) (x: ident) : Prop :=
  List.Exists (Is_variable_eq x) eqs.



Fixpoint defined_eq (defs: PS.t) (eq: equation) : PS.t :=
  match eq with
  | EqDef x _   => PS.add x defs
  | EqApp x _ _ => PS.add x defs
  | EqFby x _ _ => PS.add x defs
  end.

Definition defined (eqs: list equation) : PS.t :=
  List.fold_left defined_eq eqs PS.empty.

Inductive Is_defined_eq : ident -> equation -> Prop :=
| DefEqDef: forall x e,   Is_defined_eq x (EqDef x e)
| DefEqApp: forall x f e, Is_defined_eq x (EqApp x f e)
| DefEqFby: forall x v e, Is_defined_eq x (EqFby x v e).

Definition Is_defined (eqs: list equation) (x: ident) : Prop :=
  List.Exists (Is_defined_eq x) eqs.


(** The map containing global definitions. *)
Require Coq.FSets.FMapPositive.
Definition global := FSets.FMapPositive.PositiveMap.t node.

