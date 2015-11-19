Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.

(** 

The predicate [Is_free x t : Prop] states that the variable [x] is
used in the term [t]. If [t] is an equation, this collects the
variables in the right-hand side of the equation. In particular, if
[t] is [x = v0 fby x], [x] will (perhaps confusingly) be free.

 *)


(* TODO: use auto for the proofs. *)

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


(** * Specification lemmas *)

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

