Require Import Rustre.Common.
Require Import Rustre.Operators.

Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.IsFree.
Require Import List.

(** * Free variables: decision procedure *)

(** 

Decision procedure for the [IsFree] predicate. We show that it is
equivalent to its specification.

Remark: This development is not formally part of the correctness proof.

 *)

(* TODO: use auto for the proofs. *)

Module Type DECIDE
       (Ids        : IDS)
       (Op         : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (Import IsF : ISFREE Ids Op Syn).

  Lemma Is_free_in_clock_disj:
    forall y ck x c, Is_free_in_clock y (Con ck x c)
                     <-> y = x \/ Is_free_in_clock y ck.
  Proof.
    intros y ck x c; split; intro HH.
    inversion_clear HH; [left; reflexivity|right; assumption].
    destruct HH as [HH|HH].
    rewrite HH; constructor.
    constructor (assumption).
  Qed.

  Lemma Is_free_in_when_disj:
    forall y e x c, Is_free_in_lexp y (Ewhen e x c)
                    <-> y = x \/ Is_free_in_lexp y e.
  Proof.
    intros y e x c; split; intro HH.
    inversion_clear HH; auto.
    destruct HH as [HH|HH].
    rewrite HH; constructor (fail).
    constructor (assumption).
  Qed.

  Fixpoint free_in_clock_dec (ck : clock) (T: PS.t)
    : { S | forall x, PS.In x S <-> (Is_free_in_clock x ck \/ PS.In x T) }.
    refine (
        match ck with
        | Cbase => exist _ T _
        | Con ck' x c =>
          match free_in_clock_dec ck' T with
          | exist S' HF => exist _ (PS.add x S') _
          end
        end).
    - intro x; split; intro HH.
      right; exact HH.
      destruct HH as [HH|HH]; [inversion HH|exact HH].
    - intro y; split; intro HH.
      + rewrite PS.add_spec in HH.
        destruct HH as [HH|HH].
        rewrite HH; left; constructor.
        apply HF in HH.
        destruct HH as [HH|HH]; [left|right].
        constructor (assumption). assumption.
      + rewrite Is_free_in_clock_disj in HH.
        apply or_assoc in HH.
        destruct HH as [HH|HH].
        rewrite HH; apply PS.add_spec; left; reflexivity.
        apply HF in HH; apply PS.add_spec; right; assumption.
  Defined.
  
  Fixpoint free_in_clock (ck : clock) (fvs: PS.t) : PS.t :=
    match ck with
    | Cbase => fvs
    | Con ck' x _ => free_in_clock ck' (PS.add x fvs)
    end.

  Fixpoint free_in_lexp (e: lexp) (fvs: PS.t) : PS.t :=
    match e with
    | Econst _ => fvs
    | Evar x _ => PS.add x fvs
    | Ewhen e x _ => free_in_lexp e (PS.add x fvs)
    | Eunop _ e _ => free_in_lexp e fvs
    | Ebinop _ e1 e2 _ => free_in_lexp e2 (free_in_lexp e1 fvs)
    end.

  Definition free_in_laexp (ck: clock)(le : lexp) (fvs : PS.t) : PS.t :=
    free_in_lexp le (free_in_clock ck fvs).

  Definition free_in_laexps (ck: clock)(les : lexps) (fvs : PS.t) : PS.t :=
    fold_left (fun fvs e => free_in_lexp e fvs) les (free_in_clock ck fvs).

  Fixpoint free_in_cexp (ce: cexp) (fvs: PS.t) : PS.t :=
    match ce with
    | Emerge i t f => free_in_cexp f (free_in_cexp t (PS.add i fvs))
    | Eite b t f => free_in_cexp f (free_in_cexp t (free_in_lexp b fvs))
    | Eexp e => free_in_lexp e fvs
    end.

  Definition free_in_caexp (ck: clock)(ce: cexp) (fvs: PS.t) : PS.t :=
    free_in_cexp ce (free_in_clock ck fvs).

  Fixpoint free_in_equation (eq: equation) (fvs: PS.t) : PS.t :=
    match eq with
    | EqDef _ ck cae    => free_in_caexp ck cae fvs
    | EqApp _ ck f laes => free_in_laexps ck laes fvs
    | EqFby _ ck v lae  => free_in_laexp ck lae fvs
    end.

  (** * Specification lemmas *) 

  Lemma free_in_clock_spec:
    forall x ck m, PS.In x (free_in_clock ck m)
                   <-> Is_free_in_clock x ck \/ PS.In x m.
  Proof.
    induction ck.
    - split; intuition;
        (match goal with H:Is_free_in_clock _ Cbase |- _ => inversion H end).
    - split; intro H0.
      + apply IHck in H0; destruct H0 as [H0|H0]; try apply PS.add_spec in H0;
          intuition; subst; intuition.
      + apply IHck; destruct H0 as [H0|H0]; inversion H0;
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
    intro x; induction e using lexp_ind;
      try now intro m; (split;
                        [
                          intro H0; try apply IHe in H0
                        | intro H0; try apply IHe
                       ]);
      try destruct H0 as [H0|H0];
      try apply free_in_clock_spec in H0;
      try inversion H0; subst;
        try apply PS.add_spec;
        solve [
            intuition
          | right; apply free_in_clock_spec; intuition
          | apply PS.add_spec in H1; destruct H1; subst; intuition
          | right; apply PS.add_spec; intuition ].
    intro m.
    split; intro HH.
    - simpl in HH.
      apply IHe2 in HH.
      destruct HH as [HH|HH]; [now intuition|].
      apply IHe1 in HH. intuition.
    - simpl.
      destruct HH as [HH|HH].
      + inversion_clear HH as [| | | |? ? ? ? ? Hf].
        apply IHe2.
        destruct Hf as [HH|HH]; intuition.
        right. apply IHe1; intuition.
      + apply IHe2; right; apply IHe1; intuition.
  Qed.          

  Lemma free_in_lexp_spec':
    forall x e, PS.In x (free_in_lexp e PS.empty)
                <-> Is_free_in_lexp x e.
  Proof.
    intros; pose proof (free_in_lexp_spec x e PS.empty);
      intuition not_In_empty.
  Qed.

  Lemma free_in_laexp_spec:
    forall x ck e m, PS.In x (free_in_laexp ck e m)
                     <-> Is_free_in_laexp x ck e \/ PS.In x m.
  Proof.
    destruct e; split; intros;
      repeat
        (match goal with
         | H:_ \/ _ |- _ => destruct H as [H|H]
         | H:PS.In _ (free_in_laexp _ _ _) |- _ => apply free_in_lexp_spec in H
         | H:PS.In _ (free_in_clock _ _) |- _ => apply free_in_clock_spec in H
         | |- PS.In _ (free_in_laexp _ _ _) => apply free_in_lexp_spec
         | H:Is_free_in_laexp _ _ _ |- _ => inversion_clear H
         | |- context[PS.In _ (free_in_clock _ _)] => rewrite free_in_clock_spec
         end);
      intuition.
  Qed.

  Lemma free_in_laexp_spec':
    forall x ck e, PS.In x (free_in_laexp ck e PS.empty)
                   <-> Is_free_in_laexp x ck e.
  Proof.
    intros; pose proof (free_in_laexp_spec x ck e PS.empty);
      intuition not_In_empty.
  Qed.

  Lemma free_in_fold_left_lexp_spec : forall x l m,
      PS.In x (fold_left (fun fvs e => free_in_lexp e fvs) l m) <->
      Exists (Is_free_in_lexp x) l \/ PS.In x m.
  Proof.
    Local Hint Constructors Exists.
    intros x l. induction l; intro m; simpl.
    - intuition.
      match goal with H:Exists _ nil |- _ => inversion H end.
    - rewrite IHl. rewrite free_in_lexp_spec.
      split; intros [H | H]; auto.
      + destruct H as [H | H]; auto.
      + inversion_clear H; auto.
  Qed.

  Lemma free_in_laexps_spec:
    forall x ck e m, PS.In x (free_in_laexps ck e m)
                     <-> Is_free_in_laexps x ck e \/ PS.In x m.
  Proof.
    intros x c l m. unfold free_in_laexps.
    rewrite free_in_fold_left_lexp_spec.
    rewrite free_in_clock_spec.
    split; intros [H | H]; auto; inversion H; auto.
  Qed.

  Lemma free_in_laexps_spec':
    forall x ck l, PS.In x (free_in_laexps ck l PS.empty)
                   <-> Is_free_in_laexps x ck l.
  Proof.
    intros; pose proof (free_in_laexps_spec x ck l PS.empty);
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
    intro x;
      induction e;
      intro m; simpl; split; intro H0;
        destruct_Is_free;
        subst; auto;
          try rewrite IHe2, IHe1;
          try rewrite free_in_lexp_spec;
          match goal with
          | H:Is_free_in_cexp _ _ |- _ => inversion_clear H
          | |- _ => idtac
          end;
          intuition.
  Qed.

  Lemma free_in_cexp_spec':
    forall x e, PS.In x (free_in_cexp e PS.empty)
                <-> Is_free_in_cexp x e.
  Proof.
    intros; pose proof (free_in_cexp_spec x e PS.empty);
      intuition not_In_empty.
  Qed.

  Lemma free_in_caexp_spec:
    forall x ck e m, PS.In x (free_in_caexp ck e m)
                     <-> Is_free_in_caexp x ck e \/ PS.In x m.
  Proof.
    destruct e; split; intros;
      repeat progress (match goal with
           | H:_ \/ _ |- _ => destruct H as [H|H]
           | H:PS.In _ _ |- _ => first [ apply free_in_cexp_spec in H
                                       | apply free_in_clock_spec in H ]
           | |- context [free_in_caexp _ _ _] => apply free_in_cexp_spec
           | H:Is_free_in_caexp _ _ _ |- _ => inversion_clear H
           | _ => solve [right; apply free_in_clock_spec; intuition
                        | intuition]
                       end).
  Qed.
  
  Lemma free_in_caexp_spec':
    forall x ck e, PS.In x (free_in_caexp ck e PS.empty)
                   <-> Is_free_in_caexp x ck e.
  Proof.
    intros; rewrite (free_in_caexp_spec x ck e PS.empty).
    intuition not_In_empty.
  Qed.

  Lemma free_in_equation_spec:
    forall x eq m, PS.In x (free_in_equation eq m)
                   <-> (Is_free_in_eq x eq \/ PS.In x m).
  Proof.
    destruct eq; split; intro H;
      repeat (match goal with
              | H:Is_free_in_eq _ _ |- _ => inversion_clear H
              | H:PS.In _ (free_in_equation _ _) |- _ =>
                apply free_in_caexp_spec in H
                || apply free_in_laexp_spec in H
                || apply free_in_laexps_spec in H
              | |- PS.In _ (free_in_equation _ _) =>
                apply free_in_caexp_spec
                || apply free_in_laexp_spec
                || apply free_in_laexps_spec
              | _ => intuition
              end).
  Qed.

  Lemma free_in_equation_spec':
    forall x eq, PS.In x (free_in_equation eq PS.empty)
               <-> Is_free_in_eq x eq.
  Proof.
    intros; rewrite (free_in_equation_spec x eq PS.empty).
    intuition not_In_empty.
  Qed.

End DECIDE.

Module DecideFun
       (Ids        : IDS)
       (Op         : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (Import IsF : ISFREE Ids Op Syn) <: DECIDE Ids Op Syn IsF.
  Include DECIDE Ids Op Syn IsF.
End DecideFun.