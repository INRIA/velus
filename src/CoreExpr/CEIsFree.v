(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Coq Require Import List.

(** * Free variables *)

(**

The predicate [Is_free x t : Prop] states that the variable [x] is
used in the term [t].
 *)

Module Type CEISFREE
       (Ids         : IDS)
       (Op          : OPERATORS)
       (Import Syn  : CESYNTAX Op).

  (* Warning: induction scheme is not strong enough. *)
  Inductive Is_free_in_exp : ident -> exp -> Prop :=
  | FreeEvar: forall x ty, Is_free_in_exp x (Evar x ty)
  | FreeEwhen1: forall e c cv x,
      Is_free_in_exp x e ->
      Is_free_in_exp x (Ewhen e c cv)
  | FreeEwhen2: forall e c cv,
      Is_free_in_exp c (Ewhen e c cv)
  | FreeEunop : forall c op e ty,
      Is_free_in_exp c e -> Is_free_in_exp c (Eunop op e ty)
  | FreeEbinop : forall c op e1 e2 ty,
      Is_free_in_exp c e1 \/ Is_free_in_exp c e2 -> Is_free_in_exp c (Ebinop op e1 e2 ty).

  Inductive Is_free_in_aexp : ident -> clock -> exp -> Prop :=
  | freeAexp1: forall ck e x,
      Is_free_in_exp x e  ->
      Is_free_in_aexp x ck e
  | freeAexp2: forall ck e x,
      Is_free_in_clock x ck ->
      Is_free_in_aexp x ck e.

  Inductive Is_free_in_aexps : ident -> clock -> list exp -> Prop :=
  | freeAexps1: forall ck les x,
      Exists (Is_free_in_exp x) les ->
      Is_free_in_aexps x ck les
  | freeAexps2: forall ck les x,
      Is_free_in_clock x ck ->
      Is_free_in_aexps x ck les.

  Inductive Is_free_in_cexp : ident -> cexp -> Prop :=
  | FreeEmerge_cond: forall i t f,
      Is_free_in_cexp i (Emerge i t f)
  | FreeEmerge_true: forall i t f x,
      Is_free_in_cexp x t ->
      Is_free_in_cexp x (Emerge i t f)
  | FreeEmerge_false: forall i t f x,
      Is_free_in_cexp x f ->
      Is_free_in_cexp x (Emerge i t f)
  (* | FreeEite: forall x b t f,  *)
  (*     Is_free_in_exp x b \/ Is_free_in_cexp x t \/ Is_free_in_cexp x f -> *)
  (*     Is_free_in_cexp x (Eite b t f) *)
  | FreeEite_cond: forall x b t f,
      Is_free_in_exp x b ->
      Is_free_in_cexp x (Eite b t f)
  | FreeEite_true: forall x b t f,
      Is_free_in_cexp x t ->
      Is_free_in_cexp x (Eite b t f)
  | FreeEite_false: forall x b t f,
      Is_free_in_cexp x f ->
      Is_free_in_cexp x (Eite b t f)
  | FreeEexp: forall e x,
      Is_free_in_exp x e ->
      Is_free_in_cexp x (Eexp e).

  Inductive Is_free_in_caexp : ident -> clock -> cexp -> Prop :=
  | FreeCAexp1: forall ck ce x,
      Is_free_in_cexp x ce ->
      Is_free_in_caexp x ck ce
  | FreeCAexp2: forall ck ce x,
      Is_free_in_clock x ck ->
      Is_free_in_caexp x ck ce.

  Hint Constructors Is_free_in_clock Is_free_in_exp
       Is_free_in_aexp Is_free_in_aexps Is_free_in_cexp
       Is_free_in_caexp.

  (** * Decision procedure *)

  Lemma Is_free_in_clock_disj:
    forall y ck x c, Is_free_in_clock y (Con ck x c)
                     <-> y = x \/ Is_free_in_clock y ck.
  Proof.
    intros y ck x c; split; intro HH.
    inversion_clear HH; [left; reflexivity|right; assumption].
    destruct HH as [HH|HH].
    rewrite HH; constructor.
    now constructor 2.
  Qed.

  Lemma Is_free_in_when_disj:
    forall y e x c, Is_free_in_exp y (Ewhen e x c)
                    <-> y = x \/ Is_free_in_exp y e.
  Proof.
    intros y e x c; split; intro HH.
    inversion_clear HH; auto.
    destruct HH as [HH|HH]; try rewrite HH; auto using Is_free_in_exp.
  Qed.

  Fixpoint free_in_clock_dec (ck : clock) (T: PS.t)
    : { S | forall x, PS.In x S <-> (Is_free_in_clock x ck \/ PS.In x T) }.
    refine (
        match ck with
        | Cbase => exist _ T _
        | Con ck' x c =>
          match free_in_clock_dec ck' T with
          | exist _ S' HF => exist _ (PS.add x S') _
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
        destruct HH as [HH|HH]; [left|right]; auto using Is_free_in_clock.
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

  Fixpoint free_in_exp (e: exp) (fvs: PS.t) : PS.t :=
    match e with
    | Econst _ => fvs
    | Evar x _ => PS.add x fvs
    | Ewhen e x _ => free_in_exp e (PS.add x fvs)
    | Eunop _ e _ => free_in_exp e fvs
    | Ebinop _ e1 e2 _ => free_in_exp e2 (free_in_exp e1 fvs)
    end.

  Definition free_in_aexp (ck: clock)(le : exp) (fvs : PS.t) : PS.t :=
    free_in_exp le (free_in_clock ck fvs).

  Definition free_in_aexps (ck: clock) (es : list exp) (fvs : PS.t) : PS.t :=
    fold_left (fun fvs e => free_in_exp e fvs) es (free_in_clock ck fvs).

  Fixpoint free_in_cexp (ce: cexp) (fvs: PS.t) : PS.t :=
    match ce with
    | Emerge i t f => free_in_cexp f (free_in_cexp t (PS.add i fvs))
    | Eite b t f => free_in_cexp f (free_in_cexp t (free_in_exp b fvs))
    | Eexp e => free_in_exp e fvs
    end.

  Definition free_in_caexp (ck: clock)(ce: cexp) (fvs: PS.t) : PS.t :=
    free_in_cexp ce (free_in_clock ck fvs).

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
    intros.
    rewrite (free_in_clock_spec x ck PS.empty).
    split; [intros [HH|HH]|intro HH]; intuition.
  Qed.

  Lemma free_in_exp_spec:
    forall x e m, PS.In x (free_in_exp e m)
                  <-> Is_free_in_exp x e \/ PS.In x m.
  Proof.
    intro x; induction e using exp_ind;
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

  Lemma free_in_exp_spec':
    forall x e, PS.In x (free_in_exp e PS.empty)
                <-> Is_free_in_exp x e.
  Proof.
    setoid_rewrite (free_in_exp_spec _ _ PS.empty); intuition.
  Qed.

  Lemma free_in_aexp_spec:
    forall x ck e m, PS.In x (free_in_aexp ck e m)
                     <-> Is_free_in_aexp x ck e \/ PS.In x m.
  Proof.
    destruct e; split; intros;
      repeat
        (match goal with
         | H:_ \/ _ |- _ => destruct H as [H|H]
         | H:PS.In _ (free_in_aexp _ _ _) |- _ => apply free_in_exp_spec in H
         | H:PS.In _ (free_in_clock _ _) |- _ => apply free_in_clock_spec in H
         | |- PS.In _ (free_in_aexp _ _ _) => apply free_in_exp_spec
         | H:Is_free_in_aexp _ _ _ |- _ => inversion_clear H
         | |- context[PS.In _ (free_in_clock _ _)] => rewrite free_in_clock_spec
         end);
      intuition.
  Qed.

  Lemma free_in_aexp_spec':
    forall x ck e, PS.In x (free_in_aexp ck e PS.empty)
                   <-> Is_free_in_aexp x ck e.
  Proof.
    setoid_rewrite (free_in_aexp_spec _ _ _ PS.empty); intuition.
  Qed.

  Lemma free_in_fold_left_exp_spec : forall x l m,
      PS.In x (fold_left (fun fvs e => free_in_exp e fvs) l m) <->
      Exists (Is_free_in_exp x) l \/ PS.In x m.
  Proof.
    Local Hint Constructors Exists.
    intros x l. induction l; intro m; simpl.
    - intuition.
      match goal with H:Exists _ nil |- _ => inversion H end.
    - rewrite IHl. rewrite free_in_exp_spec.
      split; intros [H | H]; auto.
      + destruct H as [H | H]; auto.
      + inversion_clear H; auto.
  Qed.

  Lemma free_in_aexps_spec:
    forall x ck e m, PS.In x (free_in_aexps ck e m)
                     <-> Is_free_in_aexps x ck e \/ PS.In x m.
  Proof.
    intros x c l m. unfold free_in_aexps.
    rewrite free_in_fold_left_exp_spec.
    rewrite free_in_clock_spec.
    split; intros [H | H]; auto; inversion H; auto.
  Qed.

  Lemma free_in_aexps_spec':
    forall x ck l, PS.In x (free_in_aexps ck l PS.empty)
                   <-> Is_free_in_aexps x ck l.
  Proof.
    setoid_rewrite (free_in_aexps_spec _ _ _ PS.empty); intuition.
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

           | H: PS.In _ (free_in_exp _ _) |- _ =>
             apply free_in_exp_spec in H

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
          try rewrite free_in_exp_spec;
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
    setoid_rewrite (free_in_cexp_spec _ _ PS.empty); intuition.
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
    setoid_rewrite (free_in_caexp_spec _ _ _ PS.empty); intuition.
  Qed.

End CEISFREE.

Module CEIsFreeFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Syn  : CESYNTAX Op)
       <: CEISFREE Ids Op Syn.
  Include CEISFREE Ids Op Syn.
End CEIsFreeFun.
