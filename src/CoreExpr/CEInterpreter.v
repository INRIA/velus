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

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Sorting.Permutation.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESemantics.

(** * Interpreter for Core Expresssions *)

Module Type CEINTERPRETER
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import CESyn : CESYNTAX        Op)
       (Import Str   : INDEXEDSTREAMS  Op OpAux)
       (Import CESem : CESEMANTICS Ids Op OpAux CESyn Str).

  (** ** Instantaneous semantics *)

  Section InstantInterpreter.

    Variable base : bool.
    Variable R: env.

    Definition interp_var_instant (x: ident): value :=
      match Env.find x R with
      | Some v => v
      | None => absent
      end.

    Definition interp_vars_instant (xs: list ident): list value :=
      map interp_var_instant xs.

    Fixpoint interp_clock_instant (c: clock): bool :=
      match c with
      | Cbase =>
        base
      | Con c x b =>
        let cb := interp_clock_instant c in
        match interp_var_instant x with
        | present xv =>
          match val_to_bool xv with
          | Some b' =>
            cb && b' ==b b
          | None => false
          end
        | absent =>
          false
        end
      end.

     Fixpoint interp_exp_instant (e: exp): value :=
      match e with
      | Econst c =>
        if base then present (sem_const c) else absent
      | Evar x _ =>
        interp_var_instant x
      | Ewhen e x b =>
        match interp_var_instant x, interp_exp_instant e with
        | present xv, present ev =>
          match val_to_bool xv with
          | Some b' => if b ==b b' then present ev else absent
          | None => absent
          end
        | _, _ => absent
        end
      | Eunop op e _ =>
        match interp_exp_instant e with
        | present v =>
          match sem_unop op v (typeof e) with
          | Some v' => present v'
          | None => absent
          end
        | absent => absent
        end
      | Ebinop op e1 e2 _ =>
        match interp_exp_instant e1, interp_exp_instant e2 with
        | present v1, present v2 =>
          match sem_binop op v1 (typeof e1) v2 (typeof e2) with
          | Some v => present v
          | None => absent
          end
        | _, _ => absent
        end
      end.

    Definition interp_exps_instant (les: list exp): list value :=
      map interp_exp_instant les.

    Fixpoint interp_cexp_instant (e: cexp): value :=
      match e with
      | Emerge x t f =>
        match interp_var_instant x, interp_cexp_instant t, interp_cexp_instant f with
        | present xv, present tv, absent =>
          if xv ==b true_val then present tv else absent
        | present xv, absent, present fv =>
          if xv ==b false_val then present fv else absent
        | _, _, _ => absent
        end

      | Eite b t f =>
        match interp_exp_instant b, interp_cexp_instant t, interp_cexp_instant f with
        | present bv, present tv, present fv =>
          match val_to_bool bv with
          | Some b' => present (if b' then tv else fv)
          | None => absent
          end
        | _, _, _ => absent
        end

      | Eexp e =>
        interp_exp_instant e
      end.

    Lemma interp_var_instant_sound:
      forall x v,
        sem_var_instant R x v ->
        v = interp_var_instant x.
    Proof.
      unfold interp_var_instant; now intros * ->.
    Qed.

    Ltac rw_exp_helper :=
      repeat match goal with
             | _: sem_var_instant R ?x ?v |- context[interp_var_instant ?x] =>
               erewrite <-(interp_var_instant_sound x v); eauto; simpl
             | H: val_to_bool ?x = _ |- context[val_to_bool ?x] =>
               rewrite H
             | H: sem_unop ?op ?c ?t = _ |- context[sem_unop ?op ?c ?t] =>
               rewrite H
             | H: sem_binop ?op ?c1 ?t1 ?c2 ?t2 = _ |- context[sem_binop ?op ?c1 ?t1 ?c2 ?t2] =>
               rewrite H
          end.

    Lemma interp_vars_instant_sound:
      forall xs vs,
        sem_vars_instant R xs vs ->
        vs = interp_vars_instant xs.
    Proof.
      unfold sem_vars_instant, interp_vars_instant.
      induction 1; auto; simpl; rw_exp_helper; f_equal; auto.
    Qed.

    Lemma interp_clock_instant_sound:
      forall c b,
        sem_clock_instant base R c b ->
        b = interp_clock_instant c.
    Proof.
      induction 1; auto; simpl; rw_exp_helper;
        rewrite <-IHsem_clock_instant; destruct b; auto.
    Qed.

    Lemma interp_exp_instant_sound:
      forall e v,
        sem_exp_instant base R e v ->
        v = interp_exp_instant e.
    Proof.
      induction 1; simpl;
        try rewrite <-IHsem_exp_instant;
        try rewrite <-IHsem_exp_instant1;
        try rewrite <-IHsem_exp_instant2;
        rw_exp_helper; auto;
          destruct b; auto.
    Qed.

    Lemma interp_exps_instant_sound:
      forall es vs,
        sem_exps_instant base R es vs ->
        vs = interp_exps_instant es.
    Proof.
      induction 1; simpl; auto.
      f_equal; auto.
      now apply interp_exp_instant_sound.
    Qed.

    Ltac rw_cexp_helper :=
      repeat (rw_exp_helper;
              repeat match goal with
                     | _: sem_exp_instant base R ?e ?v |- context[interp_exp_instant ?e] =>
                       erewrite <-(interp_exp_instant_sound e v); eauto; simpl
                     end).

    Lemma interp_cexp_instant_sound:
      forall e v,
        sem_cexp_instant base R e v ->
        v = interp_cexp_instant e.
    Proof.
      induction 1; simpl;
        try rewrite <-IHsem_cexp_instant;
        try rewrite <-IHsem_cexp_instant1;
        try rewrite <-IHsem_cexp_instant2;
        rw_cexp_helper;
        try rewrite equiv_decb_refl; auto;
          destruct b; auto.
    Qed.

    Definition interp_annotated_instant {A} (interp: A -> value) (ck: clock) (a: A): value :=
      if interp_clock_instant ck then
        interp a
      else
        absent.

    Definition interp_caexp_instant (ck: clock) (ce: cexp) : value :=
      interp_annotated_instant (interp_cexp_instant) ck ce.

    Lemma interp_caexp_instant_sound:
      forall ck e v,
        sem_caexp_instant base R ck e v ->
        v = interp_caexp_instant ck e.
    Proof.
      unfold interp_caexp_instant, interp_annotated_instant.
      induction 1; erewrite <-interp_clock_instant_sound; eauto; simpl; auto.
      apply interp_cexp_instant_sound; auto.
    Qed.

    Definition interp_aexp_instant (ck: clock) (e: exp) : value :=
      interp_annotated_instant (interp_exp_instant) ck e.

    Lemma interp_aexp_instant_sound:
      forall ck e v,
        sem_aexp_instant base R ck e v ->
        v = interp_aexp_instant ck e.
    Proof.
      unfold interp_aexp_instant, interp_annotated_instant.
      induction 1; erewrite <-interp_clock_instant_sound; eauto; simpl; auto.
      apply interp_exp_instant_sound; auto.
    Qed.

  End InstantInterpreter.

  (** ** Liftings of instantaneous semantics *)

  Section LiftInterpreter.

    Variable bk : stream bool.
    Variable H: history.

    Definition lift {A B} (interp: bool -> env -> A -> B) x: stream B :=
      fun n => interp (bk n) (H n) x.

    Definition lift' {A B} (interp: env -> A -> B) x: stream B :=
      fun n => interp (H n) x.

    Definition interp_clock (ck: clock): stream bool :=
      lift interp_clock_instant ck.

    Definition interp_var (x: ident): stream value :=
      lift' interp_var_instant x.

    Definition interp_vars (xs: list ident): stream (list value) :=
      lift' interp_vars_instant xs.

    Definition interp_exp (e: exp): stream value :=
      lift interp_exp_instant e.

    Definition interp_exps (e: list exp): stream (list value) :=
      lift interp_exps_instant e.

    Definition interp_exps' (e: list exp): list (stream value) :=
      map interp_exp e.

    Lemma interp_exps'_sound:
      forall es ess,
        sem_exps bk H es ess ->
        Forall2 (sem_exp bk H) es (interp_exps' es).
    Proof.
      induction es; intros * Sem; simpl; auto.
      constructor.
      - intro n; specialize (Sem n); inv Sem.
        unfold interp_exp, lift.
        erewrite <-interp_exp_instant_sound; eauto.
      - eapply IHes.
        intro n; specialize (Sem n); inv Sem.
        instantiate (1 := fun n => tl (ess n)).
        simpl.
        rewrite <-H2; simpl; auto.
    Qed.

    Definition interp_cexp (e: cexp): stream value :=
      lift interp_cexp_instant e.

    Definition interp_caexp (ck: clock) (e: cexp): stream value :=
      lift (fun base R => interp_caexp_instant base R ck) e.

    Definition interp_aexp (ck: clock) (e: exp): stream value :=
      lift (fun base R => interp_aexp_instant base R ck) e.

    Lemma lift_sound:
      forall {A B} (sem: bool -> env -> A -> B -> Prop) interp x xs,
        (forall b R x v, sem b R x v -> v = interp b R x) ->
        CESem.lift bk H sem x xs ->
        xs ≈ lift interp x.
    Proof.
      intros * Instant Sem n.
      specialize (Sem n); unfold lift; auto.
    Qed.

    Lemma lift'_sound:
      forall {A B} (sem: env -> A -> B -> Prop) interp x xs,
        (forall R x v, sem R x v -> v = interp R x) ->
        CESem.lift' H sem x xs ->
        xs ≈ lift' interp x.
    Proof.
      intros * Instant Sem n.
      specialize (Sem n); unfold lift'; auto.
    Qed.

    Corollary interp_clock_sound:
      forall ck bs,
        sem_clock bk H ck bs ->
        bs ≈ interp_clock ck.
    Proof.
      intros; eapply lift_sound; eauto;
        apply interp_clock_instant_sound.
    Qed.

    Corollary interp_var_sound:
      forall x vs,
        sem_var H x vs ->
        vs ≈ interp_var x.
    Proof.
      intros; eapply lift'_sound; eauto;
        apply interp_var_instant_sound.
    Qed.

    Corollary interp_vars_sound:
      forall xs vss,
        sem_vars H xs vss ->
        vss ≈ interp_vars xs.
    Proof.
      intros; eapply lift'_sound; eauto;
        apply interp_vars_instant_sound.
    Qed.

    Corollary interp_exp_sound:
      forall e vs,
        sem_exp bk H e vs ->
        vs ≈ interp_exp e.
    Proof.
      intros; eapply lift_sound; eauto;
        apply interp_exp_instant_sound.
    Qed.

    Corollary interp_exps_sound:
      forall es vss,
        sem_exps bk H es vss ->
        vss ≈ interp_exps es.
    Proof.
      intros; eapply lift_sound; eauto;
        apply interp_exps_instant_sound.
    Qed.

    Corollary interp_cexp_sound:
      forall e vs,
        sem_cexp bk H e vs ->
        vs ≈ interp_cexp e.
    Proof.
      intros; eapply lift_sound; eauto;
        apply interp_cexp_instant_sound.
    Qed.

    Corollary interp_aexp_sound:
      forall e ck vs,
        sem_aexp bk H ck e vs ->
        vs ≈ interp_aexp ck e.
    Proof.
      intros; eapply lift_sound; eauto.
      intros; apply interp_aexp_instant_sound; auto.
    Qed.

    Corollary interp_caexp_sound:
      forall e ck vs,
        sem_caexp bk H ck e vs ->
        vs ≈ interp_caexp ck e.
    Proof.
      intros; eapply lift_sound; eauto.
      intros; apply interp_caexp_instant_sound; auto.
    Qed.
    (* Definition interp_annotated {A} (interp_instant: bool -> env -> A -> value) (ck: clock) (a: A): stream value := *)
    (*   lift (fun base R => interp_annotated_instant base R interp_instant ck) a. *)

  End LiftInterpreter.

End CEINTERPRETER.

Module CEInterpreterFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import CESyn : CESYNTAX        Op)
       (Import Str   : INDEXEDSTREAMS  Op OpAux)
       (Import CESem : CESEMANTICS Ids Op OpAux CESyn Str)
       <: CEINTERPRETER Ids Op OpAux CESyn Str CESem.
  Include CEINTERPRETER Ids Op OpAux CESyn Str CESem.
End CEInterpreterFun.
