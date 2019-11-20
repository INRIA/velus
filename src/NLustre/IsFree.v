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
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Coq Require Import List.

(** * Free variables *)

(**

The predicate [Is_free x t : Prop] states that the variable [x] is
used in the term [t]. If [t] is an equation, this collects the
variables in the right-hand side of the equation. In particular, if
[t] is [x = v0 fby x], [x] will (perhaps confusingly) be free.

 *)

Module Type ISFREE
       (Ids          : IDS)
       (Op           : OPERATORS)
       (Import CESyn : CESYNTAX     Op)
       (Import Syn   : NLSYNTAX Ids Op CESyn)
       (Import CEIsF : CEISFREE Ids Op CESyn).

  Inductive Is_free_in_eq : ident -> equation -> Prop :=
  | FreeEqDef:
      forall x ck ce i,
        Is_free_in_caexp i ck ce ->
        Is_free_in_eq i (EqDef x ck ce)
  | FreeEqApp:
      forall x f ck les i,
        Is_free_in_aexps i ck les ->
        Is_free_in_eq i (EqApp x ck f les None)
  | FreeEqReset:
      forall x f ck les i r ck_r,
        Is_free_in_aexps i ck les \/ r = i \/ Is_free_in_clock i ck_r ->
        Is_free_in_eq i (EqApp x ck f les (Some (r, ck_r)))
  | FreeEqFby:
      forall x v ck le i,
        Is_free_in_aexp i ck le ->
        Is_free_in_eq i (EqFby x ck v le).

  Hint Constructors Is_free_in_clock Is_free_in_exp
       Is_free_in_aexp Is_free_in_aexps Is_free_in_cexp
       Is_free_in_caexp Is_free_in_eq.

  (** * Decision procedure *)


  Fixpoint free_in_equation (eq: equation) (fvs: PS.t) : PS.t :=
    match eq with
    | EqDef _ ck cae      => free_in_caexp ck cae fvs
    | EqApp _ ck f laes r =>
      let fvs := free_in_aexps ck laes fvs in
      match r with
      | Some (x, ck_r) => PS.add x (free_in_clock ck_r fvs)
      | None => fvs
      end
    | EqFby _ ck v lae    => free_in_aexp ck lae fvs
    end.

  (** * Specification lemmas *)

  Lemma free_in_equation_spec:
    forall x eq m, PS.In x (free_in_equation eq m)
                   <-> (Is_free_in_eq x eq \/ PS.In x m).
  Proof.
    Local Ltac aux :=
      repeat (match goal with
              | H:Is_free_in_eq _ _ |- _ => inversion_clear H
              | H:PS.In _ (free_in_equation _ _) |- _ =>
                apply free_in_caexp_spec in H
                || apply free_in_aexp_spec in H
                || apply free_in_aexps_spec in H
              | |- PS.In _ (free_in_equation _ _) =>
                apply free_in_caexp_spec
                || apply free_in_aexp_spec
                || apply free_in_aexps_spec
              | _ => intuition; eauto
              end).

    destruct eq; split; intro H; aux.
    - destruct o as [(?&?)|]; aux.
      simpl in H.
      apply PS.add_spec in H as [|].
      + subst; left; eauto.
      + apply free_in_clock_spec in H as [|]; eauto.
        apply free_in_aexps_spec in H as [|]; aux.
    - destruct o; aux; simpl; apply PS.add_spec;
        rewrite free_in_clock_spec, free_in_aexps_spec; intuition.
    - subst; simpl. now apply PSF.add_1.
    - destruct o; aux; simpl; apply PS.add_spec;
        rewrite free_in_clock_spec, free_in_aexps_spec; intuition.
    - simpl; destruct o as [(?&?)|];
        try apply PS.add_spec; try rewrite free_in_clock_spec; try rewrite free_in_aexps_spec;
          auto.
  Qed.

  Lemma free_in_equation_spec':
    forall x eq, PS.In x (free_in_equation eq PS.empty)
               <-> Is_free_in_eq x eq.
  Proof.
    intros; rewrite (free_in_equation_spec x eq PS.empty).
    intuition.
  Qed.

End ISFREE.

Module IsFreeFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX     Op)
       (Syn   : NLSYNTAX Ids Op CESyn)
       (CEIsF : CEISFREE Ids Op CESyn)
       <: ISFREE Ids Op CESyn Syn CEIsF.
  Include ISFREE Ids Op CESyn Syn CEIsF.
End IsFreeFun.
