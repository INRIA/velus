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
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Morphisms.

Module Type CETYPING
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import Syn  : CESYNTAX Op).

  (** ** Clocks *)

  Section WellTyped.

    Variable vars : list (ident * type).

    Inductive wt_clock : clock -> Prop :=
    | wt_Cbase:
        wt_clock Cbase
    | wt_Con: forall ck x b,
        In (x, bool_type) vars ->
        wt_clock ck ->
        wt_clock (Con ck x b).

    Inductive wt_exp : exp -> Prop :=
    | wt_Econst: forall c,
        wt_exp (Econst c)
    | wt_Evar: forall x ty,
        In (x, ty) vars ->
        wt_exp (Evar x ty)
    | wt_Ewhen: forall e x b,
        In (x, bool_type) vars ->
        wt_exp e ->
        wt_exp (Ewhen e x b)
    | wt_Eunop: forall op e ty,
        type_unop op (typeof e) = Some ty ->
        wt_exp e ->
        wt_exp (Eunop op e ty)
    | wt_Ebinop: forall op e1 e2 ty,
        type_binop op (typeof e1) (typeof e2) = Some ty ->
        wt_exp e1 ->
        wt_exp e2 ->
        wt_exp (Ebinop op e1 e2 ty).

    Fixpoint typeofc (ce: cexp): type :=
      match ce with
      | Emerge x t f => typeofc t
      | Eite e t f   => typeofc t
      | Eexp e       => typeof e
      end.

    Inductive wt_cexp : cexp -> Prop :=
    | wt_Emerge: forall x t f,
        In (x, bool_type) vars ->
        typeofc t = typeofc f ->
        wt_cexp t ->
        wt_cexp f ->
        wt_cexp (Emerge x t f)
    | wt_Eite: forall e t f,
        typeof e = bool_type ->
        wt_exp e ->
        wt_cexp t ->
        wt_cexp f ->
        typeofc t = typeofc f ->
        wt_cexp (Eite e t f)
    | wt_Eexp: forall e,
        wt_exp e ->
        wt_cexp (Eexp e).

  End WellTyped.

  Hint Constructors wt_clock wt_exp wt_cexp.

  Lemma wt_clock_add:
    forall x v env ck,
      ~InMembers x env ->
      wt_clock env ck ->
      wt_clock ((x, v) :: env) ck.
  Proof.
    induction ck; auto.
    inversion 2.
    auto with datatypes.
  Qed.

  Instance wt_clock_Proper:
    Proper (@Permutation.Permutation (ident * type) ==> @eq clock ==> iff)
           wt_clock.
  Proof.
    intros env' env Henv ck' ck Hck.
    rewrite Hck; clear Hck ck'.
    induction ck.
    - split; auto.
    - destruct IHck.
      split; inversion_clear 1; constructor;
        try rewrite Henv in *;
        auto.
  Qed.

  Instance wt_exp_Proper:
    Proper (@Permutation.Permutation (ident * type) ==> @eq exp ==> iff)
           wt_exp.
  Proof.
    intros env' env Henv e' e He.
    rewrite He; clear He.
    induction e; try destruct IHe;
      try destruct IHe1, IHe2;
      split; auto;
        inversion_clear 1;
        (rewrite Henv in * || rewrite <-Henv in * || idtac);
        auto.
  Qed.

  Instance wt_exp_pointwise_Proper:
    Proper (@Permutation.Permutation (ident * type)
                                     ==> pointwise_relation exp iff) wt_exp.
  Proof.
    intros env' env Henv e.
    now rewrite Henv.
  Qed.

  Instance wt_cexp_Proper:
    Proper (@Permutation.Permutation (ident * type) ==> @eq cexp ==> iff)
           wt_cexp.
  Proof.
    intros env' env Henv e' e He.
    rewrite He; clear He.
    induction e; try destruct IHe1, IHe2;
      split; inversion_clear 1; try rewrite Henv in *;
        constructor; auto; now rewrite Henv in *.
  Qed.

End CETYPING.

Module CETypingFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Syn  : CESYNTAX Op)
       <: CETYPING Ids Op Syn.
  Include CETYPING Ids Op Syn.
End CETypingFun.
