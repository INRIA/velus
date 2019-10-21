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

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.

From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import Permutation.

(** * Well clocked expressions *)

Module Type CECLOCKING
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import Syn  : CESYNTAX Op).

  Inductive SameVar : option ident -> exp -> Prop :=
  | SVNone: forall e,
      SameVar None e
  | SVSome: forall x ty,
      SameVar (Some x) (Evar x ty).

  Section WellClocked.

    Variable vars : list (ident * clock).

    Inductive wc_exp : exp -> clock -> Prop :=
    | Cconst:
        forall c,
          wc_exp (Econst c) Cbase
    | Cvar:
        forall x ck ty,
          In (x, ck) vars ->
          wc_exp (Evar x ty) ck
    | Cwhen:
        forall e x b ck,
          wc_exp e ck ->
          In (x, ck) vars ->
          wc_exp (Ewhen e x b) (Con ck x b)
    | Cunop:
        forall op e ck ty,
          wc_exp e ck ->
          wc_exp (Eunop op e ty) ck
    | Cbinop:
        forall op e1 e2 ck ty,
          wc_exp e1 ck ->
          wc_exp e2 ck ->
          wc_exp (Ebinop op e1 e2 ty) ck.

    Inductive wc_cexp : cexp -> clock -> Prop :=
    | Cmerge:
        forall x t f ck,
          In (x, ck) vars ->
          wc_cexp t (Con ck x true) ->
          wc_cexp f (Con ck x false) ->
          wc_cexp (Emerge x t f) ck
    | Cite:
        forall b t f ck,
          wc_exp b ck ->
          wc_cexp t ck ->
          wc_cexp f ck ->
          wc_cexp (Eite b t f) ck
    | Cexp:
        forall e ck,
          wc_exp e ck ->
          wc_cexp (Eexp e) ck.

  End WellClocked.

  (** ** Basic properties of clocking *)

  Lemma wc_clock_exp:
    forall vars le ck,
      wc_env vars ->
      wc_exp vars le ck ->
      wc_clock vars ck.
  Proof.
    induction le as [| |le IH | |] (* using exp_ind2 *).
    - inversion_clear 2; now constructor.
    - intros ck Hwc; inversion_clear 1 as [|? ? ? Hcv| | |].
      apply wc_env_var with (1:=Hwc) (2:=Hcv).
    - intros ck Hwc.
      inversion_clear 1 as [| |? ? ? ck' Hle Hcv | |].
      constructor; [now apply IH with (1:=Hwc) (2:=Hle)|assumption].
    - intros ck Hwc; inversion_clear 1; auto.
    - intros ck Hwc; inversion_clear 1; auto.
  Qed.

  Lemma wc_clock_cexp:
    forall vars ce ck,
      wc_env vars ->
      wc_cexp vars ce ck ->
      wc_clock vars ck.
  Proof.
    induction ce as [i ce1 IH1 ce2 IH2| |].
    - intros ck Hwc.
      inversion_clear 1 as [? ? ? ? Hcv Hct Hcf| |].
      apply IH1 with (1:=Hwc) in Hct.
      inversion_clear Hct; assumption.
    - intros ck Hwc; inversion_clear 1 as [|? ? ? ? Hl H1 H2|].
      now apply IHce1.
    - intros ck Hwc; inversion_clear 1 as [| |? ? Hck].
      apply wc_clock_exp with (1:=Hwc) (2:=Hck).
  Qed.

  Hint Constructors wc_clock wc_exp wc_cexp : nlclocking.
  Hint Resolve Forall_nil : nlclocking.

  Instance wc_exp_Proper:
    Proper (@Permutation (ident * clock) ==> @eq exp ==> @eq clock ==> iff)
           wc_exp.
  Proof.
    intros env' env Henv e' e He ck' ck Hck.
    rewrite He, Hck; clear He Hck e' ck'.
    revert ck.
    induction e;
      split; auto with nlclocking;
        inversion_clear 1;
        (rewrite Henv in * || rewrite <-Henv in * || idtac);
        try edestruct IHe;
        try edestruct IHe1, IHe2;
        auto with nlclocking.
  Qed.

  Instance wc_cexp_Proper:
    Proper (@Permutation (ident * clock) ==> @eq cexp ==> @eq clock ==> iff)
           wc_cexp.
  Proof.
    intros env' env Henv e' e He ck' ck Hck.
    rewrite He, Hck; clear He Hck e' ck'.
    revert ck.
    induction e;
      split; inversion_clear 1;
        (rewrite Henv in * || rewrite <-Henv in *);
         constructor; auto;
         now (rewrite <-IHe1 || rewrite IHe1
              || rewrite <-IHe2 || rewrite IHe2).
  Qed.

End CECLOCKING.

Module CEClockingFun
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import Syn  : CESYNTAX Op)
  <: CECLOCKING Ids Op Syn.
  Include CECLOCKING Ids Op Syn.
End CEClockingFun.
