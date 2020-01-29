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
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Clocks.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCISINIT
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX      Op)
       (Import Syn   : STCSYNTAX Ids Op CESyn).

  Inductive Is_init_in_tc: ident -> trconstr -> Prop :=
    InitTcNext:
      forall x ck e,
        Is_init_in_tc x (TcNext x ck e).

  Definition Is_init_in (x: ident) (tcs: list trconstr) : Prop :=
    Exists (Is_init_in_tc x) tcs.

  Lemma not_Is_init_in_cons:
    forall x tc tcs,
      ~ Is_init_in x (tc :: tcs) <-> ~ Is_init_in_tc x tc /\ ~ Is_init_in x tcs.
  Proof.
    split; intros HH.
    - split; intro; apply HH; unfold Is_init_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma inits_of_In:
    forall tcs x,
      Is_init_in x tcs <-> In x (inits_of tcs).
  Proof.
    induction tcs as [|[]]; simpl.
    - now setoid_rewrite Exists_nil.
    - setoid_rewrite <-IHtcs; split; try right; auto.
      inversion_clear 1 as [?? Init|]; try inv Init; auto.
    - setoid_rewrite <-IHtcs; split.
      + inversion_clear 1 as [?? Init|]; try inv Init; auto.
      + intros [E|?].
        * subst; left; constructor.
        * right; auto.
    - setoid_rewrite <-IHtcs; split; try right; auto.
      inversion_clear 1 as [?? Init|]; try inv Init; auto.
    - setoid_rewrite <-IHtcs; split; try right; auto.
      inversion_clear 1 as [?? Init|]; try inv Init; auto.
  Qed.

  Definition is_init_in_tc_b (x: ident) (tc: trconstr) : bool :=
    match tc with
    | TcNext y ck e => ident_eqb x y
    | _ => false
    end.

  Definition is_init_in_b (x: ident) (tcs: list trconstr) : bool :=
    existsb (is_init_in_tc_b x) tcs.

  Fact Is_init_in_tc_reflect:
    forall x tc,
      Is_init_in_tc x tc <-> is_init_in_tc_b x tc = true.
  Proof.
    destruct tc; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intro; subst; constructor.
  Qed.

  Corollary Is_init_in_reflect:
    forall x tcs,
      Is_init_in x tcs <-> is_init_in_b x tcs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Init); apply Is_init_in_tc_reflect in Init; eauto.
  Qed.

  Lemma Is_init_in_dec:
    forall x tcs,
      { Is_init_in x tcs } + { ~ Is_init_in x tcs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_init_in_reflect.
  Qed.

End STCISINIT.

Module StcIsInitFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX      Op)
       (Syn   : STCSYNTAX Ids Op CESyn)
<: STCISINIT Ids Op CESyn Syn.
  Include STCISINIT Ids Op CESyn Syn.
End StcIsInitFun.
