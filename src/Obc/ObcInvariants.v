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
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import Obc.ObcSemantics.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type OBCINVARIANTS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import SynObc: Velus.Obc.ObcSyntax.OBCSYNTAX Ids Op OpAux)
       (Import SemObc: Velus.Obc.ObcSemantics.OBCSEMANTICS Ids Op OpAux SynObc).

  (** ** Determine whether an Obc command can modify a variable. *)

  Inductive Can_write_in : ident -> stmt -> Prop :=
  | CWIAssign: forall x e,
      Can_write_in x (Assign x e)
  | CWIAssignSt: forall x e,
      Can_write_in x (AssignSt x e)
  | CWIIfteTrue: forall x e s1 s2,
      Can_write_in x s1 ->
      Can_write_in x (Ifte e s1 s2)
  | CWIIfteFalse: forall x e s1 s2,
      Can_write_in x s2 ->
      Can_write_in x (Ifte e s1 s2)
  | CWICall_ap: forall x xs cls i f es,
      In x xs ->
      Can_write_in x (Call xs cls i f es)
  | CWIComp1: forall x s1 s2,
      Can_write_in x s1 ->
      Can_write_in x (Comp s1 s2)
  | CWIComp2: forall x s1 s2,
      Can_write_in x s2 ->
      Can_write_in x (Comp s1 s2).

  Lemma cannot_write_in_Ifte:
    forall x e s1 s2,
      ~ Can_write_in x (Ifte e s1 s2)
      <->
      ~ Can_write_in x s1 /\ ~ Can_write_in x s2.
  Proof.
    Hint Constructors Can_write_in.
    intros; split; intro; try (intro HH; inversion_clear HH); intuition.
  Qed.

  Lemma Can_write_in_Comp:
    forall x s1 s2,
      Can_write_in x (Comp s1 s2) <-> (Can_write_in x s1 \/ Can_write_in x s2).
  Proof.
    split; intros HH.
    - inversion_clear HH; auto.
    - destruct HH; auto.
  Qed.

  Lemma cannot_write_in_Comp:
    forall x s1 s2,
      ~ Can_write_in x (Comp s1 s2)
      <->
      ~ Can_write_in x s1 /\ ~ Can_write_in x s2.
  Proof.
    Hint Constructors Can_write_in.
    intros; split; intro; try (intro HH; inversion_clear HH); intuition.
  Qed.

  Ltac cannot_write :=
    repeat progress
           match goal with
           | |- forall x, Is_free_in_exp x _ -> _ => intros
           | Hfw: (forall x, Is_free_in_exp x ?e -> _),
                  Hfree: Is_free_in_exp ?x ?e |- _
             => pose proof (Hfw x Hfree); clear Hfw
           | |- _ /\ _ => split
           | |- ~Can_write_in _ _ => intro
           | H: Can_write_in _ (Comp _ _) |- _ => inversion_clear H
           | _ => now intuition
           end.

  Lemma cannot_write_exp_eval:
    forall prog s me ve me' ve' e v,
      (forall x, Is_free_in_exp x e -> ~ Can_write_in x s)
      -> exp_eval me ve e v
      -> stmt_eval prog me ve s (me', ve')
      -> exp_eval me' ve' e v.
  Proof.
    Hint Constructors Is_free_in_exp Can_write_in exp_eval.
    induction s; intros me ve me' ve' e' v Hfree Hexp Hstmt.
    - inv Hstmt.
      rewrite <-exp_eval_extend_venv; auto.
      intro Habs. apply (Hfree i); eauto.
    - inv Hstmt.
      eapply exp_eval_extend_menv; eauto.
      intro Habs. apply (Hfree i); auto.
    - inv Hstmt. destruct b; [eapply IHs1|eapply IHs2];
                   try eassumption; try now cannot_write.
    - inv Hstmt.
      match goal with
      | Hs1: stmt_eval _ _ _ s1 _,
             Hs2: stmt_eval _ _ _ s2 _ |- _
        => apply IHs1 with (2:=Hexp) in Hs1;
             [apply IHs2 with (2:=Hs1) (3:=Hs2)|];
             now cannot_write
      end.
    - inv Hstmt.
      apply exp_eval_extend_menv_by_obj.
      rewrite exp_eval_adds_opt_extend_venv; auto.
      intros x Hin Hfree'. apply Hfree in Hfree'.
      auto.
    - now inv Hstmt.
  Qed.

  Lemma Can_write_in_Ifte:
    forall e s1 s2 x,
      Can_write_in x (Ifte e s1 s2) <-> (Can_write_in x s1 \/ Can_write_in x s2).
  Proof.
    split; [inversion_clear 1|intros [HH|HH]]; auto.
  Qed.

  (** ** Assert that an Obc command never writes to a variable more than once. *)

  Inductive No_Overwrites : stmt -> Prop :=
  | NoOAssign: forall x e,
      No_Overwrites (Assign x e)
  | NoOAssignSt: forall x e,
      No_Overwrites (AssignSt x e)
  | NoOIfte: forall e s1 s2,
      No_Overwrites s1 ->
      No_Overwrites s2 ->
      No_Overwrites (Ifte e s1 s2)
  | NoOCall: forall xs cls i f es,
      No_Overwrites (Call xs cls i f es)
  | NoOComp: forall s1 s2,
      (forall x, Can_write_in x s1 -> ~Can_write_in x s2) ->
      (forall x, Can_write_in x s2 -> ~Can_write_in x s1) ->
      No_Overwrites s1 ->
      No_Overwrites s2 ->
      No_Overwrites (Comp s1 s2)
  | NoOSkip:
      No_Overwrites Skip.

  Hint Constructors No_Overwrites.

  Lemma cannot_write_in_No_Overwrites:
    forall s,
      (forall x, ~Can_write_in x s) -> No_Overwrites s.
  Proof.
    induction s; auto; intro HH.
    - setoid_rewrite cannot_write_in_Ifte in HH.
      constructor; (apply IHs1 || apply IHs2);
        intros x; specialize (HH x); intuition.
    - setoid_rewrite cannot_write_in_Comp in HH.
      constructor; try (apply IHs1 || apply IHs2);
        intros x Hcw; specialize (HH x); intuition.
  Qed.

  (** ** Assert that Obc calls never involve undefined variables. *)

  Inductive No_Naked_Vars : stmt -> Prop :=
  | NNVAssign: forall x e,
      No_Naked_Vars (Assign x e)
  | NNVAssignSt: forall x e,
      No_Naked_Vars (AssignSt x e)
  | NNVIfte: forall e s1 s2,
      No_Naked_Vars s1 ->
      No_Naked_Vars s2 ->
      No_Naked_Vars (Ifte e s1 s2)
  | NNVCall: forall xs cls i f es,
      Forall (fun e => forall x ty, e <> Var x ty) es ->
      No_Naked_Vars (Call xs cls i f es)
  | NNVComp: forall s1 s2,
      No_Naked_Vars s1 ->
      No_Naked_Vars s2 ->
      No_Naked_Vars (Comp s1 s2)
  | NNVSkip:
      No_Naked_Vars Skip.

  Hint Constructors No_Naked_Vars.

  Lemma stmt_eval_mono':
    forall p,
      (forall ome ome' clsid f vos rvos,
          Forall (fun vo => vo <> None) vos ->
          stmt_call_eval p ome clsid f vos ome' rvos ->
          Forall (fun x => x <> None) rvos) ->
      forall s me ve me' ve',
        No_Naked_Vars s ->
        stmt_eval p me ve s (me', ve') ->
        forall x, Env.In x ve -> Env.In x ve'.
  Proof.
    intros p Hcall.
    induction s; intros * Hnnv Heval x Hin; inv Heval; inv Hnnv; eauto.
    - destruct b; eauto.
    - match goal with H:stmt_call_eval _ _ _ _ _ _ _ |- _ => rename H into He end.
      apply Hcall in He; eauto using Env.adds_opt_mono, Forall2_exp_eval_not_None.
  Qed.

  Lemma no_vars_in_args_spec:
    forall me ve es vos,
      Forall2 (exp_eval me ve) es vos ->
      Forall (fun e => forall x ty, e <> Var x ty) es ->
      Forall (fun vo => vo <> None) vos.
  Proof.
    induction 1 as [|???? Exp]; auto.
    inversion_clear 1 as [|?? E].
    constructor; auto.
    intro; subst.
    inv Exp; eapply E; eauto.
  Qed.

End OBCINVARIANTS.

Module ObcInvariantsFun
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX Op)
       (Import SynObc: Velus.Obc.ObcSyntax.OBCSYNTAX Ids Op OpAux)
       (Import SemObc: Velus.Obc.ObcSemantics.OBCSEMANTICS Ids Op OpAux SynObc)
       <: OBCINVARIANTS Ids Op OpAux SynObc SemObc.

  Include OBCINVARIANTS Ids Op OpAux SynObc SemObc.

End ObcInvariantsFun.
