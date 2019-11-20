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

Module Type STCISVARIABLE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX     Op)
       (Import Syn   : STCSYNTAX Ids Op CESyn).

  Inductive Is_variable_in_tc: ident -> trconstr -> Prop :=
  | VarTcDef:
      forall x ck e,
        Is_variable_in_tc x (TcDef x ck e)
  | VarTcCall:
      forall x i xs ck rst f es,
        In x xs ->
        Is_variable_in_tc x (TcCall i xs ck rst f es).

  Definition Is_variable_in (x: ident) (tcs: list trconstr) : Prop :=
    Exists (Is_variable_in_tc x) tcs.

  Lemma Is_variable_in_variables:
    forall tcs x,
      Is_variable_in x tcs <-> In x (variables tcs).
  Proof.
    unfold variables.
    induction tcs as [|[]]; simpl.
    - split; try contradiction; inversion 1.
    - split.
      + inversion_clear 1 as [?? Var|]; try inv Var; auto.
        right; apply IHtcs; auto.
      + intros [E|].
        * subst; left; constructor.
        * right; apply IHtcs; auto.
    - setoid_rewrite <-IHtcs; split.
      + inversion_clear 1 as [?? Var|]; auto; inv Var.
      + right; auto.
    - setoid_rewrite <-IHtcs; split.
      + inversion_clear 1 as [?? Var|]; auto; inv Var.
      + right; auto.
    - split.
      + inversion_clear 1 as [?? Var|]; try inv Var.
        * apply in_app; auto.
        * apply in_app; right; apply IHtcs; auto.
      + rewrite in_app; intros [?|?].
        * left; constructor; auto.
        * right; apply IHtcs; auto.
  Qed.

  Definition is_variable_in_tc_b (x: ident) (tc: trconstr) : bool :=
    match tc with
    | TcDef x' _ _ => ident_eqb x x'
    | TcCall _ xs _ _ _ _ => existsb (ident_eqb x) xs
    | _ => false
    end.

  Fact Is_variable_in_tc_reflect:
    forall x tc,
      Is_variable_in_tc x tc <-> is_variable_in_tc_b x tc = true.
  Proof.
    destruct tc; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intro; subst; constructor.
    - inversion_clear 1.
      apply existsb_exists; eexists; split; eauto.
      apply ident_eqb_refl.
    - rewrite existsb_exists; intros (?&?& E).
      apply ident_eqb_eq in E; subst.
      constructor; auto.
  Qed.

  Lemma Is_variable_in_tc_dec:
    forall x tc,
      { Is_variable_in_tc x tc } + { ~ Is_variable_in_tc x tc }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_variable_in_tc_reflect.
  Qed.

  (* Definition variables_tc (vars: PS.t) (tc: trconstr) : PS.t := *)
  (*   match tc with *)
  (*   | TcDef x _ _         => PS.add x vars *)
  (*   | TcCall _ xs _ _ _ _ => ps_adds xs vars *)
  (*   | _ => vars *)
  (*   end. *)

  (* Lemma variables_tc_empty: *)
  (*   forall x tc vars, *)
  (*     PS.In x (variables_tc vars tc) *)
  (*     <-> PS.In x (variables_tc PS.empty tc) \/ PS.In x vars. *)
  (* Proof. *)
  (*   split; intro Hin. *)
  (*   - destruct tc; simpl in *; auto. *)
  (*     + apply PSE.MP.Dec.F.add_iff in Hin as [|]; subst; intuition. *)
  (*     + rewrite ps_adds_spec in *; tauto. *)
  (*   - destruct tc; simpl in *; destruct Hin as [Hin|Hin]; auto. *)
  (*     + rewrite PSE.MP.Dec.F.add_iff in *; intuition; pose proof (not_In_empty x); contradiction. *)
  (*     + rewrite PSE.MP.Dec.F.add_iff; auto. *)
  (*     + pose proof (not_In_empty x); contradiction. *)
  (*     + pose proof (not_In_empty x); contradiction. *)
  (*     + rewrite ps_adds_spec in *; intuition; pose proof (not_In_empty x); contradiction. *)
  (*     + rewrite ps_adds_spec; tauto. *)
  (* Qed. *)

End STCISVARIABLE.

Module StcIsVariableFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX     Op)
       (Syn   : STCSYNTAX Ids Op CESyn)
<: STCISVARIABLE Ids Op CESyn Syn.
  Include STCISVARIABLE Ids Op CESyn Syn.
End StcIsVariableFun.
