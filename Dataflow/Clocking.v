
Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Definition clockenv := PM.t clock.

Implicit Type C: clockenv.

Inductive clk_var C (x: ident) ck: Prop :=
| Cv:
    PM.find x C = Some ck ->
    clk_var C x ck.

Inductive clk_lexp C: lexp -> clock -> Prop :=
| Cconst:
    forall c,
      clk_lexp C (Econst c) Cbase
| Cvar:
    forall x ck,
      clk_var C x ck ->
      clk_lexp C (Evar x) ck
| Cwhen:
    forall e x b ck,
      clk_lexp C e ck ->
      clk_var C x ck ->
      clk_lexp C (Ewhen e x b) (Con ck x b).

Inductive clk_cexp C: cexp -> clock -> Prop :=
| Cmerge:
    forall x t f ck,
      clk_var C x ck ->
      clk_cexp C t (Con ck x true) ->
      clk_cexp C f (Con ck x false) ->
      clk_cexp C (Emerge x t f) ck
| Cexp:
    forall e ck,
      clk_lexp C e ck ->
      clk_cexp C (Eexp e) ck.

Inductive Well_clocked_eq C: equation -> Prop :=
| CEqDef:
    forall x ck ce,
      clk_var C x ck ->
      clk_cexp C ce ck ->
      Well_clocked_eq C (EqDef x (CAexp ck ce))
| CEqApp:
    forall x ck f le,
      clk_var C x ck ->
      clk_lexp C le ck ->
      Well_clocked_eq C (EqApp x f (LAexp ck le))
| CEqFby:
    forall x ck v0 le,
      clk_var C x ck ->
      clk_lexp C le ck ->
      Well_clocked_eq C (EqFby x v0 (LAexp ck le)).

Inductive Well_clocked_node C: node -> Prop :=
| SNode:
    forall f i o eqs,
      Forall (Well_clocked_eq C) eqs ->
      clk_var C i Cbase ->
      clk_var C o Cbase ->
      Well_clocked_node C (mk_node f i o eqs).

Definition Well_clocked G : Prop :=
  Forall (fun nd=> exists C, Well_clocked_node C nd) G.

