Require Import PArith.
Require Import List.
Import List.ListNotations.
Open Scope positive.
Open Scope list.

Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.Example.
Require Import Rustre.Dataflow.Memories.
Require Import Rustre.Dataflow.WellFormed.
Require Import Rustre.Dataflow.WellFormed.Decide.

Example eqn1_well_sch: Is_well_sch (memories eqns1) 1 eqns1.
Proof.
  assert (well_sch (memories eqns1) 1 eqns1 = true) as HW by apply eq_refl.
  pose proof (well_sch_spec (memories eqns1) 1 eqns1) as HS.
  rewrite HW in HS.
  assumption.
Qed.

Example eqn2_well_sch: Is_well_sch (memories eqns2) 1 eqns2.
Proof.
  assert (well_sch (memories eqns2) 1 eqns2 = true) as HW by apply eq_refl.
  pose proof (well_sch_spec (memories eqns2) 1 eqns2) as HS.
  rewrite HW in HS.
  assumption.
Qed.
