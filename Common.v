Require Import Coq.FSets.FMapPositive.
Require Coq.MSets.MSets.
Require Import PArith.

(** * Common definitions *)

Module PS := Coq.MSets.MSetPositive.PositiveSet.
Module PM := Coq.FSets.FMapPositive.PositiveMap.

Definition ident := positive.

Inductive const : Set :=
| Cint : BinInt.Z -> const
| Cbool : bool -> const.