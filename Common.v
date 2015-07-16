Require Import Coq.FSets.FMapPositive.
Require Import PArith.


(** * Common definitions *)


Definition ident := positive.

Inductive const : Set :=
| Cint : BinInt.Z -> const
| Cbool : bool -> const.

Coercion Cint : BinInt.Z >-> const.
Coercion Cbool : bool >-> const.