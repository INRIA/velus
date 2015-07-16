Require Import Rustre.Common.


(** * Dataflow language *)

Inductive clock : Set :=
| Cbase : clock                           (** base clock *)
| Con : clock -> ident -> bool -> clock.  (** subclock *)

Record var_dec : Set := mk_var { v_name : ident;
                                 v_clock : clock }.

(** **  Syntax  **)

(* TODO: laexp: would be nicer if it were a record *)
Inductive laexp : Set :=
  | LAexp : clock -> lexp -> laexp
with lexp : Type :=
  | Econst : const -> lexp
  | Evar : ident -> lexp
  | Ewhen : laexp -> ident -> bool -> lexp.
(* External operators are missing *)

(* TODO: caexp: would be nicer if it were a record *)
Inductive caexp : Type :=
  | CAexp : clock -> cexp -> caexp
with cexp : Type :=
  | Emerge : ident -> caexp -> caexp -> cexp (* currently only binary merge *)
  | Eexp : lexp -> cexp.

(** **  Equations  **)

Inductive equation : Type :=
  | EqDef : ident -> caexp -> equation
  | EqApp : ident -> ident -> laexp -> equation
  | EqFby : ident -> const -> caexp -> equation. (* Lionel added this one *)

Record node : Type := mk_node {
  n_name : ident;
  n_input : var_dec;
  n_output : var_dec;
  n_eqs : list equation
}.

(** The map containing global definitions. *)
Require Coq.FSets.FMapPositive.
Definition global := FSets.FMapPositive.PositiveMap.t node.
