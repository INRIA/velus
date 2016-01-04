Require Import Rustre.Common.
Require Import PArith.

Import List.ListNotations.
Open Scope list_scope.

(** * Dataflow language *)

Inductive clock : Set :=
| Cbase : clock                          (* base clock *)
| Con : clock -> ident -> bool -> clock. (* subclock *)

Implicit Type ck : clock.

(** ** Syntax *)

Inductive lexp : Type :=
  | Econst : const -> lexp
  | Evar : ident -> lexp
  | Ewhen : lexp -> ident -> bool -> lexp.
(* External operators are missing *)

Inductive laexp : Type :=
  | LAexp : clock -> lexp -> laexp.

Inductive laexps : Type :=
  | LAexps : clock -> list lexp -> laexps.

Implicit Type le: lexp.
Implicit Type lae: laexps.
Implicit Type laes: laexps.

Inductive cexp : Type :=
  | Emerge : ident -> cexp -> cexp -> cexp 
  | Eexp : lexp -> cexp.

Inductive caexp : Type :=
  | CAexp : clock -> cexp -> caexp.

Implicit Type ce: cexp.
Implicit Type cae: caexp.

(** ** Equations *)

Inductive equation : Type :=
  | EqDef : ident -> caexp -> equation
  | EqApp : ident -> ident -> laexps -> equation
  | EqFby : ident -> const -> laexp -> equation.

Implicit Type eqn: equation.

(** ** Node *)

Record node : Type := mk_node {
  n_name : ident;
  n_input : list ident;
  n_output : ident;
  n_eqs : list equation }.

Implicit Type N: node.

(** ** Program *)

Definition global := list node.

Implicit Type G: global.


Definition find_node (f : ident) : global -> option node :=
  List.find (fun n=> ident_eqb n.(n_name) f).


