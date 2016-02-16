Require Import Rustre.Common.
Require Import PArith.
Require Import Rustre.Nelist.


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

Definition lexps := nelist lexp.

Inductive cexp : Type :=
  | Emerge : ident -> cexp -> cexp -> cexp 
  | Eexp : lexp -> cexp.

Implicit Type le: lexp.
Implicit Type les: lexps.
Implicit Type ce: cexp.

(** ** Equations *)

Inductive equation : Type :=
  | EqDef : ident -> clock -> cexp -> equation
  | EqApp : ident -> clock -> ident -> lexps -> equation
  | EqFby : ident -> clock -> const -> lexp -> equation.

Implicit Type eqn: equation.

(** ** Node *)

Record node : Type := mk_node {
  n_name : ident;
  n_input : nelist ident;
  n_output : ident;
  n_eqs : list equation }.

Implicit Type N: node.

(** ** Program *)

Definition global := list node.

Implicit Type G: global.

Definition find_node (f : ident) : global -> option node :=
  List.find (fun n=> ident_eqb n.(n_name) f).
