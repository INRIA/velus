Require Import Rustre.Common.


(** * Dataflow language *)

Inductive clock : Set :=
| Cbase : clock                           (** base clock *)
| Con : clock -> ident -> bool -> clock.  (** subclock *)

Record var_dec : Set := mk_var { v_name :> ident;
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
  | EqFby : ident -> const -> var_dec -> equation.
  (* EqFby only on variables to allow for a simpler translation
     as a name would already exist for the translation before the time shift. *)

Record node : Type := mk_node {
  n_name : ident;
  n_input : var_dec;
  n_output : var_dec;
  n_eqs : list equation
}.

(** The map containing global definitions. *)
Require Coq.FSets.FMapPositive.
Definition global := FSets.FMapPositive.PositiveMap.t node.


Definition lexp_ind2 := fun (P : lexp -> Prop) f_const f_var f_when =>
  fix F (l : lexp) : P l :=
    match l as l0 return (P l0) with
      | Econst c => f_const c
      | Evar i => f_var i
      | Ewhen (LAexp ck le) i b => f_when ck le i b (F le)
    end.

Definition cexp_ind2 := fun (P : cexp -> Prop) f_merge f_exp =>
  fix F c : P c :=
    match c as c0 return (P c0) with
      | Emerge x (CAexp ck1 ce1) (CAexp ck2 ce2) => f_merge x ck1 ce1 ck2 ce2 (F ce1) (F ce2)
      | Eexp le => f_exp le
    end.

