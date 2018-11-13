Require Import Velus.Common.
Require Import Velus.Operators.

(** * The NLustre dataflow language *)

Module Type NLEXPRSYNTAX (Import Op: OPERATORS).

  (** ** Expressions *)

  Inductive lexp : Type :=
  | Econst : const -> lexp
  | Evar   : ident -> type -> lexp
  | Ewhen  : lexp -> ident -> bool -> lexp
  | Eunop  : unop -> lexp -> type -> lexp
  | Ebinop : binop -> lexp -> lexp -> type -> lexp.

  Definition lexps := list lexp.

  (** ** Control expressions *)

  Inductive cexp : Type :=
  | Emerge : ident -> cexp -> cexp -> cexp
  | Eite   : lexp -> cexp -> cexp -> cexp
  | Eexp   : lexp -> cexp.

  Fixpoint typeof (le: lexp): type :=
    match le with
    | Econst c => type_const c
    | Evar _ ty
    | Eunop _ _ ty
    | Ebinop _ _ _ ty => ty
    | Ewhen e _ _ => typeof e
    end.

End NLEXPRSYNTAX.
