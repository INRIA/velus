Require Import Velus.Common.
Require Import Velus.Operators.

(** * The core dataflow expresion syntax *)

Module Type CESYNTAX (Import Op: OPERATORS).

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

  (** Predicate used in [normal_args] in NLustre and SyBloc. *)
  Fixpoint noops_lexp (ck: clock) (le : lexp) : Prop :=
    match ck with
    | Cbase => True
    | Con ck' _ _ =>
      match le with
      | Econst _ | Evar _ _ => True
      | Ewhen le' _ _ => noops_lexp ck' le'
      | _ => False
      end
    end.

End CESYNTAX.

Module CESyntaxFun (Op: OPERATORS) <: CESYNTAX Op.
  Include CESYNTAX Op.
End CESyntaxFun.