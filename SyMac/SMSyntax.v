Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
(* Require Import PArith. *)
(* Require Import Coq.Sorting.Permutation. *)

Require Import List.
Import List.ListNotations.
Open Scope list_scope.


Module Type SMSYNTAX
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import Clks : CLOCKS Ids).

  (** ** Expressions *)

  Inductive lexp :=
  | Econst : const -> lexp
  | Evar   : ident -> type -> lexp
  | Elast  : ident -> type -> lexp
  | Ewhen  : lexp -> ident -> bool -> lexp
  | Eunop  : unop -> lexp -> type -> lexp
  | Ebinop : binop -> lexp -> lexp -> type -> lexp.

  (** ** Control expressions *)

  Inductive cexp :=
  | Emerge : ident -> cexp -> cexp -> cexp
  | Eite   : lexp -> cexp -> cexp -> cexp
  | Eexp   : lexp -> cexp.

  (** ** Equations *)

  Inductive equation :=
  | EqDef : ident -> clock -> cexp -> equation
  | EqLast: ident -> clock -> const -> equation
  | EqNext: ident -> clock -> cexp -> equation
  | EqCall: idents -> clock -> ident -> ident -> ident -> list lexp -> equation.
  (* y1, ..., yn = class instance method (e1, ..., em) *)

  Record method :=
    Method {
        m_name: ident;
        m_in  : list (ident * type);
        m_vars: list (ident * type);
        m_out : list (ident * type);
        m_eqs : list equation
      }.

  Record machine :=
    Machine {
        ma_name   : ident;
        ma_mems   : list (ident * type);
        ma_machs  : list (ident * ident);
        ma_methods: list method;
        ma_policy : list (ident * nat)
      }.

  Definition program := list machine.

  Fixpoint typeof (le: lexp): type :=
    match le with
    | Econst c => type_const c
    | Evar _ ty
    | Elast _ ty
    | Eunop _ _ ty
    | Ebinop _ _ _ ty => ty
    | Ewhen e _ _ => typeof e
    end.

End SMSYNTAX.

Module SMSyntaxFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Clks : CLOCKS Ids)
       <: SMSYNTAX Ids Op Clks.
  Include SMSYNTAX Ids Op Clks.
End SMSyntaxFun.
