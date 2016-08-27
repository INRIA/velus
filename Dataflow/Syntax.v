Require Import Rustre.Common.
Require Import PArith.
Require Import Rustre.Nelist.

Import List.ListNotations.
Open Scope list_scope.


(** * The CoreDF dataflow language *)

Module Type PRE_SYNTAX (Import Op : OPERATORS).
  (** ** Clocks *)

  (* TODO: Remove the typ argument from Con.
           Difficulty: the Control function from translation currently
                       uses this argument to generate Minimp expressions.
           Two possible solutions:
           1. Remove types from Minimp subexpressions (use a global
             environment).
           2. Pass a typing environment to Control.

           What to do??? *)
  Inductive clock : Type :=
  | Cbase : clock                          (* base clock *)
  | Con : clock -> ident -> typ -> bool -> clock. (* subclock *)

  (** ** Expressions *)

  Inductive lexp : Type :=
  | Econst : val -> typ -> lexp
  | Evar : ident -> typ -> lexp
  | Ewhen : lexp -> ident -> bool -> lexp
  | Eunop : unary_op -> lexp -> typ -> lexp
  | Ebinop : binary_op -> lexp -> lexp -> typ -> lexp.

  Fixpoint typeof (le: lexp): typ :=
    match le with
    | Econst _ ty
    | Evar _ ty
    | Eunop _ _ ty
    | Ebinop _ _ _ ty => ty
    | Ewhen e _ _ => typeof e
    end.
  
  Definition lexps := nelist lexp.

  Implicit Type le: lexp.
  Implicit Type les: lexps.

  (** ** Control expressions *)

  Inductive cexp : Type :=
  | Emerge : ident -> typ -> cexp -> cexp -> cexp 
  | Eite : lexp -> cexp -> cexp -> cexp
  | Eexp : lexp -> cexp.

  Implicit Type ce: cexp.

  (** ** Equations *)

  Inductive equation : Type :=
  | EqDef : ident -> clock -> cexp -> equation
  | EqApp : ident -> clock -> ident -> lexps -> typ -> equation
  | EqFby : ident -> clock -> val -> lexp -> equation.

  Implicit Type eqn: equation.

  (** ** Node *)

  Record node : Type :=
    mk_node {
        n_name : ident;
        n_input : nelist (ident * typ);
        n_output : (ident * typ);
        n_vars : list (ident * typ);
        n_eqs : list equation }.

  (** ** Program *)

  Definition global := list node.

  Implicit Type G: global.

  (* definition is needed in signature *)
  Definition find_node (f : ident) : global -> option node :=
    List.find (fun n=> ident_eqb n.(n_name) f).

End PRE_SYNTAX.

Module Type SYNTAX (Import Op : OPERATORS).
  
  Include PRE_SYNTAX Op.

  (** ** Properties *)

  (** Stronger induction scheme for lexp *)
  (* Definition lexp_ind2 : forall P : lexp -> Prop, *)
  (*   (forall c, P (Econst c)) -> *)
  (*   (forall i, P (Evar i)) -> *)
  (*   (forall le, P le -> forall i b, P (Ewhen le i b)) -> *)
  (*   (forall op les, Nelist.Forall P les -> P (Eop op les)) -> *)
  (*   forall le, P le. *)
  (* Proof. *)
  (* intros P Hconst Hvar Hwhen Hop. fix 1. *)
  (* intro le. *)
  (* destruct le as [c | i | le | op les]. *)
  (* + apply Hconst. *)
  (* + apply Hvar. *)
  (* + apply Hwhen. apply lexp_ind2. *)
  (* + apply Hop. induction les; constructor. *)
  (*   - apply lexp_ind2. *)
  (*   - apply lexp_ind2. *)
  (*   - apply IHles. *)
  (* Defined. *)

End SYNTAX.

Module SyntaxFun (Import Op : OPERATORS) <: SYNTAX Op.
  Include PRE_SYNTAX Op.
End SyntaxFun.
