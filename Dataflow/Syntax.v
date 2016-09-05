Require Import Rustre.Common.
Require Import PArith.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * The CoreDF dataflow language *)

Module Type SYNTAX
       (Import Ids : IDS)
       (Import Op  : OPERATORS).
  (** ** Clocks *)

  Inductive clock : Type :=
  | Cbase : clock                            (* base clock *)
  | Con   : clock -> ident -> bool -> clock. (* subclock *)

  (** ** Expressions *)

  Inductive lexp : Type :=
  | Econst : const -> lexp
  | Evar   : ident -> typ -> lexp
  | Ewhen  : lexp -> ident -> bool -> lexp
  | Eunop  : unary_op -> lexp -> typ -> lexp
  | Ebinop : binary_op -> lexp -> lexp -> typ -> lexp.

  Definition lexps := list lexp.

  Implicit Type le: lexp.
  Implicit Type les: lexps.

  (** ** Control expressions *)

  Inductive cexp : Type :=
  | Emerge : ident -> typ -> cexp -> cexp -> cexp 
  | Eite   : lexp -> cexp -> cexp -> cexp
  | Eexp   : lexp -> cexp.

  Implicit Type ce: cexp.

  (** ** Equations *)

  (* TODO: Why aren't the two others typed? *)
  Inductive equation : Type :=
  | EqDef : ident -> clock -> cexp -> equation
  | EqApp : ident -> clock -> ident -> lexps -> typ -> equation
  | EqFby : ident -> clock -> const -> lexp -> equation.

  Implicit Type eqn: equation.

  (** ** Node *)

  Inductive VarsDeclared_clock (vars: list (ident * typ)): clock -> Prop :=
  | vd_base:
      VarsDeclared_clock vars Cbase
  | vd_on: forall ck x b,
      In (x, bool_typ) vars ->
      VarsDeclared_clock vars ck ->
      VarsDeclared_clock vars (Con ck x b).
  
  Inductive VarsDeclared_lexp (vars: list (ident * typ)): lexp -> Prop :=
  | vd_const: forall c,
      VarsDeclared_lexp vars (Econst c)
  | vd_var: forall x ty,
      In (x, ty) vars ->
      VarsDeclared_lexp vars (Evar x ty)
  | vd_when: forall e x b,
      In (x, bool_typ) vars ->
      VarsDeclared_lexp vars e ->
      VarsDeclared_lexp vars (Ewhen e x b)
  | vd_unop: forall op e ty,
      VarsDeclared_lexp vars e ->
      VarsDeclared_lexp vars (Eunop op e ty)
  | vd_binop: forall op e1 e2 ty,
      VarsDeclared_lexp vars e1 ->
      VarsDeclared_lexp vars e2 ->
      VarsDeclared_lexp vars (Ebinop op e1 e2 ty).

  Inductive VarsDeclared_cexp (vars: list (ident * typ)): cexp -> Prop :=
  | vd_merge: forall x ty e1 e2,
      VarsDeclared_cexp vars e1 ->
      VarsDeclared_cexp vars e2 ->
      VarsDeclared_cexp vars (Emerge x ty e1 e2)
  | vd_ite: forall e1 et ef,
      VarsDeclared_lexp vars e1 ->
      VarsDeclared_cexp vars et ->
      VarsDeclared_cexp vars ef ->
      VarsDeclared_cexp vars (Eite e1 et ef)
  | vd_exp: forall e,
      VarsDeclared_lexp vars e ->
      VarsDeclared_cexp vars (Eexp e).

  Inductive VarsDeclared (vars: list (ident * typ)): equation -> Prop :=
  | eqn_def: forall x ck e,
      VarsDeclared_clock vars ck ->
      VarsDeclared vars (EqDef x ck e)
  | eqn_app: forall x ck f es ty,
      VarsDeclared_clock vars ck ->
      VarsDeclared vars (EqApp x ck f es ty)
  | eqn_fby: forall x ck c e,
      VarsDeclared_clock vars ck ->
      VarsDeclared vars (EqFby x ck c e).

  Fixpoint typeof (le: lexp): typ :=
    match le with
    | Econst c => typ_const c
    | Evar _ ty
    | Eunop _ _ ty
    | Ebinop _ _ _ ty => ty
    | Ewhen e _ _ => typeof e
    end.
  
  Record node : Type :=
    mk_node {
        n_name : ident;
        n_in   : list (ident * typ);
        n_out  : (ident * typ);
        n_vars : list (ident * typ);
        n_eqs  : list equation;

        n_ingt0 : 0 < length n_in;
        n_decl  : Forall (VarsDeclared (n_in ++ n_vars ++ [n_out])) n_eqs;
        n_nodup : NoDupMembers (n_in ++ n_vars ++ [n_out]);
        n_good  : Forall NotReserved (n_in ++ n_vars ++ [n_out])
      }.

  (** ** Program *)

  Definition global := list node.

  Implicit Type G: global.

  (* definition is needed in signature *)
  Definition find_node (f : ident) : global -> option node :=
    List.find (fun n=> ident_eqb n.(n_name) f).

End SYNTAX.

Module SyntaxFun
       (Import Ids : IDS)
       (Import Op  : OPERATORS) <: SYNTAX Ids Op.
  Include SYNTAX Ids Op.
End SyntaxFun.

