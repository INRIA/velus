Require Import Rustre.Common.
Require Import Rustre.Operators.
Require Import Rustre.Obc.Syntax.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * Obc typing *)

(** 

  Typing judgements for Obc and resulting properties.
  Classify Obc programs which are statically well-formed.

 *)

Module Type TYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : SYNTAX Ids Op OpAux).

  Section WellTyped.

    Variable p     : program.
    Variable insts : list (ident * ident).
    Variable mems  : list (ident * type).
    Variable vars  : list (ident * type).
    
    Inductive wt_exp : exp -> Prop :=
    | wt_Var: forall x ty,
        In (x, ty) vars ->
        wt_exp (Var x ty)
    | wt_State: forall x ty,
        In (x, ty) mems ->
        wt_exp (State x ty)
    | wt_Const: forall c,
        wt_exp (Const c)
    | wt_Unop: forall op e ty,
        type_unop op (typeof e) = Some ty ->
        wt_exp e ->
        wt_exp (Unop op e ty)
    | wt_Binop: forall op e1 e2 ty,
        type_binop op (typeof e1) (typeof e2) = Some ty ->
        wt_exp e1 ->
        wt_exp e2 ->
        wt_exp (Binop op e1 e2 ty).

    (* TODO: eliminate the result types in Call (and EqApp). *)
    Inductive wt_stmt : stmt -> Prop :=
    | wt_Assign: forall x e,
        In (x, typeof e) vars ->
        wt_exp e ->
        wt_stmt (Assign x e)
    | wt_AssignSt: forall x e,
        In (x, typeof e) mems ->
        wt_exp e ->
        wt_stmt (AssignSt x e)
    | wt_Ifte: forall e s1 s2,
        wt_exp e ->
        wt_stmt s1 ->
        wt_stmt s2 ->
        wt_stmt (Ifte e s1 s2)
    | wt_Comp: forall s1 s2,
        wt_stmt s1 ->
        wt_stmt s2 ->
        wt_stmt (Comp s1 s2)
    | wt_Call: forall clsid cls p' o f fm ys es,
        In (o, clsid) insts ->
        find_class clsid p = Some(cls, p') ->
        find_method f cls.(c_methods) = Some fm ->
        NoDup ys ->
        Forall2 (fun y xt => In (fst y, snd xt) vars) ys fm.(m_out) ->
        Forall2 (fun e xt => typeof e = snd xt) es fm.(m_in) ->
        Forall wt_exp es ->
        wt_stmt (Call ys clsid o f es)
    | wt_Skip:
        wt_stmt Skip.

  End WellTyped.

  Definition wt_method (p     : program)
                       (insts : list (ident * ident))
                       (mems  : list (ident * type))
                       (m     : method) : Prop
    := wt_stmt p insts mems (m.(m_in) ++ m.(m_vars) ++ m.(m_out)) m.(m_body).

  Definition wt_class (p : program) (cls: class) : Prop
    := Forall (wt_method p cls.(c_objs) cls.(c_mems)) cls.(c_methods).
  
  Inductive wt_program : program -> Prop :=
  | wtp_nil:
      wt_program []
  | wtp_cons: forall cls p,
      wt_class p cls ->
      wt_program p ->
      wt_program (cls::p).

End TYPING.

Module Typing
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : SYNTAX Ids Op OpAux) <: TYPING Ids Op OpAux Syn.
  Include TYPING Ids Op OpAux Syn.
End Typing.

