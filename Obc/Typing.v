Require Import Rustre.Common.
Require Import Rustre.Operators.
Require Import Rustre.RMemory.
Require Import Rustre.Obc.Syntax.
Require Import Rustre.Obc.Semantics.

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
       (Import Syn   : SYNTAX Ids Op OpAux)
       (Import Sem   : SEMANTICS Ids Op OpAux Syn).

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

  (** Properties *)
    
  Definition wt_valo (ve: stack) (xty: ident * type) :=
    match PM.find (fst xty) ve with
    | None => True
    | Some v => wt_val v (snd xty)
    end.

  Definition wt_env (vars: list (ident * type)) (ve: stack) :=
    Forall (wt_valo ve) vars.
    
  Inductive wt_mem : heap -> program -> class -> Prop :=
  | WTmenv: forall me p cl,
      wt_env cl.(c_mems) me.(mm_values) ->
      Forall (wt_mem_inst me p) cl.(c_objs) ->
      wt_mem me p cl
  with wt_mem_inst : heap -> program -> (ident * ident) -> Prop :=
  | WTminst: forall me p oclsid mo cls p',
      PM.find (fst oclsid) me.(mm_instances) = Some mo ->
      find_class (snd oclsid) p = Some(cls, p') ->
      wt_mem mo p' cls ->
      wt_mem_inst me p oclsid.
         
  Lemma venv_find_wt_val:
    forall vars ve x ty v,
      wt_env vars ve ->
      In (x, ty) vars ->
      PM.find x ve = Some v ->
      wt_val v ty.
  Proof.
    intros ** WTe Hin Hfind.
    apply In_Forall with (1:=WTe) in Hin.
    unfold wt_valo in Hin.
    simpl in Hin.
    now rewrite Hfind in Hin.
  Qed.
  
  Lemma pres_sem_exp:
    forall mems vars me ve e v,
      wt_env mems me.(mm_values) ->
      wt_env vars ve ->
      wt_exp mems vars e ->
      exp_eval me ve e v ->
      wt_val v (typeof e).
  Proof.
    intros until v. intros WTm WTv.
    revert v.
    induction e; intros v WTe Hexp.
    - inv WTe. inv Hexp.
      eapply venv_find_wt_val with (1:=WTv); eauto.
    - inv WTe. inv Hexp.
      unfold mfind_mem in *.
      eapply venv_find_wt_val with (1:=WTm); eauto.
    - inv Hexp. apply wt_val_const.
    - inv WTe. inv Hexp.
      match goal with
      | WTe:wt_exp _ _ ?e, Hexp:exp_eval _ _ ?e ?v |- _ =>
        specialize (IHe v WTe Hexp)
      end.
      eapply pres_sem_unop in IHe; now eauto.
    - inv WTe. inv Hexp.
      repeat match goal with
             | IH: forall v, _, WTe:wt_exp _ _ ?e, Hexp:exp_eval _ _ ?e ?v |- _
                 => specialize (IH v WTe Hexp)
             end.
      eapply pres_sem_binop with (3:=IHe1) in IHe2; eauto.
  Qed.
    
End TYPING.

Module Typing
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : SYNTAX Ids Op OpAux) <: TYPING Ids Op OpAux Syn.
  Include TYPING Ids Op OpAux Syn.
End Typing.

