Require Import Rustre.Common.

Open Scope bool_scope.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * Minimp syntax *)

(**
  Minimp is a minimal object-oriented programming language.
 *)

Module Type SYNTAX
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op).

  Inductive exp : Type :=
  | Var   : ident -> typ -> exp                    (* variable  *)
  | State : ident -> typ -> exp                    (* state variable  *)
  | Const : const-> exp                            (* constant *)
  | Unop  : unary_op -> exp -> typ -> exp          (* unary operator *)
  | Binop : binary_op -> exp -> exp -> typ -> exp. (* binary operator *)

  Definition typeof (e: exp): typ :=
    match e with
    | Const c => typ_const c
    | Var _ ty
    | State _ ty
    | Unop _ _ ty
    | Binop _ _ _ ty => ty
    end.

  Inductive stmt : Type :=
  | Assign : ident -> exp -> stmt                    (* x = e *)
  | AssignSt : ident -> exp -> stmt                  (* self.x = e *)
  | Ifte : exp -> stmt -> stmt -> stmt               (* if e then s1 else s2 *)
  | Comp : stmt -> stmt -> stmt                      (* s1; s2 *)
  | Call : list (ident * typ) -> ident -> ident -> ident -> list exp -> stmt
                (* y1:t1, ..., yn:tn := class instance method (e1, ..., em) *)
  | Skip.

  Inductive VarsDeclared_exp (vars: list (ident * typ)): exp -> Prop :=
  | vd_var: forall x ty,
      In (x, ty) vars ->
      VarsDeclared_exp vars (Var x ty)
  | vd_state: forall x ty,
      VarsDeclared_exp vars (State x ty)
  | vd_const: forall c,
      VarsDeclared_exp vars (Const c)
  | vd_unop: forall op e ty,
      VarsDeclared_exp vars e ->
      VarsDeclared_exp vars (Unop op e ty)
  | vd_binop: forall op e1 e2 ty,
      VarsDeclared_exp vars e1 ->
      VarsDeclared_exp vars e2 ->
      VarsDeclared_exp vars (Binop op e1 e2 ty).
                       
  Inductive VarsDeclared (vars: list (ident * typ)): stmt -> Prop :=
  | vd_assign: forall x e,
      In (x, typeof e) vars ->
      VarsDeclared_exp vars e ->
      VarsDeclared vars (Assign x e)
  | vd_assignst: forall x e,
      VarsDeclared_exp vars e ->
      VarsDeclared vars (AssignSt x e)
  | vd_ifte: forall e s1 s2,
      VarsDeclared_exp vars e ->
      VarsDeclared vars s1 ->
      VarsDeclared vars s2 ->
      VarsDeclared vars (Ifte e s1 s2)
  | vd_comp: forall s1 s2,
      VarsDeclared vars s1 ->
      VarsDeclared vars s2 ->
      VarsDeclared vars (Comp s1 s2)
  | vd_call: forall f ys c o es,
      List.incl ys vars ->
      Forall (VarsDeclared_exp vars) es ->
      VarsDeclared vars (Call ys c o f es)
  | vd_skip: 
      VarsDeclared vars Skip.

  Inductive MemsDeclared_exp (mems: list (ident * typ)): exp -> Prop :=
  | md_var: forall x ty,
      MemsDeclared_exp mems (Var x ty)
  | md_state: forall x ty,
      List.In (x, ty) mems ->
      MemsDeclared_exp mems (State x ty)
  | md_const: forall c,
      MemsDeclared_exp mems (Const c)
  | md_unop: forall op e ty,
      MemsDeclared_exp mems e ->
      MemsDeclared_exp mems (Unop op e ty)
  | md_binop: forall op e1 e2 ty,
      MemsDeclared_exp mems e1 ->
      MemsDeclared_exp mems e2 ->
      MemsDeclared_exp mems (Binop op e1 e2 ty).

  Inductive MemsDeclared (mems: list (ident * typ)): stmt -> Prop :=
  | md_assign: forall x e,
      MemsDeclared_exp mems e ->
      MemsDeclared mems (Assign x e)
  | md_assignst: forall x e,
      List.In (x, typeof e) mems ->
      MemsDeclared_exp mems e ->
      MemsDeclared mems (AssignSt x e)
  | md_ifte: forall e s1 s2,
      MemsDeclared_exp mems e ->
      MemsDeclared mems s1 ->
      MemsDeclared mems s2 ->
      MemsDeclared mems (Ifte e s1 s2)
  | md_comp: forall s1 s2,
      MemsDeclared mems s1 ->
      MemsDeclared mems s2 ->
      MemsDeclared mems (Comp s1 s2)
  | md_call: forall f ys c o es,
      Forall (MemsDeclared_exp mems) es ->
      MemsDeclared mems (Call ys c o f es)
  | md_skip: 
      MemsDeclared mems Skip.
                       
  Inductive InstanceDeclared (objs: list (ident * ident)): stmt -> Prop :=
  | id_assign: forall x e,
      InstanceDeclared objs (Assign x e)
  | id_assignst: forall x e,
      InstanceDeclared objs (AssignSt x e)
  | id_ifte: forall e s1 s2,
      InstanceDeclared objs s1 ->
      InstanceDeclared objs s2 ->
      InstanceDeclared objs (Ifte e s1 s2)
  | id_comp: forall s1 s2,
      InstanceDeclared objs s1 ->
      InstanceDeclared objs s2 ->
      InstanceDeclared objs (Comp s1 s2)
  | id_call: forall f ys c o es,
      List.In (o, c) objs ->
      InstanceDeclared objs (Call ys c o f es)
  | id_skip: 
      InstanceDeclared objs Skip.

  Record method : Type :=
    mk_method {
        m_name : ident;
	m_in   : list (ident * typ);
	m_vars : list (ident * typ);
	m_out  : list (ident * typ);
	m_body : stmt;
        
	m_nodupvars : NoDupMembers (m_in ++ m_vars ++ m_out);
        (* TODO: ~VarsDeclared m_in m_body? *)
	m_varsdecl  : VarsDeclared (m_vars ++ m_out) m_body;
        m_good      : Forall NotReserved (m_in ++ m_vars ++ m_out)
      }.
  
  Record class : Type :=
    mk_class {
	c_name    : ident;
	c_mems    : list (ident * typ);
	c_objs    : list (ident * ident);   (* (instance, class) *)
	c_methods : list method;

        c_nodups   : NoDup (map fst c_mems ++ map fst c_objs);
	c_memsdecl : Forall (fun m=>MemsDeclared c_mems m.(m_body)) c_methods;
        c_instdecl : Forall (fun m=>InstanceDeclared c_objs m.(m_body)) c_methods
      }.

  Definition program : Type := list class.
  
  Definition find_method (f: ident): list method -> option method :=
    fix find ms := match ms with
                   | [] => None
                   | m :: ms' => if ident_eqb m.(m_name) f
                                 then Some m else find ms'
                   end.

  Definition find_class (n: ident) : program -> option (class * list class) :=
    fix find p := match p with
                  | [] => None
                  | c :: p' => if ident_eqb c.(c_name) n
                               then Some (c, p') else find p'
                  end.

  Lemma exp_dec : forall e1 e2 : exp, {e1 = e2} + {e1 <> e2}.
  Proof.
    decide equality;
      try apply equiv_dec.
  Qed.
    
  Instance: EqDec exp eq := { equiv_dec := exp_dec }.

  Lemma reset_not_step:
    reset <> step.
  Proof.
    pose proof (Ids.methods_nodup) as Hndup.
    unfold methods in Hndup.
    inversion_clear Hndup.
    intro Hrs. rewrite Hrs in *.
    intuition.
  Qed.
  
End SYNTAX.

Module SyntaxFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op) <: SYNTAX Ids Op OpAux.

  Include SYNTAX Ids Op OpAux.

End SyntaxFun.

