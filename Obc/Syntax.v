Require Import Rustre.Common.
Require Import Rustre.Operators.

Open Scope bool_scope.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * Obc syntax *)

(**
  Obc is a minimal object-oriented programming language.
 *)

Module Type SYNTAX
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op).

  Inductive exp : Type :=
  | Var   : ident -> type -> exp                (* variable  *)
  | State : ident -> type -> exp                (* state variable  *)
  | Const : const-> exp                         (* constant *)
  | Unop  : unop -> exp -> type -> exp          (* unary operator *)
  | Binop : binop -> exp -> exp -> type -> exp. (* binary operator *)

  Definition typeof (e: exp): type :=
    match e with
    | Const c => type_const c
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
  | Call : list (ident * type) -> ident -> ident -> ident -> list exp -> stmt
                (* y1:t1, ..., yn:tn := class instance method (e1, ..., em) *)
  | Skip.

  Record method : Type :=
    mk_method {
        m_name : ident;
	m_in   : list (ident * type);
	m_vars : list (ident * type);
	m_out  : list (ident * type);
	m_body : stmt;
        
	m_nodupvars : NoDupMembers (m_in ++ m_vars ++ m_out);
        m_good      : Forall NotReserved (m_in ++ m_vars ++ m_out)
      }.
  
  Record class : Type :=
    mk_class {
	c_name    : ident;
	c_mems    : list (ident * type);
	c_objs    : list (ident * ident);   (* (instance, class) *)
	c_methods : list method;

        c_nodups   : NoDup (map fst c_mems ++ map fst c_objs)
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

  Lemma find_method_In:
    forall f ms fm,
      find_method f ms = Some fm ->
      In fm ms.
  Proof.
    intros f ms fm Hfind.
    induction ms as [|m ms].
    now inversion Hfind.
    simpl in Hfind.
    destruct (ident_eq_dec m.(m_name) f) as [He|Hne].
    - subst. rewrite ident_eqb_refl in Hfind.
      injection Hfind; intro; subst; apply in_eq.
    - rewrite (proj2 (ident_eqb_neq m.(m_name) f) Hne) in Hfind.
      auto using in_cons.
  Qed.
  
End SYNTAX.

Module SyntaxFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op) <: SYNTAX Ids Op OpAux.

  Include SYNTAX Ids Op OpAux.

End SyntaxFun.

