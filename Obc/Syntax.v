Require Import Velus.Common.
Require Import Velus.Operators.

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
  | Call : list ident -> ident -> ident -> ident -> list exp -> stmt
  (* y1, ..., yn := class instance method (e1, ..., em) *)
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

  Definition meth_vars m := m.(m_in) ++ m.(m_vars) ++ m.(m_out).
  Lemma NoDupMembers_meth_vars:
    forall f, NoDupMembers (meth_vars f).
  Proof. intro; apply (m_nodupvars f). Qed.
  Hint Resolve NoDupMembers_meth_vars.

  Lemma m_nodupout:
    forall f, NoDupMembers (m_out f).
  Proof.
    intro; pose proof (m_nodupvars f) as Nodup;
    now repeat apply NoDupMembers_app_r in Nodup.
  Qed.

  Lemma m_nodupin:
    forall f, NoDupMembers (m_in f).
  Proof.
    intro; pose proof (m_nodupvars f) as Nodup;
    now apply NoDupMembers_app_l in Nodup.
  Qed.

  Lemma m_nodupvars':
    forall f, NoDupMembers (m_vars f).
  Proof.
    intro; pose proof (m_nodupvars f) as Nodup;
    now apply NoDupMembers_app_r, NoDupMembers_app_l in Nodup.
  Qed.
  
  Lemma m_notreserved:
    forall x m,
      In x reserved ->
      ~InMembers x (meth_vars m).
  Proof.
    intros ** Hin Hinm.
    pose proof m.(m_good) as Good.
    unfold meth_vars in Hinm.
    induction (m.(m_in) ++ m.(m_vars) ++ m.(m_out)) as [|(x', t)];
      inv Hinm; inv Good.
    - contradiction.
    - now apply IHl.
  Qed.
  
  Record class : Type :=
    mk_class {
        c_name    : ident;
        c_mems    : list (ident * type);
        c_objs    : list (ident * ident);   (* (instance, class) *)
        c_methods : list method;

        c_nodup   : NoDup (map fst c_mems ++ map fst c_objs);
        c_nodupm  : NoDup (map m_name c_methods)
      }.

  Lemma c_nodupmems:
    forall c, NoDupMembers (c_mems c).
  Proof.
    intro.
    pose proof (c_nodup c) as Nodup.
    apply NoDup_app_weaken in Nodup.
    now rewrite fst_NoDupMembers.
  Qed.

  Lemma c_nodupobjs:
    forall c, NoDupMembers (c_objs c).
  Proof.
    intro.
    pose proof (c_nodup c) as Nodup.
    rewrite Permutation.Permutation_app_comm in Nodup.
    apply NoDup_app_weaken in Nodup.
    now rewrite fst_NoDupMembers.
  Qed.

  Definition program : Type := list class.
  
  Definition find_method (f: ident): list method -> option method :=
    fix find ms := match ms with
                   | [] => None
                   | m :: ms' => if ident_eqb m.(m_name) f
                                then Some m else find ms'
                   end.

  Remark find_method_In:
    forall fid ms f,
      find_method fid ms = Some f ->
      In f ms.
  Proof.
    intros ** Hfind.
    induction ms; inversion Hfind as [H].
    destruct (ident_eqb (m_name a) fid) eqn: E.
    - inversion H; subst. 
      apply in_eq. 
    - auto using in_cons.
  Qed.

  Remark find_method_name:
    forall fid fs f,
      find_method fid fs = Some f ->
      f.(m_name) = fid.
  Proof.
    intros ** Hfind.
    induction fs; inversion Hfind as [H].
    destruct (ident_eqb (m_name a) fid) eqn: E.
    - inversion H; subst. 
      now apply ident_eqb_eq.
    - now apply IHfs.
  Qed.

  Definition find_class (n: ident) : program -> option (class * list class) :=
    fix find p := match p with
                  | [] => None
                  | c :: p' => if ident_eqb c.(c_name) n
                              then Some (c, p') else find p'
                  end.

  (** Properties of class lookups *)
  
  Lemma find_class_none:
    forall clsnm cls prog,
      find_class clsnm (cls::prog) = None
      <-> (cls.(c_name) <> clsnm /\ find_class clsnm prog = None).
  Proof.
    intros clsnm cls prog.
    simpl; destruct (ident_eqb (c_name cls) clsnm) eqn: E.
    - split; intro HH; try discriminate.
      destruct HH.
      apply ident_eqb_eq in E; contradiction.
    - apply ident_eqb_neq in E; split; intro HH; tauto.
  Qed.

  Remark find_class_app:
    forall id cls c cls',
      find_class id cls = Some (c, cls') ->
      exists cls'',
        cls = cls'' ++ c :: cls'
        /\ find_class id cls'' = None.
  Proof.
    intros ** Hfind.
    induction cls; inversion Hfind as [H].
    destruct (ident_eqb (c_name a) id) eqn: E.
    - inversion H; subst. 
      exists nil; auto.
    - specialize (IHcls H).
      destruct IHcls as (cls'' & Hcls'' & Hnone).
      rewrite Hcls''.
      exists (a :: cls''); split; auto.
      simpl; rewrite E; auto.
  Qed.

  Remark find_class_name:
    forall id cls c cls',
      find_class id cls = Some (c, cls') ->
      c.(c_name) = id.
  Proof.
    intros ** Hfind.
    induction cls; inversion Hfind as [H].
    destruct (ident_eqb (c_name a) id) eqn: E.
    - inversion H; subst. 
      now apply ident_eqb_eq.
    - now apply IHcls.
  Qed.

  Remark find_class_In:
    forall id cls c cls',
      find_class id cls = Some (c, cls') ->
      In c cls.
  Proof.
    intros ** Hfind.
    induction cls; inversion Hfind as [H].
    destruct (ident_eqb (c_name a) id) eqn: E.
    - inversion H; subst. 
      apply in_eq. 
    - apply in_cons; auto.
  Qed.
  
  (** Syntactic predicates *)

  Inductive Is_free_in_exp : ident -> exp -> Prop :=
  | FreeVar: forall i ty,
      Is_free_in_exp i (Var i ty)
  | FreeState: forall i ty,
      Is_free_in_exp i (State i ty)
  | FreeUnop: forall i op e ty,
      Is_free_in_exp i e ->
      Is_free_in_exp i (Unop op e ty)
  |FreeBinop: forall i op e1 e2 ty,
      Is_free_in_exp i e1 \/ Is_free_in_exp i e2 ->
      Is_free_in_exp i (Binop op e1 e2 ty).

  Lemma not_free_aux1 : forall i op e ty,
      ~Is_free_in_exp i (Unop op e ty) ->
      ~Is_free_in_exp i e.
  Proof.
    intros i op e ty Hfree H; apply Hfree. now constructor. 
  Qed.
  
  Lemma not_free_aux2 : forall i op e1 e2 ty,
      ~Is_free_in_exp i (Binop op e1 e2 ty) ->
      ~Is_free_in_exp i e1 /\ ~Is_free_in_exp i e2.
  Proof.
    intros i op e1 e2 ty Hfree; split; intro H; apply Hfree;
      constructor; [now left | now right].
  Qed.

  Ltac not_free :=
    lazymatch goal with
    | H : ~Is_free_in_exp ?x (Var ?i ?ty) |- _ =>
        let HH := fresh in
        assert (HH : i <> x) by (intro; subst; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp ?x (State ?i ?ty) |- _ =>
        let HH := fresh in
        assert (HH : i <> x) by (intro; subst; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp ?x (Unop ?op ?e ?ty) |- _ =>
        apply not_free_aux1 in H
    | H : ~Is_free_in_exp ?x (Binop ?op ?e1 ?e2 ?ty) |- _ =>
        destruct (not_free_aux2 x op e1 e2 ty H)
    end.

  (** Misc. properties *)
  
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

