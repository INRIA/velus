Require Import lib.Integers.
Require Import lib.Floats.
Require cfrontend.Ctypes.

Require Import Rustre.Common Rustre.Nelist.

Require Import String.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(* SYNTAX *)
Inductive const :=
| Cint: int -> const 
| Cfloat: float -> const 
| Csingle: float32 -> const 
| Clong: int64 -> const.

Lemma const_eq: forall (c1 c2: const), {c1=c2} + {c1<>c2}.
Proof.
  decide equality.
  - apply Int.eq_dec.
  - apply Float.eq_dec.
  - apply Float32.eq_dec.
  - apply Int64.eq_dec.
Qed.

Definition typ := Ctypes.type.

Inductive exp : Type :=
| Var : ident -> typ -> exp    (* variable  *)
| State : ident -> typ -> exp  (* state variable  *)
| Const : const -> typ -> exp. (* constant *)

Definition typeof (e: exp): typ :=
  match e with
  | Var _ ty
  | State _ ty
  | Const _ ty => ty
  end.

Inductive stmt : Type :=
| Assign:                (* x = e *)
    ident -> exp -> stmt  
| AssignSt:              (* self.x = e *)
    ident -> exp -> stmt
| Ifte:                  (* if e then s1 else s2 *)
    exp -> stmt -> stmt -> stmt
| Comp:                  (* s1; s2 *)
    stmt -> stmt -> stmt   
| Call:               (* (y1:t1,...,yn:tn) = (C o).f(es) *)  
    list (ident * typ) -> ident -> ident -> ident -> list exp -> stmt 
| Skip.                  (*  *)

Inductive VarsDeclared_exp (vars: list (ident * typ)): exp -> Prop :=
| vd_var: forall x ty,
    In (x, ty) vars ->
    VarsDeclared_exp vars (Var x ty)
| vd_state: forall x ty,
    VarsDeclared_exp vars (State x ty)
| vd_const: forall c ty,
    VarsDeclared_exp vars (Const c ty).
                     
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
    incl ys vars ->
    Forall (VarsDeclared_exp vars) es ->
    VarsDeclared vars (Call ys c o f es)
| vd_skip: 
    VarsDeclared vars Skip.

Inductive StateDeclared_exp (mems: list (ident * typ)): exp -> Prop :=
| sd_var: forall x ty,
    StateDeclared_exp mems (Var x ty)
| sd_state: forall x ty,
    In (x, ty) mems ->
    StateDeclared_exp mems (State x ty)
| sd_const: forall c ty,
    StateDeclared_exp mems (Const c ty).
                     
Inductive StateDeclared (mems: list (ident * typ)): stmt -> Prop :=
| sd_assign: forall x e,
    StateDeclared_exp mems e ->
    StateDeclared mems (Assign x e)
| sd_assignst: forall x e,
    In (x, typeof e) mems ->
    StateDeclared_exp mems e ->
    StateDeclared mems (AssignSt x e)
| sd_ifte: forall e s1 s2,
    StateDeclared_exp mems e ->
    StateDeclared mems s1 ->
    StateDeclared mems s2 ->
    StateDeclared mems (Ifte e s1 s2)
| sd_comp: forall s1 s2,
    StateDeclared mems s1 ->
    StateDeclared mems s2 ->
    StateDeclared mems (Comp s1 s2)
| sd_call: forall f ys c o es,
    Forall (StateDeclared_exp mems) es ->
    StateDeclared mems (Call ys c o f es)
| sd_skip: 
    StateDeclared mems Skip.
                     
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
    In (o, c) objs ->
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
                   
	    m_nodup : NoDupMembers (m_in ++ m_vars ++ m_out);
	    m_decl  : VarsDeclared (m_in ++ m_vars ++ m_out) m_body
    }.

(* Record obj_dec : Type := *)
(*   mk_obj_dec { *)
(*       obj_inst : ident; *)
(*       obj_class: ident *)
(*     }. *)

Record class : Type :=
    mk_class {
	    c_name    : ident;
	    c_mems    : list (ident * typ);
	    c_objs    : list (ident * ident);
	    c_methods : list method;
        
	    c_nodupmems : NoDupMembers c_mems;
        c_nodupobjs : NoDupMembers c_objs;
                                   
	    c_statedecl : Forall (fun m => StateDeclared c_mems m.(m_body)) c_methods;
        c_instdecl  : Forall (fun m => InstanceDeclared c_objs m.(m_body)) c_methods
      }.

(* Record class : Type := *)
(*   mk_class { *)
(*       c_name  : ident; *)

(*       c_input : nelist (ident * typ); *)
(*       c_output: nelist (ident * typ); *)
(*       c_vars  : list (ident * typ); *)
        
(*       c_mems  : list (ident * typ); *)
(*       c_objs  : list obj_dec; *)

(*       c_step  : stmt  *)
(*     }. *)

(* Definition class_vars (c: class): list (ident * typ) := *)
(*   nelist2list c.(c_output) ++ nelist2list c.(c_input) ++ c.(c_vars). *)

Definition ClassIn (clsnm: ident) (cls: list class) : Prop :=
  Exists (fun cls => cls.(c_name) = clsnm) cls.

Inductive WelldefClasses: list class -> Prop :=
| wdc_nil:
    WelldefClasses []
| wdc_cons:
    forall c cls',
      WelldefClasses cls' ->
      (forall o c', In (o, c') c.(c_objs) ->
               ClassIn c' cls') ->
      WelldefClasses (c :: cls').

Record program : Type :=
  mk_program {
      p_classes : list class;
      p_welldef : WelldefClasses p_classes
    }.

(* Definition program : Type := list class. *)

Definition find_class' (n: ident): list class -> option (class * list class) :=
  fix find p :=
    match p with
    | [] => None
    | c :: p' => if ident_eqb c.(c_name) n then Some (c, p') else find p'
    end.

Definition find_method (f: ident): list method -> option method :=
  fix find ms :=
    match ms with
    | [] => None
    | m :: ms' => if ident_eqb m.(m_name) f then Some m else find ms'
    end.

Remark find_class_In:
  forall id cls c cls',
    find_class' id cls = Some (c, cls') ->
    In c cls.
Proof.
  intros ** Hfind.
  induction cls; inversion Hfind as [H].
  destruct (ident_eqb (c_name a) id) eqn: E.
  - inversion H; subst. 
    apply in_eq. 
  - apply in_cons; auto.
Qed.

Remark find_class_app:
  forall id cls c cls',
    find_class' id cls = Some (c, cls') ->
    exists cls'',
      cls = cls'' ++ c :: cls'
      /\ find_class' id cls'' = None.
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
    find_class' id cls = Some (c, cls') ->
    c.(c_name) = id.
Proof.
  intros ** Hfind.
  induction cls; inversion Hfind as [H].
  destruct (ident_eqb (c_name a) id) eqn: E.
  - inversion H; subst. 
    now apply ident_eqb_eq.
  - now apply IHcls.
Qed.

Lemma WelldefClasses_cons:
  forall c cls,
    WelldefClasses (c :: cls) ->
    WelldefClasses cls.
Proof.
  induction cls; inversion 1; auto.
Qed.

Lemma WelldefClasses_app:
  forall cls cls',
    WelldefClasses (cls ++ cls') ->
    WelldefClasses cls'.
Proof.
  induction cls; inversion 1; auto.
Qed.

Program Definition find_class (n: ident) (p: program): option (class * program) :=
  match find_class' n p.(p_classes) with
  | Some (c, cls') => Some (c, {| p_classes := cls' |})
  | None => None
  end.
Next Obligation.
  rename Heq_anonymous into H.
  symmetry in H; apply find_class_app in H.
  destruct H as (cls'' & Eq & ?).
  destruct p as (cls & WD).
  simpl in Eq.
  subst cls.
  apply WelldefClasses_app in WD.
  now apply WelldefClasses_cons in WD.  
Defined.

(** ** Decidable equality *)

Lemma exp_eq: forall (e1 e2: exp), {e1=e2} + {e1<>e2}.
Proof.
  decide equality; try apply Ctypes.type_eq; try now decide equality.
  apply const_eq.
Qed.

Definition exp_eqb (e1 e2 : exp): bool := if exp_eq e1 e2 then true else false. 

Lemma exp_eqb_eq:
  forall e1 e2,
    exp_eqb e1 e2 = true <-> e1 = e2.
Proof.
  unfold exp_eqb.
  intros e1 e2; destruct (exp_eq e1 e2); intuition.
Qed.
