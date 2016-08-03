Require Import lib.Integers.
Require Import lib.Floats.
Require cfrontend.Ctypes.

Require Import Rustre.Common.

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

Fixpoint get_instance_methods (s: stmt): list (ident * ident * ident) :=
  match s with
  | Ifte _ s1 s2  
  | Comp s1 s2 => get_instance_methods s2 ++ get_instance_methods s1
  | Call _ cls o f _ => [(o, cls, f)] 
  | _ => []
  end.

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

Axiom pos_of_str: string -> ident.
Definition self_id: ident := pos_of_str "self".
Definition out_id: ident := pos_of_str "out".
Axiom self_not_out: self_id <> out_id.

Record method : Type :=
  mk_method {
      m_name : ident;
	  m_in   : list (ident * typ);
	  m_vars : list (ident * typ);
	  m_out  : list (ident * typ);
	  m_body : stmt;
      
	  m_nodup : NoDupMembers (m_in ++ m_vars ++ m_out);
	  m_decl  : VarsDeclared (m_in ++ m_vars ++ m_out) m_body;

      m_self_id : ~InMembers self_id (m_in ++ m_vars ++ m_out);
      m_out_id  : ~InMembers out_id (m_in ++ m_vars ++ m_out)
    }.

Definition meth_vars (m: method): list (ident * typ) :=
  m.(m_in) ++ m.(m_vars) ++ m.(m_out).

Lemma nodup_vars:
  forall m,
    NoDupMembers (meth_vars m).
Proof.
  intro; exact (m_nodup m). 
Qed.

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

Definition ClassIn (clsnm: ident) (cls: list class) : Prop :=
  Exists (fun cls => cls.(c_name) = clsnm) cls.

Lemma NotClassIn:
  forall clsnm cls prog,
    ~ClassIn clsnm (cls::prog)
    <-> (cls.(c_name) <> clsnm /\ ~ClassIn clsnm prog).
Proof.
  intros clsnm cls prog.
  split; intro HH.
  - split; intros Hn; apply HH; constructor (assumption).
  - destruct HH as [HH1 HH2]; intros HH.
    apply HH2. inversion HH.
    + exfalso; apply HH1; assumption.
    + assumption.
Qed.

Inductive WelldefClasses: list class -> Prop :=
| wdc_nil:
    WelldefClasses []
| wdc_cons:
    forall c cls',
      WelldefClasses cls' ->
      (forall o c', In (o, c') c.(c_objs) ->
               ClassIn c' cls') ->
      Forall (fun c' => c.(c_name) <> c'.(c_name)) cls' ->
      WelldefClasses (c :: cls').

Definition program : Type := list class.

Definition find_class (n: ident): program -> option (class * program) :=
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

Lemma ClassIn_find_class:
  forall clsnm prog,
    ClassIn clsnm prog <->
    find_class clsnm prog <> None.
Proof.
  induction prog as [|cls prog' IH]; split.
  - now inversion 1.
  - simpl; intro H; now contradict H. 
  - intro Hcin.
    simpl. destruct (ident_eqb (c_name cls) clsnm) eqn:Heq.
    + intro; discriminate.
    + apply IH.
      inversion Hcin; subst.
      * rewrite ident_eqb_neq in Heq. intuition.
      * assumption.
  - simpl. intro Hfind. destruct (ident_eqb (c_name cls) clsnm) eqn:Heq.
    + left; now rewrite ident_eqb_eq in Heq.
    + right. unfold ClassIn in IH. now apply IH.
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
  - apply in_cons; auto.
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

Inductive sub_prog: program -> program -> Prop := 
  sub_prog_intro: forall p p', 
    sub_prog p (p' ++ p). 
 
Lemma find_class_sub: 
  forall prog clsid cls prog', 
    find_class clsid prog = Some (cls, prog') -> 
    sub_prog prog' prog. 
Proof. 
  intros ** Find. 
  apply find_class_app in Find.
  destruct Find as (? & ? & ?); subst. 
  rewrite List_shift_first. 
  constructor. 
Qed. 
 
Hint Constructors sub_prog. 
 
(* Remark unique_app:  *)
(*   forall cls cls',  *)
(*     unique_classes (cls ++ cls') -> unique_classes cls /\ unique_classes cls'.  *)
(* Proof.  *)
(*   induction cls.  *)
(*   - simpl; split; auto. apply unique_nil.  *)
(*   - intros cls' Unique.  *)
(*     split.  *)
(*     + unfold unique_classes.  *)
(*       introv Hin1 Hin2.  *)
(*       unfold unique_classes in Unique.  *)
(*       apply Unique; apply List.in_or_app; left; auto.  *)
(*     + rewrite <-List.app_comm_cons in Unique.    *)
(*       apply unique_cons in Unique.  *)
(*       apply IHcls; auto.  *)
(* Qed.  *)
 
Remark find_class_sub_same: 
  forall prog1 prog2 clsid cls prog', 
    find_class clsid prog2 = Some (cls, prog') -> 
    WelldefClasses prog1 -> 
    sub_prog prog2 prog1 -> 
    find_class clsid prog1 = Some (cls, prog'). 
Proof. 
  intros ** Hfind WD Sub. 
  inversion Sub; clear Sub; subst.  
  pose proof (find_class_app _ _ _ _ Hfind) as H.
  destruct H as (prog2' & Hprog2 & Hnone).
  induction p'; simpl; auto. 
  rewrite <-List.app_comm_cons in WD. 
  assert (List.In cls (p' ++ prog2)) as Hin_cls. 
  - pose proof (find_class_In _ _ _ _ Hfind) as Hin.
    apply List.in_or_app; right; auto.  
  - inversion WD as [|? ? ? ? Hforall]; subst a.
    apply find_class_name in Hfind; subst clsid.
    apply In_Forall with (2:=Hin_cls) in Hforall.
    apply ident_eqb_neq in Hforall. 
    rewrite Hforall. 
    apply IHp'. eapply WelldefClasses_cons; eauto. 
Qed. 
 
Remark find_class_welldef: 
  forall prog clsid cls prog', 
    WelldefClasses prog -> 
    find_class clsid prog = Some (cls, prog') -> 
    WelldefClasses prog'. 
Proof. 
  intros ** WD Find.
  apply find_class_app in Find.
  destruct Find as (prog2' & Hprog2 & Hnone).
  subst.
  apply WelldefClasses_app in WD.
  eapply WelldefClasses_cons; eauto. 
Qed. 
 
