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
| Assign: ident -> exp -> stmt       (* x = e *)
| AssignSt: ident -> exp -> stmt     (* self.x = e *)
| Ifte : exp -> stmt -> stmt -> stmt  (* if e then s1 else s2 *)
| Comp: stmt -> stmt -> stmt         (* s1; s2 *)
| Skip.                            (*  *)

Record obj_dec : Type :=
  mk_obj_dec {
      obj_inst  : ident;
      obj_class : ident
    }.

Record class : Type :=
  mk_class {
      c_name : ident;
      c_mems : list (ident * typ);
      c_objs : list obj_dec;
      c_vars : list (ident * typ);  
      c_step : stmt 
    }.

Definition program : Type := list class.

Definition find_class (n: ident) : program -> option (class * list class) :=
  fix find p :=
    match p with
    | [] => None
    | c :: p' => if ident_eqb c.(c_name) n then Some (c, p') else find p'
    end.

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

Axiom pos_of_str: string -> ident.
Axiom pos_to_str: ident -> string.
Definition self_id: ident := pos_of_str "self".
Definition main_id: ident := pos_of_str "main".

Section WellFormed.
  Variable c: class.

  Inductive well_formed_exp: exp -> Prop :=
  | wf_var: forall x ty,
      In (x, ty) c.(c_vars) ->
      x <> self_id ->
      well_formed_exp (Var x ty)
  | wf_state: forall x ty,
      In (x, ty) c.(c_mems) ->
      well_formed_exp (State x ty)
  | wf_const: forall c ty,
      well_formed_exp (Const c ty).

  Inductive well_formed_stmt: stmt -> Prop :=
  | wf_assign: forall x e,
      In (x, typeof e) c.(c_vars) ->
      x <> self_id ->
      well_formed_exp e ->
      well_formed_stmt (Assign x e)
  | wf_assignst: forall x e,
      In (x, typeof e) c.(c_mems) ->
      x <> self_id ->
      well_formed_exp e ->
      well_formed_stmt (AssignSt x e)
  | wf_ite: forall e s1 s2,
      well_formed_exp e ->
      well_formed_stmt s1 ->
      well_formed_stmt s2 ->
      well_formed_stmt (Ifte e s1 s2)
  | wf_comp: forall s1 s2,
      well_formed_stmt s1 ->
      well_formed_stmt s2 ->
      well_formed_stmt (Comp s1 s2)
  | wf_skip: well_formed_stmt Skip.

  Definition well_formed_cls: Prop := well_formed_stmt c.(c_step).
End WellFormed.

Definition well_formed: program -> Prop := Forall well_formed_cls. 

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
