Require Import lib.Integers.
Require Import lib.Floats.
Require Import Rustre.Common.
Require Import Rustre.Nelist.
Require Import Rustre.RMemory.
Require cfrontend.Ctypes.
Require common.Values.
Require cfrontend.Clight.
Require lib.Maps.
Require common.Smallstep.

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
| Assign : ident -> exp -> stmt                               (* x = e *)
| AssignSt : ident -> exp -> stmt                             (* self.x = e *)
| Skip.

Record obj_dec : Type :=
  mk_obj_dec {
      obj_inst  : ident;
      obj_class : ident
    }.

(* TODO: lots of fields are not strictly necessary *)
Record class : Type :=
  mk_class {
      c_name   : ident;
      c_mems   : list (ident * typ);       (* TODO: should track type of each *)
      c_objs   : list obj_dec
    }.

Definition program : Type := prod (prod stmt (list (ident * typ))) (list class).

Definition find_class (n: ident) : list class -> option (class * list class) :=
    fix find p :=
    match p with
    | [] => None
    | c :: p' => if ident_eqb c.(c_name) n then Some (c, p') else find p'
    end.

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

(* SEMANTICS *)
Definition val: Type := Values.val.

Definition menv: Type := memory val.
Definition venv: Type := PM.t (val * typ).

Definition m_empty: menv := empty_memory _.
Definition v_empty: venv := PM.empty (val * typ).

Definition val_of_const c :=
  match c with
  | Cint i => Values.Vint i
  | Cfloat f => Values.Vfloat f
  | Csingle s => Values.Vsingle s
  | Clong l => Values.Vlong l
  end.
  
Inductive exp_eval (me: menv) (ve: venv): exp -> val * typ -> Prop :=
| evar:
    forall x v ty,
      PM.find x ve = Some v ->
      exp_eval me ve (Var x ty) v
| estate:
    forall x v ty,
      mfind_mem x me = Some v ->
      exp_eval me ve (State x ty) (v, ty)
| econst:
    forall c ty,
      exp_eval me ve (Const c ty) (val_of_const c, ty).

Definition state := prod (prod menv venv) stmt.

(* =stmt_eval= *)
Inductive stmt_eval :
  program -> state -> state -> Prop :=
| Iassign: forall prog me ve x e v ve',
    exp_eval me ve e v ->
    PM.add x v ve = ve' ->
    stmt_eval prog (me, ve, Assign x e) (me, ve', Skip)
| Iassignst:
  forall prog me ve x e v me',
    exp_eval me ve e v ->
    madd_mem x (fst v) me = me' ->
    stmt_eval prog (me, ve, AssignSt x e) (me', ve, Skip)
(* | Iskip: *)
(*     forall prog menv env, *)
(*       stmt_eval prog (menv, env) Skip (menv, env). *)
.
(** ** Determinism of semantics *)

Theorem exp_eval_det:
  forall me ve e v1 v2,
    exp_eval me ve e v1 ->
    exp_eval me ve e v2 ->
    v1 = v2.
Proof.
  induction e; intros v1 v2 H1 H2;
  inversion H1 as [xa va tya Hv1|xa va tya Hv1|ca tya Hv1];
  inversion H2 as [xb vb tyb Hv2|xb vb tyb Hv2|cb tyb Hv2];
  try (rewrite Hv1 in Hv2; (injection Hv2; trivial) || apply Hv2); subst.
  now inversion 1.
  reflexivity.
Qed.

(* TRANSLATION *)
Axiom pos_of_str: string -> ident.
Axiom pos_to_str: ident -> string.
Definition self_id: ident := pos_of_str "self".
Definition main_id: ident := pos_of_str "main".

Definition type_of_inst (o: ident): typ :=
  Ctypes.Tstruct o Ctypes.noattr.
Definition pointer_of (ty: typ): typ :=
  Ctypes.Tpointer ty Ctypes.noattr.
Definition type_of_inst_p (o: ident): typ :=
  pointer_of (type_of_inst o).

Definition deref_self_field (cls x: ident) (ty: typ): Clight.expr :=
  let ty_deref_self := type_of_inst cls in
  let ty_self := pointer_of ty_deref_self in
  Clight.Efield (Clight.Ederef (Clight.Evar self_id ty_self) ty_deref_self) x ty.

Definition translate_const (c: const): typ -> Clight.expr :=
  match c with
  | Cint i => Clight.Econst_int i
  | Cfloat f => Clight.Econst_float f
  | Csingle s => Clight.Econst_single s
  | Clong l => Clight.Econst_long l
  end.

(** Straightforward expression translation *)
Definition translate_exp (cls: ident) (e: exp): Clight.expr :=
  match e with
  | Var x ty => Clight.Evar x ty  
  | State x ty =>
    deref_self_field cls x ty
  | Const c ty => translate_const c ty
  end.

(** 
Statement conversion keeps track of the produced temporaries (function calls).
[owner] represents the name of the current class.
 *)
Definition translate_stmt (owner: ident) (s: stmt): Clight.statement :=
  match s with
  | Assign x e =>
    Clight.Sassign (Clight.Evar x (typeof e)) (translate_exp owner e)
  | AssignSt x e =>
    Clight.Sassign (deref_self_field owner x (typeof e)) (translate_exp owner e)
  | Skip =>
    Clight.Sskip
  end.

Definition translate_obj_dec (obj: obj_dec): (ident * typ) :=
  match obj with
    mk_obj_dec inst cls =>
    (inst, type_of_inst cls)
  end.

Definition translate_class (c: class): Ctypes.composite_definition :=
  match c with
    mk_class name mems objs =>
    let objs := List.map translate_obj_dec objs in
    let members := mems ++ objs in
    Ctypes.Composite name Ctypes.Struct members Ctypes.noattr
  end.

Definition cl_zero: Clight.expr :=
  Clight.Econst_int Int.zero Ctypes.type_int32s.
Definition return_zero (s: Clight.statement): Clight.statement :=
  Clight.Ssequence s (Clight.Sreturn (Some cl_zero)).
                 
(** build the main function (entry point) *)
Definition make_main (body: Clight.statement) (vars: list (ident * typ))
  : AST.globdef Clight.fundef Ctypes.type :=
  let body := return_zero body in
  let main := Clight.mkfunction Ctypes.type_int32s AST.cc_default [] vars [] body in
  @AST.Gfun Clight.fundef typ (Clight.Internal main).

Definition glob_id (id: ident): ident :=
  pos_of_str ("_" ++ (pos_to_str id)).

Print program.
Definition translate (p: program) (main_node: ident)
  : Errors.res Clight.program :=
  let '(body, vars, cls) := p in
  let structs := List.map translate_class cls in
  let main := make_main (translate_stmt main_node body) vars in
  Clight.make_program structs [(main_id, main)] [] main_id.

(* SIMULATION *)

Section PRESERVATION.
 
  Variable main_node : ident.

  Variable prog: program.
  Variable tprog: Clight.program.
  Hypothesis TRANSL: translate prog main_node = Errors.OK tprog.
  
  (* Let ge := globalenv prog. *)
  Let tge := Clight.globalenv tprog.
  Let vars := snd (fst prog).
  
  Definition main_fun :=
    let '(body, vars, cls) := prog in
    Clight.mkfunction Ctypes.type_int32s AST.cc_default [] vars [] (translate_stmt main_node body).

  Inductive match_states: state -> Clight.state -> Prop :=
    state_intro: forall me ve s k e le m,
      match_states
        (me, ve, s)
        (Clight.State main_fun (translate_stmt main_node s) k e le m).

  Lemma type_pres:
    forall e, Clight.typeof (translate_exp main_node e) = typeof e.
  Proof.
    induction e; simpl; try reflexivity.
    destruct c; simpl; reflexivity.
  Qed.

  Lemma sem_cast_same:
    forall v t chunk,
      Ctypes.access_mode t = Ctypes.By_value chunk ->
      v <> Values.Vundef ->
      Values.Val.has_type v (Ctypes.typ_of_type t) ->
      Cop.sem_cast v t t = Some v.
  Proof.
    unfold Cop.sem_cast; intros v t c A U H.    
    destruct t eqn: E; simpl in *; try discriminate.
    - destruct i; destruct v; simpl in *; auto;
      try contradiction; try now contradict U.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
    - destruct v; simpl in *; auto;
      try contradiction; try now contradict U.
    - destruct f; destruct v; auto;
      try contradiction; try now contradict U.
    - destruct v; auto;
      try contradiction; try now contradict U.
  Qed.

  Definition ve_elts (ve: venv): list (ident * typ) :=
    List.map (fun (b: ident * (val * typ)) =>
                let (x, vt) := b in
                let (v, t) := vt in
                (x, t))
             (PM.elements ve).

  Remark ve_nil:
    forall ve, PM.elements ve = [] <-> ve_elts ve = [].
  Proof.  
    unfold ve_elts; split; intro H.
    - now rewrite H.
    - now apply map_eq_nil in H.
  Qed.
  
  Inductive tr_env: venv -> Clight.env -> Prop := 
    tr_env_intro: forall ve m e m',
      Clight.alloc_variables tge Clight.empty_env m (ve_elts ve) e m' ->
      tr_env ve e.
  
  Lemma tr_env_in:
    forall i ve v t e,
      PM.find i ve = Some (v, t) ->
      tr_env ve e ->
      exists loc, Maps.PTree.get i e = Some (loc, t).
  Proof.
    intros i ve v t e Hfind TRe.
    inversion TRe; subst.
    inversion H; subst.
    - apply PM.elements_correct in Hfind.
      symmetry in H3; apply ve_nil in H3.
      rewrite H3 in Hfind.
      exfalso; eapply in_nil; eauto.
    - admit.
  Qed.

  Lemma expr_eval:
    forall me ve exp v e le m m',
      Clight.alloc_variables tge Clight.empty_env m (tr_env ve) e m' ->
      exp_eval me ve exp v ->
      Clight.eval_expr tge e le m' (translate_exp main_node exp) (fst v).
  Proof.
    intros me ve exp; induction exp; inversion_clear 2; subst; simpl.    
    - assert (loc: Values.block). admit.
      apply Clight.eval_Elvalue with (loc:=loc) (ofs:=Int.zero). 
      + constructor. admit.
      + simpl. admit.
    - assert (loc: Values.block). admit.
      assert (ofs: Int.int). admit.
      assert (delta: Z). admit.
      assert (loc': Values.block). admit.
      assert (co: Ctypes.composite). admit.
      apply Clight.eval_Elvalue with (loc:=loc) (ofs:=Int.add ofs (Int.repr delta)). 
      + apply Clight.eval_Efield_struct with (id:=main_node) (co:=co) (att:=Ctypes.noattr). 
        *{ apply Clight.eval_Elvalue with (loc:=loc) (ofs:=ofs). 
           - constructor. apply Clight.eval_Elvalue with (loc:=loc') (ofs:=Int.zero).
             + constructor. admit.
             + apply Clight.deref_loc_value with (chunk:=AST.Mint32).
               * reflexivity. 
               * simpl. admit.
           - now apply Clight.deref_loc_copy.
         }
        * reflexivity.
        * admit.
        * admit.
      + simpl. admit.
    - destruct c; constructor.
  Qed.
  
  Theorem simu:
    forall S1 S2,
      stmt_eval prog S1 S2 ->
      forall S1',
        match_states S1 S1' ->
        exists S2' t,
            Smallstep.plus Clight.step1 tge S1' t S2'
            /\ match_states S2 S2'.
  Proof.
    induction 1; inversion_clear 1; simpl.
    - assert (m': Memory.Mem.mem). admit.
      assert (loc: Values.block). admit. 
      exists (Clight.State main_fun Clight.Sskip k e0 le m'); exists Events.E0; split.
      + apply Smallstep.plus_one.
        unfold Clight.step1.
        assert (exists c, Ctypes.access_mode (typeof e) = Ctypes.By_value c) as [c C]. admit.
        assert (v <> Values.Vundef) as V. admit.
        apply Clight.step_assign with (loc:=loc) (ofs:=Int.zero) (v2:=v) (v:=v).
        * constructor. admit.   (* x has to be present in the env before, cf local var *)
        * apply expr_eval with (1:=H).
        * rewrite type_pres; simpl.
          apply sem_cast_same with (1:=C) (2:=V).
          admit. 
        * simpl. apply Clight.assign_loc_value with (1:=C).
          simpl. admit.
      + constructor.
    - assert (m': Memory.Mem.mem). admit.
      assert (loc: Values.block). admit.
      assert (ofs: Int.int). admit.
      assert (loc': Values.block). admit.
      assert (delta: Z). admit.
      assert (co: Ctypes.composite). admit.
      exists (Clight.State main_fun Clight.Sskip k e0 le m'); exists Events.E0; split.
      + apply Smallstep.plus_one.
        unfold Clight.step1.
        assert (exists c, Ctypes.access_mode (typeof e) = Ctypes.By_value c) as [c C]. admit.
        assert (v <> Values.Vundef) as V. admit.
        apply Clight.step_assign with (loc:=loc) (ofs:=Int.add ofs (Int.repr delta)) (v2:=v) (v:=v).
        *{ apply Clight.eval_Efield_struct with (id:=main_node) (co:=co) (att:=Ctypes.noattr). 
           - apply Clight.eval_Elvalue with (loc:=loc) (ofs:=ofs). 
             + constructor. apply Clight.eval_Elvalue with (loc:=loc') (ofs:=Int.zero).
               * constructor. admit.
               *{ apply Clight.deref_loc_value with (chunk:=AST.Mint32).
                  - reflexivity. 
                  - simpl. admit.
                }
             + now apply Clight.deref_loc_copy.
           - reflexivity.
           - admit.
           - admit.
         }
        * apply expr_eval with (1:=H).
        * rewrite type_pres; simpl. admit.
        * simpl. apply Clight.assign_loc_value with (1:=C).
          simpl. admit.
      + constructor.
  Qed.