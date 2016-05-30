Require Import PArith.BinPos.

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

Record program : Type :=
  mk_prog {
      p_body : stmt;
      p_vars : list (ident * typ);
      p_cls  : list class 
    }.

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
Definition venv: Type := PM.t val.

Definition m_empty: menv := empty_memory _.
Definition v_empty: venv := PM.empty val.

Definition val_of_const c :=
  match c with
  | Cint i => Values.Vint i
  | Cfloat f => Values.Vfloat f
  | Csingle s => Values.Vsingle s
  | Clong l => Values.Vlong l
  end.
  
Inductive exp_eval (me: menv) (ve: venv): exp -> val -> Prop :=
| evar:
    forall x v ty,
      PM.MapsTo x v ve ->
      exp_eval me ve (Var x ty) v
(* | estate: *)
(*     forall x v ty, *)
(*       mfind_mem x me = Some v -> *)
(*       exp_eval me ve (State x ty) v *)
| econst:
    forall c ty,
      exp_eval me ve (Const c ty) (val_of_const c).

Definition state := (menv * venv * stmt)%type.

(* =stmt_eval= *)
Inductive stmt_eval :
  program -> state -> state -> Prop :=
| Iassign: forall prog me ve x e v ve',
    exp_eval me ve e v ->
    PM.add x v ve = ve' ->
    stmt_eval prog (me, ve, Assign x e) (me, ve', Skip)
(* | Iassignst: *)
(*   forall prog me ve x e v me', *)
(*     exp_eval me ve e v -> *)
(*     madd_mem x v me = me' -> *)
(*     stmt_eval prog (me, ve, AssignSt x e) (me', ve, Skip) *)
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
  inversion H1 as [xa va tya Hv1(* |xa va tya Hv1 *)|ca tya Hv1];
  inversion H2 as [xb vb tyb Hv2(* |xb vb tyb Hv2 *)|cb tyb Hv2];
  try (unfold PM.MapsTo in *; rewrite Hv1 in Hv2; (injection Hv2; trivial) || apply Hv2); subst.
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

Program Definition translate (p: program) (main_node: ident)
  : Errors.res Clight.program :=
  let structs := List.map translate_class p.(p_cls) in
  let main := make_main (translate_stmt main_node p.(p_body)) p.(p_vars) in
  Errors.bind (Ctypes.build_composite_env structs)
              (fun cenv => Errors.OK {| Clight.prog_defs := [(main_id, main)];
                 Clight.prog_public := [];
                 Clight.prog_main := main_id;
                 Clight.prog_types := structs;
                 Clight.prog_comp_env := cenv;
                 Clight.prog_comp_env_eq :=  _ |}).
Next Obligation.
  admit.
Defined.

  (* match Ctypes.build_composite_env structs with *)
  (* | Errors.OK cenv => *)
  (*   Errors.OK {| Clight.prog_defs := [(main_id, main)]; *)
  (*                Clight.prog_public := []; *)
  (*                Clight.prog_main := main_id; *)
  (*                Clight.prog_types := structs; *)
  (*                Clight.prog_comp_env := cenv; *)
  (*                Clight.prog_comp_env_eq :=  _ |} *)
  (* | Errors.Error msg => *)
  (*   Errors.Error msg *)
  (* end. *)
  (* Clight.make_program structs [(main_id, main)] [] main_id. *)

(* SIMULATION *)

Section PRESERVATION.

  Ltac inv := Coqlib.inv.
  
  Variable main_node : ident.

  Variable prog: program.
  Variable tprog: Clight.program.
  Hypothesis TRANSL: translate prog main_node = Errors.OK tprog.
  Hypothesis MAINNODE: exists c cls, find_class main_node prog.(p_cls) = Some (c, cls).
  
  (* Let ge := globalenv prog. *)
  Let tge := Clight.globalenv tprog.

  (* Hypothesis VE_IN_VARS: forall x v (ve: venv), PM.MapsTo x v ve -> exists t, In (x, t) prog.(p_vars). *)
  
  Definition main_fun :=
    Clight.mkfunction Ctypes.type_int32s AST.cc_default []
                      prog.(p_vars)
                          []
                          (translate_stmt main_node prog.(p_body)).
  
  Lemma type_pres:
    forall e, Clight.typeof (translate_exp main_node e) = typeof e.
  Proof.
    induction e; simpl; try reflexivity.
    destruct c; simpl; reflexivity.
  Qed.

  Lemma type_of_val:
    forall me ve e v,
      exp_eval me ve e v ->
      Values.Val.has_type v (Ctypes.typ_of_type (typeof e)).
  Proof.
    induction 1; simpl; admit.
  Qed.
  
  Lemma sem_cast_same:
    forall v t t',
      Ctypes.typ_of_type t = t' ->
      Ctypes.access_mode t = Ctypes.By_value (AST.chunk_of_type t') ->
      v <> Values.Vundef ->
      Values.Val.has_type v t' ->
      Cop.sem_cast v t t = Some v.
  Proof.
    unfold Cop.sem_cast; intros ** U H.    
    destruct t; simpl in *; subst; try discriminate.
    - destruct i; destruct v; destruct s; simpl in *; auto;
      try contradiction; try now contradict U.
    - destruct v; simpl in *; auto;
      try contradiction; try now contradict U.
    - destruct f; destruct v; auto;
      try contradiction; try now contradict U.
    - destruct v; auto;
      try contradiction; try now contradict U.
  Qed.

  Lemma build_co_ok:
    Ctypes.build_composite_env (map translate_class prog.(p_cls)) = Errors.OK (Clight.genv_cenv tge).
  Proof.
    unfold translate in TRANSL.
    Errors.monadInv TRANSL.
    admit.
  Qed.    

  Hypothesis BUILD_CO_OK:
    Ctypes.build_composite_env (map translate_class prog.(p_cls)) = Errors.OK (Clight.genv_cenv tge).

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
  
  Lemma tr_main_node:
    exists co,
      Maps.PTree.get main_node (Clight.genv_cenv tge) = Some co
      /\ (forall x t, In (x, t) (Ctypes.co_members co) ->
              exists delta,
                Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta).
  Proof.
    assert (tprog.(Clight.prog_types) = map translate_class prog.(p_cls)) as H.
    - admit.
    - destruct MAINNODE as [c [cls Hcls]].
      assert (In (translate_class c) tprog.(Clight.prog_types)) as Hin.
      + clear MAINNODE BUILD_CO_OK.
        induction (Clight.prog_types tprog); induction (p_cls prog); simpl in *. 
        * discriminate.
        * apply nil_cons in H; contradiction.
        * symmetry in H; apply nil_cons in H; contradiction.            
        *{ destruct (ident_eqb (c_name a0) main_node).
           - inversion Hcls; subst.
             inversion H. now left.
           - inversion H; subst.
             right. apply IHl. admit. (* how to do the induction ??? *)
         }
        (* induction prog.(p_cls). *)
        (* * simpl in *; discriminate. *)
        (* *{ simpl in *. *)
        (*    destruct (ident_eqb (c_name a) main_node). *)
        (*    - inversion_clear Hcls; subst. *)
        (*      apply in_eq. *)
        (*    - specialize (IHl Hcls tprog). *)
        (*      apply in_cons. *)
        (*  } *)
      + rewrite H in Hin.
        unfold translate_class at 1 in Hin.
        apply find_class_name in Hcls.
        destruct c; simpl in Hcls; subst.
        pose proof (Ctypes.build_composite_env_charact _ _ _ _ _ _ BUILD_CO_OK Hin) as [co Hco].
        exists co; split.
        * tauto.
        * intros ** Hx.
          admit.                (* how to get a witness ??? *)
  Qed.

  Inductive tr_vars: Clight.env -> Prop :=
    tr_vars_intro: forall m e m',
      Clight.alloc_variables tge Clight.empty_env m prog.(p_vars) e m' ->
      tr_vars e.

  Inductive tr_self: Clight.env -> Prop :=
    tr_self_intro: forall m e m',
      Clight.alloc_variables tge Clight.empty_env m [(self_id, pointer_of (type_of_inst main_node))] e m' ->
      tr_self e.

  (* Inductive legit_type: Ctypes.type -> Prop := *)
  (* | legit_tint: forall size sign attr, *)
  (*     legit_type (Ctypes.Tint size sign attr) *)
  (* | legit_tlong: forall sign attr, *)
  (*     legit_type (Ctypes.Tlong sign attr)  *)
  (* | legit_tfloat: forall size attr, *)
  (*     legit_type (Ctypes.Tfloat size attr). *)
  
  Inductive well_typed_exp: exp -> Prop :=
  | wt_var: forall x ty,
      (* legit_type ty -> *)
      In (x, ty) prog.(p_vars) ->
      well_typed_exp (Var x ty)
  | wt_const: forall c ty,
      (* legit_type ty -> *)
      well_typed_exp (Const c ty).

  Inductive well_typed: stmt -> Prop :=
  | wt_assign: forall x e,
      well_typed_exp e ->
      well_typed (Assign x e)
  | wt_skip: well_typed Skip.
  
  Inductive well_assigned_exp: exp -> Prop :=
  | wa_var: forall x ty,
      (exists m, forall chunk loc v m', Memory.Mem.store chunk m loc 0 v = Some m') ->
      well_assigned_exp (Var x ty)
  | wa_const: forall c ty,
      well_assigned_exp (Const c ty).
  
  Inductive well_assigned: stmt -> Clight.env -> Prop :=
  | wa_assign: forall x e env loc,
      well_assigned_exp e ->
      Maps.PTree.get x env = Some (loc, typeof e) ->
      well_assigned (Assign x e) env
  | wa_skip: forall env,
      well_assigned Skip env.

  Inductive compat_mem: menv -> venv -> Memory.Mem.mem -> Prop :=
    compat_mem_intro: forall menv venv mem,
      compat_mem menv venv mem.
    
  Inductive match_states: state -> Clight.state -> Prop :=
    state_intro: forall menv venv s k env lenv mem,
      tr_vars env ->
      well_typed s ->
      well_assigned s env ->
      compat_mem menv venv mem ->
      match_states
        (menv, venv, s)
        (Clight.State main_fun (translate_stmt main_node s) k env lenv mem).

  Remark allocated_is_in_env_aux:
    forall x loc t env m vars env' m',
      Clight.alloc_variables tge (Maps.PTree.set x (loc, t) env) m vars env' m' ->
      Maps.PTree.get x env' = Some (loc, t).
  Proof.
    admit.
  Qed.
  
  Remark allocated_is_in_env:
    forall l x t m e e' m',
      Clight.alloc_variables tge e m l e' m' ->
      In (x, t) l ->
      exists loc, Maps.PTree.get x e' = Some (loc, t).
  Proof.
    clear TRANSL MAINNODE BUILD_CO_OK.
    induction 1 as [|? ? ? ? ? ? loc ? ? Malloc Alloc]; intro Hin.
    - exfalso; eapply in_nil; eauto.
    - destruct Hin as [H|]; auto.
      inv H; exists loc.
      eapply allocated_is_in_env_aux; eauto.
  Qed.
  
  Lemma tr_env_in:
    forall x t (ve: venv) v e,
      PM.MapsTo x v ve ->
      In (x, t) prog.(p_vars) ->
      tr_vars e ->
      exists loc, Maps.PTree.get x e = Some (loc, t).
  Proof.
    intros ** Hfind Hin TRe.
    inv TRe.
    eapply allocated_is_in_env; eauto.
  Qed.

  Lemma tr_self_in:
    forall e,
      tr_self e ->
      exists loc, Maps.PTree.get self_id e = Some (loc, pointer_of (type_of_inst main_node)).
  Proof.
    intros ** TRe.
    inv TRe.
    eapply allocated_is_in_env; eauto; simpl; auto.
  Qed.

  Notation "( x : t )" := (Clight.Evar x t) (at level 67).
  Notation "(self --> x ) : t" := (deref_self_field main_node x t) (at level 67).
  Notation "^self" := (Clight.Ederef
                         (Clight.Evar self_id (pointer_of (type_of_inst main_node)))
                         (type_of_inst main_node))
                        (at level 67).

  
  Hint Constructors Clight.eval_lvalue well_typed well_assigned match_states.
  
  Lemma expr_eval:
    forall me ve exp v chunk e le m',
      tr_vars e ->
      well_typed_exp exp ->
      well_assigned_exp exp ->
      Values.Val.load_result chunk v = v ->
      Ctypes.access_mode (typeof exp) = Ctypes.By_value chunk ->
      exp_eval me ve exp v ->
      Clight.eval_expr tge e le m' (translate_exp main_node exp) v.
  Proof.
    intros me ve exp;
    induction exp as [x ty|x ty|c ty];
    intros ** Hvars Hwt Hwa Hload Haccess Heval;
    inversion Heval as [? ? ? Hmto(* |? ? ? Hmem *)|];
    inversion Hwt as [? ? Hin|];
    inversion Hwa as [? ? [m Hstore]|];
    revert Hload; subst; simpl in *; intro Hload.    
    - destruct (tr_env_in _ _ _ _ _ Hmto Hin Hvars) as [loc Hget].  
      apply Clight.eval_Elvalue with (loc:=loc) (ofs:=Int.zero); eauto.
      eapply Clight.deref_loc_value; eauto.
      rewrite <-Hload.
      now apply Memory.Mem.load_store_same with m.         
    (* - assert (loc: Values.block). admit. *)
    (*   assert (ofs: Int.int). admit. (* where are they comin' from ??? *) *)
    (*   destruct tr_main_node as [co [Hco Hdelta]]. *)
    (*   destruct (Hdelta x t) as [delta Hdelta']. admit. *)
    (*   apply Clight.eval_Elvalue with (loc:=loc) (ofs:=Int.add ofs (Int.repr delta)).  *)
    (*   + apply Clight.eval_Efield_struct with (id:=main_node) (co:=co) (att:=Ctypes.noattr); auto.  *)
    (*     *{ apply Clight.eval_Elvalue with (loc:=loc) (ofs:=ofs).  *)
    (*        - constructor. *)
    (*          destruct (tr_self_in _ Hself) as [loc']. *)
    (*          apply Clight.eval_Elvalue with (loc:=loc') (ofs:=Int.zero). *)
    (*          + now constructor.  *)
    (*          + apply Clight.deref_loc_value with (chunk:=AST.Mint32). *)
    (*            * reflexivity.  *)
    (*            * simpl. admit.  (* LOAD *) *)
    (*        - now apply Clight.deref_loc_copy. *)
    (*      } *)
    (*   + eapply Clight.deref_loc_value; eauto. simpl. admit. (* LOAD *) *)
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
    induction 1 as [? ? ? ? ? ? ? Heval Hve(* |? ? ? ? ? ? ? Heval Hmem *)];
    inversion_clear 1 as [? ? ? ? env ? ? Hvars Hwt Hwa]; simpl.
    - assert (m': Memory.Mem.mem). admit. (* memory state after statement step *)
      exists (Clight.State main_fun Clight.Sskip k env lenv m'); exists Events.E0; split.
      + apply Smallstep.plus_one.
        unfold Clight.step1.
        assert (Ctypes.access_mode (typeof e) = Ctypes.By_value (AST.chunk_of_type (Ctypes.typ_of_type (typeof e)))). admit.
        assert (v <> Values.Vundef) as V. admit.
        inv Hwt.
        inv Hwa.
        apply Clight.step_assign with (loc:=loc) (ofs:=Int.zero) (v2:=v) (v:=v); auto.
        * eapply expr_eval; eauto. admit. (*  *)
        * rewrite type_pres; simpl.
          eapply sem_cast_same; eauto.
          eapply type_of_val; eauto. (* seems pretty wrong... *)
        * eapply Clight.assign_loc_value; eauto. 
          simpl. admit.         (* STORE *)
      + now constructor.
    (* - assert (m': Memory.Mem.mem). admit. (* memory state after statement step *) *)
    (*   assert (loc: Values.block). admit. *)
    (*   assert (ofs: Int.int). admit. *)
    (*   exists (Clight.State main_fun Clight.Sskip k env le m'); exists Events.E0; split. *)
    (*   + apply Smallstep.plus_one. *)
    (*     unfold Clight.step1. *)
    (*     destruct v as [v t]. *)
    (*     assert (Ctypes.access_mode t = Ctypes.By_value (AST.chunk_of_type (Ctypes.typ_of_type (typeof e)))). admit. *)
    (*     assert (t = typeof e) as Ht by now inversion Heval.  *)
    (*     destruct tr_main_node as [co [Hco Hdelta]]. *)
    (*     destruct (Hdelta x t) as [delta Hdelta']. admit.         *)
    (*     subst. *)
    (*     assert (v <> Values.Vundef) as V. admit. *)
    (*     apply Clight.step_assign with (loc:=loc) (ofs:=Int.add ofs (Int.repr delta)) (v2:=v) (v:=v). *)
    (*     *{ apply Clight.eval_Efield_struct with (id:=main_node) (co:=co) (att:=Ctypes.noattr); auto.  *)
    (*       apply Clight.eval_Elvalue with (loc:=loc) (ofs:=ofs).  *)
    (*        - constructor. *)
    (*          destruct (tr_self_in _ Hself) as [loc']. *)
    (*          apply Clight.eval_Elvalue with (loc:=loc') (ofs:=Int.zero). *)
    (*          + now constructor.  *)
    (*          + apply Clight.deref_loc_value with (chunk:=AST.Mint32). *)
    (*            * reflexivity.  *)
    (*            * simpl. admit.  (* LOAD *) *)
    (*        - now apply Clight.deref_loc_copy. *)
    (*      } *)
    (*     * eapply expr_eval; eauto.  *)
    (*     * rewrite type_pres; simpl. *)
    (*       eapply sem_cast_same; eauto. *)
    (*       eapply type_of_val; eauto. (* seems pretty wrong... *) *)
    (*     * eapply Clight.assign_loc_value; eauto.  *)
    (*       simpl. admit.         (* STORE *) *)
    (*   + now constructor. *)
  Qed.