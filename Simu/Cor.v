Require cfrontend.ClightBigstep.
Require cfrontend.Clight.
Require Import lib.Integers.

Require Import Rustre.Common.
Require Import Rustre.RMemory.
Require Import Rustre.Nelist.

Require Import Syn Sem Tra.

Require Import Program.Tactics.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import LibTactics.
Ltac auto_star ::= try solve [eassumption | auto | jauto].

(* SIMULATION *)

Section PRESERVATION.

  Variable main_node : ident.
  Variable prog: program.
  Variable tprog: Clight.program.
   
  (* Let ge := globalenv prog. *)
  Let tge := Clight.globalenv tprog.

  Definition chunk_of_typ ty := AST.chunk_of_type (Ctypes.typ_of_type ty).
  Definition pointer_of_node node := pointer_of (type_of_inst node).

  Hypothesis TRANSL: translate prog main_node = Errors.OK tprog.
  Hypothesis STEPS:
    forall c (e: Clight.env),
      In c prog ->
      exists loc_f f,
        Globalenvs.Genv.find_symbol tge.(Clight.genv_genv) (step_id c.(c_name)) = Some loc_f
        /\ Maps.PTree.get (step_id c.(c_name)) e = None
        /\ Globalenvs.Genv.find_funct_ptr tge.(Clight.genv_genv) loc_f = Some (Clight.Internal f)
        /\ Clight.type_of_fundef (Clight.Internal f) =
          Ctypes.Tfunction (Ctypes.Tcons (type_of_inst_p c.(c_name))
                                         (list_type_to_typelist (map snd (nelist2list c.(c_input)))))
                                         (snd c.(c_output))
                                         AST.cc_default
        /\ Coqlib.list_norepet (Clight.var_names (Clight.fn_params f) ++ Clight.var_names (Clight.fn_vars f))
        /\ Clight.fn_body f = snd (translate_stmt None c.(c_name) c.(c_step))
        /\ length f.(Clight.fn_params) = 1 + Nelist.length c.(c_input)  
        /\ Forall (fun x => Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_typ (snd x)))
                 (f.(Clight.fn_params) ++ f.(Clight.fn_vars)).
  
  (* Hypothesis WF: well_formed prog. *)
  (* Hypothesis MAINNODE: find_class main_node prog = Some (c_main, cls_main). *)

  (* Lemma build_co_ok: *)
  (*   Ctypes.build_composite_env (map translate_class prog) = Errors.OK (Clight.genv_cenv tge). *)
  (* Proof. *)
  (*   admit. *)
  (* Qed. *)
  
    
  (* Definition main_fun := *)
  (*   Clight.mkfunction Ctypes.type_int32s AST.cc_default [] *)
  (*                     c_main.(c_vars) *)
  (*                         [] *)
  (*                         (translate_stmt main_node c_main.(c_step)). *)
  
  Lemma type_pres:
    forall c e, Clight.typeof (translate_exp c.(c_name) e) = typeof e.
  Proof.
    induction e as [| |cst]; simpl; try reflexivity.
    destruct cst; simpl; reflexivity.
  Qed.

  Definition valid_val (v: val) (t: typ): Prop :=
    Ctypes.access_mode t = Ctypes.By_value (chunk_of_typ t)
    /\ v <> Values.Vundef
    /\ Values.Val.has_type v (Ctypes.typ_of_type t).

  Lemma sem_cast_same:
    forall v t,
      valid_val v t ->
      Cop.sem_cast v t t = Some v.
  Proof.
    unfold valid_val; intros; destruct_pairs.
    destruct t, v;
      (destruct i, s || destruct f || idtac);
      (discriminates || contradiction || auto).
  Qed.

  Inductive well_formed_exp (c: class): exp -> Prop :=
  | wf_var: forall x ty,
      In (x, ty) c.(c_vars) ->
      x <> self_id ->
      well_formed_exp c (Var x ty)
  | wf_state: forall x ty,
      In (x, ty) c.(c_mems) ->
      well_formed_exp c (State x ty)
  | wf_const: forall cst ty,
      well_formed_exp c (Const cst ty).

  Inductive well_formed_stmt (c: class) (S: state): stmt -> Prop :=
  | wf_assign: forall x e v,
      In (x, typeof e) c.(c_vars) ->
      x <> self_id ->
      well_formed_exp c e ->
      exp_eval S e v ->
      valid_val v (typeof e) ->
      v = Values.Val.load_result (chunk_of_typ (typeof e)) v ->
      well_formed_stmt c S (Assign x e)
  | wf_assignst: forall x e v,
      In (x, typeof e) c.(c_mems) ->
      x <> self_id ->
      well_formed_exp c e ->
      exp_eval S e v ->
      valid_val v (typeof e) ->
      v = Values.Val.load_result (chunk_of_typ (typeof e)) v ->
      well_formed_stmt c S (AssignSt x e)
  | wf_ite: forall e s1 s2,
      well_formed_exp c e ->
      well_formed_stmt c S s1 ->
      well_formed_stmt c S s2 ->
      well_formed_stmt c S (Ifte e s1 s2)
  | wf_comp: forall S' s1 s2,
      well_formed_stmt c S s1 ->
      stmt_eval prog S s1 S' ->
      well_formed_stmt c S' s2 ->
      well_formed_stmt c S (Comp s1 s2)
  | wf_step: forall y ty c' prog' clsid o es vs me me' rv,
      In (y, ty) c.(c_vars) ->
      y <> self_id ->
      In {| obj_inst := o; obj_class := clsid |} c.(c_objs) ->
      find_class clsid prog = Some (c', prog') ->
      Nelist.Forall (well_formed_exp c) es ->
      Nelist.Forall2 (exp_eval S) es vs ->
      Nelist.Forall2 (fun e v => valid_val v (typeof e)) es vs ->
      Nelist.Forall2 (fun e x => typeof e = snd x) es c'.(c_input) ->
      ty = snd c'.(c_output) ->
      find_inst o S me ->
      stmt_step_eval prog me clsid vs me' rv ->
      valid_val rv ty ->
      rv = Values.Val.load_result (chunk_of_typ ty) rv ->
      well_formed_stmt c S (Step_ap y ty clsid o es)
  | wf_skip: 
      well_formed_stmt c S Skip.

  Definition compat_vars (c: class) (e: Clight.env) (m: Memory.Mem.mem): Prop :=
    forall x t,
      In c prog ->
      In (x, t) c.(c_vars) ->
      exists loc,
        Maps.PTree.get x e = Some (loc, t)
        /\ Memory.Mem.valid_access m (chunk_of_typ t) loc 0 Memtype.Writable.

  Definition compat_self (c: class) (e: Clight.env) (m: Memory.Mem.mem): Prop :=
    In c prog ->
    exists co loc_self loc_struct ofs,
      Maps.PTree.get self_id e = Some (loc_self, pointer_of_node c.(c_name))
      /\ Memory.Mem.load AST.Mint32 m loc_self 0 = Some (Values.Vptr loc_struct ofs)
      /\ Maps.PTree.get c.(c_name) tge.(Clight.genv_cenv) = Some co
      /\ (forall x t,
            In (x, t) c.(c_mems) ->
            exists delta,
              Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta
              /\ In (x, t) (Ctypes.co_members co)
              /\ Memory.Mem.valid_access m (chunk_of_typ t) loc_struct (Int.unsigned (Int.add ofs (Int.repr delta))) Memtype.Writable)
      /\ (forall o,
            In o c.(c_objs) ->
            exists delta,
              Ctypes.field_offset (Clight.genv_cenv tge) o.(obj_inst) (Ctypes.co_members co) = Errors.OK delta).

  (* Definition compat_fields (c: class) (e: Clight.env) (m: Memory.Mem.mem): Prop := *)
  (*   forall x t co loc_self loc_struct ofs, *)
  (*     In c prog -> *)
  (*     In (x, t) c.(c_mems) -> *)
  (*     Maps.PTree.get self_id e = Some (loc_self, pointer_of_node c.(c_name)) -> *)
  (*     Memory.Mem.load AST.Mint32 m loc_self 0 = Some (Values.Vptr loc_struct ofs) -> *)
  (*     Maps.PTree.get c.(c_name) tge.(Clight.genv_cenv) = Some co ->      *)
  (*     exists delta, *)
  (*       Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta *)
  (*       /\ In (x, t) (Ctypes.co_members co) *)
  (*       /\ Memory.Mem.valid_access m (chunk_of_typ t) loc_struct (Int.unsigned (Int.add ofs (Int.repr delta))) Memtype.Writable. *)
  
  Definition compat_venv (c: class) (S: state) (e: Clight.env) (m: Memory.Mem.mem):  Prop :=
    forall x v t loc,
      In c prog ->
      In (x, t) c.(c_vars) ->
      Maps.PTree.get x e = Some (loc, t) ->
      find_var x S v ->
      Memory.Mem.load (chunk_of_typ t) m loc 0 = Some v
      /\ valid_val v t.
  
  Definition compat_menv (c: class) (S: state) (e: Clight.env) (m: Memory.Mem.mem):  Prop :=
    forall x v t co loc_self loc_struct ofs delta,
      In c prog -> 
      In (x, t) c.(c_mems) ->
      find_field x S v ->
      Maps.PTree.get self_id e = Some (loc_self, pointer_of_node c.(c_name)) ->
      Memory.Mem.load AST.Mint32 m loc_self 0 = Some (Values.Vptr loc_struct ofs) ->
      Maps.PTree.get c.(c_name) tge.(Clight.genv_cenv) = Some co ->
      Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta ->
      Memory.Mem.load (chunk_of_typ t) m loc_struct (Int.unsigned (Int.add ofs (Int.repr delta))) = Some v
      /\ valid_val v t.
  
  Remark valid_val_implies_access:
    forall v t, valid_val v t -> Ctypes.access_mode t = Ctypes.By_value (chunk_of_typ t).
  Proof. introv H; apply H. Qed.
    
  Hint Constructors Clight.eval_lvalue Clight.eval_expr well_formed_stmt.
  Hint Resolve valid_val_implies_access.

  Remark eval_var:
    forall c S e le m x t v,
      compat_vars c e m ->
      compat_venv c S e m ->
      In c prog ->
      In (x, t) c.(c_vars) ->
      find_var x S v ->
      Clight.eval_expr tge e le m (Clight.Evar x t) v.
  Proof.
    introv Hvars Hvenv ? ? ?.
    edestruct Hvars; eauto.
    edestruct Hvenv; iauto.
    eapply Clight.eval_Elvalue, Clight.deref_loc_value; iauto. 
  Qed.

  Remark evall_self_field:
    forall c e le m x t co loc_self loc_struct ofs delta,
      Maps.PTree.get self_id e = Some (loc_self, pointer_of_node (c_name c)) ->
      Memory.Mem.load AST.Mint32 m loc_self 0 = Some (Values.Vptr loc_struct ofs) ->
      Maps.PTree.get (c_name c) (Clight.genv_cenv tge) = Some co ->
      Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta ->
      Clight.eval_lvalue tge e le m (deref_self_field c.(c_name) x t) loc_struct (Int.add ofs (Int.repr delta)).
  Proof.
    intros.
    eapply Clight.eval_Efield_struct
    with (id:=c.(c_name)) (att:=Ctypes.noattr); eauto.
    eapply Clight.eval_Elvalue. 
    - apply Clight.eval_Ederef. 
      apply* Clight.eval_Elvalue.
      apply* Clight.deref_loc_value.
      reflexivity.
    - apply* Clight.deref_loc_copy.
  Qed.
  
  Remark eval_self_field:
    forall c S e le m x t v,
      compat_self c e m ->
      compat_menv c S e m ->
      In c prog ->
      In (x, t) c.(c_mems) ->
      find_field x S v ->
      Clight.eval_expr tge e le m (deref_self_field c.(c_name) x t) v.
  Proof.
    introv Hself Hmenv ? Hin ?.
    destruct* Hself as (? & ? & ? & ? & ? & ? & ? & Hmem & ?).  
    specializes Hmem Hin; destruct_conjs.
    edestruct Hmenv; eauto; destruct_conjs. 
    eapply Clight.eval_Elvalue.
    + apply* evall_self_field.
    + apply* Clight.deref_loc_value.      
  Qed.
  
  Lemma expr_eval_simu:
    forall c S exp v e le m,
      compat_vars c e m ->
      compat_self c e m ->
      compat_venv c S e m ->
      compat_menv c S e m ->
      In c prog ->
      well_formed_exp c exp ->
      exp_eval S exp v ->
      Clight.eval_expr tge e le m (translate_exp c.(c_name) exp) v.
  Proof.
    intros c S exp; induction exp as [| |cst];
    introv ? ? ? ? ? Hwf Heval; inverts Heval; inverts Hwf.

    (* Var x ty : "x" *)
    - apply* eval_var.
      
    (* State x ty : "self->x" *)
    - apply* eval_self_field.
      
    (* Const c ty : "c" *)
    - destruct cst; constructor.
  Qed.

  Lemma exprs_eval_simu:
    forall c S es es' vs e le m,
      compat_vars c e m ->
      compat_self c e m ->
      compat_venv c S e m ->
      compat_menv c S e m ->
      In c prog ->
      Nelist.Forall (well_formed_exp c) es ->
      Nelist.Forall2 (fun e v => valid_val v (typeof e)) es vs ->
      Nelist.Forall2 (exp_eval S) es vs ->
      es' = nelist2list (Nelist.map (translate_exp c.(c_name)) es) ->
      Clight.eval_exprlist tge e le m es' (list_type_to_typelist (map Clight.typeof es')) (nelist2list vs).
  Proof.
    Hint Constructors Clight.eval_exprlist.
    introv ? ? ? ? ? Hwf Hvalid Hev ?; subst es';
    induction Hev; inverts Hwf; inverts Hvalid; econstructor;
    (apply* expr_eval_simu || (rewrite type_pres; apply* sem_cast_same) || eauto).
  Qed.

  Definition nodup_env (e: Clight.env) :=
    forall x x' loc t t',
      x' <> x ->
      Maps.PTree.get x e = Some (loc, t) ->
      Maps.PTree.get x' e <> Some (loc, t').

  Definition nodup_fields (co: Ctypes.composite) :=
    forall x t t',
      In (x, t) (Ctypes.co_members co) ->
      In (x, t') (Ctypes.co_members co) ->
      t' = t.

  Definition nodup_vars (c: class) :=
    forall x t t',
      In (x, t) c.(c_vars) ->
      In (x, t') c.(c_vars) ->
      t' = t.

   Definition nodup_mems (c: class) :=
    forall x t t',
      In (x, t) c.(c_mems) ->
      In (x, t') c.(c_mems) ->
      t' = t.
  
  Remark find_add:
    forall x (v v': val) pm, 
      PM.find x (PM.add x v pm) = Some v' -> v' = v.
  Proof.
    induction x, pm; simpl; (eauto || now injection 1).
  Qed.

  Remark find_update_var:
    forall x v v' S,
      find_var x (update_var x S v) v' -> v' = v.
  Proof.
    unfold find_var, update_var; simpl.
    intros; apply* find_add.
  Qed.

  Remark find_update_field:
    forall x v v' S,
      find_field x (update_field x S v) v' -> v' = v.
  Proof.
    unfold find_field, update_field, mfind_mem, madd_mem; simpl.
    intros; apply* find_add.
  Qed.

  Remark gso_var:
    forall x x' v v' S,
      x <> x' -> find_var x (update_var x' S v) v' -> find_var x S v'.
  Proof.
    unfold find_var, update_var; simpl.
    introv Neq H.
    rewrite <-H; symmetry.
    apply* PM.gso.
  Qed.

  Remark gso_field:
    forall x x' v v' S,
      x <> x' -> find_field x (update_field x' S v) v' -> find_field x S v'.
  Proof.
    unfold find_field, update_field; simpl.
    introv Neq H.
    rewrite <-H; symmetry.
    apply* mfind_mem_gso.
  Qed.
  
  Definition mem_sep (c: class) (e: Clight.env) (m: Memory.Mem.mem) :=
    forall x loc t loc_self loc_struct ofs,
      In (x, t) c.(c_vars) -> 
      Maps.PTree.get x e = Some (loc, t) ->
      Maps.PTree.get self_id e = Some (loc_self, pointer_of_node c.(c_name)) ->
      Memory.Mem.load AST.Mint32 m loc_self 0 = Some (Values.Vptr loc_struct ofs) ->
      loc <> loc_struct.

  Definition self_sep (c: class) (e: Clight.env) (m: Memory.Mem.mem) :=
    forall loc_self loc_struct ofs,
      Maps.PTree.get self_id e = Some (loc_self, pointer_of_node c.(c_name)) ->
      Memory.Mem.load AST.Mint32 m loc_self 0 = Some (Values.Vptr loc_struct ofs) ->
      loc_struct <> loc_self.

  Definition fields_sep (m: Memory.Mem.mem) :=
    forall co x x' t t' ofs delta delta',
      x <> x' ->
      Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta ->
      Ctypes.field_offset (Clight.genv_cenv tge) x' (Ctypes.co_members co) = Errors.OK delta' ->
      (BinInt.Z.le
         (BinInt.Z.add (Int.unsigned (Int.add ofs (Int.repr delta')))
                       (Memdata.size_chunk (chunk_of_typ t')))
         (Int.unsigned (Int.add ofs (Int.repr delta)))
       \/
       BinInt.Z.le
         (BinInt.Z.add (Int.unsigned (Int.add ofs (Int.repr delta)))
                       (Memdata.size_chunk (chunk_of_typ t)))
         (Int.unsigned (Int.add ofs (Int.repr delta')))).

  Definition c_state := (Clight.env * Clight.temp_env * Memory.Mem.mem)%type.
   
  Inductive match_states_bigbig (c: class) (S: state): c_state -> Prop :=
    intro_state_bigbig: forall e le m,
      (* state correspondance *)
      compat_venv c S e m ->     
      compat_menv c S e m ->
      
      (* Clight state well defined *)
      compat_vars c e m ->
      compat_self c e m ->

      (* Clight side separation *)
      mem_sep c e m ->
      self_sep c e m ->
      fields_sep m ->
      nodup_env e ->

      (* Minimp side separation *)
      nodup_vars c ->
      nodup_mems c ->
      match_states_bigbig c S (e, le, m).

  Hint Constructors match_states_bigbig.
  
  Remark load_same:
    forall env x t x' t' m m' chk loc loc' v vptr vptr',
      nodup_env env ->
      x <> x' ->
      Maps.PTree.get x env = Some (loc, t) ->
      Maps.PTree.get x' env = Some (loc', t') ->
      Memory.Mem.store chk m loc 0 v = Some m' ->
      Memory.Mem.load AST.Mint32 m loc' 0 = Some vptr ->
      Memory.Mem.load AST.Mint32 m' loc' 0 = Some vptr' ->
      vptr' = vptr.
  Proof.
    introv Hnodupenv ? ? ? ? Hload Hload'.
    destruct (Values.eq_block loc loc').
      + subst loc.
        edestruct Hnodupenv; eauto.
      + assert (Memory.Mem.load AST.Mint32 m' loc' 0 = Memory.Mem.load AST.Mint32 m loc' 0)
          as Eq by apply* Memory.Mem.load_store_other.
        rewrite Eq in Hload'; rewrite Hload' in Hload; inverts Hload.
        reflexivity.        
  Qed.
  
  Lemma compat_assign_pres:
    forall c S e le m loc x t v,
      In c prog ->
      match_states_bigbig c S (e, le, m) ->
      Maps.PTree.get x e = Some (loc, t) ->
      In (x, t) c.(c_vars) ->
      v = Values.Val.load_result (chunk_of_typ t) v ->
      valid_val v t ->
      x <> self_id ->
      exists m', Memory.Mem.store (chunk_of_typ t) m loc 0 v = Some m' 
            /\ match_states_bigbig c (update_var x S v) (e, le, m').
  Proof.
    introv ? MS Hget Hin Hloadres ? ?.
    inverts MS as Hvenv Hmenv Hvars Hself Hsep Hself_sep Hfields_sep Hnodupenv;
      introv Hnodupvars Hnodupmems.
    edestruct Hvars as (loc' & Hget' & ?); eauto.
    rewrite Hget' in Hget; inverts Hget; rename Hget' into Hget.
    edestruct Memory.Mem.valid_access_store with (v:=v) as [m']; eauto.
    destruct* Hself as (co & loc_self & loc_struct & ofs & Hget_self & Hload_self & Hget_co & Hmem & ?).
    exists m'; split*; constructor*.

    - unfold compat_venv; intros x' v' t' loc' ? Hin' Hget' Hfind.
      destruct (AST.ident_eq x' x).
      + subst x'.
        apply find_update_var in Hfind; subst v'.
        specializes Hnodupvars Hin Hin'; subst t'. 
        split*.
        destruct (Values.eq_block loc' loc) as [|Neq].
        * subst loc'.
          rewrite Hloadres; apply* Memory.Mem.load_store_same.
        * rewrite Hget in Hget'; inverts Hget'. now contradict Neq. 
      + apply gso_var in Hfind; auto.
        edestruct Hvenv as (Hload); eauto.
        split*.
        destruct (Values.eq_block loc' loc).
        * subst loc'.
          edestruct Hnodupenv; eauto. 
        * rewrite <-Hload. 
          apply* Memory.Mem.load_store_other.

    - unfold compat_menv;
      introv ? ? ? Hget_self' Hload_self' Hget_co' ?.
      rewrite Hget_self' in Hget_self; inverts Hget_self.
      rewrite Hget_co' in Hget_co; inverts Hget_co.
      edestruct Hmenv as (Hload); eauto.
      split*.
      forwards* Eq: load_same; inverts Eq.
      destruct (Values.eq_block loc loc_struct).
      + edestruct Hsep; eauto.
      + rewrite <-Hload.
        apply* Memory.Mem.load_store_other.

    - unfold compat_vars; intros.
      edestruct Hvars as (loc'); eauto.
      exists loc'; split*.
      apply* Memory.Mem.store_valid_access_1.

    - unfold compat_self; intro.
      exists co loc_self loc_struct ofs.
      splits*.
      + destruct (Values.eq_block loc_self loc).
        * subst loc.
          edestruct Hnodupenv; eauto.
        * rewrite <-Hload_self.
          apply* Memory.Mem.load_store_other.
      + introv Hin'.
        specializes Hmem Hin'; destruct Hmem as (delta).
        exists delta; splits*.
        apply* Memory.Mem.store_valid_access_1.

    - unfold mem_sep; introv ? ? Hget_self' ?.
      rewrite Hget_self' in Hget_self; inverts Hget_self.
      forwards* Eq: load_same; inverts Eq.
      apply* Hsep.

    - unfold self_sep; introv Hget_self' ?.
      rewrite Hget_self' in Hget_self; inverts Hget_self.
      forwards* Eq: load_same; inverts Eq.
      apply* Hself_sep.
  Qed.

  Remark load_same':
    forall c env m m' chk loc' v ofs loc1 ofs1 loc2 ofs2,
      self_sep c env m ->
      Maps.PTree.get self_id env = Some (loc', pointer_of_node c.(c_name)) ->
      Memory.Mem.store chk m loc1 ofs v = Some m' ->
      Memory.Mem.load AST.Mint32 m loc' 0 = Some (Values.Vptr loc1 ofs1) ->
      Memory.Mem.load AST.Mint32 m' loc' 0 = Some (Values.Vptr loc2 ofs2) ->
      Values.Vptr loc1 ofs1 = Values.Vptr loc2 ofs2.
  Proof.
    introv Hself_sep ? ? Hload1 Hload2.
    assert (Memory.Mem.load AST.Mint32 m' loc' 0 = Memory.Mem.load AST.Mint32 m loc' 0)
      as Eq.
    apply* Memory.Mem.load_store_other.
    left; intro Eq; symmetry in Eq; revert Eq; apply* Hself_sep.
    rewrite Eq in Hload2; rewrite Hload2 in Hload1; inverts Hload1.
    reflexivity.
  Qed.

  Lemma compat_stassign_pres:
    forall c S e le m x t v co loc_self loc_struct ofs delta,
      In c prog ->
      match_states_bigbig c S (e, le, m) ->
      Ctypes.field_offset tge.(Clight.genv_cenv) x (Ctypes.co_members co) = Errors.OK delta ->
      Maps.PTree.get c.(c_name) (Clight.genv_cenv tge) = Some co ->
      Maps.PTree.get self_id e = Some (loc_self, pointer_of_node c.(c_name)) ->
      Memory.Mem.load AST.Mint32 m loc_self 0 = Some (Values.Vptr loc_struct ofs) ->
      In (x, t) c.(c_mems) ->
      v = Values.Val.load_result (chunk_of_typ t) v ->
      valid_val v t ->
     Memory.Mem.valid_access m (chunk_of_typ t) loc_struct (Int.unsigned (Int.add ofs (Int.repr delta))) Memtype.Writable ->
      exists m',
        Memory.Mem.store (chunk_of_typ t) m loc_struct (Int.unsigned (Int.add ofs (Int.repr delta))) v = Some m'
        /\ match_states_bigbig c (update_field x S v) (e, le, m').
  Proof.
    intros ** ? MS Hoffset Hget_co Hget_self Hload_self Hin Hloadres ? ? .
    inverts MS as Hvenv Hmenv Hvars Hself Hsep Hself_sep Hfields_sep Hnodupenv;
      introv Hnodupvars Hnodupmems.
    edestruct Memory.Mem.valid_access_store with (v:=v) as [m']; eauto. 
    exists m'; split*; constructor*.

    - unfold compat_venv; intros ** loc ? ? ? ?. 
      edestruct Hvenv as (Hload); eauto.  
      split*.
      destruct (Values.eq_block loc loc_struct).
      + edestruct Hsep; eauto.
      + rewrite <-Hload.
        apply* Memory.Mem.load_store_other.

    - unfold compat_menv. intros x' v' t' ? ? ? ? ? ? Hin' Hfind' Hget_self' Hload_self' Hget_co' Hoffset'.
      rewrite Hget_self' in Hget_self; inverts Hget_self.
      rewrite Hget_co' in Hget_co; inverts Hget_co.
      forwards* Eq: load_same'; inverts Eq.
      destruct (AST.ident_eq x' x).
      + subst x'.
        rewrite Hoffset' in Hoffset; inverts Hoffset.
        apply find_update_field in Hfind'; subst v'.
        specializes Hnodupmems Hin Hin'; subst t'. 
        split*.
        rewrite Hloadres; apply* Memory.Mem.load_store_same.
      + apply gso_field in Hfind'; auto.
        edestruct Hmenv as (Hload); eauto.
        split*.
        rewrite <-Hload; apply* Memory.Mem.load_store_other.

    - unfold compat_vars; intros.
      edestruct Hvars as (loc'); eauto.
      exists loc'; split*.
      apply* Memory.Mem.store_valid_access_1.

    - unfold compat_self; intro.
      exists co loc_self loc_struct ofs.
      destruct* Hself as (? & ? & ? & ? & Hget_self' & Hload_self' & Hget_co' & Hmem & ?).
      rewrite Hget_co' in Hget_co; inverts Hget_co.
      rewrite Hget_self' in Hget_self; inverts Hget_self.
      rewrite Hload_self' in Hload_self; inverts Hload_self.  
      splits*.
      + destruct (Values.eq_block loc_self loc_struct).
        * edestruct Hself_sep; eauto.
        * rewrite <-Hload_self'.
          apply* Memory.Mem.load_store_other.
      + introv Hin'.
        specializes Hmem Hin'; destruct Hmem as (delta').
        exists delta'; splits*.
        apply* Memory.Mem.store_valid_access_1.    
        
    - unfold mem_sep; introv ? ? Hget_self' ?.
      rewrite Hget_self' in Hget_self; inverts Hget_self.
      forwards* Eq: load_same'; inverts Eq.
      apply* Hsep.

    - unfold self_sep; introv Hget_self' ?.
      rewrite Hget_self' in Hget_self; inverts Hget_self.
      forwards* Eq: load_same'; inverts Eq.
      apply* Hself_sep.
  Qed.
  
  Remark alloc_exists:
    forall vars e m,
      exists e' m',
        Clight.alloc_variables tge e m vars e' m'.
  Proof.
    induction vars as [|(x, ty)].
    - do 3 econstructor.
    - intros.
      destruct (Memory.Mem.alloc m 0 (Ctypes.sizeof (Clight.genv_cenv tge) ty)) eqn: Eq.
      specialize (IHvars (Maps.PTree.set x (b, ty) e) m0).
      destruct* IHvars as (? & ? & ?).
      do 3 econstructor; eauto.
  Qed.

  Remark assign_loc_exists:
    forall v ty m loc,
      Ctypes.access_mode ty = Ctypes.By_value (chunk_of_typ ty) ->
      Memory.Mem.valid_access m (chunk_of_typ ty) loc 0 Memtype.Writable ->
      exists m',
        Clight.assign_loc tge.(Clight.genv_cenv) ty m loc Int.zero v m'.
  Proof.
    introv ? Hvalid.
    forwards (? & ?): Memory.Mem.valid_access_store Hvalid.
    do 2 econstructor; eauto.
  Qed.
  
  Remark bind_parameters_exists:
    forall xs vs e m,
      length xs = length vs ->
      Forall (fun x => exists loc,
                  Maps.PTree.get (fst x) e = Some (loc, snd x)
                  /\ Memory.Mem.valid_access m (chunk_of_typ (snd x)) loc 0 Memtype.Writable
                  /\ Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_typ (snd x))) xs ->
      exists m',
        Clight.bind_parameters tge e m xs vs m'.
  Proof.
    induction xs as [|(x, ty)]; destruct vs; introv Hlengths Hparams; try discriminate.
    - do 2 econstructor.
    - inverts Hparams as (? & ? & Hvalid & Haccess) Hparams.  
      forwards (m' & Hassign): (assign_loc_exists v) Haccess Hvalid.
      edestruct IHxs with (m:=m') (e:=e); eauto.
      + inversion_clear Hassign as [|? ? ? ? Haccess'].
        *{ clear IHxs Hlengths. induction xs.
           - constructor.
           - inverts Hparams as (loc & ?).
             constructor.
             + exists loc; splits*.
               apply* Memory.Mem.store_valid_access_1.
             + apply* IHxs.
         }
        * rewrite Haccess' in Haccess; discriminate.
      + do 2 econstructor; eauto. 
  Qed.

  Remark alloc_variables_implies:
    forall vars e m e' m', 
      Clight.alloc_variables tge e m vars e' m' ->
      Forall (fun x => Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_typ (snd x))) vars ->
      Forall (fun x => exists loc,
                  Maps.PTree.get (fst x) e' = Some (loc, snd x)
                  /\ Memory.Mem.valid_access m' (chunk_of_typ (snd x)) loc 0 Memtype.Writable
                  /\ Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_typ (snd x))) vars.
  Proof.
    induction vars.
    - constructor.
    - introv Halloc Hforall.
      inverts Halloc.
      constructor.
      + exists b1; splits*.
        * admit.
        *{ assert (Memory.Mem.valid_access m1 (chunk_of_typ (snd (id, ty))) b1 0 Memtype.Writable).
           - eapply Memory.Mem.valid_access_freeable_any.
             apply* Memory.Mem.valid_access_alloc_same.
             + omega.
             + simpl. admit.
             + eapply BinInt.Z.divide_0_r.
           - admit.
         }
        * inverts* Hforall.
      + apply* IHvars.
        inverts* Hforall.
  Qed.

  Remark forall_app:
    forall A (P: A -> Prop) l1 l2,
      Forall P (l1 ++ l2) -> Forall P l1 /\ Forall P l2.
  Proof.
    introv HForall; split; rewrite Forall_forall in *; introv Hin;
    apply HForall; apply in_or_app; [left | right]; auto.
  Qed.

  Lemma compat_funcall_pres:
    forall m f vargs,
      Datatypes.length (Clight.fn_params f) = Datatypes.length vargs ->
      Forall (fun x => Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_typ (snd x))) (f.(Clight.fn_params) ++ f.(Clight.fn_vars)) ->
      exists m1 e_fun m2,
        Clight.alloc_variables tge Clight.empty_env m (f.(Clight.fn_params) ++ f.(Clight.fn_vars)) e_fun m1 
        /\ Clight.bind_parameters tge e_fun m1 f.(Clight.fn_params) vargs m2.
  Proof.
    introv Hlengths Haccesses.
    forwards (e_fun & m1 & Halloc):
      (alloc_exists (f.(Clight.fn_params) ++ f.(Clight.fn_vars)) Clight.empty_env m).
    exists m1 e_fun.
    forwards* Hforall': alloc_variables_implies Halloc Haccesses.
    forwards (Hforall & H'): forall_app Hforall'; clear Hforall' H'.
    forwards* (m2 & ?): bind_parameters_exists Hlengths Hforall.
  Qed.
  
  Remark type_pres':
    forall c' c es,
      Nelist.Forall2 (fun e x => typeof e = snd x) es c'.(c_input) ->
      map Clight.typeof (nelist2list (Nelist.map (translate_exp c.(c_name)) es)) =
      map snd (nelist2list c'.(c_input)).
  Proof.
    intros c'.
    induction (c_input c'); introv Heq;
    inversion_clear Heq as [? ? Hty|? ? ? ? Hty Hforall2]; simpl.
    - rewrite type_pres, Hty; auto.
    - f_equal.
      + rewrite type_pres, Hty; auto.
      + specializes IHn Hforall2; eauto.
  Qed.
  
  (* Remark ifte_translate: *)
  (*   forall c temp (b: bool) s1 s2, *)
  (*     translate_stmt temp c.(c_name) (if b then s1 else s2) = *)
  (*     if b then (translate_stmt temp c.(c_name) s1) else (translate_stmt temp c.(c_name) s2). *)
  (* Proof. *)
  (*   now destruct b. *)
  (* Qed.   *)

  Hint Constructors Clight.eval_lvalue Clight.eval_expr well_formed_stmt.
  Hint Resolve expr_eval_simu Clight.assign_loc_value sem_cast_same.
  Hint Constructors well_formed_stmt.


  (* Definition empty_temp_env: Clight.temp_env := Maps.PTree.empty val. *)
      
  (* Inductive unique_temp: Clight.temp_env -> option (ident * typ) -> Prop := *)
  (* | unique_empty: *)
  (*     unique_temp empty_temp_env None *)
  (* | unique_singleton: forall le x v ty, *)
  (*     Maps.PTree.elements le = [(x, v)] ->  *)
  (*     unique_temp le (Some (x, ty)). *)

  Remark ne_Forall2_lengths:
    forall A B (P: A -> B -> Prop) l1 l2,
      Nelist.Forall2 P l1 l2 -> Nelist.length l1 = Nelist.length l2.
  Proof.
    induction l1, l2; introv HForall2; inverts* HForall2.
    simpl; f_equal; apply* IHl1.
  Qed.

  Axiom match_step: ident -> Clight.function -> Prop.
  Axiom match_params: nelist val -> list val -> Prop.

  Theorem simu_bigbig:
    (forall p S1 s S2,
        stmt_eval p S1 s S2 ->
        p = prog ->
        forall c,
          In c prog ->
          forall (WF: well_formed_stmt c S1 s)
            e1 le1 m1 
            (MS: match_states_bigbig c S1 (e1, le1, m1))
            temp,
          exists le2 m2 t,
            ClightBigstep.exec_stmt tge e1 le1 m1
                                    (snd (translate_stmt temp c.(c_name) s))
                                    t le2 m2 ClightBigstep.Out_normal
            /\ match_states_bigbig c S2 (e1, le2, m2))
    /\ (forall p me clsid vs me' rv,
          stmt_step_eval p me clsid vs me' rv ->
          p = prog ->
          forall c c' prog' m f vargs ve e le,
            In c prog ->
            find_class clsid prog = Some (c', prog') ->
            match_step clsid f ->
            match_params vs vargs ->
            match_states_bigbig c' (me, ve) (e, le, m) ->
            exists m' t,
              ClightBigstep.eval_funcall tge m (Clight.Internal f) vargs t m' rv
              /\ match_states_bigbig c (me', ve) (e, le, m')
        ).
  Proof.
    clear TRANSL.
    apply stmt_eval_step_ind; intros; 
      try inversion_clear WF as [|? ? ? Hin| | |? ? ? ? ? ? ? ? ? ? ? ? ? Hin Hfind Hwfs Hevs Hvalids Htypes|];
      try inverts MS as Hvenv Hmenv Hvars Hself; substs; intros.    

    (* clear TRANSL; introv IN EV WF; remember prog; *)
    (* induction EV as [| | | |? ? ? ? ? ? ? ? ? ? ? ? ? Step_eval|];  *)
    (* introv (* UNI *) MS; *)
    (* inversion_clear WF as [|? ? ? Hin| | |? ? ? ? ? ? ? ? ? ? Hin Hfind Hwfs Hevs Hvalids Htypes|]; *)
    (* inverts MS as Hvenv Hmenv Hvars Hself; substs.   *)

    (* Assign x e : "x = e" *)
    - app_exp_eval_det.
      edestruct Hvars; eauto.
      edestruct compat_assign_pres; iauto.  
      do 3 econstructor; split*.
      apply* ClightBigstep.exec_Sassign. 
      rewrite* type_pres. 
       
    (* AssignSt x e : "self->x = e"*)
    - app_exp_eval_det.
      pose proof Hself as Hself'.
      destruct* Hself' as (? & ? & ? & ? & ? & ? & ? & Hmem & ?).
      specializes Hmem Hin; destruct_conjs.    
      edestruct compat_stassign_pres; iauto.      
      do 3 econstructor; split*.
      apply* ClightBigstep.exec_Sassign.
      + apply* evall_self_field. 
      + rewrite* type_pres.
        
    (* Ifte e s1 s2 : "if e then s1 else s2" *)
    - destruct b.
      + edestruct H3 with (le1:=le1) (temp:=temp) as (? & ? & ? & Step & ?); eauto. 
        do 3 econstructor; split*.
        simpl; destruct (translate_stmt temp (c_name c) s1);
        destruct (translate_stmt o (c_name c) s2).
        apply* ClightBigstep.exec_Sifthenelse. 
        * erewrite type_pres, bool_val_ptr; eauto.
        * eauto.
      + simpl; destruct (translate_stmt temp (c_name c) s1) as [temp1].
        edestruct H3 with (le1:=le1) (temp:=temp1) as (? & ? & ? & Step & ?); eauto. 
        do 3 econstructor; split*.
        destruct (translate_stmt temp1 (c_name c) s2).
        apply* ClightBigstep.exec_Sifthenelse.
        * erewrite type_pres, bool_val_ptr; eauto.
        * eauto.
          
    (* Comp s1 s2 : "s1; s2" *)
    - app_stmt_eval_det.
      edestruct H0 with (le1:=le1) (temp:=temp) ; destruct_conjs; eauto.
      simpl. destruct (translate_stmt temp (c_name c) s1) as [temp1].
      destruct (translate_stmt temp1 (c_name c) s2) eqn: E2.
      edestruct H2 with (temp:=temp1) as (? & ? & ? & Step & ?); destruct_conjs; eauto.
      do 3 econstructor; split*.
      apply* ClightBigstep.exec_Sseq_1.
      rewrite* E2 in Step.

    (* Step_ap y ty clsid o [e1; ... ;en] : "y = step_clsid (&o, e1, ... , en)" *)
    - app_exps_eval_det.
      app_find_inst_det.
      app_stmt_step_eval_det.
      
      (* get the Clight corresponding function *)
      forwards* Hin': find_class_In Hfind.
      specialize (STEPS _ e1 Hin').
      destruct STEPS as (loc_f & f & ? & ? & ? & Htype_fun & ? & Htr & Hlengths & Haccesses); clear STEPS.
      forwards Eq: find_class_name Hfind.
      rewrite Eq in *; clear Eq.
      rewrite <-type_pres' with (c:=c) (es:=es) in Htype_fun; auto.

      (* get the Clight corresponding field *)
      pose proof Hself as Hself'.
      destruct Hself' as (? & ? & loc_struct & ofs & ? & ? & ? & Hmem & Hobj);
        auto; clear Hmem.
      specializes Hobj Hin; destruct Hobj as (delta).

      (* recursive funcall evaluation *)
      edestruct H2 with (c:=c) (f:=f) (le:=le1)
                               (vargs:=Values.Vptr loc_struct (Int.add ofs (Int.repr delta)) :: nelist2list vs);
        destruct_conjs; eauto.
      admit.
      admit.
      skip.

      (* memory state after assignment *)
      edestruct Hvars; eauto.
      edestruct compat_assign_pres with (c:=c); destruct_conjs; iauto.
           
      do 3 econstructor; split.
      + eapply ClightBigstep.exec_Sseq_1.

        (* funcall: "$t = clsid_step(&(self->o), v1, ..., vn)" *)
        *{ eapply ClightBigstep.exec_Scall; eauto.
           - simpl; eauto.
           - eapply Clight.eval_Elvalue.
             + apply* Clight.eval_Evar_global.
             + apply* Clight.deref_loc_reference.
           - econstructor.
             + eapply Clight.eval_Eaddrof.
               apply* evall_self_field.
             + eapply sem_cast_same.
               unfold valid_val; splits~.
               * discriminate.
               * simpl; trivial.
             + apply* exprs_eval_simu.
           - eauto.
         }

        (* assignment: "y = $t" *)
        * eapply ClightBigstep.exec_Sassign; iauto. 
          eapply Clight.eval_Etempvar; eauto.
          destruct temp; try destruct p; eapply Maps.PTree.gss. 

      + inverts H27. constructor*.
        skip. skip.

    (* Skip : "skip" *)
    - do 3 econstructor; split*.
      eapply ClightBigstep.exec_Sskip.

    (* funcall *)
    - (* get the Clight function entry state *)
      (* forwards Eq1: ne_Forall2_lengths Htypes. *)
      (* forwards Eq2: ne_Forall2_lengths Hvalids. *)
      (* rewrite Eq2 in Eq1; clear Eq2. *)
      (* rewrite <-Eq1 in Hlengths; clear Eq1. *)
      (* assert (length f.(Clight.fn_params) = *)
      (*         length (Values.Vptr loc_struct (Int.add ofs (Int.repr delta)) :: nelist2list vs)) *)
      (*   by (rewrite Hlengths; simpl; f_equal; rewrite Nelist.nelist2list_length; auto). *)
      forwards* (m' & e' & m'' & ? & ?): (compat_funcall_pres m f vargs).
      admit.
      admit.
      inverts H1.
  Qed.