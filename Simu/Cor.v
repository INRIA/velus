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
  
  Hypothesis TRANSL: translate prog main_node = Errors.OK tprog.    
  (* Hypothesis WF: well_formed prog. *)
  (* Hypothesis MAINNODE: find_class main_node prog = Some (c_main, cls_main). *)

  (* Lemma build_co_ok: *)
  (*   Ctypes.build_composite_env (map translate_class prog) = Errors.OK (Clight.genv_cenv tge). *)
  (* Proof. *)
  (*   admit. *)
  (* Qed. *)
  
  Definition chunk_of_typ ty := AST.chunk_of_type (Ctypes.typ_of_type ty).
  Definition pointer_of_node node := pointer_of (type_of_inst node).
  
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
  | wf_step: forall y ty clsid o es vs,
      Nelist.Forall (well_formed_exp c) es ->
      Nelist.Forall2 (exp_eval S) es vs ->
      Nelist.Forall2 (fun (e : exp) (v : val) => valid_val v (typeof e)) es vs ->
      well_formed_stmt c S (Step_ap y ty clsid o es)
  | wf_skip: 
      well_formed_stmt c S Skip.

  Definition compat_venv (c: class) (S: state) (env: Clight.env) (m: Memory.Mem.mem):  Prop :=
    forall x v t,
      find_var x S v ->
      In (x, t) c.(c_vars) ->
      exists loc,
        Maps.PTree.get x env = Some (loc, t)
        /\ Memory.Mem.load (chunk_of_typ t) m loc 0 = Some v
        /\ valid_val v t.

  Definition compat_menv (c: class) (S: state) (env: Clight.env) (m: Memory.Mem.mem):  Prop :=
    forall x v t,
      find_field x S v ->
      In (x, t) c.(c_mems) ->
      exists co loc' loc ofs delta,
        Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta
        /\ Memory.Mem.load (chunk_of_typ t) m loc (Int.unsigned (Int.add ofs (Int.repr delta))) = Some v
        /\ valid_val v t
        /\ Maps.PTree.get c.(c_name) (Clight.genv_cenv tge) = Some co 
        /\ Maps.PTree.get self_id env = Some (loc', pointer_of_node c.(c_name))
        /\ Memory.Mem.load (chunk_of_typ (pointer_of_node c.(c_name))) m loc' 0 = Some (Values.Vptr loc ofs)
        /\ Ctypes.access_mode (pointer_of_node c.(c_name)) = Ctypes.By_value (chunk_of_typ (pointer_of_node c.(c_name))).

  Remark valid_val_implies_access:
    forall v t, valid_val v t -> Ctypes.access_mode t = Ctypes.By_value (chunk_of_typ t).
  Proof. introv H; apply H. Qed.
    
  Hint Constructors Clight.eval_lvalue Clight.eval_expr well_formed_stmt.
  Hint Resolve valid_val_implies_access.
  
  Lemma expr_eval_simu:
    forall c S exp v e le m,
      compat_venv c S e m ->
      compat_menv c S e m ->
      well_formed_exp c exp ->
      exp_eval S exp v ->
      Clight.eval_expr tge e le m (translate_exp c.(c_name) exp) v.
  Proof.
    intros c S exp;
    induction exp as [| |cst];
    introv Hvenv Hmenv Hwf Heval;
    inverts Heval; inverts Hwf; simpl.

    (* Var x ty : "x" *)
    - edestruct Hvenv; eauto.
      eapply Clight.eval_Elvalue, Clight.deref_loc_value; iauto.

    (* State x ty : "self->x" *)
    - edestruct Hmenv; destruct_conjs; eauto.
      eapply Clight.eval_Elvalue.
      + eapply Clight.eval_Efield_struct
        with (id:=c.(c_name)) (att:=Ctypes.noattr); eauto.
        eapply Clight.eval_Elvalue. 
        * apply Clight.eval_Ederef. 
          eapply Clight.eval_Elvalue, Clight.deref_loc_value; eauto.
        * apply* Clight.deref_loc_copy.
      + apply* Clight.deref_loc_value.

    (* Const c ty : "c" *)
    - destruct cst; constructor.
  Qed.

  Lemma exprs_eval_simu:
    forall c S es es' vs e le m,
      compat_venv c S e m ->
      compat_menv c S e m ->
      Nelist.Forall (well_formed_exp c) es ->
      Nelist.Forall2 (fun e v => valid_val v (typeof e)) es vs ->
      Nelist.Forall2 (exp_eval S) es vs ->
      es' = nelist2list (Nelist.map (translate_exp c.(c_name)) es) ->
      Clight.eval_exprlist tge e le m es' (list_type_to_typelist (map Clight.typeof es')) (nelist2list vs).
  Proof.
    Hint Constructors Clight.eval_exprlist.
    introv Hvenv Hmenv Hwf Hvalid Hev Heq; subst es';
    induction Hev; inverts Hwf; inverts Hvalid; econstructor;
    (apply* expr_eval_simu || (rewrite type_pres; apply* sem_cast_same) || eauto).
  Qed.
  
  Definition compat_vars (c: class) (e: Clight.env) (m: Memory.Mem.mem): Prop :=
    forall x t,
      In (x, t) c.(c_vars) ->
      exists loc,
        Maps.PTree.get x e = Some (loc, t)
        /\ Memory.Mem.valid_access m (chunk_of_typ t) loc 0 Memtype.Writable.

  Definition compat_fields (c: class) (env: Clight.env) (m: Memory.Mem.mem): Prop :=
    forall x t,
      In (x, t) c.(c_mems) ->
      exists co loc' loc ofs delta,
        Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta
        /\ In (x, t) (Ctypes.co_members co)
        /\ Maps.PTree.get c.(c_name) (Clight.genv_cenv tge) = Some co
        /\ Maps.PTree.get self_id env = Some (loc', pointer_of_node c.(c_name))
        /\ Memory.Mem.load (chunk_of_typ (pointer_of_node c.(c_name))) m loc' 0 = Some (Values.Vptr loc ofs)
        /\ Memory.Mem.valid_access m (chunk_of_typ t) loc (Int.unsigned (Int.add ofs (Int.repr delta))) Memtype.Writable.

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
    forall x loc t (* co x' *) ofs (* delta t' *) loc' (* v *) loc'',
      In (x, t) c.(c_vars) -> 
      Maps.PTree.get x e = Some (loc, t) ->
      Maps.PTree.get self_id e = Some (loc'', pointer_of_node c.(c_name)) ->
      (* Maps.PTree.get c.(c_name) (Clight.genv_cenv tge) = Some co -> *)
      (* Ctypes.field_offset (Clight.genv_cenv tge) x' (Ctypes.co_members co) = Errors.OK delta -> *)
      (* Memory.Mem.load (chunk_of_typ t') m loc' (Int.unsigned (Int.add ofs (Int.repr delta))) = Some v -> *)
      Memory.Mem.load (chunk_of_typ (pointer_of_node c.(c_name))) m loc'' 0 = Some (Values.Vptr loc' ofs) ->
      loc <> loc'.

  Definition self_sep (c: class) (e: Clight.env) (m: Memory.Mem.mem) :=
    forall loc ofs loc',
      Maps.PTree.get self_id e = Some (loc', pointer_of_node c.(c_name)) ->
      Memory.Mem.load (chunk_of_typ (pointer_of_node c.(c_name))) m loc' 0 = Some (Values.Vptr loc ofs) ->
      loc <> loc'.

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
        
  Lemma compat_assign_pres:
    forall c S env m loc x e v,
      compat_venv c S env m ->
      compat_menv c S env m ->
      compat_vars c env m ->
      compat_fields c env m ->
      mem_sep c env m ->
      self_sep c env m ->
      nodup_env env ->
      nodup_vars c ->
      Maps.PTree.get x env = Some (loc, typeof e) ->
      In (x, typeof e) c.(c_vars) ->
      v = Values.Val.load_result (chunk_of_typ (typeof e)) v ->
      valid_val v (typeof e) ->
      x <> self_id ->
      Memory.Mem.valid_access m (chunk_of_typ (typeof e)) loc 0 Memtype.Writable ->
      exp_eval S e v ->
      exists m', Memory.Mem.store (chunk_of_typ (typeof e)) m loc 0 v = Some m' 
            /\ compat_venv c (update_var x S v) env m'
            /\ compat_menv c S env m'
            /\ compat_vars c env m' 
            /\ compat_fields c env m' 
            /\ mem_sep c env m'
            /\ self_sep c env m'.
  Proof.
    intros ** Hvenv Hmenv Hvars Hfields Hsep Hself_sep Hnodupenv Hnodupvars Hget Hin Hloadres ? ? ? ?.
    edestruct Memory.Mem.valid_access_store with (v:=v) as [m']; eauto. 
    exists m'; splits*. 
    - unfold compat_venv; intros x' v' t' Hfind Hin'.
      destruct (AST.ident_eq x' x).
      + subst x'.
        apply find_update_var in Hfind; subst v'.
        specializes Hnodupvars Hin Hin'; subst t'. 
        exists loc; splits*.
        rewrite Hloadres; apply* Memory.Mem.load_store_same.
      + apply gso_var in Hfind; auto.
        edestruct Hvenv as [loc' [? [Hload]]]; eauto.
        exists loc'; splits*.
        destruct (Values.eq_block loc' loc).
        * subst loc'.
          edestruct Hnodupenv; eauto. 
        * rewrite <-Hload. 
          apply* Memory.Mem.load_store_other.
    - unfold compat_menv; intros x' v' t' Hmem Hin'.
      edestruct Hmenv
        as (co & loc'' & loc' & ofs & delta & ? & Hload & ? & ? & Hself' & Hloadptr & ?); eauto.
      exists co loc'' loc' ofs delta; splits*. 
      + destruct (Values.eq_block loc loc').
        * edestruct Hsep with (2:=Hget); eauto; contradiction.
        * rewrite <-Hload.
          apply* Memory.Mem.load_store_other.
      + destruct (Values.eq_block loc'' loc).
        * subst loc''.
          edestruct Hnodupenv with (2:=Hget); eauto.
        * rewrite <-Hloadptr.
          apply* Memory.Mem.load_store_other.
    - unfold compat_vars; intros x' t' Hin'.
      edestruct Hvars as (loc' & ? & ?); eauto.
      exists loc'; split*.
      apply* Memory.Mem.store_valid_access_1.
    - unfold compat_fields; intros x' t' Hin'.
      edestruct Hfields as (co & loc1' & loc1 & ofs & delta & ? & ? & ? & ? & Hload & ?); eauto. 
      exists co loc1' loc1 ofs delta; splits*.
      + destruct (Values.eq_block loc1' loc).
        * subst loc1'.
          edestruct Hnodupenv with (2:=Hget); eauto.
        * rewrite <-Hload; apply* Memory.Mem.load_store_other.
      + apply* Memory.Mem.store_valid_access_1.
    - unfold mem_sep; intros x' loc1 t' ofs loc1' loc1'' Hin1 Hget1 Hself Hload.
      apply* Hsep.
      instantiate (1:=ofs).
      destruct (Values.eq_block loc1'' loc).
      + subst loc1''.
        edestruct Hnodupenv with (2:=Hget); eauto.
      + rewrite <-Hload; symmetry; apply* Memory.Mem.load_store_other.
    - unfold self_sep; intros loc1 ofs loc1' Hself Hload.
      apply* Hself_sep.
      instantiate (1:=ofs).
      destruct (Values.eq_block loc1' loc).
      + subst loc1'.
        edestruct Hnodupenv with (2:=Hget); eauto.
      + rewrite <-Hload; symmetry; apply* Memory.Mem.load_store_other.
  Qed.

   Lemma compat_stassign_pres:
    forall c S env m x e v co loc loc' ofs delta,
      compat_venv c S env m ->
      compat_menv c S env m ->
      compat_vars c env m ->
      compat_fields c env m ->
      mem_sep c env m ->
      self_sep c env m ->
      fields_sep m ->
      nodup_mems c ->
      In (x, (typeof e)) (Ctypes.co_members co) ->
      Ctypes.field_offset tge.(Clight.genv_cenv) x (Ctypes.co_members co) = Errors.OK delta ->
      Maps.PTree.get c.(c_name) (Clight.genv_cenv tge) = Some co ->
      Maps.PTree.get self_id env = Some (loc', pointer_of_node c.(c_name)) ->
      Memory.Mem.load (chunk_of_typ (pointer_of_node c.(c_name))) m loc' 0 = Some (Values.Vptr loc ofs) ->
      In (x, typeof e) c.(c_mems) ->
      v = Values.Val.load_result (chunk_of_typ (typeof e)) v ->
      valid_val v (typeof e) ->
     Memory.Mem.valid_access m (chunk_of_typ (typeof e)) loc (Int.unsigned (Int.add ofs (Int.repr delta))) Memtype.Writable ->
      exp_eval S e v ->
      exists m',
        Memory.Mem.store (chunk_of_typ (typeof e)) m loc (Int.unsigned (Int.add ofs (Int.repr delta))) v = Some m'
        /\ compat_venv c S env m'
        /\ compat_menv c (update_field x S v) env m'
        /\ compat_vars c env m'
        /\ compat_fields c env m'
        /\ mem_sep c env m'
        /\ self_sep c env m'.
  Proof.
    intros ** Hvenv Hmenv Hvars Hfields Hsep Hself_sep Hfields_sep Hnodupmems Hmembers Hoffset Hmain Hself Hloadptr Hin Hloadres ? ? ?.
    edestruct Memory.Mem.valid_access_store with (v:=v) as [m']; eauto. 
    exists m'; splits*.
    - unfold compat_venv; intros x' v' t' Hmto Hin'.
      edestruct Hvenv as (loc'' & Hget & Hload' & ?); eauto.
      exists loc''; splits*.
      destruct (Values.eq_block loc'' loc).
      + edestruct Hsep with (1:=Hin'); eauto.
      + rewrite <-Hload'.
        apply* Memory.Mem.load_store_other.
    - unfold compat_menv; intros x' v' t' Hmem Hin'.
      destruct (AST.ident_eq x' x).
      + subst x'.
        apply find_update_field in Hmem; subst v'.
        specializes Hnodupmems Hin Hin'; subst t'. 
        exists co loc' loc ofs delta; splits*.
        * rewrite Hloadres; apply* Memory.Mem.load_store_same.
        *{ destruct (Values.eq_block loc' loc).
           - edestruct Hself_sep; eauto.  
           - rewrite <-Hloadptr.
             apply* Memory.Mem.load_store_other.
         }
      + apply gso_field in Hmem; auto.
        edestruct Hmenv
          as (co' & loc1' & loc1 & ofs' & delta' & ? & Hload' & ? & Hmain1 & Hself1 & Hloadptr1 & ?); eauto. 
        rewrite Hmain1 in Hmain; inverts Hmain. 
        rewrite Hself1 in Hself; inverts Hself. 
        rewrite Hloadptr1 in Hloadptr; inverts Hloadptr.
        exists co loc' loc ofs delta'; splits*.
        * rewrite <-Hload'. apply* Memory.Mem.load_store_other. 
        *{ destruct (Values.eq_block loc' loc).
           - edestruct Hself_sep; eauto. 
           - rewrite <-Hloadptr1.
             apply* Memory.Mem.load_store_other.
         }
    - unfold compat_vars; intros x' t' Hin'.
      edestruct Hvars as (loc1' & ? & ?); eauto.
      exists loc1'; split; auto.
      apply* Memory.Mem.store_valid_access_1.
    - unfold compat_fields; intros x' t' Hin'.
      edestruct Hfields as (co' & loc1' & loc1 & ofs' & delta' & ? & ? & ? & Hself' & Hload & ?); eauto. 
      exists co' loc1' loc1 ofs' delta'; splits*.
      + destruct (Values.eq_block loc1' loc).
        * subst loc1'.
          rewrite Hself in Hself'; inverts Hself'. 
          edestruct Hself_sep; eauto.
        * rewrite <-Hload; apply* Memory.Mem.load_store_other.
      + apply* Memory.Mem.store_valid_access_1.
    - unfold mem_sep; intros x' loc1 t' ofs' loc1' loc1'' Hin1 Hget1 Hself' Hload.
      apply* Hsep.
      instantiate (1:=ofs').
      destruct (Values.eq_block loc1'' loc).
      + subst loc1''.
        rewrite Hself in Hself'; inverts Hself'.
        edestruct Hself_sep; eauto.  
      + rewrite <-Hload; symmetry; apply* Memory.Mem.load_store_other.
    - unfold self_sep; intros loc1 ofs' loc1' Hself' Hload.
      apply* Hself_sep.
      instantiate (1:=ofs').
      destruct (Values.eq_block loc1' loc).
      + subst loc1'.
        rewrite Hself in Hself'; inverts Hself'. 
        edestruct Hself_sep; eauto.  
      + rewrite <-Hload; symmetry; apply* Memory.Mem.load_store_other.
  Qed.

Remark ifte_translate:
    forall c temp (b: bool) s1 s2,
      translate_stmt temp c.(c_name) (if b then s1 else s2) =
      if b then (translate_stmt temp c.(c_name) s1) else (translate_stmt temp c.(c_name) s2).
  Proof.
    now destruct b.
  Qed.  

  Hint Constructors Clight.eval_lvalue Clight.eval_expr well_formed_stmt.
  Hint Resolve expr_eval_simu Clight.assign_loc_value sem_cast_same.
  Hint Constructors well_formed_stmt.

  Definition c_state := (Clight.env * Clight.temp_env * Memory.Mem.mem)%type.
   
  Inductive match_states_bigbig (c: class) (S: state): c_state -> Prop :=
    intro_state_bigbig: forall e le m,
      (* state correspondance *)
      compat_venv c S e m ->     
      compat_menv c S e m ->
      
      (* Clight state well defined *)
      compat_vars c e m ->
      compat_fields c e m ->

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

  Definition empty_temp_env: Clight.temp_env := Maps.PTree.empty val.
      
  Inductive unique_temp: Clight.temp_env -> option (ident * typ) -> Prop :=
  | unique_empty:
      unique_temp empty_temp_env None
  | unique_singleton: forall le x v ty,
      Maps.PTree.elements le = [(x, v)] -> 
      unique_temp le (Some (x, ty)).
  
  Theorem simu_bigbig:
    forall c S1 s S2,
      well_formed_stmt c S1 s ->
      stmt_eval prog S1 s S2 ->
      forall e1 le1 m1 temp,
        (* unique_temp le1 temp -> *)
        match_states_bigbig c S1 (e1, le1, m1) ->
        exists le2 m2 t,
          ClightBigstep.exec_stmt tge e1 le1 m1
                                  (snd (translate_stmt temp c.(c_name) s))
                                  t le2 m2 ClightBigstep.Out_normal
          /\ match_states_bigbig c S2 (e1, le2, m2).
  Proof.
    Check stmt_eval_ind_2.
    clear TRANSL; introv WF EV; remember prog;
    induction EV (* using stmt_eval_ind_2 with *)
    (* (P := fun p St1 stmt St2 => *)
    (*         well_formed_stmt c St1 stmt -> *)
    (*         p = prog -> *)
    (*         forall e1 le1 m1, *)
    (*           match_states_bigbig c St1 (e1, le1, m1) -> *)
    (*           exists le2 m2 t, *)
    (*             ClightBigstep.exec_stmt tge e1 le1 m1 *)
    (*                                     (snd (translate_stmt None c.(c_name) stmt)) *)
    (*                                     t le2 m2 ClightBigstep.Out_normal *)
    (*             /\ match_states_bigbig c St2 (e1, le2, m2) *)
    (* ) *)
    (*   (P0 := fun p me clsid vs me' rv => *)
    (*            forall p' c S1 s S2, *)
    (*              well_formed_stmt c S1 s -> *)
    (*              stmt_eval p' S1 s S2 -> *)
    (*              forall e1 le1 m1, *)
    (*                match_states_bigbig c S1 (e1, le1, m1) -> *)
    (*                exists le2 m2 t, *)
    (*                  ClightBigstep.exec_stmt tge e1 le1 m1 *)
    (*                                          (snd (translate_stmt None c.(c_name) s)) *)
    (*                                          t le2 m2 ClightBigstep.Out_normal *)
    (*                  /\ match_states_bigbig c S2 (e1, le2, m2)) *)
    ; introv (* UNI *) MS;  try inverts WF;
    inverts MS as Hvenv Hmenv Hvars Hfields.

    (* Assign x e : "x = e" *)
    - app_exp_eval_det.
      edestruct Hvars; eauto.
      edestruct compat_assign_pres; iauto.  
      do 3 econstructor; split*.
      apply* ClightBigstep.exec_Sassign. 
      rewrite* type_pres. 
      
    (* AssignSt x e : "self->x = e"*)
    - app_exp_eval_det.
      edestruct Hfields; eauto; destruct_conjs.
      edestruct compat_stassign_pres; iauto.
      do 3 econstructor; split*.
      apply* ClightBigstep.exec_Sassign.
      + eapply Clight.eval_Efield_struct
        with (id:=c.(c_name)) (att:=Ctypes.noattr); eauto.
        apply* Clight.eval_Elvalue.  
        * apply Clight.eval_Ederef. 
          apply* Clight.eval_Elvalue.
          apply Clight.deref_loc_value with (chunk:=AST.Mint32); eauto.
        * apply* Clight.deref_loc_copy.
      + rewrite* type_pres.
        
    (* Ifte e s1 s2 : "if e then s1 else s2" *)
    - destruct b.
      + edestruct IHEV with (le1:=le1) (temp:=temp) as (? & ? & ? & Step & ?); eauto. 
        do 3 econstructor; split*.
        simpl; destruct (translate_stmt temp (c_name c) s1);
        destruct (translate_stmt o (c_name c) s2).
        apply* ClightBigstep.exec_Sifthenelse. 
        * erewrite type_pres, bool_val_ptr; eauto.
        * eauto.
      + simpl; destruct (translate_stmt temp (c_name c) s1) as [temp1].
        edestruct IHEV with (le1:=le1) (temp:=temp1) as (? & ? & ? & Step & ?); eauto. 
        do 3 econstructor; split*.
        destruct (translate_stmt temp1 (c_name c) s2).
        apply* ClightBigstep.exec_Sifthenelse.
        * erewrite type_pres, bool_val_ptr; eauto.
        * eauto.
          
    (* Comp s1 s2 : "s1; s2" *)
    - subst prog0.
      app_stmt_eval_det.
      edestruct IHEV1 with (le1:=le1) (temp:=temp) ; destruct_conjs; eauto.
      simpl. destruct (translate_stmt temp (c_name c) s1) as [temp1].
      destruct (translate_stmt temp1 (c_name c) s2) eqn: E2.
      edestruct IHEV2 with (temp:=temp1) as (? & ? & ? & Step & ?); destruct_conjs; eauto.
      do 3 econstructor; split*.
      apply* ClightBigstep.exec_Sseq_1.
      rewrite* E2 in Step.

    (* Step_ap y ty clsid o [e1; ... ;en] : "y = step_clsid (&o, e1, ... , en)" *)
    - assert (loc_f: Values.block). admit.
      assert (Globalenvs.Genv.find_symbol (Clight.genv_genv tge) (step_id clsid) = Some loc_f). admit.
      assert (Maps.PTree.get (step_id clsid) e1 = None). admit.

      assert (loc_self: Values.block). admit.
      assert (Maps.PTree.get self_id e1 = Some (loc_self, pointer_of_node (c_name c))). admit.
      assert (loc_struct: Values.block). admit.
      assert (ofs: Int.int). admit.
      assert (Memory.Mem.loadv AST.Mint32 m1 (Values.Vptr loc_self Int.zero) = Some (Values.Vptr loc_struct ofs)). admit.
      assert (co: Ctypes.composite). admit.
      assert (Maps.PTree.get (c_name c) (Clight.genv_cenv tge) = Some co). admit.
      assert (delta: Z). admit.
      assert (Ctypes.field_offset (Clight.genv_cenv tge) o (Ctypes.co_members co) = Errors.OK delta). admit.

      assert (f: Clight.function). admit.
      assert (Globalenvs.Genv.find_funct (Clight.genv_genv tge) (Values.Vptr loc_f Int.zero) = Some (Clight.Internal f)). admit.

      assert (e': Clight.env). admit.
      assert (m': Memory.Mem.mem). admit.
      assert (Clight.alloc_variables tge Clight.empty_env m1 (Clight.fn_params f ++ Clight.fn_vars f) e' m'). admit.
      assert (m'': Memory.Mem.mem). admit.
      assert (Clight.bind_parameters tge e' m' (Clight.fn_params f) (Values.Vptr loc_struct (Int.add ofs (Int.repr delta)) :: nelist2list vs0) m''). admit.

      inverts H1.
      assert (well_formed_stmt cls
                               (omenv, adds (nefst (c_input cls)) vs v_empty) 
                               (c_step cls)) as Hwf. admit.
      assert (match_states_bigbig cls
                                  (omenv, adds (nefst (c_input cls)) vs v_empty) 
                                  (e', Clight.create_undef_temps (Clight.fn_temps f), m'')) as Hms. admit.
      assert (Clight.fn_body f = snd (translate_stmt None (c_name cls) (c_step cls))) as Htr. admit.
      
        do 3 econstructor; split*.
      eapply ClightBigstep.exec_Sseq_1.
      + 
        
        eapply ClightBigstep.exec_Scall.
        * simpl; eauto.
        *{ eapply Clight.eval_Elvalue; simpl.
           - apply* Clight.eval_Evar_global.
           - apply* Clight.deref_loc_reference.
         }
        *{ econstructor.
           - eapply Clight.eval_Eaddrof.
             eapply Clight.eval_Efield_struct
             with (id:=c.(c_name)) (att:=Ctypes.noattr); eauto.
             apply* Clight.eval_Elvalue.  
             + apply Clight.eval_Ederef.
               apply* Clight.eval_Elvalue.
               apply Clight.deref_loc_value with (chunk:=AST.Mint32); eauto.
             + apply* Clight.deref_loc_copy.                
           - eapply sem_cast_same.
             unfold valid_val. splits.
             + reflexivity.
             + discriminate.
             + now simpl.
           - apply* exprs_eval_simu.
         }
        * eauto.
        * admit.
        *{ apply* ClightBigstep.eval_funcall_internal.
           - admit.
           - rewrite Htr.
             (* specializes IHEV Hwf H22 Hms. *)
             (* edestruct IHEV as (le2 & m2 & t & Hexec & Hms'); eauto. *)
             skip.
           - skip.
           - skip.
         }
      + skip.
      + skip.

    (* Skip : "skip" *)
    - do 3 econstructor; split*.
      eapply ClightBigstep.exec_Sskip.
  Qed.