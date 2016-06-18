Require cfrontend.ClightBigstep.
Require cfrontend.Clight.
Require Export lib.Integers.

Require Export Rustre.Common.
Require Export Rustre.RMemory.

Require Export Syn CommonSem Tra.
Require Import Sem2.

Require Export Program.Tactics.
Require Export List.
Export List.ListNotations.
Open Scope list_scope.

(* SIMULATION *)

Section PRESERVATION.

  Variable main_node : ident.
  Variable prog: program.
  Variable tprog: Clight.program.
  Variable c_main: class.
  Variable cls_main: list class.
  
  (* Let ge := globalenv prog. *)
  Let tge := Clight.globalenv tprog.
  
  Hypothesis TRANSL: translate prog main_node = Errors.OK tprog.    
  (* Hypothesis WF: well_formed prog. *)
  Hypothesis MAINNODE: find_class main_node prog = Some (c_main, cls_main).

  Lemma build_co_ok:
    Ctypes.build_composite_env (map translate_class prog) = Errors.OK (Clight.genv_cenv tge).
  Proof.
    unfold translate in TRANSL.
    rewrite MAINNODE in TRANSL.
    unfold Clight.make_program in TRANSL.
    revert TRANSL.
    generalize (Clight.make_program_obligation_1
                  (map translate_class prog)
                  [(main_id,
                    make_main
                      (translate_stmt main_node
                                      (c_step c_main))
                      (c_vars c_main))] 
                  [] main_id).
    generalize (eq_refl (Ctypes.build_composite_env (map translate_class prog))).
    intros H1 H2.
    simpl in H2.
    admit.
  Qed.
  
  Definition chunk_of_typ ty := AST.chunk_of_type (Ctypes.typ_of_type ty).
  Definition pointer_of_node node := pointer_of (type_of_inst node).
  
  Definition main_fun :=
    Clight.mkfunction Ctypes.type_int32s AST.cc_default []
                      c_main.(c_vars)
                          []
                          (translate_stmt main_node c_main.(c_step)).
  
  Lemma type_pres:
    forall e, Clight.typeof (translate_exp main_node e) = typeof e.
  Proof.
    induction e; simpl; try reflexivity.
    destruct c; simpl; reflexivity.
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

  Inductive well_formed_exp: exp -> Prop :=
  | wf_var: forall x ty,
      In (x, ty) c_main.(c_vars) ->
      x <> self_id ->
      well_formed_exp (Var x ty)
  | wf_state: forall x ty,
      In (x, ty) c_main.(c_mems) ->
      well_formed_exp (State x ty)
  | wf_const: forall c ty,
      well_formed_exp (Const c ty).

  Inductive well_formed_stmt: menv -> venv -> stmt -> Prop :=
  | wf_assign: forall me ve x e v,
      In (x, typeof e) c_main.(c_vars) ->
      x <> self_id ->
      well_formed_exp e ->
      exp_eval me ve e v ->
      valid_val v (typeof e) ->
      v = Values.Val.load_result (chunk_of_typ (typeof e)) v ->
      well_formed_stmt me ve (Assign x e)
  | wf_assignst: forall me ve x e v,
      In (x, typeof e) c_main.(c_mems) ->
      x <> self_id ->
      well_formed_exp e ->
      exp_eval me ve e v ->
      valid_val v (typeof e) ->
      v = Values.Val.load_result (chunk_of_typ (typeof e)) v ->
      well_formed_stmt me ve (AssignSt x e)
  | wf_ite: forall me ve e s1 s2,
      well_formed_exp e ->
      well_formed_stmt me ve s1 ->
      well_formed_stmt me ve s2 ->
      well_formed_stmt me ve (Ifte e s1 s2)
  | wf_comp: forall me ve me' ve' s1 s2,
      well_formed_stmt me ve s1 ->
      stmt_eval (me, ve) s1 (me', ve') ->
      well_formed_stmt me' ve' s2 ->
      well_formed_stmt me ve (Comp s1 s2)
  | wf_skip: forall me ve,
      well_formed_stmt me ve Skip.

  Definition compat_venv (ve: venv) (env: Clight.env) (m: Memory.Mem.mem):  Prop :=
    forall x v t,
      PM.MapsTo x v ve ->
      In (x, t) c_main.(c_vars) ->
      exists loc,
        Maps.PTree.get x env = Some (loc, t)
        /\ Memory.Mem.load (chunk_of_typ t) m loc 0 = Some v
        /\ valid_val v t.

  Definition compat_menv (me: menv) (env: Clight.env) (m: Memory.Mem.mem):  Prop :=
    forall x v t,
      mfind_mem x me = Some v ->
      In (x, t) c_main.(c_mems) ->
      exists co loc' loc ofs delta,
        Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta
        /\ Memory.Mem.load (chunk_of_typ t) m loc (Int.unsigned (Int.add ofs (Int.repr delta))) = Some v
        /\ valid_val v t
        /\ Maps.PTree.get main_node (Clight.genv_cenv tge) = Some co 
        /\ Maps.PTree.get self_id env = Some (loc', pointer_of_node main_node)
        /\ Memory.Mem.load (chunk_of_typ (pointer_of_node main_node)) m loc' 0 = Some (Values.Vptr loc ofs)
        /\ Ctypes.access_mode (pointer_of_node main_node) = Ctypes.By_value (chunk_of_typ (pointer_of_node main_node)).

  Remark valid_val_implies_access:
    forall v t, valid_val v t -> Ctypes.access_mode t = Ctypes.By_value (chunk_of_typ t).
  Proof. intros ** H; apply H. Qed.
    
  Hint Constructors Clight.eval_lvalue Clight.eval_expr well_formed_stmt(* well_typed *).
  Hint Resolve valid_val_implies_access.
  
  Lemma expr_eval_simu:
    forall me ve exp v e le m,
      compat_venv ve e m ->
      compat_menv me e m ->
      well_formed_exp exp ->
      exp_eval me ve exp v ->
      Clight.eval_expr tge e le m (translate_exp main_node exp) v.
  Proof.
    intros me ve exp;
    induction exp as [x ty|x ty|c ty];
    intros ** Hvenv Hmenv Hwf Heval;
    inv Heval; inv Hwf; simpl.

    (* Var x ty : "x" *)
    - edestruct Hvenv; destruct_conjs; eauto.
      eapply Clight.eval_Elvalue, Clight.deref_loc_value; eauto.

    (* State x ty : "self->x" *)
    - edestruct Hmenv; destruct_conjs; eauto.
      eapply Clight.eval_Elvalue.
      + eapply Clight.eval_Efield_struct
        with (id:=main_node) (att:=Ctypes.noattr); eauto.
        eapply Clight.eval_Elvalue. 
        * apply Clight.eval_Ederef. 
          eapply Clight.eval_Elvalue, Clight.deref_loc_value; eauto.
        * apply Clight.deref_loc_copy; auto.
      + eapply Clight.deref_loc_value; eauto.

    (* Const c ty : "c" *)
    - destruct c; constructor.
  Qed.
  
  Definition compat_vars (e: Clight.env) (m: Memory.Mem.mem): Prop :=
    forall x t,
      In (x, t) c_main.(c_vars) ->
      exists loc,
        Maps.PTree.get x e = Some (loc, t)
        /\ Memory.Mem.valid_access m (chunk_of_typ t) loc 0 Memtype.Writable.

  Definition compat_fields (env: Clight.env) (m: Memory.Mem.mem): Prop :=
    forall x t,
      In (x, t) c_main.(c_mems) ->
      exists co loc' loc ofs delta,
        Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta
        /\ In (x, t) (Ctypes.co_members co)
        /\ Maps.PTree.get main_node (Clight.genv_cenv tge) = Some co
        /\ Maps.PTree.get self_id env = Some (loc', pointer_of_node main_node)
        /\ Memory.Mem.load (chunk_of_typ (pointer_of_node main_node)) m loc' 0 = Some (Values.Vptr loc ofs)
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

  Definition nodup_vars :=
    forall x t t',
      In (x, t) c_main.(c_vars) ->
      In (x, t') c_main.(c_vars) ->
      t' = t.

   Definition nodup_mems :=
    forall x t t',
      In (x, t) c_main.(c_mems) ->
      In (x, t') c_main.(c_mems) ->
      t' = t.

  (* Inductive compat_stmt: menv -> venv -> Clight.env -> Memory.Mem.mem -> stmt -> Prop := *)
  (* | compat_assign: forall me ve m (env: Clight.env) e v x loc, *)
  (*     exp_eval me ve e v -> *)
  (*     Maps.PTree.get x env = Some (loc, typeof e) -> *)
  (*     Memory.Mem.valid_access m (chunk_of_typ (typeof e)) loc 0 Memtype.Writable -> *)
  (*     valid_val v (typeof e) -> *)
  (*     v = Values.Val.load_result (chunk_of_typ (typeof e)) v -> *)
  (*     compat_stmt me ve env m (Assign x e) *)
  (* | compat_stassign: forall me ve m (env: Clight.env) e v x co loc' loc ofs delta, *)
  (*     exp_eval me ve e v -> *)
  (*     Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta -> *)
  (*     In (x, typeof e) (Ctypes.co_members co) -> *)
  (*     Maps.PTree.get main_node (Clight.genv_cenv tge) = Some co -> *)
  (*     Maps.PTree.get self_id env = Some (loc', pointer_of_node main_node) -> *)
  (*     Memory.Mem.load (chunk_of_typ (pointer_of_node main_node)) m loc' 0 = Some (Values.Vptr loc ofs) -> *)
                                                                                     
  (*     Memory.Mem.valid_access m (chunk_of_typ (typeof e)) loc (Int.unsigned (Int.add ofs (Int.repr delta))) Memtype.Writable -> *)
  (*     valid_val v (typeof e) -> *)
  (*     v = Values.Val.load_result (chunk_of_typ (typeof e)) v -> *)
  (*     compat_stmt me ve env m (AssignSt x e) *)
  (* | compat_ite: forall me ve env m e s1 s2, *)
  (*     compat_stmt me ve env m s1 -> *)
  (*     compat_stmt me ve env m s2 -> *)
  (*     compat_stmt me ve env m (Ifte e s1 s2) *)
  (* | compat_comp: forall me ve m env s1 s2, *)
  (*     compat_stmt me ve env m s1 -> *)
  (*     compat_stmt me ve env m (Comp s1 s2) *)
  (*  | compat_skip: forall me ve m env, *)
  (*     compat_stmt me ve env m Skip. *)
  
  Remark find_add:
    forall x (v v': val) pm, 
      PM.find x (PM.add x v pm) = Some v' -> v' = v.
  Proof.
    induction x, pm; simpl; (eauto || now injection 1).
  Qed.

  Remark mto_add:
    forall x v v' (ve: venv),
      PM.MapsTo x v' (PM.add x v ve) -> v' = v.
  Proof.
    unfold PM.MapsTo.
    apply find_add.
  Qed.

  Remark mfindmem_add:
    forall x v v' (me: menv),
      mfind_mem x (madd_mem x v me) = Some v' -> v' = v.
  Proof.
    unfold mfind_mem, madd_mem. simpl.
    intros; eapply find_add; eauto.
  Qed.

  Definition mem_sep (e: Clight.env) (m: Memory.Mem.mem) :=
    forall x loc t (* co x' *) ofs (* delta t' *) loc' (* v *) loc'',
      In (x, t) c_main.(c_vars) -> 
      Maps.PTree.get x e = Some (loc, t) ->
      Maps.PTree.get self_id e = Some (loc'', pointer_of_node main_node) ->
      (* Maps.PTree.get main_node (Clight.genv_cenv tge) = Some co -> *)
      (* Ctypes.field_offset (Clight.genv_cenv tge) x' (Ctypes.co_members co) = Errors.OK delta -> *)
      (* Memory.Mem.load (chunk_of_typ t') m loc' (Int.unsigned (Int.add ofs (Int.repr delta))) = Some v -> *)
      Memory.Mem.load (chunk_of_typ (pointer_of_node main_node)) m loc'' 0 = Some (Values.Vptr loc' ofs) ->
      loc <> loc'.

  Definition self_sep (e: Clight.env) (m: Memory.Mem.mem) :=
    forall loc ofs loc',
      Maps.PTree.get self_id e = Some (loc', pointer_of_node main_node) ->
      Memory.Mem.load (chunk_of_typ (pointer_of_node main_node)) m loc' 0 = Some (Values.Vptr loc ofs) ->
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
      
  
  Ltac clear_refl_trivial :=
    match goal with
    | H: ?x = ?x |- _ => clear H
    end.
  Ltac clear_refl_trivials := repeat clear_refl_trivial.
  Ltac clean_context := clear_dups; clear_refl_trivials.
  
  Lemma compat_assign_pres:
    forall ve me env m loc x e v,
      compat_venv ve env m ->
      compat_menv me env m ->
      compat_vars env m ->
      compat_fields env m ->
      mem_sep env m ->
      self_sep env m ->
      nodup_env env ->
      nodup_vars ->
      Maps.PTree.get x env = Some (loc, typeof e) ->
      well_formed_stmt me ve (Assign x e) ->
      Memory.Mem.valid_access m (chunk_of_typ (typeof e)) loc 0 Memtype.Writable ->
      exp_eval me ve e v ->
      exists m', Memory.Mem.store (chunk_of_typ (typeof e)) m loc 0 v = Some m' 
            /\ compat_venv (PM.add x v ve) env m'
            /\ compat_menv me env m'
            /\ compat_vars env m' 
            /\ compat_fields env m' 
            /\ mem_sep env m'
            /\ self_sep env m'.
  Proof.
    intros ** Hvenv Hmenv Hvars Hfields Hsep Hself_sep Hnodupenv Hnodupvars Hget Hwf ? ?.
    inversion_clear Hwf as [? ? ? ? ? Hin ? ? ? ? Hloadres| | | |].
    app_exp_eval_det.
    edestruct Memory.Mem.valid_access_store with (v:=v) as [m']; eauto. 
    exists m'; repeat split; auto; clean_context.
    - unfold compat_venv; intros x' v' t' Hmto Hin'.
      destruct (AST.ident_eq x' x) as [|Hx].
      + subst x'.
        apply mto_add in Hmto; subst v'.
        generalize (Hnodupvars _ _ _ Hin Hin'); intro; subst t'. 
        exists loc; split; [|split]; auto.
        rewrite Hloadres; eapply Memory.Mem.load_store_same; eauto.
      + apply PM.add_3 in Hmto; auto.
        edestruct Hvenv as [loc' [? [Hload]]]; eauto.
        exists loc'; split; [|split]; auto. 
        destruct (Values.eq_block loc' loc).
        * subst loc'.
          edestruct Hnodupenv; eauto. 
        * rewrite <-Hload. 
          eapply Memory.Mem.load_store_other; eauto.
    - unfold compat_menv; intros x' v' t' Hmem Hin'.
      edestruct Hmenv
        as (co & loc'' & loc' & ofs & delta & ? & Hload & ? & ? & Hself' & Hloadptr & ?); eauto.
      exists co, loc'', loc', ofs, delta.
      split; [|split; [|split; [|repeat split]]]; auto.
      + destruct (Values.eq_block loc loc').
        * edestruct Hsep with (2:=Hget); eauto; contradiction.
        * rewrite <-Hload.
          eapply Memory.Mem.load_store_other; eauto.
      + destruct (Values.eq_block loc'' loc).
        * subst loc''.
          edestruct Hnodupenv with (2:=Hget); eauto.
        * rewrite <-Hloadptr.
          eapply Memory.Mem.load_store_other; eauto.
    - unfold compat_vars; intros x' t' Hin'.
      edestruct Hvars as (loc' & ? & ?); eauto.
      exists loc'; split; auto.
      eapply Memory.Mem.store_valid_access_1; eauto.
    - unfold compat_fields; intros x' t' Hin'.
      edestruct Hfields as (co & loc1' & loc1 & ofs & delta & ? & ? & ? & ? & Hload & ?); eauto. 
      exists co, loc1', loc1, ofs, delta; split; [|split; [|split; [|split; [|split]]]]; auto.
      + destruct (Values.eq_block loc1' loc).
        * subst loc1'.
          edestruct Hnodupenv with (2:=Hget); eauto.
        * rewrite <-Hload; eapply Memory.Mem.load_store_other; eauto.
      + eapply Memory.Mem.store_valid_access_1; eauto.
    - unfold mem_sep; intros x' loc1 t' ofs loc1' loc1'' Hin1 Hget1 Hself Hload.
      eapply Hsep; eauto.
      instantiate (1:=ofs).
      destruct (Values.eq_block loc1'' loc).
      + subst loc1''.
        edestruct Hnodupenv with (2:=Hget); eauto.
      + rewrite <-Hload; symmetry; eapply Memory.Mem.load_store_other; eauto.
    - unfold self_sep; intros loc1 ofs loc1' Hself Hload.
      eapply Hself_sep; eauto.
      instantiate (1:=ofs).
      destruct (Values.eq_block loc1' loc).
      + subst loc1'.
        edestruct Hnodupenv with (2:=Hget); eauto.
      + rewrite <-Hload; symmetry; eapply Memory.Mem.load_store_other; eauto.
  Qed.

   Lemma compat_stassign_pres:
    forall ve me env m x e v co loc loc' ofs delta,
      compat_venv ve env m ->
      compat_menv me env m ->
      compat_vars env m ->
      compat_fields env m ->
      mem_sep env m ->
      self_sep env m ->
      fields_sep m ->
      nodup_mems ->
      In (x, (typeof e)) (Ctypes.co_members co) ->
      Ctypes.field_offset tge.(Clight.genv_cenv) x (Ctypes.co_members co) = Errors.OK delta ->
      Maps.PTree.get main_node (Clight.genv_cenv tge) = Some co ->
      Maps.PTree.get self_id env = Some (loc', pointer_of_node main_node) ->
      Memory.Mem.load (chunk_of_typ (pointer_of_node main_node)) m loc' 0 = Some (Values.Vptr loc ofs) ->
      well_formed_stmt me ve (AssignSt x e) ->
      Memory.Mem.valid_access m (chunk_of_typ (typeof e)) loc (Int.unsigned (Int.add ofs (Int.repr delta))) Memtype.Writable ->
      exp_eval me ve e v ->
      exists m',
        Memory.Mem.store (chunk_of_typ (typeof e)) m loc (Int.unsigned (Int.add ofs (Int.repr delta))) v = Some m'
        /\ compat_venv ve env m'
        /\ compat_menv (madd_mem x v me) env m'
        /\ compat_vars env m'
        /\ compat_fields env m'
        /\ mem_sep env m'
        /\ self_sep env m'.
  Proof.
    intros ** Hvenv Hmenv Hvars Hfields Hsep Hself_sep Hfields_sep Hnodupmems Hmembers Hoffset Hmain Hself Hloadptr Hwf ? ?.
    (* inversion_clear Hcompat as [|? ? ? ? ? v' ? co' loc1' loc1 ofs' delta' Heval' Hoffset' Hmembers' Hmain' Hself' Hloadptr' ? ? Hloadres| | |].  *)
    inversion_clear Hwf as [|? ? ? ? ? Hin ? ? ? ? Hloadres| | |].
    (* rewrite Hmain in Hmain'; inversion Hmain'; subst co'. *)
    (* rewrite Hself in Hself'; inversion Hself'; subst loc1'. *)
    (* rewrite Hoffset in Hoffset'; inversion Hoffset'; subst delta'. *)
    (* rewrite Hloadptr in Hloadptr'; inversion Hloadptr'; subst loc1 ofs'. *)
    app_exp_eval_det.
    edestruct Memory.Mem.valid_access_store with (v:=v) as [m']; eauto. 
    exists m'; repeat (split; auto); clean_context.
    - unfold compat_venv; intros x' v' t' Hmto Hin'.
      edestruct Hvenv as (loc'' & Hget & Hload' & ?); eauto.
      exists loc''; split; [|split]; auto.
      destruct (Values.eq_block loc'' loc).
      + edestruct Hsep with (1:=Hin'); eauto.
      + rewrite <-Hload'.
        eapply Memory.Mem.load_store_other; eauto.
    - unfold compat_menv; intros x' v' t' Hmem Hin'.
      destruct (AST.ident_eq x' x).
      + subst x'.
        apply mfindmem_add in Hmem; subst v'.
        generalize (Hnodupmems _ _ _ Hin Hin'); intro; subst t'. 
        exists co, loc', loc, ofs, delta.
        split; [|split; [|split; [|split; [|repeat split]]]]; auto.
        * rewrite Hloadres; eapply Memory.Mem.load_store_same; eauto.
        *{ destruct (Values.eq_block loc' loc).
           - edestruct Hself_sep; eauto.  
           - rewrite <-Hloadptr.
             eapply Memory.Mem.load_store_other; eauto.
         }
      + rewrite mfind_mem_gso in Hmem; auto.
        edestruct Hmenv
          as (co' & loc1' & loc1 & ofs' & delta' & ? & Hload' & ? & Hmain1 & Hself1 & Hloadptr1 & ?); eauto. 
        rewrite Hmain in Hmain1; inversion Hmain1; subst co'.
        rewrite Hself in Hself1; inversion Hself1; subst loc1'.
        rewrite Hloadptr in Hloadptr1; inversion Hloadptr1; subst loc1 ofs'.
        exists co, loc', loc, ofs, delta'.
        split; [|split; [|split; [|split; [|repeat split]]]]; auto.
        * rewrite <-Hload'. eapply Memory.Mem.load_store_other; eauto. 
        *{ destruct (Values.eq_block loc' loc).
           - edestruct Hself_sep; eauto. 
           - rewrite <-Hloadptr.
             eapply Memory.Mem.load_store_other; eauto.
         }
    - unfold compat_vars; intros x' t' Hin'.
      edestruct Hvars as (loc1' & ? & ?); eauto.
      exists loc1'; split; auto.
      eapply Memory.Mem.store_valid_access_1; eauto.
    - unfold compat_fields; intros x' t' Hin'.
      edestruct Hfields as (co' & loc1' & loc1 & ofs' & delta' & ? & ? & ? & Hself' & Hload & ?); eauto. 
      exists co', loc1', loc1, ofs', delta'; split; [|split; [|split; [|split; [|split]]]]; auto.
      + destruct (Values.eq_block loc1' loc).
        * subst loc1'.
          rewrite Hself in Hself'; inversion Hself'. subst loc'.
          edestruct Hself_sep; eauto.
        * rewrite <-Hload; eapply Memory.Mem.load_store_other; eauto.
      + eapply Memory.Mem.store_valid_access_1; eauto.          
    - unfold mem_sep; intros x' loc1 t' ofs' loc1' loc1'' Hin1 Hget1 Hself' Hload.
      eapply Hsep; eauto.
      instantiate (1:=ofs').
      destruct (Values.eq_block loc1'' loc).
      + subst loc1''.
        rewrite Hself in Hself'; inversion Hself'. subst loc'.
        edestruct Hself_sep; eauto.  
      + rewrite <-Hload; symmetry; eapply Memory.Mem.load_store_other; eauto.
    - unfold self_sep; intros loc1 ofs' loc1' Hself' Hload.
      eapply Hself_sep; eauto.
      instantiate (1:=ofs').
      destruct (Values.eq_block loc1' loc).
      + subst loc1'.
        rewrite Hself in Hself'; inversion Hself'. subst loc'.
        edestruct Hself_sep; eauto.  
      + rewrite <-Hload; symmetry; eapply Memory.Mem.load_store_other; eauto.
  Qed.

Remark ifte_translate:
    forall (b: bool) s1 s2,
      translate_stmt main_node (if b then s1 else s2) =
      if b then (translate_stmt main_node s1) else (translate_stmt main_node s2).
  Proof.
    now destruct b.
  Qed.  

  Hint Constructors Clight.eval_lvalue Clight.eval_expr well_formed_stmt.
  Hint Resolve expr_eval_simu Clight.assign_loc_value sem_cast_same.
  Hint Constructors well_formed_stmt.

  Definition c_state := (Clight.env * Clight.temp_env * Memory.Mem.mem)%type.
   
  Inductive match_states_bigbig: state -> c_state -> Prop :=
  | intro_state: forall me ve e le m,
      (* state correspondance *)
      compat_venv ve e m ->     
      compat_menv me e m ->

      (* Clight state well defined *)
      compat_vars e m ->
      compat_fields e m ->

      (* Clight side separation *)
      mem_sep e m ->
      self_sep e m ->
      fields_sep m ->
      nodup_env e ->

      (* Minimp side separation *)
      nodup_vars ->
      nodup_mems ->
      match_states_bigbig (me, ve) (e, le, m).

  Hint Constructors match_states.

  Definition well_formed_stmt' S := well_formed_stmt (fst S) (snd S). 
  
  Theorem simu_bigstep:
    forall S1 s S2,
      well_formed_stmt' S1 s ->
      stmt_eval S1 s S2 ->
      forall e1 le1 m1,
        match_states S1 (e1, le1, m1) ->
        (* compat_stmt' S1 e1 m1 s -> *)
        exists le2 m2 t,
          ClightBigstep.exec_stmt tge e1 le1 m1 (translate_stmt main_node s) t le2 m2 ClightBigstep.Out_normal
          /\ match_states S2 (e1, le2, m2).
  Proof.
    induction 2; inversion_clear H; 
    inversion_clear 1 as [? ? ? ? ? Hvenv Hmenv Hvars Hfields].
    
    (* Assign x e : "x = e" *)
    - app_exp_eval_det.
      edestruct Hvars; eauto.
      edestruct compat_assign_pres as [m']; destruct_conjs; eauto.
      do 3 econstructor; split.
      + eapply ClightBigstep.exec_Sassign; eauto. 
        rewrite type_pres; auto. 
      + constructor; auto. 

    (* AssignSt x e : "self->x = e"*)
    - app_exp_eval_det.
      edestruct Hfields; eauto; destruct_conjs.
      edestruct compat_stassign_pres as [m']; eauto; destruct_conjs. 
      do 3 econstructor; split.
      + eapply ClightBigstep.exec_Sassign; eauto.
        *{ eapply Clight.eval_Efield_struct
           with (id:=main_node) (att:=Ctypes.noattr); eauto.
           eapply Clight.eval_Elvalue; eauto. 
           - apply Clight.eval_Ederef. 
             eapply Clight.eval_Elvalue; eauto.
             apply Clight.deref_loc_value with (chunk:=AST.Mint32); eauto.
           - apply Clight.deref_loc_copy; auto.
         }
        * rewrite type_pres; auto. 
      + constructor; auto. 

    (* Ifte e s1 s2 : "if e then s1 else s2" *)
    - edestruct IHstmt_eval as (le2 & m2 & t & ? & ?); eauto;
      [destruct b|]; auto.
      do 3 econstructor; split; eauto.
      eapply ClightBigstep.exec_Sifthenelse; eauto.
      + erewrite type_pres, bool_val_ptr; eauto. 
      + fold translate_stmt; rewrite <-ifte_translate; eauto.

    (* Comp s1 s2 : "s1; s2" *)
    - app_stmt_eval_det.
      edestruct IHstmt_eval1 as (le2 & m2 & t1 & ? & ?); eauto.
      edestruct IHstmt_eval2 as (le3 & m3 & t2 & ? & ?); eauto.
      do 3 econstructor; split; eauto.
      eapply ClightBigstep.exec_Sseq_1; eauto.
     
    (* Skip : "skip" *)
    - do 3 econstructor; split; eauto.
      eapply ClightBigstep.exec_Sskip.
  Qed.