Require cfrontend.Clight.
Require Import lib.Integers.

Require Import Rustre.Common.
Require Import Rustre.RMemory.

Require Import Syn Sem2 Tra.

Require Import Program.Tactics.
Require Import List.
Import List.ListNotations.
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

  (* Lemma well_formed_main: well_formed_cls c_main. *)
  (* Proof. *)
  (*   unfold well_formed in WF. *)
  (*   rewrite Forall_forall in WF. *)
  (*   apply find_class_In in MAINNODE; auto. *)
  (* Qed. *)
    
  (* Hypothesis BUILD_CO_OK: *)
  (*   Ctypes.build_composite_env (map translate_class prog.(p_cls)) = Errors.OK (Clight.genv_cenv tge). *)

  (* Hypothesis VE_IN_VARS: forall x v (ve: venv), PM.MapsTo x v ve -> exists t, In (x, t) prog.(p_vars). *)

  Lemma build_co_ok:
    Ctypes.build_composite_env (map translate_class prog) = Errors.OK (Clight.genv_cenv tge).
  Proof.
    unfold translate in TRANSL.
    rewrite MAINNODE in TRANSL.
    unfold Clight.make_program in TRANSL.
    destruct prog.
    - discriminate.
    - unfold Ctypes.build_composite_env in *; simpl in *.
      destruct (translate_class c).
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
  
  (* Lemma tr_main_node: *)
  (*   exists co, *)
  (*     Maps.PTree.get main_node (Clight.genv_cenv tge) = Some co *)
  (*     /\ (forall x (me: menv) v, *)
  (*           mfind_mem x me = Some v -> *)
  (*           exists delta, *)
  (*             Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta). *)
  (* Proof. *)
  (*   destruct MAINNODE as [c [? Hcls]]. *)
  (*   assert (In (translate_class c) (map translate_class prog.(p_cls))) as Hin. *)
  (*   - clear TRANSL MAINNODE BUILD_CO_OK. *)
  (*     apply in_map. *)
  (*     induction (p_cls prog); simpl in *. *)
  (*     + discriminate. *)
  (*     + destruct (ident_eqb (c_name a) main_node). *)
  (*       * inv Hcls; now left. *)
  (*       * right; now apply IHl. *)
  (*   - unfold translate_class in Hin. *)
  (*     apply find_class_name in Hcls. *)
  (*     destruct c; simpl in Hcls; subst. *)
  (*     pose proof (Ctypes.build_composite_env_charact _ _ _ _ _ _ BUILD_CO_OK Hin) as [co Hco]. *)
  (*     exists co; split. *)
  (*     * tauto. *)
  (*     * intros ** Hx. *)
  (*       admit.                (* how to get a delta witness ??? *) *)
  (* Qed. *)
  
  (* Axiom wt_state_pred: ident * typ -> program -> Prop. *)
  (* Inductive well_typed_exp: exp -> Prop := *)
  (* | wt_var: forall x ty, *)
  (*     In (x, ty) prog.(p_vars) -> *)
  (*     well_typed_exp (Var x ty) *)
  (* | wt_state: forall x ty, *)
  (*     wt_state_pred (x, ty) prog -> *)
  (*     well_typed_exp (State x ty) *)
  (* | wt_const: forall c ty, *)
  (*     well_typed_exp (Const c ty). *)

  (* Inductive well_typed: stmt -> Prop := *)
  (* | wt_assign: forall x e, *)
  (*     x <> self_id -> *)
  (*     In (x, typeof e) prog.(p_vars) -> *)
  (*     well_typed_exp e -> *)
  (*     well_typed (Assign x e) *)
  (* | wt_stassign: forall x e, *)
  (*     x <> self_id -> *)
  (*     wt_state_pred (x, typeof e) prog -> *)
  (*     well_typed_exp e -> *)
  (*     well_typed (AssignSt x e) *)
  (* | wt_skip:  *)
  (*     well_typed Skip. *)

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
        (* /\ In (x, t) (Ctypes.co_members co) *)
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
      well_formed_exp c_main exp ->
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
  
  Definition compat_vars (env: Clight.env): Prop :=
    forall x t,
      In (x, t) c_main.(c_vars) ->
      exists loc, Maps.PTree.get x env = Some (loc, t).

  Definition compat_fields (env: Clight.env) (m: Memory.Mem.mem): Prop :=
    forall x t,
      In (x, t) c_main.(c_mems) ->
      exists co loc' loc ofs delta,
        Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta
        /\ In (x, t) (Ctypes.co_members co)
        /\ Maps.PTree.get main_node (Clight.genv_cenv tge) = Some co
        /\ Maps.PTree.get self_id env = Some (loc', pointer_of_node main_node)
        /\ Memory.Mem.load (chunk_of_typ (pointer_of_node main_node)) m loc' 0 = Some (Values.Vptr loc ofs).

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
  
  Inductive compat_stmt: menv -> venv -> Clight.env -> Memory.Mem.mem -> stmt -> Prop :=
  | compat_assign: forall me ve m (env: Clight.env) e v x loc,
      exp_eval me ve e v ->
      Maps.PTree.get x env = Some (loc, typeof e) ->
      Memory.Mem.valid_access m (chunk_of_typ (typeof e)) loc 0 Memtype.Writable ->
      valid_val v (typeof e) ->
      v = Values.Val.load_result (chunk_of_typ (typeof e)) v ->
      compat_stmt me ve env m (Assign x e)
  | compat_stassign: forall me ve m (env: Clight.env) e v x co loc' loc ofs delta,
      exp_eval me ve e v ->
      Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta ->
      In (x, typeof e) (Ctypes.co_members co) ->
      Maps.PTree.get main_node (Clight.genv_cenv tge) = Some co ->
      Maps.PTree.get self_id env = Some (loc', pointer_of_node main_node) ->
      Memory.Mem.load (chunk_of_typ (pointer_of_node main_node)) m loc' 0 = Some (Values.Vptr loc ofs) ->
                                                                                     
      Memory.Mem.valid_access m (chunk_of_typ (typeof e)) loc (Int.unsigned (Int.add ofs (Int.repr delta))) Memtype.Writable ->
      valid_val v (typeof e) ->
      v = Values.Val.load_result (chunk_of_typ (typeof e)) v ->
      compat_stmt me ve env m (AssignSt x e)
  | compat_comp: forall me1 ve1 (* me2 ve2 *) m1 (* m2 *) env s1 s2,
      compat_stmt me1 ve1 env m1 s1 ->
      (* stmt_eval (me1, ve1, s1) (me2, ve2, Skip) -> *)
      (* compat_venv ve2 env m2 -> *)
      (* compat_menv me2 env m2 -> *)
      (* compat_stmt me2 ve2 env m2 s2 -> *)
      compat_stmt me1 ve1 env m1 (Comp s1 s2)
  | compat_skip: forall me ve m env,
      compat_stmt me ve env m Skip.
  
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
  
  Lemma compat_assign_pres:
    forall ve me env m loc x e v,
      compat_venv ve env m ->
      compat_menv me env m ->
      nodup_env env ->
      nodup_vars ->
      Maps.PTree.get x env = Some (loc, typeof e) ->
      well_formed_stmt c_main (Assign x e) ->
      compat_stmt me ve env m (Assign x e) ->
      exp_eval me ve e v ->
      exists m', Memory.Mem.store (chunk_of_typ (typeof e)) m loc 0 v = Some m' 
            /\ compat_venv (PM.add x v ve) env m'
            /\ compat_menv me env m'.
  Proof.
    intros ** Hvenv Hmenv Hnodupenv Hnodupvars Hget Hwf Hcompat ?.
    inversion_clear Hcompat as [? ? ? ? ? v' ? loc' ? Hget' ? ? Hloadres| | |]. 
    inversion_clear Hwf as [? ? Hin| | |].
    rewrite Hget in Hget'; inversion Hget'; subst loc'.        
    app_exp_eval_det.
    edestruct Memory.Mem.valid_access_store with (v:=v) as [m']; eauto. 
    exists m'; repeat split; auto. 
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
      + destruct (Values.eq_block loc' loc).
        * subst loc'.
          admit.                (* arf *)
        * rewrite <-Hload.
          eapply Memory.Mem.load_store_other; eauto.
      + destruct (Values.eq_block loc'' loc).
        * subst loc''.
          edestruct Hnodupenv with (2:=Hget); eauto.
        * rewrite <-Hloadptr.
          eapply Memory.Mem.load_store_other; eauto.
  Qed.

   Lemma compat_stassign_pres:
    forall ve me env m x e v co loc loc' ofs delta,
      compat_venv ve env m ->
      compat_menv me env m ->
      nodup_mems ->
      In (x, (typeof e)) (Ctypes.co_members co) ->
      Ctypes.field_offset tge.(Clight.genv_cenv) x (Ctypes.co_members co) = Errors.OK delta ->
      Maps.PTree.get main_node (Clight.genv_cenv tge) = Some co ->
      Maps.PTree.get self_id env = Some (loc', pointer_of_node main_node) ->
      Memory.Mem.load (chunk_of_typ (pointer_of_node main_node)) m loc' 0 = Some (Values.Vptr loc ofs) ->
      well_formed_stmt c_main (AssignSt x e) ->
      compat_stmt me ve env m (AssignSt x e) ->
      exp_eval me ve e v ->
      exists m',
        Memory.Mem.store (chunk_of_typ (typeof e)) m loc (Int.unsigned (Int.add ofs (Int.repr delta))) v = Some m'
        /\ compat_venv ve env m'
        /\ compat_menv (madd_mem x v me) env m'.
  Proof.
    intros ** Hvenv Hmenv Hnodupmems Hmembers Hoffset Hmain Hself Hloadptr Hwf Hcompat Heval.
    inversion_clear Hcompat as [|? ? ? ? ? v' ? co' loc1' loc1 ofs' delta' Heval' Hoffset' Hmembers' Hmain' Hself' Hloadptr' ? ? Hloadres| |]. 
    inversion_clear Hwf as [|? ? Hin| |].
    rewrite Hmain in Hmain'; inversion Hmain'; subst co'.
    rewrite Hself in Hself'; inversion Hself'; subst loc1'.
    rewrite Hoffset in Hoffset'; inversion Hoffset'; subst delta'.
    rewrite Hloadptr in Hloadptr'; inversion Hloadptr'; subst loc1 ofs'.
    app_exp_eval_det.
    edestruct Memory.Mem.valid_access_store with (v:=v) as [m']; eauto. 
    exists m'; repeat (split; auto).
    - unfold compat_venv; intros x' v' t' Hmto Hin'.
      edestruct Hvenv as (loc'' & Hget & Hload' & ?); eauto.
      exists loc''; split; [|split]; auto.
      destruct (Values.eq_block loc'' loc).
      + subst loc''.
        admit.
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
           - subst loc'.
             admit.
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
        * rewrite <-Hload'. eapply Memory.Mem.load_store_other; eauto. right.
          admit.
        *{ destruct (Values.eq_block loc' loc).
           - subst loc'. admit.
           - rewrite <-Hloadptr.
             eapply Memory.Mem.load_store_other; eauto.
         }
  Qed.

  Inductive compat_cont: menv -> venv -> Clight.env -> Memory.Mem.mem -> cont -> Clight.cont -> Prop :=
  | compat_kstop: forall me ve e m,
      compat_cont me ve e m Kstop Clight.Kstop
  | compat_kseq: forall me ve e m s k k',
      well_formed_stmt c_main s ->
      compat_stmt me ve e m s ->
      compat_cont me ve e m k k' ->
      compat_cont me ve e m (Kseq s k) (Clight.Kseq (translate_stmt main_node s) k').
  
  Inductive match_states: state * stmt * cont -> Clight.state -> Prop :=
    intro_state: forall me ve s k k' e le m,
      compat_venv ve e m ->
      compat_menv me e m ->
      well_formed_stmt c_main s ->
      compat_stmt me ve e m s ->
      (* state_context (me, ve, s) k e le m -> *)
      compat_cont me ve e m k k' ->
      nodup_env e ->
      nodup_vars ->
      nodup_mems ->
      match_states
        ((me, ve), s, k)
        (Clight.State main_fun (translate_stmt main_node s) k' e le m).
  
  Hint Resolve expr_eval_simu Clight.assign_loc_value sem_cast_same.
  Hint Constructors compat_stmt compat_cont match_states(* state_context *).
  Hint Constructors well_formed_stmt.
        
  Ltac discriminate' :=
    match goal with
    | H: ?x <> ?x |- _ => contradict H; reflexivity
    end.
  
  Theorem simu:
    forall S1 S2,
      stmt_eval_cont S1 S2 ->
      forall S1',
        match_states S1 S1' ->
        exists S2' t,
          Smallstep.plus Clight.step1 tge S1' t S2'
          /\ match_states S2 S2'.
  Proof.
    induction 1;
    inversion_clear 1 as [? ? ? ? ? ? ? ? Hvenv Hmenv Hwf Hstmt (* Hctxt *) Hcont];
    inv Hwf; inversion_clear Hstmt; (* inversion Hctxt; *)
    (* (((subst s1 || subst s2); inv_stmt_eval) || destruct_conjs). *)
    destruct_conjs.
    
    (* Assign x e : "x = e" *)
    - app_exp_eval_det.
      edestruct compat_assign_pres as [m']; eauto; destruct_conjs. 
      do 2 econstructor; split.
      + eapply Smallstep.plus_one, Clight.step_assign; eauto. 
        rewrite type_pres; auto. 
      + constructor; auto. admit.
        
    (* AssignSt x e : "self->x = e"*)
    - app_exp_eval_det.
      edestruct compat_stassign_pres as [m']; eauto; destruct_conjs. 
      do 2 econstructor; split.
      + eapply Smallstep.plus_one, Clight.step_assign; eauto.
        *{ eapply Clight.eval_Efield_struct
           with (id:=main_node) (att:=Ctypes.noattr); eauto.
           eapply Clight.eval_Elvalue; eauto. 
           - apply Clight.eval_Ederef. 
             eapply Clight.eval_Elvalue; eauto.
             apply Clight.deref_loc_value with (chunk:=AST.Mint32); eauto.
           - apply Clight.deref_loc_copy; auto.
         }
        * rewrite type_pres; auto. 
      + constructor; auto.  admit.

    (* Comp s1 s2 : "s1; s2" *)
    - do 2 econstructor; split.
      + eapply Smallstep.plus_one, Clight.step_seq.
      + constructor; auto. admit.
     
    (* Skip : "skip" *)
    - inv Hcont.
      do 2 econstructor; split.
      + eapply Smallstep.plus_one, Clight.step_skip_seq.
      + constructor; auto. 
  Qed.