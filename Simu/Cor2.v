Require Import ClightBigstep2.
Require cfrontend.Clight.
Require Import lib.Integers.

Require Import Rustre.Common.
Require Import Rustre.RMemory.
Require Import Rustre.Nelist.

Require Import Syn Sem Tra2.

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
  Hypothesis UNIQUE: unique_classes prog.
  
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
  | wf_assign: forall x e (* v *),
      In (x, typeof e) c.(c_vars) ->
      x <> self_id ->
      well_formed_exp c e ->
      (* exp_eval S e v -> *)
      (* valid_val v (typeof e) -> *)
      (* v = Values.Val.load_result (chunk_of_typ (typeof e)) v -> *)
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
  | wf_step: forall y ty c' prog' clsid o es vs me (*me' rv *),
      In (y, ty) c.(c_vars) ->
      y <> self_id ->
      In {| obj_inst := o; obj_class := clsid |} c.(c_objs) ->
      find_class clsid prog = Some (c', prog') ->
      Nelist.Forall (well_formed_exp c) es ->
      Nelist.Forall2 (exp_eval S) es vs ->
      Nelist.Forall2 (fun e v => valid_val v (typeof e)) es vs ->
      Nelist.Forall2 (fun e x => typeof e = snd x) es c'.(c_input) ->
      ty = snd c'.(c_output) ->
      (* well_formed_stmt c' S c'.(c_step) -> *)
      find_inst o S me ->
      well_formed_stmt c' (me, adds (Nelist.map_fst c'.(c_input)) vs v_empty) c'.(c_step) ->
      (* stmt_step_eval prog me clsid vs me' rv -> *)
      (* valid_val rv ty -> *)
      (* rv = Values.Val.load_result (chunk_of_typ ty) rv -> *)
      well_formed_stmt c S (Step_ap y ty clsid o es)
  | wf_skip: 
      well_formed_stmt c S Skip.

  Definition well_formed_cls (c: class) (S: state): Prop := well_formed_stmt c S c.(c_step).

  Definition compat_vars (c: class) (S: state) (le: Clight.temp_env): Prop :=
    forall x t v,
      In c prog ->
      In (x, t) c.(c_vars) ->
      find_var x S v ->
      Maps.PTree.get x le = Some v.

  Definition compat_self (c: class) (S: state) (le: Clight.temp_env) (m: Memory.Mem.mem): Prop :=
    In c prog ->
    exists co loc_struct ofs,
      Maps.PTree.get self_id le = Some (Values.Vptr loc_struct ofs)
      /\ Maps.PTree.get c.(c_name) tge.(Clight.genv_cenv) = Some co
      /\ (forall x t,
            In (x, t) c.(c_mems) ->
            exists delta,
              Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta
              /\ In (x, t) (Ctypes.co_members co)
              /\ Memory.Mem.valid_access m (chunk_of_typ t) loc_struct (Int.unsigned (Int.add ofs (Int.repr delta))) Memtype.Writable
              /\ forall v,
                  find_field x S v ->
                  (Memory.Mem.load (chunk_of_typ t) m loc_struct (Int.unsigned (Int.add ofs (Int.repr delta))) = Some v
                   /\ valid_val v t))
      /\ (forall o,
            In o c.(c_objs) ->
            exists delta,
              Ctypes.field_offset (Clight.genv_cenv tge) o.(obj_inst) (Ctypes.co_members co) = Errors.OK delta).

  
  Remark valid_val_implies_access:
    forall v t, valid_val v t -> Ctypes.access_mode t = Ctypes.By_value (chunk_of_typ t).
  Proof. introv H; apply H. Qed.
    
  Hint Constructors Clight.eval_lvalue Clight.eval_expr well_formed_stmt.
  Hint Resolve valid_val_implies_access.

  Remark evall_self_field:
    forall c e le m x t co loc_struct ofs delta,
      Maps.PTree.get self_id le = Some (Values.Vptr loc_struct ofs) ->
      Maps.PTree.get (c_name c) (Clight.genv_cenv tge) = Some co ->
      Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta ->
      Clight.eval_lvalue tge e le m (deref_self_field c.(c_name) x t) loc_struct (Int.add ofs (Int.repr delta)).
  Proof.
    intros.
    eapply Clight.eval_Efield_struct
    with (id:=c.(c_name)) (att:=Ctypes.noattr); eauto.
    eapply Clight.eval_Elvalue. 
    - do 2 econstructor; eauto.
    - apply* Clight.deref_loc_copy.
  Qed.
  
  Remark eval_self_field:
    forall c S e le m x t v,
      compat_self c S le m ->
      In c prog ->
      In (x, t) c.(c_mems) ->
      find_field x S v ->
      Clight.eval_expr tge e le m (deref_self_field c.(c_name) x t) v.
  Proof.
    introv Hself ? Hin Hfind.
    destruct* Hself as (? & ? & ? & ? & ? & Hmem & ?).
    specializes Hmem Hin.
    destruct Hmem as (? & ? & ? & ? & Hval).
    specializes Hval Hfind.
    eapply Clight.eval_Elvalue.
    + apply* evall_self_field.
    + apply* Clight.deref_loc_value.      
  Qed.
  
  Lemma expr_eval_simu:
    forall c S exp v e le m,
      compat_vars c S le ->
      compat_self c S le m ->
      In c prog ->
      well_formed_exp c exp ->
      exp_eval S exp v ->
      Clight.eval_expr tge e le m (translate_exp c.(c_name) exp) v.
  Proof.
    intros c S exp; induction exp as [| |cst];
    introv Hvars ? ? Hwf Heval; inverts Heval; inverts Hwf.

    (* Var x ty : "x" *)
    - constructor; apply* Hvars. 
      
    (* State x ty : "self->x" *)
    - apply* eval_self_field.
      
    (* Const c ty : "c" *)
    - destruct cst; constructor.
  Qed.

  Lemma exprs_eval_simu:
    forall c S es es' vs e le m,
      compat_vars c S le ->
      compat_self c S le m ->
      In c prog ->
      Nelist.Forall (well_formed_exp c) es ->
      Nelist.Forall2 (fun e v => valid_val v (typeof e)) es vs ->
      Nelist.Forall2 (exp_eval S) es vs ->
      es' = nelist2list (Nelist.map (translate_exp c.(c_name)) es) ->
      Clight.eval_exprlist tge e le m es' (list_type_to_typelist (map Clight.typeof es')) (nelist2list vs).
  Proof.
    Hint Constructors Clight.eval_exprlist.
    introv ? ? ? Hwf Hvalid Hev ?; subst es';
    induction Hev; inverts Hwf; inverts Hvalid; econstructor;
    (apply* expr_eval_simu || (rewrite type_pres; apply* sem_cast_same) || eauto).
  Qed.

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

  Definition match_step (e: Clight.env) :=
    forall c,
      In c prog ->
      exists loc_f f,
        Globalenvs.Genv.find_symbol tge.(Clight.genv_genv) (step_id c.(c_name)) = Some loc_f
        /\ Maps.PTree.get (step_id c.(c_name)) e = None
        /\ Globalenvs.Genv.find_funct_ptr tge.(Clight.genv_genv) loc_f = Some (Clight.Internal f)
        /\ Clight.type_of_fundef (Clight.Internal f) =
          Ctypes.Tfunction (Ctypes.Tcons (type_of_inst_p c.(c_name))
                                         (list_type_to_typelist (map snd (nelist2list c.(c_input)))))
                           (snd c.(c_output)) AST.cc_default
        /\ Coqlib.list_norepet (Clight.var_names (Clight.fn_vars f))
        /\ Coqlib.list_norepet (Clight.var_names (Clight.fn_params f))
        /\ Coqlib.list_disjoint (Clight.var_names (Clight.fn_params f)) (Clight.var_names (Clight.fn_temps f))
        /\ Clight.fn_body f = translate_stmt c.(c_name) c.(c_step)
        (* /\ length f.(Clight.fn_params) = 1 + Nelist.length c.(c_input) *)
        /\ f.(Clight.fn_params) = (self_id, type_of_inst_p c.(c_name)) :: Nelist.nelist2list c.(c_input)
        /\ Forall (fun x => Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_typ (snd x)))
                 (f.(Clight.fn_params) ++ f.(Clight.fn_vars)).
  
  Definition c_state := (Clight.env * Clight.temp_env * Memory.Mem.mem)%type.
   
  Inductive match_states_bigbig (c: class) (S: state): c_state -> Prop :=
    intro_state_bigbig: forall e le m,
      (* state correspondance *)
      compat_vars c S le ->
      compat_self c S le m ->

      (* function *)
      match_step e ->
      
      (* Clight side separation *)
      fields_sep m ->

      (* Minimp side separation *)
      nodup_mems c ->
      
      match_states_bigbig c S (e, le, m).

  Hint Constructors match_states_bigbig.
  
  Lemma compat_assign_pres:
    forall c S e le m x v,
      In c prog ->
      match_states_bigbig c S (e, le, m) ->
      x <> self_id ->
      match_states_bigbig c (update_var x S v) (e, Maps.PTree.set x v le, m).
  Proof.
    introv ? MS ?.
    inverts MS as Hvars Hself.
    constructor*.
    - unfold compat_vars.
      intros x' t' v' ? Hin Hfind.
      destruct (AST.ident_eq x' x).
      + subst x'.
        apply find_update_var in Hfind; subst v'.
        apply Maps.PTree.gss.
      + apply gso_var in Hfind; auto.
        rewrite Maps.PTree.gso; auto.
        apply* Hvars.

    - unfold compat_self.
      intros.
      destruct* Hself; destruct_conjs.
      do 3 econstructor; splits*.
      rewrite* Maps.PTree.gso.
  Qed.

  Hint Resolve compat_assign_pres.
  
   Remark size_type_chunk:
    forall v t,
      valid_val v t ->
      Memdata.size_chunk (chunk_of_typ t) = Ctypes.sizeof tge.(Clight.genv_cenv) t.
  Proof.
    unfold valid_val; intros; destruct_pairs.
    destruct t, v;
      (destruct i, s || destruct f || idtac);
      (discriminates || contradiction || auto).
  Qed.
  
  Lemma compat_stassign_pres:
    forall c S e le m x t v co loc_struct ofs delta,
      In c prog ->
      match_states_bigbig c S (e, le, m) ->
      Ctypes.field_offset tge.(Clight.genv_cenv) x (Ctypes.co_members co) = Errors.OK delta ->
      Maps.PTree.get c.(c_name) (Clight.genv_cenv tge) = Some co ->
      Maps.PTree.get self_id le = Some (Values.Vptr loc_struct ofs) ->
      In (x, t) c.(c_mems) ->
      v = Values.Val.load_result (chunk_of_typ t) v ->
      valid_val v t ->
     Memory.Mem.valid_access m (chunk_of_typ t) loc_struct (Int.unsigned (Int.add ofs (Int.repr delta))) Memtype.Writable ->
      exists m',
        Memory.Mem.store (chunk_of_typ t) m loc_struct (Int.unsigned (Int.add ofs (Int.repr delta))) v = Some m'
        /\ match_states_bigbig c (update_field x S v) (e, le, m').
  Proof.
    intros ** ? MS Hoffset Hget_co Hget_self Hin Hloadres ? ? .
    inverts MS as Hvars Hself ? Hfields_sep Hnodupmems. 
    edestruct Memory.Mem.valid_access_store with (v:=v) as [m']; eauto. 
    exists m'; split*; constructor*.
    unfold compat_self.
    intros.
    destruct* Hself as (? & ? & ? & Hget_self' & Hget_co' & Hmem & ?).
    rewrite Hget_self' in Hget_self; inverts Hget_self.
    rewrite Hget_co' in Hget_co; inverts Hget_co.
    do 3 econstructor; splits*.
    intros x' t' Hin'.
    destruct (AST.ident_eq x' x).
    - subst x'.
      specializes Hnodupmems Hin Hin'; subst t'; clear Hin'.
      specializes Hmem Hin; destruct Hmem as (delta' & Hoffset' & ? & ? & ?).
      rewrite Hoffset' in Hoffset; inverts Hoffset.
      exists delta; splits*.
      + apply* Memory.Mem.store_valid_access_1.
      + intros v' Hfind'.
        apply find_update_field in Hfind'; subst v'.
        split*.
        rewrite Hloadres; apply* Memory.Mem.load_store_same.
    - specializes Hmem Hin'; destruct Hmem as (delta' & Hoffset' & Hmembers' & ? & Hval).
      exists delta'; splits*.
      + apply* Memory.Mem.store_valid_access_1.
      + intros v' Hfind'.
        apply gso_field in Hfind'; auto.
        specializes Hval Hfind'; split*.
        destruct Hval as (Hload).
        rewrite <-Hload; apply* Memory.Mem.load_store_other.          
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

  Remark bind_parameter_temps_exists:
    forall xs vs le,
      length xs = length vs ->
      exists le',
        Clight.bind_parameter_temps xs vs le = Some le'.
  Proof.
    induction xs as [|(x, ty)]; destruct vs; introv Hlengths; try discriminate.
    - exists le; reflexivity.  
    - simpl.
      inverts Hlengths as Hlengths.
      specializes IHxs Hlengths; eauto.
  Qed.

  Remark find_var_aux:
    forall x x' me v v' vs vptr le le',
      find_var x (me, adds (nebase x') (necons v' vs) v_empty) v ->
      Some (Maps.PTree.set x' v' (Maps.PTree.set self_id vptr le)) = Some le' ->
      Maps.PTree.get x le' = Some v.
  Proof.
    introv Find Bind.
    inverts Bind.
    unfold find_var in Find; simpl in *.
    unfold adds in Find; simpl in *.
    destruct (AST.ident_eq x x').
    - subst x.
      apply find_add in Find.
      subst v.
      apply Maps.PTree.gss.
    - rewrite PM.gso, PM.gempty in Find; auto. discriminate.
  Qed.
  
  Remark bind_parameters_temp_implies:
    forall c x me vs v vptr le le',
      find_var x (me, adds (map_fst (c_input c)) vs v_empty) v ->
      Clight.bind_parameter_temps ((self_id, type_of_inst_p c.(c_name)) :: nelist2list c.(c_input))
                                  (vptr :: nelist2list vs) le = Some le' ->
      Maps.PTree.get x le' = Some v.
  Proof.
    admit.
  Qed.
  
  Lemma compat_funcall_pres:
    forall c S' S m o f me vargs vptr vs,
      Datatypes.length (Clight.fn_params f) = Datatypes.length vargs ->
      Clight.fn_params f = (self_id, type_of_inst_p c.(c_name)) :: nelist2list c.(c_input) ->
      match_states_bigbig c S S' ->
      vargs = vptr :: (Nelist.nelist2list vs) ->
      find_inst o S me ->
      exists m_fun e_fun le_fun,
        Clight.alloc_variables tge Clight.empty_env m f.(Clight.fn_vars) e_fun m_fun 
        /\ Clight.bind_parameter_temps f.(Clight.fn_params) vargs (Clight.create_undef_temps f.(Clight.fn_temps))
          = Some le_fun
        /\ match_states_bigbig c (me, adds (map_fst c.(c_input)) vs v_empty) (e_fun, le_fun, m_fun).
  Proof.
    introv Hlengths Hparams MS ? ?.
    forwards (e_fun & m_fun & ?): (alloc_exists f.(Clight.fn_vars) Clight.empty_env m).
    forwards (le_fun & Bind): bind_parameter_temps_exists Hlengths.
    do 3 econstructor; splits*.
    inverts MS.
    constructor*.
    - unfold compat_vars.
      intros x' t' v' ? Hin Hfind.
      subst vargs.
      rewrite Hparams in Bind.
      apply* bind_parameters_temp_implies.

    - unfold compat_self.
      intros.
      destruct* H3; destruct_conjs.
      admit.

    - unfold match_step.
      intros c' Hin.
      specializes H4 Hin.
      destruct_conjs.
      do 2 econstructor; splits*.
      admit.
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
  
  Hint Constructors Clight.eval_lvalue Clight.eval_expr well_formed_stmt.
  Hint Resolve expr_eval_simu Clight.assign_loc_value sem_cast_same.
  Hint Constructors well_formed_stmt.

  Remark ne_Forall2_lengths:
    forall A B (P: A -> B -> Prop) l1 l2,
      Nelist.Forall2 P l1 l2 -> Nelist.length l1 = Nelist.length l2.
  Proof.
    induction l1, l2; introv HForall2; inverts* HForall2.
    simpl; f_equal; apply* IHl1.
  Qed.
  
  Theorem simu_bigbig:
    (forall p S1 s S2,
        stmt_eval p S1 s S2 ->
        sub_prog p prog ->
        (* p = prog -> *)
        forall c,
          In c prog ->
          forall (WF: well_formed_stmt c S1 s)
            e1 le1 m1 
            (MS: match_states_bigbig c S1 (e1, le1, m1)),
          exists le2 m2 t,
            exec_stmt_2 tge e1 le1 m1 (translate_stmt c.(c_name) s)
                        t le2 m2 ClightBigstep.Out_normal
            /\ match_states_bigbig c S2 (e1, le2, m2))
    /\ (forall p me clsid vs me' rv,
          stmt_step_eval p me clsid vs me' rv ->
          sub_prog p prog ->
          (* p = prog -> *)
          forall c S o c' prog' m loc_f f vptr e le,
            (* In c prog -> *)
            In c' prog ->
            well_formed_stmt c' (me, adds (Nelist.map_fst c'.(c_input)) vs v_empty) c'.(c_step) ->
            match_states_bigbig c S (e, le, m) ->
            Globalenvs.Genv.find_symbol tge.(Clight.genv_genv) (step_id clsid) = Some loc_f ->
            Globalenvs.Genv.find_funct_ptr tge.(Clight.genv_genv) loc_f = Some (Clight.Internal f) ->
            find_inst o S me ->
            find_class clsid prog = Some (c', prog') ->
            List.length f.(Clight.fn_params) = 1 + Nelist.length vs ->
            Clight.eval_expr tge e le m (ptr_obj (Some c.(c_name)) clsid o) vptr ->
            exists m' t,
              eval_funcall_2 tge m (Clight.Internal f) (vptr :: nelist2list vs) t m' rv
              /\ match_states_bigbig c (update_inst o S me') (e, le, m')
        ).
  Proof.
    clear TRANSL.
    apply stmt_eval_step_ind;
      [| |introv ? ? ? ? Hifte|introv ? HS1 ? HS2|introv ? Evs ? Hrec_eval|
       |(introv Hfind ? ? Hrec_exec; intros ** MS Hget_loc_f Hget_f ? Hfind' Hlengths ?)];
      intros;
      try inverts WF as; [|introv Hin| | |introv ? Hin Hfind Wfs ? Valids Types| |]; intros;
      inverts MS as Hvars Hself Hstep.

    (* Assign x e : "x = e" *)
    - do 3 econstructor; split*.
      + apply* exec_Sset.
      + apply* compat_assign_pres.
       
    (* AssignSt x e : "self->x = e"*)
    - app_exp_eval_det.
      pose proof Hself as Hself'.
      destruct* Hself' as (? & ? & ? & Hget_self' & Hget_co' & Hmem & ?).
      specializes Hmem Hin; destruct_conjs.
      edestruct compat_stassign_pres; iauto.
      do 3 econstructor; split*.
      apply* exec_Sassign.
      + apply* evall_self_field. 
      + rewrite* type_pres.
        
    (* Ifte e s1 s2 : "if e then s1 else s2" *)
    - edestruct Hifte with (le1:=le1); destruct_conjs; eauto; [destruct* b|]. 
      do 3 econstructor; split*.
      apply* exec_Sifthenelse. 
      + erewrite type_pres, bool_val_ptr; eauto.
      + destruct* b. 
          
    (* Comp s1 s2 : "s1; s2" *)
    - app_stmt_eval_det'.
      edestruct HS1 with (e1:=e1); destruct_conjs; eauto.
      edestruct HS2; destruct_conjs; eauto.
      do 3 econstructor; split*.
      apply* exec_Sseq_1.

    (* Step_ap y ty clsid o [e1; ... ;en] : "y = clsid_step(&(self->o), e1, ..., en)" *)
    - app_exps_eval_det.

      (* app_find_inst_det. *)
      (* app_stmt_step_eval_det. *)
      
      (* get the Clight corresponding function *)
      forwards* Hin': find_class_In Hfind.
      pose proof Hstep as Hstep'.
      edestruct Hstep' as (loc_f & f & ? & ? & ? & Htype_fun & ? & ? & ? & ? & Hlengths & ?); eauto.
      rewrite <-type_pres' with (c:=c) (es:=es) in Htype_fun; auto.
      forwards Eq: find_class_name Hfind.
      rewrite Eq in *; clear Eq.
      
      (* get the Clight corresponding field *)
      pose proof Hself as Hself'.
      destruct* Hself' as (? & loc_struct & ofs & Hget_self' & Hget_co' & Hmem & Hobj).
        auto; clear Hmem.
      specializes Hobj Hin; destruct Hobj as (delta).

      (* recursive funcall evaluation *)
      app_find_inst_det.
      edestruct Hrec_eval with (c:=c) (e:=e1) (m:=m1) (le:=le1); destruct_conjs; eauto.
      + rewrite <-ne_Forall2_lengths with (1:=Evs).
        rewrite Hlengths; simpl; f_equal. rewrite <-nelist2list_length.
        symmetry; apply* ne_Forall2_lengths.        
      + apply Clight.eval_Eaddrof; apply* evall_self_field.
      + do 3 econstructor; split.
        *{ eapply exec_Scall; eauto.
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
        * apply* compat_assign_pres. 

    (* Skip : "skip" *)
    - do 3 econstructor; split*.
      eapply exec_Sskip.

    (* funcall *)
    - (* get the Clight function entry state *)
      forwards* Hfind'': find_class_sub_same Hfind UNIQUE.
      rewrite Hfind' in Hfind''; inverts Hfind''.
      
      (* rewrite Hfind in Hfind'; inverts Hfind'. *)
      destruct Hstep with (c:=cls) as (loc_f' & f' & Hget_loc_f' & ? & Hget_f' & ?); destruct_conjs; eauto.
      forwards Eq: find_class_name Hfind.
      rewrite Eq in Hget_loc_f'; clear Eq.
      rewrite Hget_loc_f' in Hget_loc_f; inverts Hget_loc_f.
      rewrite Hget_f' in Hget_f; inverts Hget_f.

      assert (length f.(Clight.fn_params) = length (vptr :: nelist2list vs))
        by (rewrite Hlengths; simpl; f_equal; rewrite Nelist.nelist2list_length; auto).

      forwards* (m_fun & e_fun & le_fun & ? & ? & ?): (compat_funcall_pres cls).
      + skip.
      + forwards* Hsub: find_class_sub.
        subst env.
        edestruct Hrec_exec with (e1:=e_fun) (le1:=le_fun) (m1:=m_fun); eauto.
        destruct_conjs.
        
        do 2 econstructor; split.
        apply* eval_funcall_internal.
        * rewrite* H12.
        * admit.
        * skip.
        * skip.
  Qed.