Require Import cfrontend.ClightBigstep.
Require Import cfrontend.Clight.
Require Import cfrontend.Ctypes.
Require Import lib.Integers.
Require Import lib.Maps.
Require Import lib.Coqlib.
Require Errors.
Require Import common.Separation.
Require Import common.Values.
Require Import common.Memory.
Require Import common.Events.
Require Import common.Globalenvs.

Require Import Rustre.Common.
Require Import Rustre.RMemory.
Require Import Rustre.Nelist.

Require Import Syn Sem Tra Sep.

Require Import Program.Tactics.
Require Import List.
Import List.ListNotations.
Require Import Coq.ZArith.BinInt.

Open Scope list_scope.
Open Scope sep_scope.
Open Scope Z.

Require Import LibTactics.
Ltac auto_star ::= try solve [eassumption | auto | jauto].

(* SIMULATION *)

Section PRESERVATION.

  Variable main_node : ident.
  Variable prog: program.
  Variable tprog: Clight.program.
   
  (* Let ge := globalenv prog. *)
  Let tge := Clight.globalenv tprog.
  Let gcenv := Clight.genv_cenv tge.
  
  Definition pointer_of_node node := pointer_of (type_of_inst node).

  Hypothesis TRANSL: translate prog main_node = Errors.OK tprog.
  Hypothesis main_node_exists: find_class main_node prog <> None.
  Hypothesis WD: WelldefClasses prog.
  
  (* Hypothesis UNIQUE: unique_classes prog. *)
  
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

  Lemma global_out_struct:
    forall clsnm c prog' f id su m a,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      translate_out c f = Composite id su m a ->
      exists co,
        gcenv ! id = Some co
        /\ co.(co_members) = f.(m_out).
  Admitted.

  Lemma type_pres:
    forall c m e, Clight.typeof (translate_exp c m e) = typeof e.
  Proof.
    induction e as [| |cst]; simpl; auto.
    - case (existsb (fun out : positive * typ => ident_eqb (fst out) i) (m_out m)); auto.
    - destruct cst; simpl; reflexivity.
  Qed.

  Lemma sem_cast_same:
    forall m v t,
      valid_val v t ->
      Cop.sem_cast v t t m = Some v.
  Proof.
    unfold valid_val; intros; destruct_pairs.
    destruct t, v;
      (destruct i, s || destruct f || idtac);
      (discriminates || contradiction || auto).
  Qed.

  Inductive well_formed_exp (c: class) (m: method): exp -> Prop :=
  | wf_var: forall x ty,
      In (x, ty) (meth_vars m) ->
      well_formed_exp c m (Var x ty)
  | wf_state: forall x ty,
      In (x, ty) c.(c_mems) ->
      well_formed_exp c m (State x ty)
  | wf_const: forall cst ty,
      well_formed_exp c m (Const cst ty).

  Inductive well_formed_stmt (c: class) (m: method): stmt -> Prop :=
  | wf_assign: forall x e,
      In (x, typeof e) (meth_vars m) ->
      well_formed_exp c m e ->
      well_formed_stmt c m (Assign x e)
  | wf_assignst: forall x e,
      In (x, typeof e) c.(c_mems) ->
      well_formed_exp c m e ->
      well_formed_stmt c m (AssignSt x e)
  | wf_ite: forall e s1 s2,
      well_formed_exp c m e ->
      well_formed_stmt c m s1 ->
      well_formed_stmt c m s2 ->
      well_formed_stmt c m (Ifte e s1 s2)
  | wf_comp: forall  s1 s2,
      well_formed_stmt c m s1 ->
      well_formed_stmt c m s2 ->
      well_formed_stmt c m (Comp s1 s2)
  | wf_call: forall ys clsid c' prog' o fid f es,
      (* In (y, ty) (class_vars c) -> *)
      (* Nelist.length ys = Nelist.length rvs -> *)
      (* Nelist.Forall (fun y => In y (class_vars c)) ys -> *)
      (* y <> self_id -> *)
      length ys = length f.(m_out) ->
      In (o, clsid) c.(c_objs) ->
      In (o, clsid, fid) (get_instance_methods m.(m_body)) ->
      (* find_class clsid prog = Some (c', prog') -> *)
      Forall (well_formed_exp c m) es ->
      (* Nelist.Forall2 (exp_eval S) es vs -> *)
      (* Nelist.Forall2 (fun e v => valid_val v (typeof e)) es vs -> *)
      Forall2 (fun e x => typeof e = snd x) es f.(m_in) ->
      (* ty = snd c'.(c_output) -> *)
      (* find_inst S o me -> *)
      (* well_formed_stmt c' (me, adds (Nelist.map_fst c'.(c_input)) vs v_empty) m.(m_body) -> *)
      (* stmt_call_eval prog me clsid vs me' rvs -> *)
      (* valid_val rv ty -> *)
      (* ty <> Ctypes.Tvoid -> *)
      find_class clsid prog = Some (c', prog') ->
      find_method fid (c_methods c') = Some f ->
      well_formed_stmt c m (Call ys clsid o fid es)
  | wf_skip: 
      well_formed_stmt c m Skip.
  
   Remark valid_val_access:
    forall v t, valid_val v t -> access_mode t = By_value (chunk_of_type t).
  Proof.
    introv H.
    apply H.
  Qed.

  Hint Resolve valid_val_access.
  Hint Constructors Clight.eval_lvalue Clight.eval_expr well_formed_stmt.

  Definition c_state := (Clight.env * Clight.temp_env * Memory.Mem.mem)%type.

  Definition sep_invariant
             (c: class) (f: method) (S: state) (e: env) (le: temp_env) (m: Mem.mem)
             (sb: block) (sofs: Int.int) (outb: block) (outco: composite) :=
    let (me, ve) := S in
    m |= staterep gcenv prog c.(c_name) me sb (Int.unsigned sofs)
        ** blockrep gcenv ve (co_members outco) outb
        ** sepall (fun ocg =>
                     let '(o, cid, g) := ocg in
                     match gcenv ! (prefix g cid), e!o with 
                     | Some gco, Some (oblk, t) =>
                       if type_eq t (type_of_inst (prefix g cid)) then
                         blockrep gcenv v_empty (co_members gco) oblk
                       else sepfalse
                     | _, _ => sepfalse
                     end) (get_instance_methods f.(m_body))
        ** pure (Forall (fun (xty: ident * typ) =>
                           let (x, ty) := xty in
                           match le ! x with
                           | Some v => match_value ve x v
                           | None => False
                           end) (f.(m_in) ++ f.(m_vars))).
  
  Inductive match_states (c: class) (f: method) (S: state): c_state -> Prop :=
    intro_match_states: forall e le m sb sofs outb outco,
      le ! self_id = Some (Vptr sb sofs) ->
      le ! out_id = Some (Vptr outb Int.zero) ->
      gcenv ! (prefix f.(m_name) c.(c_name)) = Some outco ->
      sep_invariant c f S e le m sb sofs outb outco ->
      (0 <= Int.unsigned sofs)%Z ->
      match_states c f S (e, le, m).

  Hint Constructors match_states.
  
  Remark invariant_blockrep:
    forall c f me ve e le m sb sofs outb outco,
      sep_invariant c f (me, ve) e le m sb sofs outb outco ->
      m |= blockrep gcenv ve (co_members outco) outb.
  Proof.
    introv Hrep.
    now apply sep_pick2 in Hrep.
  Qed.

  Remark existsb_In:
    forall f x ty,
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = true ->
      In (x, ty) (meth_vars f) ->
      In (x, ty) f.(m_out).
  Proof.
    introv E ?.
    apply existsb_exists in E.
    destruct E as ((x' & ty') & Hin & E).
    rewrite ident_eqb_eq in E; simpl in E; subst.
    pose proof (m_nodup f) as Nodup.
    assert (In (x, ty') (meth_vars f)) by
        (now apply in_or_app; right; apply in_or_app; right).
    now app_NoDupMembers_det.
  Qed.

  Remark not_existsb_In:
    forall f x ty,
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = false ->
      In (x, ty) (meth_vars f) ->
      ~ In (x, ty) f.(m_out).
  Proof.
    introv E ?.
    apply not_true_iff_false in E.
    intro Hin; apply E.
    apply existsb_exists.
    exists (x, ty); split*; simpl.
    apply ident_eqb_refl.
  Qed.
  
  Remark output_match:
    forall clsnm prog' c f outco,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      gcenv ! (prefix (m_name f) (c_name c)) = Some outco ->
      f.(m_out) = outco.(co_members).
  Proof.
    introv ? ? Houtco.
    forwards* (outco' & Houtco' & Eq): global_out_struct;
      [unfold translate_out; eauto |].
    rewrite Houtco in Houtco'; inverts* Houtco'.
  Qed.

  Remark staterep_skip:
    forall c clsnm prog' me m sb sofs P,
      find_class clsnm prog = Some (c, prog') ->
      (m |= staterep gcenv prog c.(c_name) me sb (Int.unsigned sofs) ** P <->
      m |= staterep gcenv (c :: prog') c.(c_name) me sb (Int.unsigned sofs) ** P).
  Proof.
    introv Find.
    forwards ?: find_class_name Find; subst.
    forwards (? & Hprog & FindNone): find_class_app Find.
    split; intro Hrep.
    - rewrite Hprog in Hrep.
      rewrite* staterep_skip_app in Hrep.
      intro Hin.
      apply ClassIn_find_class in Hin.
      contradiction.
    - rewrite Hprog.
      rewrite* staterep_skip_app.
      intro Hin.
      apply ClassIn_find_class in Hin.
      contradiction.
  Qed.
  
  Remark invariant_staterep:
    forall c clsnm prog' f me ve e le m sb sofs outb outco,
      sep_invariant c f (me, ve) e le m sb sofs outb outco ->
      find_class clsnm prog = Some (c, prog') ->
      m |= staterep gcenv (c :: prog') c.(c_name) me sb (Int.unsigned sofs).
  Proof.
    introv Hrep Find.
    eapply staterep_skip in Hrep; eauto.
    now apply sep_proj1 in Hrep.
  Qed.
  
  Lemma evall_out_field:
    forall clsnm prog' c f S e le m x ty sb sofs outb outco,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      le ! out_id = Some (Vptr outb Int.zero) ->
      sep_invariant c f S e le m sb sofs outb outco ->
      gcenv ! (prefix (m_name f) (c_name c)) = Some outco ->
      In (x, ty) (meth_vars f) ->
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = true ->
      exists d,
        eval_lvalue tge e le m (deref_field out_id (prefix (m_name f) (c_name c)) x ty)
                    outb (Int.add Int.zero (Int.repr d))
        /\ field_offset gcenv x (co_members outco) = Errors.OK d.
  Proof.
    introv ? ? ? Hrep Houtco ? E.
    (* pick the interesting conjunct *)
    destruct S.
    apply invariant_blockrep in Hrep.

    (* show that (x, ty) ∈ f.(m_out) *)
    eapply existsb_In in E; eauto.

    (* show that (x, ty) ∈ outco.(co_members) *)
    erewrite output_match in E; eauto.  

    forwards* (d & Hoffset): blockrep_field_offset.
    exists d; splits*.
    apply* eval_Efield_struct.
    + apply* eval_Elvalue.
      apply* deref_loc_copy.
    + simpl; unfold type_of_inst; eauto.
  Qed.
       
  Lemma eval_out_field:
    forall clsnm prog' c f S e le m x ty sb sofs outb outco v,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      le ! out_id = Some (Vptr outb Int.zero) ->
      sep_invariant c f S e le m sb sofs outb outco ->
      gcenv ! (prefix (m_name f) (c_name c)) = Some outco ->
      In (x, ty) (meth_vars f) ->
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = true ->
      find_var S x v ->
      eval_expr tge e le m (deref_field out_id (prefix (m_name f) (c_name c)) x ty) v.
  Proof.
    intros.
    destruct S.
    edestruct evall_out_field; eauto.
    apply* eval_Elvalue.
    rewrite Int.add_zero_l.
    apply* blockrep_deref_mem.
    - apply* invariant_blockrep.
    - erewrite <-output_match; eauto.
      apply* existsb_In.
  Qed.

  Lemma eval_temp_var:
    forall clsnm prog' c f S e le m x ty sb sofs outb outco v,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      sep_invariant c f S e le m sb sofs outb outco ->
      In (x, ty) (meth_vars f) ->
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = false ->
      find_var S x v ->
      eval_expr tge e le m (Etempvar x ty) v.
  Proof.
    introv ? ? Hrep Hvars E ?.
    destruct S.
    apply sep_proj2, sep_proj2, sep_comm, sep_pure in Hrep.
    destruct Hrep as (Hrep & H'); clear H'.
    apply eval_Etempvar.
    assert (~ In (x, ty) f.(m_out)) as HnIn.
    * apply not_true_iff_false in E.
      intro Hin; apply E.
      apply existsb_exists.
      exists (x, ty); split*.
      apply ident_eqb_refl. 
    * unfold meth_vars in Hvars.
      rewrite app_assoc in Hvars.
      eapply not_In_app in HnIn; eauto.
      eapply In_Forall in Hrep; eauto.
      simpl in Hrep.
      destruct (le ! x);    
      [now app_match_find_var_det | contradiction].
  Qed.

  Remark field_offset_rec_in_range':
    forall flds x ofs pos,
      field_offset_rec gcenv x flds pos = Errors.OK ofs ->
      (pos <= ofs)%Z.
  Proof.
    induction flds as [|[i t]]; simpl; intros.
    - discriminate.
    - destruct (AST.ident_eq x i); intros.
      + inv H. apply align_le. apply alignof_pos.
      + specializes IHflds H. eapply Zle_trans; eauto.
        apply Zle_trans with (align pos (alignof gcenv t)).
        * apply align_le. apply alignof_pos.
        * generalize (sizeof_pos gcenv t). omega.
  Qed.

  Remark field_offset_in_range':
  forall flds x ofs,
  field_offset gcenv x flds = Errors.OK ofs ->
  (0 <= ofs)%Z.
  Proof.
    unfold field_offset; intros.
    apply* field_offset_rec_in_range'.
  Qed.
  
  Lemma evall_self_field:
    forall clsnm prog' c f S e le m x ty sb sofs outb outco,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      le ! self_id = Some (Vptr sb sofs) ->
      (0 <= Int.unsigned sofs)%Z ->
      sep_invariant c f S e le m sb sofs outb outco ->
      In (x, ty) (c_mems c) ->
      exists d,
        eval_lvalue tge e le m (deref_field self_id (c_name c) x ty)
                    sb (Int.add sofs (Int.repr d))
        /\ field_offset gcenv x (make_members c) = Errors.OK d
        /\ (0 <= d <= Int.max_unsigned)%Z.
  Proof.
    introv Find ? ? ? Hrep Hin.
    destruct S.
    forwards ?: find_class_name Find; subst.
    eapply invariant_staterep in Hrep; eauto.
    forwards* (? & Hco & ? & Eq & ? & ?): make_members_co; instantiate (1:=tprog) in Hco.
    forwards* (d & Hoffset & (Hpos & Hnotmax)): staterep_field_offset. 
    exists d; splits*.
    - apply* eval_Efield_struct.
      + apply* eval_Elvalue.
        apply* deref_loc_copy. 
      + simpl; unfold type_of_inst; eauto.
      + rewrite* Eq. 
    - apply* field_offset_in_range'.
    - rewrite Z.add_comm in Hnotmax.
      rewrite <-Z.add_0_r in Hnotmax. 
      apply Z.le_le_add_le with (m:=Int.unsigned sofs) (n:=Z0); auto.
  Qed.
  
  Lemma eval_self_field:
    forall clsnm prog' c f S e le m x ty sb sofs outb outco v,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      le ! self_id = Some (Vptr sb sofs) ->
      (0 <= Int.unsigned sofs)%Z ->
      sep_invariant c f S e le m sb sofs outb outco ->
      In (x, ty) (c_mems c) ->
      find_field S x v ->
      valid_val v ty ->
      eval_expr tge e le m (deref_field self_id (c_name c) x ty) v.
  Proof.
    introv ? ? ? ? Hrep ? ? ?.
    destruct S.
    edestruct evall_self_field as (? & ? & Hoffset & (? & ?)); eauto.
    eapply invariant_staterep in Hrep; eauto.
    apply* eval_Elvalue.
    apply* staterep_deref_mem.
    rewrite* Int.unsigned_repr.
  Qed.
  
  Lemma expr_eval_simu:
    forall c S exp clsnm prog' v e le m f,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      match_states c f S (e, le , m) ->
      well_formed_exp c f exp ->
      exp_eval S exp v ->
      Clight.eval_expr tge e le m (translate_exp c f exp) v.
  Proof.
    intros c S exp; induction exp as [x ty| |cst];
    introv Find Hf MS WF EV;
    inverts EV; inverts MS as Hself Hout Houtco Hrep.

    (* Var x ty : "x" *)
    - inverts WF as Hvars.
      simpl.
      destruct (existsb (fun out => ident_eqb (fst out) x) f.(m_out)) eqn: E.
      + apply* eval_out_field.
      + apply* eval_temp_var.
        
    (* State x ty : "self->x" *)
    - inverts WF.
      simpl.
      apply* eval_self_field.

    (* Const c ty : "c" *)
    - destruct cst; constructor.
  Qed.

  Lemma exp_eval_valid:
    forall S e v,
      exp_eval S e v -> valid_val v (typeof e).
  Proof.
    induction 1; auto.
  Qed.

  Lemma exp_eval_access:
    forall S e v,
      exp_eval S e v -> access_mode (typeof e) = By_value (chunk_of_type (typeof e)).
  Proof.
    introv H.
    apply exp_eval_valid in H.
    apply H.
  Qed.

  Lemma exp_eval_lr:
    forall S e v,
      exp_eval S e v -> v = Val.load_result (chunk_of_type (typeof e)) v.
  Proof.
    introv H.
    apply exp_eval_valid in H.
    apply H.
  Qed.

  Hint Resolve exp_eval_valid exp_eval_access exp_eval_lr.

  Lemma exprs_eval_simu:
    forall c S es es' prog' clsnm vs e le m f,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      match_states c f S (e, le , m) ->
      Forall (well_formed_exp c f) es ->
      Forall2 (exp_eval S) es vs ->
      es' = map (translate_exp c f) es ->
      Clight.eval_exprlist tge e le m es'
                           (list_type_to_typelist (map Clight.typeof es')) vs.
  Proof.
    Hint Constructors Clight.eval_exprlist.
    introv Find Hin MS WF EV ?; subst es';
      induction EV; inverts WF; econstructor;
    (apply* expr_eval_simu || (rewrite type_pres; apply* sem_cast_same) || eauto).
  Qed.

  Remark eval_exprlist_app:
    forall e le m es es' vs vs',
      Clight.eval_exprlist tge e le m es
                           (list_type_to_typelist (map Clight.typeof es)) vs ->
      Clight.eval_exprlist tge e le m es'
                           (list_type_to_typelist (map Clight.typeof es')) vs' ->
      Clight.eval_exprlist tge e le m (es ++ es')
                           (list_type_to_typelist (map Clight.typeof (es ++ es'))) (vs ++ vs').
  Proof.
    induction es; introv Ev Ev'; inverts* Ev.
    repeat rewrite <-app_comm_cons.
    simpl; econstructor; eauto.
  Qed.

  Lemma match_states_assign_out:
    forall c clsnm prog' f S x ty e le m v d sb sofs outco outb,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      le ! out_id = Some (Vptr outb Int.zero) ->
      le ! self_id = Some (Vptr sb sofs) ->
      gcenv ! (prefix (m_name f) (c_name c)) = Some outco ->
      (0 <= Int.unsigned sofs)%Z ->
      sep_invariant c f S e le m sb sofs outb outco ->
      In (x, ty) (meth_vars f) ->
      field_offset gcenv x (co_members outco) = Errors.OK d ->
      access_mode ty = By_value (chunk_of_type ty) ->
      v = Values.Val.load_result (chunk_of_type ty) v ->
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = true ->
      exists m', Memory.Mem.storev (chunk_of_type ty) m (Vptr outb (Int.repr d)) v = Some m'
            /\ match_states c f (update_var S x v) (e, le, m').
  Proof.
    intros **  ? ? ? ? Houtco ? Hrep Hvars Hoffset Haccess Hlr E.
    destruct S.
    unfold sep_invariant in Hrep.

    eapply existsb_In in E; eauto.
    forwards* Eq: output_match.
    pose proof E as Hin; rewrite Eq in Hin.
    pose proof (m_nodup f) as Nodup.
    
    (* get the updated memory *)
    apply sepall_in in Hin.
    destruct Hin as [ws [ys [Hys Heq]]].
    unfold blockrep at 1 in Hrep.
    rewrite Heq in Hrep.
    rewrite Hoffset, Haccess in Hrep.
    rewrite sep_assoc, sep_swap in Hrep.
    eapply Separation.storev_rule' with (v:=v) in Hrep; eauto.
    destruct Hrep as (m' & ? & Hrep).
    exists m'; split*.
    unfold update_var; simpl.
    econstructor; eauto.
    unfold sep_invariant.
    unfold blockrep at 1.
    rewrite Heq.
    rewrite Hoffset, Haccess.
    rewrite sep_assoc, sep_swap.
    do 3 rewrite <-sep_assoc; rewrite sep_comm;
    rewrite sep_pure; do 2 rewrite sep_assoc.
    do 3 rewrite <-sep_assoc in Hrep; rewrite sep_comm in Hrep;
    rewrite sep_pure in Hrep; do 2 rewrite sep_assoc in Hrep.
    destruct Hrep as (Hpure & Hrep); split.
    - clear Hrep.
      rewrite app_assoc in Nodup.
      rewrite NoDupMembers_app in Nodup.
      apply In_InMembers in E.
      eapply NoDupMembers_app_InMembers in Nodup; eauto.
      induction* (m_in f ++ m_vars f).
      inverts* Hpure; constructor; destruct a.
      + destruct* le ! i.
        rewrite* match_value_add.
        intro.
        apply Nodup.
        subst i.
        now left.
      + apply* IHl.
        intro.
        apply Nodup.
        now right.
    - eapply sep_imp; eauto.
      + unfold hasvalue.
        unfold match_value; simpl.
        rewrite PM.gss.
        rewrite <-Hlr; auto.
      + apply* sep_imp'.
        apply* sep_imp'.
        do 2 apply NoDupMembers_app_r in Nodup.
        rewrite Eq, Hys in Nodup.
        apply NoDupMembers_app_cons in Nodup.
        destruct Nodup as (Notin & Nodup).
        rewrite sepall_switchp with
        (f' := fun xty : ident * type =>
                 let (x0, ty0) := xty in
                 match field_offset gcenv x0 (co_members outco) with
                 | Errors.OK d0 =>
                   match access_mode ty0 with
                   | By_value chunk => contains chunk outb d0 (match_value (PM.add x v v0) x0)
                   | By_reference => sepfalse
                   | By_copy => sepfalse
                   | By_nothing => sepfalse
                   end
                 | Errors.Error _ => sepfalse
                 end); auto.
        * apply NoDupMembers_NoDup; iauto.
        * intros (x' & t') Hin.
          rewrite* match_value_add.
          intro; subst x'.
          apply Notin.
          eapply In_InMembers; eauto.
  Qed.
  
  Lemma match_states_assign_tempvar:
    forall c clsnm prog' f S x ty e le m v sb sofs outco outb,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      x <> self_id ->
      x <> out_id ->
      le ! out_id = Some (Vptr outb Int.zero) ->
      le ! self_id = Some (Vptr sb sofs) ->
      gcenv ! (prefix (m_name f) (c_name c)) = Some outco ->
      (0 <= Int.unsigned sofs)%Z ->
      sep_invariant c f S e le m sb sofs outb outco ->
      In (x, ty) (meth_vars f) ->
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = false ->
      match_states c f (update_var S x v) (e, PTree.set x v le, m).
  Proof.
    intros ** ? ? ? ? Hout Hself ? ? Hrep Hin E.
    rewrite <-PTree.gso with (j:=x) (x:=v) in Hout; auto.
    rewrite <-PTree.gso with (j:=x) (x:=v) in Hself; auto.
    eapply not_existsb_In in E; eauto.
    pose proof (m_nodup f) as Nodup.
    destruct S.
    unfold update_var; simpl.
    econstructor; eauto.
    unfold sep_invariant in *.
    do 2 rewrite <-sep_assoc; rewrite sep_comm;
    rewrite sep_pure; rewrite sep_assoc.
    do 2 rewrite <-sep_assoc in Hrep; rewrite sep_comm in Hrep;
    rewrite sep_pure in Hrep; rewrite sep_assoc in Hrep.
    destruct Hrep as (Hpure & Hrep); split.
    - clear Hrep.
      induction* (m_in f ++ m_vars f).
      inverts* Hpure; constructor; destruct a as (x' & t').
      + destruct (ident_eqb x' x) eqn: Eq.
        * apply ident_eqb_eq in Eq.
          subst x'.
          rewrite PTree.gss.
          unfold match_value.
          rewrite* PM.gss.
        * apply ident_eqb_neq in Eq.
          rewrite* PTree.gso.
          rewrite* match_value_add.
      + apply* IHl.
    - eapply sep_imp; eauto.
      eapply sep_imp'; eauto.
      + do 2 apply NoDupMembers_app_r in Nodup.
        forwards* Eq:output_match; rewrite Eq in Nodup. 
        unfold blockrep.
        rewrite sepall_switchp with
        (f' := fun xty : ident * type =>
                 let (x0, ty0) := xty in
                 match field_offset gcenv x0 (co_members outco) with
                 | Errors.OK d0 =>
                   match access_mode ty0 with
                   | By_value chunk => contains chunk outb d0 (match_value (PM.add x v v0) x0)
                   | By_reference => sepfalse
                   | By_copy => sepfalse
                   | By_nothing => sepfalse
                   end
                 | Errors.Error _ => sepfalse
                 end); auto.
        * apply NoDupMembers_NoDup; iauto.
        * intros (x' & t') Hin'.
          rewrite* match_value_add.
          intro; subst x'.
          assert (In (x, t') (meth_vars f)) by
              (apply in_or_app; right; apply in_or_app; right; rewrite* Eq).
          pose proof (nodup_vars f); app_NoDupMembers_det.
          apply E. 
          rewrite* Eq.
  Qed.  

  Lemma match_states_assign_state:
    forall c clsnm prog' f S x ty e le m v d sb sofs outco outb, 
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      le ! out_id = Some (Vptr outb Int.zero) ->
      le ! self_id = Some (Vptr sb sofs) ->
      gcenv ! (prefix (m_name f) (c_name c)) = Some outco ->
      (0 <= Int.unsigned sofs)%Z ->
      sep_invariant c f S e le m sb sofs outb outco ->
      In (x, ty) (c_mems c) ->
      field_offset gcenv x (make_members c) = Errors.OK d ->
      v = Values.Val.load_result (chunk_of_type ty) v ->
      exists m', Memory.Mem.storev (chunk_of_type ty) m (Vptr sb (Int.repr (Int.unsigned sofs + d))) v = Some m'
            /\ match_states c f (update_field S x v) (e, le, m').
  Proof.
    intros **  ? ? ? ? Houtco ? Hrep Hmems Hoffset Hlr.
    destruct S.
    unfold sep_invariant in Hrep.
    
    (* get the updated memory *)
    apply sepall_in in Hmems.
    destruct Hmems as [ws [ys [Hys Heq]]].
    eapply staterep_skip in Hrep; eauto.
    simpl staterep in Hrep.
    rewrite ident_eqb_refl in Hrep.
    rewrite Heq in Hrep.
    rewrite Hoffset in Hrep.
    do 2 rewrite sep_assoc in Hrep.
    eapply Separation.storev_rule' with (v:=v) in Hrep; eauto.
    destruct Hrep as (m' & ? & Hrep).
    exists m'; split*.
    unfold update_field; simpl.
    econstructor; eauto.
    unfold sep_invariant.
    eapply staterep_skip; eauto.
    simpl staterep.
    rewrite ident_eqb_refl.
    rewrite Heq.
    rewrite Hoffset.
    do 2 rewrite sep_assoc.
    eapply sep_imp; eauto.
    + unfold hasvalue.
      unfold match_value; simpl.
      rewrite PM.gss.
      rewrite <-Hlr; auto.
    + apply* sep_imp'.
      pose proof (c_nodupmems c) as Nodup.
      rewrite Hys in Nodup.
      apply NoDupMembers_app_cons in Nodup.
      destruct Nodup as (Notin & Nodup).        
      rewrite sepall_switchp with
      (f' := fun xty : ident * typ =>
               let (x0, ty0) := xty in
               match field_offset gcenv x0 (make_members c) with
               | Errors.OK d0 =>
                 contains (chunk_of_type ty0) sb (Int.unsigned sofs + d0)
                          (match_value (PM.add x v (mm_values m0)) x0)
               | Errors.Error _ => sepfalse
               end); auto.
      * apply NoDupMembers_NoDup; iauto.
      * intros (x' & t') Hin.
        rewrite* match_value_add.
        intro; subst x'.
        apply Notin.
        eapply In_InMembers; eauto.
  Qed.

  (* Remark alloc_exists: *) 
  (*   forall vars e m, *) 
  (*     exists e' m', *) 
  (*       Clight.alloc_variables tge e m vars e' m'. *) 
  (* Proof. *) 
  (*   induction vars as [|(x, ty)]. *) 
  (*   - do 3 econstructor. *) 
  (*   - intros. *) 
  (*     destruct (Memory.Mem.alloc m 0 (Ctypes.sizeof (Clight.genv_cenv tge) ty)) eqn: Eq. *) 
  (*     specialize (IHvars (Maps.PTree.set x (b, ty) e) m0). *) 
  (*     destruct* IHvars as (? & ? & ?). *) 
  (*     do 3 econstructor; eauto. *) 
  (* Qed. *) 
 
  (* Remark assign_loc_exists: *) 
  (*   forall v ty m loc, *) 
  (*     Ctypes.access_mode ty = Ctypes.By_value (chunk_of_type ty) -> *) 
  (*     Memory.Mem.valid_access m (chunk_of_type ty) loc 0 Memtype.Writable -> *) 
  (*     exists m', *) 
  (*       Clight.assign_loc tge.(Clight.genv_cenv) ty m loc Int.zero v m'. *) 
  (* Proof. *) 
  (*   introv ? Hvalid. *) 
  (*   forwards (? & ?): Memory.Mem.valid_access_store Hvalid. *) 
  (*   do 2 econstructor; eauto. *) 
  (* Qed. *) 
   
  (* Remark bind_parameters_exists: *) 
  (*   forall xs vs e m, *) 
  (*     length xs = length vs -> *) 
  (*     Forall (fun x => exists loc, *) 
  (*                 Maps.PTree.get (fst x) e = Some (loc, snd x) *) 
  (*                 /\ Memory.Mem.valid_access m (chunk_of_type (snd x)) loc 0 Memtype.Writable *) 
  (*                 /\ Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_type (snd x))) xs -> *) 
  (*     exists m', *) 
  (*       Clight.bind_parameters tge e m xs vs m'. *) 
  (* Proof. *) 
  (*   induction xs as [|(x, ty)]; destruct vs; introv Hlengths Hparams; try discriminate. *) 
  (*   - do 2 econstructor. *) 
  (*   - inverts Hparams as (? & ? & Hvalid & Haccess) Hparams.   *) 
  (*     forwards (m' & Hassign): (assign_loc_exists v) Haccess Hvalid. *) 
  (*     edestruct IHxs with (m:=m') (e:=e); eauto. *) 
  (*     + inversion_clear Hassign as [|? ? ? ? Haccess']. *) 
  (*       *{ clear IHxs Hlengths. induction xs. *) 
  (*          - constructor. *) 
  (*          - inverts Hparams as (loc & ?). *) 
  (*            constructor. *) 
  (*            + exists loc; splits*. *) 
  (*              apply* Memory.Mem.store_valid_access_1. *) 
  (*            + apply* IHxs. *) 
  (*        } *) 
  (*       * rewrite Haccess' in Haccess; discriminate. *) 
  (*     + do 2 econstructor; eauto.  *) 
  (* Qed. *) 
 
  (* Remark alloc_variables_implies: *) 
  (*   forall vars e m e' m',  *) 
  (*     Clight.alloc_variables tge e m vars e' m' -> *) 
  (*     Forall (fun x => Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_type (snd x))) vars -> *) 
  (*     Forall (fun x => exists loc, *) 
  (*                 Maps.PTree.get (fst x) e' = Some (loc, snd x) *) 
  (*                 /\ Memory.Mem.valid_access m' (chunk_of_type (snd x)) loc 0 Memtype.Writable *) 
  (*                 /\ Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_type (snd x))) vars. *) 
  (* Proof. *) 
  (*   induction vars. *) 
  (*   - constructor. *) 
  (*   - introv Halloc Hforall. *) 
  (*     inverts Halloc. *) 
  (*     constructor. *) 
  (*     + exists b1; splits*. *) 
  (*       * admit. *) 
  (*       *{ assert (Memory.Mem.valid_access m1 (chunk_of_type (snd (id, ty))) b1 0 Memtype.Writable). *) 
  (*          - eapply Memory.Mem.valid_access_freeable_any. *) 
  (*            apply* Memory.Mem.valid_access_alloc_same. *) 
  (*            + omega. *) 
  (*            + simpl. admit. *) 
  (*            + eapply BinInt.Z.divide_0_r. *) 
  (*          - admit. *) 
  (*        } *) 
  (*       * inverts* Hforall. *) 
  (*     + apply* IHvars. *) 
  (*       inverts* Hforall. *) 
  (* Qed. *) 
 
  (* Remark forall_app: *) 
  (*   forall A (P: A -> Prop) l1 l2, *) 
  (*     Forall P (l1 ++ l2) -> Forall P l1 /\ Forall P l2. *) 
  (* Proof. *) 
  (*   introv HForall; split; rewrite Forall_forall in *; introv Hin; *) 
  (*   apply HForall; apply in_or_app; [left | right]; auto. *) 
  (* Qed. *) 
 
  (* Lemma compat_funcall_pres: *) 
  (*   forall m f vargs, *) 
  (*     Datatypes.length (Clight.fn_params f) = Datatypes.length vargs -> *) 
  (*     Forall (fun x => Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_type (snd x))) (f.(Clight.fn_params) ++ f.(Clight.fn_vars)) -> *) 
  (*     exists m1 e_fun m2, *) 
  (*       Clight.alloc_variables tge Clight.empty_env m (f.(Clight.fn_params) ++ f.(Clight.fn_vars)) e_fun m1  *) 
  (*       /\ Clight.bind_parameters tge e_fun m1 f.(Clight.fn_params) vargs m2. *) 
  (* Proof. *) 
  (*   introv Hlengths Haccesses. *) 
  (*   forwards (e_fun & m1 & Halloc): *) 
  (*     (alloc_exists (f.(Clight.fn_params) ++ f.(Clight.fn_vars)) Clight.empty_env m). *) 
  (*   exists m1 e_fun. *) 
  (*   forwards* Hforall': alloc_variables_implies Halloc Haccesses. *) 
  (*   forwards (Hforall & H'): forall_app Hforall'; clear Hforall' H'. *) 
  (*   forwards* (m2 & ?): bind_parameters_exists Hlengths Hforall. *) 
  (* Qed. *)
  
  (* Hint Constructors Clight.eval_lvalue Clight.eval_expr well_formed_stmt. *)
  Hint Resolve expr_eval_simu Clight.assign_loc_value exp_eval_valid sem_cast_same.

  Lemma methods_corres:
    forall c clsnm prog' mid m (e: Clight.env),
      find_class clsnm prog = Some (c, prog') ->
      find_method mid c.(c_methods) = Some m ->
      exists loc_f f,
        Genv.find_symbol tge mid = Some loc_f
        /\ e ! mid = None
        /\ Genv.find_funct_ptr tge loc_f = Some (Internal f)
        /\ type_of_function f =
          Tfunction
            (Ctypes.Tcons (type_of_inst_p c.(c_name))
                          (Ctypes.Tcons (type_of_inst_p (prefix m.(m_name) c.(c_name)))
                                        (list_type_to_typelist (map snd m.(m_in)))))
            Tvoid AST.cc_default
  (* /\ type_of_fundef (Internal f) = *)
        (*   Tfunction (Ctypes.Tcons (type_of_inst_p c.(c_name)) *)
        (*                           (Ctypes.Tcons (type_of_inst_p (prefix m.(m_name) c.(c_name))) *)
        (*                                         (list_type_to_typelist (map snd m.(m_in))))) *)
        (*             Tvoid AST.cc_default *)
        (* /\ Coqlib.list_norepet (Clight.var_names (Clight.fn_params f) ++ Clight.var_names (Clight.fn_vars f)) *)
        (* /\ Clight.fn_body f = snd (translate_stmt c.(c_name) c.(c_step)) *)
        (* /\ length f.(Clight.fn_params) = 1 + Nelist.length c.(c_input) *)
        (* /\ Forall (fun x => Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_type (snd x))) *)
        (*          (f.(Clight.fn_params) ++ f.(Clight.fn_vars)) *).
  Admitted.
  
  Lemma eval_self_inst:
    forall clsnm prog' c f S e le m o c' sb sofs outb outco,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      le ! self_id = Some (Vptr sb sofs) ->
      sep_invariant c f S e le m sb sofs outb outco ->
      In (o, c') (c_objs c) ->
      exists d,
        eval_expr tge e le m (ptr_obj c.(c_name) c' o) (Vptr sb (Int.add sofs (Int.repr d))).
  Proof.
    introv Find ? ? Hrep Hin.
    destruct S.
    forwards ?: find_class_name Find; subst.
    eapply invariant_staterep in Hrep; eauto.
    forwards* (? & Hco & ? & Eq & ? & ?): make_members_co; instantiate (1:=tprog) in Hco.
    forwards* (d & Hoffset): staterep_inst_offset. 
    exists d.
    apply eval_Eaddrof.
    apply* eval_Efield_struct.
    - apply* eval_Elvalue.
      apply* deref_loc_copy. 
    - simpl; unfold type_of_inst; eauto.
    - rewrite* Eq. 
  Qed.

  Lemma evall_out_struct:
    forall clsnm prog' c f f' S e le m o ty c' sb sofs outb outco,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      le ! self_id = Some (Vptr sb sofs) ->
      sep_invariant c f S e le m sb sofs outb outco ->
      In (o, c', f') (get_instance_methods f.(m_body)) ->
      ty = type_of_inst (prefix f' c') ->
      exists b,
        eval_lvalue tge e le m (Evar o ty) b Int.zero.
  Proof.
    introv Find ? ? Hrep Hin ?; subst.
    destruct S.
    forwards ?: find_class_name Find; subst.
    apply sep_pick3 in Hrep.
    apply sepall_in in Hin; destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hrep. clear Hsplit Hin.
    apply sep_proj1 in Hrep.
    clear ws xs.
    destruct gcenv ! (prefix f' c'); [|contradict Hrep].
    destruct e ! o eqn: E; [|contradict Hrep].
    destruct p as (oblk, t).
    destruct (type_eq t (type_of_inst (prefix f' c'))); [|contradict Hrep].
    subst.
    exists oblk.
    apply* eval_Evar_local.
  Qed.  

  Remark type_pres':
    forall f c caller es,
      Forall2 (fun e x => typeof e = snd x) es f.(m_in) ->
      map snd f.(m_in) = map Clight.typeof (map (translate_exp c caller) es).
  Proof.
    intro f.
    induction (m_in f); introv Heq; inversion_clear Heq as [|? ? ? ? Ht]; simpl; auto.
    f_equal.
    - rewrite <-Ht.
      rewrite* type_pres.
    - apply* IHl.
  Qed.

  (* Lemma exec_assign: *)
  (*   forall e1 le1 m1 clsnm prog' c S f x e v sb sofs outb outco, *)
  (*     find_class clsnm prog = Some (c, prog') -> *)
  (*     In f c.(c_methods) -> *)
  (*     well_formed_exp c f e -> *)
  (*     In (x, typeof e) (meth_vars f) -> *)
  (*     le1 ! self_id = Some (Vptr sb sofs) -> *)
  (*     (0 <= Int.unsigned sofs)%Z -> *)
  (*     le1 ! out_id = Some (Vptr outb Int.zero) -> *)
  (*     gcenv ! (prefix f.(m_name) c.(c_name)) = Some outco -> *)
  (*     sep_invariant c f S e1 le1 m1 sb sofs outb outco -> *)
  (*     exp_eval S e v -> *)
  (*     exists le2 m2 T, *)
  (*       exec_stmt tge (function_entry2 tge) e1 le1 m1 *)
  (*                 (translate_stmt prog c f (Assign x e)) T le2 m2 Out_normal *)
  (*       /\ match_states c f (update_var S x v) (e1, le2, m2). *)
  (* Proof. *)
  (*   introv ? ? ? Hvars; intros. *)
  (*   simpl. *)
  (*   simpl; unfold assign. *)
  (*   destruct (existsb (fun out => ident_eqb (fst out) x) f.(m_out)) eqn: E. *)
    
  (*   (* out->x = e *) *)
  (*   - (* get the 'out' variable left value evaluation *) *)
  (*     edestruct evall_out_field; eauto. *)
      
  (*     (* get the updated memory *) *)
  (*     edestruct match_states_assign_out as (m2 & ?); jauto. *)
        
  (*     exists le1 m2 E0; split*. *)
  (*     apply* ClightBigstep.exec_Sassign. *)
  (*     + rewrite* type_pres; apply* sem_cast_same; apply* exp_eval_valid. *)
  (*     + apply* assign_loc_value. *)
  (*       * simpl; apply* exp_eval_access. *)
  (*       * rewrite* Int.add_zero_l. *)
          
  (*   (* x = e *) *)
  (*   - exists (PTree.set x v le1) m1 E0; split. *)
  (*     + apply* ClightBigstep.exec_Sset. *)
  (*     + pose proof (m_out_id f); pose proof (m_self_id f). *)
  (*       apply* match_states_assign_tempvar; *)
  (*         apply In_InMembers in Hvars; eapply InMembers_neq; eauto. *)
  (* Qed. *)
  
  Lemma exec_funcall_assign:
    forall callee caller ys e1 le1 m1 c prog' c' prog'' o f clsid S sb sofs outb outco instco,  
      find_class c.(c_name) prog = Some (c, prog') ->
      In caller c.(c_methods) ->
      find_class clsid prog = Some (c', prog'') ->
      find_method f c'.(c_methods) = Some callee ->
      gcenv ! (prefix f clsid) = Some instco ->
      In (o, clsid, f) (get_instance_methods caller.(m_body)) ->
      length ys = length callee.(m_out) ->
      Forall (fun y => In y (meth_vars caller)) ys ->
      le1 ! out_id = Some (Vptr outb Int.zero) ->
      le1 ! self_id = Some (Vptr sb sofs) ->
      sep_invariant c caller S e1 le1 m1 sb sofs outb outco ->
      gcenv ! (prefix caller.(m_name) c.(c_name)) = Some outco ->
      exists le2 m2 T,
        exec_stmt tge (function_entry2 tge) e1 le1 m1
                  (funcall_assign ys c.(c_name) caller o (type_of_inst (prefix f clsid)) callee)
                  T le2 m2 Out_normal.
  Proof.
    unfold funcall_assign.
    introv Findc ? ? ? Hinstco ? Length Hforall; intros.
    revert le1 m1 H3 H4 H5 ys Hforall Length.
    induction (m_out callee); introv Hforall Length;    
    destruct ys; simpl in *; try discriminate.
    - exists le1 m1 E0; apply exec_Sskip.
    - destruct p as (y, ty); destruct a as (y', ty').
      inverts Length.
      inverts Hforall.
      (* forwards Eq: find_class_name Findc. *)
      (* forwards Eq': find_method_name Findmeth. *)
      (* edestruct IHl as (? & ? & ? & ?); eauto. *)
      (* clear IHl. *)
      (* unfold assign. *)
      (* destruct (existsb (fun out => ident_eqb (fst out) y) caller.(m_out)) eqn: E. *)

      (* (* out->y = o.y' *) *)
      (* + (* get the 'out' variable left value evaluation *) *)
      (*   forwards* (? & ? & ?): evall_out_field Findc. *)

      (*   (* get the o struct left value evaluation *) *)
      (*   forwards* (? & ?): evall_out_struct Findc. *)

      (*   do 3 econstructor. *)
      (*   apply* exec_Sseq_1. *)
      (*   apply* ClightBigstep.exec_Sassign. *)
      (*   *{ apply* eval_Elvalue. *)
      (*      - eapply eval_Efield_struct. *)
      (*        + apply* eval_Elvalue. *)
      (*          apply* deref_loc_copy. *)
      (*        + unfold type_of_inst; simpl; eauto.   *)
      (*        + eauto. *)
      (*        + skip. *)
      (*      - apply* deref_loc_value. *)
      (*        + simpl. skip. *)
      (*        + skip. *)
      (*    } *)
      (*   * simpl; apply* sem_cast_same. skip. *)
      (*   *{ apply* assign_loc_value. *)
      (*      - simpl. skip. *)
      (*      - rewrite Int.add_zero_l. *)
      (*        skip. *)
      (*    } *)

      (* (* x = e *) *)
      (* + do 3 econstructor. *)
      (*   apply* exec_Sseq_1. *)
      (*   apply* ClightBigstep.exec_Sset. *)
      (*   * pose proof (m_out_id f); pose proof (m_self_id f). *)
      (*     apply* match_states_assign_tempvar;  *)
      (*       apply In_InMembers in Hvars; eapply InMembers_neq; eauto. *)
Admitted.
  
  Theorem correctness:
    (forall p S1 s S2,
        stmt_eval p S1 s S2 ->
        sub_prog p prog ->
        forall c prog' f
          (WF: well_formed_stmt c f s)
          (Find: find_class c.(c_name) prog = Some (c, prog'))
          (Hf: In f c.(c_methods)),
        forall e1 le1 m1
          (MS: match_states c f S1 (e1, le1, m1)),
        exists le2 m2 T,
          exec_stmt tge (function_entry2 tge) e1 le1 m1
                    (translate_stmt prog c f s) T le2 m2 Out_normal
          /\ match_states c f S2 (e1, le2, m2))
    /\
    (forall p me1 clsid fid vs me2 rvs,
        stmt_call_eval p me1 clsid fid vs me2 rvs ->
        sub_prog p prog ->
        forall c caller S e1 le1 m1 o f ptr_f sb o_ofs outb oty
          (MS: match_states c caller S (e1, le1, m1)),
          Globalenvs.Genv.find_symbol tge fid = Some ptr_f ->
          Globalenvs.Genv.find_funct_ptr tge ptr_f = Some (Ctypes.Internal f) ->
          find_inst S o me1 ->
          oty = type_of_inst (prefix fid clsid) ->
          eval_expr tge e1 le1 m1 (ptr_obj c.(c_name) clsid o) (Vptr sb o_ofs) ->
          eval_expr tge e1 le1 m1 (Eaddrof (Evar o oty) (pointer_of oty)) (Vptr outb Int.zero) ->
          exists m2 T,
            eval_funcall tge (function_entry2 tge) m1 (Internal f)
                         ((Vptr sb o_ofs) :: (Vptr outb Int.zero) :: vs) T m2 Vundef
            /\ match_states c caller (update_inst S o me2) (e1, le1, m2)).
  Proof.
    clear TRANSL main_node_exists.
    apply stmt_eval_call_ind;
      [| |introv ? ? ? ? Hifte|introv ? HS1 ? HS2|introv ? Evs ? Hrec_eval|
       |introv Find ? ? Hrec_exec];
      intros;
      try inversion_clear WF as [? ? Hvars|? ? Hin| | |? ? ? ? ? ? ? ? ? ? ? ? ? Find' Findmeth|];
      pose proof MS as MS'; inverts MS' as Hself Hout Houtco Hrep.
    
    (* Assign x e : "x = e" *)
    - simpl; unfold assign.
      destruct (existsb (fun out => ident_eqb (fst out) x) f.(m_out)) eqn: E.

      (* out->x = e *)
      + (* get the 'out' variable left value evaluation *)
        edestruct evall_out_field; eauto.

        (* get the updated memory *)
        edestruct match_states_assign_out as (m2 & ?); jauto.

        exists le1 m2 E0; split*.
        apply* ClightBigstep.exec_Sassign.
        * rewrite* type_pres; apply* sem_cast_same; apply* exp_eval_valid.
        *{ apply* assign_loc_value.
           - simpl; apply* exp_eval_access.
           - rewrite* Int.add_zero_l.
         }

      (* x = e *)
      + exists (PTree.set x v le1) m1 E0; split.
        * apply* ClightBigstep.exec_Sset.
        * pose proof (m_out_id f); pose proof (m_self_id f).
          apply* match_states_assign_tempvar; 
            apply In_InMembers in Hvars; eapply InMembers_neq; eauto.

    (* AssignSt x e : "self->x = e"*)
    - (* get the 'self' variable left value evaluation *)
      edestruct evall_self_field as (? & ? & Hoffset & ?); eauto.

      (* get the updated memory *)
      edestruct match_states_assign_state as (m2 & ?); jauto.
      
      exists le1 m2 E0; split*.
      apply* ClightBigstep.exec_Sassign.
      + rewrite* type_pres; apply* sem_cast_same; apply* exp_eval_valid.
      + apply* assign_loc_value.
        * simpl; apply* exp_eval_access.
        * unfold Int.add.
          rewrite* Int.unsigned_repr.
      
    (* Ifte e s1 s2 : "if e then s1 else s2" *)
    - edestruct Hifte; destruct_conjs; eauto; [destruct* b|]. 
      do 3 econstructor; split*.
      apply* exec_Sifthenelse.
      + erewrite type_pres, bool_val_ptr; eauto.
      + destruct* b.
      
    (* Comp s1 s2 : "s1; s2" *)
    - edestruct HS1; destruct_conjs; eauto.
      edestruct HS2; destruct_conjs; eauto.
      do 3 econstructor; split*.
      apply* exec_Sseq_1.
      
    (* Step_ap y ty clsid o [e1; ... ;en] : "y = clsid_step(&(self->o), e1, ..., en)" *)
    - (* get the Clight corresponding function *)
      forwards* Hin': find_class_In Find'.
      edestruct methods_corres with (e:=e1) as (ptr_f & cf & ? & ? & ? & Htypefun); eauto.

      forwards Eq: find_class_name Find'.
      forwards Eq': find_method_name Findmeth.
      rewrite Eq, Eq' in *.

      (* the *self parameter *)
      edestruct eval_self_inst with (1:=Find); eauto.
      
      (* the *out parameter *)
      edestruct evall_out_struct with (1:=Find) (o:=o) (c':=clsid) (f':=f); eauto.        
      
      (* recursive funcall evaluation *)
      edestruct Hrec_eval with (c:=c) (e1:=e1) (m1:=m1) (le1:=le1) as (m2 & T & ? & ?); eauto.

      (* output assignments *)
      edestruct exec_funcall_assign with (ys:=ys) as (? & ? & ? & ?) ; eauto.
      skip. admit. admit.
      (* TODO write a lemma which gives the right state *)
      do 3 econstructor; split.
      + simpl.
        unfold binded_funcall.
        rewrite Find', Findmeth.
        apply* exec_Sseq_1.
        *{ eapply exec_Scall; eauto.
           - reflexivity.
           - simpl.
             eapply eval_Elvalue.
             + apply* eval_Evar_global.
             + apply* deref_loc_reference.               
           - apply find_method_In in Findmeth.
             do 2 (econstructor; eauto).
             applys* exprs_eval_simu Find.
           - unfold Genv.find_funct.
             destruct* (Int.eq_dec Int.zero Int.zero) as [|Neq].
             exfalso; apply* Neq.
           - simpl; rewrite Htypefun; repeat f_equal.
             apply* type_pres'.
         }
        * 
      + skip.
      
    (* Skip : "skip" *)
    - exists le1 m1 E0; split*.
      eapply exec_Sskip.

    (* funcall *)
    - forwards* Find'': find_class_sub_same.
      (* rewrite Hfind' in Hfind''; inverts Hfind''. *)
      (* destruct Hstep with (c:=cls) *)
      (*   as (loc_f' & f' & Hget_loc_f' & Hget_f' & Htype_fun & Hvars_nil & ? & ? & Htr & ?); *)
      (*   destruct_conjs; eauto. *)
      forwards Eq: find_class_name Find.
      (* rewrite Eq in Hget_loc_f'; clear Eq. *)
      (* rewrite Hget_loc_f' in Hget_loc_f; inverts Hget_loc_f. *)
      (* rewrite Hget_f' in Hget_f; inverts Hget_f. *)

      (* assert (length f.(Clight.fn_params) = length ((Values.Vptr loc_struct ofs) :: nelist2list vs)) *)
      (*   by (rewrite Hlengths; simpl; f_equal; rewrite Nelist.nelist2list_length; auto). *)

      (* forwards* (le_fun & ? & ?): (compat_funcall_pres cls m). *)
      forwards* Hsub: find_class_sub.
      (* subst env. *)
      edestruct Hrec_exec with (le1:=le_fun) as (? & ? & ? & ? & MS); eauto.
      destruct_conjs.
        
      do 2 econstructor; split.
      apply* eval_funcall_internal.
      + constructor*; rewrite Hvars_nil; simpl; constructor.
      + rewrite* Htr.
        apply* exec_Sseq_1.
        apply* exec_Sreturn_some.
        apply* Clight.eval_Etempvar.
        inverts MS as Hvars'.
        apply* Hvars'; rewrite <-surjective_pairing; eapply in_eq.
      + simpl; split*.
        inverts Htype_fun.
        apply* sem_cast_same.
      + simpl; eauto.
      + constructor*.
        unfold compat_self.
        intro Hin.
        pose proof Hself as Hself'.
        destruct* Hself' as (? & loc_struct' & ofs' & Hget_self' & Hget_co' & Hmem & Hobj).
        do 3 econstructor; splits*.
        intros x' t' Hin'.
        specializes Hmem Hin'; destruct Hmem.
        econstructor; splits*.
        * admit.
        * admit.
  Qed.