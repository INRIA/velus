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
      NoDupMembers ys ->
      length ys = length f.(m_out) ->
      In (o, clsid) c.(c_objs) ->
      In (o, clsid, fid) (get_instance_methods m.(m_body)) ->
      Forall (well_formed_exp c m) es ->
      Forall2 (fun e x => typeof e = snd x) es f.(m_in) ->
      Forall2 (fun y y' => snd y = snd y') ys f.(m_out) ->
      incl ys (meth_vars m) ->
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

  Definition subrep (f: method) (e: env) :=
    sepall (fun ocg =>
              let '(o, cid, g) := ocg in
              match gcenv ! (prefix g cid), e ! o with 
              | Some gco, Some (oblk, t) =>
                if type_eq t (type_of_inst (prefix g cid)) then
                  blockrep gcenv v_empty (co_members gco) oblk
                else sepfalse
              | _, _ => sepfalse
              end) (get_instance_methods f.(m_body)).

  Definition varsrep (f: method) (ve: venv) (le: temp_env) :=
    pure (Forall (fun (xty: ident * typ) =>
                    let (x, ty) := xty in
                    match le ! x with
                    | Some v => match_value ve x v
                    | None => False
                    end) (f.(m_in) ++ f.(m_vars))).
  
  (* Definition sep_invariant *)
  (*            (c: class) (f: method) (S: state) (e: env) (le: temp_env) (m: Mem.mem) *)
  (*            (sb: block) (sofs: Int.int) (outb: block) (outco: composite) := *)
  (*   let (me, ve) := S in *)
  (*   m |= staterep gcenv prog c.(c_name) me sb (Int.unsigned sofs) *)
  (*       ** blockrep gcenv ve outco.(co_members) outb *)
  (*       ** subrep f e *)
  (*       ** varsrep f ve le. *)
  
  Inductive match_states (c: class) (f: method) (S: state): c_state -> Prop :=
    intro_match_states: forall e le m sb sofs outb outco,
      le ! self_id = Some (Vptr sb sofs) ->
      le ! out_id = Some (Vptr outb Int.zero) ->
      gcenv ! (prefix f.(m_name) c.(c_name)) = Some outco ->
      m |= staterep gcenv prog c.(c_name) (fst S) sb (Int.unsigned sofs)
          ** blockrep gcenv (snd S) outco.(co_members) outb
          ** subrep f e
          ** varsrep f (snd S) le ->
      (0 <= Int.unsigned sofs)%Z ->
      match_states c f S (e, le, m).

  Hint Constructors match_states.
  
  (* Remark invariant_blockrep: *)
  (*   forall c f me ve e le m sb sofs outb outco, *)
  (*     sep_invariant c f (me, ve) e le m sb sofs outb outco -> *)
  (*     m |= blockrep gcenv ve (co_members outco) outb. *)
  (* Proof. *)
  (*   introv Hrep. *)
  (*   now apply sep_pick2 in Hrep. *)
  (* Qed. *)

  (* Remark invariant_varsrep: *)
  (*   forall c f me ve e le m sb sofs outb outco, *)
  (*     sep_invariant c f (me, ve) e le m sb sofs outb outco -> *)
  (*     m |= varsrep f ve le. *)
  (* Proof. *)
  (*   introv Hrep. *)
  (*   now do 3 apply sep_proj2 in Hrep. *)
  (* Qed. *)

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

  Remark not_existsb_InMembers:
    forall f x ty,
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = false ->
      In (x, ty) (meth_vars f) ->
      ~ InMembers x f.(m_out).
  Proof.
    introv E ?.
    apply not_true_iff_false in E.
    intro Hin; apply E.
    apply existsb_exists.
    exists (x, ty); split; simpl.
    - apply InMembers_In in Hin.
      destruct Hin as [ty' Hin].
      assert (In (x, ty') (meth_vars f)).
      + now apply in_or_app; right; apply in_or_app; right.
      + pose proof (m_nodup f). 
        now app_NoDupMembers_det.
    - apply ident_eqb_refl.
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
  
  (* Remark invariant_staterep: *)
  (*   forall c clsnm prog' f me ve e le m sb sofs outb outco, *)
  (*     sep_invariant c f (me, ve) e le m sb sofs outb outco -> *)
  (*     find_class clsnm prog = Some (c, prog') -> *)
  (*     m |= staterep gcenv (c :: prog') c.(c_name) me sb (Int.unsigned sofs). *)
  (* Proof. *)
  (*   introv Hrep Find. *)
  (*   eapply staterep_skip in Hrep; eauto. *)
  (*   now apply sep_proj1 in Hrep. *)
  (* Qed. *)
  
  Lemma evall_out_field:
    forall clsnm prog' c f ve e le m x ty outb outco P,
      find_class clsnm prog = Some (c, prog') ->
      m |= blockrep gcenv ve outco.(co_members) outb ** P ->
      In f c.(c_methods) ->
      le ! out_id = Some (Vptr outb Int.zero) ->
      gcenv ! (prefix (m_name f) (c_name c)) = Some outco ->
      In (x, ty) (meth_vars f) ->
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = true ->
      exists d,
        eval_lvalue tge e le m (deref_field out_id (prefix (m_name f) (c_name c)) x ty)
                    outb (Int.add Int.zero (Int.repr d))
        /\ field_offset gcenv x (co_members outco) = Errors.OK d.
  Proof.
    intros ** E.

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
    forall clsnm prog' c f S e le m x ty outb outco v P,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      le ! out_id = Some (Vptr outb Int.zero) ->
      m |= blockrep gcenv (snd S) outco.(co_members) outb ** P ->
      gcenv ! (prefix (m_name f) (c_name c)) = Some outco ->
      In (x, ty) (meth_vars f) ->
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = true ->
      find_var S x v ->
      eval_expr tge e le m (deref_field out_id (prefix (m_name f) (c_name c)) x ty) v.
  Proof.
    intros.
    edestruct evall_out_field with (e:=e); eauto.
    apply* eval_Elvalue.
    rewrite Int.add_zero_l.
    apply* blockrep_deref_mem.
    erewrite <-output_match; eauto.
    apply* existsb_In.
  Qed.

  Lemma eval_temp_var:
    forall clsnm prog' c f S e le m x ty v P,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      m |= varsrep f (snd S) le ** P ->
      In (x, ty) (meth_vars f) ->
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = false ->
      find_var S x v ->
      eval_expr tge e le m (Etempvar x ty) v.
  Proof.
    introv ? ? Hrep Hvars E ?.
    apply sep_proj1, sep_pure' in Hrep.
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
      [(destruct S; now app_match_find_var_det) | contradiction].
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
    forall clsnm prog' c f me e le m x ty sb sofs P,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      le ! self_id = Some (Vptr sb sofs) ->
      (0 <= Int.unsigned sofs)%Z ->
      m |= staterep gcenv prog c.(c_name) me sb (Int.unsigned sofs) ** P ->
      In (x, ty) c.(c_mems) ->
      exists d,
        eval_lvalue tge e le m (deref_field self_id (c_name c) x ty)
                    sb (Int.add sofs (Int.repr d))
        /\ field_offset gcenv x (make_members c) = Errors.OK d
        /\ (0 <= d <= Int.max_unsigned)%Z.
  Proof.
    introv Find ? ? ? Hrep Hin.
    forwards ?: find_class_name Find; subst.
    forwards* (? & Hco & ? & Eq & ? & ?): make_members_co; instantiate (1:=tprog) in Hco.
    rewrite* staterep_skip in Hrep.
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
    forall clsnm prog' c f S e le m x ty sb sofs v P,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      le ! self_id = Some (Vptr sb sofs) ->
      (0 <= Int.unsigned sofs)%Z ->
      m |= staterep gcenv prog c.(c_name) (fst S) sb (Int.unsigned sofs) ** P ->
      In (x, ty) (c_mems c) ->
      find_field S x v ->
      valid_val v ty ->
      eval_expr tge e le m (deref_field self_id (c_name c) x ty) v.
  Proof.
    introv ? ? ? ? Hrep ? ? ?.
    destruct S.
    edestruct evall_self_field as (? & ? & Hoffset & (? & ?)); eauto.
    apply* eval_Elvalue.
    rewrite* staterep_skip in Hrep.
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
      simpl; destruct (existsb (fun out => ident_eqb (fst out) x) f.(m_out)) eqn: E.
      + rewrite sep_swap in Hrep.
        apply* eval_out_field.
      + rewrite sep_comm, sep_assoc, sep_assoc, sep_swap3 in Hrep. 
        apply* eval_temp_var.

    (* State x ty : "self->x" *)
    - inverts WF.
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

  Lemma exp_eval_valid_s:
   forall S es vs,
      Forall2 (exp_eval S) es vs -> Forall2 (fun e v => valid_val v (typeof e)) es vs.
  Proof.
    induction es, vs; intros ** H; inverts H; auto.
    constructor.
    - apply* exp_eval_valid.
    - apply* IHes.
  Qed.

  Lemma exp_eval_access:
    forall S e v,
      exp_eval S e v -> access_mode (typeof e) = By_value (chunk_of_type (typeof e)).
  Proof.
    introv H.
    apply exp_eval_valid in H.
    apply H.
  Qed.

  Lemma exp_eval_access_s:
   forall S es vs,
     Forall2 (exp_eval S) es vs ->
     Forall (fun e => access_mode (typeof e) = By_value (chunk_of_type (typeof e))) es.
  Proof.
    induction es, vs; intros ** H; inverts H; auto.
    constructor.
    - apply* exp_eval_access.
    - apply* IHes.
  Qed.
  
  Lemma exp_eval_lr:
    forall S e v,
      exp_eval S e v -> v = Val.load_result (chunk_of_type (typeof e)) v.
  Proof.
    introv H.
    apply exp_eval_valid in H.
    apply H.
  Qed.

  Lemma exp_eval_lr_s:
   forall S es vs,
     Forall2 (exp_eval S) es vs ->
     Forall2 (fun e v => v = Val.load_result (chunk_of_type (typeof e)) v) es vs.
  Proof.
    induction es, vs; intros ** H; inverts H; auto.
    constructor.
    - apply* exp_eval_lr.
    - apply* IHes.
  Qed.
  
  Hint Resolve exp_eval_valid exp_eval_access exp_eval_lr
       exp_eval_valid_s exp_eval_access_s exp_eval_lr.

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

  Lemma varsrep_corres_out:
    forall m f ve le x t v P Q,
      In (x, t) (m_out f) ->
      (m |= P -> m |= Q) ->
      (m |= varsrep f ve le ** P -> m |= varsrep f (PM.add x v ve) le ** Q).
  Proof.
    intros ** E Himp Hrep.
    unfold varsrep in *.
    rewrite sep_pure in *.
    destruct Hrep as [Hpure Hrep]; split.
    - assert (~InMembers x (f.(m_in) ++ f.(m_vars))) as Notin.
      + pose proof (m_nodup f) as Nodup.
        rewrite app_assoc in Nodup.
        rewrite NoDupMembers_app in Nodup.
        apply In_InMembers in E.
        eapply NoDupMembers_app_InMembers; eauto.
      + induction (m_in f ++ m_vars f) as [|(x', t')]; eauto.
        inverts Hpure.
        constructor.
        * destruct* le ! x'.
          rewrite* match_value_add.
          intro Eqx'y.
          apply Notin.
          subst x'.
          apply inmembers_eq.
        * apply* IHl.
          eapply NotInMembers_cons; eauto.
    - apply* Himp.
  Qed.

  Lemma varsrep_corres_temp:
    forall m f ve le x v P Q,
      (m |= P -> m |= Q) ->
      (m |= varsrep f ve le ** P -> m |= varsrep f (PM.add x v ve) (PTree.set x v le) ** Q).
  Proof.
    intros **  Himp Hrep.
    unfold varsrep in *.
    rewrite sep_pure in *.
    destruct Hrep as [Hpure Hrep]; split.
    - induction (m_in f ++ m_vars f) as [|(x', t')]; eauto.
      inverts Hpure.
      constructor.
      + destruct (ident_eqb x' x) eqn: Ex'x.
        * apply ident_eqb_eq in Ex'x.
          subst x'.
          rewrite PTree.gss.
          unfold match_value. rewrite* PM.gss.
        * apply ident_eqb_neq in Ex'x.
          rewrite PTree.gso.
          change (@PTree.get val x' le) with (@PTree.get Values.val x' le).
          destruct* le ! x'.          
          unfold match_value. rewrite* PM.gso. exact Ex'x.
      + apply* IHl.
    - apply* Himp.
  Qed.
  
  Lemma match_states_assign_out:
    forall c clsnm prog' f le ve x ty m v d outco outb P,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      gcenv ! (prefix (m_name f) (c_name c)) = Some outco ->
      m |= varsrep f ve le ** blockrep gcenv ve outco.(co_members) outb ** P ->
      In (x, ty) (meth_vars f) ->
      field_offset gcenv x (co_members outco) = Errors.OK d ->
      access_mode ty = By_value (chunk_of_type ty) ->
      v = Values.Val.load_result (chunk_of_type ty) v ->
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = true ->
      exists m', Memory.Mem.storev (chunk_of_type ty) m (Vptr outb (Int.repr d)) v = Some m'
            /\ m' |= varsrep f (PM.add x v ve) le
                   ** blockrep gcenv (PM.add x v ve) outco.(co_members) outb ** P .
  Proof.
    intros ** Hrep Hvars Hoffset Haccess Hlr E.

    eapply existsb_In in E; eauto.
    forwards* Eq: output_match.
    pose proof E as Hin; rewrite Eq in Hin.
    pose proof (m_nodup f) as Nodup.
    
    (* get the updated memory *)
    apply sepall_in in Hin.
    destruct Hin as [ws [ys [Hys Heq]]].
    unfold blockrep in Hrep.
    rewrite Heq, Hoffset, Haccess, sep_assoc in Hrep.
    rewrite sep_swap in Hrep.
    eapply Separation.storev_rule' with (v:=v) in Hrep; eauto.
    destruct Hrep as (m' & ? & Hrep).
    exists m'; split*.
    unfold blockrep.
    rewrite Heq, Hoffset, Haccess, sep_assoc.
    rewrite sep_swap in Hrep.
    revert Hrep; apply* varsrep_corres_out; intro Hrep. 
    eapply sep_imp; eauto.
    - unfold hasvalue.
      unfold match_value; simpl.
      rewrite PM.gss.
      rewrite <-Hlr; auto.
    - do 2 apply NoDupMembers_app_r in Nodup.
      rewrite Eq, Hys in Nodup.
      apply NoDupMembers_app_cons in Nodup.
      destruct Nodup as (Notin & Nodup).
      rewrite sepall_switchp with
      (f' := fun xty : ident * type =>
               let (x0, ty0) := xty in
               match field_offset gcenv x0 (co_members outco) with
               | Errors.OK d0 =>
                 match access_mode ty0 with
                 | By_value chunk => contains chunk outb d0 (match_value (PM.add x v ve) x0)
                 | By_reference => sepfalse
                 | By_copy => sepfalse
                 | By_nothing => sepfalse
                 end
               | Errors.Error _ => sepfalse
               end); auto.
      + apply NoDupMembers_NoDup; iauto.
      + intros (x' & t') Hin.
        rewrite* match_value_add.
        intro; subst x'.
        apply Notin.
        eapply In_InMembers; eauto.
  Qed.
  
  Lemma match_states_assign_tempvar:
    forall c clsnm prog' f ve x ty le m v P outco outb,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      gcenv ! (prefix (m_name f) (c_name c)) = Some outco ->
      m |= varsrep f ve le ** blockrep gcenv ve outco.(co_members) outb ** P ->
      In (x, ty) (meth_vars f) ->
      existsb (fun out => ident_eqb (fst out) x) f.(m_out) = false ->
      m |= varsrep f (PM.add x v ve) (PTree.set x v le)
          ** blockrep gcenv (PM.add x v ve) outco.(co_members) outb ** P.
  Proof.
    intros ** Hrep ? E.
    forwards* Eq_outco: output_match. 
    unfold varsrep in *.
    rewrite sep_pure in *. 
    destruct Hrep as (Hpure & Hrep); split*.
    - induction* (m_in f ++ m_vars f).
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
      unfold blockrep in *.
      rewrite sepall_switchp with
      (f' := fun xty : ident * type =>
               let (x0, ty0) := xty in
               match field_offset gcenv x0 (co_members outco) with
               | Errors.OK d0 =>
                 match access_mode ty0 with
                 | By_value chunk => contains chunk outb d0 (match_value (PM.add x v ve) x0)
                 | By_reference => sepfalse
                 | By_copy => sepfalse
                 | By_nothing => sepfalse
                 end
               | Errors.Error _ => sepfalse
               end); auto.
      + pose proof (m_nodup f) as Nodup.
        do 2 apply NoDupMembers_app_r in Nodup.
        rewrite <-Eq_outco; apply NoDupMembers_NoDup; auto.
      + intros (x', t') Hx'.
        rewrite* match_value_add.
        eapply not_existsb_InMembers in E; eauto.
        apply In_InMembers in Hx'.
        intro Hxx'; subst x.
        apply E; rewrite* Eq_outco.
  Qed.  

  Lemma match_states_assign_state:
    forall c clsnm prog' f me x ty m v d sb sofs P,  
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      m |= staterep gcenv prog c.(c_name) me sb (Int.unsigned sofs) ** P ->
      In (x, ty) (c_mems c) ->
      field_offset gcenv x (make_members c) = Errors.OK d ->
      v = Values.Val.load_result (chunk_of_type ty) v ->
      exists m', Memory.Mem.storev (chunk_of_type ty) m (Vptr sb (Int.repr (Int.unsigned sofs + d))) v = Some m'
            /\ m' |= staterep gcenv prog c.(c_name) (madd_mem x v me) sb (Int.unsigned sofs) ** P.
  Proof.
    intros ** Hrep Hmems Hoffset Hlr.
    
    (* get the updated memory *)
    apply sepall_in in Hmems.
    destruct Hmems as [ws [ys [Hys Heq]]].
    eapply staterep_skip in Hrep; eauto.
    simpl staterep in Hrep.
    rewrite ident_eqb_refl, Heq, Hoffset in Hrep.
    do 2 rewrite sep_assoc in Hrep.
    eapply Separation.storev_rule' with (v:=v) in Hrep; eauto.
    destruct Hrep as (m' & ? & Hrep).
    exists m'; split*.
    eapply staterep_skip; eauto.
    simpl staterep.
    rewrite ident_eqb_refl, Heq, Hoffset.
    do 2 rewrite sep_assoc.
    eapply sep_imp; eauto.
    - unfold hasvalue.
      unfold match_value; simpl.
      rewrite PM.gss.
      rewrite <-Hlr; auto.
    - apply* sep_imp'.
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
                          (match_value (PM.add x v (mm_values me)) x0)
               | Errors.Error _ => sepfalse
               end); auto.
      + apply NoDupMembers_NoDup; iauto.
      + intros (x' & t') Hin.
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
    forall clsnm prog' c f me e le m o c' sb sofs P,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      le ! self_id = Some (Vptr sb sofs) ->
      m |= staterep gcenv prog c.(c_name) me sb (Int.unsigned sofs) ** P ->
      In (o, c') (c_objs c) ->
      exists d,
        eval_expr tge e le m (ptr_obj c.(c_name) c' o) (Vptr sb (Int.add sofs (Int.repr d))).
  Proof.
    introv Find ? ? Hrep Hin.
    forwards ?: find_class_name Find; subst.
    forwards* (? & Hco & ? & Eq & ? & ?): make_members_co; instantiate (1:=tprog) in Hco.
    rewrite* staterep_skip in Hrep.
    forwards* (d & Hoffset): staterep_inst_offset. 
    exists d.
    apply eval_Eaddrof.
    apply* eval_Efield_struct.
    - apply* eval_Elvalue.
      apply* deref_loc_copy. 
    - simpl; unfold type_of_inst; eauto.
    - rewrite* Eq. 
  Qed.

  (* Lemma invariant_inst: *)
  (*   forall c f f' S e le m o c' sb sofs outb outco, *)
  (*     sep_invariant c f S e le m sb sofs outb outco -> *)
  (*     In (o, c', f') (get_instance_methods f.(m_body)) -> *)
  (*     exists b co, *)
  (*       e ! o = Some (b, type_of_inst (prefix f' c')) *)
  (*       /\ gcenv ! (prefix f' c') = Some co *)
  (*       /\ m |= blockrep gcenv v_empty (co_members co) b. *)
  (* Proof. *)
  (*   introv Hrep Hin. *)
  (*   destruct S. *)
  (*   apply sep_pick3 in Hrep. *)
  (*   apply sepall_in in Hin; destruct Hin as [ws [xs [Hsplit Hin]]]. *)
  (*   unfold subrep in Hrep. *)
  (*   rewrite Hin in Hrep. clear Hsplit Hin. *)
  (*   apply sep_proj1 in Hrep. *)
  (*   clear ws xs. *)
  (*   destruct gcenv ! (prefix f' c') eqn: Find; [|contradict Hrep]. *)
  (*   destruct e ! o eqn: E; [|contradict Hrep]. *)
  (*   destruct p as (oblk, t). *)
  (*   destruct (type_eq t (type_of_inst (prefix f' c'))); [|contradict Hrep]; subst. *)
  (*   exists oblk c0; split*. *)
  (* Qed. *)

  (* Lemma evall_inst_struct:  *)
  (*   forall clsnm prog' c f f' e le m o c' sb sofs b,  *)
  (*     find_class clsnm prog = Some (c, prog') ->  *)
  (*     In f c.(c_methods) ->  *)
  (*     le ! self_id = Some (Vptr sb sofs) ->  *)
  (*     e ! o = Some (b, type_of_inst (prefix f' c')) -> *)
  (*     eval_lvalue tge e le m (Evar o (type_of_inst (prefix f' c'))) b Int.zero.  *)
  (* Proof.  *)
  (*   intros. *)
  (*   econstructor; eauto. *)
  (* Qed. *)

  Lemma subrep_extract:
    forall f f' e m o c' P,
      m |= subrep f e ** P ->
      In (o, c', f') (get_instance_methods f.(m_body)) ->
      exists b co,
        e ! o = Some (b, type_of_inst (prefix f' c'))
        /\ gcenv ! (prefix f' c') = Some co.
  Proof.
    intros ** Hrep Hin.
    unfold subrep in Hrep.
    apply sepall_in in Hin; destruct Hin as (ws & xs & Hin & Heq). 
    rewrite Heq in Hrep.
    do 2 apply sep_proj1 in Hrep.
    destruct gcenv ! (prefix f' c'); [|contradict Hrep].
    destruct e ! o; [|contradict Hrep].
    destruct p as (oblk, t).
    destruct (type_eq t (type_of_inst (prefix f' c'))); [|contradict Hrep].
    subst t.
    exists oblk c; auto.
  Qed.

  Lemma evall_inst_field:
     forall x ty e le m o clsid f c callee prog'' oblk instco ve P,
      m |= blockrep gcenv ve instco.(co_members) oblk ** P ->
      e ! o = Some (oblk, type_of_inst (prefix f clsid)) ->
      gcenv ! (prefix f clsid) = Some instco ->
      find_class clsid prog = Some (c, prog'') ->
      find_method f c.(c_methods) = Some callee ->
      In (x, ty) callee.(m_out) ->
      exists d,
        eval_lvalue tge e le m (Efield (Evar o (type_of_inst (prefix f clsid))) x ty) 
                    oblk (Int.add Int.zero (Int.repr d))
        /\ field_offset tge x instco.(co_members) = Errors.OK d.
  Proof.
    intros ** Find Findmeth Hin.

    forwards Eq: find_class_name Find.
    forwards Eq': find_method_name Findmeth.
    subst.
    apply find_method_In in Findmeth.
    erewrite output_match in Hin; eauto.

    forwards* (d & Hoffset): blockrep_field_offset.
    exists d; splits*.
    apply* eval_Efield_struct.
    + apply* eval_Elvalue.
      apply* deref_loc_copy.
    + simpl; unfold type_of_inst; eauto.
  Qed.
  
  Lemma exec_funcall_assign:
    forall callee caller ys e1 le1 m1 c prog' c' prog'' o f clsid
      me ve me' ve' sb sofs outb outco rvs binst instco P,  
      find_class c.(c_name) prog = Some (c, prog') ->
      In caller c.(c_methods) ->
      find_class clsid prog = Some (c', prog'') ->
      find_method f c'.(c_methods) = Some callee ->
      In (o, clsid, f) (get_instance_methods caller.(m_body)) ->
      length ys = length callee.(m_out) ->
      length rvs = length callee.(m_out) ->
      NoDupMembers ys ->
      incl ys (meth_vars caller) ->
      Forall2 (fun y y' => snd y = snd y') ys callee.(m_out) ->
      le1 ! out_id = Some (Vptr outb Int.zero) ->
      le1 ! self_id = Some (Vptr sb sofs) ->
      gcenv ! (prefix (m_name caller) (c_name c)) = Some outco ->
      m1 |= staterep gcenv prog c.(c_name) (madd_obj o me' me) sb (Int.unsigned sofs)
           ** blockrep gcenv (adds' callee.(m_out) rvs ve') instco.(co_members) binst
           ** blockrep gcenv ve outco.(co_members) outb
           ** varsrep caller ve le1
           ** P ->                                       
      Forall2 (fun v y => valid_val v (snd y)) rvs ys ->
      e1 ! o = Some (binst, type_of_inst (prefix f clsid)) ->
      gcenv ! (prefix f clsid) = Some instco ->
      exists le2 m2 T,
        exec_stmt tge (function_entry2 tge) e1 le1 m1
                  (funcall_assign ys c.(c_name) caller o (type_of_inst (prefix f clsid)) callee)
                  T le2 m2 Out_normal
        /\ m2 |= staterep gcenv prog c.(c_name) (madd_obj o me' me) sb (Int.unsigned sofs)
               ** blockrep gcenv (adds' ys rvs ve) outco.(co_members) outb
               ** varsrep caller (adds' ys rvs ve) le2
               ** P
        /\ le2 ! out_id = Some (Vptr outb Int.zero) 
        /\ le2 ! self_id = Some (Vptr sb sofs). 
  Proof.
    unfold funcall_assign.
    intros ** Findc ? Findc' Findmeth ? Length1 Length2 Nodup Incl 
           Types Hout Hself Houtco Hrep Valids Hinst Hinstco.
    revert ve ve' le1 m1 ys rvs Hout Hself Hrep Incl Types Length1 Length2 Nodup Valids.
    pose proof (m_nodup callee) as Nodup'.
    do 2 apply NoDupMembers_app_r in Nodup'.
    induction (m_out callee) as [|(y', ty') outs]; intros;
    destruct ys, rvs; try discriminate.
    - exists le1 m1 E0; splits*.
      + apply exec_Sskip.
      + apply sep_drop2 in Hrep.
        unfold adds'; simpl fold_right; auto.
    - destruct p as (y, ty). 
      inverts Length1.
      inverts Length2.
      inverts Nodup.
      inverts Nodup'.    
      apply incl_cons' in Incl.
      destruct Incl as [Hvars Incl].
      inverts Types as Eqty Types; simpl in Eqty.
      inverts Valids as Valid Valids; simpl in Valid.
      forwards Eq: find_class_name Findc'.
      forwards Eq': find_method_name Findmeth.
      
      forwards* Findmeth': find_method_In Findmeth. 
      forwards* Eq_instco: output_match Findc'; [rewrite Eq, Eq'; eauto|].
      forwards* Eq_outco: output_match Findc. 

      (* get the o.y' value evaluation *)
      assert (In (y', ty') callee.(m_out)) as Hin. admit.
      apply sep_swap in Hrep.
      forwards* (dy' & Ev_o_y' & Hoffset_y'): (evall_inst_field y' ty' e1 le1).
      subst ty'.
      assert (eval_expr tge e1 le1 m1 (Efield (Evar o (type_of_inst (prefix f clsid))) y' ty) v).
      + apply* eval_Elvalue.
        apply* blockrep_deref_mem.
        * rewrite <-Eq, <-Eq' in Hinstco.
          erewrite output_match in Hin; eauto.
        * unfold adds'; simpl.
          apply PM.gss.
        * rewrite Int.unsigned_zero; simpl.
          rewrite* Int.unsigned_repr.
          admit.
          
      + unfold assign.
        simpl fold_right.
        destruct (existsb (fun out => ident_eqb (fst out) y) caller.(m_out)) eqn: E.

        (* out->y = o.y' *)
        *{ (* get the 'out' variable left value evaluation *)
            rewrite sep_swap3, sep_swap34, sep_swap23 in Hrep. 
            forwards* (dy & Ev_out_y & Hoffset_y): evall_out_field Findc.            
            
            (* get the updated memory *)
            rewrite sep_swap in Hrep.
            edestruct match_states_assign_out with (1:=Findc) as (m2 & Store & Hm2); eauto.
            apply Valid. 
            
            edestruct IHouts with (m1:=m2) (ve:= PM.add y v ve) (ve':=PM.add y' v ve')
              as (le' & m' & T' & Exec & Hm' & ? & ?); eauto.
            - rewrite sep_swap4, sep_swap23, sep_swap34.  
              rewrite adds'_cons_cons in Hm2; auto.

            - clear IHouts.            
              do 3 econstructor; splits*.
              + eapply exec_Sseq_1 with (m1:=m2); eauto.
                apply* ClightBigstep.exec_Sassign.
                apply* assign_loc_value.
                rewrite* Int.add_zero_l. 
              + rewrite* adds'_cons_cons. 
          }
          
        (* y = o.y' *)
        *{ edestruct IHouts with (m1:=m1) (le1:=PTree.set y v le1) (ve:= PM.add y v ve) (ve':=PM.add y' v ve')
             as (le' & m' & T' & Exec & Hm' & ? & ?); eauto.
           - rewrite* PTree.gso.
             pose proof (m_out_id caller) as Notout.
             apply In_InMembers in Hvars.
             eapply InMembers_neq in Hvars; eauto.
           - rewrite* PTree.gso.
             pose proof (m_self_id caller) as Notout.
             apply In_InMembers in Hvars.
             eapply InMembers_neq in Hvars; eauto.
           - rewrite sep_swap3, sep_swap34, sep_swap23, sep_swap in Hrep.
             rewrite sep_swap23, sep_swap34, sep_swap3.
             rewrite adds'_cons_cons in Hrep; auto.
             eapply match_states_assign_tempvar with (c:=c); eauto.
               
           - clear IHouts.
             do 3 econstructor; splits*.
             + eapply exec_Sseq_1; eauto.
               apply* ClightBigstep.exec_Sset.
             + rewrite* adds'_cons_cons. 
         }
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
        forall c c' caller callee prog'' S e1 le1 m1 o f ptr_f sb o_ofs outb outco oty sofs binst instco
          (* (MS: match_states c caller S (e1, le1, m1)) *),
          m1 |= staterep gcenv prog c.(c_name) (fst S) sb (Int.unsigned sofs)
               ** blockrep gcenv (snd S) outco.(co_members) outb
               ** subrep caller e1
               ** varsrep caller (snd S) le1 ->
          Globalenvs.Genv.find_symbol tge fid = Some ptr_f ->
          Globalenvs.Genv.find_funct_ptr tge ptr_f = Some (Ctypes.Internal f) ->
          find_inst S o me1 ->
          find_class clsid prog = Some (c', prog'') ->
          find_method fid c'.(c_methods) = Some callee ->
          oty = type_of_inst (prefix fid clsid) ->
          e1 ! o = Some (binst, oty) ->
          eval_expr tge e1 le1 m1 (ptr_obj c.(c_name) clsid o) (Vptr sb o_ofs) ->
          (* eval_expr tge e1 le1 m1 (Eaddrof (Evar o oty) (pointer_of oty)) (Vptr outb Int.zero) -> *)
          exists m2 T,
            eval_funcall tge (function_entry2 tge) m1 (Internal f)
                         ((Vptr sb o_ofs) :: (Vptr binst Int.zero) :: vs) T m2 Vundef
            /\ m2 |= staterep gcenv prog c.(c_name) (madd_obj o me2 (fst S)) sb (Int.unsigned sofs)
                   ** blockrep gcenv (adds' callee.(m_out) rvs v_empty) instco.(co_members) binst
                   ** blockrep gcenv (snd S) outco.(co_members) outb
                   ** subrep caller e1
                   ** varsrep caller (snd S) le1

            (* match_states c caller (update_inst S o me2) (e1, le1, m2) *)).
  Proof.
    clear TRANSL main_node_exists.
    apply stmt_eval_call_ind;
      [| |introv ? ? ? ? Hifte|introv ? HS1 ? HS2|introv ? Evs ? Hrec_eval|
       |introv Find ? ? Hrec_exec];
      intros;
      try inversion_clear WF as [? ? Hvars|? ? Hin| |
                                 |? ? ? ? ? ? ? ? ? ? ? ? Hin ? ? ? Find' Findmeth|];
      try inverts MS as Hself Hout Houtco Hrep.
    
    (* Assign x e : "x = e" *)
    - simpl; unfold assign.
      destruct (existsb (fun out => ident_eqb (fst out) x) f.(m_out)) eqn: E.

      (* out->x = e *)
      + (* get the 'out' variable left value evaluation *)
        rewrite sep_comm, sep_assoc, sep_assoc, sep_swap23 in Hrep.            
        edestruct evall_out_field; eauto.
        
        (* get the updated memory *)
        rewrite sep_swap in Hrep.
        edestruct match_states_assign_out as (m2 & ? & Hm2); jauto.
        rewrite sep_swap, sep_swap23, <-sep_assoc, <-sep_assoc, sep_comm, sep_assoc in Hrep.  
        
        exists le1 m2 E0; split*.
        apply* ClightBigstep.exec_Sassign.
        * rewrite* type_pres; apply* sem_cast_same; apply* exp_eval_valid.
        *{ apply* assign_loc_value.
           - simpl; apply* exp_eval_access.
           - rewrite* Int.add_zero_l.
         }
        * econstructor; eauto.
          rewrite sep_comm, sep_assoc, sep_assoc, sep_swap23, sep_swap.  
          unfold update_var; auto.
           
      (* x = e *)
      + exists (PTree.set x v le1) m1 E0; split.
        * apply* ClightBigstep.exec_Sset.
        *{ pose proof (m_out_id f); pose proof (m_self_id f).
           econstructor; eauto.
           - rewrite* PTree.gso.
             eapply In_InMembers, InMembers_neq in Hvars; eauto.
           - rewrite* PTree.gso.
             eapply In_InMembers, InMembers_neq in Hvars; eauto.
           - rewrite sep_comm, sep_assoc, sep_assoc, sep_swap23, sep_swap in *.
             apply* match_states_assign_tempvar.
         }
         
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
      edestruct eval_self_inst with (1:=Find) (e:=e1); eauto.

      (* the *out parameter *)
      rewrite sep_swap3 in Hrep.
      edestruct subrep_extract as (oblk & instco & Hoblk & Hinstco); eauto.
      
      (* recursive funcall evaluation *)
      rewrite sep_swap3 in Hrep.
      edestruct Hrec_eval with (c:=c) (e1:=e1) (m1:=m1) (le1:=le1) (instco:=instco)
        as (m2 & T & ? & Hm2); eauto.
      clear Hrec_eval.
      
      (* output assignments *)
      rewrite sepemp_right in Hm2; do 4 rewrite sep_assoc in Hm2.
      rewrite sep_swap45 in Hm2.
      edestruct exec_funcall_assign with (ys:=ys) (m1:=m2) as (le3 & m3 & ? & ? & Hm3 & ? & ?) ; eauto.
      + transitivity (length ys); auto.
      + admit.
      + rewrite sep_swap34, <-sepemp_right in Hm3.
        exists le3 m3; econstructor; split*.
        simpl.
        unfold binded_funcall.
        rewrite Find', Findmeth.
        eapply exec_Sseq_1 with (m1:=m2); eauto.
        assert (forall v, le1 = set_opttemp None v le1) as E by reflexivity.
        erewrite E at 2.
        eapply exec_Scall; eauto.
        * reflexivity.
        *{ simpl.
           eapply eval_Elvalue.
           - apply* eval_Evar_global.
           - apply* deref_loc_reference.               
         }
        * apply find_method_In in Findmeth.
          do 2 (econstructor; eauto).
          applys* exprs_eval_simu Find.
        * unfold Genv.find_funct.
          destruct* (Int.eq_dec Int.zero Int.zero) as [|Neq].
          exfalso; apply* Neq.
        * simpl; rewrite Htypefun; repeat f_equal.
          apply* type_pres'.
          
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
        * admit
  Qed.