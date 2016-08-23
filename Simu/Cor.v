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

Require Import Syn Sem Tra Sep SepInv.

Require Import Program.Tactics.
Require Import List.
Import List.ListNotations.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Sorting.Permutation.

Open Scope list_scope.
Open Scope sep_scope.
Open Scope Z.

Require Import LibTactics.
Ltac auto_star ::= try solve [eassumption | auto | jauto].

(* To Tidy: *)

Ltac app_match_find_var_det :=
  match goal with
  | H1: find_var (?me, ?ve) ?x ?v1,
        H2: match_value ?ve ?x ?v2 |- _ =>
    assert (v2 = v1) by (applys* match_find_var_det H2 H1); subst v1; clear H2
  end.

Lemma type_eq_refl:
  forall {A} t (T F: A),
    (if type_eq t t then T else F) = T.
Proof.
  intros.
  destruct (type_eq t t) as [|Neq]; auto.
  now contradict Neq.
Qed.

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
  Hypothesis Consistent: composite_env_consistent gcenv.
  
  Opaque sepconj.
  
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
      well_formed_stmt c' f f.(m_body) ->
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

  Definition c_state := (Clight.env * Clight.temp_env)%type.

  (* Definition subrep_inst e ocg := *)
  (*   let '(o, cid, g) := ocg in *)
  (*   match gcenv ! (prefix g cid), e ! o with  *)
  (*   | Some gco, Some (oblk, t) => *)
  (*     if type_eq t (type_of_inst (prefix g cid)) then *)
  (*       blockrep gcenv v_empty (co_members gco) oblk *)
  (*     else sepfalse *)
  (*   | _, _ => sepfalse *)
  (*   end. *)

  Definition subrep_inst (xbt: ident * (block * typ)) :=
    let '(x, (b, t)) := xbt in
    match t with
    | Tstruct id _ =>
      match gcenv ! id with
      | Some co =>
        blockrep gcenv v_empty (co_members co) b
      | None => sepfalse
      end
    | _ => sepfalse
    end.

  Definition subrep_inst_env e (xt: ident * type) :=
    let (x, t) := xt in
    match e ! x with
    | Some (b, Tstruct id _ as t') =>
      if (type_eq t t') then
        match gcenv ! id with
        | Some co =>
          blockrep gcenv v_empty (co_members co) b
        | None => sepfalse
        end
      else sepfalse
    | _ => sepfalse
    end.
    
  (* Definition subrep (f: method) (e: env) := *)
  (*   sepall (subrep_inst e) (get_instance_methods f.(m_body)). *)

  Definition drop_block (xbt: ident * (block * type)) :=
    let '(x, (b, t)) := xbt in
    (x, t).
  
  Definition subrep (f: method) (e: env) :=
    sepall (subrep_inst_env e)
           (make_out_vars (get_instance_methods f.(m_body))).

  Lemma subrep_eqv:
    forall f e,
      Permutation (make_out_vars (get_instance_methods f.(m_body)))
                  (map drop_block (PTree.elements e)) ->
      subrep f e <-*->
      sepall subrep_inst (PTree.elements e).
  Proof.
    intros ** Permut.
    unfold subrep.
    rewrite Permut.
    clear Permut.
    remember (PTree.elements e) as elems.
    assert (exists elems', PTree.elements e = elems' ++ elems) as Helems by
          (exists (@nil (ident * (block * typ))); now simpl).
    clear Heqelems.
    induction elems as [|(x, (b, t))]; simpl; auto.
    destruct Helems as (elems' & Helems).
    apply sepconj_eqv.
    - assert (e ! x = Some (b, t)) as Hx
          by (apply PTree.elements_complete; rewrite Helems;
              apply in_app; right; apply in_eq).
      rewrite Hx; auto.
      destruct t; auto.
      rewrite type_eq_refl; auto.
    - eapply IHelems; eauto.
      exists (elems' ++ [(x, (b, t))]); rewrite app_last_app; auto.
  Qed.
  
  Definition range_inst (xbt: ident * (block * typ)):=
    let '(x, (b, t)) := xbt in
    range b 0 (Ctypes.sizeof tge t).

  Definition range_inst_env e x :=
    match e ! x with
    | Some (b, t) => range b 0 (Ctypes.sizeof tge t)
    | None => sepfalse
    end.

  Definition subrep_range (e: env) :=
    sepall range_inst (PTree.elements e).
  
  Lemma subrep_range_eqv:
    forall e,
      subrep_range e <-*->
      sepall (range_inst_env e) (map fst (PTree.elements e)).
  Proof.
    intro e.
    unfold subrep_range.
    remember (PTree.elements e) as elems.
    assert (exists elems', PTree.elements e = elems' ++ elems) as Helems by
          (exists (@nil (ident * (block * typ))); now simpl).
    clear Heqelems.
    induction elems as [|(x, (b, t))]; auto; simpl.
    destruct Helems as [elems' Helems].
    apply sepconj_eqv.
    - unfold range_inst_env.
      assert (In (x, (b, t)) (PTree.elements e)) as Hin
          by (rewrite Helems; apply in_or_app; right; apply in_eq).
      apply PTree.elements_complete in Hin.
      rewrite Hin; auto.
    - apply IHelems.
      exists (elems' ++ [(x, (b, t))]).
      rewrite app_last_app; auto.
  Qed.

  Remark decidable_footprint_subrep_inst:
    forall x, decidable_footprint (subrep_inst x).
  Proof.
    intros (x, (b, t)).
    simpl; destruct t; auto. destruct gcenv ! i; auto.
  Qed.

  Remark footprint_perm_subrep_inst:
    forall x b lo hi,
      footprint_perm (subrep_inst x) b lo hi.
  Proof.
    intros (x, (b, t)) b' lo hi.
    simpl; destruct t; auto. destruct gcenv ! i; auto.
  Qed.
  
  Remark disjoint_footprint_range_inst:
    forall l b lo hi,
      ~ InMembers b (map snd l) ->
      disjoint_footprint (range b lo hi) (sepall range_inst l).
  Proof.
    induction l as [|(x, (b', t'))]; simpl;
    intros b lo hi Notin.
    - apply sepemp_disjoint. 
    - rewrite disjoint_footprint_sepconj; split.
      + intros blk ofs Hfp Hfp'.
        apply Notin.
        left.
        simpl in *. transitivity blk; iauto.
      + apply IHl.
        intro; apply Notin; now right.
  Qed.
  
  Hint Resolve decidable_footprint_subrep_inst footprint_perm_subrep_inst.

  Lemma range_wand_equiv:
    forall e,
      Forall (fun xt: ident * typ => let (_, t):= xt in
                     exists id co,
                       t = Tstruct id noattr
                       /\ gcenv ! id = Some co
                       /\ co_su co = Struct
                       /\ NoDupMembers (co_members co)
                       /\ forall x' t',
                           In (x', t') (co_members co) ->
                           exists chunk : AST.memory_chunk,
                             access_mode t' = By_value chunk /\
                             (align_chunk chunk | alignof gcenv t'))
             (map drop_block (PTree.elements e)) ->
      NoDupMembers (map snd (PTree.elements e)) ->
      subrep_range e <-*->
      sepall subrep_inst (PTree.elements e)
      ** (sepall subrep_inst (PTree.elements e) -* subrep_range e).
  Proof.
    unfold subrep_range.
    intros ** Forall Nodup.
    split.
    2: now rewrite* sep_unwand.
    induction (PTree.elements e) as [|(x, (b, t))]; simpl in *.
    - rewrite <-hide_in_sepwand; auto.
      now rewrite <-sepemp_right.
    - inverts Forall as (id & co & Ht & Hco & ? & ? & ?) Forall.
      inverts Nodup as Notin Nodup.
      rewrite Ht, Hco.
      rewrite sep_assoc.
      rewrite IHl at 1; auto.
      rewrite <-unify_distinct_wands; auto.
      + repeat rewrite <-sep_assoc.
        apply sep_imp'; auto.
        rewrite sep_comm, sep_assoc, sep_swap.
        apply sep_imp'; auto.
        simpl range_inst.
        rewrite <-range_imp_with_wand; auto.
        simpl.
        change ((prog_comp_env tprog) ! id) with (gcenv ! id).
        rewrite Hco.
        eapply blockrep_empty; eauto.
      + now apply disjoint_footprint_range_inst. 
      + simpl. change ((prog_comp_env tprog) ! id) with (gcenv ! id); rewrite Hco.
        rewrite blockrep_empty; eauto.
        reflexivity.
      + apply subseteq_footprint_sepall.
        intros (x', (b', t')) Hin; simpl.
        assert (In (x', t') (map drop_block l))
          by (change (x', t') with (drop_block (x', (b', t')));
               apply in_map; auto).
        eapply In_Forall in Forall; eauto.
        simpl in Forall.
        destruct Forall as (id' & co' & Ht' & Hco' & ? & ? & ?).
        rewrite Ht', Hco'. simpl.
        change ((prog_comp_env tprog) ! id') with (gcenv ! id').
        rewrite Hco'.        
        rewrite blockrep_empty; eauto.
        reflexivity.
  Qed.
  
  Definition varsrep (f: method) (ve: venv) (le: temp_env) :=
    pure (Forall (fun (xty: ident * typ) =>
                    let (x, ty) := xty in
                    match le ! x with
                    | Some v => match_value ve x v
                    | None => False
                    end) (f.(m_in) ++ f.(m_vars))).

  Definition match_states
             (c: class) (f: method) (S: state) (CS: c_state)
             (sb: block) (sofs: int) (outb: block) (outco: composite): massert :=
    let (e, le) := CS in
    pure (le ! self_id = Some (Vptr sb sofs))
    ** pure (le ! out_id = Some (Vptr outb Int.zero))
    ** pure (gcenv ! (prefix f.(m_name) c.(c_name)) = Some outco)
    ** pure (0 <= Int.unsigned sofs)%Z
    ** staterep gcenv prog c.(c_name) (fst S) sb (Int.unsigned sofs)
    ** blockrep gcenv (snd S) outco.(co_members) outb
    ** subrep f e
    ** varsrep f (snd S) le
    ** (subrep f e -* subrep_range e).

  Lemma match_states_conj:
    forall c f S e le m sb sofs outb outco P,
      m |= match_states c f S (e, le) sb sofs outb outco ** P <->
      m |= staterep gcenv prog c.(c_name) (fst S) sb (Int.unsigned sofs)
          ** blockrep gcenv (snd S) outco.(co_members) outb
          ** subrep f e
          ** varsrep f (snd S) le
          ** (subrep f e -* subrep_range e)
          ** P
      /\ le ! self_id = Some (Vptr sb sofs)
      /\ le ! out_id = Some (Vptr outb Int.zero)
      /\ gcenv ! (prefix f.(m_name) c.(c_name)) = Some outco
      /\ (0 <= Int.unsigned sofs)%Z.
  Proof.
    unfold match_states; split; intros ** H.
    - repeat rewrite sep_assoc in H; repeat rewrite sep_pure in H; tauto.
    - repeat rewrite sep_assoc; repeat rewrite sep_pure; tauto. 
  Qed.

   (* Inductive match_states (c: class) (f: method) (S: state): c_state -> Prop := *)
  (*   intro_match_states: forall e le m sb sofs outb outco, *)
  (*     le ! self_id = Some (Vptr sb sofs) -> *)
  (*     le ! out_id = Some (Vptr outb Int.zero) -> *)
  (*     gcenv ! (prefix f.(m_name) c.(c_name)) = Some outco -> *)
  (*     m |= staterep gcenv prog c.(c_name) (fst S) sb (Int.unsigned sofs) *)
  (*         ** blockrep gcenv (snd S) outco.(co_members) outb *)
  (*         ** subrep f e *)
  (*         ** varsrep f (snd S) le -> *)
  (*     (0 <= Int.unsigned sofs)%Z -> *)
  (*     match_states c f S (e, le, m). *)

  (* Hint Constructors match_states. *)
  
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

    forwards* (d & Hoffset & ?): blockrep_field_offset.
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
    forall c S exp clsnm prog' v e le m f sb sofs outb outco P,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      m |= staterep gcenv prog c.(c_name) (fst S) sb (Int.unsigned sofs)
          ** blockrep gcenv (snd S) outco.(co_members) outb
          ** subrep f e
          ** varsrep f (snd S) le
          ** P ->
      le ! self_id = Some (Vptr sb sofs) ->
      le ! out_id = Some (Vptr outb Int.zero) ->
      gcenv ! (prefix f.(m_name) c.(c_name)) = Some outco ->
      (0 <= Int.unsigned sofs)%Z ->
      well_formed_exp c f exp ->
      exp_eval S exp v ->
      Clight.eval_expr tge e le m (translate_exp c f exp) v.
  Proof.
    intros c S exp; induction exp as [x ty| |cst];
    introv Find Hf Hrep ? ? ? ? WF EV;
    inverts EV.

    (* Var x ty : "x" *)
    - inverts WF as Hvars.
      simpl; destruct (existsb (fun out => ident_eqb (fst out) x) f.(m_out)) eqn: E.
      + rewrite sep_swap in Hrep.
        apply* eval_out_field.
      + rewrite sep_swap4 in Hrep.
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
    forall c S es es' prog' clsnm vs e le m f sb sofs outb outco P,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      m |= staterep gcenv prog c.(c_name) (fst S) sb (Int.unsigned sofs)
          ** blockrep gcenv (snd S) outco.(co_members) outb
          ** subrep f e
          ** varsrep f (snd S) le
          ** P ->
      le ! self_id = Some (Vptr sb sofs) ->
      le ! out_id = Some (Vptr outb Int.zero) ->
      gcenv ! (prefix f.(m_name) c.(c_name)) = Some outco ->
      (0 <= Int.unsigned sofs)%Z ->
      Forall (well_formed_exp c f) es ->
      Forall2 (exp_eval S) es vs ->
      es' = map (translate_exp c f) es ->
      Clight.eval_exprlist tge e le m es'
                           (list_type_to_typelist (map Clight.typeof es')) vs.
  Proof.
    Hint Constructors Clight.eval_exprlist.
    introv ? ? ? ? ? ? ? WF EV ?; subst es';
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
    rewrite staterep_skip in Hrep; eauto.
    simpl staterep in Hrep.
    unfold staterep_mems in Hrep.
    rewrite ident_eqb_refl, Heq, Hoffset in Hrep.
    do 2 rewrite sep_assoc in Hrep.
    eapply Separation.storev_rule' with (v:=v) in Hrep; eauto.
    destruct Hrep as (m' & ? & Hrep).
    exists m'; split*.
    rewrite staterep_skip; eauto.
    simpl staterep.
    unfold staterep_mems.
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
          /\ f.(fn_params) = (self_id, type_of_inst_p c.(c_name))
                              :: (out_id, type_of_inst_p (prefix m.(m_name) c.(c_name)))
                              :: m.(m_in)
        /\ f.(fn_return) = Tvoid
        /\ f.(fn_callconv) = AST.cc_default
        /\ f.(fn_vars) = make_out_vars (get_instance_methods m.(m_body))
        /\ f.(fn_temps) = m.(m_vars) 
        /\ list_norepet (var_names f.(fn_params))
        /\ list_norepet (var_names f.(fn_vars))
        /\ list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps))
        /\ f.(fn_body) = return_none (translate_stmt prog c m m.(m_body)).
  Admitted.
  
  Lemma eval_self_inst:
    forall clsnm prog' c f me e le m o c' sb sofs P,
      find_class clsnm prog = Some (c, prog') ->
      In f c.(c_methods) ->
      le ! self_id = Some (Vptr sb sofs) ->
      m |= staterep gcenv prog c.(c_name) me sb (Int.unsigned sofs) ** P ->
      In (o, c') (c_objs c) ->
      exists d,
        eval_expr tge e le m (ptr_obj c.(c_name) c' o) (Vptr sb (Int.add sofs (Int.repr d)))
        /\ field_offset gcenv o (make_members c) = Errors.OK d.
  Proof.
    introv Find ? ? Hrep Hin.
    forwards ?: find_class_name Find; subst.
    forwards* (? & Hco & ? & Eq & ? & ?): make_members_co; instantiate (1:=tprog) in Hco.
    rewrite* staterep_skip in Hrep.
    forwards* (d & Hoffset): staterep_inst_offset. 
    exists d; split*.
    apply eval_Eaddrof.
    apply* eval_Efield_struct.
    - apply* eval_Elvalue.
      apply* deref_loc_copy. 
    - simpl; unfold type_of_inst; eauto.
    - rewrite* Eq. 
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
        /\ field_offset tge x instco.(co_members) = Errors.OK d
        /\ (0 <= d <= Int.max_unsigned)%Z.
  Proof.
    intros ** Find Findmeth Hin.

    forwards Eq: find_class_name Find.
    forwards Eq': find_method_name Findmeth.
    subst.
    apply find_method_In in Findmeth.
    erewrite output_match in Hin; eauto.

    forwards* (d & Hoffset & ?): blockrep_field_offset.
    exists d; splits*.
    apply* eval_Efield_struct.
    + apply* eval_Elvalue.
      apply* deref_loc_copy.
    + simpl; unfold type_of_inst; eauto.
  Qed.
  
  Lemma exec_funcall_assign:
    forall callee caller ys e1 le1 m1 c prog' c' prog'' o f clsid
      ve ve' sb sofs outb outco rvs binst instco P,  
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
      m1 |= blockrep gcenv (adds callee.(m_out) rvs ve') instco.(co_members) binst
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
        /\ m2 |= blockrep gcenv (adds callee.(m_out) rvs ve') instco.(co_members) binst
               ** blockrep gcenv (adds ys rvs ve) outco.(co_members) outb
               ** varsrep caller (adds ys rvs ve) le2
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
    remember (m_out callee) as outs.
    assert (exists outs', m_out callee = outs' ++ outs) as Eq_out
        by (exists (@nil (ident * typ)); auto).
    clear Heqouts.
    induction outs as [|(y', ty') outs]; intros;
    destruct ys, rvs; try discriminate.
    - exists le1 m1 E0; splits*.
      apply exec_Sskip.
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
      destruct Eq_out as (outs' & Eq_out).

      (* get the o.y' value evaluation *)
      assert (In (y', ty') callee.(m_out)) as Hin
          by (rewrite Eq_out; apply in_or_app; right; apply in_eq).
      forwards* (dy' & Ev_o_y' & Hoffset_y' & ?): (evall_inst_field y' ty' e1 le1).
      subst ty'.
      assert (eval_expr tge e1 le1 m1 (Efield (Evar o (type_of_inst (prefix f clsid))) y' ty) v).
      + apply* eval_Elvalue.
        apply* blockrep_deref_mem.
        * rewrite <-Eq, <-Eq' in Hinstco.
          erewrite output_match in Hin; eauto.
        * unfold adds; simpl.
          apply PM.gss.
        * rewrite Int.unsigned_zero; simpl.
          rewrite* Int.unsigned_repr.
          
      + unfold assign.
        simpl fold_right.
        destruct (existsb (fun out => ident_eqb (fst out) y) caller.(m_out)) eqn: E.

        (* out->y = o.y' *)
        *{ (* get the 'out' variable left value evaluation *)
            rewrite sep_swap in Hrep.
            forwards* (dy & Ev_out_y & Hoffset_y): evall_out_field Findc.            
            
            (* get the updated memory *)
            rewrite sep_swap23, sep_swap in Hrep.
            edestruct match_states_assign_out with (1:=Findc) as (m2 & Store & Hm2); eauto.
            apply Valid. 
            
            edestruct IHouts with (m1:=m2) (ve:= PM.add y v ve) (ve':=PM.add y' v ve')
              as (le' & m' & T' & Exec & Hm' & ? & ?); eauto.
            - exists (outs' ++ [(y', ty)]).
              rewrite app_last_app; auto.
            - rewrite sep_swap3. 
              rewrite adds_cons_cons in Hm2; auto.

            - clear IHouts.            
              do 3 econstructor; splits*.
              + eapply exec_Sseq_1 with (m1:=m2); eauto.
                apply* ClightBigstep.exec_Sassign.
                apply* assign_loc_value.
                rewrite* Int.add_zero_l. 
              + repeat rewrite* adds_cons_cons. 
          }
          
        (* y = o.y' *)
        *{ edestruct IHouts with (m1:=m1) (le1:=PTree.set y v le1) (ve:= PM.add y v ve) (ve':=PM.add y' v ve')
             as (le' & m' & T' & Exec & Hm' & ? & ?); eauto.
           - exists (outs' ++ [(y', ty)]).
             rewrite app_last_app; auto.
           - rewrite* PTree.gso.
             pose proof (m_out_id caller) as Notout.
             apply In_InMembers in Hvars.
             eapply InMembers_neq in Hvars; eauto.
           - rewrite* PTree.gso.
             pose proof (m_self_id caller) as Notout.
             apply In_InMembers in Hvars.
             eapply InMembers_neq in Hvars; eauto.
           - rewrite sep_swap3 in *.
             rewrite adds_cons_cons in Hrep; auto.
             eapply match_states_assign_tempvar with (c:=c); eauto.
               
           - clear IHouts.
             do 3 econstructor; splits*.
             + eapply exec_Sseq_1; eauto.
               apply* ClightBigstep.exec_Sset.
             + repeat rewrite* adds_cons_cons. 
         }
  Qed.

  Lemma NoDup_norepet:
    forall {A} (l: list A),
      NoDup l <-> list_norepet l.
  Proof.
    induction l; split; constructor.
    - now inversion H.
    - apply IHl; now inversion H.
    - now inversion H.
    - apply IHl; now inversion H.
  Qed.
  
  Theorem set_comm:
    forall {A} x x' (v v': A) m,
      x <> x' ->
      PTree.set x v (PTree.set x' v' m) = PTree.set x' v' (PTree.set x v m).
  Proof.
    induction x, x', m; simpl; intro Neq;
    ((f_equal; apply IHx; intro Eq; apply Neq; now inversion Eq) || now contradict Neq).
  Qed.
  
  Remark bind_parameters_temps_cons:
    forall x t xs v vs le le',
      bind_parameter_temps ((x, t) :: xs) (v :: vs) le = Some le' ->
      list_norepet (var_names ((x, t) :: xs)) ->
      PTree.get x le' = Some v.
  Proof.
    induction xs as [|[x' t']]; destruct vs;
    introv Bind Norep; inverts Bind as Bind.
    - apply PTree.gss.
    - inverts Norep as Notin Norep.
      apply not_in_cons in Notin.
      apply* IHxs.
      + simpl.
        erewrite set_comm in Bind; iauto.
      + constructor.
        * apply Notin.
        * inverts Norep as Notin' Norep.
          apply Norep.
  Qed.

  Remark bind_parameters_temps_comm:
    forall xs vs s ts o to vself vout x t v le le',
      x <> o ->
      x <> s ->
      (bind_parameter_temps ((s, ts) :: (o, to) :: (x, t) :: xs) (vself :: vout :: v :: vs) le = Some le' <->
      bind_parameter_temps ((x, t) :: (s, ts) :: (o, to) :: xs) (v :: vself :: vout :: vs) le = Some le').
  Proof.
    destruct xs as [|(y, ty)], vs; split; intros ** Bind; inverts Bind; simpl.
    - f_equal. rewrite (set_comm s x); auto.
      apply set_comm; auto.
    - f_equal. rewrite (set_comm x o); auto.
      f_equal. apply set_comm; auto.
    - do 2 f_equal. rewrite (set_comm s x); auto.
      apply set_comm; auto.
    - do 2 f_equal. rewrite (set_comm x o); auto.
      f_equal. apply set_comm; auto.
  Qed.
  
  Remark bind_parameters_temps_implies':
    forall xs vs s ts vself o to vout le le',
      s <> o ->
      ~ InMembers s xs ->
      ~ InMembers o xs ->
      bind_parameter_temps ((s, ts) :: (o, to) :: xs)
                           (vself :: vout :: vs) le = Some le' ->
      PTree.get s le' = Some vself /\ PTree.get o le' = Some vout.
  Proof.
    induction xs as [|(x', t')]; destruct vs;
    introv Neq Notin_s Notin_o Bind.
    - inverts Bind.
      split.
      + rewrite PTree.gso, PTree.gss; auto.
      + rewrite* PTree.gss.
    - inverts Bind.
    - inverts Bind.
    - rewrite bind_parameters_temps_comm in Bind.
      + remember ((s, ts)::(o, to)::xs) as xs' in Bind.
        remember (vself::vout::vs) as vs' in Bind.
        unfold bind_parameter_temps in Bind.
        fold Clight.bind_parameter_temps in Bind.
        rewrite Heqxs', Heqvs' in Bind; clear Heqxs' Heqvs'.
        eapply IHxs; eauto; eapply NotInMembers_cons; eauto.
      + intro Eq.
        apply Notin_o.
        subst o. apply inmembers_eq.
      + intro Eq.
        apply Notin_s.
        subst s. apply inmembers_eq.
  Qed.

  Remark bind_parameters_temps_cons':
    forall xs vs x ty v le le',
      ~ InMembers x xs ->
      bind_parameter_temps xs vs le = Some le' ->
      bind_parameter_temps ((x, ty) :: xs) (v :: vs) le = Some (PTree.set x v le').
  Proof.
    induction xs as [|(x', t')], vs; simpl; intros ** Notin Bind; try discriminate.
    - now inversion Bind.
    - simpl in IHxs.
      rewrite set_comm.
      + apply* IHxs.
      + intro; apply Notin; now left.
  Qed.
  
  Remark bind_parameter_temps_exists:
    forall xs s o ys vs ts to sptr optr,
      s <> o ->
      NoDupMembers xs ->
      ~ InMembers s xs ->
      ~ InMembers o xs ->
      ~ InMembers s ys ->
      ~ InMembers o ys ->
      length xs = length vs ->
      exists le',
        bind_parameter_temps ((s, ts) :: (o, to) :: xs)
                             (sptr :: optr :: vs)
                             (create_undef_temps ys) = Some le'
        /\ Forall (fun xty : ident * typ =>
                    let (x, _) := xty in
                    match le' ! x with
                    | Some v => match_value (adds xs vs v_empty) x v
                    | None => False
                    end) (xs ++ ys).
  Proof.
    induction xs as [|(x, ty)]; destruct vs;
    introv Hso Nodup Nos Noo Nos' Noo' Hlengths; try discriminate.
    - simpl; econstructor; split*.
      unfold match_value, adds; simpl.
      induction ys as [|(y, t)]; simpl; auto.
      assert (y <> s) by (intro; subst; apply Nos'; apply inmembers_eq).
      assert (y <> o) by (intro; subst; apply Noo'; apply inmembers_eq).
      constructor.
      + rewrite PM.gempty.
        do 2 rewrite* PTree.gso.
        rewrite* PTree.gss.
      + apply NotInMembers_cons in Nos'; destruct Nos' as [Nos'].
        apply NotInMembers_cons in Noo'; destruct Noo' as [Noo'].
        specializes IHys Nos' Noo'.
        eapply Forall_impl_In; eauto.
        intros (y', t') Hin Hmatch.
        assert (y' <> s) by (intro; subst; apply Nos'; eapply In_InMembers; eauto).
        assert (y' <> o) by (intro; subst; apply Noo'; eapply In_InMembers; eauto).
        do 2 rewrite PTree.gso in *; auto.      
        destruct (ident_eqb y' y) eqn: E.
        * apply ident_eqb_eq in E; subst y'.
          rewrite PTree.gss.
          now rewrite PM.gempty.
        * apply ident_eqb_neq in E.
          rewrite* PTree.gso.
    - inverts Hlengths as Hlengths.
      inversion Nodup as [|? ? ? Notin Nodup']; subst.
      edestruct IHxs with (s:=s) (ts:=ts) (o:=o) (to:=to) (sptr:=sptr) (optr:=optr)
        as (le' & Bind & ?); eauto.
      + eapply NotInMembers_cons; eauto.
      + eapply NotInMembers_cons; eauto.
      + assert (x <> s) by (intro; subst; apply Nos; apply inmembers_eq).
        assert (x <> o) by (intro; subst; apply Noo; apply inmembers_eq).      
        exists (PTree.set x v le'); split.
        * rewrite* bind_parameters_temps_comm.
          apply* bind_parameters_temps_cons'.
          simpl; intros [|[|]]; auto.
        *{ rewrite <-app_comm_cons.
           constructor.
           - rewrite PTree.gss.
             unfold match_value, adds; simpl.
             now rewrite PM.gss.
           - eapply Forall_impl_In; eauto.
             intros (x', t') Hin MV.
             destruct (ident_eqb x' x) eqn: E.
             + rewrite ident_eqb_eq in E; subst x'.
               rewrite PTree.gss; unfold match_value, adds; simpl.
               now rewrite PM.gss.
             + rewrite ident_eqb_neq in E.
               rewrite PTree.gso.
               destruct le' ! x'; try contradiction.
               unfold match_value, adds in MV.
               unfold match_value, adds; simpl.
               rewrite* PM.gso.
               exact E.
         }
  Qed.
  
  Remark alloc_implies:
    forall vars x b t e m e' m', 
      ~ InMembers x vars ->
      alloc_variables tge (PTree.set x (b, t) e) m vars e' m' ->
      e' ! x = Some (b, t).
  Proof.
    induction vars as [|(x', t')]; intros ** Notin H;
    inverts H as ? Halloc.
    - apply PTree.gss.
    - rewrite <-set_comm in Halloc.
      + apply* IHvars.
        eapply NotInMembers_cons; eauto.
      + intro; subst x; apply Notin; apply inmembers_eq.
  Qed.

  (* Remark alloc_InMembers: *)
  (*   forall vars e m e' m',  *)
  (*     alloc_variables tge e m vars e' m' -> *)
  (*     (forall x, *)
  (*         InMembers x (PTree.elements e') <-> InMembers x (PTree.elements e) \/ InMembers x vars). *)
  (* Proof. *)
  (*   induction vars as [|(y, t)]; intros ** Alloc x;     *)
  (*   inverts Alloc as ? Alloc. *)
  (*   - split*. simpl. *)
  (*     intros [?|?]; auto. *)
  (*     contradiction. *)
  (*   - specialize (IHvars _ _ _ _ Alloc x). *)
  (*     destruct IHvars as [In_Or Or_In]. *)
  (*     split.     *)
  (*     + intro Hin. *)
  (*       apply In_Or in Hin. *)
  (*       destruct Hin as [Hin|?]. *)
  (*       *{ destruct (ident_eqb x y) eqn: E. *)
  (*          - apply ident_eqb_eq in E. *)
  (*            subst y. *)
  (*            right; apply inmembers_eq. *)
  (*          - apply ident_eqb_neq in E. *)
  (*            apply InMembers_In in Hin. *)
  (*            destruct Hin as ((b, t') & Hin). *)
  (*            apply PTree.elements_complete in Hin. *)
  (*            rewrite* PTree.gso in Hin. *)
  (*            apply PTree.elements_correct in Hin. *)
  (*            left; eapply In_InMembers; eauto. *)
  (*        } *)
  (*       * right; apply inmembers_cons; auto. *)
  (*     + intros [Hin|Hin]; apply Or_In. *)
  (*       *{ destruct (ident_eqb x y) eqn: E. *)
  (*          - apply ident_eqb_eq in E. *)
  (*            subst y. *)
  (*            left. *)
  (*            apply In_InMembers with (b:=(b1, t)). *)
  (*            apply PTree.elements_correct.              *)
  (*            rewrite* PTree.gss. *)
  (*          - apply ident_eqb_neq in E. *)
  (*            left. *)
  (*            apply InMembers_In in Hin. *)
  (*            destruct Hin as ((b', t') & Hin). *)
  (*            apply In_InMembers with (b:=(b', t')). *)
  (*            apply PTree.elements_correct.              *)
  (*            rewrite* PTree.gso. *)
  (*            apply* PTree.elements_complete. *)
  (*        } *)
  (*       *{ inverts Hin. *)
  (*          - left. *)
  (*            apply In_InMembers with (b:=(b1, t)). *)
  (*            apply PTree.elements_correct.              *)
  (*            rewrite* PTree.gss. *)
  (*          - now right.  *)
  (*        } *)
  (* Qed. *)
  
  Remark In_drop_block:
    forall elts x t,
      In (x, t) (map drop_block elts) ->
      exists b, In (x, (b, t)) elts.
  Proof.
    induction elts as [|(x', (b', t'))]; simpl; intros ** Hin.
    - contradiction.
    - destruct Hin as [Eq|Hin].
      + inverts Eq.
        exists b'; now left.
      + apply IHelts in Hin.
        destruct Hin as [b Hin].
        exists b; now right.
  Qed.

  Remark drop_block_In:
    forall elts x b t,
      In (x, (b, t)) elts ->
      In (x, t) (map drop_block elts).
  Proof.
    induction elts as [|(x', (b', t'))]; simpl; intros ** Hin.
    - contradiction.
    - destruct Hin as [Eq|Hin].
      + inverts Eq.
        now left.
      + apply IHelts in Hin.
        now right.
  Qed.

  Remark get_set_same:
    forall {A} x e v (v': A),
      (PTree.set x v e) ! x = Some v' -> v = v'.
  Proof.
    induction x, e; simpl; (eauto || now inversion 1).
  Qed.
  
  Remark alloc_In:
    forall vars e m e' m',
      alloc_variables tge e m vars e' m' ->
      NoDupMembers vars ->
      (forall x t,
          In (x, t) (map drop_block (PTree.elements e')) <->
          (In (x, t) (map drop_block (PTree.elements e)) /\ (forall t', In (x, t') vars -> t = t'))
          \/ In (x, t) vars).
  Proof.
    intro vars.
    remember vars as vars'.
    assert (exists vars'', vars = vars'' ++ vars') as Hvars
      by (exists (@nil (ident * type)); simpl; auto).
    clear Heqvars'.
    induction vars' as [|(y, ty)]; intros ** Alloc Nodup x t;
    inverts Alloc as ? Alloc; inverts Nodup as Notin Nodup.
    - split; simpl.
      + intros. left; split*.
        intros; contradiction.
      + intros [[? ?]|?]; auto.
        contradiction.
    - destruct Hvars as [vars'' Hvars].
      edestruct IHvars' with (x:=x) (t:=t) as [In_Or Or_In]; eauto.
      1: exists (vars'' ++ [(y, ty)]); rewrite app_last_app; auto.
      clear IHvars'.
      split.
      + intro Hin.
        apply In_Or in Hin.
        destruct Hin as [[Hin Ht]|?].
        *{ destruct (ident_eqb x y) eqn: E.
           - apply ident_eqb_eq in E.
             subst y.
             apply In_drop_block in Hin.
             destruct Hin as [b Hin].
             apply PTree.elements_complete in Hin.
             apply get_set_same in Hin.
             inverts Hin.
             right; apply in_eq.
           - apply ident_eqb_neq in E.
             apply In_drop_block in Hin.
             destruct Hin as [b Hin].
             apply PTree.elements_complete in Hin.
             rewrite* PTree.gso in Hin.
             apply PTree.elements_correct in Hin.
             left; split.
             + eapply drop_block_In; eauto.
             + intros t' [Eq|Hin'].
               * inverts Eq. now contradict E.
               * now apply Ht.
               
         }
        * right; apply in_cons; auto.
      + intros [[Hin Ht]|Hin]; apply Or_In.
        *{ left; split.
           - destruct (ident_eqb x y) eqn: E.
             + apply ident_eqb_eq in E.
               subst y.
               apply drop_block_In with (b:=b1).
               apply PTree.elements_correct.
               rewrite* PTree.gss.
               repeat f_equal.
               symmetry; apply Ht.
               apply in_eq.
             + apply ident_eqb_neq in E.
               apply In_drop_block in Hin.
               destruct Hin as [b Hin].
               apply drop_block_In with (b:=b).
               apply PTree.elements_correct.
               rewrite* PTree.gso.
               apply* PTree.elements_complete.
           - intros.
             apply Ht.
             now apply in_cons.
         }
        *{ inverts Hin as Eq.
           - inverts Eq.
             left; split.
             + apply drop_block_In with (b:=b1).
               apply PTree.elements_correct.
               rewrite* PTree.gss.
             + intros ** Hin.
               contradict Hin.
               apply NotInMembers_NotIn; auto. 
           - now right.
         }
  Qed.
  
  Remark alloc_mem_vars:
    forall vars e m e' m' P,
      m |= P ->
      NoDupMembers vars ->
      alloc_variables tge e m vars e' m' ->
      m' |= sepall (range_inst_env e') (var_names vars) ** P.
  Proof.
    induction vars as [|(y, t)]; intros ** Hrep Nodup Alloc;  
    inverts Alloc as ? Alloc; simpl.
    - now rewrite <-sepemp_left.
    - inverts Nodup.
      unfold range_inst_env at 1.
      erewrite alloc_implies; eauto.
      rewrite sep_assoc, sep_swap.
      apply* IHvars.
      apply* alloc_rule.
      + omega.
      + admit.
  Qed.

  Remark alloc_permutation:
    forall vars m e' m',
      alloc_variables tge empty_env m vars e' m' ->
      NoDupMembers vars ->
      Permutation vars (map drop_block (PTree.elements e')).
  Proof.
    intros ** Alloc Nodup.
    pose proof (alloc_In _ _ _ _ _ Alloc) as H.
    apply NoDup_Permutation.
    - apply NoDupMembers_NoDup; auto.
    - pose proof (PTree.elements_keys_norepet e') as Norep.
      clear H.
      induction (PTree.elements e') as [|(x, (b, t))]; simpl in *; constructor.
      + inverts Norep as Notin Norep.
        clear IHl.
        induction l as [|(x', (b', t'))]; simpl in *.
        * intro; contradiction.
        *{ intros [Eq | Hin].
           - inverts Eq. apply Notin. now left.
           - inverts Norep. apply IHl; auto.
         }
      + inverts Norep as Notin Norep.
        apply IHl; auto. 
    - intros (x, t).
      specialize (H Nodup x t).
      intuition. 
  Qed.

  Remark get_leaf:
    forall {A: Type} x, 
      (@PTree.Leaf A) ! x = None.
  Proof.
     intros; now destruct x. 
  Qed.
  
  Remark In_singleton:
    forall {A} (y x: A),
      In y [x] <-> y = x.
  Proof.
    split; intro H.
    - simpl in H; destruct H; auto.
      contradiction.
    - subst x; apply in_eq.
  Qed.
  
  Remark equiv_eq_singleton:
    forall {A} (x: A) l,
      NoDup l ->
      ([x] = l <-> (forall y, In y l <-> In y [x])).
  Proof.
    intros ** Nodup.
    split.
    - intros; subst l; split; auto.
    - destruct l; intro H.
      + specialize (H x); destruct H as [? H'].
        exfalso; apply H'; now left.
      + inverts Nodup as Notin Nodup.
        destruct l.
        * specialize (H x); do 2 rewrite In_singleton in H.
          f_equal; now apply H.
        *{ pose proof H as H'.
           specialize (H a); rewrite In_singleton in H.
           specialize (H' a0); rewrite In_singleton in H'.
           destruct H as [Ha].
           destruct H' as [Ha0].
           assert (a = a0).
           - transitivity x.
             + apply Ha, in_eq.
             + symmetry; apply Ha0, in_cons, in_eq.
           - exfalso; apply Notin.
             subst; apply in_eq.
         }
  Qed.
  
  Remark elements_set_leaf:
    forall {A} x (v: A),
      PTree.elements (PTree.set x v PTree.Leaf) = [(x, v)].
  Proof.
    symmetry; rewrite equiv_eq_singleton.
    - intros (y, a).
      rewrite In_singleton.
      split; intro H.
      + apply PTree.elements_complete in H.
        destruct (ident_eqb x y) eqn: E.
        * apply ident_eqb_eq in E; subst y.
          apply get_set_same in H.
          now f_equal.
        * apply ident_eqb_neq in E.
          rewrite PTree.gso in H; auto.
          rewrite get_leaf in H; discriminate.
      + inverts H.
        apply PTree.elements_correct, PTree.gss.
    - apply NoDup_map_inv with (f:=fst).
      apply NoDup_norepet.
      apply PTree.elements_keys_norepet.
  Qed.
  
  Lemma set_nodupmembers:
    forall x (e: env) b1 t,
      NoDupMembers (map snd (PTree.elements e)) ->
      (forall b, InMembers b (map snd (PTree.elements e)) -> b <> b1) ->
      NoDupMembers (map snd (PTree.elements (PTree.set x (b1, t) e))).
  Proof.
    induction e; simpl in *; intros ** Nodup Diff.
    - rewrite elements_set_leaf; simpl.
      constructor; auto.
    - admit.
  Qed.
  
  Remark alloc_nodupmembers:
    forall vars e m e' m',
      alloc_variables tge e m vars e' m' ->
      NoDupMembers (map snd (PTree.elements e)) ->
      (forall b, InMembers b (map snd (PTree.elements e)) -> Mem.valid_block m b) ->
      NoDupMembers (map snd (PTree.elements e')).
  Proof.
    induction vars as [|(x, t)]; intros ** Alloc Nodup Valid; inverts Alloc as Alloc; auto.
    apply IHvars with (e:=PTree.set x (b1, t) e) (m:=m1) (m':=m'); auto.
    - apply set_nodupmembers; auto.
      intros b Hinb. 
      apply Valid in Hinb.
      eapply Mem.valid_not_valid_diff; eauto.
      eapply Mem.fresh_block_alloc; eauto.
    - intros b Hinb.
      destruct (eq_block b b1) as [Eq|Neq].
      + subst b1. eapply Mem.valid_new_block; eauto.
      + admit.
  Qed.
  
  Remark alloc_exists:
    forall vars e m,
      NoDupMembers vars ->
      exists e' m',
        alloc_variables tge e m vars e' m'.
  Proof.
    induction vars as [|(x, t)]; intros ** Nodup.
    - exists e m; constructor.  
    - inverts Nodup as Notin.
      destruct (Mem.alloc m 0 (Ctypes.sizeof gcenv t)) as (m1 & b) eqn: Eq.
      edestruct IHvars with (e:=PTree.set x (b, t) e) (m:=m1)
        as (e' & m' & Halloc); eauto.
      exists e' m'; econstructor; eauto.
  Qed.

  Remark Permutation_fst:
    forall vars elems,
      Permutation vars elems ->
      Permutation (var_names vars) (map fst elems).
  Proof.
    intros ** Perm.
    induction Perm; simpl; try constructor; auto.
    transitivity (map fst l'); auto.
  Qed.

  Remark map_fst_drop_block:
    forall elems,
      map fst (map drop_block elems) = map fst elems.
  Proof.
    induction elems as [|(x, (b, t))]; simpl; auto.
    now f_equal.
  Qed.

  Lemma Permutation_Forall:
    forall {A} (l l': list A) P,
      Permutation l l' ->
      Forall P l ->
      Forall P l'.
  Proof.
    induction 1; inversion 1; auto.
    inversion H3.
    repeat constructor; auto.
  Qed.
  
  (* Lemma  *)
  Lemma alloc_result:
    forall f vars m P,
      vars = get_instance_methods f.(m_body) ->
      Forall (fun xt: positive * type =>
                let (_, t) := xt in
                exists (id : AST.ident) (co : composite),
                  t = Tstruct id noattr /\
                  gcenv ! id = Some co /\
                  co_su co = Struct /\
                  NoDupMembers (co_members co) /\
                  (forall (x' : AST.ident) (t' : type),
                      In (x', t') (co_members co) ->
                      exists chunk : AST.memory_chunk,
                        access_mode t' = By_value chunk /\
                        (align_chunk chunk | alignof gcenv t'))) (make_out_vars vars) ->
      NoDupMembers (make_out_vars vars) ->
      m |= P ->
      exists e' m',
        alloc_variables tge empty_env m (make_out_vars vars) e' m'
        /\ m' |= subrep f e'
             ** (subrep f e' -* subrep_range e')
             ** P.
  Proof.
    intros ** Heq Hforall Nodup Hrep; subst.
    pose proof (alloc_exists _ empty_env m Nodup) as Alloc.
    destruct Alloc as (e' & m' & Alloc).
    exists e' m'; split*.
    eapply alloc_mem_vars in Hrep; eauto.
    pose proof Alloc as Perm.
    apply alloc_permutation in Perm; auto.
    pose proof Perm as Perm_fst.
    apply Permutation_fst in Perm_fst.
    rewrite map_fst_drop_block in Perm_fst.
    rewrite Perm_fst in Hrep.
    rewrite <-subrep_range_eqv in Hrep.
    repeat rewrite subrep_eqv; auto.
    rewrite range_wand_equiv in Hrep.
    - now rewrite sep_assoc in Hrep.
    - eapply Permutation_Forall; eauto. 
    - eapply alloc_nodupmembers; eauto.
      + unfold PTree.elements; simpl; constructor.
      + intros ** Hin.
        unfold PTree.elements in Hin; simpl in Hin.
        contradiction.
  Qed.

  Lemma compat_funcall_pres:
    forall f sb sofs ob vs vargs c prog' prog'' o owner d me me' tself tout callee instco m P,
      c.(c_name) <> owner.(c_name) ->
      In (o, c.(c_name)) owner.(c_objs) ->
      field_offset gcenv o (make_members owner) = Errors.OK d ->
      (0 <= (Int.unsigned sofs) + d <= Int.max_unsigned)%Z ->
      (0 <= d <= Int.max_unsigned)%Z ->
      find_class owner.(c_name) prog = Some (owner, prog') ->
      find_class c.(c_name) prog = Some (c, prog'') ->
      In callee c.(c_methods) ->
      length (fn_params f) = length vargs ->
      fn_params f = (self_id, tself) :: (out_id, tout) :: callee.(m_in) ->
      fn_vars f = (make_out_vars (get_instance_methods callee.(m_body))) ->
      fn_temps f = m_vars callee ->
      list_norepet (var_names f.(fn_params)) ->
      list_norepet (var_names f.(fn_vars)) ->
      vargs = (Vptr sb (Int.add sofs (Int.repr d))) :: (Vptr ob Int.zero) :: vs ->
      mfind_inst o me = Some me' ->
      gcenv ! (prefix (m_name callee) (c_name c)) = Some instco ->
      m |= staterep gcenv prog owner.(c_name) me sb (Int.unsigned sofs)
          ** blockrep gcenv v_empty (co_members instco) ob
          ** P ->
      exists e_fun le_fun m_fun ws xs,
        bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le_fun
        /\ alloc_variables tge empty_env m f.(fn_vars) e_fun m_fun
        /\ le_fun ! self_id = Some (Vptr sb (Int.add sofs (Int.repr d)))
        /\ le_fun ! out_id = Some (Vptr ob Int.zero)
        /\ c_objs owner = ws ++ (o, c_name c) :: xs
        /\ m_fun |= sepall (staterep_mems gcenv owner me sb (Int.unsigned sofs)) (c_mems owner)
                  ** staterep gcenv prog (c_name c) me' sb (Int.unsigned (Int.add sofs (Int.repr d)))
                  ** sepall (staterep_objs gcenv prog' owner me sb (Int.unsigned sofs)) (ws ++ xs)
                  ** blockrep gcenv (adds (m_in callee) vs v_empty) (co_members instco) ob
                  ** subrep callee e_fun
                  ** (subrep callee e_fun -* subrep_range e_fun)
                  ** varsrep callee (adds (m_in callee) vs v_empty) le_fun
                  ** P
        /\ (0 <= Int.unsigned (Int.add sofs (Int.repr d)) <= Int.max_unsigned)%Z.     
  Proof.
    intros ** ? Hin Offs ? ? Findowner Findc Hcallee Hlengths Hparams Hvars Htemps
           Norep_par Norep_vars ? Find_inst ? Hrep.
    subst vargs; rewrite Hparams, Hvars, Htemps in *.
    pose proof (m_self_id callee) as Notin_s.
    pose proof (m_out_id callee) as Notin_o.
    assert (~ InMembers self_id (m_in callee)) by (apply NotInMembers_app in Notin_s; tauto). 
    assert (~ InMembers out_id (m_in callee)) by (apply NotInMembers_app in Notin_o; tauto).
    assert (~ InMembers self_id (m_vars callee)) by
        (rewrite NotInMembers_app_comm, <-app_assoc in Notin_s; apply NotInMembers_app in Notin_s; tauto).
    assert (~ InMembers out_id (m_vars callee)) by
        (rewrite NotInMembers_app_comm, <-app_assoc in Notin_o; apply NotInMembers_app in Notin_o; tauto).

    forwards* (le_fun & Bind & Hinputs):
      (bind_parameter_temps_exists (m_in callee) self_id out_id (m_vars callee)) self_not_out.
    - pose proof (m_nodup callee) as Nodup.
      rewrite NoDupMembers_app in Nodup.
      now apply NoDupMembers_app_r in Nodup.
    - simpl in Hlengths. inversion Hlengths; eauto.
    - forwards* (e_fun & m_fun & ? & Hm_fun): (alloc_result callee).
      + skip.
      + unfold var_names in Norep_vars.
        now rewrite fst_NoDupMembers, NoDup_norepet. 
      + forwards* (? & ?): (bind_parameters_temps_implies' (m_in callee)) self_not_out.
        pose proof Hin as Hin'.
        apply sepall_in in Hin.
        destruct Hin as (ws & xs & Hin & Heq).             
        exists e_fun le_fun m_fun ws xs; splits*.
        *{ do 5 rewrite <-sep_assoc; rewrite sep_swap.
           apply sep_pure; split*.
           rewrite sep_assoc, sep_swap, sep_assoc, sep_swap23, sep_swap.
           eapply sep_imp; eauto.
           apply sep_imp'; auto.
           rewrite sep_assoc.
           apply sep_imp'; auto.
           - edestruct find_class_app with (1:=Findowner)
               as (pre_prog & Hprog & FindNone); eauto.
             rewrite Hprog in WD.
             eapply welldef_not_class_in in WD; eauto.
             rewrite staterep_skip; eauto.
             simpl.
             rewrite ident_eqb_refl.
             rewrite sep_assoc.
             apply sep_imp'; auto.
             rewrite Heq, Offs.
             apply sep_imp'; auto.
             unfold instance_match; rewrite Find_inst.
             erewrite <-staterep_skip_cons; eauto.
             erewrite <-staterep_skip_app; eauto.
             rewrite <-Hprog.
             unfold Int.add; repeat rewrite* Int.unsigned_repr.
           - apply sep_imp'; auto.
             erewrite <-output_match; eauto.
             apply* blockrep_nodup.
             pose proof (m_nodup callee) as Nodup.
             rewrite app_assoc, NoDupMembers_app, app_assoc, NoDupMembers_app in Nodup.
             now apply NoDupMembers_app_r, NoDupMembers_app in Nodup.   
         }
        * unfold Int.add; repeat rewrite* Int.unsigned_repr.
        * unfold Int.add; repeat rewrite* Int.unsigned_repr. 
  Qed.
  
  Remark type_pres':
    forall f c caller es,
      Forall2 (fun e x => typeof e = snd x) es f.(m_in) ->
      type_of_params f.(m_in) =
      list_type_to_typelist (map Clight.typeof (map (translate_exp c caller) es)).
  Proof.
    intro f.
    induction (m_in f) as [|(x, t)]; introv Heq;
    inversion_clear Heq as [|? ? ? ? Ht]; simpl; auto.
    f_equal.
    - simpl in Ht; rewrite <-Ht.
      rewrite* type_pres.
    - apply* IHl.
  Qed.

  Lemma free_exists:
    forall e f m P,
      m |= subrep f e
        ** (subrep f e -* subrep_range e)
        ** P ->
      exists m',
        Mem.free_list m (blocks_of_env tge e) = Some m'
        /\ m' |= P.
  Proof.
    intros ** Hrep.
    rewrite <-sep_assoc, sep_unwand in Hrep.
    - revert P m Hrep.
      unfold subrep_range, blocks_of_env.
      induction (PTree.elements e) as [|(x,(b,ty))];
        simpl; intros P m Hrep.
      + exists m; split*.
        rewrite* sepemp_left.
      + rewrite sep_assoc in Hrep.
        apply free_rule in Hrep.
        destruct Hrep as (m1 & Hfree & Hm1).
        rewrite Hfree.
        apply IHl; auto.
    - unfold subrep.
      induction (make_out_vars (get_instance_methods (m_body f))) as [|(x, t)]; simpl; auto.
      apply decidable_footprint_sepconj; auto.
      destruct (e ! x) as [(b, t')|]; auto.
      destruct t'; auto.
      destruct (type_eq t (Tstruct i a)); auto.
      destruct (gcenv ! i); auto.
  Qed.

  Lemma subrep_extract:
    forall f f' e m o c' P,
      m |= subrep f e ** P ->
      In (o, c', f') (get_instance_methods f.(m_body)) ->
      exists b co ws xs,
        e ! o = Some (b, type_of_inst (prefix f' c'))
        /\ gcenv ! (prefix f' c') = Some co
        /\ make_out_vars (get_instance_methods (m_body f)) = ws ++ (o, type_of_inst (prefix f' c')) :: xs
        /\ m |= blockrep gcenv v_empty (co_members co) b
            ** sepall (subrep_inst_env e) (ws ++ xs)
            ** P.
  Proof.
    intros ** Hrep Hin.
    unfold subrep, subrep_inst in *.
    assert (In (o, type_of_inst (prefix f' c')) (make_out_vars (get_instance_methods (m_body f)))) as Hin'.
    - apply in_map with
      (f:=fun x => let '(o0, cid, f0) := x in (o0, type_of_inst (prefix f0 cid))) in Hin.
      unfold make_out_vars; auto.
    - clear Hin.
      apply sepall_in in Hin'; destruct Hin' as (ws & xs & Hin & Heq). 
      repeat rewrite Heq in Hrep.
      pose proof Hrep as Hrep'.
      do 2 apply sep_proj1 in Hrep.
      unfold subrep_inst_env in *.
      destruct e ! o; [|contradict Hrep].
      destruct p as (oblk, t).
      destruct t; try now contradict Hrep.
      destruct (type_eq (type_of_inst (prefix f' c')) (Tstruct i a)) as [Eq|]; [|contradict Hrep].
      unfold type_of_inst in Eq.
      inverts Eq.
      destruct gcenv ! (prefix f' c'); [|contradict Hrep].
      rewrite sep_assoc in Hrep'.
      exists oblk c ws xs; splits*.
  Qed.
  
  Theorem correctness:
    (forall p S1 s S2,
        stmt_eval p S1 s S2 ->
        sub_prog p prog ->
        forall c prog' f
          (WF: well_formed_stmt c f s)
          (Find: find_class c.(c_name) prog = Some (c, prog'))
          (Hf: In f c.(c_methods)),
        forall e1 le1 m1 sb sofs outb outco P
          (MS: m1 |= match_states c f S1 (e1, le1) sb sofs outb outco ** P),
        exists le2 m2 T,
          exec_stmt tge (function_entry2 tge) e1 le1 m1
                    (translate_stmt prog c f s) T le2 m2 Out_normal
          /\ m2 |= match_states c f S2 (e1, le2) sb sofs outb outco ** P)
    /\
    (forall p me1 clsid fid vs me2 rvs,
        stmt_call_eval p me1 clsid fid vs me2 rvs ->
        sub_prog p prog ->
        forall owner c caller callee prog' prog'' S e1 le1 m1 o cf ptr_f sb
          d outb outco oty sofs binst instco P,
          find_class clsid prog = Some (c, prog') ->
          find_method fid c.(c_methods) = Some callee ->
          m1 |= staterep gcenv prog owner.(c_name) (fst S) sb (Int.unsigned sofs)
               ** blockrep gcenv (snd S) outco.(co_members) outb
               ** subrep caller e1
               ** varsrep caller (snd S) le1
               ** P ->
          find_class owner.(c_name) prog = Some (owner, prog'') ->
          In caller owner.(c_methods) ->
          Globalenvs.Genv.find_symbol tge fid = Some ptr_f ->
          Globalenvs.Genv.find_funct_ptr tge ptr_f = Some (Ctypes.Internal cf) ->
          length cf.(fn_params) = 2 + length vs ->
          find_inst S o me1 ->
          oty = type_of_inst (prefix fid clsid) ->
          e1 ! o = Some (binst, oty) ->
          In (o, clsid) owner.(c_objs) ->
          In (o, clsid, fid) (get_instance_methods caller.(m_body)) ->
          field_offset gcenv o (make_members owner) = Errors.OK d ->
          gcenv ! (prefix fid clsid) = Some instco ->
          well_formed_stmt c callee callee.(m_body) ->
          In callee (c_methods c) ->
          eval_expr tge e1 le1 m1 (ptr_obj owner.(c_name) clsid o) (Vptr sb (Int.add sofs (Int.repr d))) ->
          exists m2 T ws xs,
            eval_funcall tge (function_entry2 tge) m1 (Internal cf)
                         ((Vptr sb (Int.add sofs (Int.repr d))) :: (Vptr binst Int.zero) :: vs) T m2 Vundef
            /\ make_out_vars (get_instance_methods (m_body caller)) = ws ++ (o, type_of_inst (prefix fid clsid)) :: xs
            /\ m2 |= staterep gcenv prog owner.(c_name) (madd_obj o me2 (fst S)) sb (Int.unsigned sofs)
                   ** blockrep gcenv (snd S) outco.(co_members) outb
                   ** blockrep gcenv (adds callee.(m_out) rvs v_empty) instco.(co_members) binst
                   ** sepall (subrep_inst_env e1) (ws ++ xs)
                   ** varsrep caller (snd S) le1
                   ** P).
  Proof.
    clear TRANSL main_node_exists.
    apply stmt_eval_call_ind;
      [| |introv ? ? ? ? Hifte|introv ? HS1 ? HS2|introv ? Evs ? Hrec_eval|
       |introv Find Findmeth ? Hrec_exec Findvars ? Find' Findmeth' Hrep;
         introv Findowner ? Hgetptrf Hgetcf ? Findinst Hinstty Hbinst ? Hin;
         introv Offs Hinstco];
      intros;
      try inversion_clear WF as [? ? Hvars|? ? Hin| |
                                 |? ? ? ? ? ? ? ? ? ? ? ? Hin ? ? ? Find' Findmeth|];
      try (rewrite match_states_conj in MS; destruct MS as (Hrep & Hself & Hout & Houtco & ?)).
    
    (* Assign x e : "x = e" *)
    - simpl translate_stmt; unfold assign.
      destruct (existsb (fun out => ident_eqb (fst out) x) f.(m_out)) eqn: E.

      (* out->x = e *)
      + (* get the 'out' variable left value evaluation *)
        rewrite sep_swap in Hrep.
        edestruct evall_out_field; eauto.
        
        (* get the updated memory *)
        rewrite sep_swap34, sep_swap23, sep_swap in Hrep.
        edestruct match_states_assign_out as (m2 & ? & Hm2); jauto.
        rewrite sep_swap, sep_swap23, sep_swap34, sep_swap in Hrep.
        
        exists le1 m2 E0; split*.
        apply* ClightBigstep.exec_Sassign.
        * rewrite* type_pres; apply* sem_cast_same; apply* exp_eval_valid.
        *{ apply* assign_loc_value.
           - simpl; apply* exp_eval_access.
           - rewrite* Int.add_zero_l.
         }
        * rewrite match_states_conj. 
          rewrite sep_swap34, sep_swap23, sep_swap, sep_swap23; auto.  
           
      (* x = e *)
      + exists (PTree.set x v le1) m1 E0; split.
        * apply* ClightBigstep.exec_Sset.
          
        *{ pose proof (m_out_id f); pose proof (m_self_id f).
           rewrite match_states_conj; splits*.
           - rewrite sep_swap4 in *.
             apply* match_states_assign_tempvar.
           - rewrite* PTree.gso.
             eapply In_InMembers, InMembers_neq in Hvars; eauto.
           - rewrite* PTree.gso.
             eapply In_InMembers, InMembers_neq in Hvars; eauto.
         }
         
    (* AssignSt x e : "self->x = e"*)
    - (* get the 'self' variable left value evaluation *)
      edestruct evall_self_field as (? & ? & Hoffset & ?); eauto.

      (* get the updated memory *)
      edestruct match_states_assign_state as (m2 & ?); jauto.
      
      exists le1 m2 E0; split.
      + apply* ClightBigstep.exec_Sassign.
        * rewrite* type_pres; apply* sem_cast_same; apply* exp_eval_valid.
        *{ apply* assign_loc_value.
           - simpl; apply* exp_eval_access.
           - unfold Int.add.
             rewrite* Int.unsigned_repr.
         }
      + rewrite* match_states_conj. 
        
    (* Ifte e s1 s2 : "if e then s1 else s2" *)
    - edestruct Hifte; destruct_conjs; eauto; [destruct* b| |]. 
      + rewrite* match_states_conj.
      + do 3 econstructor; split*.
        apply* exec_Sifthenelse.
        * erewrite type_pres, bool_val_ptr; eauto.
        * destruct* b.
      
    (* Comp s1 s2 : "s1; s2" *)
    - edestruct HS1; destruct_conjs; eauto.
      + rewrite* match_states_conj.
      + edestruct HS2; destruct_conjs; eauto.
        do 3 econstructor; split*.
        apply* exec_Sseq_1.
      
    (* Step_ap y ty clsid o [e1; ... ;en] : "y = clsid_step(&(self->o), e1, ..., en)" *)
    - (* get the Clight corresponding function *)
      forwards* Hin': find_class_In Find'.
      edestruct methods_corres with (e:=e1)
        as (ptr_f & cf & ? & ? & ? & Hparams & Hreturn & Hcc & ?); eauto.

      forwards Eq: find_class_name Find'.
      forwards Eq': find_method_name Findmeth.
      rewrite Eq, Eq' in *.

      (* the *self parameter *)
      edestruct eval_self_inst with (1:=Find) (e:=e1) as (? & ? & ?); eauto.

      (* the *out parameter *)
      rewrite sep_swap3 in Hrep.
      edestruct subrep_extract as (oblk & instco & ? & ? & Hoblk & Hinstco & ?); eauto.
      
      (* recursive funcall evaluation *)
      rewrite sep_swap3 in Hrep.
      edestruct Hrec_eval with (owner:=c) (e1:=e1) (m1:=m1) (le1:=le1) (instco:=instco)
        as (m2 & T & xs & ws & ? & Heq & Hm2); eauto.
      + symmetry; erewrite <-Forall2_length; eauto.
        rewrite Hparams; simpl; repeat f_equal.
        eapply Forall2_length; eauto.
      + eapply find_method_In; eauto.
      + (* output assignments *)
        clear Hrec_eval.      
        rewrite sep_swap3, sep_swap45, sep_swap34 in Hm2.
        edestruct exec_funcall_assign with (ys:=ys) (m1:=m2)
          as (le3 & m3 & ? & ? & Hm3 & ? & ?) ; eauto.
        * transitivity (length ys); auto. eapply Forall2_length; eauto.
        *{ exists le3 m3; econstructor; split*.
           - simpl.
             unfold binded_funcall.
             rewrite Find', Findmeth.
             eapply exec_Sseq_1 with (m1:=m2); eauto.
             assert (forall v, le1 = set_opttemp None v le1) as E by reflexivity.
             erewrite E at 2.
             eapply exec_Scall; eauto.
             + reflexivity.
             + simpl.
               eapply eval_Elvalue.
               * apply* eval_Evar_global.
               * apply* deref_loc_reference.               
             + apply find_method_In in Findmeth.
               do 2 (econstructor; eauto).
               applys* exprs_eval_simu Find.
             + unfold Genv.find_funct.
               destruct* (Int.eq_dec Int.zero Int.zero) as [|Neq].
               exfalso; apply* Neq.
             + simpl. unfold type_of_function;
               rewrite Hparams, Hreturn, Hcc; simpl; repeat f_equal.
               apply* type_pres'.
           - rewrite match_states_conj; splits*; simpl.
             rewrite sep_swap34.
             rewrite sep_swap4 in Hm3.
             eapply sep_imp; eauto.
             apply sep_imp'; auto.
             apply sep_imp'; auto.
             rewrite <-sep_assoc.
             apply sep_imp'; auto.
             unfold subrep.
             rewrite (sepall_breakout _ _ _ _ (subrep_inst_env e1) Heq).
             apply sep_imp'; auto.
             unfold subrep_inst_env.
             rewrite Hoblk.
             unfold type_of_inst.
             rewrite Hinstco.
             rewrite type_eq_refl.
             apply* blockrep_any_empty.
         }
         
    (* Skip : "skip" *)
    - exists le1 m1 E0; split.
      + eapply exec_Sskip.
      + rewrite* match_states_conj. 
        
    (* funcall *)
    - forwards* Find'': find_class_sub_same Find.
      rewrite Find' in Find''; inverts Find''.
      rewrite Findmeth in Findmeth'; inverts Findmeth'.

      (* get the clight function *)
      edestruct methods_corres with (e:=e1)
        as (ptr_f' & cf' & Hgetptrf' & ? & Hgetcf' & ? & Hret & ? & ? & ? & ? & ? & ? & Htr); eauto.
      rewrite Hgetptrf' in Hgetptrf; inverts Hgetptrf.
      rewrite Hgetcf' in Hgetcf; inverts Hgetcf.

      forwards Eq: find_class_name Find.
      forwards Eq': find_method_name Findmeth.
      rewrite <-Eq, <-Eq' in *.

      edestruct find_class_app with (1:=Findowner)
        as (pre_prog & Hprog & FindNone); eauto.
      rewrite Hprog in WD.
      assert (c_name c <> c_name owner) by (apply* welldef_not_same_name).

      (* extract the out structure *)
      rewrite sep_swap23, sep_swap in Hrep.
      eapply subrep_extract in Hrep; eauto.
      destruct Hrep as (binst' & instco' & ws & xs & Hbinst' & Hinstco' & ? & Hrep).
      rewrite Hinstco' in Hinstco; inverts Hinstco.
      rewrite Hbinst' in Hbinst; inverts Hbinst.
      rewrite sep_swap23, sep_swap in Hrep.
      forwards* (e_fun & le_fun & m_fun & ws' & xs' & Bind & Alloc & ? & ? & Hobjs & Hm_fun & ? & ?):
        (compat_funcall_pres cf sb sofs binst vs); auto.
      + admit.
      + admit.
      + forwards* Hsub: find_class_sub.
        specialize (Hrec_exec Hsub c).
        apply find_method_In in Findmeth.
        edestruct Hrec_exec with (le1:=le_fun) (e1:=e_fun) (m1:=m_fun)
          as (? & m_fun' & ? & ? & MS'); eauto.
        * rewrite match_states_conj; splits*.
          simpl.
          rewrite sep_swap, sep_swap34, sep_swap23, sep_swap45, sep_swap34,
          <-sep_assoc, <-sep_assoc, sep_swap45, sep_swap34, sep_swap23,
          sep_swap45, sep_swap34, sep_assoc, sep_assoc in Hm_fun; eauto.  
        *{ rewrite match_states_conj in MS'; destruct MS' as (Hm_fun' & ?).
           rewrite sep_swap23, sep_swap5, sep_swap in Hm_fun'.
           forwards* (m_fun'' & Hfree & Hm_fun''): free_exists.
           exists m_fun''; econstructor; exists ws xs; splits*.
           - apply* eval_funcall_internal.
             + constructor*. 
             + rewrite* Htr.
               apply* exec_Sseq_1.
               apply* exec_Sreturn_none.
             + rewrite Hret; reflexivity. 
           - rewrite sep_swap5.
             do 3 rewrite <-sep_assoc in Hm_fun''; rewrite sep_swap5 in Hm_fun'';
             do 3 rewrite sep_assoc in Hm_fun''.          
             unfold varsrep in *; rewrite sep_pure in *.
             destruct Hm_fun'' as (Hpure & Hm_fun''); split*.
             rewrite sep_swap5, sep_pure in Hm_fun''.
             destruct Hm_fun'' as (Hpure' & Hm_fun'').             
             rewrite sep_swap23, sep_swap.
             eapply sep_imp; eauto.
             apply sep_imp'; auto.
             apply sep_imp'; auto.
             + erewrite <-output_match; eauto.
               apply* blockrep_findvars.
             + rewrite staterep_skip with (c:=owner); eauto. simpl.
               rewrite ident_eqb_refl. rewrite sep_assoc, sep_swap3.
               apply sep_imp'; auto.
               rewrite sepall_breakout with (ys:=c_objs owner); eauto; simpl.
               rewrite sep_assoc.
               apply sep_imp'.
               * rewrite Offs.
                 unfold instance_match, mfind_inst, madd_obj; simpl.
                 rewrite PM.gss.
                 eapply welldef_not_class_in in WD; eauto.
                 rewrite <-staterep_skip_cons with (prog:=prog'') (cls:=owner); eauto.
                 rewrite <-staterep_skip_app with (prog:=owner :: prog''); eauto.
                 rewrite <-Hprog.
                 unfold Int.add.
                 repeat rewrite* Int.unsigned_repr.
                 admit.
                 admit.
                 admit.
               *{ apply sep_imp'; auto.
                  unfold staterep_objs.
                  apply sepall_swapp.
                  intros (i, k) Hini.
                  destruct (field_offset gcenv i (make_members owner)); auto.
                  unfold instance_match, mfind_inst, madd_obj; simpl.
                  destruct (ident_eqb i o) eqn: E.
                  - exfalso.
                    apply ident_eqb_eq in E; subst i.
                    pose proof (c_nodupobjs owner) as Nodup.
                    rewrite Hobjs in Nodup.
                    rewrite NoDupMembers_app_cons in Nodup.
                    destruct Nodup as [Notin Nodup].
                    apply Notin.
                    eapply In_InMembers; eauto.
                  - apply ident_eqb_neq in E. 
                    rewrite* PM.gso.
                }
         }
  Admitted.
  
End PRESERVATION.
