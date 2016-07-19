Require Import cfrontend.ClightBigstep.
Require Import cfrontend.Clight.
Require Import cfrontend.Ctypes.
Require Import lib.Integers.
Require Import lib.Maps.
Require Import lib.Coqlib.
Require Import Errors.
Require Import common.Separation.

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
      x <> self_id ->
      well_formed_exp c m (Var x ty)
  | wf_state: forall x ty,
      In (x, ty) c.(c_mems) ->
      well_formed_exp c m (State x ty)
  | wf_const: forall cst ty,
      well_formed_exp c m (Const cst ty).

  Inductive well_formed_stmt (c: class) (m: method) (S: state): stmt -> Prop :=
  | wf_assign: forall x e v,
      In (x, typeof e) (meth_vars m) ->
      x <> self_id ->
      well_formed_exp c m e ->
      exp_eval S e v ->
      valid_val v (typeof e) ->
      v = Values.Val.load_result (chunk_of_type (typeof e)) v ->
      well_formed_stmt c m S (Assign x e)
  | wf_assignst: forall x e v,
      In (x, typeof e) c.(c_mems) ->
      x <> self_id ->
      well_formed_exp c m e ->
      exp_eval S e v ->
      valid_val v (typeof e) ->
      v = Values.Val.load_result (chunk_of_type (typeof e)) v ->
      well_formed_stmt c m S (AssignSt x e)
  | wf_ite: forall e s1 s2,
      well_formed_exp c m e ->
      well_formed_stmt c m S s1 ->
      well_formed_stmt c m S s2 ->
      well_formed_stmt c m S (Ifte e s1 s2)
  | wf_comp: forall S' s1 s2,
      well_formed_stmt c m S s1 ->
      stmt_eval prog S s1 S' ->
      well_formed_stmt c m S' s2 ->
      well_formed_stmt c m S (Comp s1 s2)
  | wf_call: forall ys clsid o f es,
      (* In (y, ty) (class_vars c) -> *)
      (* Nelist.length ys = Nelist.length rvs -> *)
      (* Nelist.Forall (fun y => In y (class_vars c)) ys -> *)
      (* y <> self_id -> *)
      (* In {| obj_inst := o; obj_class := clsid |} c.(c_objs) -> *)
      (* find_class clsid prog = Some (c', prog') -> *)
      (* Nelist.Forall (well_formed_exp c) es -> *)
      (* Nelist.Forall2 (exp_eval S) es vs -> *)
      (* Nelist.Forall2 (fun e v => valid_val v (typeof e)) es vs -> *)
      (* Nelist.Forall2 (fun e x => typeof e = snd x) es c'.(c_input) -> *)
      (* ty = snd c'.(c_output) -> *)
      (* find_inst S o me -> *)
      (* well_formed_stmt c' (me, adds (Nelist.map_fst c'.(c_input)) vs v_empty) m.(m_body) -> *)
      (* stmt_call_eval prog me clsid vs me' rvs -> *)
      (* valid_val rv ty -> *)
      (* ty <> Ctypes.Tvoid -> *)
      well_formed_stmt c m S (Call ys clsid o f es)
  | wf_skip: 
      well_formed_stmt c m S Skip.

  (* Definition compat_vars (c: class) (S: state) (e: Clight.env) (m: Memory.Mem.mem): Prop := *)
  (*   forall x t, *)
  (*     In c prog -> *)
  (*     In (x, t) (class_vars c) -> *)
  (*     exists loc, *)
  (*       Maps.PTree.get x e = Some (loc, t) *)
  (*       /\ Memory.Mem.valid_access m (chunk_of_type t) loc 0 Memtype.Writable *)
  (*       /\ forall v, *)
  (*           find_var S x v -> *)
  (*           Memory.Mem.load (chunk_of_type t) m loc 0 = Some v *)
  (*           /\ valid_val v t. *)

  (* Definition compat_self (c: class) (S: state) (e: Clight.env) (m: Memory.Mem.mem): Prop := *)
  (*   In c prog -> *)
  (*   exists co loc_self loc_struct ofs, *)
  (*     Maps.PTree.get self_id e = Some (loc_self, pointer_of_node c.(c_name)) *)
  (*     /\ Memory.Mem.load AST.Mint32 m loc_self 0 = Some (Values.Vptr loc_struct ofs) *)
  (*     /\ Maps.PTree.get c.(c_name) tge.(Clight.genv_cenv) = Some co *)
  (*     /\ (forall x t, *)
  (*           In (x, t) c.(c_mems) -> *)
  (*           exists delta, *)
  (*             Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta *)
  (*             /\ In (x, t) (Ctypes.co_members co) *)
  (*             /\ Memory.Mem.valid_access m (chunk_of_type t) loc_struct (Int.unsigned (Int.add ofs (Int.repr delta))) Memtype.Writable *)
  (*             /\ forall v, *)
  (*                 find_field S x v -> *)
  (*                 Memory.Mem.load (chunk_of_type t) m loc_struct (Int.unsigned (Int.add ofs (Int.repr delta))) = Some v *)
  (*                 /\ valid_val v t) *)
  (*     /\ forall o, *)
  (*         In o c.(c_objs) -> *)
  (*         exists delta, *)
  (*           Ctypes.field_offset (Clight.genv_cenv tge) o.(obj_inst) (Ctypes.co_members co) = Errors.OK delta. *)
  
  Lemma make_members_co:
    forall clsnm cls prog',
      find_class clsnm prog = Some (cls, prog') ->
      (exists co, gcenv!clsnm = Some co
             /\ co_su co = Struct
             /\ co_members co = make_members cls
             /\ attr_alignas (co_attr co) = None
             /\ NoDupMembers (co_members co)).
  Proof.
    unfold translate in TRANSL.
    apply not_None_is_Some in main_node_exists.
    destruct main_node_exists as [[maincls prog'] Hfind_main].
    rewrite Hfind_main in TRANSL.
    destruct (map (translate_class prog) prog.(p_classes)) as [|cls clss] eqn:Hmap.
    - apply map_eq_nil in Hmap.
      apply find_class_nil with (n:=main_node) in Hmap.
      rewrite Hmap in Hfind_main. discriminate.
    - 
  Admitted.

  Lemma field_translate_mem_type:
    forall clsnm cls prog',
      find_class clsnm prog = Some (cls, prog') ->
      NoDupMembers (make_members cls) ->
      forall x ty,
        In (x, ty) cls.(c_mems) ->
        field_type x (make_members cls) = OK ty.
  Proof.
    introv Hfind Hndup Hin.
    apply in_field_type with (1:=Hndup).
    unfold make_members. apply in_app_iff. now left.
  Qed.

  Lemma field_translate_obj_type:
    forall clsnm cls prog',
      find_class clsnm prog = Some (cls, prog') ->
      NoDupMembers (make_members cls) ->
      forall o c,
        In (o, c) cls.(c_objs) ->
        field_type o (make_members cls) = OK (type_of_inst c).
  Proof.
    introv Hfind Hndup Hin.
    apply in_field_type with (1:=Hndup).
    unfold make_members. apply in_app_iff. right.
    apply in_map_iff. exists* (o, c). 
  Qed.

  (* TODO: Construct a global environment of structs for a given program. *)

  Lemma gcenv_consistent:
    composite_env_consistent gcenv.
  Admitted.
  
  Lemma range_staterep:
    forall ve b clsnm,
      (* Welldef_Program prog -> *)
      find_class clsnm prog <> None ->
      range b 0 (sizeof gcenv (type_of_inst clsnm)) -*>
            staterep gcenv prog clsnm (m_empty, ve) b 0.
  Proof.
    introv Hfind.
    cut (forall lo,
           (alignof gcenv (type_of_inst clsnm) | lo) ->
           massert_imp (range b lo (lo + sizeof gcenv (type_of_inst clsnm)))
                       (staterep gcenv prog clsnm (m_empty, ve) b lo)).
    intro HH; apply HH; apply Z.divide_0_r.
    clear main_node_exists TRANSL.

    revert clsnm Hfind.
    destruct prog as [p Hwdef].
    induction p as [|cls prog' IH]; intros clsnm Hfind lo.
    - apply not_None_is_Some in Hfind.
      destruct Hfind. discriminate.
    - intro Halign.
      inversion Hwdef as [|? ? Hwdef']; subst.

      assert (find_class clsnm prog = Some (cls, {| p_classes:=prog'; p_welldef:=Hwdef' |})) as Hprog.
      admit.
      (* TODO: need to link prog to (possibly reversed) translation *)

      pose proof (make_members_co _ _ _ Hprog) as Hmco.
      destruct Hmco as [co [Hg [Hsu [Hmem [Hattr Hndup]]]]].

      pose proof (co_members_alignof _ _ (gcenv_consistent _ _ Hg) Hattr)
        as Hcoal.
      rewrite Hmem in Hcoal.
      unfold make_members in Hcoal.
      apply Forall_app in Hcoal.
      destruct Hcoal as [Hcoal1 Hcoal2].
      simpl in Halign.
      rewrite Hg in Halign.
      rewrite align_noattr in Halign.
      assert (Hndup':=Hndup). rewrite Hmem in Hndup'.

      simpl.
      destruct (ident_eqb clsnm cls.(c_name)) eqn:Hclsnm.
      +
        rewrite Hg.
        unfold staterep; simpl.
        rewrite Hclsnm.
        rewrite <-Hmem.
        rewrite split_range_fields
        with (1:=gcenv_consistent) (2:=Hg) (3:=Hsu) (4:=Hndup).
        rewrite Hmem at 1.
        unfold make_members.
        rewrite sepall_app.

        apply sep_imp'.

        *{ pose proof (field_translate_mem_type _ _ _ Hprog Hndup') as Htype.
           clear Hcoal2.
           
           induction (c_mems cls); auto.
           apply Forall_cons2 in Hcoal1.
           destruct Hcoal1 as [Hcoal1 Hcoal2].

           apply sep_imp'.
           - destruct a.
             destruct (field_offset gcenv i (co_members co)) eqn:Hfo; auto.
             unfold match_field.
             rewrite match_value_empty.
             rewrite sizeof_translate_chunk.
             + apply range_contains'.
               specialize (Htype i t).
               rewrite <-Hmem in Htype.
               apply field_offset_aligned with (ty:=t) in Hfo.
               *{ simpl in Hcoal1.
                  apply Z.divide_add_r.
                  - apply Zdivide_trans with (2:=Halign).
                    apply Zdivide_trans with (2:=Hcoal1).
                    apply align_chunk_divides_alignof_type.
                    admit.
                  - apply Zdivide_trans with (2:=Hfo).
                    apply align_chunk_divides_alignof_type.
                    admit.
                }
               * apply Htype; constructor; reflexivity.
             + admit.
           - apply IHl. 
             + apply Hcoal2. 
             + intros; apply Htype; constructor (assumption).
         }             

        *{ pose proof (field_translate_obj_type _ _ _ Hprog Hndup') as Htype.
           rewrite <-Hmem in Htype.
           
           induction (c_objs cls); auto.
           simpl.
           apply sep_imp'.
           - clear IHl.

             destruct a as [o c].
             assert (ClassIn c prog') as Hcin
                 by (eapply H0; econstructor; eauto).
             clear H0 Hcoal1.

             apply Forall_cons2 in Hcoal2.
             destruct Hcoal2 as [Hcoal2 Hcoal3].
             
             specialize (Htype o c (in_eq _ _)).
             clear Hcoal3 l.

             simpl. 
             destruct (field_offset gcenv o (co_members co)) eqn:Hfo; auto.
             rewrite instance_match_empty.
             apply ClassIn_find_class with (Hwdef:=Hwdef') in Hcin.
             specialize (IH Hwdef' c Hcin (lo + z)%Z).

             apply not_None_is_Some in Hcin.
             destruct Hcin as ((c' & prog'') & Hcin).
             assert (find_class c prog = Some (c', prog'')) as Hcin'.
             admit. (* TODO: make_members_co should be more flexible. *)

             assert (Hcin'' := Hcin').
             apply make_members_co in Hcin'.
             destruct Hcin' as [? [? [? [? [? ?]]]]].
             rewrite H.

             simpl in IH.
             rewrite H in IH.
             apply IH.

             simpl in Hcoal2.
             rewrite align_noattr in Hcoal2.
             rewrite H in Hcoal2.

             rewrite align_noattr.
             apply Z.divide_add_r.
             + apply Zdivide_trans with (1:=Hcoal2).
               assumption.

             + simpl in Htype.
               eapply field_offset_aligned in Hfo.
               2:apply Htype.
               apply Zdivide_trans with (2:=Hfo).
               simpl. rewrite H, align_noattr.
               apply Z.divide_refl.
           - apply IHl.
             + clear IHl. intros o c' Hin.
               apply H0 with (o:=o). constructor (assumption).
             + simpl in Hcoal2. apply Forall_cons2 in Hcoal2.
               destruct Hcoal2 as [Hcoal2 Hcoal3]. exact Hcoal3.
             + intros o c Hin. apply Htype. constructor (assumption). 
         }  

      + rewrite Hg.

        assert (find_class clsnm {| p_classes := prog'; p_welldef := Hwdef' |} <> None) as Hfind'.
        admit.
        unfold staterep, staterep'; simpl.
        rewrite Hclsnm; simpl.
        admit.
        (* rewrite ident_eqb_sym in Hclsnm. *)
        (* unfold staterep; simpl. *)
        (* rewrite Hclsnm in Hfind. *)
        (* specialize (IH Hwdef' clsnm Hfind' lo). *)
        (* simpl in IH. *)
        (* rewrite Hg in IH. *)
        (* apply IH. *)
        (* rewrite align_noattr. *)
        (* assumption. *)
  Qed.

  Lemma staterep_deref_mem:
    forall cls prog' m S b ofs x ty d v,
      access_mode ty = By_value (chunk_of_type ty) ->
      m |= staterep' gcenv (cls::prog') cls.(c_name) S b ofs ->
      In (x, ty) cls.(c_mems) ->
      find_field S x v ->
      field_offset gcenv x (make_members cls) = OK d ->
      Clight.deref_loc ty m b (Int.repr (ofs + d)) v.
  Proof.
    intros ** Hty Hm Hin Hv Hoff.
    simpl in Hm. rewrite ident_eqb_refl in Hm.
    apply sep_proj1 in Hm.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    apply sep_proj1 in Hm. clear ws xs.
    rewrite Hoff in Hm. clear Hoff.
    apply loadv_rule in Hm.
    destruct Hm as [v' [Hloadv Hmatch]].
    unfold match_field, match_value in Hmatch.
    unfold find_field, mfind_mem in Hv.
    rewrite Hv in Hmatch. clear Hv.
    rewrite <-Hmatch in Hloadv. clear Hmatch.
    apply Clight.deref_loc_value with (2:=Hloadv); auto.
  Qed.

  Lemma staterep_assign_mem:
    forall P cls prog' m m' S b ofs x ty d v,
      access_mode ty = By_value (chunk_of_type ty) ->
      NoDup cls.(c_objs) ->
      NoDupMembers cls.(c_mems) ->
      m |= staterep' gcenv (cls::prog') cls.(c_name) S b ofs ** P ->
      In (x, ty) cls.(c_mems) ->
      field_offset gcenv x (make_members cls) = OK d ->
      v = Values.Val.load_result (chunk_of_type ty) v ->
      Clight.assign_loc gcenv ty m b (Int.repr (ofs + d)) v m' ->
      m' |= staterep' gcenv (cls::prog') cls.(c_name) (update_field S x v) b ofs ** P.
  Proof.
    Opaque sepconj.
    intros ** Hty Hcls Hmem Hm Hin Hoff Hlr Hal.
    simpl in *. rewrite ident_eqb_refl in *.
    rewrite sep_assoc. rewrite sep_assoc in Hm.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hsplit in Hmem.
    rewrite Hin in Hm. rewrite sep_assoc in Hm.
    rewrite Hin. rewrite sep_assoc.
    rewrite Hoff in *.
    rewrite sep_swap2.
    rewrite sepall_switchp
    with (f':=fun xty : ident * typ =>
                let (x0, ty0) := xty in
                match field_offset gcenv x0 (make_members cls) with
                | OK d0 =>
                  contains (chunk_of_type ty0) b (ofs + d0)
                           (match_field S x0)
                | Error _ => sepfalse
                end).
    - rewrite <-sep_swap2.
      eapply storev_rule' with (1:=Hm).
      + unfold match_field, match_value. simpl.
        rewrite PM.gss. exact Hlr.
      + clear Hlr. inversion Hal as [? ? ? Haccess|? ? ? ? Haccess].
        * rewrite Hty in Haccess.
          injection Haccess. intro; subst. assumption.
        * rewrite Hty in Haccess. discriminate.
    - apply NoDupMembers_remove_1 in Hmem.
      apply NoDupMembers_NoDup with (1:=Hmem).
    - intros x' Hin'; destruct x' as [x' ty'].
      unfold match_field, update_field, madd_mem; simpl.
      rewrite match_value_add; [reflexivity|].
      apply NoDupMembers_app_cons in Hmem.
      destruct Hmem as [Hmem].
      apply In_InMembers in Hin'.
      intro Heq. apply Hmem. rewrite Heq in Hin'.
      assumption.
  Qed.
  
  Remark valid_val_not_void:
    forall v t, valid_val v t -> t <> Ctypes.Tvoid.
  Proof.
    introv H E; subst.
    inverts H; discriminate.
  Qed.
  
  Hint Constructors Clight.eval_lvalue Clight.eval_expr well_formed_stmt.
  Hint Resolve valid_val_implies_access.

  (* Remark eval_var: *)
  (*   forall (* c *) S e le m x t v, *)
  (*     (* compat_vars c S e m -> *) *)
  (*     (* In c prog -> *) *)
  (*     (* In (x, t) (class_vars c) -> *) *)
  (*     find_var S x v -> *)
  (*     Clight.eval_expr tge e le m (Clight.Evar x t) v. *)
  (* Proof. *)
  (*   introv (* Hvars ? ? *) Find. *)
  (*   (* edestruct Hvars as (? & ? & ? & Hmem); eauto. *) *)
  (*   (* specializes Hmem Find. *) *)
  (*   eapply Clight.eval_Elvalue, Clight.deref_loc_value. *)
  (*   econstructor. *)
    
  (* Qed. *)

  (* Remark evall_self_field: *)
  (*   forall c e le m x t co loc_self loc_struct ofs delta, *)
  (*     Maps.PTree.get self_id e = Some (loc_self, pointer_of_node (c_name c)) -> *)
  (*     Memory.Mem.load AST.Mint32 m loc_self 0 = Some (Values.Vptr loc_struct ofs) -> *)
  (*     Maps.PTree.get (c_name c) (Clight.genv_cenv tge) = Some co -> *)
  (*     Ctypes.field_offset (Clight.genv_cenv tge) x (Ctypes.co_members co) = Errors.OK delta -> *)
  (*     Clight.eval_lvalue tge e le m (deref_self_field c.(c_name) x t) loc_struct (Int.add ofs (Int.repr delta)). *)
  (* Proof. *)
  (*   intros. *)
  (*   eapply Clight.eval_Efield_struct *)
  (*   with (id:=c.(c_name)) (att:=Ctypes.noattr); eauto. *)
  (*   eapply Clight.eval_Elvalue.  *)
  (*   - apply Clight.eval_Ederef.  *)
  (*     apply* Clight.eval_Elvalue. *)
  (*     apply* Clight.deref_loc_value. *)
  (*     reflexivity. *)
  (*   - apply* Clight.deref_loc_copy. *)
  (* Qed. *)
  
  (* Remark eval_self_field: *)
  (*   forall c S e le m x t v, *)
  (*     compat_self c S e m -> *)
  (*     In c prog -> *)
  (*     In (x, t) c.(c_mems) -> *)
  (*     find_field S x v -> *)
  (*     Clight.eval_expr tge e le m (deref_self_field c.(c_name) x t) v. *)
  (* Proof. *)
  (*   introv Hself ? Hin Find. *)
  (*   destruct* Hself as (? & ? & ? & ? & ? & ? & ? & Hmem & ?).   *)
  (*   forwards (? & ? & ? & ? & Hmem'): Hmem Hin. *)
  (*   specializes Hmem' Find. *)
  (*   eapply Clight.eval_Elvalue. *)
  (*   + apply* evall_self_field. *)
  (*   + apply* Clight.deref_loc_value.       *)
  (* Qed. *)
  
  Lemma expr_eval_simu:
    forall c S exp v e le m meth,
      (* compat_vars c S e m -> *)
      (* compat_self c S e m -> *)
      (* In c prog -> *)
      (* well_formed_exp c exp -> *)
      exp_eval S exp v ->
      Clight.eval_expr tge e le m (translate_exp c meth exp) v.
  Proof.
    intros c S exp; induction exp as [x ty| |cst];
    introv (* ? ? ? Hwf *) Heval; inverts Heval(* ; inverts Hwf *).

    (* Var x ty : "x" *)
    - simpl.
      case (existsb (fun out : positive * typ => ident_eqb (fst out) x) (m_out meth)).
      + eapply eval_Elvalue.
        *{ eapply eval_Efield_struct.
           - eapply eval_Elvalue.
             + apply eval_Ederef.
               eapply eval_Elvalue.
               * apply eval_Evar_local.
                 skip.
               *{ eapply deref_loc_value.
                  - simpl; eauto.
                  - skip.
                }
             + apply deref_loc_copy; auto.
           - simpl; unfold type_of_inst; eauto.
           - skip.
           - skip.
         }
        *{ eapply deref_loc_value.
           - simpl. skip.
           - skip.
         }
      + apply eval_Etempvar.
        admit.
      
    (* State x ty : "self->x" *)
    - simpl.
      eapply eval_Elvalue.
      + eapply eval_Efield_struct.
        *{ eapply eval_Elvalue.
           - apply eval_Ederef.
             eapply eval_Elvalue.
             + apply eval_Evar_local.
               skip.
             + eapply deref_loc_value.
               * simpl; eauto.
               * skip.
           - apply deref_loc_copy; auto.
         } 
        * simpl; unfold type_of_inst; eauto.
        * skip.
        * skip.
      + eapply deref_loc_value.
        * simpl. skip.
        * skip.
        
    (* Const c ty : "c" *)
    - destruct cst; constructor.
  Admitted.

  Lemma exprs_eval_simu:
    forall c S es es' vs e le m,
      compat_vars c S e m ->
      compat_self c S e m ->
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

  Remark eval_exprlist_app:
    forall e le m es es' vs vs',
      Clight.eval_exprlist tge e le m es (list_type_to_typelist (map Clight.typeof es)) vs ->
      Clight.eval_exprlist tge e le m es' (list_type_to_typelist (map Clight.typeof es')) vs' ->
      Clight.eval_exprlist tge e le m (es ++ es') (list_type_to_typelist (map Clight.typeof (es ++ es'))) (vs ++ vs').
  Proof.
    induction es; introv Ev Ev'; inverts* Ev.
    repeat rewrite <-app_comm_cons.
    simpl; econstructor; eauto.
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
      In (x, t) (class_vars c) ->
      In (x, t') (class_vars c) ->
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
      find_var (update_var S x v) x v' -> v' = v.
  Proof.
    unfold find_var, update_var; simpl.
    intros; apply* find_add.
  Qed.

  Remark find_update_field:
    forall x v v' S,
      find_field (update_field S x v) x v' -> v' = v.
  Proof.
    unfold find_field, update_field, mfind_mem, madd_mem; simpl.
    intros; apply* find_add.
  Qed.

  Remark gso_var:
    forall x x' v v' S,
      x <> x' -> find_var (update_var S x' v) x v' -> find_var S x v'.
  Proof.
    unfold find_var, update_var; simpl.
    introv Neq H.
    rewrite <-H; symmetry.
    apply* PM.gso.
  Qed.

  Remark gso_field:
    forall x x' v v' S,
      x <> x' -> find_field (update_field S x' v) x v' -> find_field S x v'.
  Proof.
    unfold find_field, update_field; simpl.
    introv Neq H.
    rewrite <-H; symmetry.
    apply* mfind_mem_gso.
  Qed.

  Remark find_field_update_var:
    forall S x v x' v',
      find_field (update_var S x v) x' v' -> find_field S x' v'.
  Proof. unfold find_field, update_var; simpl; auto. Qed.

  Remark find_var_update_field:
    forall S x v x' v',
      find_var (update_field S x v) x' v' -> find_var S x' v'.
  Proof. unfold find_var, update_field; simpl; auto. Qed.

  Definition mem_sep (c: class) (e: Clight.env) (m: Memory.Mem.mem) :=
    forall x loc t loc_self loc_struct ofs,
      In (x, t) (class_vars c) -> 
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
                       (Memdata.size_chunk (chunk_of_type t')))
         (Int.unsigned (Int.add ofs (Int.repr delta)))
       \/
       BinInt.Z.le
         (BinInt.Z.add (Int.unsigned (Int.add ofs (Int.repr delta)))
                       (Memdata.size_chunk (chunk_of_type t)))
         (Int.unsigned (Int.add ofs (Int.repr delta')))).

  (* Hypothesis STEPS: *)
  (*   forall c (e: Clight.env), *)
  (*     In c prog -> *)
  (*     exists loc_f f, *)
  (*       Globalenvs.Genv.find_symbol tge.(Clight.genv_genv) (step_id c.(c_name)) = Some loc_f *)
  (*       /\ Maps.PTree.get (step_id c.(c_name)) e = None *)
  (*       /\ Globalenvs.Genv.find_funct_ptr tge.(Clight.genv_genv) loc_f = Some (Ctypes.Internal f) *)
  (*       /\ Clight.type_of_fundef (Ctypes.Internal f) = *)
  (*         Ctypes.Tfunction (Ctypes.Tcons (type_of_inst_p c.(c_name)) *)
  (*                                        (list_type_to_typelist (map snd (nelist2list c.(c_input) ++ nelist2list c.(c_output))))) *)
  (*                                        Ctypes.Tvoid AST.cc_default *)
  (*       /\ Coqlib.list_norepet (Clight.var_names (Clight.fn_params f) ++ Clight.var_names (Clight.fn_vars f)) *)
  (*       /\ Clight.fn_body f = snd (translate_stmt c.(c_name) c.(c_step)) *)
  (*       /\ length f.(Clight.fn_params) = 1 + Nelist.length c.(c_input)   *)
  (*       /\ Forall (fun x => Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_type (snd x))) *)
  (*                (f.(Clight.fn_params) ++ f.(Clight.fn_vars)). *)
  
  Definition match_step (e: Clight.env) :=
    forall c,
      In c prog ->
      exists loc_f f,
        Globalenvs.Genv.find_symbol tge.(Clight.genv_genv) (step_id c.(c_name)) = Some loc_f
        /\ Maps.PTree.get (step_id c.(c_name)) e = None
        /\ Globalenvs.Genv.find_funct_ptr tge.(Clight.genv_genv) loc_f = Some (Ctypes.Internal f)
        /\ Clight.type_of_fundef (Ctypes.Internal f) =
          Ctypes.Tfunction (Ctypes.Tcons (type_of_inst_p c.(c_name))
                                         (list_type_to_typelist
                                            (map snd (nelist2list c.(c_input) ++ nelist2list c.(c_output)))))
                           Ctypes.Tvoid AST.cc_default
        (* /\ f.(Clight.fn_vars) = [] *)
        /\ Coqlib.list_norepet (Clight.var_names (Clight.fn_params f) ++ Clight.var_names (Clight.fn_vars f))
        /\ Clight.fn_body f = Clight.Ssequence (translate_stmt c.(c_name) c.(c_step)) (Clight.Sreturn None)
        /\ f.(Clight.fn_params) =
          (self_id, type_of_inst_p c.(c_name)) :: nelist2list c.(c_input) ++ nelist2list c.(c_output)
        /\ Forall (fun x => Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_type (snd x)))
                 (f.(Clight.fn_params) ++ f.(Clight.fn_vars)).
  
  Definition c_state := (Clight.env * Memory.Mem.mem)%type.
   
  Inductive match_states (c: class) (S: state): c_state -> Prop :=
    intro_match_states: forall e m,
      (* state correspondance *)
      compat_vars c S e m ->
      compat_self c S e m ->

      (* function *)
      match_step e ->
      
      (* Clight side separation *)
      mem_sep c e m ->
      self_sep c e m ->
      fields_sep m ->
      nodup_env e ->

      (* Minimp side separation *)
      nodup_vars c ->
      nodup_mems c ->
      match_states c S (e, m).

  Hint Constructors match_states.
  
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
    forall c S e m loc x t v,
      In c prog ->
      match_states c S (e, m) ->
      Maps.PTree.get x e = Some (loc, t) ->
      In (x, t) (class_vars c) ->
      v = Values.Val.load_result (chunk_of_type t) v ->
      valid_val v t ->
      x <> self_id ->
      exists m', Memory.Mem.store (chunk_of_type t) m loc 0 v = Some m' 
            /\ match_states c (update_var S x v) (e, m').
  Proof.
    introv ? MS Hget Hin Hloadres ? ?.
    inverts MS as Hvars Hself Hstep Hsep Hself_sep Hfields_sep Hnodupenv Hnodupvars; intro Hnodupmems.
    edestruct Hvars as (loc' & Hget' & ? & ?); eauto.
    rewrite Hget' in Hget; inverts Hget; rename Hget' into Hget.
    edestruct Memory.Mem.valid_access_store with (v:=v) as [m']; eauto.
    destruct* Hself as (co & loc_self & loc_struct & ofs & Hget_self & Hload_self & Hget_co & Hmem & ?).
    exists m'; split*; constructor*.

    - unfold compat_vars; intros x' t' ? Hin'.
      edestruct Hvars as (loc' & Hget' & ? & Hm); eauto.
      exists loc'; splits*.
      + apply* Memory.Mem.store_valid_access_1.
      + intros v' Hfind.
        destruct (AST.ident_eq x' x).
        *{ subst x'.
           apply find_update_var in Hfind; subst v'.
           specializes Hnodupvars Hin Hin'; subst t'. 
           split*.
           destruct (Values.eq_block loc' loc) as [|Neq].
           - subst loc'.
             rewrite Hloadres; apply* Memory.Mem.load_store_same.
           - rewrite Hget in Hget'; inverts Hget'. now contradict Neq. 
         }
        *{ apply gso_var in Hfind; auto.
           forwards (Hload & ?): Hm Hfind. 
           split*.
           destruct (Values.eq_block loc' loc).
           - subst loc'.
             edestruct Hnodupenv; eauto. 
           - rewrite <-Hload. 
             apply* Memory.Mem.load_store_other.
         }        
         
    - unfold compat_self; intro.
      exists co loc_self loc_struct ofs.
      splits*.
      + destruct (Values.eq_block loc_self loc).
        * subst loc.
          edestruct Hnodupenv; eauto.
        * rewrite <-Hload_self.
          apply* Memory.Mem.load_store_other.
      + intros x' t' Hin'.
        specializes Hmem Hin'; destruct Hmem as (delta & ? & ? & ? & Hm).
        exists delta; splits*.
         * apply* Memory.Mem.store_valid_access_1.
         *{ intros v' Hfind.
            apply find_field_update_var in Hfind.
            forwards (Hload & ?): Hm Hfind.
            splits*.
            destruct (Values.eq_block loc loc_struct).
            - edestruct Hsep; eauto.
            - rewrite <-Hload.
              apply* Memory.Mem.load_store_other.
          }

    - unfold mem_sep; introv ? ? Hget_self' ?.
      rewrite Hget_self' in Hget_self; inverts Hget_self.
      forwards* Eq: load_same; inverts Eq.
      apply* Hsep.

    - unfold self_sep; introv Hget_self' ?.
      rewrite Hget_self' in Hget_self; inverts Hget_self.
      forwards* Eq: load_same; inverts Eq.
      apply* Hself_sep.
  Qed.

  (* Lemma compat_assigns_pres: *)
  (*   forall c S e m loc ys vs, *)
  (*     In c prog -> *)
  (*     match_states c S (e, m) -> *)
  (*     Nelist.Forall (fun y => In y (class_vars c)) ys -> *)
  (*     exists m', Memory.Mem.store (chunk_of_type t) m loc 0 v = Some m'  *)
  (*           /\ match_states c (update_var S x v) (e, m'). *)
  (* Proof. *)
  (*   introv ? MS Hget Hin Hloadres ? ?. *)
  (*   inverts MS as Hvars Hself Hstep Hsep Hself_sep Hfields_sep Hnodupenv Hnodupvars; intro Hnodupmems. *)
  (*   edestruct Hvars as (loc' & Hget' & ? & ?); eauto. *)
  (*   rewrite Hget' in Hget; inverts Hget; rename Hget' into Hget. *)
  (*   edestruct Memory.Mem.valid_access_store with (v:=v) as [m']; eauto. *)
  (*   destruct* Hself as (co & loc_self & loc_struct & ofs & Hget_self & Hload_self & Hget_co & Hmem & ?). *)
  (*   exists m'; split*; constructor*. *)

  (*   - unfold compat_vars; intros x' t' ? Hin'. *)
  (*     edestruct Hvars as (loc' & Hget' & ? & Hm); eauto. *)
  (*     exists loc'; splits*. *)
  (*     + apply* Memory.Mem.store_valid_access_1. *)
  (*     + intros v' Hfind. *)
  (*       destruct (AST.ident_eq x' x). *)
  (*       *{ subst x'. *)
  (*          apply find_update_var in Hfind; subst v'. *)
  (*          specializes Hnodupvars Hin Hin'; subst t'.  *)
  (*          split*. *)
  (*          destruct (Values.eq_block loc' loc) as [|Neq]. *)
  (*          - subst loc'. *)
  (*            rewrite Hloadres; apply* Memory.Mem.load_store_same. *)
  (*          - rewrite Hget in Hget'; inverts Hget'. now contradict Neq.  *)
  (*        } *)
  (*       *{ apply gso_var in Hfind; auto. *)
  (*          forwards (Hload & ?): Hm Hfind.  *)
  (*          split*. *)
  (*          destruct (Values.eq_block loc' loc). *)
  (*          - subst loc'. *)
  (*            edestruct Hnodupenv; eauto.  *)
  (*          - rewrite <-Hload.  *)
  (*            apply* Memory.Mem.load_store_other. *)
  (*        }         *)
         
  (*   - unfold compat_self; intro. *)
  (*     exists co loc_self loc_struct ofs. *)
  (*     splits*. *)
  (*     + destruct (Values.eq_block loc_self loc). *)
  (*       * subst loc. *)
  (*         edestruct Hnodupenv; eauto. *)
  (*       * rewrite <-Hload_self. *)
  (*         apply* Memory.Mem.load_store_other. *)
  (*     + intros x' t' Hin'. *)
  (*       specializes Hmem Hin'; destruct Hmem as (delta & ? & ? & ? & Hm). *)
  (*       exists delta; splits*. *)
  (*        * apply* Memory.Mem.store_valid_access_1. *)
  (*        *{ intros v' Hfind. *)
  (*           apply find_field_update_var in Hfind. *)
  (*           forwards (Hload & ?): Hm Hfind. *)
  (*           splits*. *)
  (*           destruct (Values.eq_block loc loc_struct). *)
  (*           - edestruct Hsep; eauto. *)
  (*           - rewrite <-Hload. *)
  (*             apply* Memory.Mem.load_store_other. *)
  (*         } *)

  (*   - unfold mem_sep; introv ? ? Hget_self' ?. *)
  (*     rewrite Hget_self' in Hget_self; inverts Hget_self. *)
  (*     forwards* Eq: load_same; inverts Eq. *)
  (*     apply* Hsep. *)

  (*   - unfold self_sep; introv Hget_self' ?. *)
  (*     rewrite Hget_self' in Hget_self; inverts Hget_self. *)
  (*     forwards* Eq: load_same; inverts Eq. *)
  (*     apply* Hself_sep. *)
  (* Qed. *)

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
    forall c S e m x t v co loc_self loc_struct ofs delta,
      In c prog ->
      match_states c S (e, m) ->
      Ctypes.field_offset tge.(Clight.genv_cenv) x (Ctypes.co_members co) = Errors.OK delta ->
      Maps.PTree.get c.(c_name) (Clight.genv_cenv tge) = Some co ->
      Maps.PTree.get self_id e = Some (loc_self, pointer_of_node c.(c_name)) ->
      Memory.Mem.load AST.Mint32 m loc_self 0 = Some (Values.Vptr loc_struct ofs) ->
      In (x, t) c.(c_mems) ->
      v = Values.Val.load_result (chunk_of_type t) v ->
      valid_val v t ->
     Memory.Mem.valid_access m (chunk_of_type t) loc_struct (Int.unsigned (Int.add ofs (Int.repr delta))) Memtype.Writable ->
      exists m',
        Memory.Mem.store (chunk_of_type t) m loc_struct (Int.unsigned (Int.add ofs (Int.repr delta))) v = Some m'
        /\ match_states c (update_field S x v) (e, m').
  Proof.
    intros ** ? MS Hoffset Hget_co Hget_self Hload_self Hin Hloadres ? ? .
    inverts MS as Hvars Hself Hstep Hsep Hself_sep Hfields_sep Hnodupenv Hnodupvars; intro Hnodupmems.
    edestruct Memory.Mem.valid_access_store with (v:=v) as [m']; eauto. 
    exists m'; split*; constructor*.

    - unfold compat_vars; intros.
      edestruct Hvars as (loc & ? & ? & Hm); eauto.
      exists loc; splits*.
      + apply* Memory.Mem.store_valid_access_1.
      + introv Hfind.
        apply find_var_update_field in Hfind.
        forwards (Hload & ?): Hm Hfind.
        split*.
        destruct (Values.eq_block loc loc_struct).
        * edestruct Hsep; eauto.
        * rewrite <-Hload.
          apply* Memory.Mem.load_store_other.

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
      + intros x' t' Hin'.
        specializes Hmem Hin'; destruct Hmem as (delta' & Hoffset' & ? & ? & Hm).
        exists delta'; splits*.
        * apply* Memory.Mem.store_valid_access_1.  
        *{ intros v' Hfind'.
           destruct (AST.ident_eq x' x).
           - subst x'.
             rewrite Hoffset' in Hoffset; inverts Hoffset.
             apply find_update_field in Hfind'; subst v'.
             specializes Hnodupmems Hin Hin'; subst t'. 
             split*.
             rewrite Hloadres; apply* Memory.Mem.load_store_same.
           - apply gso_field in Hfind'; auto.
             forwards (Hload & ?): Hm Hfind'.
             split*.
             rewrite <-Hload; apply* Memory.Mem.load_store_other.
         }
        
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
      Ctypes.access_mode ty = Ctypes.By_value (chunk_of_type ty) ->
      Memory.Mem.valid_access m (chunk_of_type ty) loc 0 Memtype.Writable ->
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
                  /\ Memory.Mem.valid_access m (chunk_of_type (snd x)) loc 0 Memtype.Writable
                  /\ Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_type (snd x))) xs ->
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
      Forall (fun x => Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_type (snd x))) vars ->
      Forall (fun x => exists loc,
                  Maps.PTree.get (fst x) e' = Some (loc, snd x)
                  /\ Memory.Mem.valid_access m' (chunk_of_type (snd x)) loc 0 Memtype.Writable
                  /\ Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_type (snd x))) vars.
  Proof.
    induction vars.
    - constructor.
    - introv Halloc Hforall.
      inverts Halloc.
      constructor.
      + exists b1; splits*.
        * admit.
        *{ assert (Memory.Mem.valid_access m1 (chunk_of_type (snd (id, ty))) b1 0 Memtype.Writable).
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
      Forall (fun x => Ctypes.access_mode (snd x) = Ctypes.By_value (chunk_of_type (snd x))) (f.(Clight.fn_params) ++ f.(Clight.fn_vars)) ->
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
    forall c' c es ys,
      Nelist.Forall2 (fun e x => typeof e = snd x) es c'.(c_input) ->
      map Clight.typeof (nelist2list (Nelist.map (translate_exp c.(c_name)) es)
                         ++ nelist2list (Nelist.map make_out_arg ys)) =
      map snd (nelist2list c'.(c_input) ++ nelist2list c'.(c_output)).
  Proof.
    (* intros c'. *)
    (* induction (c_input c'); introv Heq; *)
    (* inversion_clear Heq as [? ? Hty|? ? ? ? Hty Hforall2]; simpl. *)
    (* - rewrite type_pres, Hty; auto. *)
    (* - f_equal. *)
    (*   + rewrite type_pres, Hty; auto. *)
    (*   + specializes IHn Hforall2; eauto. *)
    admit.
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

  Lemma exprlist_make_out_arg:
    forall c S e le m ys,
      In c prog ->
      compat_vars c S e m ->
      Nelist.Forall (fun y => In y (class_vars c)) ys ->
      exists vs, Clight.eval_exprlist tge e le m
                                 (nelist2list (Nelist.map make_out_arg ys))
                                 (list_type_to_typelist
                                    (map Clight.typeof (nelist2list (Nelist.map make_out_arg ys))))
                                 vs.
  Proof.
    introv ? Hvars Hins.
    induction ys as [[x t]|[x t]]; inverts Hins as ? Hins;
    edestruct Hvars; eauto.
    - do 2 econstructor; eauto.
      + apply Clight.eval_Eaddrof.
        apply* Clight.eval_Evar_local.
      + apply sem_cast_same.
        simpl. splits*.
        * discriminate.
        * unfold pointer_of; simpl; trivial.
    - forwards (? & ?): IHys Hins.
      simpl.
      do 2 econstructor; eauto.
      + apply Clight.eval_Eaddrof.
        apply* Clight.eval_Evar_local.
      + apply sem_cast_same.
        splits*.
        * discriminate.
        * unfold pointer_of; simpl; trivial.
  Qed.
  
  Theorem simu_bigbig:
    (forall p S1 s S2,
        stmt_eval p S1 s S2 ->
        sub_prog p prog ->
         forall c,
          In c prog ->
          forall e1 le1 m1
            (WF: well_formed_stmt c S1 s) 
            (MS: match_states c S1 (e1, m1)),
          exists le2 m2 t,
            exec_stmt tge (Clight.function_entry1 tge) e1 le1 m1
                      (translate_stmt c.(c_name) s) t le2 m2 ClightBigstep.Out_normal
            /\ match_states c S2 (e1, m2))
    /\ (forall p me clsid vs me' rvs,
          stmt_step_eval p me clsid vs me' rvs ->
          sub_prog p prog ->
          forall c S o c' prog' m loc_f f loc_struct ofs e le outs,
            In c' prog ->
            well_formed_stmt c' (me, adds (Nelist.map_fst c'.(c_input)) vs v_empty) c'.(c_step) ->
            match_states c S (e, m) ->
            Globalenvs.Genv.find_symbol tge.(Clight.genv_genv) (step_id clsid) = Some loc_f ->
            Globalenvs.Genv.find_funct_ptr tge.(Clight.genv_genv) loc_f = Some (Ctypes.Internal f) ->
            find_inst S o me ->
            find_class clsid prog = Some (c', prog') ->
            List.length f.(Clight.fn_params) = 1 + Nelist.length vs + Nelist.length c'.(c_output) ->
            Clight.eval_expr tge e le m (ptr_obj (Some c.(c_name)) clsid o) (Values.Vptr loc_struct ofs) ->
            exists m' t,
              eval_funcall tge (Clight.function_entry1 tge) m (Ctypes.Internal f)
                           ((Values.Vptr loc_struct ofs) :: nelist2list vs ++ outs) t m' Values.Vundef
              /\ match_states c (update_inst S o me') (e, m')
        ).
  Proof.
    clear TRANSL.
    apply stmt_eval_step_ind;
      [| |introv ? ? ? ? Hifte|introv ? HS1 ? HS2|introv ? Evs ? Hrec_eval|
       |(introv Hfind ? ? Hrec_exec; intros ** MS Hget_loc_f Hget_f ? Hfind' Hlengths ?)];
      intros;
      try inverts WF as; [|introv Hin| | |introv Hlengths' Hins Hin Hfind Wfs ? Valids Types| |]; intros;
      inverts MS as Hvars Hself Hstep.

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
    - edestruct Hifte with (le1:=le1); destruct_conjs; eauto; [destruct* b|]. 
      do 3 econstructor; split*.
      apply* exec_Sifthenelse. 
      + erewrite type_pres, bool_val_ptr; eauto.
      + destruct* b. 
      
    (* Comp s1 s2 : "s1; s2" *)
    - app_stmt_eval_det'.
      edestruct HS1; destruct_conjs; eauto.
      edestruct HS2; destruct_conjs; eauto.
      do 3 econstructor; split*.
      apply* exec_Sseq_1.

    (* Step_ap y ty clsid o [e1; ... ;en] : "y = clsid_step(&(self->o), e1, ..., en)" *)
    - app_exps_eval_det.
      app_find_inst_det.
      app_stmt_step_eval_det'.
      
      (* get the Clight corresponding function *)
      forwards* Hin': find_class_In Hfind.
      pose proof Hstep as Hstep'.
      edestruct Hstep' as (loc_f & f & ? & ? & ? & Htype_fun & ? & ? & Hlengths & ?); eauto.
      rewrite <-type_pres' with (c:=c) (es:=es) (ys:=ys) in Htype_fun; auto.
      forwards Eq: find_class_name Hfind.
      rewrite Eq in *; clear Eq.
      
      (* get the Clight corresponding field *)
      pose proof Hself as Hself'.
      destruct* Hself' as (? & ? & ? & ? & ? & ? & ? & ? & Hobj).
      specializes Hobj Hin; destruct Hobj. 

      (* get outs values *)
      edestruct exprlist_make_out_arg with (le:=le1) (c:=c) as (outs); eauto.
      
      (* recursive funcall evaluation *)
      edestruct Hrec_eval with (c:=c) (e:=e1) (m:=m1) (le:=le1) (outs:=outs); destruct_conjs; eauto.
      + rewrite <-ne_Forall2_lengths with (1:=Evs).
        rewrite Hlengths; simpl; f_equal.
        rewrite app_length; do 2 rewrite <-nelist2list_length.
        f_equal; symmetry; apply* ne_Forall2_lengths.        
      + apply Clight.eval_Eaddrof; apply* evall_self_field.
      + do 3 econstructor; split*.
        *{ apply* exec_Scall.
           - simpl; eauto.
           - eapply Clight.eval_Elvalue.
             + apply* Clight.eval_Evar_global.
             + apply* Clight.deref_loc_reference.
           - econstructor.
             + eapply Clight.eval_Eaddrof.
               apply* evall_self_field.
             + eapply sem_cast_same.
               unfold valid_val; splits*.
               * discriminate.
               * simpl; trivial.
             + apply* eval_exprlist_app.
               apply* exprs_eval_simu.
           - eauto.
         }
        * admit. 

    (* Skip : "skip" *)
    - do 3 econstructor; split*.
      eapply exec_Sskip.

    (* funcall *)
    - forwards* Hfind'': find_class_sub_same Hfind UNIQUE.
      rewrite Hfind' in Hfind''; inverts Hfind''.
      destruct Hstep with (c:=cls)
        as (loc_f' & f' & Hget_loc_f' & Hget_f' & Htype_fun & Hvars_nil & ? & ? & Htr & ?);
        destruct_conjs; eauto.
      forwards Eq: find_class_name Hfind.
      rewrite Eq in Hget_loc_f'; clear Eq.
      rewrite Hget_loc_f' in Hget_loc_f; inverts Hget_loc_f.
      rewrite Hget_f' in Hget_f; inverts Hget_f.

      assert (length f.(Clight.fn_params) = length ((Values.Vptr loc_struct ofs) :: nelist2list vs))
        by (rewrite Hlengths; simpl; f_equal; rewrite Nelist.nelist2list_length; auto).

      forwards* (le_fun & ? & ?): (compat_funcall_pres cls m).
      forwards* Hsub: find_class_sub.
      subst env.
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