From compcert Require Import cfrontend.ClightBigstep.
From compcert Require Import cfrontend.Clight.
From compcert Require Import cfrontend.Ctypes.
From compcert Require Import lib.Integers.
From compcert Require Import lib.Maps.
From compcert Require Import lib.Coqlib.
From compcert Require Errors.
From compcert Require Import common.Separation.
From compcert Require Import common.Values.
From compcert Require Import common.Memory.
From compcert Require Import common.Events.
From compcert Require Import common.Globalenvs.
From compcert Require Import common.Smallstep.
From compcert Require Import common.Behaviors.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import VelusMemory.
From Velus Require Import Ident.
From Velus Require Import Traces.

From Velus Require Import Common.CompCertLib.
From Velus Require Import ObcToClight.MoreSeparation.
From Velus Require Import ObcToClight.SepInvariant.
From Velus Require Import ObcToClight.Generation.
From Velus Require Import ObcToClight.GenerationProperties.
From Velus Require Import ObcToClight.Interface.

From Coq Require Import Program.Tactics.
From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import ZArith.BinInt.
From Coq Require Import Omega.
From Coq Require Import Sorting.Permutation.

Import Obc.Typ.
Import Obc.Syn.
Import Obc.Sem.
Import Obc.Inv.
Import OpAux.

Open Scope list_scope.
Open Scope sep_scope.
Open Scope Z.
Hint Constructors Clight.eval_lvalue Clight.eval_expr.
Hint Resolve  Clight.assign_loc_value.

Hint Resolve Z.divide_refl.

(*****************************************************************)
(** simple occurence predicate                                  **)
(** (to ensure that a statement occurs in the caller body)      **)
(*****************************************************************)

Inductive occurs_in: stmt -> stmt -> Prop :=
| occurs_refl: forall s,
    occurs_in s s
| occurs_ite: forall s e s1 s2,
    occurs_in s s1 \/ occurs_in s s2 ->
    occurs_in s (Ifte e s1 s2)
| occurs_comp: forall s s1 s2,
    occurs_in s s1 \/ occurs_in s s2 ->
    occurs_in s (Comp s1 s2).
Hint Resolve occurs_refl.

Remark occurs_in_ite:
  forall e s1 s2 s,
    occurs_in (Ifte e s1 s2) s ->
    occurs_in s1 s /\ occurs_in s2 s.
Proof.
  intros * Occurs.
  induction s; inversion_clear Occurs as [|? ? ? ? [Hs1|Hs2]|? ? ? [Hs1|Hs2]];
    split; constructor; ((left; now apply IHs1) || (right; now apply IHs2) || idtac).
  - left; auto.
  - right; auto.
Qed.

Remark occurs_in_comp:
  forall s1 s2 s,
    occurs_in (Comp s1 s2) s ->
    occurs_in s1 s /\ occurs_in s2 s.
Proof.
  intros * Occurs.
  induction s; inversion_clear Occurs as [|? ? ? ? [Hs1|Hs2]|? ? ? [Hs1|Hs2]];
    split; constructor; ((left; now apply IHs1) || (right; now apply IHs2) || idtac).
  - left; auto.
  - right; auto.
Qed.
Hint Resolve occurs_in_ite occurs_in_comp.

Lemma occurs_in_wt:
  forall s s' p insts mems vars,
    wt_stmt p insts mems vars s ->
    occurs_in s' s ->
    wt_stmt p insts mems vars s'.
Proof.
  induction s; intros * Wt Occ;
    inv Wt; inversion_clear Occ as [|? ? ? ? [?|?]|? ? ? [?|?]];
      try econstructor; eauto.
Qed.

Lemma occurs_in_No_Naked_Vars:
  forall s2 s1,
    No_Naked_Vars s2 ->
    occurs_in s1 s2 ->
    No_Naked_Vars s1.
Proof.
  induction s2; inversion_clear 1; inversion_clear 1; eauto using No_Naked_Vars;
    take (_ \/ _) and destruct it; auto.
Qed.

Lemma occurs_in_instance_methods:
  forall ys clsid o fid es f p insts mems,
    wt_method p insts mems f ->
    NoDupMembers insts ->
    occurs_in (Call ys clsid o fid es) (m_body f) ->
    (1 < length ys)%nat ->
    M.MapsTo (o, fid) clsid (instance_methods f).
Proof.
  unfold instance_methods, wt_method.
  intros * Wt Nodup Occurs Length.
  induction (m_body f);
    inversion Occurs as [|? ? ? ? [Hs1|Hs2]|? ? ? [Hs1|Hs2]];
    inversion Wt; subst; simpl.
  - rewrite In_rec_instance_methods; eauto.
    eapply occurs_in_wt in Hs1; eauto.
    inv Hs1; assumption.
  - rewrite In_rec_instance_methods; eauto.
    eapply occurs_in_wt in Hs2; eauto.
    inv Hs2; assumption.
  - rewrite In_rec_instance_methods; eauto.
    eapply occurs_in_wt in Hs1; eauto.
    inv Hs1; assumption.
  - rewrite In_rec_instance_methods; eauto.
    eapply occurs_in_wt in Hs2; eauto.
    inv Hs2; assumption.
  - destruct i as [|i is]; try destruct is.
    + contradict Length; apply lt_n_0.
    + contradict Length; simpl; apply lt_irrefl.
    + apply M.add_1; auto.
Qed.

Section PRESERVATION.

  (*****************************************************************)
  (** we work in a well-typed translated program                  **)
  (*****************************************************************)

  Variable (main_node  : ident)
           (prog       : program)
           (tprog      : Clight.program)
           (do_sync    : bool)
           (all_public : bool).
  Let tge              := Clight.globalenv tprog.
  Let gcenv            := Clight.genv_cenv tge.

  Hypothesis (TRANSL : translate do_sync all_public main_node prog = Errors.OK tprog)
             (WT     : wt_program prog).

  Opaque sepconj.


  Hint Resolve wt_val_load_result.
  Hint Constructors wt_stmt.

  Section MatchStates.

    (*****************************************************************)
    (** we work under a caller method of an owner class,            **)
    (** we state various results of semantics preservation using    **)
    (** the memory predicate match_states                           **)
    (*****************************************************************)

    Variable
      (** Obc class *)
      (ownerid  : ident)     (owner  : class)     (prog' : program)

      (** Obc method *)
      (callerid : ident)     (caller : method)

      (** Obc state *)
      (me       : menv)      (ve     : venv)

      (** Clight state *)
      (m        : Mem.mem)   (e      : Clight.env) (le   : temp_env)

      (** Clight self structure *)
      (sb       : block)     (sofs   : ptrofs)

      (** Clight output structure *)
      (outb_co  : option (block * composite))

      (** frame *)
      (P        : massert).

    Hypothesis (Findowner  : find_class ownerid prog = Some (owner, prog'))
               (Findcaller : find_method callerid owner.(c_methods) = Some caller)
               (Hmem       : m |= match_states gcenv prog owner caller (me, ve) (e, le) sb sofs outb_co
                                  ** P).

    Section ExprCorrectness.

      (*****************************************************************)
      (** correctness of expressions                                  **)
      (*****************************************************************)

      (** out->x *)
      Section OutField.

        Variable (x  : ident)
                 (ty : type).
        Let out_ind_field := deref_field out (prefix_fun (c_name owner) (m_name caller)) x (cltype ty).

        Hypothesis (Hin    : In (x, ty) caller.(m_out))
                   (Length : (1 < length caller.(m_out))%nat).

        Lemma evall_out_field:
          forall ve1 le1 m1 P1,
            m1 |= outputrep gcenv owner caller ve1 le1 outb_co ** P1 ->
            exists outb outco d,
              eval_lvalue tge e le1 m1 out_ind_field outb (Ptrofs.repr d)
              /\ outb_co = Some (outb, outco)
              /\ field_offset gcenv x (co_members outco) = Errors.OK d.
        Proof.
          clear Hmem; intros * Hmem.
          apply outputrep_notnil in Hmem as (outb & outco & E &?&?&?); auto.
          apply in_map with (f:=translate_param) in Hin.
          subst out_ind_field; erewrite find_class_name, find_method_name in *; eauto.
          erewrite output_match in Hin; eauto.
          edestruct fieldsrep_field_offset as (d & Hoffset & ?); eauto.
          exists outb, outco, d; split; auto.
          rewrite <- Ptrofs.add_zero_l.
          eapply eval_Efield_struct; eauto.
          - eapply eval_Elvalue; eauto.
            now apply deref_loc_copy.
          - simpl; unfold type_of_inst; eauto.
        Qed.

        Corollary eval_out_field:
          forall v,
            Env.find x ve = Some v ->
            eval_expr tge e le m out_ind_field v.
        Proof.
          intros.
          apply match_states_conj in Hmem as (Hmem &?); rewrite sep_swap in Hmem.
          edestruct evall_out_field as (?&?&?&?& E &?); eauto.
          eapply eval_Elvalue; eauto.
          apply outputrep_notnil in Hmem as (?&?& E' &?&?&?); auto.
          erewrite find_class_name, find_method_name in *; eauto.
          rewrite E in E'; inv E'.
          eapply fieldsrep_deref_mem; eauto.
          erewrite <-output_match; eauto.
          rewrite in_map_iff.
          exists (x, ty); split; auto.
        Qed.

      End OutField.

      (** ̄x *)
      Lemma eval_temp_var:
        forall x ty v,
          In (x, ty) (meth_vars caller) ->
          ~ InMembers x caller.(m_out) ->
          Env.find x ve = Some v ->
          eval_expr tge e le m (Etempvar x (cltype ty)) v.
      Proof.
        intros * Hvars E Find.
        apply match_states_conj in Hmem as (Hmem &?).
        rewrite sep_swap5 in Hmem.
        apply sep_proj1, sep_pure' in Hmem.
        apply eval_Etempvar.
        apply NotInMembers_NotIn with (b := ty) in E.
        unfold meth_vars in Hvars.
        rewrite app_assoc in Hvars.
        eapply not_In2_app in E; eauto.
        apply in_map with (f:=fst) in E.
        eapply Forall_forall in Hmem; eauto.
        unfold match_var in Hmem; simpl in Hmem.
        cases; try contradiction.
        rewrite Find in Hmem; simpl in Hmem; congruence.
      Qed.

      (** x *)
      Corollary eval_var:
        forall x ty v,
          Env.find x ve = Some v ->
          In (x, ty) (meth_vars caller) ->
          eval_expr tge e le m (translate_var owner caller x ty) v.
      Proof.
        intros * Hx Hin; unfold translate_var; simpl.
        destruct (mem_assoc_ident x caller.(m_out)) eqn:E.
        - assert (In (x, ty) caller.(m_out)).
          { apply mem_assoc_ident_true in E as (t'&?).
            assert (In (x, t') (meth_vars caller)) by (unfold meth_vars; rewrite 2 in_app; auto).
            pose proof (m_nodupvars caller); app_NoDupMembers_det; auto.
          }
          destruct_list caller.(m_out) as (?, ?) (?, ?) ? : Out; try contradiction.
          + simpl in E; apply orb_true_iff in E; destruct E as [E|]; try discriminate.
            apply ident_eqb_eq in E; subst x.
            econstructor.
            apply match_states_conj in Hmem as (Hmem &?); rewrite sep_swap in Hmem.
            rewrite outputrep_singleton in Hmem; eauto.
            destruct Hmem as (? & Eq).
            unfold match_var in Eq; cases; rewrite Hx in Eq; congruence.
          + simpl; simpl in E; rewrite E.
            assert (1 < length caller.(m_out))%nat by (rewrite Out; simpl; omega).
            eapply eval_out_field; eauto; rewrite Out; auto.
        - assert (~ InMembers x caller.(m_out)) by
              (apply NotIn_NotInMembers; intro; apply mem_assoc_ident_false; auto).
          destruct_list caller.(m_out) as xt ? ?: Out; simpl in E; try rewrite E;
            eapply eval_temp_var; eauto; rewrite Out; auto.
      Qed.

      (** self->x and &self->o *)
      Section SelfField.

        Variable (x  : ident)
                 (ty : type).
        Let self_ind_field := deref_field self (c_name owner) x (cltype ty).

        Hypothesis (Hmems : In (x, ty) owner.(c_mems)).

        Lemma evall_self_field:
          exists d,
            eval_lvalue tge e le m self_ind_field sb (Ptrofs.add sofs (Ptrofs.repr d))
            /\ field_offset gcenv x (make_members owner) = Errors.OK d
            /\ 0 <= d <= Ptrofs.max_unsigned.
        Proof.
          apply match_states_conj in Hmem as (Hmem &?&?&?&?).
          intros.
          pose proof (find_class_name _ _ _ _ Findowner); subst.
          edestruct make_members_co as (? & Hco & ? & Eq & ? & ?); eauto.
          edestruct staterep_field_offset as (d & ? & ?); eauto.
          exists d; split; [|split]; auto.
          - eapply eval_Efield_struct; eauto.
            + eapply eval_Elvalue; eauto.
              now apply deref_loc_copy.
            + simpl; unfold type_of_inst; eauto.
            + now rewrite Eq.
          - split.
            + eapply field_offset_in_range'; eauto.
            + assert (0 <= Ptrofs.unsigned sofs) by eauto; omega.
        Qed.

        Corollary eval_self_field:
          forall v,
            find_val x me = Some v ->
            eval_expr tge e le m self_ind_field v.
        Proof.
          intros.
          edestruct evall_self_field as (?&?&?&?); eauto.
          apply match_states_conj in Hmem as (Hmem &?).
          eapply eval_Elvalue; eauto.
          erewrite find_class_name in Hmem; eauto.
          eapply staterep_deref_mem; eauto.
          rewrite Ptrofs.unsigned_repr; auto.
        Qed.

        (** &self->o : appears only as an additional parameter of funcalls *)
        Lemma eval_self_inst:
          forall o c',
            In (o, c') (c_objs owner) ->
            exists d,
              eval_expr tge e le m (ptr_obj owner c' o) (Vptr sb (Ptrofs.add sofs (Ptrofs.repr d)))
              /\ field_offset gcenv o (make_members owner) = Errors.OK d
              /\ 0 <= Ptrofs.unsigned sofs + d <= Ptrofs.max_unsigned.
        Proof.
          apply match_states_conj in Hmem as (Hmem &?&?&?&?); clear Hmem.
          intros * Hin.
          pose proof (find_class_name _ _ _ _ Findowner); subst.
          edestruct make_members_co as (? & Hco & ? & Eq & ? & ?); eauto.
          destruct (struct_in_bounds_sizeof _ _ _ Hco).
          edestruct wt_program_find_class as [[Find]]; eauto.
          eapply Forall_forall in Find; eauto; simpl in Find.
          apply not_None_is_Some in Find.
          destruct Find as [(?, ?)]; eauto.
          edestruct struct_in_struct_in_bounds' as (d & ? & Struct); eauto.
          exists d; split; [|split]; auto.
          + apply eval_Eaddrof.
            eapply eval_Efield_struct; eauto.
            * eapply eval_Elvalue; eauto.
              now apply deref_loc_copy.
            * simpl; unfold type_of_inst; eauto.
            * now rewrite Eq.
          + destruct Struct.
            split; try omega.
            apply (Z.le_le_add_le 0 (sizeof_struct (Clight.globalenv tprog) 0 (make_members c))); try omega.
            apply sizeof_struct_incr.
        Qed.

      End SelfField.

      Theorem expr_correct:
        forall ex v,
          wt_exp owner.(c_mems) (meth_vars caller) ex ->
          exp_eval me ve ex (Some v) ->
          eval_expr tge e le m (translate_exp owner caller ex) v.
      Proof.
        induction ex as [x| |cst|op| |x]; intros * WTex Ev; inv Ev; inv WTex; simpl.

        (* Var x ty : "x" *)
        - eapply eval_var; eauto.

        (* State x ty : "self->x" *)
        - eapply eval_self_field; eauto.

        (* Const c ty : "c" *)
        - destruct cst; constructor.

        (* Unop op e ty : "op e" *)
        - destruct op; simpl in *; econstructor; eauto;
            apply match_states_conj in Hmem as (?&?&?&?); rewrite type_pres.
          + erewrite sem_unary_operation_any_mem; eauto.
            eapply wt_val_not_vundef_nor_vptr; eauto.
          + match goal with
              H: match Ctyping.check_cast ?x ?y with _ => _ end = _ |- _ =>
              destruct (Ctyping.check_cast x y); inv H
            end.
            erewrite sem_cast_any_mem; eauto.
            eapply wt_val_not_vundef_nor_vptr; eauto.

        (* Binop op e1 e2 : "e1 op e2" *)
        - simpl in *. unfold translate_binop.
          econstructor; eauto.
          apply match_states_conj in Hmem as (?&?&?&?); rewrite 2 type_pres.
          erewrite sem_binary_operation_any_cenv_mem; eauto;
            eapply wt_val_not_vundef_nor_vptr; eauto.

        (* Valid x ty *)
        - eapply eval_var; eauto.
      Qed.

      Corollary exprs_correct:
        forall es vs,
          let es' := map (translate_exp owner caller) es in
          Forall (wt_exp owner.(c_mems) (meth_vars caller)) es ->
          Forall2 (fun e v => exp_eval me ve e (Some v)) es vs ->
          Clight.eval_exprlist tge e le m es'
                               (list_type_to_typelist (map Clight.typeof es')) vs.
      Proof.
        Hint Constructors Clight.eval_exprlist.
        intros * WF EV; subst es'.
        induction EV; inv WF; econstructor;
          ((eapply expr_correct; eauto)
           || (apply match_states_conj in Hmem as (?&?&?&?); rewrite type_pres; apply sem_cast_same; eauto)
           || auto).
      Qed.

    End ExprCorrectness.

    Hint Resolve exprs_correct.

    Section AssignCorrectness.

      (*****************************************************************)
      (** 'Hoare triple' for assignments, the leaves of the program   **)
      (*****************************************************************)

      Variable (x  : ident) (ty : type) (v : val)
               (ae : expr).

      Hypothesis (WTv : wt_val v ty)
                 (Teq : Clight.typeof ae = cltype ty)
                 (Hin : In (x, ty) (meth_vars caller)).

      (** x = ae : x can be a temp or an indirect access field (output variable) *)
      Lemma exec_assign:
        forall m1 le1 ve1 P1,
          m1 |= outputrep gcenv owner caller ve1 le1 outb_co
                ** varsrep caller ve1 le1
                ** P1 ->
          eval_expr tge e le1 m1 ae v ->
          exists m' le',
            exec_stmt_fe function_entry2 tge e le1 m1
                      (assign owner caller x (cltype ty) ae)
                      E0 le' m' Out_normal
            /\ m' |= outputrep gcenv owner caller (Env.add x v ve1) le' outb_co
                     ** varsrep caller (Env.add x v ve1) le'
                     ** P1
            /\ forall v, le1 ! self = Some v -> le' ! self = Some v.
      Proof.
        clear Hmem; intros * Hmem Ev.
        assert (x <> self)
          by (intro; subst;  eapply (m_notreserved self); eauto;
              eapply In_InMembers; eauto).
        destruct (mem_assoc_ident x caller.(m_out)) eqn:E.

        (* x is a caller output *)
        - assert (In (x, ty) caller.(m_out)) as Hin'.
          { apply mem_assoc_ident_true in E as (t &?).
            assert (In (x, t) (meth_vars caller)) by (do 2 setoid_rewrite in_app; auto).
            pose proof (m_nodupvars caller); app_NoDupMembers_det; auto.
          }
          unfold assign.
          destruct_list caller.(m_out) as (x', t') (x'', t'') outs : Houts; try contradiction.

          (* only one output: x is a temporary *)
          + inversion_clear Hin' as [Eq|Eq]; inv Eq.
            exists m1, (PTree.set x v le1); rewrite PTree.gso; intuition; unfold exec_stmt_fe; eauto using exec_stmt.
            eapply sep_imp; eauto.
            * eapply outputrep_assign_singleton_mem; eauto.
            * rewrite varsrep_add; eauto.

          (* several outputs: x is an indirect access out->x *)
          + assert (1 < Datatypes.length (m_out caller))%nat by (rewrite Houts; simpl; omega).
            assert (In (x, ty) caller.(m_out)) by now rewrite Houts.
            rewrite E.
            edestruct outputrep_assign_gt1_mem as (m' & ?&?&?& Hco & Hofs &?&?); eauto using output_match.
            exists m', le1; intuition; auto.
            * edestruct evall_out_field with (m1 := m1) as (?&?&?&?& Hco' & Hofs'); eauto.
              rewrite Hco in Hco'; inv Hco'. simpl in Hofs.
              change (prog_comp_env tprog) with gcenv in Hofs; rewrite Hofs in Hofs'; inv Hofs'.
              econstructor; eauto; simpl.
              rewrite Teq; eauto.
            * eapply sep_imp; eauto.
              rewrite varsrep_corres_out; eauto.

        (* x is not a caller output *)
        - assert (~ InMembers x caller.(m_out)) by
              (apply NotIn_NotInMembers; intro; apply mem_assoc_ident_false; auto).
          exists m1, (PTree.set x v le1); rewrite PTree.gso; intuition; auto.
          + unfold assign.
            destruct_list caller.(m_out) : Houts; try rewrite E;
              unfold exec_stmt_fe; eauto using exec_stmt.
          + rewrite varsrep_add in Hmem.
            eapply outputrep_assign_var_mem; eauto using output_match.
      Qed.

      Corollary exec_assign_match_states:
          eval_expr tge e le m ae v ->
          exists m' le',
            exec_stmt_fe function_entry2 tge e le m
                      (assign owner caller x (cltype ty) ae)
                      E0 le' m' Out_normal
            /\ m' |= match_states gcenv prog owner caller (me, Env.add x v ve) (e, le') sb sofs outb_co
                     ** P .
      Proof.
        intros.
        apply match_states_conj in Hmem as (Hmem & ?).
        rewrite sep_swap, sep_swap45, sep_swap34, sep_swap23 in Hmem.
        edestruct exec_assign as (m' & le' & ?&?&?); eauto.
        exists m', le'; intuition.
        apply match_states_conj; intuition; eauto using m_nodupvars.
        rewrite sep_swap, sep_swap45, sep_swap34, sep_swap23; auto.
      Qed.

    End AssignCorrectness.

    Section FuncallAssignCorrectness.

      (*****************************************************************)
      (** assignments after a funcall are particular as they do not   **)
      (** correspond to source statements                             **)
      (** we assume that the callee exists in a child class, with     **)
      (** more at least two outputs, meaning that a local output      **)
      (** structure is declared in the caller                         **)
      (*****************************************************************)

      Variable
        (** Child class *)
        (cid       : ident)   (c      : class)     (prog'' : program)

        (** Callee *)
        (fid       : ident)   (callee : method)

        (** the callee environment *)
        (ve_callee : venv)

        (** the local output structure *)
        (o         : ident)   (instco : composite) (instb  : block).

      Hypothesis (Findchild  : find_class cid prog = Some (c, prog''))
                 (Findcallee : find_method fid c.(c_methods) = Some callee)
                 (Len        : (1 < Datatypes.length (m_out callee))%nat)
                 (Ho         : e ! o = Some (instb, type_of_inst (prefix_fun cid fid)))
                 (Hinstco    : gcenv ! (prefix_fun cid fid) = Some instco).

      (** o.x : a local output structure field is evaluated to the value found in the callee env *)
      Lemma eval_inst_field:
        forall x ty v le2 m1 P1,
          let inst_field := Efield (Evar o (type_of_inst (prefix_fun cid fid))) x (cltype ty) in
          m1 |= fieldsrep gcenv ve_callee (co_members instco) instb ** P1 ->
          In (x, ty) callee.(m_out) ->
          Env.find x ve_callee = Some v ->
          eval_expr tge e le2 m1 inst_field v.
      Proof.
        clear Hmem Findcaller Findowner; intros * Hmem Hin ?.
        apply in_map with (f:=translate_param) in Hin.
        erewrite output_match in Hin; eauto.
        edestruct fieldsrep_field_offset as (d & Hoffset & ?); eauto.
        eapply eval_Elvalue; eauto.
        - eapply eval_Efield_struct; eauto.
          + eapply eval_Elvalue; eauto.
            now apply deref_loc_copy.
          + simpl; unfold type_of_inst; eauto.
        - eapply fieldsrep_deref_mem; eauto.
          rewrite Ptrofs.unsigned_zero, Ptrofs.unsigned_repr; auto.
      Qed.


      (*****************************************************************)
      (** after a call, we are not in match_states: the according     **)
      (** structure is 'filled' with return values                    **)
      (** the variables to be assigned are again temporaries or       **)
      (** indirect field accesses                                     **)
      (*****************************************************************)

      Variables
        (** the memory just after the call *)
        (m1 : Mem.mem)
        (** frame *)
        (P1 : massert).

      Hypothesis (Hmem1 : m1 |= fieldsrep gcenv ve_callee (co_members instco) instb
                                ** outputrep gcenv owner caller ve le outb_co
                                ** varsrep caller ve le
                                ** P1).

      Lemma exec_funcall_assign_outs:
        forall outs xs vs,
          let tyo := type_of_inst (prefix_fun cid fid) in
          incl outs callee.(m_out) ->
          Forall2 (fun y xt => In (y, snd xt) (meth_vars caller)) xs outs ->
          wt_vals vs outs ->
          Forall2 (fun xt v => Env.find (fst xt) ve_callee = Some v) outs vs ->
          exists m' le',
            exec_stmt_fe function_entry2 tge e le m1
                      (funcall_assign owner caller xs o tyo outs)
                      E0 le' m' Out_normal
            /\ m' |= fieldsrep gcenv ve_callee (co_members instco) instb
                    ** outputrep gcenv owner caller (Env.adds xs vs ve) le' outb_co
                    ** varsrep caller (Env.adds xs vs ve) le'
                    ** P1
            /\ forall v, le ! self = Some v -> le' ! self = Some v.
      Proof.
        clear Hmem.
        intro outs; revert dependent m1; clear Hmem1 m1; revert ve le.
        induction outs as [|(x, t)]; intros * Hmem ??? Incl Hins WTvs Hvs;
          inversion_clear Hins as [|y]; inv WTvs; inv Hvs; unfold funcall_assign; simpl.
        - rewrite Env.adds_nil_l.
          exists m1, le; intuition; unfold exec_stmt_fe;  eauto using exec_stmt.
        - apply incl_cons' in Incl as (?&?).
          rewrite sep_swap, sep_swap23 in Hmem.
          edestruct exec_assign with (x := y) (ty := t) (ae := Efield (Evar o tyo) x (cltype t))
            as (l_x & le_x & ? & Hmem_x & ?); eauto.
          { rewrite sep_swap23, sep_swap in Hmem.
            eapply eval_inst_field; eauto.
          }
          clear Hmem.
          rewrite sep_swap23, sep_swap in Hmem_x.
          edestruct IHouts as (m' & le' & ? & ?); eauto.
          change E0 with (Eapp E0 (Eapp E0 E0)).
          exists m', le'; intuition; unfold exec_stmt_fe; eauto using exec_stmt.
      Qed.

      Corollary exec_funcall_assign:
        forall xs vs,
          let tyo := type_of_inst (prefix_fun cid fid) in
          Forall2 (fun y xt => In (y, snd xt) (meth_vars caller)) xs callee.(m_out) ->
          wt_vals vs callee.(m_out) ->
          Forall2 (fun xt v => Env.find (fst xt) ve_callee = Some v) callee.(m_out) vs ->
          exists m' le',
            exec_stmt_fe function_entry2 tge e le m1
                      (funcall_assign owner caller xs o tyo callee.(m_out))
                      E0 le' m' Out_normal
            /\ m' |= fieldsrep gcenv ve_callee (co_members instco) instb
                    ** outputrep gcenv owner caller (Env.adds xs vs ve) le' outb_co
                    ** varsrep caller (Env.adds xs vs ve) le'
                    ** P1
            /\ forall v, le ! self = Some v -> le' ! self = Some v.
      Proof.
        intros; eapply exec_funcall_assign_outs; eauto.
        apply incl_refl.
      Qed.

    End FuncallAssignCorrectness.

    (*****************************************************************)
    (** the expected execution and memory state after a funcall,    **)
    (** depending on the numbers of outputs:                        **)
    (**   0: no 'out' pointer parameter, we only need staterep for  **)
    (**      the sub-state, and we get an updated staterep after    **)
    (**      the call, with no return value                         **)
    (**   1: no 'out' pointer parameter, we only need staterep for  **)
    (**      the sub-state, and we get an updated staterep after    **)
    (**      the call, with only one return value                   **)
    (**   n: 'out' pointer parameter, we need both staterep for     **)
    (**      the sub-state and fieldsrep for the output structure,  **)
    (**      we get an updated staterep and a the output structure  **)
    (**      filled with the return values                          **)
    (*****************************************************************)

    Definition call_spec (c: class) (f: method) (vs rvs: list val) (me me': menv) : Prop :=
      forall sb sofs m P,
        bounded_struct_of_class tge c sofs ->
        case_out f
                 (
                   m |= staterep gcenv prog c.(c_name) me sb (Ptrofs.unsigned sofs) ** P ->
                   exists m' fd,
                     method_spec c f prog fd
                     /\ eval_funcall_fe function_entry2 tge m (Internal fd)
                                       (Vptr sb sofs :: vs) E0 m' Vundef
                     /\ m' |= staterep gcenv prog c.(c_name) me' sb (Ptrofs.unsigned sofs) ** P
                 )
                 (fun _ _ =>
                    m |= staterep gcenv prog c.(c_name) me sb (Ptrofs.unsigned sofs) ** P ->
                    exists m' fd rv,
                      method_spec c f prog fd
                      /\ eval_funcall_fe function_entry2 tge m (Internal fd)
                                        (Vptr sb sofs :: vs) E0 m' rv
                      /\ rvs = [rv]
                      /\ m' |= staterep gcenv prog c.(c_name) me' sb (Ptrofs.unsigned sofs) ** P
                 )
                 (fun outs =>
                    forall instb instco,
                      gcenv ! (prefix_fun c.(c_name) f.(m_name)) = Some instco ->
                      m |= staterep gcenv prog c.(c_name) me sb (Ptrofs.unsigned sofs)
                           ** fieldsrep gcenv vempty instco.(co_members) instb
                           ** P ->
                      exists ve_f m' fd,
                        method_spec c f prog fd
                        /\ eval_funcall_fe function_entry2 tge m (Internal fd)
                                          (Vptr sb sofs :: var_ptr instb :: vs) E0 m' Vundef
                        /\ Forall2 (fun xt v => Env.find (fst xt) ve_f = Some v) outs rvs
                        /\ m' |= staterep gcenv prog c.(c_name) me' sb (Ptrofs.unsigned sofs)
                                ** fieldsrep gcenv ve_f instco.(co_members) instb
                                ** P
                 ).

    (*****************************************************************)
    (** 'Hoare triple' for funcalls, assuming call_spec for the     **)
    (** callee as a mutual induction hypothesis                     **)
    (*****************************************************************)

    Lemma exec_binded_funcall:
      forall ys o es me_o' vs rvs cid c prog'' fid callee,
        find_class cid prog' = Some (c, prog'') ->
        find_method fid c.(c_methods) = Some callee ->
        call_spec c callee vs rvs (instance_match o me) me_o' ->
        Forall2 (fun y xt => In (y, snd xt) (meth_vars caller)) ys callee.(m_out) ->
        wt_vals rvs callee.(m_out) ->
        ((1 < Datatypes.length callee.(m_out))%nat -> M.MapsTo (o, fid) cid (instance_methods caller)) ->
        NoDup ys ->
        In (o, cid) (c_objs owner) ->
        Forall2 (fun e xt => Clight.typeof e = cltype (snd xt)) es callee.(m_in) ->
        eval_exprlist tge e le m es (list_type_to_typelist (map Clight.typeof es)) vs ->
        wt_mem me_o' prog'' c ->
        exists m' le',
          exec_stmt_fe function_entry2 tge e le m
                    (binded_funcall (rev prog) owner caller ys cid o fid es)
                    E0 le' m' Out_normal /\
          m' |= match_states gcenv prog owner caller
                  (add_inst o me_o' me, Env.adds_opt ys (map Some rvs) ve)
                  (e, le') sb sofs outb_co
                ** P.
    Proof.
      intros * Findchild Findcallee CallSpec Hins WTrvs Hinstmth Nodup Hin Hts Evs WTme_o.

      (* get the Clight function *)
      assert (find_class cid prog = Some (c, prog'')) as Findchild'
          by (eapply find_class_chained; eauto);
        edestruct methods_corres with (3 := Findchild')
        as (loc_f & fun_f & Gf & Gptrf & Spec_f); eauto.
      assert (forall targs tres cc,
                 eval_expr tge e le m (Evar (prefix_fun cid fid) (Tfunction targs tres cc))
                           (Vptr loc_f Ptrofs.zero)).
      { intros; eapply eval_Elvalue.
        - apply eval_Evar_global; eauto.
          rewrite <-not_Some_is_None.
          intros (?, ?) Hget.
          apply match_states_conj in Hmem as (?&?&?&?& He).
          apply He in Hget; destruct Hget as (? & ? & Eqpref).
          unfold prefix_fun, prefix_out in Eqpref.
          apply prefix_injective in Eqpref; destruct Eqpref.
          + apply fun_not_out; auto.
          + apply fun_id_valid.
          + apply out_valid.
        - apply deref_loc_reference; auto.
      }
      assert (Genv.find_funct (Genv.globalenv tprog) (Vptr loc_f Ptrofs.zero)
              = Some (Internal fun_f))
        by auto.
      assert (type_of_fundef (Internal fun_f)
              = Tfunction
                  (case_out callee
                            (Tcons (type_of_inst_p cid) (list_type_to_typelist (map Clight.typeof es)))
                            (fun _ _ => Tcons (type_of_inst_p cid) (list_type_to_typelist (map Clight.typeof es)))
                            (fun _ => Tcons (type_of_inst_p cid)
                                         (Tcons (type_of_inst_p (prefix_fun cid fid))
                                                (list_type_to_typelist (map Clight.typeof es)))))
                  (case_out callee Tvoid (fun _ t => cltype t) (fun _ => Tvoid))
                  AST.cc_default) as Type_f.
      { simpl; unfold type_of_function.
        destruct Spec_f as (Params_f & Return_f & CC_f &?).
        rewrite Params_f, Return_f, CC_f; simpl; f_equal.
        erewrite find_class_name, find_method_name; eauto.
        unfold case_out; destruct_list (m_out callee) as (?,?) (?,?) ?; simpl;
          erewrite types_pres'; eauto.
      }

      (* get the &self->o parameter *)
      edestruct eval_self_inst as (d & ?& Hofs &?); eauto.
      assert (Cop.sem_cast (Vptr sb (Ptrofs.add sofs (Ptrofs.repr d)))
                           (type_of_inst_p cid) (type_of_inst_p cid) m
              = Some (Vptr sb (Ptrofs.add sofs (Ptrofs.repr d)))) by auto.
      apply match_states_conj in Hmem as (Hmem & ?&?&?&?).
      (* the sub-structure is well-sized *)
      assert (bounded_struct_of_class tge c (Ptrofs.repr (Ptrofs.unsigned sofs + d))).
      { unfold bounded_struct_of_class.
        edestruct make_members_co as (?&?&?& <- &?); eauto.
        rewrite Ptrofs.unsigned_repr; auto.
        eapply struct_in_struct_in_bounds; eauto.
        - eapply Consistent; eauto.
        - eapply field_translate_obj_type; eauto.
      }

      (* prepare the induction invariant *)
      erewrite find_class_name in Hmem; eauto.
      pose proof (conj Hin Hmem) as Hmem';
        eapply staterep_extract in Hmem' as (objs & objs' & ? & E & Hofs' & Hmem'); eauto.
      clear Hmem; rename Hmem' into Hmem.
      erewrite <-(find_class_name cid) in Hmem; eauto.
      rewrite Hofs' in Hofs; inv Hofs.
      rewrite <- (Ptrofs.unsigned_repr (Ptrofs.unsigned sofs + d)) in Hmem; auto.
      assert (0 <= d <= Ptrofs.max_unsigned).
      { assert (0 <= Ptrofs.unsigned sofs) by eauto.
        split; try omega.
        edestruct field_offset_type; eauto.
        eapply field_offset_rec_in_range; eauto.
      }
      assert (~ InMembers o (objs ++ objs'))
        by (eapply NoDupMembers_app_cons; setoid_rewrite <-E; apply c_nodupobjs).


      unfold binded_funcall.
      pose proof Findchild';
        apply find_class_rev in Findchild' as (cls & Findchild'); auto.
      rewrite Findchild', Findcallee.
      unfold call_spec in CallSpec.
      unfold case_out in Type_f, CallSpec.
      destruct_list callee.(m_out) as (a, ta) (b, tb) ? : Hout;
        inversion Hins as [|x ???? Hins']; try inv Hins';
          inversion WTrvs as [|????? WTrvs']; try inv WTrvs'.

      (* no output *)
      - (* get the induction invariant *)
        edestruct CallSpec as (m' & ? & Spec_f' & EvalF & Hmem'); eauto.
        clear Hmem.
        erewrite find_class_name in Hmem'; eauto.
        eapply method_spec_eq with (2 := Spec_f) in Spec_f'; eauto; subst.
        rewrite <- (Ptrofs.unsigned_repr d), <- Ptrofs.add_unsigned in EvalF; eauto.

        exists m', le; split.
        + unfold funcall.
          change le with (set_opttemp None Vundef le).
          econstructor; simpl; eauto using eval_exprlist.
        + rewrite Env.adds_opt_nil_l.
          apply match_states_conj; intuition; eauto.
          erewrite find_class_name; eauto.
          eapply staterep_extract; eauto.
          exists objs, objs', d; intuition; eauto.
          eapply sep_imp; eauto.
          * unfold instance_match; rewrite find_inst_gss.
            rewrite Ptrofs.unsigned_repr; auto.
          * repeat apply sep_imp'; auto.
            apply staterep_objs_not_in; auto.

      (* one output *)
      - (* get the induction invariant *)
        edestruct CallSpec as (m' & ? & rv & Spec_f' & EvalF & Erv & Hmem'); eauto.
        clear Hmem.
        erewrite find_class_name in Hmem'; eauto.
        inv Erv.
        eapply method_spec_eq with (2 := Spec_f) in Spec_f'; eauto; subst.
        rewrite <- (Ptrofs.unsigned_repr d), <- Ptrofs.add_unsigned in EvalF; eauto.

        (* get the only assignment after the call *)
        rewrite sep_swap34, sep_swap23, sep_swap,
        sep_swap67, sep_swap56, sep_swap45, sep_swap34, sep_swap23 in Hmem'.
        edestruct exec_assign with (x := x) (ty := ta)
                                   (ae := Etempvar (prefix fid a) (cltype ta))
                                   (le1 := PTree.set (prefix fid a) rv le)
          as (m'' & le' & ? & Hmem'' & Hself);
          eauto using eval_expr, PTree.gss.
        { eapply sep_imp; eauto.
          - apply outputrep_add_prefix.
          - repeat apply sep_imp'; auto.
            apply varsrep_add'''.
            intro; eapply (m_notprefixed (prefix fid a)); auto using prefixed.
            unfold meth_vars; rewrite app_assoc, InMembers_app; eauto.
        }
        clear Hmem'.

        exists m'', le'; split.
        + change E0 with (Eapp E0 (Eapp E0 E0)).
          unfold funcall.
          eapply exec_Sseq_1; eauto.
          change (PTree.set (prefix fid a) rv le) with (set_opttemp (Some (prefix fid a)) rv le).
          econstructor; simpl; eauto using eval_exprlist.
        + simpl map; rewrite Env.adds_opt_cons_cons, Env.adds_opt_nil_l.
          apply match_states_conj; intuition; eauto using m_nodupvars.
          * erewrite find_class_name; eauto.
            eapply staterep_extract; eauto.
            exists objs, objs', d; intuition; eauto.
            rewrite sep_swap34, sep_swap23, sep_swap,
            sep_swap67, sep_swap56, sep_swap45, sep_swap34, sep_swap23.
            eapply sep_imp; eauto.
            repeat apply sep_imp'; auto.
            -- unfold instance_match; rewrite find_inst_gss.
               rewrite Ptrofs.unsigned_repr; auto.
            -- apply staterep_objs_not_in; auto.
          * apply Hself.
            rewrite PTree.gso; auto.
            intro Eself; apply self_not_prefixed; rewrite Eself; auto using prefixed.

      (* multiple outputs *)
      - (* get the local structure *)
        assert (M.MapsTo (o, fid) cid (instance_methods caller))
          by (apply Hinstmth; simpl; omega).
        rewrite sep_swap45, sep_swap34, sep_swap23, sep_swap in Hmem.
        eapply subrep_extract in Hmem as (instb & instco & xs & xs' &?& Hinstco &?& Hmem); eauto.
        pose proof Hinstco;
          erewrite <-(find_class_name cid), <-(find_method_name fid) in Hinstco; eauto.

        (* get the &o parameter *)
        assert (eval_expr tge e le m (Eaddrof (Evar (prefix_out o fid) (type_of_inst (prefix_fun cid fid)))
                                              (pointer_of (type_of_inst (prefix_fun cid fid))))
                          (Vptr instb Ptrofs.zero))
          by (constructor; constructor; auto).
        assert (Cop.sem_cast (Vptr instb Ptrofs.zero)
                             (Clight.typeof
                                (Eaddrof (Evar (prefix_out o fid) (type_of_inst (prefix_fun cid fid)))
                                         (pointer_of (type_of_inst (prefix_fun cid fid)))))
                             (pointer_of (type_of_inst (prefix_fun cid fid))) m
                = Some (Vptr instb Ptrofs.zero)) by auto.

        (* get the induction invariant *)
        rewrite sep_swap23, sep_swap in Hmem.
        edestruct CallSpec as (ve_f & m' & ? & Spec_f' & EvalF & ? & Hmem'); eauto.
        erewrite find_class_name in Hmem'; eauto.
        clear Hmem.
        eapply method_spec_eq with (2 := Spec_f) in Spec_f'; eauto; subst.
        rewrite <- (Ptrofs.unsigned_repr d), <- Ptrofs.add_unsigned in EvalF; eauto.

        (* get the multiple assignments after the call *)
        assert (1 < Datatypes.length (m_out callee))%nat by (rewrite Hout; simpl; omega).
        rewrite sep_swap, sep_swap56, sep_swap45, sep_swap34, sep_swap23,
        sep_swap78, sep_swap67, sep_swap56, sep_swap45, sep_swap34 in Hmem'.
        edestruct exec_funcall_assign as (m'' & le' & ? & Hmem'' & Hself);
          eauto; try rewrite Hout; eauto.
        clear Hmem'.

        exists m'', le'; split.
        + change E0 with (Eapp E0 (Eapp E0 E0)).
          unfold funcall.
          rewrite <-Hout.
          eapply exec_Sseq_1; eauto.
          change le with (set_opttemp None Vundef le).
          econstructor; simpl; eauto using eval_exprlist.
        + apply match_states_conj; intuition; eauto using m_nodupvars.
          erewrite find_class_name; eauto.
          eapply staterep_extract; eauto.
          exists objs, objs', d; intuition; eauto.
          rewrite sep_swap45, sep_swap34, sep_swap23, sep_swap.
          eapply subrep_extract; eauto.
          exists instb, instco, xs, xs'; intuition.
          rewrite Env.adds_opt_is_adds; auto.
          rewrite sep_swap56, sep_swap45, sep_swap34, sep_swap23,
          sep_swap78, sep_swap67, sep_swap56, sep_swap45, sep_swap34,
          sep_swap45.
          eapply sep_imp; eauto using fieldsrep_any_empty.
          repeat apply sep_imp'; eauto.
          * unfold instance_match; rewrite find_inst_gss.
            rewrite Ptrofs.unsigned_repr; auto.
          * apply staterep_objs_not_in; auto.
    Qed.

  End MatchStates.


  (*****************************************************************)
  (** The main correctness result, shown by mutual induction:     **)
  (** the usual scheme with induction on the program is not       **)
  (** adapted because the generation function is monadic, and not **)
  (** recursive                                                   **)
  (** we have to perform the mutual induction on suffixes though, **)
  (** to be able to use the previous results                      **)
  (*****************************************************************)

  Hypothesis SpecIO :
    forall ome ome' clsid f vos rvos,
      Forall (fun vo => vo <> None) vos ->
      stmt_call_eval prog ome clsid f vos ome' rvos ->
      Forall (fun x => x <> None) rvos.

  Hypothesis NO_NAKED_VARS: Forall_methods (fun m => No_Naked_Vars m.(m_body)) prog.

  Theorem mutual_correctness:
    (forall p me ve s me' ve' ownerid owner prog' callerid caller m e le outb_co sb sofs P,
        suffix p prog ->
        stmt_eval p me ve s (me', ve') ->
        find_class ownerid prog = Some (owner, prog') ->
        find_method callerid owner.(c_methods) = Some caller ->
        occurs_in s caller.(m_body) ->
        m |= match_states gcenv prog owner caller (me, ve) (e, le) sb sofs outb_co
             ** P ->
        exists m' le',
          exec_stmt_fe function_entry2 tge e le m
                    (translate_stmt (rev prog) owner caller s)
                    E0 le' m' Out_normal
          /\ m' |= match_states gcenv prog owner caller (me', ve') (e, le') sb sofs outb_co
                  ** P)
    /\
    (forall p me cid fid c f vs rvs prog' me',
        suffix p prog ->
        stmt_call_eval p me cid fid (map Some vs) me' (map Some rvs) ->
        find_class cid prog = Some (c, prog') ->
        find_method fid c.(c_methods) = Some f ->
        wt_vals vs f.(m_in) ->
        wt_mem me prog c ->
        call_spec c f vs rvs me me').
  Proof.
    (* get the result in mutual induction form using a cut *)
    cut ((forall p me ve s (me_ve': menv * venv),
             stmt_eval p me ve s me_ve' ->
             suffix p prog ->
             forall ownerid owner prog' callerid caller m e le outb_co sb sofs P,
               let (me', ve') := me_ve' in
               forall (Findowner  : find_class ownerid prog = Some (owner, prog'))
                 (Findcaller : find_method callerid owner.(c_methods) = Some caller)
                 (Hmem       : m |= match_states gcenv prog owner caller (me, ve) (e, le) sb sofs outb_co ** P)
                 (Occurs     : occurs_in s caller.(m_body))
                 (NoNaked    : No_Naked_Vars s)
                 (WTs        : wt_stmt prog' owner.(c_objs) owner.(c_mems) (meth_vars caller) s),
               exists m' le',
                 exec_stmt_fe function_entry2 tge e le m
                           (translate_stmt (rev prog) owner caller s) E0 le' m' Out_normal
                 /\ m' |= match_states gcenv prog owner caller (me', ve') (e, le') sb sofs outb_co ** P)
         /\
         (forall p me cid fid vos me' rvos,
             stmt_call_eval p me cid fid vos me' rvos ->
             suffix p prog ->
             forall c f vs rvs prog',
               find_class cid prog = Some (c, prog') ->
               find_method fid c.(c_methods) = Some f ->
               wt_vals vs f.(m_in) ->
               wt_mem me prog' c ->
               vos = map Some vs ->
               rvos = map Some rvs ->
               call_spec c f vs rvs me me')).
    { intros (Hstmt & Hcall); split; eauto.
      intros * ???? Occurs ?.
      eapply (Hstmt p me ve s (me', ve')); eauto.
      - eapply occurs_in_No_Naked_Vars with (2 := Occurs); eauto.
        eapply Forall_methods_find with (1 := NO_NAKED_VARS); eauto.
      - eapply occurs_in_wt with (2 := Occurs); eauto.
        eapply wt_class_find_method; eauto.
        eapply wt_program_find_class; eauto.
    }

    Opaque match_states sepconj.
    apply stmt_eval_call_ind; [| |
                               |intros ?????????? IH1 ? IH2
                               |intros ????????????? IH|
                               |intros * Findcl Findmth ?? IH Hrvos ? * Findcl' Findmth']; intros;
      try inversion_clear WTs as [| | | |????????? Findcl Findmth|];
      try inv NoNaked; simpl.

    (* x = e *)
    - eapply exec_assign_match_states; eauto using expr_correct.

    (* state(x) = e  *)
    - edestruct evall_self_field as (?&?& Hofs' &?); eauto.
      take (In _ (c_mems owner))
           and edestruct match_states_assign_state_mem with (4 := it)
        as (m' & ? & Hofs & ? & Hmem'); eauto.
      rewrite Hofs in Hofs'; inv Hofs'.
      exists m', le; intuition.
      econstructor; eauto using expr_correct; simpl.
      + rewrite type_pres; eauto.
      + rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr; auto.

    (* xs = (i : c).f(es) *)
    - take (stmt_call_eval _ _ _ _ _ _ _) and rename it into Ev.
      eapply stmt_call_eval_suffix in Ev; eauto.
      assert (Forall (fun vo => vo <> None) vos) as HnNone
          by (eapply no_vars_in_args_spec; eauto).
      assert (exists vs, vos = map Some vs) as (vs & ?)
          by (eapply not_None_is_Some_Forall; auto).
      assert (exists rvs, rvos = map Some rvs) as (rvs &?)
          by (eapply not_None_is_Some_Forall; eauto).
      assert (Forall2 (fun vo xt => wt_valo vo (snd xt)) vos (m_in fm)) as WTvs by eauto.
      subst.
      rewrite Forall2_map_1 in WTvs; simpl in WTvs.
      pose proof Ev as Ev'.
      pose proof Findcl; eapply find_class_chained in Findcl; eauto.
      assert (wt_mem (instance_match o me) p' cls).
      { apply match_states_conj in Hmem as (?&?& (WTmem & ?) &?).
        inversion_clear WTmem as [???? WTinsts].
        eapply Forall_forall in WTinsts; eauto.
        unfold instance_match.
        inversion_clear WTinsts as [???? Find|??????? Find Findcl'];
          rewrite Find; auto.
        rewrite Findcl in Findcl'; inv Findcl'; auto.
      }
      eapply pres_sem_stmt_call in Ev' as (?& WTrvos); eauto.
      rewrite Forall2_map_1 in WTrvos.
      take (Forall2 (exp_eval _ _) _ _) and rewrite Forall2_map_2 in it.
      inversion_clear Ev as [??????????? Findcl' Findmth' ?? Hrvs].
      rewrite Findcl in Findcl'; inv Findcl'; rewrite Findmth in Findmth'; inv Findmth'.
      rewrite Forall2_map_1, Forall2_map_2 in Hrvs.
      eapply exec_binded_funcall; eauto using exprs_correct.
      + intro; eapply occurs_in_instance_methods; eauto.
        * eapply wt_class_find_method; eauto.
          eapply wt_program_find_class; eauto.
        * apply c_nodupobjs.
        * erewrite Forall2_length; eauto.
      + rewrite Forall2_map_1.
        eapply Forall2_impl_In; eauto; simpl.
        setoid_rewrite type_pres; congruence.

    (* s1 ; s2 *)
    - apply occurs_in_comp in Occurs as (?&?).
      edestruct IH1 as (?&?&?&?); eauto.
      clear Hmem.
      edestruct IH2 as (m' & le' &?&?); eauto.
      change E0 with (Eapp E0 (Eapp E0 E0)).
      exists m', le'; intuition; unfold exec_stmt_fe; eauto using exec_stmt.

    (* if e then s1 else s2 *)
    - assert (Cop.bool_val v (Clight.typeof (translate_exp owner caller cond)) m = Some b)
        by (rewrite type_pres; take (_ = bool_type) and rewrite it; eauto).
      apply occurs_in_ite in Occurs as (?&?).
      destruct b.
      + edestruct IH as (m' & le' &?&?); eauto.
        exists m', le'; intuition.
        eapply exec_Sifthenelse with (b := true); eauto using expr_correct.
      + edestruct IH as (m' & le' &?&?); eauto.
        exists m', le'; intuition.
        eapply exec_Sifthenelse with (b := false); eauto using expr_correct.

    (* skip *)
    - exists m, le; split; eauto; constructor.

    (* funcall *)
    - eapply find_class_sub_same in Findcl; eauto.
      rewrite Findcl' in Findcl; inv Findcl.
      rewrite Findmth' in Findmth; inv Findmth.
      assert (NoDup (map fst (m_in fm))) by (apply fst_NoDupMembers, m_nodupin).
      rewrite Env.adds_opt_is_adds in IH; auto.
      assert (wt_stmt prog' (c_objs cls) (c_mems cls) (meth_vars fm) (m_body fm))
        by (eapply wt_class_find_method; eauto; eapply wt_program_find_class; eauto).
      assert (No_Naked_Vars fm.(m_body)) by
          (eapply Forall_methods_find with (1 := NO_NAKED_VARS); eauto).

      (* return values are well-typed *)
      assert (wt_vals rvs fm.(m_out)) as WTrvs.
      { assert (Forall2 (fun v xt => wt_valo v (snd xt)) (map Some vs) (m_in fm))
          by (rewrite Forall2_map_1; simpl; auto).
        assert (Forall2 (fun v xt => wt_valo v (snd xt)) (map Some rvs) (m_out fm)) as WTrvs
            by (eapply pres_sem_stmt_call with (me := me); eauto using stmt_call_eval).
        rewrite Forall2_map_1 in WTrvs; simpl in WTrvs; auto.
      }

      (* find the Clight function *)
      edestruct methods_corres as (fun_b & fd & ?&?& Mspec); eauto.

      (* prepare the entry state *)
      pose proof Mspec as Entry;
        eapply function_entry_match_states with (me := me) in Entry; eauto.
      assert (fn_body fd = return_with (translate_stmt (rev prog) cls fm (m_body fm))
                                       (case_out fm
                                                 None
                                                 (fun x t => Some (make_in_arg (x, t)))
                                                 (fun _ => None)))
        as Body by (destruct Mspec as (?&?&?&?&?&?&?&?&?); auto).
      assert (fn_return fd = case_out fm
                                      Tvoid
                                      (fun _ t => cltype t)
                                      (fun _ => Tvoid))
        as Return by (destruct Mspec as (?&?&?); auto).

      unfold call_spec, case_out in *; intros.
      assert (suffix prog' prog) by (eapply find_class_sub; eauto).
      subst gcenv; erewrite find_class_name, find_method_name; eauto.
      destruct_list (m_out fm) as (a, ta) (?,?) ? : Hout;
        [intros * Hmem|intros * Hmem|intros * ? Hmem];

        (* get the entry state *)
        edestruct Entry as (e_f & le_f & m_f & ? & Hm_f); eauto;
          clear Hmem;

          (* get the state after evaluating the body *)
          edestruct IH as (m' & le' & ? & Hm'); eauto;
            clear Hm_f;

            (* free the environment *)
            apply match_states_conj in Hm' as (Hm' &?);
            rewrite sep_swap23, sep_swap, sep_swap34, sep_swap23, <-sep_assoc, sep_unwand in Hm';
            eauto using decidable_subrep;
            apply free_exists in Hm' as (m'' & ?& Hm'').

      (* no output *)
      + exists m'', fd; intuition; eauto.
        * econstructor; eauto.
          -- rewrite Body.
             change E0 with (Eapp E0 E0).
             eapply exec_Sseq_1; eauto using exec_stmt.
          -- rewrite Return; simpl; auto.
        * erewrite find_class_name in Hm''; eauto.
          now do 2 apply sep_drop2 in Hm''.

      (* one output *)
      + (* get the return value *)
        rewrite sep_swap in Hm''.
        rewrite outputrep_singleton in Hm''; eauto.
        rewrite Forall2_map_1, Forall2_map_2 in Hrvos.
        inversion Hrvos as [|? rv ?? Hrv Hrvos']; inv Hrvos'.
        inv WTrvs.
        unfold match_var in Hm''; simpl in Hrv; rewrite Hrv in Hm''.
        destruct Hm'' as (Hm'' & Eq).
        cases_eqn E; inv Eq.

        exists m'', fd, rv; intuition; eauto.
        * econstructor; eauto.
          -- rewrite Body.
             change E0 with (Eapp E0 E0).
             eapply exec_Sseq_1; eauto using exec_stmt, eval_expr.
          -- rewrite Return; simpl; auto.
             split; eauto using sem_cast_same.
             destruct ta; simpl; discriminate.
        * erewrite find_class_name in Hm''; eauto.
          now apply sep_drop2 in Hm''.

      (* multiple output *)
      + (* return values *)
        rewrite Forall2_map_1, Forall2_map_2 in Hrvos.

        exists ve', m'', fd; intuition; eauto.
        * econstructor; eauto.
          -- rewrite Body.
             change E0 with (Eapp E0 E0).
             eapply exec_Sseq_1; eauto using exec_stmt.
          -- rewrite Return; simpl; auto.
        * erewrite find_class_name in Hm''; eauto.
          rewrite sep_swap in Hm''.
          assert (1 < Datatypes.length (m_out fm))%nat by (rewrite Hout; simpl; omega).
          apply outputrep_notnil in Hm'' as (?&?& E & Hm'' &?); auto; inv E.
          rewrite sep_swap, <-sep_assoc in Hm''.
          apply sep_drop2 in Hm''.
          now rewrite sep_assoc in Hm''.
  Qed.

  Corollary stmt_call_correctness:
    forall me cid fid c f vs rvs prog' me',
      stmt_call_eval prog me cid fid (map Some vs) me' (map Some rvs) ->
      find_class cid prog = Some (c, prog') ->
      find_method fid c.(c_methods) = Some f ->
      wt_vals vs f.(m_in) ->
      wt_mem me prog' c ->
      call_spec c f vs rvs me me'.
  Proof.
    intros; eapply mutual_correctness; eauto.
  Qed.

  (*****************************************************************)
  (** Correctness of the whole program                            **)
  (*****************************************************************)

  Let c_main     := c_main _ _ _ _ _ TRANSL.
  Let prog_main  := prog_main _ _ _ _ _ TRANSL.
  Let main_step  := main_step _ _ _ _ _ TRANSL.
  Let main_reset := main_reset _ _ _ _ _ TRANSL.
  Let main_f     := main_f _ _ _ _ _ TRANSL.

  Definition find_main_class: find_class main_node prog = Some (c_main, prog_main) :=
    find_main_class _ _ _ _ _ TRANSL.
  Definition find_main_step: find_method step c_main.(c_methods) = Some main_step :=
    find_main_step _ _ _ _ _ TRANSL.
  Definition find_main_reset: find_method reset c_main.(c_methods) = Some main_reset :=
    find_main_reset _ _ _ _ _ TRANSL.
  Hint Resolve find_main_class find_main_step find_main_reset.

  Lemma bounded_main_class:
    bounded_struct_of_class tge c_main Ptrofs.zero.
  Proof.
    unfold bounded_struct_of_class; rewrite Ptrofs.unsigned_zero; split; try reflexivity.
    simpl.
    edestruct make_members_co as (co &?& Kind & <- &?&?& Size); eauto.
    erewrite co_consistent_sizeof in Size; try eapply Consistent; eauto.
    rewrite Kind in Size. simpl in Size.
    etransitivity; eauto.
    apply align_le.
    destruct (co_alignof_two_p co) as (?&->).
    apply two_power_nat_pos.
  Qed.
  Hint Resolve bounded_main_class.

  Lemma reset_correct:
    forall me0,
      stmt_call_eval prog mempty main_node reset [] me0 [] ->
      call_spec c_main main_reset [] [] mempty me0.
  Proof.
    intros * Sem; eapply stmt_call_correctness; eauto.
    inversion_clear Sem as [??????????? Findcl Findmth Len].
    rewrite find_main_class in Findcl; inv Findcl;
      rewrite find_main_reset in Findmth; inv Findmth.
    destruct (m_in main_reset); try constructor.
    simpl in Len; omega.
  Qed.

  Lemma step_correct:
    forall me me' vs rvs,
      stmt_call_eval prog me main_node step (map Some vs) me' (map Some rvs) ->
      wt_vals vs (m_in main_step) ->
      wt_mem me prog_main c_main ->
      call_spec c_main main_step vs rvs me me'.
  Proof.
    intros * Sem; eapply stmt_call_correctness; eauto.
  Qed.

  Let le_main    := create_undef_temps main_f.(fn_temps).
  Let out_step   := prefix out step.
  Let t_out_step := type_of_inst (prefix_fun main_node step).

  (* !!!: do not use case_out or match on outputs directly because of further dependent destruction failure *)
  Lemma main_entry:
    forall m0 P,
      m0 |= P ->
      if lt_dec 1 (length (m_out main_step))
      then
        exists m1 step_b step_co,
          function_entry2 tge main_f [] m0
                          (PTree.set out_step (step_b, t_out_step) empty_env) le_main m1
          /\ gcenv ! (prefix_fun main_node step) = Some step_co
          /\ m1 |= P
                  ** fieldsrep gcenv vempty step_co.(co_members) step_b
      else function_entry2 tge main_f [] m0 empty_env le_main m0.
  Proof.
    intros * Hmem.
    assert (list_norepet (var_names (fn_vars main_f))) by apply norepet_vars_main.
    assert (list_norepet (var_names (fn_params main_f))) by apply norepet_params_main.
    assert (list_disjoint (var_names (fn_params main_f)) (var_names (fn_temps main_f)))
      by apply disjoint_params_temps_main.
    cases.
    - edestruct main_with_output_structure as (m1 & step_b & step_co &?&?& Hm1); eauto.
      rewrite sep_comm in Hm1.
      exists m1, step_b, step_co; intuition.
      constructor; auto.
    - constructor; auto.
      simpl; unfold main_step, case_out in *.
      cases; simpl in *; try omega; constructor.
  Qed.

  (*****************************************************************)
  (** Trace semantics of reads and writes to volatiles             *)
  (*****************************************************************)

  Definition out_step_env (e: Clight.env) : Prop :=
    forall x b t,
      e ! x = Some (b, t) ->
      x = out_step.

  Remark out_step_env_no_glob_id:
    forall e x,
      valid x ->
      out_step_env e ->
      e ! (glob_id x) = None.
  Proof.
    intros * Valid He.
    rewrite <-not_Some_is_None.
    intros (b, t') Hget.
    apply He in Hget.
    apply (glob_id_not_prefixed x); auto.
    rewrite Hget. constructor.
  Qed.

  Lemma exec_read:
    forall vs e le m,
      out_step_env e ->
      wt_vals vs main_step.(m_in) ->
      exists le',
        exec_stmt_fe function_entry2 tge e le m
                  (load_in main_step.(m_in))
                  (load_events vs main_step.(m_in))
                  le' m Out_normal
        /\ Forall2 (fun v xt => le' ! (fst xt) = Some v) vs main_step.(m_in)
        /\ (forall x, ~ InMembers x main_step.(m_in) -> le' ! x = le ! x).
  Proof.
    pose proof (m_nodupin main_step) as Hnodup.
    pose proof (m_good_in main_step) as Good.
    pose proof  (volatile_step_in _ _ _ _ _ TRANSL WT) as Vol.
    subst main_step.

    induction (m_in (GenerationProperties.main_step _ _ _ _ _ TRANSL)) as [|(x, t)]; simpl;
      intros * He Hwt;
      inversion_clear Hwt as [| v ? vs' ? Hwt_v Hwts ]; inversion_clear Hnodup.

    - rewrite load_events_nil.
      repeat econstructor; auto.

    - inversion_clear Vol as [|? ? Findx].
      destruct Findx as (bx & Findx & Volx).
      rewrite load_events_cons.
      assert (exists le',
                 exec_stmt_fe function_entry2 tge e le m
                           (Sbuiltin (Some x) (AST.EF_vload (type_chunk t))
                                     (Ctypes.Tcons (Tpointer (cltype t) noattr) Ctypes.Tnil)
                                     [Eaddrof (Evar (glob_id x) (cltype t)) (Tpointer (cltype t) noattr)])
                           [load_event_of_val v (x, t)] le' m Out_normal
                 /\ le' ! x = Some v
                 /\ forall y, y <> x -> le' ! y = le ! y)
        as (le' & Hload & Hgss_le' & Hgso_le').
      {
        exists (set_opttemp (Some x) v le).
        repeat split;
          [
            | now apply  PTree.gss
            | now intros; eapply PTree.gso ].
        econstructor.
        - econstructor; eauto using eval_exprlist.
          + apply eval_Eaddrof, eval_Evar_global; eauto.
            apply out_step_env_no_glob_id; auto.
            apply (Good (x, t)), in_eq.
          + unfold Cop.sem_cast; simpl; eauto.
        - constructor.
          unfold load_event_of_val; simpl.
          rewrite wt_val_load_result with (ty:=t); auto.
          apply volatile_load_vol; auto.
          apply eventval_of_val_match; auto.
      }

      assert (forall xt, In xt l -> ValidId xt)
        by (intros; apply Good, in_cons; auto).
      edestruct IHl with (le := le') as (le'' & ? & Hgss & Hgso); eauto.
      exists le''; repeat split.
      + eapply exec_Sseq_1; eauto.
      + econstructor; eauto.
        rewrite Hgso; auto.
      + intros * Hnot_in.
        apply Decidable.not_or in Hnot_in as [? ?].
        rewrite Hgso; auto.
  Qed.

  Lemma exec_write_multiple:
    forall outs,
      incl outs main_step.(m_out) ->
      (1 < Datatypes.length (m_out main_step))%nat ->
      forall rvs e ve le m step_b step_co,
        NoDupMembers outs ->
        out_step_env e ->
        wt_vals rvs outs ->
        gcenv ! (prefix_fun main_node step) = Some step_co ->
        e ! out_step = Some (step_b, t_out_step) ->
        Forall2 (fun xt v => Env.find (fst xt) ve = Some v) outs rvs ->
        m |= fieldsrep gcenv ve (co_members step_co) step_b ->
        exec_stmt_fe function_entry2 tge e le m
                  (write_multiple_outs main_node outs)
                  (store_events rvs outs)
                  le m Out_normal.
  Proof.
    intros ? Incl Len.
    assert (Forall (is_volatile tprog) outs) as Vol
      by (apply Forall_incl with (2 := Incl), volatile_step_out; auto).
    assert (Forall ValidId outs) as Good
        by (apply Forall_incl with (2 := Incl), Forall_forall, m_good_out).

    unfold exec_stmt_fe.
    induction outs as [|(x, t)]; intros * Nodup He WTrvs Hrco Findstr Hrvs Hm.
    - rewrite store_events_nil; constructor.
    - inversion_clear Vol as [|? ? Findx];  destruct Findx as (bx & Findx & Volx).
      inversion_clear Good as [|?? Good_x].
      inversion WTrvs as [|rv ? rvs']; subst.
      inv Hrvs.
      inversion_clear Nodup.
      simpl in Incl; apply incl_cons' in Incl as (Hin &?).
      unfold main_step in Hin.

      pose proof Hm as Hm'; rewrite sepemp_right in Hm'.
      eapply eval_inst_field in Hm'; eauto using find_main_class, find_main_step; simpl.
      rewrite store_events_cons.
      eapply exec_Sseq_1; eauto.
      eapply exec_Sbuiltin with (vres:=Vundef).
      + repeat
          match goal with
          | |- eval_exprlist _ _ _ _ _ _ _ => econstructor; eauto
          end.
        * econstructor.
          apply eval_Evar_global; eauto.
          apply out_step_env_no_glob_id; auto.
          apply Good_x.
        * reflexivity.
        * eapply sem_cast_same; eauto.
      + constructor.
        apply volatile_store_vol; auto.
        rewrite <-wt_val_load_result; auto.
        apply eventval_of_val_match; auto.
  Qed.

  Corollary exec_write:
    forall rvs e le m,
      out_step_env e ->
      wt_vals rvs main_step.(m_out) ->
      case_out main_step
               True
               (fun y t => exists rv, rvs = [rv] /\ le ! y = Some rv)
               (fun outs =>
                  exists ve step_b step_co,
                    gcenv ! (prefix_fun main_node step) = Some step_co
                    /\ e ! out_step = Some (step_b, t_out_step)
                    /\ Forall2 (fun xt v => Env.find (fst xt) ve = Some v) outs rvs
                    /\ m |= fieldsrep gcenv ve (co_members step_co) step_b) ->
      exec_stmt_fe function_entry2 tge e le m
                (write_out main_node main_step.(m_out))
                (store_events rvs main_step.(m_out))
                le m Out_normal.
  Proof.
    pose proof (m_good_out main_step) as Good.
    assert (Forall (is_volatile tprog) (m_out main_step)) as Vol by (apply volatile_step_out; auto).
    intros * He WT_vals Hrep.
    assert (length rvs = length main_step.(m_out)) as Length by (eapply Forall2_length; eauto).

    unfold case_out in Hrep.
    unfold exec_stmt_fe.
    destruct_list (m_out main_step) as (y, t) (y', t') outs : Out;
      destruct_list rvs as rv rv' rvs' : Rvs; contr.

    (* no output *)
    - rewrite store_events_nil; eauto using exec_stmt.

    (* one output *)
    - unfold write_out.
      inversion_clear Vol as [|? ? Findy];
        destruct Findy as (b_y & Findy & Voly).
      inversion_clear WT_vals.
      destruct Hrep as (?&E&?); inv E.
      eapply exec_Sbuiltin with (vres:=Vundef).
      + repeat
          match goal with
          | |- eval_exprlist _ _ _ _ _ _ _ => econstructor
          end.
        * econstructor.
          apply eval_Evar_global; eauto.
          apply out_step_env_no_glob_id; auto.
          apply (Good (y, t)), in_eq.
        * reflexivity.
        * econstructor; eauto.
        * eapply sem_cast_same; eauto.
      + constructor.
        apply volatile_store_vol; auto; simpl.
        rewrite <-wt_val_load_result; auto.
        apply eventval_of_val_match; auto.

    (* multiple outputs *)
    - destruct Hrep as (?&?&?&?&?&?&?).
      unfold write_out.
      eapply exec_write_multiple; eauto.
      + rewrite <-Out; apply incl_refl.
      + rewrite Out; simpl; omega.
      + rewrite <-Out; apply m_nodupout.
  Qed.


  (*****************************************************************)
  (** Clight version of dostep                                    **)
  (*****************************************************************)

  Section dostep.

    Variables (sb     : block)
              (step_f : function).

    Variables ins outs: Str.stream (list val).

    (** This coinductive predicate describes the logical behavior of
        the [while] loop. *)


    CoInductive dostep (e: Clight.env) : nat -> mem -> Prop :=
      DoStep :
        forall n m m',
          case_out main_step
                   (eval_funcall_fe function_entry2 tge m (Internal step_f)
                                 (var_ptr sb :: ins n) E0 m' Vundef)
                   (fun _ _ =>
                      exists v,
                        outs n = [v]
                        /\ eval_funcall_fe function_entry2 tge m (Internal step_f)
                                       (var_ptr sb :: ins n) E0 m' v)
                   (fun ys =>
                      exists ve step_b step_co,
                        eval_funcall_fe function_entry2 tge m (Internal step_f)
                                     (var_ptr sb :: var_ptr step_b :: ins n) E0 m' Vundef
                          /\ gcenv ! (prefix_fun main_node step) = Some step_co
                        /\ e ! out_step = Some (step_b, t_out_step)
                        /\ Forall2 (fun xt v => Env.find (fst xt) ve = Some v) ys (outs n)
                        /\ m' |= fieldsrep gcenv ve (co_members step_co) step_b) ->
          out_step_env e ->
          dostep e (S n) m' ->
          dostep e n m.

    Section Dostep_coind.

      Variable R: nat -> mem -> Prop.
      Variable e: Clight.env.

      Hypothesis He : out_step_env e.

      Definition dostepCase :=
        forall n m,
          R n m ->
          exists m',
            case_out main_step
                     (eval_funcall_fe function_entry2 tge m (Internal step_f)
                                   (var_ptr sb :: ins n) E0 m' Vundef)
                     (fun _ _ =>
                      exists v,
                        outs n = [v]
                        /\ eval_funcall_fe function_entry2 tge m (Internal step_f)
                                       (var_ptr sb :: ins n) E0 m' v)
                     (fun ys =>
                        exists ve step_b step_co,
                          eval_funcall_fe function_entry2 tge m (Internal step_f)
                                       (var_ptr sb :: var_ptr step_b :: ins n) E0 m' Vundef
                          /\ gcenv ! (prefix_fun main_node step) = Some step_co
                          /\ e ! out_step = Some (step_b, t_out_step)
                          /\ Forall2 (fun xt v => Env.find (fst xt) ve = Some v) ys (outs n)
                          /\ m' |= fieldsrep gcenv ve (co_members step_co) step_b)
            /\ R (S n) m'.

      Lemma dostep_coind:
        dostepCase ->
        forall n m,
          R n m -> dostep e n m.
      Proof.
        intro DoStep.
        cofix COINDHYP.
        intros ? ? HR.
        pose proof (DoStep _ _ HR) as Hstep.
        simpl in *; decompose record Hstep; subst.
        econstructor; eauto.
      Qed.

    End Dostep_coind.


    (*****************************************************************)
    (** dostep implies a step of the body loop                      **)
    (*****************************************************************)

    Remark out_step_env_no_prefix_fun:
      forall e x f,
        out_step_env e ->
        e ! (prefix_fun x f) = None.
    Proof.
      intros * He.
      rewrite <-not_Some_is_None.
      intros (b, t') Hget.
      apply He in Hget; unfold out_step in Hget.
      unfold prefix_fun in Hget.
      apply prefix_injective in Hget as (?&?); auto using fun_id_valid, out_valid.
    Qed.
    Hint Resolve out_step_env_no_prefix_fun.

    Let step_name := Evar (prefix_fun main_node step).
    Let self_addr := Eaddrof (Evar (glob_id self) (type_of_inst main_node))
                               (type_of_inst_p main_node).

    Hypothesis Find_self : Genv.find_symbol tge (glob_id self) = Some sb.

    (** evaluate the self parameter *)
    Lemma eval_expr_self:
      forall e le m,
        out_step_env e ->
        eval_expr tge e le m self_addr (var_ptr sb).
    Proof.
      econstructor.
      apply eval_Evar_global; eauto.
      apply out_step_env_no_glob_id; auto; apply self_valid.
    Qed.
    Hint Resolve eval_expr_self.

    Hypothesis Hwt_ins  : forall n, wt_vals (ins n) main_step.(m_in).
    Hypothesis Hwt_outs : forall n, wt_vals (outs n) main_step.(m_out).
    Hypothesis StepSpec : method_spec c_main main_step prog step_f.

    Lemma exec_body:
      forall e n m_n le_n,
        dostep e n m_n ->
        exists le_Sn m_Sn,
          exec_stmt_fe function_entry2 tge e le_n m_n
                       (main_loop_body false main_node main_step)
                       (load_events (ins n) (m_in main_step)
                         ++ E0
                         ++ store_events (outs n) (m_out main_step))
                       le_Sn m_Sn Out_normal
          /\ dostep e (S n) m_Sn.
    Proof.
      intros * Dostep.

      (* the loop predicate gives the expected memory after a call *)
      inversion_clear Dostep as [?? m_Sn EvalStep].

      (*  load in *)
      edestruct exec_read with (le := le_n) (m := m_n) as (le1 & ?&?&?); eauto.

      (* get the function *)
      edestruct methods_corres with (4 := find_main_step) as (ptr_step & f & Get_s & Get_f & ?); eauto.
      assert (f = step_f) by (eapply method_spec_eq; eauto); subst f.

      (* evaluate the lvalue function name *)
      assert (forall targs tres cc,
                 eval_expr tge e le1 m_n (step_name (Tfunction targs tres cc)) (var_ptr ptr_step)).
      { intros; eapply eval_Elvalue.
        - apply eval_Evar_global; eauto.
        - apply deref_loc_reference; auto.
      }

      (* evaluate the arguments of the step call *)
      assert (forall vs,
                 wt_vals vs main_step.(m_in) ->
                 Forall2 (fun v xt => le1 ! (fst xt) = Some v) vs main_step.(m_in) ->
                 eval_exprlist tge e le1 m_n
                               (map make_in_arg main_step.(m_in))
                               (list_type_to_typelist
                                  (map Clight.typeof (map make_in_arg (m_in main_step))))
                               vs).
      { clear.
        induction main_step.(m_in) as [|(x, t)];
          intros ? Hvals_in;
          inversion_clear Hvals_in as [| cin ? cins];
          intro Hdef;
          inversion_clear Hdef;
          simpl in *;
          eauto using eval_exprlist.
        apply eval_Econs with (v1 := cin)(v2 := cin).
        - econstructor; eauto.
        - now apply sem_cast_same.
        - apply IHl; eauto.
      }

      (* step call *)
      assert (exists le2,
                 exec_stmt_fe function_entry2 tge e le1 m_n
                           (step_call main_node (map make_in_arg (m_in main_step)) (m_out main_step))
                           E0 le2 m_Sn Out_normal
                 /\ match main_step.(m_out), outs n with
                   | [(x, _)], [v] => le2 ! x = Some v
                   | _, _ => True
                   end)
        as (le2 & Hcall & ?).
      { unfold step_call.
        destruct_list main_step.(m_out) as (?, ?) ? ? : Out;
          unfold case_out in EvalStep; rewrite Out in EvalStep.
        - eexists; split; auto.
          eapply exec_Scall; simpl; eauto; simpl; eauto using eval_exprlist.
          unfold type_of_function.
          destruct StepSpec as (P_f & R_f & CC_f &?).
          rewrite P_f, R_f, CC_f; unfold case_out; rewrite Out; simpl.
          rewrite type_of_params_make_in_arg; auto.
          erewrite find_class_name; eauto.
        - destruct EvalStep as (? & E & ?); rewrite E.
          eexists; split.
          + eapply exec_Scall; simpl; eauto; simpl; eauto using eval_exprlist.
            unfold type_of_function.
            destruct StepSpec as (P_f & R_f & CC_f &?).
            rewrite P_f, R_f, CC_f; unfold case_out; rewrite Out; simpl.
            rewrite type_of_params_make_in_arg; auto.
            erewrite find_class_name; eauto.
          + simpl; apply PTree.gss.
        - destruct EvalStep as (?&?&?&?&?&?&?).
          eexists; split; auto.
          eapply exec_Scall; simpl; eauto; simpl; eauto 7 using eval_exprlist.
          unfold type_of_function.
          destruct StepSpec as (P_f & R_f & CC_f &?).
          rewrite P_f, R_f, CC_f; unfold case_out; rewrite Out; simpl.
          rewrite type_of_params_make_in_arg; auto.
          erewrite find_class_name, find_method_name; eauto.
          unfold type_of_inst_p; auto.
      }

      eexists le2, m_Sn; split; auto.
      repeat eapply exec_Sseq_1; eauto.

      (* write out *)
      eapply exec_write; eauto.
      unfold case_out; destruct_list main_step.(m_out) as (?, ?) ? ?: Outs; auto;
        unfold case_out in EvalStep; rewrite Outs in EvalStep.
      - destruct EvalStep as (?& E & ?).
        rewrite E in *; eauto.
      - destruct EvalStep as (ve & step_b & step_co & ?&?&?&?).
        exists ve, step_b, step_co; intuition; eauto.
    Qed.

    Section MainCorrectness.

      Variables (me0     : menv)
                (reset_f : function)
                (e       : Clight.env)
                (m_main  : mem).

      Hypothesis (ResetCall : stmt_call_eval prog mempty main_node reset [] me0 [])
                 (WTme0     : wt_mem me0 prog_main c_main)
                 (StepLoop  : loop_call prog main_node step (fun n => map Some (ins n)) (fun n => map Some (outs n)) 0 me0)
                 (ResetSpec : method_spec c_main main_reset prog reset_f)
                 (He        : out_step_env e)
                 (Hm_main   : if lt_dec 1 (length (m_out main_step))
                              then
                                exists step_b step_co,
                                  gcenv ! (prefix_fun main_node step) = Some step_co
                                  /\ e ! out_step = Some (step_b, t_out_step)
                                  /\ m_main |= staterep gcenv prog main_node mempty sb Z0
                                           ** fieldsrep gcenv vempty step_co.(co_members) step_b
                              else m_main |= staterep gcenv prog main_node mempty sb Z0).

      Lemma reset_no_output:
        m_out main_reset = [].
      Proof.
        inversion_clear ResetCall as [??????????? Findcl Findmth ?? Houts].
        rewrite find_main_class in Findcl; inv Findcl;
          rewrite find_main_reset in Findmth; inv Findmth.
        rewrite Forall2_map_1 in Houts; unfold main_reset; inv Houts; auto.
      Qed.

      Lemma reset_no_input:
        m_in main_reset = [].
      Proof.
        inversion_clear ResetCall as [??????????? Findcl Findmth].
        rewrite find_main_class in Findcl; inv Findcl;
          rewrite find_main_reset in Findmth; inv Findmth.
        destruct main_reset.(m_in); simpl in *; auto; omega.
      Qed.

      (*****************************************************************)
      (** Correctness of dostep relatively to loop_call               **)
      (*****************************************************************)

      Lemma dostep_imp:
        exists m0,
          eval_funcall_fe function_entry2 tge m_main (Internal reset_f)
                          [var_ptr sb] E0 m0 Vundef
          /\ dostep e 0 m0.
      Proof.
        (* reset correctness preparation *)
        pose proof ResetCall as ResetCall'.
        apply reset_correct in ResetCall'.
        unfold call_spec, case_out in ResetCall'.
        rewrite reset_no_output in ResetCall'.
        erewrite find_class_name in ResetCall'; eauto.
        rewrite <- Ptrofs.unsigned_zero in Hm_main.

        (* prepare the coinduction relation in advance *)
        set (R := fun n m => case_out main_step
                                   (exists me,
                                       loop_call prog main_node step
                                                 (fun n => map Some (ins n)) (fun n => map Some (outs n)) n me
                                       /\ wt_mem me prog_main c_main
                                       /\ m |= staterep gcenv prog main_node me sb 0)
                                   (fun _ _ =>
                                      exists me,
                                        loop_call prog main_node step
                                                  (fun n => map Some (ins n)) (fun n => map Some (outs n)) n me
                                        /\ wt_mem me prog_main c_main
                                        /\ m |= staterep gcenv prog main_node me sb 0 )
                                   (fun _ =>
                                      exists me step_b step_co,
                                        loop_call prog main_node step
                                                  (fun n => map Some (ins n)) (fun n => map Some (outs n)) n me
                                        /\ wt_mem me prog_main c_main
                                        /\ gcenv ! (prefix_fun main_node step) = Some step_co
                                        /\ e ! out_step = Some (step_b, t_out_step)
                                        /\ m |= staterep gcenv prog main_node me sb 0
                                            ** fieldsrep gcenv vempty (co_members step_co) step_b)).

        assert (dostepCase R e).
        { unfold R; unfold dostepCase, case_out.
          intros n m_n Spec.
          destruct_list (m_out main_step) as (?,?) (?,?) ? : Hout;
            [destruct Spec as (? & Dostep & Hwt & Hm_n)
            |destruct Spec as (? & Dostep & Hwt & Hm_n)
            |destruct Spec as (? & step_b' & step_co' & Dostep & Hwt & ? & ? & Hm_n)];
            destruct Dostep as [? me_n me_Sn EvalStep dostep];
            assert (wt_mem me_Sn prog_main c_main)
              by (eapply pres_sem_stmt_call with (f := step); eauto;
                  rewrite Forall2_map_1; simpl; apply Hwt_ins);

            (* step correctness *)
            eapply step_correct in EvalStep; auto;
              unfold call_spec, case_out in EvalStep;
              rewrite Hout in EvalStep; erewrite find_class_name in EvalStep; eauto;
                rewrite sepemp_right, <- Ptrofs.unsigned_zero in Hm_n; try rewrite sep_assoc in Hm_n;
                  [eapply EvalStep in Hm_n as (m_Sn & step_f' & ? & ? & Hm_Sn)
                  |eapply EvalStep in Hm_n as (m_Sn & step_f' & ? & ? & ? & ? & Hm_Sn)
                  |eapply EvalStep in Hm_n as (ve_f & m_Sn & step_f' & ? & ? & ? & Hm_Sn)]; auto;
                    try erewrite find_method_name; eauto;
                      assert (step_f = step_f') by (eapply method_spec_eq; eauto); subst step_f'.

          - exists m_Sn; split; eauto.
            exists me_Sn; intuition.
            now rewrite <-sepemp_right, Ptrofs.unsigned_zero in Hm_Sn.
          - exists m_Sn; split; eauto.
            exists me_Sn; intuition.
            now rewrite <-sepemp_right, Ptrofs.unsigned_zero in Hm_Sn.
          - exists m_Sn; split; eauto.
            + exists ve_f, step_b', step_co'; intuition.
              now apply sep_proj2, sep_proj1 in Hm_Sn.
            + exists me_Sn, step_b', step_co'; intuition.
              rewrite <-sepemp_right, Ptrofs.unsigned_zero in Hm_Sn.
              eapply sep_imp; eauto.
              apply fieldsrep_any_empty.
        }

        cases;
          (* reset correctness *)
          [destruct Hm_main as (step_b & step_co & ? & ? & Hm_main');
           clear Hm_main; rename Hm_main' into Hm_main
          |rewrite sepemp_right in Hm_main];
          eapply ResetCall' in Hm_main as (m0 & reset_f' & ? & ? & Hm0); auto;
            assert (reset_f = reset_f') by (eapply method_spec_eq; eauto); subst reset_f';
              exists m0; split; auto;

                (* loop correctness using the R relation defined before *)
                apply dostep_coind with (R := R); auto;
                  unfold R, case_out; destruct_list (m_out main_step) as (?,?) (?,?) ?;
                                                                               simpl in *; try omega.
        - exists me0, step_b, step_co; intuition.
        - exists me0; intuition.
          now rewrite <-sepemp_right, Ptrofs.unsigned_zero in Hm0.
        - exists me0; intuition.
          now rewrite <-sepemp_right, Ptrofs.unsigned_zero in Hm0.
      Qed.

      Let reset_name := Evar (prefix_fun main_node reset).

      Corollary exec_reset:
        exists m0,
          exec_stmt_fe function_entry2 tge e
                       le_main m_main (reset_call main_node) E0
                       le_main m0 Out_normal
          /\ dostep e 0 m0.
      Proof.
        destruct dostep_imp as (m0 & ?&?).
        exists m0; split; auto.

        (* get the function *)
        edestruct methods_corres with (4 := find_main_reset) as (ptr_reset & f & Get_s & Get_f & ?); eauto.
        assert (f = reset_f) by (eapply method_spec_eq; eauto); subst f.

        (* evaluate the lvalue function name *)
        assert (forall targs tres cc,
                   eval_expr tge e le_main m_main (reset_name (Tfunction targs tres cc)) (var_ptr ptr_reset)).
        { intros; eapply eval_Elvalue.
          - apply eval_Evar_global; eauto.
          - apply deref_loc_reference; auto.
        }

        change le_main with (set_opttemp None Vundef le_main).
        eapply exec_Scall; eauto; simpl; eauto using eval_exprlist.
        unfold type_of_function.
        destruct ResetSpec as (-> & -> & -> &?); unfold case_out;
          rewrite reset_no_output, reset_no_input;
          erewrite find_class_name; eauto; simpl; auto.
      Qed.


      (*****************************************************************)
      (** Corollary of exec_body: dostep implies the infinte looping* **)
      (** execution                                                   **)
      (** We switch to the small-step semantics since the big-step    **)
      (** one cannot distinguish between Reacts and Diverges          **)
      (*****************************************************************)

      Section TraceInf.

        Hypothesis Step_in_out_spec: main_step.(m_in) <> [] \/ main_step.(m_out) <> [].

        Fact Len_ins:
          forall n : nat, Datatypes.length (ins n) = Datatypes.length (m_in main_step).
        Proof.
          intro n; specialize (Hwt_ins n); eapply Forall2_length; eauto.
        Qed.

        Fact Len_outs:
          forall n : nat, Datatypes.length (outs n) = Datatypes.length (m_out main_step).
        Proof.
          intro n; specialize (Hwt_outs n); eapply Forall2_length; eauto.
        Qed.

        Definition trace_main_step (n: nat): traceinf := trace_step main_step ins outs Step_in_out_spec Len_ins Len_outs n.

        Let main_state F := Clight.State F (main_loop false main_node main_step).

        Lemma reactive_loop:
          forall n F e m le k,
            dostep e n m ->
            Forever_reactive (semantics2 tprog) (main_state F k e le m) (trace_main_step n).
        Proof.
          unfold trace_main_step, trace_step.
          cofix COINDHYP.
          intros * Hdostep'.
          edestruct exec_body with (1:=Hdostep') as (? & ? & Exec_body & ?).
          eapply exec_stmt_steps in Exec_body as (? & Star_body & Out_body).
          unfold main_loop_body in Star_body.
          rewrite unfold_mk_trace.

          econstructor; simpl.
          - eapply star_step.
            + eapply step_loop.
            + eapply star_right with (t2:=E0); auto.
              * eapply star_right with (t2:=E0); auto.
                -- eapply Star_body.
                -- inversion_clear Out_body.
                   apply step_skip_or_continue_loop1; auto.
              * apply step_skip_loop2.
            + simpl; rewrite 2 E0_right; auto.
          - intro Evts; apply Eapp_E0_inv in Evts.
            assert (forall n, Datatypes.length (ins n) = Datatypes.length (m_in main_step)) as Len_ins
              by (intro n'; pose proof (Hwt_ins n'); eapply Forall2_length; eauto).
            assert (forall n, Datatypes.length (outs n) = Datatypes.length (m_out main_step)) as Len_outs
                by (intro n'; pose proof (Hwt_outs n'); eapply Forall2_length; eauto).
            pose proof (load_store_events_not_E0 _ _ _ _ Step_in_out_spec Len_ins Len_outs n).
            intuition.
          - apply COINDHYP; auto.
        Qed.

        (*****************************************************************)
        (** We show that the whole program is reactive, with the        **)
        (** correct infinite trace                                      **)
        (*****************************************************************)

        Section Behavior.

          Variable (m0 : mem).
          Hypothesis Init: Genv.init_mem tprog = Some m0.

          Let prog_state := Clight.Callstate (Internal main_f) [] Kstop m0.

          Lemma initial_state_main:
            Clight.initial_state tprog prog_state.
          Proof.
            intros.
            edestruct find_main_ptr with (tprog := tprog) (TRANSL := TRANSL) as (?& Find_main &?); eauto.
            erewrite <- tprog_main_proved_id in Find_main; eauto.
            econstructor; eauto.
          Qed.

          Lemma reacts:
            function_entry2 tge main_f [] m0 e le_main m_main ->
            program_behaves (semantics2 tprog) (Reacts (trace_main_step 0)).
          Proof.
            intros.
            econstructor.
            - apply initial_state_main.
            - econstructor.
              destruct exec_reset as (? & Exec_reset & ?).
              eapply exec_stmt_steps in Exec_reset as (? & Star_reset & Out_reset).
              rewrite <-E0_left_inf.
              eapply Smallstep.star_forever_reactive.
              + eapply star_step with (t1:=E0) (t2:=E0); auto.
                * eapply step_internal_function; eauto.
                * eapply star_step with (t1:=E0) (t2:=E0); auto.
                  -- apply step_seq.
                  -- eapply star_right with (t1:=E0) (t2:=E0); auto.
                     ++ eapply Star_reset.
                     ++ inversion_clear Out_reset.
                        apply step_skip_seq.
              + apply reactive_loop; auto.
          Qed.

        End Behavior.

      End TraceInf.

    End MainCorrectness.

  End dostep.

  Lemma out_step_env_empty:
    out_step_env empty_env.
  Proof.
    intros ??? Hin; rewrite PTree.gempty in Hin; discriminate.
  Qed.

  Lemma out_step_env_set_out_step:
    forall b t,
      out_step_env (PTree.set out_step (b, t) empty_env).
  Proof.
    intros ????? Hin; rewrite PTree.gsspec in Hin.
    cases; rewrite PTree.gempty in Hin; discriminate.
  Qed.

  Program Theorem correctness:
    forall ins outs me0
      (WTins            : forall n, wt_vals (ins n) (m_in main_step))
      (WTouts           : forall n, wt_vals (outs n) (m_out main_step))
      (Step_in_out_spec : m_in main_step <> [] \/  m_out main_step <> []),
      stmt_call_eval prog mempty main_node reset [] me0 [] ->
      loop_call prog main_node step (fun n => map Some (ins n)) (fun n => map Some (outs n)) 0 me0 ->
      wt_mem me0 prog_main c_main ->
      program_behaves (semantics2 tprog) (Reacts (trace_main_step ins outs _ _ _ 0)).
  Proof.
    intros.
    (* get the reset and step functions *)
    edestruct methods_corres with (callerid := reset) as (?&?&?&?&?); eauto.
    edestruct methods_corres with (callerid := step) as (?&?&?&?&?); eauto.

    (* get the self state *)
    edestruct find_self as (?& FindSelf); eauto.

    (* initialize the memory *)
    edestruct init_mem as (?&?&?& FindSelf' & Hm); eauto.
    rewrite FindSelf in FindSelf'; inv FindSelf'.

    (* enter the main function *)
    pose proof Hm; apply main_entry in Hm.

    cases_eqn E.
    - destruct Hm as (?& b & co &?&?&?).
      eapply reacts; eauto.
      + apply out_step_env_set_out_step.
      + rewrite E; exists b, co; split; [|split]; auto.
        apply PTree.gss.
    - eapply reacts; eauto.
      * apply out_step_env_empty.
      * rewrite E; auto.
  Qed.

End PRESERVATION.
