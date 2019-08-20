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
From compcert Require Import common.Behaviors.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Memory.
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
(**      the sub-state and blockrep for the output structure,   **)
(**      we get an updated staterep and a the output structure  **)
(**      filled with the return values                          **)
(*****************************************************************)

Definition call_spec (prog: program) (ge: genv) (c: class) (f: method) (vs rvs: list val) (me me': menv) : Prop :=
  forall sb sofs m P,
    let gcenv := Clight.genv_cenv ge in
    bounded_struct_of_class ge c sofs ->
    case_out f
             (
               m |= staterep gcenv prog c.(c_name) me sb (Ptrofs.unsigned sofs) ** P ->
               exists m' fd rv,
                 method_spec c f prog fd
                 /\ eval_funcall ge (function_entry2 ge) m (Internal fd)
                                (Vptr sb sofs :: vs) E0 m' rv
                 /\ m' |= staterep gcenv prog c.(c_name) me' sb (Ptrofs.unsigned sofs) ** P
             )
             (fun _ _ =>
                m |= staterep gcenv prog c.(c_name) me sb (Ptrofs.unsigned sofs) ** P ->
                exists m' fd rv,
                  method_spec c f prog fd
                  /\ eval_funcall ge (function_entry2 ge) m (Internal fd)
                                 (Vptr sb sofs :: vs) E0 m' rv
                  /\ rvs = [rv]
                  /\ m' |= staterep gcenv prog c.(c_name) me' sb (Ptrofs.unsigned sofs) ** P
             )
             (fun outs =>
                forall instb instco,
                  gcenv ! (prefix_fun c.(c_name) f.(m_name)) = Some instco ->
                  m |= staterep gcenv prog c.(c_name) me sb (Ptrofs.unsigned sofs)
                       ** blockrep gcenv vempty instco.(co_members) instb
                       ** P ->
                  exists ve_f m' fd rv,
                    method_spec c f prog fd
                    /\ eval_funcall ge (function_entry2 ge) m (Internal fd)
                                   (Vptr sb sofs :: var_ptr instb :: vs) E0 m' rv
                    /\ Forall2 (fun xt v => Env.find (fst xt) ve_f = Some v) outs rvs
                    /\ m' |= staterep gcenv prog c.(c_name) me' sb (Ptrofs.unsigned sofs)
                            ** blockrep gcenv ve_f instco.(co_members) instb
                            ** P
             ).

Lemma call_spec_chained:
  forall prog ge prog' cid c fid f vs rvs me me' ownerid owner prog'',
    wt_program prog ->
    find_class ownerid prog = Some (owner, prog') ->
    find_class cid prog' = Some (c, prog'') ->
    find_method fid (c_methods c) = Some f ->
    call_spec prog ge c f vs rvs me me' ->
    call_spec prog' ge c f vs rvs me me'.
Proof.
  unfold call_spec, case_out.
  intros * WT Findowner Findcl Findmth Spec * ?.
  erewrite find_class_name in Spec; eauto.
  erewrite find_class_name; eauto.
  destruct_list (m_out f) as (?,?) (?,?) ?; [intros * Hmem|intros * Hmem|intros * ? Hmem];
    try (setoid_rewrite staterep_chained in Hmem; eauto;
      eapply Spec in Hmem as (m' & fd & rv & ? & ? & ?); eauto;
        exists m', fd, rv; intuition;
          try eapply method_spec_find_class; eauto;
          rewrite staterep_chained; eauto).
  setoid_rewrite staterep_chained in Hmem; eauto;
    eapply Spec in Hmem as (ve_f & m' & fd & rv & ? & ? & ?); eauto;
      exists ve_f, m', fd, rv; intuition;
        try eapply method_spec_find_class; eauto;
          rewrite staterep_chained; eauto.
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
            m1 |= match_out gcenv owner caller ve1 le1 outb_co ** P1 ->
            exists outb outco d,
              eval_lvalue tge e le1 m1 out_ind_field outb (Ptrofs.repr d)
              /\ outb_co = Some (outb, outco)
              /\ field_offset gcenv x (co_members outco) = Errors.OK d.
        Proof.
          clear Hmem; intros * Hmem.
          apply match_out_notnil in Hmem as (outb & outco & E &?&?&?); auto.
          apply in_map with (f:=translate_param) in Hin.
          erewrite output_match in Hin; eauto.
          edestruct blockrep_field_offset as (d & Hoffset & ?); eauto.
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
          apply match_out_notnil in Hmem as (?&?& E' &?&?&?); auto.
          rewrite E in E'; inv E'.
          eapply blockrep_deref_mem; eauto.
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
        intros * Hvars E ?.
        apply match_states_conj in Hmem as (Hmem &?).
        rewrite sep_swap5 in Hmem.
        apply sep_proj1, sep_pure' in Hmem.
        apply eval_Etempvar.
        apply NotInMembers_NotIn with (b := ty) in E.
        unfold meth_vars in Hvars.
        rewrite app_assoc in Hvars.
        eapply not_In2_app in E; eauto.
        apply in_map with (f:=translate_param) in E.
        eapply Forall_forall in Hmem; eauto.
        simpl in Hmem.
        destruct (le ! x);
          [now app_match_find_var_det | contradiction].
      Qed.

      (** x *)
      Lemma eval_var:
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
            rewrite match_out_singleton in Hmem; eauto.
            unfold find_or_vundef in Hmem;
              destruct Hmem as (? & Eq); destruct (Env.find i ve); contr;
                rewrite Eq; auto.
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
          rewrite staterep_skip in Hmem; eauto.
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
          rewrite staterep_skip in Hmem; eauto.
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
          apply match_states_conj in Hmem as (Hmem &?&?&?&?).
          intros * Hin.
          pose proof (find_class_name _ _ _ _ Findowner); subst.
          edestruct make_members_co as (? & Hco & ? & Eq & ? & ?); eauto.
          rewrite staterep_skip in Hmem; eauto.
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
            apply (Z.le_le_add_le 0 (sizeof_struct (globalenv tprog) 0 (make_members c))); try omega.
            apply sizeof_struct_incr.
        Qed.

      End SelfField.

      Lemma expr_correct:
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
          m1 |= match_out gcenv owner caller ve1 le1 outb_co
                ** varsrep caller ve1 le1
                ** P1 ->
          eval_expr tge e le1 m1 ae v ->
          exists m' le',
            exec_stmt tge (function_entry2 tge) e le1 m1
                      (assign owner caller x (cltype ty) ae)
                      E0 le' m' Out_normal
            /\ m' |= match_out gcenv owner caller (Env.add x v ve1) le' outb_co
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
            exists m1, (PTree.set x v le1); rewrite PTree.gso; intuition; eauto using exec_stmt.
            eapply sep_imp; eauto.
            * eapply match_out_assign_singleton_mem; eauto.
            * rewrite varsrep_add; eauto.

          (* several outputs: x is an indirect access out->x *)
          + assert (1 < Datatypes.length (m_out caller))%nat by (rewrite Houts; simpl; omega).
            assert (In (x, ty) caller.(m_out)) by now rewrite Houts.
            rewrite E.
            edestruct match_out_assign_gt1_mem as (m' & ?&?&?& Hco & Hofs &?&?); eauto using output_match.
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
            destruct_list caller.(m_out) : Houts; try rewrite E; eauto using exec_stmt.
          + eapply sep_imp; eauto.
            * eapply match_out_assign_var_mem; eauto using output_match.
            * rewrite varsrep_add; eauto.
      Qed.

      Corollary exec_assign_match_states:
          eval_expr tge e le m ae v ->
          exists m' le',
            exec_stmt tge (function_entry2 tge) e le m
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

      Hypothesis (Findchild  : find_class cid prog' = Some (c, prog''))
                 (Findcallee : find_method fid c.(c_methods) = Some callee)
                 (Len        : (1 < Datatypes.length (m_out callee))%nat)
                 (Ho         : e ! o = Some (instb, type_of_inst (prefix_fun cid fid)))
                 (Hinstco    : gcenv ! (prefix_fun cid fid) = Some instco).

      (** o.x : a local output structure field is evaluated to the value found in the callee env *)
      Lemma eval_inst_field:
        forall x ty v le2 m1 P1,
          let inst_field := Efield (Evar o (type_of_inst (prefix_fun cid fid))) x (cltype ty) in
          m1 |= blockrep gcenv ve_callee (co_members instco) instb ** P1 ->
          In (x, ty) callee.(m_out) ->
          Env.find x ve_callee = Some v ->
          eval_expr tge e le2 m1 inst_field v.
      Proof.
        clear Hmem Findcaller; intros * Hmem Hin ?.
        apply in_map with (f:=translate_param) in Hin.
        assert (find_class cid prog = Some (c, prog''))
          by (eapply find_class_chained; eauto).
        clear Findowner Findchild.
        erewrite output_match in Hin; eauto.
        - edestruct blockrep_field_offset as (d & Hoffset & ?); eauto.
          eapply eval_Elvalue; eauto.
          + eapply eval_Efield_struct; eauto.
            * eapply eval_Elvalue; eauto.
              now apply deref_loc_copy.
            * simpl; unfold type_of_inst; eauto.
          + eapply blockrep_deref_mem; eauto.
            rewrite Ptrofs.unsigned_zero, Ptrofs.unsigned_repr; auto.
        - erewrite find_class_name, find_method_name; eauto.
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

      Hypothesis (Hmem1 : m1 |= blockrep gcenv ve_callee (co_members instco) instb
                                ** match_out gcenv owner caller ve le outb_co
                                ** varsrep caller ve le
                                ** P1).

      Lemma exec_funcall_assign_outs:
        forall outs xs vs,
          let tyo := type_of_inst (prefix_fun cid fid) in
          incl outs callee.(m_out) ->
          Forall2 (fun y xt => In (y, snd xt) (meth_vars caller)) xs outs ->
          Forall2 (fun v xt => wt_val v (snd xt)) vs outs ->
          Forall2 (fun xt v => Env.find (fst xt) ve_callee = Some v) outs vs ->
          exists m' le',
            exec_stmt tge (function_entry2 tge) e le m1
                      (funcall_assign owner caller xs o tyo outs)
                      E0 le' m' Out_normal
            /\ m' |= blockrep gcenv ve_callee (co_members instco) instb
                 ** match_out gcenv owner caller (Env.adds xs vs ve) le' outb_co
                 ** varsrep caller (Env.adds xs vs ve) le'
                 ** P1
            /\ forall v, le ! self = Some v -> le' ! self = Some v.
      Proof.
        clear Hmem.
        intro outs; revert dependent m1; clear Hmem1 m1; revert ve le.
        induction outs as [|(x, t)]; intros * Hmem ??? Incl Hins WTvs Hvs;
          inversion_clear Hins as [|y]; inv WTvs; inv Hvs; unfold funcall_assign; simpl.
        - rewrite Env.adds_nil_l.
          exists m1, le; intuition; eauto using exec_stmt.
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
          exists m', le'; intuition; eauto using exec_stmt.
      Qed.

      Corollary exec_funcall_assign:
        forall xs vs,
          let tyo := type_of_inst (prefix_fun cid fid) in
          Forall2 (fun y xt => In (y, snd xt) (meth_vars caller)) xs callee.(m_out) ->
          Forall2 (fun v xt => wt_val v (snd xt)) vs callee.(m_out) ->
          Forall2 (fun xt v => Env.find (fst xt) ve_callee = Some v) callee.(m_out) vs ->
          exists m' le',
            exec_stmt tge (function_entry2 tge) e le m1
                      (funcall_assign owner caller xs o tyo callee.(m_out))
                      E0 le' m' Out_normal
            /\ m' |= blockrep gcenv ve_callee (co_members instco) instb
                 ** match_out gcenv owner caller (Env.adds xs vs ve) le' outb_co
                 ** varsrep caller (Env.adds xs vs ve) le'
                 ** P1
            /\ forall v, le ! self = Some v -> le' ! self = Some v.
      Proof.
        intros; eapply exec_funcall_assign_outs; eauto.
        apply incl_refl.
      Qed.

    End FuncallAssignCorrectness.


    (*****************************************************************)
    (** 'Hoare triple' for funcalls, assuming call_spec for the     **)
    (** callee as a mutual induction hypothesis                     **)
    (*****************************************************************)

    Lemma exec_binded_funcall:
      forall ys o es me_o' vs rvs cid c prog'' fid callee,
        find_class cid prog' = Some (c, prog'') ->
        find_method fid c.(c_methods) = Some callee ->
        call_spec prog' tge c callee vs rvs (instance_match o me) me_o' ->
        Forall2 (fun y xt => In (y, snd xt) (meth_vars caller)) ys callee.(m_out) ->
        Forall2 (fun rv xt => wt_val rv (snd xt)) rvs callee.(m_out) ->
        ((1 < Datatypes.length callee.(m_out))%nat -> M.MapsTo (o, fid) cid (instance_methods caller)) ->
        NoDup ys ->
        In (o, cid) (c_objs owner) ->
        Forall2 (fun e xt => Clight.typeof e = cltype (snd xt)) es callee.(m_in) ->
        eval_exprlist tge e le m es (list_type_to_typelist (map Clight.typeof es)) vs ->
        wt_mem me_o' prog'' c ->
        exists m' le',
          exec_stmt tge (function_entry2 tge) e le m
                    (binded_funcall prog owner caller ys cid o fid es)
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
      rewrite Findchild', Findcallee.
      unfold call_spec in CallSpec.
      unfold case_out in Type_f, CallSpec.
      destruct_list callee.(m_out) as (a, ta) (b, tb) ? : Hout;
        inversion Hins as [|x B C D F Hins']; try inv Hins';
          inversion WTrvs as [|????? WTrvs']; try inv WTrvs'.

      (* no output *)
      - (* get the induction invariant *)
        edestruct CallSpec as (m' & ? & rv & Spec_f' & EvalF & Hmem'); eauto.
        clear Hmem.
        erewrite find_class_name in Hmem'; eauto.
        rewrite method_spec_find_class in Spec_f'; eauto.
        eapply method_spec_eq with (2 := Spec_f) in Spec_f'; eauto; subst.
        rewrite <- (Ptrofs.unsigned_repr d), <- Ptrofs.add_unsigned in EvalF; eauto.

        exists m', le; split.
        + unfold funcall.
          change le with (set_opttemp None rv le).
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
        rewrite method_spec_find_class in Spec_f'; eauto.
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
          - apply match_out_add_prefix.
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
        edestruct CallSpec as (ve_f & m' & ? & rv & Spec_f' & EvalF & ? & Hmem'); eauto.
        erewrite find_class_name in Hmem'; eauto.
        clear Hmem.
        rewrite method_spec_find_class in Spec_f'; eauto.
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
          change le with (set_opttemp None rv le).
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
          eapply sep_imp; eauto using blockrep_any_empty.
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
          exec_stmt tge (function_entry2 tge) e le m
                    (translate_stmt prog owner caller s)
                    E0 le' m' Out_normal
          /\ m' |= match_states gcenv prog owner caller (me', ve') (e, le') sb sofs outb_co
                  ** P)
    /\
    (forall p me cid fid c f vs rvs prog' me',
        suffix p prog ->
        stmt_call_eval p me cid fid (map Some vs) me' (map Some rvs) ->
        find_class cid prog = Some (c, prog') ->
        find_method fid c.(c_methods) = Some f ->
        Forall2 (fun v xt => wt_val v (snd xt)) vs f.(m_in) ->
        wt_mem me prog c ->
        call_spec prog tge c f vs rvs me me').
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
                 exec_stmt tge (function_entry2 tge) e le m
                           (translate_stmt prog owner caller s) E0 le' m' Out_normal
                 /\ m' |= match_states gcenv prog owner caller (me', ve') (e, le') sb sofs outb_co ** P)
         /\
         (forall p me cid fid vos me' rvos,
             stmt_call_eval p me cid fid vos me' rvos ->
             suffix p prog ->
             forall c f vs rvs prog',
               find_class cid prog = Some (c, prog') ->
               find_method fid c.(c_methods) = Some f ->
               Forall2 (fun v xt => wt_val v (snd xt)) vs f.(m_in) ->
               wt_mem me prog c ->
               vos = map Some vs ->
               rvos = map Some rvs ->
               call_spec prog tge c f vs rvs me me')).
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
                               |intros * Findcl Findmth Len ? IH Hrvos ? * Findcl' Findmth']; intros;
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
      eapply exec_binded_funcall; eauto using exprs_correct, call_spec_chained.
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
      exists m', le'; intuition; eauto using exec_stmt.


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
    - exists m, le; split; eauto using exec_stmt.

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
      assert (Forall2 (fun v yt => wt_val v (snd yt)) rvs fm.(m_out)) as WTrvs.
      { assert (Forall2 (fun v xt => wt_valo v (snd xt)) (map Some vs) (m_in fm))
          by (rewrite Forall2_map_1; simpl; auto).
        assert (Forall2 (fun v xt => wt_valo v (snd xt)) (map Some rvs) (m_out fm)) as WTrvs
            by (eapply pres_sem_stmt_call with (me := me); eauto using stmt_call_eval).
        rewrite Forall2_map_1 in WTrvs; simpl in WTrvs; auto.
      }

      (* find the Clight function *)
      edestruct methods_corres as (fun_b & fd & ?&?& Mspec); eauto.

      (* prepare the entry state *)
      rewrite map_length in Len.
      pose proof Mspec as Entry;
        eapply function_entry_match_states with (me := me) in Entry; eauto.
      assert (fn_body fd = return_with (translate_stmt prog cls fm (m_body fm))
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
      + exists m'', fd, Vundef; intuition; eauto.
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
        rewrite match_out_singleton in Hm''; eauto.
        rewrite Forall2_map_1, Forall2_map_2 in Hrvos.
        inversion Hrvos as [|? rv ?? Hrv Hrvos']; inv Hrvos'.
        inv WTrvs.
        unfold find_or_vundef in Hm''; simpl in Hrv; rewrite Hrv in Hm''.
        destruct Hm'' as (Hm'' &?).

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

        exists ve', m'', fd, Vundef; intuition; eauto.
        * econstructor; eauto.
          -- rewrite Body.
             change E0 with (Eapp E0 E0).
             eapply exec_Sseq_1; eauto using exec_stmt.
          -- rewrite Return; simpl; auto.
        * erewrite find_class_name in Hm''; eauto.
          rewrite sep_swap in Hm''.
          assert (1 < Datatypes.length (m_out fm))%nat by (rewrite Hout; simpl; omega).
          apply match_out_notnil in Hm'' as (?&?& E & Hm'' &?); auto; inv E.
          rewrite sep_swap, <-sep_assoc in Hm''.
          apply sep_drop2 in Hm''.
          now rewrite sep_assoc in Hm''.
  Qed.

  Corollary stmt_correctness:
    forall me ve s me' ve' ownerid owner prog' callerid caller m e le outb_co sb sofs P,
      stmt_eval prog me ve s (me', ve') ->
      find_class ownerid prog = Some (owner, prog') ->
      find_method callerid owner.(c_methods) = Some caller ->
      occurs_in s caller.(m_body) ->
      m |= match_states gcenv prog owner caller (me, ve) (e, le) sb sofs outb_co
           ** P ->
      exists m' le',
        exec_stmt tge (function_entry2 tge) e le m
                  (translate_stmt prog owner caller s)
                  E0 le' m' Out_normal
        /\ m' |= match_states gcenv prog owner caller (me', ve') (e, le') sb sofs outb_co
                ** P.
  Proof.
    intros; eapply mutual_correctness; eauto.
  Qed.

  Corollary stmt_call_correctness:
    forall me cid fid c f vs rvs prog' me',
      stmt_call_eval prog me cid fid (map Some vs) me' (map Some rvs) ->
      find_class cid prog = Some (c, prog') ->
      find_method fid c.(c_methods) = Some f ->
      Forall2 (fun v xt => wt_val v (snd xt)) vs f.(m_in) ->
      wt_mem me prog c ->
      call_spec prog tge c f vs rvs me me'.
  Proof.
    intros; eapply mutual_correctness; eauto.
  Qed.


End PRESERVATION.


    Lemma compat_auto_funcall_pres:
      forall f sb ob vs c prog' me tself tout callee_id callee instco m ob_co P,
        let vargs := var_ptr sb
                          :: match callee.(m_out) with
                            | [] | [_] => vs
                            | _ => var_ptr ob :: vs
                            end
        in
        find_class c.(c_name) prog = Some (c, prog') ->
        find_method callee_id c.(c_methods) = Some callee ->
        length f.(fn_params) = length vargs ->
        fn_params f = (self, tself)
                        :: match callee.(m_out) with
                          | [] | [_] => map translate_param callee.(m_in)
                          | _ => (out, tout) :: map translate_param callee.(m_in)
                          end ->
        fn_vars f = make_out_vars (instance_methods callee) ->
        fn_temps f = match callee.(m_out) with
                     | [yt] => [translate_param yt]
                     | _ => []
                     end
                       ++ make_out_temps (instance_methods_temp (rev prog) callee)
                       ++ map translate_param callee.(m_vars) ->
        list_norepet (var_names f.(fn_params)) ->
        list_norepet (var_names f.(fn_vars)) ->
        match callee.(m_out) with
        | [] | [_] => True
        | _ =>
          ob_co = Some (ob, instco)
          /\ gcenv ! (prefix_fun c.(c_name) callee.(m_name)) = Some instco
        end ->
        m |= staterep gcenv prog c.(c_name) me sb Z0
                                            ** match callee.(m_out) with
                                               | [] | [_] => sepemp
                                               | _ => blockrep gcenv vempty instco.(co_members) ob
                                               end
                                            ** P ->
        exists e_fun le_fun m_fun,
          bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le_fun
          /\ alloc_variables tge empty_env m f.(fn_vars) e_fun m_fun
          /\ (forall x b t, e_fun ! x = Some (b, t) -> exists o f, x = prefix_out o f)
          /\ le_fun ! self = Some (var_ptr sb)
          /\ m_fun |= staterep gcenv prog c.(c_name) me sb Z0
                      ** match_out c callee (Env.adds (map fst callee.(m_in)) vs vempty) le_fun ob_co
                      ** subrep callee e_fun
                      ** (subrep callee e_fun -* subrep_range e_fun)
                      ** varsrep callee (Env.adds (map fst callee.(m_in)) vs vempty) le_fun
                      ** P.
    Proof.
      intros * Findc Hcallee Hlengths
             Hparams Hvars Htemps Norep_par Norep_vars Hinstco Hrep.
      subst vargs; rewrite Hparams, Hvars, Htemps in *.
      assert (~ InMembers self (meth_vars callee)) as Notin_s
          by apply m_notreserved, in_eq.
      assert (~ InMembers out (meth_vars callee)) as Notin_o
          by apply m_notreserved, in_cons, in_eq.
      assert (~ InMembers self (map translate_param (m_in callee))).
      { unfold meth_vars in Notin_s; apply NotInMembers_app in Notin_s.
        rewrite fst_InMembers, translate_param_fst, <-fst_InMembers; tauto.
      }
      assert (~ InMembers self (map translate_param (m_out callee))).
      { unfold meth_vars in Notin_s; repeat rewrite NotInMembers_app in Notin_s.
        rewrite fst_InMembers, translate_param_fst, <-fst_InMembers; tauto.
      }
      assert (~ InMembers out (map translate_param (m_in callee))).
      { unfold meth_vars in Notin_o; apply NotInMembers_app in Notin_o.
        rewrite fst_InMembers, translate_param_fst, <-fst_InMembers; tauto.
      }
      assert (~ InMembers self (map translate_param (m_vars callee))).
      { unfold meth_vars in Notin_s; rewrite Permutation_app_comm, <-app_assoc in Notin_s;
          apply NotInMembers_app in Notin_s.
        rewrite fst_InMembers, translate_param_fst, <-fst_InMembers; tauto.
      }
      assert (~ InMembers out (map translate_param (m_vars callee))).
      { unfold meth_vars in Notin_o; rewrite Permutation_app_comm, <-app_assoc in Notin_o;
          apply NotInMembers_app in Notin_o.
        rewrite fst_InMembers, translate_param_fst, <-fst_InMembers; tauto.
      }
      assert (~ InMembers self (make_out_temps (instance_methods_temp (rev prog) callee))).
      { intro Hin_s.
        apply make_out_temps_prefixed in Hin_s.
        apply self_not_prefixed; auto.
      }
      assert (~ InMembers out (make_out_temps (instance_methods_temp (rev prog) callee))).
      { intro Hin_o.
        apply make_out_temps_prefixed in Hin_o.
        apply out_not_prefixed; auto.
      }

      assert (NoDupMembers (map translate_param (m_in callee))).
      { pose proof (m_nodupvars callee) as Nodup.
        rewrite Permutation_app_comm in Nodup.
        apply NoDupMembers_app_r in Nodup.
        rewrite fst_NoDupMembers, translate_param_fst, <-fst_NoDupMembers; auto.
      }
      assert (Forall (fun xt => sizeof tge (snd xt) <= Int.max_unsigned /\
                             (exists (id : AST.ident) (co : composite),
                                 snd xt = Tstruct id noattr /\
                                 gcenv ! id = Some co /\
                                 co_su co = Struct /\
                                 NoDupMembers (co_members co) /\
                                 (forall (x' : AST.ident) (t' : Ctypes.type),
                                     In (x', t') (co_members co) ->
                                     exists chunk : AST.memory_chunk,
                                       access_mode t' = By_value chunk /\
                                       (align_chunk chunk | alignof gcenv t'))))
                     (make_out_vars (instance_methods callee)))
        by (eapply instance_methods_caract; eauto).
      assert (NoDupMembers (make_out_vars (instance_methods callee)))
        by (unfold var_names in Norep_vars; now rewrite fst_NoDupMembers, NoDup_norepet).

      destruct_list (m_out callee) as (y, t) ? ? : E.
      - edestruct
          (bind_parameter_temps_exists_noout (map translate_param callee.(m_in)) self
                                             (make_out_temps (instance_methods_temp (rev prog) callee)
                                                             ++ map translate_param callee.(m_vars)) vs
                                             tself (var_ptr sb))
          as (le_fun & Bind & Hinputs); eauto.
        + rewrite NotInMembers_app; auto.
        + edestruct (alloc_result callee) as (e_fun & m_fun & ? & ? & Hm_fun); eauto.
          assert (le_fun ! self = Some (var_ptr sb)) by
              (eapply (bind_parameter_temps_implies'_noout (map translate_param (m_in callee))); eauto).
          exists e_fun, le_fun, m_fun;
            split; [|split; [|split; [|split]]]; auto.
          rewrite sep_swap4, <-sepemp_left in Hm_fun.
          rewrite sep_swap, match_out_nil; auto.
          rewrite <- 2 sep_assoc, sep_swap.
          rewrite translate_param_fst in Hinputs.
          apply sep_pure; split; auto.
          * rewrite map_app; simpl in Hinputs; repeat rewrite Forall_app in Hinputs.
            rewrite Forall_app; tauto.
          * rewrite sep_assoc, sep_swap, sep_assoc; auto.

      - edestruct
          (bind_parameter_temps_exists_noout (map translate_param callee.(m_in)) self
                                             (translate_param (y, t) ::
                                                              make_out_temps (instance_methods_temp (rev prog) callee)
                                                              ++ map translate_param callee.(m_vars)) vs
                                             tself (var_ptr sb))
          as (le_fun & Bind & Hinputs); eauto.
        + rewrite cons_is_app. repeat rewrite NotInMembers_app; tauto.
        + edestruct (alloc_result callee) as (e_fun & m_fun & ? & ? & Hm_fun); eauto.
          assert (le_fun ! self = Some (var_ptr sb)) by
              (eapply (bind_parameter_temps_implies'_noout (map translate_param (m_in callee))); eauto).
          simpl.
          exists e_fun, le_fun, m_fun;
            split; [|split; [|split; [|split]]]; auto.
          rewrite sep_swap4, <-sepemp_left in Hm_fun.
          rewrite sep_swap, match_out_singleton; eauto; split.
          *{ rewrite <- 2 sep_assoc, sep_swap.
             rewrite translate_param_fst in Hinputs.
             apply sep_pure; split; auto.
             - rewrite map_app; simpl in Hinputs; rewrite Forall_app, Forall_cons2, Forall_app in Hinputs.
               rewrite Forall_app; tauto.
             - rewrite sep_assoc, sep_swap, sep_assoc; auto.
           }
          *{ pose proof (m_nodupvars callee) as Nodup.
             rewrite Permutation_app_comm, <-app_assoc, E in Nodup.
             apply NoDupMembers_app_r in Nodup.
             rewrite <-cons_is_app in Nodup.
             inversion_clear Nodup as [|? ? ? Notin].
             rewrite fst_InMembers in Notin.
             rewrite Env.gsso, Env.gempty; auto.
             rewrite <-fst_InMembers in Notin.
             eapply bind_parameter_temps_conservation; eauto.
             - apply NotInMembers_cons; split.
               + rewrite InMembers_translate_param_idem; auto.
               + simpl in *; auto.
             - simpl; apply PTree.gss.
           }

      - destruct Hinstco.
        edestruct
          (bind_parameter_temps_exists (map translate_param callee.(m_in)) self out
                                       (make_out_temps (instance_methods_temp (rev prog) callee)
                                                       ++ map translate_param callee.(m_vars)) vs
                                       tself tout (var_ptr sb) (var_ptr ob))
          with (1:=self_not_out) as (le_fun & Bind & Hinputs); eauto.
        + rewrite NotInMembers_app; auto.
        + rewrite NotInMembers_app; auto.
        + simpl in Hlengths. inversion Hlengths; eauto.
        + edestruct (alloc_result callee) as (e_fun & m_fun & ? & ? & Hm_fun); eauto.
          edestruct (bind_parameter_temps_implies' (map translate_param (m_in callee)))
            with (1:=self_not_out) as (? & ?); eauto.
          exists e_fun, le_fun, m_fun;
            split; [|split; [|split; [|split]]]; auto.
          assert (1 < length callee.(m_out))%nat by (rewrite E; simpl; omega).
          rewrite sep_swap, match_out_notnil; auto;
            do 2 econstructor; split; [|split]; eauto.
          rewrite sep_swap, <- 3 sep_assoc, sep_swap.
          rewrite translate_param_fst in Hinputs.
          apply sep_pure; split; auto.
          * rewrite map_app; simpl in Hinputs; repeat rewrite Forall_app in Hinputs.
            rewrite Forall_app; tauto.
          * rewrite sep_assoc, sep_swap, sep_assoc, sep_swap23, sep_swap.
            eapply sep_imp; eauto.
            apply sep_imp'; auto.
            rewrite sep_assoc.
            apply sep_imp'; auto.
            apply sep_imp'; auto.
            rewrite <-translate_param_fst.
            erewrite <-output_match; eauto.
            apply blockrep_nodup.
            pose proof (m_nodupvars callee) as Nodup.
            rewrite app_assoc, Permutation_app_comm, app_assoc, Permutation_app_comm in Nodup.
            apply NoDupMembers_app_r in Nodup; rewrite Permutation_app_comm in Nodup.
            rewrite <-map_app, fst_NoDupMembers, translate_param_fst, <-fst_NoDupMembers; auto.
    Qed.

    Lemma corres_auto_funcall:
      forall me1 clsid fid vs me2 rvs c callee cf ptr_f prog' m1 sb outb outco P,
        let oty := type_of_inst (prefix_fun clsid fid) in
        stmt_call_eval prog me1 clsid fid (map Some vs) me2 (map Some rvs) ->
        find_class clsid prog = Some (c, prog') ->
        find_method fid c.(c_methods) = Some callee ->
        m1 |= staterep gcenv prog c.(c_name) me1 sb Z0
                                             ** match callee.(m_out) with
                                                | [] | [_] => sepemp
                                                | _ => blockrep gcenv vempty outco.(co_members) outb
                                                end
                                             ** P ->
        wt_mem me1 prog' c ->
        Forall2 (fun (v : val) (xt : ident * type) => wt_val v (snd xt)) vs (m_in callee) ->
        Globalenvs.Genv.find_symbol tge (prefix_fun clsid fid) = Some ptr_f ->
        Globalenvs.Genv.find_funct_ptr tge ptr_f = Some (Ctypes.Internal cf) ->
        length cf.(fn_params) = (match callee.(m_out) with
                                 | [] | [_] => 1
                                 | _ => 2
                                 end + length vs)%nat ->
        match callee.(m_out) with
        | [] | [_] => True
        | _ => gcenv ! (prefix_fun clsid fid) = Some outco
        end ->
        wt_stmt prog c.(c_objs) c.(c_mems) (meth_vars callee) callee.(m_body) ->
        exists m2,
          eval_funcall tge (function_entry2 tge) m1 (Internal cf)
                       (var_ptr sb
                             :: match callee.(m_out) with
                               | [] | [_] => vs
                               | _ => var_ptr outb :: vs
                               end) E0 m2
                       match rvs with
                       | [v] => v
                       | _ => Vundef
                       end
          /\ m2 |= staterep gcenv prog c.(c_name) me2 sb Z0
                                                 ** match callee.(m_out) with
                                                    | [] | [_] => sepemp
                                                    | _ => blockrep gcenv (Env.adds (map fst callee.(m_out)) rvs vempty) outco.(co_members) outb
                                                    end
                                                 ** P.
    Proof.
      intros ????????????????? Heval Findc Findm Hm1 Wtmem ? Hgetptrf Hgetcf ? ? ?.

      edestruct pres_sem_stmt_call with (6:=Heval) as (? & WT_val); eauto; try rewrite Forall2_map_1; auto.
      inversion_clear Heval as [??????????? Findc' Findm' ? Hev Hvars].
      rewrite Findc' in Findc; inv Findc;
        rewrite Findm' in Findm; inv Findm.
      assert (sub_prog prog' prog) by (eapply find_class_sub; eauto).
      eapply stmt_eval_sub_prog in Hev; eauto.
      eapply wt_mem_sub in Wtmem; eauto; inv Wtmem.

      (* get the clight function *)
      edestruct methods_corres
        as (ptr_f' & cf' & Hgetptrf' & Hgetcf' & Hparams & Hret & ? & ? & ? & ? & ? & ? & Htr); eauto.
      rewrite Hgetptrf' in Hgetptrf; inv Hgetptrf;
        rewrite Hgetcf' in Hgetcf; inv Hgetcf.

      pose proof (find_class_name _ _ _ _ Findc') as Eq;
        pose proof (find_method_name _ _ _ Findm') as Eq';
        rewrite <-Eq, <-Eq' in *.

      assert (length (fn_params cf) =
              length (var_ptr sb :: match m_out callee with
                                         | [] | [_] => vs
                                         | _ :: _ => var_ptr outb :: vs
                                         end))
        by (destruct_list callee.(m_out); simpl; auto).
      assert (length rvs = length callee.(m_out))
        by (now apply Forall2_length in Hvars; rewrite 2 map_length in Hvars).

      assert (NoDup (map fst (m_in callee))) by apply fst_NoDupMembers, m_nodupin.

      edestruct compat_auto_funcall_pres with (vs:=vs) (2:=Findm')
        as (e & le & m & ? & ? & ? & ? & Hm); eauto; simpl; auto.
      - destruct_list callee.(m_out); auto.
      - edestruct stmt_correctness with (p:=prog) (s:=callee.(m_body)) as (le' & m' & Hexec & MS); eauto.
        + apply find_class_In in Findc'; apply find_method_In in Findm'.
          do 2 eapply Forall_forall in NO_NAKED_VARS; eauto.
        + rewrite match_states_conj; split; [|split; [|repeat split; eauto]].
          * rewrite Env.adds_opt_is_adds; auto.
            rewrite Ptrofs.unsigned_zero, sep_swap45; eauto.
          * rewrite Ptrofs.unsigned_zero. split; try omega.
            simpl.
            edestruct make_members_co as (co & Hco & Hsu & Hmb & ? & ? & Hbound); eauto.
            transitivity co.(co_sizeof); auto.
            erewrite co_consistent_sizeof; eauto.
            rewrite Hsu, Hmb.
            apply align_le.
            erewrite co_consistent_alignof; eauto.
            apply alignof_composite_pos.
          * apply wt_env_params; rewrite Forall2_map_1; auto.
          * rewrite Ptrofs.unsigned_zero; omega.
        + rewrite match_states_conj in MS; destruct MS as (Hm_fun' & ?).
          rewrite sep_swap23, sep_swap5, sep_swap in Hm_fun'.
          rewrite <-sep_assoc, sep_unwand in Hm_fun'; auto.
          edestruct free_exists as (m_fun'' & Hfree & Hm_fun''); eauto.
          exists m_fun''; split.
          *{ destruct_list callee.(m_out) as (?, ?)  ? ? : Out; destruct_list rvs; contr.
             - eapply eval_funcall_internal; eauto.
               + constructor; eauto.
               + rewrite Htr.
                 change E0 with (Eapp E0 E0).
                 eapply exec_Sseq_1; eauto.
                 apply exec_Sreturn_none.
               + rewrite Hret; reflexivity.
             - eapply eval_funcall_internal; eauto.
               + constructor; eauto.
               + rewrite Htr.
                 change E0 with (Eapp E0 E0).
                 eapply exec_Sseq_1; eauto.
                 apply exec_Sreturn_some.
                 rewrite sep_swap, match_out_singleton in Hm_fun'; eauto;
                   destruct Hm_fun' as (Hm_fun' & Find').
                 inversion_clear Hvars as [|? ? ? ? Find]; rewrite Find in Find'.
                 econstructor; eauto.
               + rewrite Hret; simpl; split.
                 * destruct t; intro; contr.
                 * inversion_clear WT_val; apply sem_cast_same; auto.
             - eapply eval_funcall_internal; eauto.
               + constructor; eauto.
               + rewrite Htr.
                 change E0 with (Eapp E0 E0).
                 eapply exec_Sseq_1; eauto.
                 apply exec_Sreturn_none.
               + rewrite Hret; reflexivity.
           }
          *{ rewrite sep_swap.
             destruct_list (m_out callee) as (?, ?) ? ? : Out.
             - rewrite 2 sep_drop in Hm_fun''.
               rewrite <-sepemp_left; auto.
             - rewrite 2 sep_drop in Hm_fun''.
               rewrite <-sepemp_left; auto.
             - assert (1 < length callee.(m_out))%nat by (rewrite Out; simpl; omega).
               rewrite match_out_notnil in Hm_fun''; auto; destruct Hm_fun'' as (? & ? & E & Hm_fun'' & ? & ?).
               inversion E; subst outb outco.
               eapply sep_imp; eauto.
               + rewrite <-Out.
                 erewrite <-output_match; eauto.
                 rewrite <-translate_param_fst.
                 rewrite <-Env.adds_opt_is_adds.
                 * apply blockrep_findvars.
                   rewrite translate_param_fst, Out; auto.
                 * rewrite translate_param_fst.
                   apply fst_NoDupMembers, m_nodupout.
               + rewrite sep_drop; apply sep_imp'; auto.
           }
    Qed.

    Definition is_volatile (xt: ident * type) :=
      let (x, t) := xt in
      exists b, Genv.find_symbol (globalenv tprog) (glob_id x) = Some b
           /\ Genv.block_is_volatile (globalenv tprog) b = true.

    Lemma find_main:
      forall m P,
        m |= P ->
        exists c_main prog_main m_reset m_step,
          find_class main_node prog = Some (c_main, prog_main)
          /\ find_method reset c_main.(c_methods) = Some m_reset
          /\ find_method step c_main.(c_methods) = Some m_step
          /\ Forall is_volatile m_step.(m_in)
          /\ Forall is_volatile m_step.(m_out)
          /\ exists b,
              Genv.find_symbol tge tprog.(Ctypes.prog_main) = Some b
              /\ exists main,
                Genv.find_funct_ptr tge b = Some (Ctypes.Internal main)
                /\ main.(fn_return) = type_int32s
                /\ main.(fn_callconv) = AST.cc_default
                /\ main.(fn_params) = []
                /\ main.(fn_vars) = match m_out m_step with
                                   | [] | [_] => []
                                   | _ :: _ => [(prefix out step, type_of_inst (prefix_fun main_node step))]
                                   end
                /\ main.(fn_temps) = map translate_param
                                        (match m_out m_step with
                                         | [yt] => [yt]
                                         | _ => []
                                         end ++ m_in m_step)
                /\ main.(fn_body) = main_body false main_node m_step
                /\ match m_out m_step with
                  | [] | [_] => True
                  | _ =>
                    exists m' step_b,
                    alloc_variables tge empty_env m main.(fn_vars)
                                                           (PTree.set (prefix out step) (step_b, type_of_inst (prefix_fun main_node step))
                                                                      empty_env) m'
                    /\ exists step_co,
                        gcenv ! (prefix_fun main_node step) = Some step_co
                        /\ m' |= blockrep gcenv vempty step_co.(co_members) step_b
                                                                           ** P
                  end.
    Proof.
      intros * Hm.
      pose proof prog_defs_norepet. pose proof global_out_struct as GOS.
      pose proof make_members_co as MMC. pose proof Consistent.
      inv_trans TRANSL as En Estep Ereset with structs funs E.
      unfold make_program' in TRANSL.
      destruct (build_composite_env' (concat structs)) as [(ce, ?)|]; try discriminate.
      destruct (check_size_env ce (concat structs)); try discriminate.
      do 4 econstructor; repeat (split; eauto).
      - inversion TRANSL.
        apply Forall_forall.
        intros (x, t) Hin.
        set (ty := merge_attributes (cltype t) (mk_attr true None)).
        assert ((AST.prog_defmap tprog) ! (glob_id x) =
                Some (@AST.Gvar Clight.fundef _
                                (AST.mkglobvar ty [AST.Init_space (Ctypes.sizeof ce ty)] false true)))
          as Hget.
        subst ty.
        { unfold AST.prog_defmap; simpl.
          apply PTree_Properties.of_list_norepet; auto.
          inversion_clear TRANSL; auto; simpl.
          rewrite map_app.
          apply in_cons, in_app; left; apply in_app; right.
          apply in_map_iff.
          exists (glob_id x, cltype t); split; auto.
          apply in_map_iff.
          exists (x, t); split; auto.
        }
        apply Genv.find_def_symbol in Hget.
        destruct Hget as (b & Findsym & Finddef).
        unfold is_volatile.
        exists b; split; auto.
        unfold Genv.block_is_volatile, Genv.find_var_info.
        change (@Genv.find_def Clight.fundef Ctypes.type (genv_genv (globalenv tprog)) b)
          with (@Genv.find_def Clight.fundef Ctypes.type (@Genv.globalenv Clight.fundef Ctypes.type
                                                                          (@program_of_program function tprog)) b).
        rewrite Finddef; auto.

      - inversion TRANSL.
        apply Forall_forall.
        intros (x, t) Hin.
        set (ty := merge_attributes (cltype t) (mk_attr true None)).
        assert ((AST.prog_defmap tprog) ! (glob_id x) =
                Some (@AST.Gvar Clight.fundef _
                                (AST.mkglobvar ty [AST.Init_space (Ctypes.sizeof ce ty)] false true)))
          as Hget.
        subst ty.
        { unfold AST.prog_defmap; simpl.
          apply PTree_Properties.of_list_norepet; auto.
          inversion_clear TRANSL; auto; simpl.
          rewrite map_app.
          apply in_cons, in_app; left; apply in_app; left.
          apply in_map_iff.
          exists (glob_id x, cltype t); split; auto.
          apply in_map_iff.
          exists (x, t); split; auto.
        }
        apply Genv.find_def_symbol in Hget.
        destruct Hget as (b & Findsym & Finddef).
        unfold is_volatile.
        exists b; split; auto.
        unfold Genv.block_is_volatile, Genv.find_var_info.
        change (@Genv.find_def Clight.fundef Ctypes.type (genv_genv (globalenv tprog)) b)
          with (@Genv.find_def Clight.fundef Ctypes.type (@Genv.globalenv Clight.fundef Ctypes.type
                                                                          (@program_of_program function tprog)) b).
        rewrite Finddef; auto.

      - assert ((AST.prog_defmap tprog) ! main_id = Some (make_main false main_node m0)
                /\ tprog.(Ctypes.prog_main) = main_id)
          as [Hget Hmain_id].
        { unfold AST.prog_defmap; simpl; split;
            [apply PTree_Properties.of_list_norepet; auto|];
            inversion_clear TRANSL; auto.
          apply in_cons, in_app; right; apply in_app; right.
          destruct do_sync; [do 2 apply in_cons|]; apply in_eq.
        }
        rewrite Hmain_id.
        apply Genv.find_def_symbol in Hget.
        destruct Hget as (b & Findsym & Finddef).
        exists b; split; auto; econstructor; repeat split; eauto.
        + change (Genv.find_funct_ptr tge b) with (Genv.find_funct_ptr (Genv.globalenv tprog) b).
          unfold Genv.find_funct_ptr.
          unfold Clight.fundef in Finddef.
          now rewrite Finddef.
        + eauto.
        + eauto.
        + eauto.
        + eauto.
        + eauto.
        + eauto.
        + simpl.
          destruct_list m0.(m_out) : Out; auto.
          assert (1 < length m0.(m_out))%nat by (rewrite Out; simpl; omega).
          destruct (Mem.alloc m 0 (sizeof tge (type_of_inst (prefix_fun main_node step))))
            as (m', step_b) eqn: AllocStep.
          exists m', step_b; split.
          * repeat (econstructor; eauto).
          * edestruct GOS with (2:=Estep) as (step_co & Hsco & ? & Hms & ? & ? & ?); eauto.
            edestruct MMC as (co & Hco & ? & ? & ? & ? & ?); eauto.
            exists step_co.
            pose proof (find_class_name _ _ _ _ En) as Eq;
              pose proof (find_method_name _ _ _ Estep) as Eq';
              rewrite Eq, Eq' in *.
            split; auto.
            change (gcenv ! (prefix_fun main_node step))
              with ((prog_comp_env tprog) ! (prefix_fun main_node step)) in Hsco.
            assert (sizeof tge (type_of_inst (prefix_fun main_node step)) <= Int.modulus)
              by (simpl; rewrite Hsco; transitivity Int.max_unsigned;
                  auto; unfold Int.max_unsigned; omega).
            eapply alloc_rule in AllocStep; eauto; try omega.
            eapply sep_imp; eauto.
            simpl; rewrite Hsco; eapply blockrep_empty; eauto.
            rewrite Hms; eauto.
    Qed.

    Lemma init_mem:
      exists m sb,
        Genv.init_mem tprog = Some m
        /\ Genv.find_symbol tge (glob_id self) = Some sb
        /\ m |= staterep gcenv prog main_node mempty sb Z0.
    Proof.
      clear SPEC_IO NO_NAKED_VARS. pose proof find_self as FS.
      pose proof prog_defs_norepet. pose proof make_members_co as MMC.
      pose proof Consistent as C.
      inv_trans TRANSL as En Estep Ereset with structs funs E.
      pose proof (build_ok _ _ _ _ _ _ _ TRANSL) as Hbuild.
      pose proof TRANSL as TRANSL'.
      apply make_program_defs in TRANSL'; destruct TRANSL' as (gce & Hbuild' & Eq).
      rewrite Hbuild in Hbuild'; inv Hbuild'.
      destruct Genv.init_mem_exists with (p:=tprog) as (m' & Initmem).
      - rewrite Eq; clear Eq.
        simpl.
        intros * [Hinv|Hinv].
        + inv Hinv; simpl; split.
          * split; auto; apply Z.divide_0_r.
          * intros * Hinio; simpl in Hinio;
              destruct Hinio; [discriminate|contradiction].
        + repeat rewrite in_app in Hinv;
            destruct Hinv as [Hinv|[Hinv|[Hinv|Hinv]]]; try now inv Hinv.
          *{ clear TRANSL.
             induction (map glob_bind (m_out m) ++ map glob_bind (m_in m)) as [|(x, t)].
             - contradict Hinv.
             - destruct Hinv as [Hinv|]; auto.
               inv Hinv; simpl; split.
               + split; auto; apply Z.divide_0_r.
               + intros * Hinio; simpl in Hinio;
                   destruct Hinio; [discriminate|contradiction].
           }
          *{ clear En Hbuild WT.
             remember prog as prog1.
             replace (translate_class (rev prog1)) with (translate_class (rev prog)) in E
               by now rewrite <-Heqprog1.
             clear Heqprog1 TRANSL MMC.
             revert structs funs E Hinv.
             induction prog1 as [|c' prog']; intros * E Hinv; simpl in E.
             - inv E; simpl in Hinv; contradiction.
             - rewrite map_app in E; simpl in E; rewrite split_last in E.
               destruct (split (map (translate_class (rev prog)) (rev prog'))) as (g, d) eqn: Egd; inv E.
               rewrite concat_app in Hinv; simpl in Hinv; rewrite app_nil_r in Hinv;
                 apply in_app in Hinv; destruct Hinv as [|Hinv]; eauto.
               unfold make_methods in Hinv.
               induction (c_methods c'); simpl in Hinv; try contradiction.
               destruct Hinv as [Hinv|]; auto.
               unfold translate_method in Hinv.
               destruct_list (m_out a) as (?, ?) ? ?; inv Hinv.
           }
          * destruct do_sync; try now inv Hinv.
            rewrite cons_is_app, in_app in Hinv.
            destruct Hinv as [[Hinv|Hinv]|[Hinv|Hinv]]; try inv Hinv.
      - exists m'.
        destruct FS as (sb & find_step).
        exists sb; split; [|split]; auto.
        assert (NoDupMembers tprog.(AST.prog_defs)) as Nodup
            by (rewrite fst_NoDupMembers, NoDup_norepet; auto).
        pose proof (init_grange _ _ Nodup Initmem) as Hgrange.
        unfold make_program' in TRANSL.
        destruct (build_composite_env' (concat structs)) as [(ce, ?)|]; try discriminate.
        destruct (check_size_env ce (concat structs)) eqn: Check_size; try discriminate.
        unfold translate_class in E.
        apply split_map in E; destruct E as [? Funs].
        inversion TRANSL as [Htprog].
        rewrite <-Htprog in Hgrange at 2.
        simpl in Hgrange.
        change (Genv.find_symbol tge (glob_id self) = Some sb)
          with (Genv.find_symbol (Genv.globalenv tprog) (glob_id self) = Some sb) in find_step.
        rewrite find_step in Hgrange.
        rewrite <-Zplus_0_r_reverse in Hgrange.
        rewrite Zmax_left in Hgrange;
          [|destruct (ce ! main_node); try omega; apply co_sizeof_pos].
        apply sep_proj1 in Hgrange.
        rewrite sepemp_right in *.
        eapply sep_imp; eauto.
        rewrite pure_sepwand.
        + unfold Genv.perm_globvar. simpl.
          transitivity (range_w sb 0 (sizeof gcenv (type_of_inst main_node))).
          * unfold sizeof. simpl.
            change (gcenv ! main_node) with (tprog.(prog_comp_env) ! main_node).
            rewrite <-Htprog; auto.
          * apply range_staterep; auto.
            intro En'; rewrite En' in En; discriminate.
        + edestruct MMC as (co & Find_main & ? & ? & ? & ? & ?); eauto.
          change (gcenv ! main_node) with (tprog.(prog_comp_env) ! main_node) in Find_main.
          rewrite <-Htprog in Find_main; simpl in Find_main.
          rewrite Find_main.
          transitivity Int.max_unsigned; auto; unfold Int.max_unsigned; omega.
    Qed.

    Section Init.
      Variables (c_main: class) (prog_main: program) (m_reset m_step: method).
      Hypothesis Find: find_class main_node prog = Some (c_main, prog_main).
      Hypothesis Findreset: find_method reset c_main.(c_methods) = Some m_reset.
      Hypothesis Findstep: find_method step c_main.(c_methods) = Some m_step.

      (* XXX: to be discharged from generation function *)
      Hypothesis Reset_in_spec: m_reset.(m_in) = [].
      Hypothesis Reset_out_spec: m_reset.(m_out) = [].
      Hypothesis Step_in_spec: m_step.(m_in) <> [].
      Hypothesis Step_out_spec: m_step.(m_out) <> [].

      Hypothesis Step_in: Forall is_volatile m_step.(m_in).
      Hypothesis Step_out: Forall is_volatile m_step.(m_out).

      Variables (rst_ptr stp_ptr: block) (reset_f step_f: function).
      Hypothesis Getreset_s: Genv.find_symbol tge (prefix_fun main_node reset) = Some rst_ptr.
      Hypothesis Getreset_f: Genv.find_funct_ptr tge rst_ptr = Some (Internal reset_f).
      Hypothesis Getstep_s: Genv.find_symbol tge (prefix_fun main_node step) = Some stp_ptr.
      Hypothesis Getstep_f: Genv.find_funct_ptr tge stp_ptr = Some (Internal step_f).

      Variables (main_b: block) (main_f: function) (sb step_b: block)
                (step_co: composite).
      Hypothesis Find_s_main: Genv.find_symbol tge tprog.(Ctypes.prog_main) = Some main_b.
      Hypothesis Findmain: Genv.find_funct_ptr tge main_b = Some (Ctypes.Internal main_f).
      Hypothesis Caractmain: main_f.(fn_return) = type_int32s
                             /\ main_f.(fn_callconv) = AST.cc_default
                             /\ main_f.(fn_params) = []
                             /\ main_f.(fn_vars) = match m_out m_step with
                                                  | [] | [_] => []
                                                  | _ :: _ => [(prefix out step, type_of_inst (prefix_fun main_node step))]
                                                  end
                             /\ main_f.(fn_temps) = map translate_param
                                                       (match m_out m_step with
                                                        | [yt] => [yt]
                                                        | _ => []
                                                        end ++ m_in m_step)
                             /\ main_f.(fn_body) = main_body false main_node m_step.

      Hypothesis Getstep_co: match m_step.(m_out) with
                             | [] | [_] => True
                             | _ => gcenv ! (prefix_fun main_node step) = Some step_co
                             end.

      Variables (m0 m1: Mem.mem).
      Hypothesis Initmem: Genv.init_mem tprog = Some m0.

      Let e1 := match m_step.(m_out) with
                | [] | [_] => empty_env
                | _ => PTree.set (prefix out step) (step_b, type_of_inst (prefix_fun main_node step))
                                empty_env
                end.
      Hypothesis Alloc: alloc_variables tge empty_env m0 main_f.(fn_vars) e1 m1.

      Hypothesis find_step: Genv.find_symbol (Genv.globalenv tprog) (glob_id self) = Some sb.

      Variable P: massert.

      Hypothesis Hm0: m1 |= staterep gcenv prog main_node mempty sb Z0
                         ** match m_step.(m_out) with
                            | [] | [_] => sepemp
                            | _ => blockrep gcenv vempty step_co.(co_members) step_b
                            end
                         ** P.

      Variable me0: menv.
      Hypothesis ResetNode: stmt_call_eval prog mempty c_main.(c_name) m_reset.(m_name) [] me0 [].

      Let le_main := create_undef_temps main_f.(fn_temps).

      Lemma entry_main:
        function_entry2 (globalenv tprog) main_f [] m0 e1 le_main m1.
      Proof.
        destruct Caractmain as (Hret & Hcc & Hparams & Hvars & Htemps & Hbody).
        econstructor; eauto.
        - rewrite Hvars.
          unfold var_names.
          rewrite <-NoDup_norepet, <-fst_NoDupMembers.
          destruct_list m_step.(m_out); repeat constructor; auto.
        - rewrite Hparams; constructor.
        - rewrite Hparams, Htemps; simpl.
          intros ? ? Hx; contradiction.
        - unfold le_main; rewrite Hparams, Htemps; simpl; auto.
      Qed.

      Lemma match_states_main_after_reset:
        exists m2,
          eval_funcall tge (function_entry2 tge) m1 (Internal reset_f)
                       [var_ptr sb] E0 m2 Vundef
          /\ m2 |= staterep gcenv prog c_main.(c_name) me0 sb 0
                                                      ** match m_step.(m_out) with
                                                         | [] | [_] => sepemp
                                                         | _ => blockrep gcenv vempty step_co.(co_members) step_b
                                                         end
                                                      ** P.
      Proof.
        pose proof methods_corres as MC.
        pose proof corres_auto_funcall as CAF.
        pose proof (find_class_name _ _ _ _ Find) as Eq;
          pose proof (find_method_name _ _ _ Findreset) as Eq';
          rewrite <-Eq, <-Eq' in *.
        edestruct MC with (2:=Findreset)
          as (ptr & f & Get_s & Get_f & Hp & ? & ? & ? & ? & ? & ? & ?); eauto.
        rewrite Getreset_s in Get_s; inversion Get_s; subst ptr;
          rewrite Getreset_f in Get_f; inversion Get_f; subst f.
        edestruct CAF with (3:=Findreset) (vs := @nil val) (rvs := @nil val)
          as (m'' & ? & Hm''); eauto.
        - rewrite Reset_out_spec, sep_swap, <-sepemp_left; eauto.
        - rewrite Reset_in_spec; auto.
        - rewrite Hp, Reset_in_spec, Reset_out_spec; auto.
        - rewrite Reset_out_spec; auto.
        - edestruct wt_program_find_class as [WT_main]; eauto.
          eapply wt_stmt_sub with (prog':=prog_main); eauto.
          + eapply wt_class_find_method with (2:=Findreset); auto.
          + eapply find_class_sub; eauto.
        - rewrite Reset_out_spec in *.
          exists m''; split; auto.
          rewrite sep_swap, <-sepemp_left in Hm''; auto.

          Grab Existential Variables.
          eauto.
          eauto.
      Qed.

      Lemma match_states_main_after_step:
        forall m' P me me' vs rvs,
          stmt_call_eval prog me c_main.(c_name) m_step.(m_name) (map Some vs) me' (map Some rvs) ->
          m' |= staterep gcenv prog c_main.(c_name) me sb 0
                                                    ** match m_step.(m_out) with
                                                       | [] | [_] => sepemp
                                                       | _ => blockrep gcenv vempty step_co.(co_members) step_b
                                                       end
                                                    ** P ->
          wt_mem me prog_main c_main ->
          wt_vals vs m_step.(m_in) ->
          exists m'',
            eval_funcall tge (function_entry2 tge) m' (Internal step_f)
                         (var_ptr sb
                               :: match m_step.(m_out) with
                                 | [] | [_] => vs
                                 | _ => var_ptr step_b :: vs
                                 end) E0 m''
                         match rvs with
                         | [v] => v
                         | _ => Vundef
                         end

            /\ m'' |= staterep gcenv prog c_main.(c_name) me' sb 0
                                                         ** match m_step.(m_out) with
                                                            | [] | [_] => sepemp
                                                            | _ => blockrep gcenv (Env.adds (map fst m_step.(m_out)) rvs vempty) step_co.(co_members) step_b
                                                            end
                                                         ** P.
      Proof.
        pose proof methods_corres as MC.
        pose proof corres_auto_funcall as CAF.
        intros.
        pose proof (find_class_name _ _ _ _ Find) as Eq;
          pose proof (find_method_name _ _ _ Findstep) as Eq';
          rewrite <-Eq, <-Eq' in *.
        edestruct MC with (2:=Findstep)
          as (ptr & f & Get_s & Get_f & Hp & ? & ? & ? & ? & ? & ? & ?); eauto.
        rewrite Getstep_s in Get_s; inversion Get_s; subst ptr;
          rewrite Getstep_f in Get_f; inversion Get_f; subst f.
        edestruct CAF with (3:=Findstep) as (m'' & ? & Hm''); eauto.
        - destruct_list m_step.(m_out); rewrite Hp; simpl; rewrite map_length;
            symmetry; erewrite Forall2_length; eauto.
        - edestruct wt_program_find_class as [WT_main]; eauto.
          eapply wt_stmt_sub with (prog':=prog_main); eauto.
          + eapply wt_class_find_method with (2:=Findstep); auto.
          + eapply find_class_sub; eauto.
      Qed.


      (*****************************************************************)
      (** Trace semantics of reads and writes to volatiles             *)
      (*****************************************************************)

      Lemma exec_read:
        forall cs le m,
          wt_vals cs m_step.(m_in) ->
          exists le', (* XXX: not any le': the one that contains [cs] *)
            exec_stmt (globalenv tprog) (function_entry2 (globalenv tprog)) e1 le m
                      (load_in m_step.(m_in))
                      (load_events cs m_step.(m_in))
                      le' m Out_normal
            /\ Forall2 (fun v xt => le' ! (fst xt) = Some v) cs m_step.(m_in)
            /\ (forall x, ~ InMembers x m_step.(m_in) -> le' ! x = le ! x).
      Proof.
        clear Caractmain Step_in_spec.
        pose proof (m_nodupin m_step) as Hnodup.
        pose proof (m_good_in m_step) as Good.

        induction m_step.(m_in) as [|(x, t)]; simpl;
          intros * Hwt;
          inversion_clear Hwt as [| v ? vs ? Hwt_v Hwts ];
          inversion_clear Hnodup.
        - (* Case: m_step.(m_in) ~ [] *)
          rewrite load_events_nil.
          repeat econstructor; auto.
        - (* Case: m_step.(m_in) ~ xt :: xts *)
          inversion_clear Step_in as [|? ? Findx].
          destruct Findx as (bx & Findx & Volx).
          rewrite load_events_cons.

          assert (exists le',
                     exec_stmt (globalenv tprog) (function_entry2 (globalenv tprog)) e1 le m
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
                rewrite <-not_Some_is_None.
                intros (b, t') Hget.
                subst e1.
                assert (glob_id x <> self) by (eapply self_not_glob; eauto).
                destruct_list m_step.(m_out).
                * rewrite PTree.gempty in Hget; auto; try discriminate.
                * rewrite PTree.gempty in Hget; auto; try discriminate.
                *{ rewrite PTree.gso, PTree.gempty in Hget; auto; try discriminate.
                   intro E; apply (glob_id_not_prefixed x).
                   - apply (Good (x, t)), in_eq.
                   - rewrite E; constructor.
                 }
              + unfold Cop.sem_cast; simpl; eauto.
            - constructor.
              unfold load_event_of_val; simpl.
              rewrite wt_val_load_result with (ty:=t); auto.
              apply volatile_load_vol; auto.
              apply eventval_of_val_match; auto.
          }

          assert (forall x0 : ident * type, In x0 l -> ValidId x0)
            by (intros; apply Good, in_cons; auto).
          edestruct IHl with (le := le') as (le'' & ? & Hgss & Hgso); eauto.

          exists le''.
          repeat split.
          + eapply exec_Sseq_1; eauto.
          + econstructor; eauto.
            rewrite Hgso; auto.
          + intros * Hnot_in.
            apply Decidable.not_or in Hnot_in as [? ?].
            rewrite Hgso; auto.
      Qed.

      Lemma exec_write:
        forall vs ve le m,
          wt_vals vs m_step.(m_out) ->
          m |= match m_step.(m_out), vs with
               | [], [] => sepemp
               | [(y, _)], [v] => pure (le ! y = Some v)
               | _, _ => blockrep gcenv (Env.adds (map fst m_step.(m_out)) vs ve) (co_members step_co) step_b
               end
            ** P ->
          exec_stmt (globalenv tprog) (function_entry2 (globalenv tprog)) e1 le m
                    (write_out main_node m_step.(m_out))
                    (store_events vs m_step.(m_out))
                    le m Out_normal.
      Proof.
        pose proof global_out_struct as GOS.
        intros * WT_vals Hrep.
        assert (length vs = length m_step.(m_out)) as Length by (eapply Forall2_length; eauto).
        (* XXX: factorize proof (& code) with [exec_read] *)
        destruct_list m_step.(m_out) as (y, t) (y', t') outs : Out;
          destruct_list vs as v v' vs' : Vs; contr.

        - unfold write_out.
          inversion_clear Step_out as [|? ? Findy].
          destruct Findy as (b_y & Findy & Voly).
          inversion_clear WT_vals.
          eapply exec_Sbuiltin with (vres:=Vundef).
          + repeat
              match goal with
              | |- eval_exprlist _ _ _ _ _ _ _ => econstructor
              end.
            * econstructor.
              apply eval_Evar_global; eauto.
              rewrite <-not_Some_is_None.
              intros (b, t'') Hget.
              subst e1.
              rewrite PTree.gempty in Hget; contr.
            * reflexivity.
            * econstructor.
              apply sep_pure in Hrep; destruct Hrep as (Hpure & Hrep).
              change val with Values.val in Hpure.
              rewrite Hpure; eauto.
            * eapply sem_cast_same; eauto.
          + constructor.
            apply volatile_store_vol; auto; simpl.
            rewrite <-wt_val_load_result; auto.
            apply eventval_of_val_match; auto.

        - assert (1 < length m_step.(m_out))%nat by (rewrite Out; simpl; omega).
          clear Caractmain Step_out_spec Hm0.

          pose proof (m_nodupout m_step) as Hnodup.

          pose proof (find_class_name _ _ _ _ Find) as Eq;
            pose proof (find_method_name _ _ _ Findstep) as Eq';
            rewrite <-Eq, <-Eq' in *.

          assert (e1 ! (prefix out step)
                  = Some (step_b, type_of_inst (prefix_fun main_node step))) as Findstr
              by (subst e1; rewrite PTree.gss; auto).
          rewrite <-Eq, <-Eq' in Findstr.

          edestruct GOS with (2:=Findstep)
            as (step_co' & Hrco & ? & Hmr & ? & ? & ?); eauto.
          rewrite Getstep_co in Hrco; inversion Hrco; subst step_co'.

          (* This induction is tricky: [co_members step_co ~ m_out m_step]
           is fixed across the induction while we are going down inside
           [m_out m_step]. The following assertion allows us to get back
           into [co_members] whenever necessary. *)

          assert (Hfield_offs: forall x ty,
                     In (x, ty) (map translate_param (m_out m_step)) ->
                     In (x, ty) (co_members step_co))
            by now rewrite Hmr.

          unfold write_out.

          rewrite <-Vs, <-Out in *.
          clear Vs.
          pose proof (m_good_out m_step) as Good.
          revert ve vs Hrep Hnodup Hfield_offs Findstr Step_out Eq Eq' Length WT_vals Good.
          generalize m_step.(m_out) as xts.
          clear - Getstep_co.

          induction xts as [|(x, t) xts]; destruct vs; contr;
            intros; eauto using exec_stmt.

          inversion_clear Hnodup as [|? ? ? Notin].
          inversion_clear Step_out as [|? ? Findx].
          destruct Findx as (bx & Findx & Volx).
          inversion_clear WT_vals.

          rewrite store_events_cons.
          eapply exec_Sseq_1 with (le1 := le); eauto.
          + eapply exec_Sbuiltin with (vres:=Vundef).
            *{ repeat
                 match goal with
                 | |- eval_exprlist _ _ _ _ _ _ _ => econstructor
                 end.
               - econstructor.
                 apply eval_Evar_global; eauto.
                 rewrite <-not_Some_is_None.
                 intros (b, t'') Hget.
                 subst e1.
                 rewrite PTree.gso, PTree.gempty in Hget.
                 + discriminate.
                 + intro E; apply (glob_id_not_prefixed x).
                   * apply (Good (x, t)), in_eq.
                   * rewrite E; constructor.
               - reflexivity.
               - assert (In (x, cltype t) (co_members step_co))
                   by now eapply Hfield_offs; econstructor; eauto.

                 edestruct blockrep_field_offset as (? & ? & ? & ?); eauto.

                 eapply eval_Elvalue; eauto.
                 + eapply eval_Efield_struct; eauto.
                   *{ eapply eval_Elvalue; eauto.
                      - constructor;
                          rewrite <- Eq'; eauto.
                      - now apply deref_loc_copy.
                    }
                   * unfold type_of_inst; simpl; rewrite Eq'; eauto.
                 + simpl; eapply blockrep_deref_mem; eauto.
                   * simpl; apply Env.find_gsss.
                     now rewrite <-fst_InMembers.
                   * rewrite Ptrofs.unsigned_zero; simpl.
                     rewrite Ptrofs.unsigned_repr; auto.
               - eapply sem_cast_same; eauto.
             }
            * constructor.
              apply volatile_store_vol; auto.
              rewrite <-wt_val_load_result; auto.
              apply eventval_of_val_match; auto.

          + eapply IHxts with (ve:=Env.add x v ve); eauto.
            * intros.
              eapply Hfield_offs. constructor 2; auto.
            * intros; apply Good, in_cons; auto.
      Qed.

      (*****************************************************************)
      (** Clight version of Corr.dostep'                               *)
      (*****************************************************************)

      Section dostep.

        Variables ins outs: Str.stream (list val).
        Variables xs ys: list (ident * type).

        Hypothesis Hwt_ins: forall n, wt_vals (ins n) m_step.(m_in).
        Hypothesis Hwt_outs: forall n, wt_vals (outs n) m_step.(m_out).

        (** This coinductive predicate describes the logical behavior of
          the [while] loop. *)

        CoInductive dostep : nat -> mem -> Prop
          := Step :
               forall n me me',
                 eval_funcall tge (function_entry2 tge) me (Internal step_f)
                              (var_ptr sb
                                    :: match m_step.(m_out) with
                                       | []  | [_] => ins n
                                       | _ => var_ptr step_b :: (ins n)
                                       end) E0 me'
                              match outs n with
                              | [v] => v
                              | _ => Vundef
                              end
                 ->
                 me' |= match m_step.(m_out) with
                        | [] | [_] => sepemp
                        | _ => blockrep gcenv (Env.adds (map fst (m_out m_step))
                                                        (outs n) vempty)
                                        (co_members step_co) step_b
                        end
                     ** P ->
                 dostep (S n) me' ->
                 dostep n me.

        Section Dostep_coind.

          Variable t: genv.
          Variable R: nat -> mem -> Prop.

          Hypothesis StepCase: forall n me,
              R n me ->
              exists me',
                eval_funcall tge (function_entry2 tge) me (Internal step_f)
                             (var_ptr sb
                                   :: match m_step.(m_out) with
                                      | [] | [_] => ins n
                                      | _ => var_ptr step_b :: (ins n)
                                      end) E0 me'
                             match outs n with
                             | [v] => v
                             | _ => Vundef
                             end
                /\ me' |= match m_step.(m_out) with
                          | [] | [_] => sepemp
                          | _ => blockrep gcenv (Env.adds (map fst (m_out m_step)) (outs n) vempty)
                                          (co_members step_co) step_b
                          end
                       ** P
                /\ R (S n) me'.

          Lemma dostep_coind:
            forall n me,
              R n me  -> dostep n me.
          Proof.
            cofix COINDHYP.
            intros ? ? HR.
            pose proof (StepCase _ _ HR) as Hstep.
            simpl in *; decompose record Hstep; subst.
            econstructor; eauto.
          Qed.

        End Dostep_coind.

        Definition mInit := m1.

        Hypothesis WT_mem: wt_mem me0 prog_main c_main.
        Hypothesis LoopCall: loop_call prog (c_name c_main) step
                                       (fun n => map Some (ins n)) (fun n => map Some (outs n)) 0 me0.

        Lemma dostep_imp:
          wt_program prog ->
          exists m0,
            eval_funcall tge (function_entry2 tge) mInit (Internal reset_f)
                         [var_ptr sb] E0 m0 Vundef
            /\ dostep 0 m0.
        Proof.
          intros Hwt_prog (* Hwt_mem Hdostep *).

          (* Initialisation *)
          edestruct match_states_main_after_reset as (mem0 & ? & Hmem0).
          eexists; split; eauto.
          (* rewrite <- sep_assoc, sep_swap, sep_assoc, sep_swap in Hmem0. *)

          (* Coinduction *)
          set (R := fun n (m: mem) =>
                      exists me,
                        loop_call prog (c_name c_main) step
                                  (fun n => map Some (ins n)) (fun n => map Some (outs n)) n me
                        /\ wt_mem me prog_main c_main
                        /\ m
                             |= staterep gcenv prog (c_name c_main) me sb 0
                             ** match m_step.(m_out) with
                                | [] | [_] => sepemp
                                | _ => blockrep gcenv vempty (co_members step_co) step_b
                                end
                             ** P).
          apply dostep_coind with (R := R);
            unfold R.
          - (* clear - Hwt_ins Hwt_prog WT_mem m_step Find Findstep. *)
            pose proof match_states_main_after_step as MSMAS.

            intros n meN (? & Hdostep & Hwt & Hblock).
            destruct Hdostep as [n menvN menvSn (* cins couts *) Hstmt Hdostep].
            specialize Hwt_ins with n.

            assert (c_name c_main = main_node) as <-
                by now eapply find_class_name; eauto.

            assert (m_step.(m_name) = step) as Hstep
                by now eapply find_method_name; eauto.

            assert (exists meSn,
                       eval_funcall tge (function_entry2 tge) meN
                                    (Internal step_f)
                                    (var_ptr sb
                                          :: match m_step.(m_out) with
                                             | [] | [_] => ins n
                                             | _ => var_ptr step_b :: (ins n)
                                             end)
                                    E0 meSn
                                    match outs n with
                                    | [v] => v
                                    | _ => Vundef
                                    end
                       /\ meSn
                            |= staterep gcenv prog (c_name c_main) menvSn sb 0
                            ** match m_step.(m_out) with
                               | [] | [_] => sepemp
                               | _ => blockrep gcenv (Env.adds (map fst (m_out m_step)) (outs n) vempty)
                                               (co_members step_co) step_b
                               end
                            ** P)
              as (meSn & ? & Hblock_step).
            {
              eapply MSMAS; eauto. rewrite Hstep; auto.
            }

            exists meSn.

            assert (meSn |= match m_step.(m_out) with
                            | [] | [_] => sepemp
                            | _ => blockrep gcenv (Env.adds (map fst (m_out m_step)) (outs n) vempty)
                                            (co_members step_co) step_b
                            end
                         ** P)
              by (apply sep_drop in Hblock_step; auto).

            assert (wt_mem menvSn prog_main c_main)
              by (edestruct pres_sem_stmt_call as (? & ?); eauto; rewrite Forall2_map_1; auto).

            assert (meSn
                      |= staterep gcenv prog (c_name c_main) menvSn sb 0
                      ** match m_step.(m_out) with
                         | [] | [_] => sepemp
                         | _ => blockrep gcenv vempty (co_members step_co) step_b
                         end
                      ** P).
            {
              eapply sep_imp.
              - eapply Hblock_step.
              - auto.
              - destruct_list m_step.(m_out); eauto.
                rewrite blockrep_any_empty; auto.
            }

            repeat (split; eauto).

          - now exists me0; repeat (split; auto).
        Qed.

        (*    End dostep'. *)

        (*****************************************************************)
        (** Correctness of the main loop                                 *)
        (*****************************************************************)

        Lemma exec_body:
          forall n meN le,
            dostep n meN ->
            exists leSn meSn,
              exec_stmt (globalenv tprog) (function_entry2 (globalenv tprog)) e1 le meN
                        (main_loop_body false main_node m_step)
                        (load_events (ins n) (m_in m_step)
                                     ++ E0
                                     ++ store_events (outs n) (m_out m_step))
                        leSn meSn Out_normal
              /\ dostep (S n) meSn.
        Proof.
          intros * Hdostep.

          destruct Hdostep as [n meN meSn Hvals_in Hvals_out Hfuncall].

          (* load in *)
          edestruct exec_read
            with (le := le)(m := meN)
            as (le1 & Hload & Hgss_le1 & Hgso_le1); eauto.

          assert (eval_exprlist (globalenv tprog) e1 le1 meN
                                (Eaddrof (Evar (glob_id self) (type_of_inst main_node)) (type_of_inst_p main_node)
                                         :: match m_step.(m_out) with
                                            | [] | [_] => map make_in_arg (m_in m_step)
                                            | _ => Eaddrof (Evar (prefix out step)
                                                                 (type_of_inst (prefix_fun main_node step)))
                                                           (pointer_of (type_of_inst (prefix_fun main_node step)))
                                                           :: map make_in_arg (m_in m_step)
                                            end)
                                (Ctypes.Tcons
                                   (type_of_inst_p main_node)
                                   match m_step.(m_out) with
                                   | [] | [_] => list_type_to_typelist (map Clight.typeof (map make_in_arg (m_in m_step)))
                                   | _ => Ctypes.Tcons
                                            (pointer_of (type_of_inst (prefix_fun main_node step)))
                                            (list_type_to_typelist
                                               (map Clight.typeof (map make_in_arg (m_in m_step))))
                                   end)
                                (var_ptr sb
                                      :: match m_step.(m_out) with
                                         | [] | [_] => ins n
                                         | _ => var_ptr step_b :: (ins n)
                                         end)).
          {
            assert (forall vs,
                       wt_vals vs m_step.(m_in) ->
                       Forall2 (fun v xt => le1 ! (fst xt) = Some v) vs m_step.(m_in) ->
                       eval_exprlist (globalenv tprog) e1 le1 meN
                                     (map make_in_arg m_step.(m_in))
                                     (list_type_to_typelist
                                        (map Clight.typeof (map make_in_arg (m_in m_step))))
                                     vs).
            {
              clear.
              induction m_step.(m_in) as [|(x, t)];
                intros ? Hvals_in;
                inversion_clear Hvals_in as [| cin ? cins];
                intro Hdef;
                inversion_clear Hdef;
                simpl in *;
                eauto using eval_exprlist.
              apply eval_Econs with (v1 := cin)(v2 := cin).
              econstructor; eauto.
              now apply sem_cast_same.
              apply IHl; eauto.
            }
            destruct_list m_step.(m_out).
            - econstructor; eauto.
              + econstructor.
                apply eval_Evar_global; eauto.
                rewrite PTree.gempty; auto.
              + constructor.
            - econstructor; eauto.
              + econstructor.
                apply eval_Evar_global; eauto.
                rewrite PTree.gempty; auto.
              + constructor.
            - econstructor.
              + econstructor.
                apply eval_Evar_global; eauto.
                rewrite <-not_Some_is_None.
                intros (b, t'') Hget.
                subst e1.
                rewrite PTree.gso, PTree.gempty in Hget.
                * discriminate.
                *{ intro E; apply (glob_id_not_prefixed self).
                   - apply self_valid.
                   - rewrite E; constructor.
                 }
              + constructor.
              + repeat (econstructor; eauto).
                subst e1. rewrite PTree.gss; auto.
          }

          assert (length (outs n) = length m_step.(m_out))
            by (specialize (Hwt_outs n); eapply Forall2_length; eauto).

          (* call step *)
          assert (exists le2,
                     exec_stmt (globalenv tprog) (function_entry2 (globalenv tprog)) e1 le1 meN
                               (step_call main_node (map make_in_arg (m_in m_step)) (m_out m_step)) E0
                               le2 meSn Out_normal
                     /\ match m_step.(m_out), outs n with
                        | [(x, _)], [v] => le2 ! x = Some v
                        | _, _ => True
                        end)
            as (le2 & Hcall & ?).
          { edestruct methods_corres with (2:=Findstep)
              as (ptr & f & Get_s & Get_f & Hp_stp & Hr_stp & Hcc_stp
                  & ? & ? & ? & ? & ? & Htr_stp); eauto.
            rewrite Getstep_s in Get_s; inversion Get_s; subst ptr;
              rewrite Getstep_f in Get_f; inversion Get_f; subst f.
            unfold step_call.
            destruct_list m_step.(m_out) as (?, ?) ? ? : Out.
            - eexists; split; auto;
                eapply exec_Scall; simpl; eauto; simpl.
              + eapply eval_Elvalue.
                * apply eval_Evar_global; eauto.
                  rewrite PTree.gempty; auto.
                * apply deref_loc_reference; auto.
              + unfold Genv.find_funct. auto.
              + assert (c_name c_main = main_node) as <-
                    by now eapply find_class_name; eauto.
                assert (m_step.(m_name) = step) as Hstep
                    by now eapply find_method_name; eauto.
                simpl; unfold type_of_function;
                  rewrite Hp_stp, Hr_stp, Hcc_stp; simpl; repeat f_equal.
                clear.
                induction (m_in m_step) as [|(x, t)]; simpl; auto.
                rewrite IHl; auto.
            - eexists; split.
              + eapply exec_Scall; simpl; eauto; simpl.
                *{ eapply eval_Elvalue.
                   - apply eval_Evar_global; eauto.
                     rewrite PTree.gempty; auto.
                   - apply deref_loc_reference; auto.
                 }
                * unfold Genv.find_funct. auto.
                * assert (c_name c_main = main_node) as <-
                      by now eapply find_class_name; eauto.
                  assert (m_step.(m_name) = step) as Hstep
                      by now eapply find_method_name; eauto.
                  simpl; unfold type_of_function;
                    rewrite Hp_stp, Hr_stp, Hcc_stp; simpl; repeat f_equal.
                  clear.
                  induction (m_in m_step) as [|(x, t)]; simpl; auto.
                  rewrite IHl; auto.
              + destruct_list (outs n); contr.
                simpl; rewrite PTree.gss; auto.
            - eexists; split; auto;
                eapply exec_Scall; simpl; eauto; simpl.
              + eapply eval_Elvalue.
                *{ apply eval_Evar_global; eauto.
                   rewrite <-not_Some_is_None.
                   intros (b, t') Hget.
                   subst e1.
                   rewrite PTree.gso, PTree.gempty in Hget.
                   - discriminate.
                   - intro E; apply prefix_injective in E.
                     + destruct E as [E].
                       contradict E; apply fun_not_out.
                     + apply fun_id_valid.
                     + apply out_valid.
                 }
                * apply deref_loc_reference; auto.
              + unfold Genv.find_funct. auto.
              + assert (c_name c_main = main_node) as <-
                    by now eapply find_class_name; eauto.
                assert (m_step.(m_name) = step) as <-
                    by now eapply find_method_name; eauto.
                simpl; unfold type_of_function;
                  rewrite Hp_stp, Hr_stp, Hcc_stp; simpl; repeat f_equal.
                clear.
                induction (m_in m_step) as [|(x, t)]; simpl; auto.
                rewrite IHl; auto.
          }
          eexists le2, meSn; split; auto.
          repeat eapply exec_Sseq_1; eauto.
          eapply exec_write; eauto.
          destruct_list m_step.(m_out) as (?, ?) ? ?; destruct_list (outs n);
            contr; eauto.
          apply sep_pure; split; auto.
          rewrite sepemp_left; auto.
        Qed.

        Definition transl_trace (n: nat): traceinf' :=
          trace_step m_step ins outs Step_in_spec Step_out_spec Hwt_ins Hwt_outs n.

        Lemma dostep_loop:
          forall n meInit le me,
            wt_mem meInit prog_main c_main ->
            dostep n me ->
            execinf_stmt (globalenv tprog) (function_entry2 (globalenv tprog)) e1 le me
                         (main_loop false main_node m_step)
                         (traceinf_of_traceinf' (transl_trace n)).
        Proof.
          cofix COINDHYP.
          intros ????? Hdostep.
          destruct exec_body with (1:=Hdostep) (le:=le) as (? & ? & ? & ?).
          unfold transl_trace, trace_step; rewrite unfold_mk_trace.
          eapply execinf_Sloop_loop with (out1 := Out_normal);
            eauto using out_normal_or_continue, exec_stmt.
        Qed.

        Lemma exec_reset:
          exists m2,
            exec_stmt (globalenv tprog) (function_entry2 (globalenv tprog)) e1
                      le_main m1 (reset_call (c_name c_main)) E0
                      le_main m2 Out_normal
            /\ dostep 0 m2.
        Proof.
          pose proof methods_corres as MC.
          destruct dostep_imp as (m2 & Heval & Step); auto.
          change (eval_funcall tge (function_entry2 tge) m0 (Internal reset_f)
                               [var_ptr sb] E0 m2 Vundef)
            with (eval_funcall (globalenv tprog) (function_entry2 (globalenv tprog)) m0 (Internal reset_f)
                               [var_ptr sb] E0 m2 Vundef) in Heval.
          pose proof (find_class_name _ _ _ _ Find) as Eq;
            pose proof (find_method_name _ _ _ Findreset) as Eq';
            rewrite <-Eq, <-Eq' in *.
          edestruct MC with (2:=Findreset)
            as (ptr & f & Get_s & Get_f & Hp_rst & Hr_rst & Hcc_rst
                & ? & ? & ? & ? & ? & Htr_rst); eauto.
          rewrite Getreset_s in Get_s; inversion Get_s; subst ptr;
            rewrite Getreset_f in Get_f; inversion Get_f; subst f.
          exists m2; split; auto.
          unfold reset_call.
          rewrite <-Eq'.
          change le_main with (set_opttemp None Vundef le_main) at 2.
          econstructor; simpl; eauto.
          - eapply eval_Elvalue.
            + apply eval_Evar_global; eauto.
              rewrite <-not_Some_is_None.
              intros (b, t) Hget.
              subst e1.
              destruct_list m_step.(m_out).
              * rewrite PTree.gempty in Hget; discriminate.
              * rewrite PTree.gempty in Hget; discriminate.
              *{ rewrite PTree.gso, PTree.gempty in Hget.
                 - discriminate.
                 - intro E; apply prefix_injective in E.
                   + destruct E as [E].
                     contradict E; apply fun_not_out.
                   + apply fun_id_valid.
                   + apply out_valid.
               }
            + apply deref_loc_reference; auto.
          - apply find_method_In in Findreset.
            do 2 (econstructor; eauto).
            apply eval_Evar_global; auto.
            rewrite <-not_Some_is_None.
            intros (b, t) Hget.
            subst e1.
            destruct_list m_step.(m_out).
            + rewrite PTree.gempty in Hget; discriminate.
            + rewrite PTree.gempty in Hget; discriminate.
            + rewrite PTree.gso, PTree.gempty in Hget.
              * discriminate.
              *{ intro E; apply (glob_id_not_prefixed self).
                 - apply self_valid.
                 - rewrite E; constructor.
               }
          - unfold Genv.find_funct. auto.
          - simpl; unfold type_of_function;
              rewrite Hp_rst, Hr_rst, Hcc_rst; simpl; repeat f_equal.
            + rewrite Reset_in_spec; auto.
              rewrite Reset_out_spec; auto.
            + rewrite Reset_out_spec; auto.
        Qed.

        Lemma main_inf:
          evalinf_funcall (globalenv tprog) (function_entry2 (globalenv tprog)) m0
                          (Internal main_f) [] (traceinf_of_traceinf' (transl_trace 0)).
        Proof.
          pose proof exec_reset as ER. pose proof entry_main as EM.
          pose proof dostep_loop as DSL.
          pose proof (find_class_name _ _ _ _ Find) as Eq;
            pose proof (find_method_name _ _ _ Findreset) as Eq';
            rewrite <-Eq, <-Eq' in *.
          destruct Caractmain as (? & ? & ? & ? & ? & Hbody).
          destruct ER as (? & ? & ?); auto.
          econstructor; eauto.
          rewrite <-E0_left_inf, Hbody.
          eapply execinf_Sseq_1, execinf_Sseq_2; eauto.
        Qed.

        Let after_loop := Kseq (Sreturn (Some cl_zero)) Kstop.

        Lemma reactive_loop:
          forall n m le,
            dostep n m ->
            Smallstep.forever_reactive (step_fe function_entry2) (globalenv tprog)
                                       (Clight.State main_f (main_loop false main_node m_step) after_loop e1 le m)
                                       (traceinf_of_traceinf' (transl_trace n)).
        Proof.
          unfold transl_trace, trace_step.
          cofix COINDHYP.
          intros * Hdostep'.
          edestruct exec_body with (1:=Hdostep') as (? & ? & Exec_body & ?).
          eapply exec_stmt_steps in Exec_body.
          destruct Exec_body as (? & Star_body & Out_body).
          unfold main_loop_body in Star_body.
          rewrite unfold_mk_trace.

          econstructor; simpl.

          (* eapply Smallstep.star_forever_reactive. *)
          - eapply Smallstep.star_step.
            + eapply step_loop.
            + eapply Smallstep.star_right with (t2:=E0); auto.
              *{ eapply Smallstep.star_right with (t2:=E0); auto.
                 - eapply Star_body.
                 - inversion_clear Out_body.
                   apply step_skip_or_continue_loop1; auto.
               }
              * apply step_skip_loop2.
            + simpl; rewrite 2 E0_right; auto.
          - intro Evts.
            apply app_eq_nil in Evts; destruct Evts.
            apply (load_events_not_E0 ins (m_in m_step) Step_in_spec Hwt_ins n); auto.
          - apply COINDHYP; auto.
        Qed.

        Lemma reacts:
          program_behaves (semantics2 tprog) (Reacts (traceinf_of_traceinf' (transl_trace 0))).
        Proof.
          pose proof entry_main as EM.
          destruct Caractmain as (Hret & Hcc & Hparams & ? & ? & Hbody).

          destruct exec_reset as (? & Exec_reset & ?).
          eapply exec_stmt_steps in Exec_reset.
          destruct Exec_reset as (? & Star_reset & Out_reset).

          pose proof reactive_loop as RL.
          pose proof (find_class_name _ _ _ _ Find) as Eq;
            pose proof (find_method_name _ _ _ Findreset) as Eq';
            rewrite <-Eq, <-Eq' in *.
          econstructor.
          - econstructor; eauto.
            simpl; unfold type_of_function; auto.
            rewrite Hparams, Hret, Hcc; auto.
          -
            econstructor.
            rewrite <-E0_left_inf.
            eapply Smallstep.star_forever_reactive.
            + eapply Smallstep.star_step with (t1:=E0) (t2:=E0); auto.
              * eapply step_internal_function. eapply EM.
              *{ eapply Smallstep.star_step with (t1:=E0) (t2:=E0); auto.
                 - rewrite Hbody.
                   apply step_seq.
                 - eapply Smallstep.star_step with (t1:=E0) (t2:=E0); auto.
                   + apply step_seq.
                   + eapply Smallstep.star_right with (t1:=E0) (t2:=E0); auto.
                     * eapply Star_reset.
                     * inversion_clear Out_reset.
                       apply step_skip_seq.
               }
            + apply RL with (le:=le_main) in H1.
              unfold after_loop, step_fe in H1. auto.
        Qed.

      End dostep.

    End Init.

    Theorem reacts':
      forall me0 ins outs c_main prog_main m_step m_reset,
        stmt_call_eval prog mempty (c_name c_main) (m_name m_reset) [] me0 [] ->
        wt_mem me0 prog_main c_main ->
        loop_call prog (c_name c_main) step (fun n => map Some (ins n)) (fun n => map Some (outs n)) 0 me0 ->
        find_class main_node prog = Some (c_main, prog_main) ->
        find_method reset (c_methods c_main) = Some m_reset ->
        find_method step (c_methods c_main) = Some m_step ->
        m_in m_reset = [] ->
        m_out m_reset = [] ->
        forall (Step_in_spec: m_in m_step <> []) (Step_out_spec: m_out m_step <> [])
          (Hwt_in: forall n : nat, wt_vals (ins n) (m_in m_step))
          (Hwt_out: forall n : nat, wt_vals (outs n) (m_out m_step)),
          program_behaves (semantics2 tprog)
                          (Reacts
                             (traceinf_of_traceinf'
                                (transl_trace m_step Step_in_spec Step_out_spec ins outs Hwt_in Hwt_out 0))).
    Proof.
      intros until m_reset; intros ? ? ? Findmain Findreset Findstep.
      destruct init_mem as (m0 & sb & Initmem & find_step & Hrep).
      edestruct (find_main m0 _ Hrep) as
          (c_main' & prog_main' & m_reset' & m_step' & Findmain' & Findreset' & Findstep' & ? & ? &
           ? & ? & ? & ? & ? & ? & ? & Hvars & ?  & Hbody & Hmout).
      rewrite Findmain' in Findmain; inv Findmain; subst.
      rewrite Findreset' in Findreset; rewrite Findstep' in Findstep; inv Findreset; inv Findstep; subst.
      edestruct methods_corres with (2:=Findreset')
        as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
      edestruct methods_corres with (2:=Findstep')
        as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
      intros.
      case_eq (m_out m_step).
      - intros Out; rewrite Out in *.
        eapply reacts with (m_reset:=m_reset) (m_step:=m_step);
          try rewrite Out; eauto.
        + repeat split; auto.
        + rewrite Hvars; econstructor.
        + erewrite <-sepemp_left, <-sepemp_right; eauto.
      - intros (x', t') xs Out.
        destruct xs; rewrite Out in *.
        + eapply reacts with (m_reset:=m_reset) (m_step:=m_step);
            try rewrite Out; eauto.
          * repeat split; auto.
          * rewrite Hvars; econstructor.
          * erewrite <-sepemp_left, <-sepemp_right; eauto.
        + destruct Hmout as (? & ? & ? & ? & ? & ?).
          eapply reacts; eauto; try rewrite Out; eauto.
          * repeat split; try rewrite Out; auto.
          * erewrite sep_swap, <-sepemp_right; eauto.

            Grab Existential Variables.
            exact empty_co.
            eauto.
            exact empty_co.
            eauto.
    Qed.

    End CORRECTNESS.

End PRESERVATION.
