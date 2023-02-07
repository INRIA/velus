From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Permutation.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.

Module Type COMPLETE
  (Import Ids : IDS)
  (Import Op : OPERATORS)
  (OpAux : OPERATORS_AUX Ids Op)
  (Import Cks : CLOCKS Ids Op OpAux)
  (Import Senv : STATICENV Ids Op OpAux Cks)
  (Import Syn : LSYNTAX Ids Op OpAux Cks Senv).

  Section complete_branch.
    Context {A : Type}.

    Variable f_comp : A -> A.
    Variable add_equations : list equation -> A -> A.

    Variable must_def : PS.t.
    Variable is_def : PS.t.

    Definition complete_branch (env : Env.t type) (br : branch A) : branch A :=
      let 'Branch caus blks := br in
      let diff := PS.diff must_def is_def in
      let eqs := List.map (fun x => ([x], [Elast x (or_default OpAux.bool_velus_type (Env.find x env), Cbase)])) (PS.elements diff) in
      Branch caus (add_equations eqs (f_comp blks)).
  End complete_branch.

  Section complete_scope.
    Context {A : Type}.

    Variable f_comp : Env.t type -> A -> A.

    Definition complete_scope (env : Env.t type) (s : scope A) :=
      let 'Scope locs blks := s in
      let env' := Env.adds' (map_filter (fun '(x, (ty, ck, _, o)) => if isSome o then Some (x, ty) else None) locs) env in
      Scope locs (f_comp env' blks).
  End complete_scope.

  Fixpoint complete_block (env : Env.t type) (blk : block) :=
    match blk with
    | Beq eq => Beq eq
    | Breset blks er => Breset (map (complete_block env) blks) er
    | Blocal s => Blocal (complete_scope (fun env => map (complete_block env)) env s)
    | Bswitch e brs =>
        let must_def := vars_defined (Bswitch e brs) in
        Bswitch e
          (map (fun '(k, br) =>
                  let br' := complete_branch
                               (map (complete_block env))
                               (fun eqs blks => map Beq eqs++blks)
                               must_def
                               (vars_defined_branch (fun blks => PSUnion (map vars_defined blks)) br)
                               env br
                  in (k, br')) brs)
    | Bauto aut ck ini sts =>
        let must_def := vars_defined (Bauto aut ck ini sts) in
        Bauto aut ck ini
          (map (fun '(k, br) =>
                  let br' := complete_branch
                               (fun '(unl, s) => (unl, complete_scope (fun env '(blks, unt) => (map (complete_block env) blks, unt)) env s))
                               (fun eq '(unl, Scope locs (blks, unt)) => (unl, Scope locs (map Beq eq++blks, unt)))
                               must_def
                               (vars_defined_branch (fun '(_, blks) => vars_defined_scope (fun '(blks0, _) => PSUnion (map vars_defined blks0)) blks) br)
                               env br
             in (k, br')) sts)
    end.

  (** NoDupLocals *)

  Lemma complete_block_NoDupLocals : forall blk env xs,
      NoDupLocals xs blk ->
      NoDupLocals xs (complete_block env blk).
  Proof.
    induction blk using block_ind2; intros * ND; inv ND;
      constructor; simpl_Forall; eauto.
    all:repeat inv_branch; repeat inv_scope.
    - (* switch *)
      econstructor; eauto.
      apply Forall_app; split; simpl_Forall; eauto.
      constructor.
    - (* automaton *)
      repeat econstructor; eauto.
      apply Forall_app; split; simpl_Forall; eauto.
      constructor.
    - (* local *)
      econstructor; eauto. simpl_Forall; eauto.
  Qed.

  (** GoodLocals *)

  Lemma complete_block_GoodLocals : forall blk env xs,
      GoodLocals xs blk ->
      GoodLocals xs (complete_block env blk).
  Proof.
    induction blk using block_ind2; intros * ND; inv ND;
      constructor; simpl_Forall; eauto.
    all:repeat inv_branch; repeat inv_scope.
    - (* switch *)
      econstructor; eauto.
      apply Forall_app; split; simpl_Forall; eauto.
      constructor.
    - (* automaton *)
      repeat econstructor; eauto.
      apply Forall_app; split; simpl_Forall; eauto.
      constructor.
    - (* local *)
      econstructor; eauto. simpl_Forall; eauto.
  Qed.

  (** VarsDefined *)

  Lemma complete_scope_VarsDefined {A} P_nd P_vd1 (P_vd2: _ -> _ -> Prop) f_comp :
    forall locs (blks: A) env Γ,
      NoDupMembers Γ ->
      NoDupScope P_nd (map fst Γ) (Scope locs blks) ->
      VarsDefinedScope P_vd1 (Scope locs blks) Γ ->
      (forall env Γ,
          NoDupMembers Γ ->
          P_nd (map fst Γ) blks ->
          P_vd1 blks Γ ->
          P_vd2 (f_comp env blks) (map fst Γ)) ->
      VarsDefinedCompScope P_vd2 (complete_scope f_comp env (Scope locs blks)) (map fst Γ).
  Proof.
    intros * Nd1 Nd2 Vd Ind. repeat inv_scope.
    econstructor.
    rewrite <-map_fst_senv_of_decls, <-map_app.
    eapply Ind; eauto using NoDupScope_NoDupMembers.
    now rewrite map_app, map_fst_senv_of_decls.
  Qed.

  Opaque complete_scope.
  Lemma complete_block_VarsDefined : forall blk env Γ,
      NoDupMembers Γ ->
      NoDupLocals (map fst Γ) blk ->
      VarsDefined blk Γ ->
      VarsDefinedComp (complete_block env blk) (map fst Γ).
  Proof.
    induction blk using block_ind2; intros * ND1 ND VD;
      assert (ND':=ND); inv ND'; assert (VD':=VD); inv VD'; simpl.
    - (* equation *)
      rewrite H0. constructor.
    - (* reset *)
      rewrite concat_map. econstructor.
      simpl_Forall. eauto 6 using NoDupMembers_concat, NoDupLocals_incl, incl_map, incl_concat.
    - (* switch *)
      econstructor.
      1:{ intros * Nil. apply map_eq_nil in Nil. contradiction. }
      simpl_Forall. repeat inv_branch. econstructor; eauto.
      remember (PS.diff _ _) as diff.
      do 2 esplit. apply Forall2_app with (l1':=map (fun x => [x]) (PS.elements diff)) (l2':=map (map fst) x).
      + simpl_Forall. constructor.
      + simpl_Forall. eapply H; [| |eauto].
        * eapply NoDupMembers_concat; eauto.
          take (Permutation (concat x) _) and rewrite it. eapply NoDupMembers_app_l. take (Permutation _ Γ) and now rewrite it.
        * eapply NoDupLocals_incl; [|eauto]. apply incl_map. etransitivity; eauto using incl_concat.
          take (Permutation (concat x) _) and rewrite it. take (Permutation _ Γ) and rewrite <-it. solve_incl_app.
      + take (Permutation _ Γ) and rewrite <-it. take (Permutation _ ys') and rewrite <-it.
        rewrite map_app, concat_app, concat_map, Permutation_app_comm, concat_map_singl1.
        apply Permutation_app_head.
        apply NoDup_Permutation; auto using PS_elements_NoDup.
        * apply fst_NoDupMembers. eapply NoDupMembers_app_r. take (Permutation _ Γ) and now rewrite it.
        * intros ?. subst. rewrite In_PS_elements, PS.diff_spec, map_vars_defined_spec, <-fst_InMembers.
          setoid_rewrite vars_defined_spec with (blk:=Bswitch ec _).
          assert (InMembers x0 ysl <-> InMembers x0 Γ /\ ~InMembers x0 ys') as ->.
          { rewrite <-it0, InMembers_app.
            split; [intros ?|intros ([|]&?)]; auto. 2:contradiction.
            split; auto.
            eapply NoDupMembers_app_InMembers; [|eauto]. now rewrite Permutation_app_comm, it0. }
          rewrite <-it, VarsDefined_spec, Exists_VarsDefined_spec; eauto. reflexivity.
          simpl_Forall. rewrite it. eapply NoDupLocals_incl; [|eauto]. rewrite <-it0. solve_incl_app.
    - (* state machine *)
      econstructor.
      1:{ intros * Nil. apply map_eq_nil in Nil. contradiction. }
      simpl_Forall. repeat inv_branch. econstructor; eauto.
      remember (PS.diff _ _) as diff.
      destruct s. eapply complete_scope_VarsDefined
        with (P_vd2:=fun '(blks, _) ys => exists xs, Forall2 VarsDefinedComp blks xs /\ Permutation (concat xs) ys)
        (f_comp:=fun env0 '(blks, unt) => (map (complete_block env0) blks, unt))
             (env:=env) in H4 as VD'; eauto.
      2:{ take (Permutation _ _) and rewrite <-it in ND1; eauto using NoDupMembers_app_l. }
      2:{ eapply NoDupScope_incl; [| |eauto]. 2:take (Permutation _ _) and rewrite <-it; solve_incl_app.
          intros; simpl in *; simpl_Forall; eauto using NoDupLocals_incl. }
      2:{ intros * ND1' ND' VD'. destruct_conjs.
          do 2 esplit. 2:take (Permutation _ _) and now rewrite <-it, concat_map.
          simpl_Forall. take (Permutation _ _) and rewrite <-it in ND1', ND'.
          eapply H; eauto using NoDupMembers_concat, NoDupLocals_incl, incl_map, incl_concat. }
      1:{ destruct (complete_scope _ _ _) as [?(?&?)] eqn:Eq; simpl.
          Transparent complete_scope.
          assert (l2 = l1); subst.
          { destruct p. now inv Eq. } clear Eq.
          inv VD'. destruct_conjs. remember (PS.elements _ ) as xs.
          econstructor. do 2 esplit.
          - apply Forall2_app; eauto.
            instantiate (1:=map (fun x => [x]) xs). simpl_Forall. constructor.
          - subst. rewrite <-H1, map_app, concat_app, concat_map_singl1, H7, app_assoc.
            apply Permutation_app_tail. rewrite Permutation_app_comm. apply Permutation_app_head.
            apply NoDup_Permutation; auto using PS_elements_NoDup.
            + apply fst_NoDupMembers. eapply NoDupMembers_app_r. take (Permutation _ Γ) and now rewrite it.
            + intros ?. subst. rewrite In_PS_elements, PS.diff_spec, PS.filter_spec, map_vars_defined_spec, <-fst_InMembers, Bool.negb_true_iff.
              2:{ intros ?? Eq; now inv Eq. }
              setoid_rewrite vars_defined_spec with (blk:=Bauto type0 ck (l, e) _).
              assert (InMembers x0 ysl <-> InMembers x0 Γ /\ ~InMembers x0 ys') as ->.
              { rewrite <-H1, InMembers_app.
                split; [intros ?|intros ([|]&?)]; auto. 2:contradiction.
                split; auto.
                eapply NoDupMembers_app_InMembers; [|eauto]. now rewrite Permutation_app_comm, H1. }
              repeat inv_scope. destruct_conjs.
              rewrite mem_assoc_ident_false_iff, <-VarsDefined_spec, <-Exists_VarsDefined_spec; eauto.
              2:{ simpl_Forall. eapply NoDupLocals_incl; [|eauto].
                  take (Permutation (concat x1) _) and rewrite it, map_app, map_fst_senv_of_decls.
                  take (Permutation _ Γ) and rewrite <-it. solve_incl_app. }
              take (Permutation (concat x1) _) and rewrite it, InMembers_app, InMembers_senv_of_decls.
              split; intros (?&contra); split; auto; contradict contra.
              * split; auto. intros In'.
                eapply H17; eauto. now apply fst_InMembers.
              * destruct contra as ([|]&?); auto. contradiction.
      }
    - (* local *)
      econstructor.
      eapply complete_scope_VarsDefined; eauto.
      intros * ND1' ND' VD'. destruct_conjs.
      take (Permutation _ _) and setoid_rewrite <-it.
      do 2 esplit; [|now rewrite concat_map].
      simpl_Forall. rewrite <-it in ND1', ND'.
      eapply H; eauto using NoDupMembers_concat, NoDupLocals_incl, incl_map, incl_concat.
  Qed.
  Transparent complete_scope.

  Program Definition complete_node (n : @node (fun _ _ => True) elab_prefs) : @node complete elab_prefs :=
    let env := Env.from_list
                 (map_filter
                    (fun xtc => if isSome (snd (snd xtc))
                             then Some (fst xtc, fst (fst (fst (snd xtc))))
                             else None) (n_out n)) in
    {|
      n_name := n_name n;
      n_hasstate := n_hasstate n;
      n_in := n_in n;
      n_out := n_out n;
      n_block := complete_block env (n_block n);
      n_ingt0 := n_ingt0 n;
      n_outgt0 := n_outgt0 n;
    |}.
  Next Obligation.
    pose proof (n_nodup n) as (Nd1&Nd2).
    pose proof (n_defd n) as (?&Vars&Perm).
    do 2 esplit; [|eauto].
    eapply VarsDefinedComp_VarsDefined, complete_block_VarsDefined; eauto.
    eapply complete_block_NoDupLocals.
    all:rewrite Perm; try rewrite fst_NoDupMembers; rewrite map_fst_senv_of_decls.
    1,3:eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
    eauto using NoDup_app_r.
  Qed.
  Next Obligation.
    pose proof (n_nodup n) as (Nd1&Nd2).
    split; eauto using complete_block_NoDupLocals.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Good1&Good2&Good3).
    repeat split; eauto using complete_block_GoodLocals.
  Qed.
  Next Obligation.
    pose proof (n_nodup n) as (Nd1&Nd2).
    pose proof (n_defd n) as (?&Defs&Perm).
    econstructor. 2:now rewrite <-map_fst_senv_of_decls, <-Perm.
    eapply complete_block_VarsDefined; eauto.
    all:rewrite Perm; try rewrite fst_NoDupMembers; rewrite map_fst_senv_of_decls.
    eauto using NoDup_app_r.
    eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
  Qed.

  Global Program Instance complete_node_transform_unit: TransformUnit (@node (fun _ _ => True) elab_prefs) (@node complete elab_prefs) :=
    { transform_unit := complete_node }.

  Global Program Instance complete_global_without_units : TransformProgramWithoutUnits (@global (fun _ _ => True) elab_prefs) (@global complete elab_prefs) :=
    { transform_program_without_units := fun g => Global g.(types) g.(externs) [] }.

  Definition complete_global : @global (fun _ _ => True) elab_prefs -> @global complete elab_prefs :=
    transform_units.

  (** *** Equality of interfaces *)

  Lemma complete_global_iface_eq : forall G,
      global_iface_eq G (complete_global G).
  Proof.
    repeat split; auto.
    intros f. unfold find_node.
    destruct (find_unit f G) as [(?&?)|] eqn:Hfind; simpl.
    - setoid_rewrite find_unit_transform_units_forward; eauto.
      simpl. repeat constructor.
    - destruct (find_unit f (complete_global G)) as [(?&?)|] eqn:Hfind'; simpl; try constructor.
      eapply find_unit_transform_units_backward in Hfind' as (?&?&?&?); congruence.
  Qed.

End COMPLETE.

Module CompleteFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       <: COMPLETE Ids Op OpAux Cks Senv Syn.
  Include COMPLETE Ids Op OpAux Cks Senv Syn.
End CompleteFun.
