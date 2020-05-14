From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common Ident.
From Velus Require Import Operators.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.
From Velus Require Import Lustre.Normalization.Specification.

(** * Normalization of a full norm *)

Local Set Warnings "-masking-absolute-name".
Module Type FULLNORM
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op).

  Module Export Norm := NormalizationFun Ids Op OpAux Syn.
  Module Export Spec := SpecificationFun Ids Op OpAux Syn Norm.

  Import Fresh Fresh.Fresh Facts Tactics.

  Definition normalize_equations' (to_cut : PS.t) (eq : list equation) (st : fresh_st ((type * clock) * bool)) :
    { res | normalize_equations to_cut eq st = res }.
  Proof.
    remember (normalize_equations to_cut eq st) as eqs'.
    econstructor; eauto.
  Defined.

  Definition first_unused_ident (vs : list ident) : ident :=
    ((fold_left Pos.max vs xH) + 100)%positive.

  Fact first_unused_ident_gt : forall vs id,
      first_unused_ident vs = id ->
      Forall (fun id' => (id' < id)%positive) vs.
  Proof.
    intros n id Hfirst.
    subst. unfold first_unused_ident.
    rewrite Forall_forall; intros x Hin.
    eapply Pos.le_lt_trans. 2: apply Pos.lt_add_r.
    apply max_fold_in; auto.
  Qed.

  Program Definition normalize_node (to_cut : PS.t) (n : node) (G : { G | wl_node G n}) : node :=
    let anon := anon_in_eqs (n_eqs n) in
    let id0 := first_unused_ident (reserved++List.map fst (n_in n++n_vars n++n_out n++anon)) in
    let eqs := normalize_equations' (PS.union to_cut (ps_from_list (map fst (n_out n)))) (n_eqs n) (init_st id0) in
    let nvars := (idty (st_anns (snd (proj1_sig eqs)))) in
    {| n_name := (n_name n);
       n_hasstate := (n_hasstate n);
       n_in := (n_in n);
       n_out := (n_out n);
       n_vars := (n_vars n)++nvars;
       n_eqs := fst (proj1_sig eqs);
       n_ingt0 := (n_ingt0 n);
       n_outgt0 := (n_outgt0 n);
    |}.
  Next Obligation.
    remember (first_unused_ident _) as id0.
    eapply normalize_equations_vars_perm with (st:=init_st id0) in H. 2: eapply surjective_pairing.
    specialize (n_defd n) as Hperm'.
    unfold st_ids, idty in *. rewrite init_st_anns in H. rewrite app_nil_r in H.
    etransitivity. apply H.
    rewrite Permutation_app_comm. symmetry.
    rewrite <- app_assoc. rewrite Permutation_swap.
    repeat rewrite map_app in *. rewrite map_map in *.
    rewrite Hperm'. reflexivity.
  Qed.
  Next Obligation.
    remember (first_unused_ident _) as id0.
    specialize (first_unused_ident_gt _ id0 (eq_sym Heqid0)) as Hident.
    remember (normalize_equations _ (n_eqs n) (init_st id0)) as res.
    assert (st_valid_reuse (snd res) (PSP.of_list (map fst (n_in n ++ n_vars n ++ n_out n)))
                           PS.empty) as Hvalid.
    { specialize (n_nodup n) as Hndup. rewrite fst_NoDupMembers in Hndup.
      repeat rewrite map_app in Hndup.
      subst. eapply normalize_equations_st_valid.
      2: eapply surjective_pairing.
      2: eapply init_st_valid_reuse.
      + rewrite PSP.elements_empty, app_nil_r.
        repeat ndup_r Hndup.
      + replace (ps_adds _ PS.empty) with (ps_from_list (map fst (anon_in_eqs (n_eqs n)))); auto.
        rewrite ps_from_list_ps_of_list.
        repeat rewrite ps_of_list_ps_to_list_Perm; repeat rewrite map_app; repeat rewrite <- app_assoc in *; auto.
        repeat ndup_r Hndup.
        repeat rewrite app_assoc in Hndup. apply NoDup_app_l in Hndup.
        repeat rewrite <- app_assoc in Hndup; auto.
      + rewrite <- ps_from_list_ps_of_list. rewrite PS_For_all_Forall'.
        eapply Forall_incl; eauto.
        repeat rewrite map_app.
        repeat apply incl_tl.
        repeat rewrite app_assoc. apply incl_appl. reflexivity.
      + replace (ps_adds _ PS.empty) with (ps_from_list (map fst (anon_in_eqs (n_eqs n)))); auto.
        rewrite PS_For_all_Forall'.
        eapply Forall_incl; eauto.
        repeat rewrite map_app.
        repeat apply incl_tl.
        repeat apply incl_appr. reflexivity. }
    destruct res as [eqs st']. simpl in *.
    apply st_valid_reuse_st_valid in Hvalid. apply st_valid_NoDup in Hvalid.
    specialize (n_nodup n) as Hndup.
    rewrite ps_of_list_ps_to_list_Perm in Hvalid.
    - rewrite fst_NoDupMembers.
      repeat rewrite map_app in *.
      unfold idty, st_ids in *; rewrite map_map; simpl.
      rewrite <- app_assoc, app_assoc, Permutation_swap, <- app_assoc.
      assert (anon_in_eqs eqs = []).
      { symmetry in Heqres. eapply normalize_equations_no_anon in Heqres; eauto.
        2: apply PSP.union_subset_2.
        eapply st_valid_weak_valid. apply init_st_valid.
        rewrite PS_For_all_Forall. rewrite ps_from_list_ps_of_list.
        rewrite ps_of_list_ps_to_list_Perm.
        + eapply Forall_incl; eauto.
          repeat eapply incl_tl. eapply incl_appr. eapply incl_appr.
          eapply incl_appl. reflexivity.
        + repeat ndup_r Hvalid. }
      rewrite H0; simpl. rewrite app_nil_r. assumption.
    - rewrite <- fst_NoDupMembers.
      repeat rewrite app_assoc in *.
      apply NoDupMembers_app_l in Hndup; auto.
  Qed.
  Admit Obligations.

  Fixpoint normalize_global (G : global) (Hwl: wl_global G) : global.
  Proof.
    destruct G as [|hd tl].
    - exact [].
    - refine ((normalize_node PS.empty hd _)::(normalize_global tl _)).
      + econstructor. inv Hwl; eauto.
      + inv Hwl; eauto.
  Defined.

  (** ** After normalization, a node is normalized *)

  Lemma normalize_node_normalized_node : forall n to_cut Hwl,
      normalized_node (normalize_node to_cut n Hwl).
  Proof.
    intros n to_cut [G Hwl].
    unfold normalize_node.
    unfold normalized_node; simpl.
    eapply normalize_equations_normalized_eq; eauto.
    2: apply surjective_pairing.
    - apply st_valid_weak_valid.
      apply init_st_valid.
      rewrite PS_For_all_Forall'.
      remember (first_unused_ident _) as id0. symmetry in Heqid0.
      apply first_unused_ident_gt in Heqid0.
      eapply Forall_incl; eauto.
      repeat rewrite map_app.
      repeat apply incl_tl. apply incl_appr. apply incl_appr.
      apply incl_appl. reflexivity.
    - apply PSP.union_subset_2.
  Qed.

  Lemma normalize_global_normalized_global : forall G Hwl,
      normalized_global (normalize_global G Hwl).
  Proof.
    induction G; intros Hwl; simpl; constructor.
    - apply normalize_node_normalized_node.
    - apply IHG.
  Qed.

End FULLNORM.

Module FullNormFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       <: FULLNORM Ids Op OpAux Syn.
  Include FULLNORM Ids Op OpAux Syn.
End FullNormFun.
