From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import Omega.
Require Import ProofIrrelevance.

From Velus Require Import Common Ident.
From Velus Require Import Operators.
From Velus Require Import Lustre.LSyntax Lustre.LCausality.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

(** * Idempotence of the normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type IDEMPOTENCE
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Cau : LCAUSALITY Ids Op Syn)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn Cau).

  Import Fresh Fresh.Fresh Facts Tactics.

  (** ** Idempotence of untupling *)

  Fact normalized_lexp_normalize_idem : forall e is_control st,
      normalized_lexp e ->
      unnest_exp is_control e st = ([e], [], st).
  Proof with eauto.
    intros e is_control st Hnormed; revert is_control.
    induction Hnormed; intro is_control; repeat inv_bind...
    - (* unop *)
      repeat eexists...
      inv_bind...
    - (* binop *)
      repeat eexists...
      inv_bind. repeat eexists...
      inv_bind...
    - (* when *)
      exists [e]. exists []. exists st.
      repeat split; inv_bind...
      exists [[e]]. exists [[]]. exists st.
      repeat split; simpl; inv_bind...
      repeat eexists...
      inv_bind.
      repeat eexists; inv_bind...
  Qed.

  Corollary normalized_lexps_normalize_idem' : forall es is_control st,
      Forall normalized_lexp es ->
      (exists eqs, map_bind2 (unnest_exp is_control) es st = (List.map (fun e => [e]) es, eqs, st) /\ (concat eqs = [])).
  Proof with eauto.
    induction es; intros is_control st Hf;
      inv Hf; repeat inv_bind...
    eapply normalized_lexp_normalize_idem in H1...
    eapply (IHes is_control st) in H2; clear IHes.
    destruct H2 as [eqs [H2 Heqs]].
    exists ([]::eqs).
    repeat eexists... inv_bind.
    repeat eexists... inv_bind.
    repeat eexists... inv_bind.
    repeat f_equal.
  Qed.

  Corollary normalized_lexps_normalize_idem : forall es st,
      Forall normalized_lexp es ->
      unnest_exps es st = (es, [], st).
  Proof with eauto.
    intros.
    eapply normalized_lexps_normalize_idem' in H. destruct H as [eqs [H Heqs]].
    unfold unnest_exps; inv_bind.
    repeat eexists...
    inv_bind. rewrite concat_map_singl1. congruence.
  Qed.

  Fact normalized_cexp_normalize_idem : forall e st,
      normalized_cexp e ->
      unnest_exp true e st = ([e], [], st).
  Proof with eauto.
    intros e st Hnormed.
    induction Hnormed; repeat inv_bind...
    - (* merge *)
      exists [et]. exists []. exists st.
      repeat split; inv_bind...
      + exists [[et]]. exists [[]]. exists st.
        repeat split; simpl; inv_bind...
        repeat eexists...
        inv_bind.
        repeat eexists; inv_bind...
      + exists [ef]. exists []. exists st.
        repeat split; simpl; inv_bind...
        exists [[ef]]. exists [[]]. exists st.
        repeat split; simpl; inv_bind...
        repeat eexists...
        inv_bind.
        repeat eexists; inv_bind...
    - (* ite *)
      eapply normalized_lexp_normalize_idem in H. repeat eexists...
      repeat inv_bind.
      exists [et]. exists []. exists st.
      repeat split; inv_bind...
      + exists [[et]]. exists [[]]. exists st.
        repeat split; simpl; inv_bind...
        repeat eexists...
        inv_bind.
        repeat eexists; inv_bind...
      + exists [ef]. exists []. exists st.
        repeat split; simpl; inv_bind...
        exists [[ef]]. exists [[]]. exists st.
        repeat split; simpl; inv_bind...
        repeat eexists...
        inv_bind.
        repeat eexists; inv_bind...
    - (* lexp *) eapply normalized_lexp_normalize_idem...
  Qed.

  Fact unnested_rhs_normalize_idem : forall e st,
      unnested_rhs e ->
      unnest_rhs e st = ([e], [], st).
  Proof with eauto.
    intros * Hnormed.
    destruct e; inv Hnormed; unfold unnest_rhs;
      try (solve [eapply normalized_cexp_normalize_idem; eauto]);
      try (solve [inv H; inv H0]).
    - (* fby *)
      repeat inv_bind.
      exists [e0]. exists []. exists st.
      split; unfold unnest_exps; inv_bind.
      + exists [[e0]]. exists [[]]. exists st. split; simpl; inv_bind...
        exists [e0]. exists []. exists st. split; simpl.
        eapply normalized_lexp_normalize_idem in H1...
        inv_bind.
        exists []. exists []. exists st.
        repeat split; inv_bind...
      + exists [e]. exists []. exists st. split; simpl; inv_bind...
        * exists [[e]]. exists [[]]. exists st. split; simpl; inv_bind...
          exists [e]. exists []. exists st. split; simpl.
          eapply normalized_lexp_normalize_idem in H3...
          inv_bind; repeat eexists...
          1,2:inv_bind...
    - (* arrow *)
      repeat inv_bind.
      exists [e0]. exists []. exists st.
      split; unfold unnest_exps; inv_bind.
      + exists [[e0]]. exists [[]]. exists st. split; simpl; inv_bind...
        exists [e0]. exists []. exists st. split; simpl.
        eapply normalized_lexp_normalize_idem in H1...
        inv_bind.
        exists []. exists []. exists st.
        split; inv_bind...
      + exists [e]. exists []. exists st. split; simpl; inv_bind...
        * exists [[e]]. exists [[]]. exists st. split; simpl; inv_bind...
          exists [e]. exists []. exists st. split; simpl.
          eapply normalized_lexp_normalize_idem in H3...
          inv_bind; repeat eexists...
          1,2:inv_bind...
    - (* app *)
      repeat inv_bind.
      eapply normalized_lexps_normalize_idem in H0.
      repeat eexists... repeat inv_bind.
      repeat eexists...
      inv_bind...
    - (* app (reset) *)
      repeat inv_bind.
      eapply normalized_lexps_normalize_idem in H0.
      repeat eexists; eauto.
      repeat inv_bind.
      repeat eexists; inv_bind; eauto.
      repeat eexists; [inv_bind|]; eauto.
      simpl; inv_bind; eauto.
  Qed.

  Corollary unnested_rhss_normalize_idem' : forall es st,
      Forall unnested_rhs es ->
      (exists eqs, map_bind2 unnest_rhs es st = (List.map (fun e => [e]) es, eqs, st) /\ (concat eqs = [])).
  Proof with eauto.
    induction es; intros st Hf;
      inv Hf; repeat inv_bind...
    eapply unnested_rhs_normalize_idem in H1...
    eapply (IHes st) in H2; clear IHes.
    destruct H2 as [eqs [H2 Heqs]].
    exists ([]::eqs).
    repeat (repeat eexists; eauto; inv_bind).
  Qed.

  Corollary unnested_rhss_normalize_idem : forall es st,
      Forall unnested_rhs es ->
      unnest_rhss es st = (es, [], st).
  Proof with eauto.
    intros.
    eapply unnested_rhss_normalize_idem' in H. destruct H as [eqs [H Heqs]].
    unfold unnest_rhss; inv_bind.
    repeat eexists...
    inv_bind. rewrite concat_map_singl1. congruence.
  Qed.

  Fact unnested_equation_unnest_idem : forall G eq st,
      wl_equation G eq ->
      unnested_equation eq ->
      unnest_equation eq st = ([eq], st).
  Proof with eauto.
    intros G [xs es] st Hwl Hnormed. inv Hwl.
    specialize (unnested_equation_unnested_rhs _ _ Hnormed) as Hnormed2.
    apply unnested_rhss_normalize_idem with (st:=st) in Hnormed2.
    inv Hnormed; repeat inv_bind;
      repeat eexists; eauto;
        inv_bind; try rewrite app_nil_r in *;
          simpl in *; repeat f_equal.
    - apply firstn_all2. rewrite H0. apply le_refl.
    - apply firstn_all2. rewrite H0. apply le_refl.
    - rewrite length_annot_numstreams in H0.
      apply firstn_all2. simpl. rewrite H0. apply le_refl.
  Qed.

  Corollary unnested_equations_unnest_idem : forall G eqs st,
      Forall (wl_equation G) eqs ->
      Forall unnested_equation eqs ->
      unnest_equations eqs st = (eqs, st).
  Proof with eauto.
    induction eqs; intros * Hwl Hnormed; inv Hwl; inv Hnormed;
      unfold unnest_equations; repeat inv_bind...
    - exists []. exists st. repeat split; inv_bind; auto.
    - eapply unnested_equation_unnest_idem in H3...
      eapply IHeqs with (st:=st) in H2... unfold unnest_equations in H2; repeat inv_bind.
      exists ([a]::x). exists st. inv_bind.
      split; auto.
      inv_bind. repeat eexists...
      inv_bind. repeat eexists...
      inv_bind...
  Qed.

  Definition transport1 {n1 n2 : node} (Hin : n_in n1 = n_in n2) : 0 < length (n_in n1) -> 0 < length (n_in n2).
  Proof. intros. induction Hin. auto. Defined.

  Definition transport2 {n1 n2 : node} (Hout : n_out n1 = n_out n2) : 0 < length (n_out n1) -> 0 < length (n_out n2).
  Proof. intros. induction Hout. auto. Defined.

  Definition transport3 {n1 n2 : node}
             (Heqs : n_eqs n1 = n_eqs n2)
             (Hvars : n_vars n1 = n_vars n2)
             (Hout : n_out n1 = n_out n2) :
    Permutation (vars_defined (n_eqs n1)) (map fst ((n_vars n1) ++ (n_out n1))) ->
    Permutation (vars_defined (n_eqs n2)) (map fst ((n_vars n2) ++ (n_out n2))).
  Proof.
    intros.
    induction Heqs. induction Hvars. induction Hout.
    auto.
  Defined.

  Definition transport4 {n1 n2 : node}
             (Hin : n_in n1 = n_in n2)
             (Hvars : n_vars n1 = n_vars n2)
             (Hout : n_out n1 = n_out n2)
             (Heqs : n_eqs n1 = n_eqs n2):
    NoDupMembers (n_in n1 ++ n_vars n1 ++ n_out n1 ++ anon_in_eqs (n_eqs n1)) ->
    NoDupMembers (n_in n2 ++ n_vars n2 ++ n_out n2 ++ anon_in_eqs (n_eqs n2)).
  Proof.
    intros.
    induction Hin. induction Hvars. induction Hout. induction Heqs.
    auto.
  Defined.

  Definition transport5 {n1 n2 : node}
             (Hname : n_name n1 = n_name n2)
             (Hin : n_in n1 = n_in n2)
             (Hvars : n_vars n1 = n_vars n2)
             (Hout : n_out n1 = n_out n2) :
    Forall ValidId (n_in n1 ++ n_vars n1 ++ n_out n1) /\ valid (n_name n1) ->
    Forall ValidId (n_in n2 ++ n_vars n2 ++ n_out n2) /\ valid (n_name n2).
  Proof.
    intros.
    induction Hname. induction Hin. induction Hvars. induction Hout.
    auto.
  Defined.

  Fact equal_node (n1 n2 : node)
    (Hname : n_name n1 = n_name n2)
    (Hstate : n_hasstate n1 = n_hasstate n2)
    (Hin : n_in n1 = n_in n2)
    (Hout : n_out n1 = n_out n2)
    (Hvars : n_vars n1 = n_vars n2)
    (Heqs : n_eqs n1 = n_eqs n2) :
    (transport1 Hin (n_ingt0 n1) = n_ingt0 n2) ->
    (transport2 Hout (n_outgt0 n1) = n_outgt0 n2) ->
    (transport3 Heqs Hvars Hout (n_defd n1) = n_defd n2) ->
    (transport4 Hin Hvars Hout Heqs (n_nodup n1) = n_nodup n2) ->
    (transport5 Hname Hin Hvars Hout (n_good n1) = n_good n2) ->
    n1 = n2.
  Proof.
    intros Heq1 Heq2 Heq3 Heq4 Heq5.
    destruct n1. destruct n2.
    simpl in *.
    destruct Hname. destruct Hstate.
    destruct Hin. destruct Hout. destruct Hvars.
    destruct Heqs.
    simpl in *; subst.
    reflexivity.
  Qed.

  Lemma unnested_node_unnest_idem : forall n Hwl,
      unnested_node n ->
      unnest_node n Hwl = n.
  Proof with eauto.
    intros n [G Hwl] Hnormed.
    unfold unnested_node in *.
    eapply unnested_equations_unnest_idem
      with (st:=init_st (first_unused_ident
                           (self :: out :: map fst (n_in n ++ n_vars n ++ n_out n ++ anon_in_eqs (n_eqs n))))) in Hnormed...
    destruct n; simpl in *.
    eapply equal_node; simpl...
    Unshelve. 6,7,8,9,10:simpl.
    6,7,8: reflexivity.
    1,2:reflexivity.
    4: { rewrite Hnormed; simpl.
         rewrite init_st_anns; simpl.
         apply app_nil_r. }
    4: { rewrite Hnormed... }
    simpl.
    1,2,3:apply proof_irrelevance.
  Qed.

  Corollary unnested_global_unnest_idem : forall G Hwl,
      unnested_global G ->
      unnest_global G Hwl = G.
  Proof with eauto.
    induction G; intros Hwl Hnormed...
    simpl. inv Hnormed.
    eapply unnested_node_unnest_idem in H1...
    rewrite H1.
    rewrite IHG...
  Qed.

  (** ** Idempotence of fby-normalization *)

  Fact normalized_equation_fby_idem : forall to_cut eq st,
      normalized_equation to_cut eq ->
      fby_equation to_cut eq st = ([eq], st).
  Proof.
    intros to_cut (xs&es) st Hnormed.
    destruct xs; [|destruct xs]; simpl; repeat inv_bind; auto.
    inv Hnormed; simpl; repeat inv_bind; auto.
    destruct ann0 as (?&?&?);
      rewrite <- is_constant_normalized_constant in H3; rewrite H3;
        apply PSE.mem_3 in H1; rewrite H1;
          inv_bind; auto.
    inv H1; try inv_bind; auto.
    inv H; try inv_bind; auto.
  Qed.

  Fact normalized_equations_fby_idem : forall to_cut eqs st,
      Forall (normalized_equation to_cut) eqs ->
      fby_equations to_cut eqs st = (eqs, st).
  Proof.
    induction eqs; intros * Hnormed;
      unfold fby_equations in *; simpl; repeat inv_bind.
    - exists []. exists st. split; auto. inv_bind; auto.
    - inv Hnormed.
      apply IHeqs with (st:=st) in H2; clear IHeqs. repeat inv_bind.
      exists ([a]::x). exists st. repeat inv_bind. split; auto.
      inv_bind. exists [a]. exists st.
      split; [eapply normalized_equation_fby_idem in H1;eauto|].
      inv_bind. exists x. exists st. split; auto. inv_bind; auto.
  Qed.

  Lemma normalized_node_normfby_idem : forall n Hunt,
      normalized_node n ->
      normfby_node PS.empty n Hunt = n.
  Proof with eauto.
    intros n Hunt Hnormed.
    unfold normalized_node in *.
    eapply normalized_equations_fby_idem
      with (st:=init_st (first_unused_ident
                           (self :: out :: map fst (n_in n ++ n_vars n ++ n_out n ++ anon_in_eqs (n_eqs n))))) in Hnormed...
    destruct n; simpl in *.
    eapply equal_node; simpl...
    Unshelve. 6,7,8,9,10:simpl.
    6,7,8: reflexivity.
    1,2:reflexivity.
    4: { rewrite Hnormed; simpl.
         rewrite init_st_anns; simpl.
         apply app_nil_r. }
    4: { rewrite Hnormed... }
    simpl.
    1,2,3:apply proof_irrelevance.
  Qed.

  Corollary normalized_global_normfby_idem : forall G Hunt,
      normalized_global G ->
      normfby_global G Hunt = G.
  Proof with eauto.
    induction G; intros Hwl Hnormed...
    simpl. inv Hnormed.
    eapply normalized_node_normfby_idem in H1...
    rewrite H1.
    rewrite IHG...
  Qed.

  (** ** Idempotence of normalization *)

  Fact normalized_node_unnested_node: forall n,
      normalized_node n ->
      unnested_node n.
  Proof.
    intros * Hnormed.
    unfold normalized_node, unnested_node in *.
    solve_forall.
    eapply normalized_eq_unnested_eq; eauto.
  Qed.

  Fact normalized_global_unnested_global : forall G,
      normalized_global G ->
      unnested_global G.
  Proof.
    intros * Hnormed.
    unfold normalized_global, unnested_global in *.
    solve_forall.
    apply normalized_node_unnested_node; auto.
  Qed.

  Lemma normalized_global_normalize_idem : forall (G : global_wl) G',
      normalized_global G ->
      normalize_global G = Errors.OK G' ->
      G' = G.
  Proof.
    intros [G Hwl] * Hnormed Hnorm; simpl in *.
    unfold normalize_global in Hnorm.
    apply Errors.bind_inversion in Hnorm as [? [H1 H2]]; inv H2.
    assert (unnest_global G Hwl = G) as Heq1.
    { apply unnested_global_unnest_idem.
      eapply normalized_global_unnested_global; eauto. }
    erewrite normalized_global_normfby_idem; auto.
    congruence.
  Qed.

  Theorem normalize_global_idem : forall (G G' : global_wl) G'',
      normalize_global G = Errors.OK (G' : global) ->
      normalize_global G' = Errors.OK G'' ->
      G'' = G'.
  Proof.
    intros * Hnorm1 Hnorm2.
    eapply normalized_global_normalize_idem; eauto.
    eapply normalize_global_normalized_global; eauto.
  Qed.
End IDEMPOTENCE.

Module IdempotenceFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Cau : LCAUSALITY Ids Op Syn)
       (Norm : NORMALIZATION Ids Op OpAux Syn Cau)
       <: IDEMPOTENCE Ids Op OpAux Syn Cau Norm.
  Include IDEMPOTENCE Ids Op OpAux Syn Cau Norm.
End IdempotenceFun.
