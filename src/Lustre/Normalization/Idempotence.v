From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import Omega.
Require Import ProofIrrelevance.

From Velus Require Import Common Ident.
From Velus Require Import Operators.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.FullNorm.

(** * Idempotence of the normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type IDEMPOTENCE
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Norm : FULLNORM Ids Op OpAux Syn).

  Import Fresh Fresh.Fresh Facts Tactics.

  (** ** Idempotence of normalization *)

  Fact normalized_lexp_normalize_idem : forall e is_control st,
      normalized_lexp e ->
      normalize_exp is_control e st = ([e], [], st).
  Proof with eauto.
    intros e is_control st Hnormed; revert is_control.
    induction Hnormed; intro is_control; simpl; repeat inv_bind...
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
      (exists eqs, map_bind2 (normalize_exp is_control) es st = (List.map (fun e => [e]) es, eqs, st) /\ (concat eqs = [])).
  Proof with eauto.
    induction es; intros is_control st Hf;
      inv Hf; simpl; repeat inv_bind...
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
      normalize_exps es st = (es, [], st).
  Proof with eauto.
    intros.
    eapply normalized_lexps_normalize_idem' in H. destruct H as [eqs [H Heqs]].
    unfold normalize_exps; inv_bind.
    repeat eexists...
    inv_bind. rewrite concat_map_singl1. congruence.
  Qed.

  Fact normalized_cexp_normalize_idem : forall e st,
      normalized_cexp e ->
      normalize_exp true e st = ([e], [], st).
  Proof with eauto.
    intros e st Hnormed.
    induction Hnormed; simpl; repeat inv_bind...
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

  Fact normalize_fby_idem : forall e0 e ann st,
      is_constant e0 ->
      normalized_lexp e ->
      normalize_fby [e0] [e] [ann] st = ([Efby [e0] [e] [ann]], [], st).
  Proof with eauto.
    intros e0 e [ty cl] st Hcons Hnormed.
    unfold normalize_fby; inv_bind.
    eexists. exists [[]]. exists st. split; simpl; inv_bind...
    eexists. exists []. exists st. split; simpl.
    - unfold fby_iteexp.
      destruct (Norm.is_constant e0) eqn:Hisconstant; repeat inv_bind...
      rewrite <- is_constant_is_constant in Hcons. congruence.
    - inv_bind.
      repeat eexists; inv_bind...
  Qed.

  Fact normalized_rhs_normalize_idem : forall e keep_fby st,
      normalized_rhs keep_fby e ->
      normalize_rhs keep_fby e st = ([e], [], st).
  Proof with eauto.
    intros e keep_fby st Hnormed.
    destruct e; inv Hnormed; unfold normalize_rhs;
      try (solve [eapply normalized_cexp_normalize_idem; eauto]);
      try (solve [inv H; inv H0]).
    - (* fby *)
      repeat inv_bind.
      exists [e0]. exists []. exists st.
      split; unfold normalize_exps; inv_bind.
      + exists [[e0]]. exists [[]]. exists st. split; simpl; inv_bind...
        eapply constant_normalized_lexp in H2. eapply normalized_lexp_normalize_idem in H2.
        repeat eexists...
        inv_bind.
        exists []. exists []. exists st.
        repeat split; inv_bind...
      + exists [e]. exists []. exists st. split; simpl; inv_bind...
        * exists [[e]]. exists [[]]. exists st. split; simpl; inv_bind...
          eapply normalized_lexp_normalize_idem in H4.
          repeat eexists... inv_bind.
          repeat eexists; inv_bind...
        * repeat eexists; try inv_bind...
          eapply normalize_fby_idem...
    - (* app *)
      repeat inv_bind.
      eapply normalized_lexps_normalize_idem in H1.
      repeat eexists... repeat inv_bind.
      repeat eexists...
      inv_bind...
    - (* app (reset) *)
      repeat inv_bind.
      eapply normalized_lexps_normalize_idem in H1.
      repeat (repeat eexists; eauto; simpl; inv_bind; eauto).
  Qed.

  Corollary normalized_rhss_normalize_idem' : forall es keep_fby st,
      Forall (normalized_rhs keep_fby) es ->
      (exists eqs, map_bind2 (normalize_rhs keep_fby) es st = (List.map (fun e => [e]) es, eqs, st) /\ (concat eqs = [])).
  Proof with eauto.
    induction es; intros keep_fby st Hf;
      inv Hf; simpl; repeat inv_bind...
    eapply normalized_rhs_normalize_idem in H1...
    eapply (IHes keep_fby st) in H2; clear IHes.
    destruct H2 as [eqs [H2 Heqs]].
    exists ([]::eqs).
    repeat (repeat eexists; eauto; inv_bind).
  Qed.

  Corollary normalized_rhss_normalize_idem : forall es keep_fby st,
      Forall (normalized_rhs keep_fby) es ->
      normalize_rhss keep_fby es st = (es, [], st).
  Proof with eauto.
    intros.
    eapply normalized_rhss_normalize_idem' in H. destruct H as [eqs [H Heqs]].
    unfold normalize_rhss; inv_bind.
    repeat eexists...
    inv_bind. rewrite concat_map_singl1. congruence.
  Qed.

  Fact normalized_equation_normalize_idem : forall G eq to_cut st,
      wl_equation G eq ->
      normalized_equation to_cut eq ->
      normalize_equation to_cut eq st = ([eq], st).
  Proof with eauto.
    intros G [xs es] to_cut st Hwl Hnormed. inv Hwl.
    specialize (normalized_equation_normalized_rhs _ _ _ Hnormed) as Hnormed2.
    apply normalized_rhss_normalize_idem with (st:=st) in Hnormed2.
    inv Hnormed; simpl; repeat inv_bind;
      repeat eexists; eauto;
        inv_bind; rewrite app_nil_r;
          simpl in *; repeat f_equal.
    - rewrite app_nil_r in H0.
      apply firstn_all2. rewrite H0. apply le_refl.
    - rewrite app_nil_r in H0.
      apply firstn_all2. rewrite H0. apply le_refl.
    - rewrite app_nil_r in H0. rewrite length_annot_numstreams in H0.
      apply firstn_all2. simpl. rewrite H0. apply le_refl.
  Qed.

  Corollary normalized_equations_normalize_idem : forall G eqs to_cut st,
      Forall (wl_equation G) eqs ->
      Forall (normalized_equation to_cut) eqs ->
      normalize_equations to_cut eqs st = (eqs, st).
  Proof with eauto.
    induction eqs; intros to_cut st Hwl Hnormed; inv Hwl; inv Hnormed;
      unfold normalize_equations; repeat inv_bind...
    eapply normalized_equation_normalize_idem in H3...
    repeat eexists... inv_bind.
    repeat eexists... inv_bind.
    rewrite <- cons_is_app...
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

  Lemma normalized_node_normalize_idem : forall n Hwl,
      normalized_node n ->
      normalize_node PS.empty n Hwl = n.
  Proof with eauto.
    intros n [G Hwl] Hnormed.
    unfold normalize_node, normalized_node in *.
    eapply normalized_equations_normalize_idem
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

  Corollary normalized_global_normalize_idem : forall G Hwl,
      normalized_global G ->
      normalize_global G Hwl = G.
  Proof with eauto.
    induction G; intros Hwl Hnormed...
    simpl. inv Hnormed.
    eapply normalized_node_normalize_idem in H1...
    rewrite H1.
    rewrite IHG...
  Qed.

  Theorem normalize_global_idem : forall G Hwl1 Hwl2,
      normalize_global (normalize_global G Hwl1) Hwl2 = normalize_global G Hwl1.
  Proof.
    intros G Hwl1 Hwl2.
    apply normalized_global_normalize_idem.
    apply normalize_global_normalized_global.
  Qed.
End IDEMPOTENCE.

Module IdempotenceFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Norm : FULLNORM Ids Op OpAux Syn)
       <: IDEMPOTENCE Ids Op OpAux Syn Norm.
  Include IDEMPOTENCE Ids Op OpAux Syn Norm.
End IdempotenceFun.
