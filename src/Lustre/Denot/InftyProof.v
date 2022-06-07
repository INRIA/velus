From Coq Require Import String Morphisms.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoindStreams.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LCausality Lustre.LOrdered Lustre.LSemantics.

From Velus Require Import Lustre.Denot.Cpo.
Require Import Cpo_ext SDfuns Denot Infty.

Import List.

(* TODO: move *)
Lemma In_list_pair_l :
  forall {A B} (l : list (A*B)) x y,
    In (x,y) l -> In x (map fst l).
Proof.
  induction l; simpl; firstorder; subst; auto.
Qed.

(* TODO: move if used *)
Lemma Forall_In :
  forall {A} (P : A -> Prop) l x,
    Forall P l ->
    In x l ->
    P x.
Proof.
  setoid_rewrite Forall_forall.
  auto.
Qed.

Module Type LDENOTINF
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Typ   : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import LCA   : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Import Lord  : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Import Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord CStr).

  Section node_inf.

  Context {PSyn : block -> Prop}.
  Context {prefs : PS.t}.
  Variable (G : @global PSyn prefs).
  (* Variable Γ : static_env. *)

  (* Selon Basile, il ne serait pas difficile de modifier l'élaboration
     de sorte à ce que la propritété suivante soit vérifiée pour les nœuds
     sans blocs. En attendant, on la suppose. *)
  Hypothesis HasCausInj :
    forall Γ x cx, HasCaus Γ x cx -> x = cx.

  Lemma HasCausRefl : forall Γ x, IsVar Γ x -> HasCaus Γ x x.
  Proof.
    intros * Hv.
    inv Hv.
    apply InMembers_In in H as [e Hin].
    econstructor; eauto.
    erewrite HasCausInj; eauto using HasCaus.
  Qed.

  Lemma idcaus_map :
    forall l : list (ident * (type * clock * ident)),
      map snd (idcaus l) = map fst l.
  Proof.
    intros.
    rewrite <- map_fst_senv_of_inout.
    unfold idcaus, senv_of_inout.
    rewrite 2 map_map.
    apply map_ext_in_iff.
    intros (x & (ty&c) &cx) Hin; simpl.
    apply symmetry, HasCausInj with (Γ := senv_of_inout l).
    econstructor.
    apply in_map_iff; esplit; split; eauto.
    all: eauto.
  Qed.

  (** Invariants pour l'induction causale *)
  Definition P_var (n : nat) (env : DS_prod SI) (x : ident) : Prop :=
    is_cons (nrem n (PROJ _ x env)).

  Definition P_vars (n : nat) (env : DS_prod SI) (cxs : list ident) : Prop :=
    Forall (P_var n env) cxs.

  Definition P_exp (n : nat) ins envI bs env (e : exp) (k : nat) : Prop :=
    let ss := denot_exp ins e envI bs env in
    is_cons (nrem n (get_nth ss k)).

  Lemma P_vars_In :
    forall n env xs x,
      P_vars n env xs ->
      In x xs ->
      P_var n env x.
  Proof.
    unfold P_vars.
    setoid_rewrite Forall_forall.
    auto.
  Qed.

  Lemma P_var_S :
    forall n env x,
      P_var (S n) env x ->
      P_var n env x.
  Proof.
    unfold P_var.
    eauto using is_consn_S.
  Qed.

  Lemma P_vars_S :
    forall n env xs,
      P_vars (S n) env xs ->
      P_vars n env xs.
  Proof.
    unfold P_vars.
    eauto using Forall_impl, P_var_S.
  Qed.

  Lemma P_vars_weaken :
    forall n env xs ys,
      P_vars n env (xs ++ ys) ->
      P_vars n env ys.
  Proof.
    unfold P_vars.
    eauto using Forall_app_weaken.
  Qed.

  (* TODO: move to LSyntax *)
  Lemma annots_numstreams :
    forall es, length (annots es) = list_sum (map numstreams es).
  Proof.
    induction es; simpl; auto.
    rewrite app_length; f_equal; auto.
    rewrite <- length_typeof_numstreams, typeof_annot.
    now rewrite map_length.
  Qed.

  (* TODO: move? *)
  Lemma denot_equation_input :
    forall {PSyn prefs} (G : @global PSyn prefs) Γ
      e ins envI bs env x,
      wt_equation G Γ e ->
      In x ins ->
      denot_equation ins e envI bs env x = envI x.
  Proof.
    intros * Hwt Hx.
    apply mem_ident_spec in Hx.
    destruct e as (xs,es).
    destruct Hwt as [? Hwt]. apply Forall2_length in Hwt.
    rewrite length_typesof_annots, annots_numstreams in Hwt.
    rewrite denot_equation_eq.
    cases_eqn HH; congruence.
  Qed.

  Lemma P_exps_k : forall n es ins envI bs env k,
      P_exps (P_exp n ins envI bs env) es k ->
      is_cons (nrem n (get_nth (denot_exps ins es envI bs env) k)).
  Proof.
    induction es as [| e es]; intros * Hp (* Hwl Hr *); inv Hp; simpl_Forall.
    - setoid_rewrite denot_exps_eq.
      setoid_rewrite nprod_app_nth1; eauto using Is_free_left_list.
    - setoid_rewrite denot_exps_eq.
      setoid_rewrite nprod_app_nth2; eauto using Is_free_left_list.
  Qed.

  (* TODO: move? *)
  Lemma P_exps_impl :
    forall (Q_exp P_exp : exp -> nat -> Prop) es k,
      P_exps Q_exp es k ->
      P_exps (fun e k => Q_exp e k -> P_exp e k) es k ->
      P_exps P_exp es k.
  Proof.
    intros * Hpq Hq.
    induction Hpq; inv Hq; constructor; auto; lia.
  Qed.

  (* TODO: move? *)
  Lemma P_exps_Forall :
    forall (P_exp : exp -> Prop) es k,
      Forall P_exp es ->
      k < list_sum (map numstreams es) ->
      P_exps (fun e _ => P_exp e) es k.
  Proof.
    induction es as [|e es]; simpl; intros * Hf Hk. inv Hk.
    inv Hf.
    destruct (Nat.lt_ge_cases k (numstreams e)); auto using P_exps.
    constructor 2; auto.
    apply IHes; auto; lia.
  Qed.

  Lemma exp_O :
    forall Γ e ins envI bs env k,
      is_cons (nrem O bs) ->
      P_vars O envI ins ->
      k < numstreams e ->
      (forall x, Is_free_left Γ x k e -> P_var O env x) ->
      wl_exp G e ->
      wx_exp Γ e ->
      restr_exp e ->
      P_exp O ins envI bs env e k.
  Proof.
    intros * Hbs Hins Hk Hdep Hwl Hwx Hre.
    assert (Hwl' := Hwl).
    revert Hwl Hre.
    eapply exp_causal_ind with (15 := Hdep); eauto.
    all: intros; clear dependent e; inv Hre; unfold P_exp.
    - (* const *)
      rewrite denot_exp_eq.
      now apply is_consn_sconst.
    - (* var *)
      rewrite denot_exp_eq.
      unfold P_vars, P_var in *.
      simpl. rewrite ID_simpl, Id_simpl, Forall_forall in *.
      cases_eqn HH.
      + (* in *)
        rewrite mem_ident_spec in HH.
        now apply Hins.
      + (* out *)
        apply HasCausInj in H; subst; auto.
    - (* unop *)
      rewrite denot_exp_eq.
      cases_eqn HH; subst.
      1,3: inv Hwl; rewrite <- length_typeof_numstreams, HH in *; now simpl in *.
      assert (is_cons (nrem O (get_nth (denot_exp ins e1 envI bs env0) 0))) as He.
      { inv Hwl. apply H; auto. }
      revert He.
      generalize (denot_exp ins e1 envI bs env0).
      generalize (numstreams e1).
      simpl. intros; cases.
      2: apply is_consn_DS_const with (n := O). (* pourquoi auto ne fonctionne pas ? *)
      apply is_consn_sunop with (n := O); auto.
    - (* fby *)
      rewrite denot_exp_eq; simpl.
      unfold eq_rect_r, eq_rect.
      cases.
      2,3: rewrite get_nth_const; auto; apply (is_consn_DS_const _ O).
      rewrite lift2_nth; auto; cases.
      apply is_cons_fby; auto.
      inv Hwl.
      rewrite annots_numstreams, H10, <- H9 in *.
      eapply P_exps_k with (n := O); eauto.
      eauto using P_exps_impl, P_exps_Forall.
  Qed.

  Lemma exp_n :
    forall Γ n e ins envI bs env k,
      is_cons (nrem n bs) ->
      P_vars n envI ins ->
      k < numstreams e ->
      wl_exp G e ->
      wx_exp Γ e ->
      restr_exp e ->
      (forall x cx, HasCaus Γ x cx -> P_var n env cx) ->
      P_exp n ins envI bs env e k.
  Proof.
    intros ?????? env ? Hbs Hins.
    revert k.
    induction e using exp_ind2; simpl; intros ? Hk Hwl Hwx Hre Hn.
    all: inv Hre; unfold P_exp.
    - (* const *)
      assert (k = O) by lia; subst.
      rewrite denot_exp_eq.
      now apply is_consn_sconst.
    - (* var *)
      assert (k = O) by lia; subst.
      unfold P_vars, P_var in *.
      simpl. rewrite ID_simpl, Id_simpl, Forall_forall in *.
      setoid_rewrite denot_exp_eq.
      cases_eqn HH.
      + (* in *)
        rewrite mem_ident_spec in HH.
        now apply Hins.
      + (* out *)
        inv Hwx.
        eapply Hn, HasCausRefl; auto.
    - (* unop *)
      assert (k = O) by lia; subst.
      rewrite denot_exp_eq.
      cases_eqn HH; subst.
      1,3: inv Hwl; rewrite <- length_typeof_numstreams, HH in *; now simpl in *.
      assert (is_cons (nrem n (get_nth (denot_exp ins e envI bs env) 0))) as He.
      { inv Hwl. inv Hwx. eapply IHe; auto; lia. }
      revert He.
      generalize (denot_exp ins e envI bs env).
      generalize (numstreams e).
      intros; cases.
      2: apply is_consn_DS_const. (* pourquoi auto ne fonctionne pas ? *)
      apply is_consn_sunop; auto.
    - (* fby *)
      rewrite denot_exp_eq; simpl.
      unfold eq_rect_r, eq_rect.
      cases.
      2,3: rewrite get_nth_const; auto; apply (is_consn_DS_const _ n).
      rewrite lift2_nth; auto; cases.
      inv Hwl.
      apply is_consn_fby.
      (* TODO: factoriser un peu le raisonnement *)
      + (* e0s *)
        assert (k < list_sum (map numstreams e0s))
          by (rewrite annots_numstreams in *; congruence).
        apply P_exps_k.
        inv Hwx. clear dependent es. clear H9.
        revert dependent k. induction e0s; intros; simpl in *. lia.
        simpl_Forall.
        destruct (Nat.lt_ge_cases k (numstreams a0)); auto using P_exps.
        constructor 2; auto. apply IHe0s; auto; lia.
      + (* es *)
        assert (k < list_sum (map numstreams es))
          by (rewrite annots_numstreams in *; congruence).
        apply P_exps_k.
        inv Hwx. clear dependent e0s. clear H10.
        revert dependent k. induction es; intros; simpl in *. lia.
        simpl_Forall.
        destruct (Nat.lt_ge_cases k (numstreams a0)); auto using P_exps.
        constructor 2; auto. apply IHes; auto; lia.
  Qed.

  Lemma exps_n :
    forall Γ n es ins envI bs env k,
      is_cons (nrem n bs) ->
      P_vars n envI ins ->
      k < list_sum (map numstreams es) ->
      Forall (wl_exp G) es ->
      Forall (wx_exp Γ) es ->
      Forall restr_exp es ->
      (forall x cx, HasCaus Γ x cx -> P_var n env cx) ->
      P_exps (P_exp n ins envI bs env) es k.
  Proof.
    induction es as [| e es]; simpl; intros * Hbs Hins Hk Hwl Hwx Hre Hn.
    inv Hk.
    simpl_Forall.
    destruct (Nat.lt_ge_cases k (numstreams e)).
    - constructor; eauto using exp_n.
    - constructor 2; auto. apply IHes; auto; lia.
  Qed.

  Lemma exp_S :
    forall Γ n e ins envI bs env k,
      is_cons (nrem (S n) bs) ->
      P_vars (S n) envI ins ->
      k < numstreams e ->
      (forall x, Is_free_left Γ x k e -> P_var (S n) env x) ->
      wl_exp G e ->
      wx_exp Γ e ->
      restr_exp e ->
      (forall x cx, HasCaus Γ x cx -> P_var n env cx) ->
      P_exp (S n) ins envI bs env e k.
  Proof.
    intros ?????? env ? Hbs Hins Hk Hdep Hwl Hwx Hre Hn.
    assert (Hwl' := Hwl).
    assert (Hwx' := Hwx).
    revert Hwl Hwx Hre.
    eapply exp_causal_ind with (15 := Hdep); eauto.
    all: clear dependent e; clear k.
    all: intros; inv Hre; unfold P_exp.
    - (* const *)
      rewrite denot_exp_eq.
      now apply is_consn_sconst.
    - (* var *)
      unfold P_vars, P_var in *.
      simpl. rewrite ID_simpl, Id_simpl, Forall_forall in *.
      setoid_rewrite denot_exp_eq.
      cases_eqn HH.
      + (* in *)
        rewrite mem_ident_spec in HH.
        now apply Hins.
      + (* out *)
        apply HasCausInj in H; subst; auto.
    - (* unop *)
      rewrite denot_exp_eq.
      cases_eqn HH; subst.
      1,3: inv Hwl; rewrite <- length_typeof_numstreams, HH in *; now simpl in *.
      assert (is_cons (nrem (S n) (get_nth (denot_exp ins e1 envI bs env) 0))) as He.
      { inv Hwl. inv Hwx. apply H; auto. }
      revert He.
      generalize (denot_exp ins e1 envI bs env).
      generalize (numstreams e1).
      intros; cases.
      2: apply is_consn_DS_const. (* pourquoi auto ne fonctionne pas ? *)
      apply is_consn_sunop; auto.
    - (* fby *)
      rewrite denot_exp_eq; simpl.
      unfold eq_rect_r, eq_rect.
      cases.
      2,3: rewrite get_nth_const; auto; apply (is_consn_DS_const _ (S n)).
      rewrite lift2_nth; auto; cases.
      inv Hwl. inv Hwx.
      apply is_consn_S_fby.
      + (* e0s *)
        assert (k < list_sum (map numstreams e0s))
          by (rewrite annots_numstreams in *; congruence).
        do 3 (apply P_exps_impl in H0; eauto using P_exps_Forall).
        now apply P_exps_k.
      + (* es *)
        eapply P_exps_k, exps_n; eauto using is_consn_S, P_vars_S.
  Qed.

  Lemma equation_n :
    forall xs es n k ins envI bs,
      let env := FIXP (DS_prod SI) (denot_equation ins (xs,es) envI bs) in
      NoDup (ins ++ xs) ->
      k < length xs ->
      P_exps (P_exp n ins envI bs env) es k ->
      P_var n env (nth k xs xH).
  Proof.
    intros ??????? env Hnd Hk Hes.
    subst env.
    unfold P_var.
    rewrite FIXP_eq, PROJ_simpl, denot_equation_eq.
    rewrite mem_nth_nth; eauto using NoDup_app_r.
    cases_eqn HH; auto using is_consn_DS_const, P_exps_k.
    (* cas pénible *)
    exfalso. rewrite mem_ident_spec in *.
    eapply NoDup_app_In; eauto using nth_In.
  Qed.

  Lemma P_var_input_eq :
    forall Γ ins envI bs e x n,
      wt_equation G Γ e ->
      In x ins ->
      P_vars n envI ins ->
      P_var n (FIXP (DS_prod SI) (denot_equation ins e envI bs)) x.
  Proof.
    intros * Hwt Hin Hins.
    unfold P_vars, P_var in *.
    rewrite FIXP_eq, PROJ_simpl.
    erewrite denot_equation_input, Forall_forall, <- PROJ_simpl in *; eauto.
  Qed.

  Lemma P_var_input_node :
    forall nd envI bs x n,
      restr_node nd ->
      wt_node G nd ->
      In x (map fst (n_in nd)) ->
      P_vars n envI (map fst (n_in nd)) ->
      P_var n (FIXP (DS_prod SI) (denot_node nd envI bs)) x.
  Proof.
    intros * Hr Hwt Hx Hins.
    unfold denot_node, denot_block.
    destruct Hwt as (?&?&?& Hwt).
    inv Hwt; inv Hr; try congruence; eauto using P_var_input_eq.
  Qed.

  Lemma denot_S :
    forall nd envI bs n,
      restr_node nd ->
      wt_node G nd ->
      node_causal nd ->
      is_cons (nrem (S n) bs) ->
      P_vars (S n) envI (map fst nd.(n_in)) ->
      P_vars n (FIXP _ (denot_node nd envI bs)) (map fst nd.(n_out)) ->
      P_vars (S n) (FIXP _ (denot_node nd envI bs)) (map fst nd.(n_out)).
  Proof.
    intros * Hr Hwt Hcaus Hbs Hins Hn.
    eapply P_vars_weaken.
    rewrite <- map_app, <- idcaus_map.
    rewrite <- (@app_nil_r (ident*ident)) at 1.
    assert (idcaus_of_locals (n_block nd) = []) as <- by now inv Hr.
    eapply node_causal_ind; auto.
    - unfold P_vars. now intros ?? ->.
    - now red.
    - intros x xs' [Hx|Hx] Hxs' Hdep.
      2: now destruct Hr; simpl in *.
      constructor; auto.
      rewrite idcaus_app, map_app, in_app_iff, 2 idcaus_map in Hx.
      destruct Hx as [|Hx]; eauto using P_var_input_node.
      (* TODO: nettoyer *)

      destruct (n_defd nd) as (ys & Hvd & Hperm).
      destruct Hwt as (?&?&?& Hwt).
      unfold denot_node, denot_block in *.
      inv Hvd; destruct Hr as [? es Hr]; try congruence.
      inv H3; simpl (fst _) in *.

      rewrite <- Hperm in Hx.
      apply In_nth with (d := xH) in Hx as (k & Hlen & Hnth); subst.
      eapply equation_n; eauto.
      { rewrite Hperm, <- map_app; apply node_NoDup. }
      eapply Pexp_Pexps with
        (Γ := (senv_of_inout (n_in nd ++ n_out nd)))
        (P_var := P_var (S n) (FIXP _ (denot_equation (map fst (n_in nd)) (xs, es) envI bs))); eauto.
      + inv Hwt.  assert(Wte := H4). destruct H4 as [Hwt].
        apply Forall_wt_exp_wx_exp in Hwt as Hwx.
        apply Forall_wt_exp_wl_exp in Hwt as Hwl.
        apply Forall_forall.
        intros e Hin k' Hk' Hdp.
        pose proof (Forall_In _ _ _ Hwx Hin) as Hwxe.
        pose proof (Forall_In _ _ _ Hwl Hin) as Hwle.
        pose proof (Forall_In _ _ _ Hwt Hin) as Hwte.
        pose proof (Forall_In _ _ _ Hr  Hin) as Hre.
        eapply exp_S; eauto.
        (* TODO: lemma pour ça : *)
        intros x cx Hc.
        apply HasCausInj in Hc as ?; subst.
        eapply or_introl, idcaus_of_senv_In in Hc.
        rewrite idcaus_of_senv_inout in Hc.
        apply In_list_pair_l in Hc.
        rewrite map_fst_idcaus, map_app, in_app_iff in Hc.
        destruct Hc as [Hc|]; eauto using P_vars_In, P_var_input_eq, P_vars_S.
      + intros x Hfr.
        eapply P_vars_In; eauto.
        apply Hdep.
        econstructor; eauto using (nth_error_nth' _ xH).
        apply HasCausRefl.
        (* TODO: lemme pour ça ? : *)
        rewrite <- map_fst_senv_of_inout in Hperm.
        unfold senv_of_inout in *.
        constructor.
        rewrite fst_InMembers, 2 map_app, in_app, <- Hperm.
        auto using nth_In.
      + inv Hwt.
        destruct H4 as [? Hwt]. apply Forall2_length in Hwt.
        rewrite length_typesof_annots in Hwt. congruence.
  Qed.

  (* TODO: ressemble beaucoup à denot_S... *)
  Lemma denot_O :
    forall nd envI bs,
      restr_node nd ->
      wt_node G nd ->
      node_causal nd ->
      is_cons (nrem O bs) ->
      P_vars O envI (map fst nd.(n_in)) ->
      P_vars O (FIXP _ (denot_node nd envI bs)) (map fst nd.(n_out)).
  Proof.
    intros * Hr Hwt Hcaus Hbs Hins.
    eapply P_vars_weaken.
    rewrite <- map_app, <- idcaus_map.
    rewrite <- (@app_nil_r (ident*ident)) at 1.
    assert (idcaus_of_locals (n_block nd) = []) as <- by now inv Hr.
    eapply node_causal_ind; auto.
    - unfold P_vars. now intros ?? ->.
    - now red.
    - intros x xs' [Hx|Hx] Hxs' Hdep.
      2: now destruct Hr; simpl in *.
      constructor; auto.
      rewrite idcaus_app, map_app, in_app_iff, 2 idcaus_map in Hx.
      destruct Hx as [|Hx]; eauto using P_var_input_node.

      destruct (n_defd nd) as (ys & Hvd & Hperm).
      destruct Hwt as (?&?&?& Hwt).
      unfold denot_node, denot_block in *.
      inv Hvd; destruct Hr as [? es Hr]; try congruence.
      inv H3; simpl (fst _) in *.

      rewrite <- Hperm in Hx.
      apply In_nth with (d := xH) in Hx as (k & Hlen & Hnth); subst.
      eapply equation_n; eauto.
      { rewrite Hperm, <- map_app; apply node_NoDup. }
      eapply Pexp_Pexps with
        (Γ := (senv_of_inout (n_in nd ++ n_out nd)))
        (P_var := P_var O (FIXP _ (denot_equation (map fst (n_in nd)) (xs, es) envI bs))); eauto.
      + inv Hwt. assert(Wte := H4). destruct H4 as [Hwt].
        apply Forall_wt_exp_wx_exp in Hwt as Hwx.
        apply Forall_wt_exp_wl_exp in Hwt as Hwl.
        apply Forall_forall.
        intros e Hin k' Hk' Hdp.
        pose proof (Forall_In _ _ _ Hwx Hin) as Hwxe.
        pose proof (Forall_In _ _ _ Hwl Hin) as Hwle.
        pose proof (Forall_In _ _ _ Hwt Hin) as Hwte.
        pose proof (Forall_In _ _ _ Hr  Hin) as Hre.
        eapply exp_O; eauto.
      + intros x Hfr.
        eapply P_vars_In; eauto.
        apply Hdep.
        econstructor; eauto using (nth_error_nth' _ xH).
        apply HasCausRefl.
        (* TODO: lemme pour ça ? : *)
        rewrite <- map_fst_senv_of_inout in Hperm.
        unfold senv_of_inout in *.
        constructor.
        rewrite fst_InMembers, 2 map_app, in_app, <- Hperm.
        auto using nth_In.
      + inv Hwt.
        destruct H4 as [? Hwt]. apply Forall2_length in Hwt.
        rewrite length_typesof_annots in Hwt. congruence.
  Qed.

  Theorem denot_n :
    forall nd envI bs n,
      restr_node nd ->
      wt_node G nd ->
      node_causal nd ->
      is_cons (nrem n bs) ->
      P_vars n envI (map fst nd.(n_in)) ->
      P_vars n (FIXP _ (denot_node nd envI bs)) (map fst nd.(n_out)).
  Proof.
    induction n; intros Hr Hwt Hcaus Hbs Hins.
    - apply denot_O; auto.
    - apply denot_S; auto using is_consn_S, P_vars_S.
  Qed.

  (* Avec l'hypothèse [restr_node] actuelle, toutes les variables du nœud
     sont définies dans une seule équation et [denot_equation] associe
     [DS_const err] aux autres variables. On peut donc en déduire que
     tous les flots dans le point fixe de denot_equation sont P_vars n.
   *)
  Lemma P_vars_node_all :
    forall nd envI bs n,
      restr_node nd ->
      wt_node G nd ->
      P_vars n envI (map fst nd.(n_in)) ->
      P_vars n (FIXP _ (denot_node nd envI bs)) (map fst nd.(n_out)) ->
      forall x, P_var n (FIXP _ (denot_node nd envI bs)) x.
  Proof.
    intros * Hr Hwt Hins Hn x.
    destruct (mem_ident x (map fst (n_in nd))) eqn:Hin.
    { rewrite mem_ident_spec in Hin. eauto using P_var_input_node. }
    destruct (mem_ident x (map fst (n_out nd))) eqn:Hout.
    { rewrite mem_ident_spec in Hout. eapply Forall_In in Hn; eauto. }
    destruct (n_defd nd) as (ys & Hvd & Hperm).
    unfold P_var.
    rewrite FIXP_eq, PROJ_simpl.
    unfold denot_node, denot_block in *.
    destruct Hr; inv Hvd; simpl (fst _) in *.
    rewrite <- Bool.not_true_iff_false, mem_ident_spec, <- Hperm in Hout.
    rewrite denot_equation_eq.
    cases_eqn HH; try congruence; auto using is_consn_DS_const.
    destruct Hout; eauto using mem_nth_In.
  Qed.

  Corollary denot_n_all_vars :
    forall nd envI bs n,
      restr_node nd ->
      wt_node G nd ->
      node_causal nd ->
      is_cons (nrem n bs) ->
      P_vars n envI (idents nd.(n_in)) ->
      forall x, P_var n (FIXP _ (denot_node nd envI bs)) x.
  Proof.
    intros.
    apply P_vars_node_all; auto using denot_n.
  Qed.

  (** Maintenant on passe à l'infini *)

  Definition all_infinite (env : DS_prod SI) : Prop :=
    forall x, infinite (env x).

  Lemma infinite_P_vars :
    forall env, all_infinite env <-> (forall n x, P_var n env x).
  Proof.
    intro env.
    unfold P_var, all_infinite.
    Opaque nrem. (* WTF *)
    setoid_rewrite PROJ_simpl.
    split; eauto using nrem_inf, inf_nrem.
  Qed.

  Definition all_infinite_in (l : list ident) (env : DS_prod SI) : Prop :=
    forall x, In x l -> infinite (env x).

  Lemma infinite_in_P_vars :
    forall l env, all_infinite_in l env <-> (forall n, P_vars n env l).
  Proof.
    intros l env.
    unfold P_vars, P_var, all_infinite_in.
    setoid_rewrite Forall_forall.
    Opaque nrem. (* WTF *)
    setoid_rewrite PROJ_simpl.
    split; eauto using nrem_inf, inf_nrem.
  Qed.

  Theorem denot_inf :
    forall nd envI bs,
      restr_node nd ->
      wt_node G nd ->
      node_causal nd ->
      infinite bs ->
      all_infinite_in (idents nd.(n_in)) envI ->
      all_infinite_in (idents nd.(n_out)) (FIXP _ (denot_node nd envI bs)).
  Proof.
    intros.
    rewrite infinite_in_P_vars in *.
    intro.
    eapply denot_n; eauto using inf_nrem.
  Qed.

  Corollary denot_inf_all :
    forall nd envI bs,
      restr_node nd ->
      wt_node G nd ->
      node_causal nd ->
      infinite bs ->
      all_infinite_in (idents nd.(n_in)) envI ->
      all_infinite (FIXP _ (denot_node nd envI bs)).
  Proof.
    intros.
    rewrite infinite_P_vars, infinite_in_P_vars in *.
    intro.
    eapply denot_n_all_vars; eauto using inf_nrem.
  Qed.

  End node_inf.

End LDENOTINF.

Module LDenotInfFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Senv  : STATICENV     Ids Op OpAux Cks)
       (Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ   : LTYPING Ids Op OpAux Cks Senv Syn)
       (LCA   : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Lord  : LORDERED Ids Op OpAux Cks Senv Syn)
       (CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord CStr)
<: LDENOTINF Ids Op OpAux Cks Senv Syn Typ LCA Lord CStr Den.
  Include LDENOTINF Ids Op OpAux Cks Senv Syn Typ LCA Lord CStr Den.
End LDenotInfFun.
