From Coq Require Import String Morphisms.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LCausality Lustre.LSemantics Lustre.LOrdered.

From Velus Require Import Lustre.Denot.Cpo.
Require Import Cpo_ext SDfuns Denot Infty CommonList2.

Import List.

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
       (Import Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord).

  (* TODO: move?? *)
  Ltac gen_sub_exps :=
  (* simpl; (* important, même si l'action n'est pas visible *) *)
  repeat match goal with
  | |- context [ ?f1 (?f2 (?f3 (?f4 (denot_expss ?e1 ?e2 ?e3 ?e4) ?e5) ?e6) ?e7) ?e8 ] =>
      generalize (f1 (f2 (f3 (f4 (denot_expss e1 e2 e3 e4) e5) e6) e7) e8)
  | |- context [ ?f1 (?f2 (?f3 (?f4 (denot_exps ?e1 ?e2 ?e3) ?e4) ?e5) ?e6) ?e7 ] =>
      generalize (f1 (f2 (f3 (f4 (denot_exps e1 e2 e3) e4) e5) e6) e7)
  | |- context [ ?f1 (?f2 (?f3 (?f4 (denot_exp ?e1 ?e2 ?e3) ?e4) ?e5) ?e6) ?e7 ] =>
      generalize (f1 (f2 (f3 (f4 (denot_exp e1 e2 e3) e4) e5) e6) e7)
    end.

  (* section là juste pour supposer HasCausInj, amené à disparaître  *)
  Section Top.

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

  (** First we show that a well-formed node receiving streams of
      length n outputs streams of length n. *)
  Section Node_n.

  Variables
    (G : global)
    (envG : Dprodi FI).

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
    is_ncons n (PROJ _ x env).

  Definition P_vars (n : nat) (env : DS_prod SI) (cxs : list ident) : Prop :=
    Forall (P_var n env) cxs.

  Definition P_exp (n : nat) ins envI bs env (e : exp) (k : nat) : Prop :=
    let ss := denot_exp G ins e envG envI bs env in
    is_ncons n (get_nth k errTy ss).

  (* Hypothèse sur les nœuds *)
  Hypothesis Hnode :
    forall (n : nat) (f : ident) (envI : DS_prod SI),
      In f (map n_name G.(nodes)) ->
      (forall x, P_var n envI x) ->
      (forall x, P_var n (envG f envI) x).


  Global Add Parametric Morphism n : (P_var n) with signature
      Oeq (O := DS_prod SI) ==> eq ==> iff as P_var_morph.
  Proof.
    unfold P_var.
    intros ?? H ?.
    now rewrite H.
  Qed.

  Global Add Parametric Morphism n : (P_vars n) with signature
      Oeq (O := DS_prod SI) ==> eq ==> iff as P_vars_morph.
  Proof.
    unfold P_vars.
    setoid_rewrite Forall_forall.
    intros ?? H ?.
    now setoid_rewrite H.
  Qed.

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
    eauto using is_ncons_S.
  Qed.

  Lemma P_vars_S :
    forall n env xs,
      P_vars (S n) env xs ->
      P_vars n env xs.
  Proof.
    unfold P_vars.
    eauto using Forall_impl, P_var_S.
  Qed.

  Lemma P_vars_O :
    forall env xs,
      P_vars O env xs.
  Proof.
    induction xs; constructor; simpl; auto.
  Qed.

  Lemma P_vars_app_l :
    forall n env xs ys,
      P_vars n env (xs ++ ys) ->
      P_vars n env ys.
  Proof.
    unfold P_vars.
    eauto using Forall_app_weaken.
  Qed.

  Lemma P_exps_k : forall n es ins envI bs env k,
      P_exps (P_exp n ins envI bs env) es k ->
      is_ncons n (get_nth k errTy (denot_exps G ins es envG envI bs env)).
  Proof.
    induction es as [| e es]; intros * Hp (* Hwl Hr *); inv Hp; simpl_Forall.
    - setoid_rewrite denot_exps_eq.
      setoid_rewrite nprod_app_nth1; eauto using Is_free_left_list.
    - setoid_rewrite denot_exps_eq.
      setoid_rewrite nprod_app_nth2; eauto using Is_free_left_list.
  Qed.

  Lemma P_expss_k : forall n (ess : list (enumtag * list exp)) ins envI bs env k m,
      Forall (fun es => length (annots (snd es)) = m) ess ->
      Forall (fun es => P_exps (P_exp n ins envI bs env) es k) (map snd ess) ->
      forall_nprod (fun np => is_ncons n (get_nth k errTy np))
        (denot_expss G ins ess m envG envI bs env).
  Proof.
    intros * Hl Hp.
    induction ess as [|[j es] ess]. now simpl.
    rewrite denot_expss_eq.
    inv Hl. inv Hp.
    simpl (snd _) in *.
    rewrite annots_numstreams in *.
    unfold eq_rect; cases; try congruence.
    apply (@forall_nprod_app _ _ 1).
    - apply P_exps_k; auto.
    - apply IHess; auto.
  Qed.

  (* TODO: inutile? *)
  Lemma P_exps_impl' :
    forall (Q_exp P_exp : exp -> nat -> Prop) es k,
      P_exps Q_exp es k ->
      P_exps (fun e k => Q_exp e k -> P_exp e k) es k ->
      P_exps P_exp es k.
  Proof.
    intros * Hpq Hq.
    induction Hpq; inv Hq; constructor; auto; lia.
  Qed.

  Lemma P_exps_impl :
    forall Q (P_exp : exp -> nat -> Prop) es k,
      Forall Q es ->
      P_exps (fun e k => Q e -> P_exp e k) es k ->
      P_exps P_exp es k.
  Proof.
    induction es as [|a es]; intros * Hf Hp; simpl_Forall. inv Hp.
    destruct (Nat.lt_ge_cases k (numstreams a)); inv Hp; auto using P_exps.
  Qed.

  (* TODO: semble foireux *)
  Lemma Forall_P_exps' :
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

  Lemma Forall_P_exps :
    forall (P_exp : exp -> nat -> Prop) es k,
      (* hyothèse de récurrence typique avec exp_ind2 *)
      Forall (fun e => forall k, k < numstreams e -> P_exp e k) es ->
      k < list_sum (map numstreams es) ->
      P_exps P_exp es k.
  Proof.
    induction es as [|e es]; simpl; intros * Hf Hk. inv Hk.
    inv Hf.
    destruct (Nat.lt_ge_cases k (numstreams e)); auto using P_exps.
    constructor 2; auto.
    apply IHes; auto; lia.
  Qed.

  Lemma Forall_P_expss :
    forall (P_exp : exp -> nat -> Prop) (ess : list (enumtag * list exp)) k m,
      (* hyothèse de récurrence typique avec exp_ind2 *)
      Forall (Forall (fun e => forall k, k < numstreams e -> P_exp e k)) (map snd ess) ->
      Forall (fun es => length (annots (snd es)) = m) ess ->
      k < m ->
      Forall (fun es => P_exps P_exp es k) (map snd ess).
  Proof.
    intros.
    simpl_Forall; subst.
    apply Forall_P_exps; auto.
    now rewrite <- annots_numstreams.
  Qed.


  Ltac solve_err :=
    try (
        repeat (rewrite get_nth_const; [|simpl; cases]);
        now (apply is_ncons_DS_const || apply is_consn_DS_const)
      ).

  Lemma exp_n :
    forall Γ n e ins envI bs env k,
      is_ncons n bs ->
      P_vars n envI ins ->
      k < numstreams e ->
      wl_exp G e ->
      wx_exp Γ e ->
      (forall x cx, HasCaus Γ x cx -> P_var n env cx) ->
      P_exp n ins envI bs env e k.
  Proof.
    intros * Hbs Hins.
    intros Hk Hwl Hwx Hn.
    (* cas des variables, mutualisé *)
    assert (forall x, IsVar Γ x -> is_ncons n (denot_var ins envI env x)) as Hvar.
    { unfold P_vars, P_var in Hins.
      rewrite Forall_forall in Hins.
      intros.
      unfold denot_var. cases_eqn HH.
      * (* in *)
        rewrite mem_ident_spec in HH.
        now apply Hins.
      * (* out *)
        eapply Hn, HasCausRefl; auto.
    }
    revert dependent k.
    induction e using exp_ind2; simpl; intros.
    (* cas restreints : *)
    all: unfold P_exp; try (rewrite denot_exp_eq; now solve_err).
    - (* Econst *)
      assert (k = O) by lia; subst.
      rewrite denot_exp_eq.
      now apply is_ncons_sconst.
    - (* Evar *)
      assert (k = O) by lia; subst.
      rewrite denot_exp_eq.
      inv Hwx. now apply Hvar.
    - (* Eunop *)
      assert (k = O) by lia; subst.
      revert IHe.
      rewrite denot_exp_eq.
      unfold P_exp.
      gen_sub_exps.
      rewrite <- length_typeof_numstreams.
      inv Hwl. inv Hwx.
      intros. cases_eqn HH; solve_err.
      apply is_ncons_sunop.
      unshelve eapply (IHe _ _ O); auto.
    - (* Ebinop *)
      assert (k = O) by lia; subst.
      revert IHe1 IHe2.
      rewrite denot_exp_eq.
      unfold P_exp.
      gen_sub_exps.
      rewrite <- 2 length_typeof_numstreams.
      inv Hwl. inv Hwx.
      intros. cases_eqn HH; solve_err.
      apply is_ncons_sbinop.
      unshelve eapply (IHe1 _ _ O); auto.
      unshelve eapply (IHe2 _ _ O); auto.
    - (* Efby *)
      rewrite denot_exp_eq; simpl.
      unfold eq_rect.
      cases; solve_err.
      erewrite lift2_nth; cases.
      inv Hwl. apply Forall_impl_inside with (P := wl_exp _) in H0,H; auto.
      inv Hwx. apply Forall_impl_inside with (P := wx_exp _) in H0,H; auto.
      rewrite annots_numstreams in *.
      apply is_ncons_fby; apply P_exps_k, Forall_P_exps; auto; congruence.
    - (* Ewhen *)
      rewrite denot_exp_eq; simpl.
      unfold eq_rect.
      cases; solve_err.
      erewrite llift_nth; cases.
      inv Hwl. apply Forall_impl_inside with (P := wl_exp _) in H; auto.
      inv Hwx. apply Forall_impl_inside with (P := wx_exp _) in H; auto.
      apply is_ncons_swhen; auto.
      now apply P_exps_k, Forall_P_exps.
    - (* Emerge *)
      destruct x, a.
      inv Hwl.
      inv Hwx.
      rewrite <- Forall_map in *.
      rewrite <- Forall_concat in *.
      apply Forall_impl_inside with (P := wl_exp _) in H; auto.
      apply Forall_impl_inside with (P := wx_exp _) in H; auto.
      rewrite Forall_concat in H.
      eapply Forall_P_expss, P_expss_k in H; eauto.
      rewrite denot_exp_eq; simpl.
      erewrite lift_nprod_nth; auto.
      apply is_ncons_smerge; auto.
      unfold eq_rect_r, eq_rect, eq_sym; cases.
      apply forall_nprod_lift; eauto.
    - (* Ecase *)
      destruct a.
      inv Hwl.
      inv Hwx.
      rewrite <- Forall_map in *.
      rewrite <- Forall_concat in *.
      apply Forall_impl_inside with (P := wl_exp _) in H; auto.
      apply Forall_impl_inside with (P := wx_exp _) in H; auto.
      rewrite Forall_concat in H.
      eapply Forall_P_expss, P_expss_k in H; eauto.
      take (wl_exp G e) and apply IHe with (k := O) in it as Hc; auto; try lia.
      destruct d; rewrite denot_exp_eq; simpl.
      + (* défaut *)
        apply Forall_impl_inside with (P := wl_exp _) in H0; auto.
        apply Forall_impl_inside with (P := wx_exp _) in H0; auto.
        eapply Forall_P_exps with (k := k), P_exps_k in H0; auto.
        2:{ rewrite <- annots_numstreams, H13; auto. }
        revert H0 H Hc.
        unfold P_exp.
        gen_sub_exps.
        cases; try congruence; intros; solve_err.
        rewrite curry_nprod_simpl.
        setoid_rewrite lift_nprod_nth; auto.
        rewrite uncurry_nprod_simpl.
        apply is_ncons_scase_def; auto.
        * rewrite lift_hd, (nprod_hd_app O).
          unfold eq_rect; cases; eauto.
        * rewrite lift_tl.
          apply forall_nprod_lift.
          unfold eq_rect_r, eq_rect, eq_sym; cases.
          apply forall_nprod_tl, (@forall_nprod_app _ _ 1); auto.
      + (* total *)
        revert Hc H.
        unfold P_exp.
        gen_sub_exps.
        cases; try congruence; intros; solve_err.
        erewrite lift_nprod_nth; auto.
        apply is_ncons_scase; auto.
        unfold eq_rect_r, eq_rect, eq_sym; cases.
        apply forall_nprod_lift; eauto.
    - (* Eapp *)
      rewrite denot_exp_eq; simpl.
      unfold eq_rect.
      inv Hwl. apply Forall_impl_inside with (P := wl_exp _) in H; auto.
      inv Hwx. apply Forall_impl_inside with (P := wx_exp _) in H; auto.
      destruct (find_node f G) eqn:Hfind; cases; solve_err.
      apply forall_nprod_k; auto.
      apply forall_np_of_env, (Hnode n); intros; eauto using find_node_name.
      unfold P_var. rewrite PROJ_simpl.
      apply forall_env_of_np; solve_err.
      apply k_forall_nprod_def with (d := errTy); intros; solve_err.
      now apply P_exps_k, Forall_P_exps.
  Qed.

  Lemma exps_n :
    forall Γ n es ins envI bs env k,
      is_ncons n bs ->
      P_vars n envI ins ->
      k < list_sum (map numstreams es) ->
      Forall (wl_exp G) es ->
      Forall (wx_exp Γ) es ->
      (forall x cx, HasCaus Γ x cx -> P_var n env cx) ->
      P_exps (P_exp n ins envI bs env) es k.
  Proof.
    induction es as [| e es]; simpl; intros * Hbs Hins Hk Hwl Hwx Hn.
    inv Hk.
    simpl_Forall.
    destruct (Nat.lt_ge_cases k (numstreams e)).
    - constructor; eauto using exp_n.
    - constructor 2; auto. apply IHes; auto; lia.
  Qed.

  Lemma exp_S :
    forall Γ n e ins envI bs env k,
      is_ncons (S n) bs ->
      P_vars (S n) envI ins ->
      k < numstreams e ->
      (forall x, Is_free_left Γ x k e -> P_var (S n) env x) ->
      wl_exp G e ->
      wx_exp Γ e ->
      (forall x cx, HasCaus Γ x cx -> P_var n env cx) ->
      P_exp (S n) ins envI bs env e k.
  Proof.
    intros * Hbs Hins Hk Hdep Hwl Hwx Hn.
    (* cas des variables, mutualisé *)
    assert (Hvar : forall x cx,
               HasCaus Γ x cx ->
               P_var (S n) env cx ->
               is_ncons (S n) (denot_var ins envI env x)).
    { unfold P_vars, P_var in Hins.
      rewrite Forall_forall in Hins.
      intros x cx Hc Hx.
      unfold denot_var. cases_eqn HH.
      + (* in *)
        rewrite mem_ident_spec in HH.
        now apply Hins.
      + (* out *)
        apply HasCausInj in Hc; subst; auto.
    }
    assert (Hwl' := Hwl).
    assert (Hwx' := Hwx).
    revert Hwl Hwx.
    eapply exp_causal_ind with (16 := Hdep); eauto.
    all: clear dependent e; clear k; intros.
    (* cas restreints : *)
    all: unfold P_exp; try (rewrite denot_exp_eq; now solve_err).
    - (* Econst *)
      rewrite denot_exp_eq.
      now apply is_ncons_sconst.
    - (* Evar *)
      setoid_rewrite denot_exp_eq.
      eapply Hvar; eauto.
    - (* Eunop *)
      revert H.
      rewrite denot_exp_eq.
      unfold P_exp.
      gen_sub_exps.
      rewrite <- length_typeof_numstreams.
      inv Hwl. inv Hwx.
      intros. cases_eqn HH; solve_err.
      apply is_ncons_sunop; auto.
    - (* Ebinop *)
      revert H H0.
      rewrite denot_exp_eq.
      unfold P_exp.
      gen_sub_exps.
      rewrite <- 2 length_typeof_numstreams.
      inv Hwl. inv Hwx.
      intros. cases_eqn HH; solve_err.
      apply is_ncons_sbinop; auto.
    - (* Efby *)
      rewrite denot_exp_eq; simpl.
      unfold eq_rect.
      cases; solve_err.
      erewrite lift2_nth; cases.
      inv Hwl. apply P_exps_impl in H0; auto.
      inv Hwx. apply P_exps_impl in H0; auto.
      apply is_ncons_S_fby; apply P_exps_k; auto.
      eapply exps_n; eauto using is_ncons_S, P_vars_S.
    - (* Ewhen *)
      rewrite denot_exp_eq; simpl.
      unfold eq_rect.
      cases; simpl in H; solve_err.
      inv Hwl. apply P_exps_impl in H0; auto.
      inv Hwx. apply P_exps_impl in H0; auto.
      rewrite annots_numstreams in *.
      erewrite llift_nth; try congruence.
      eapply is_ncons_swhen with (n := S n); eauto using P_exps_k.
    - (* Emerge *)
      destruct ann0.
      rewrite denot_exp_eq; simpl.
      erewrite lift_nprod_nth; auto.
      eapply is_ncons_smerge with (n := S n); eauto.
      apply forall_nprod_lift.
      unfold eq_rect_r, eq_rect, eq_sym; cases.
      apply forall_denot_expss.
      unfold eq_rect.
      inv Hwl. inv Hwx.
      simpl_Forall; cases; solve_err.
      apply P_exps_k with (n := S n).
      apply P_exps_impl, P_exps_impl in H2; auto.
    - (* Ecase *)
      destruct ann0.
      inv Hwl. inv Hwx.
      take (Forall (fun _ => length _ = _) es) and
        eapply P_expss_k with (n := S n) in it as Hess; eauto.
      2:{ simpl_Forall.
          eapply P_exps_impl in H1; eauto.
          eapply P_exps_impl in H1; eauto. }
      destruct d; rewrite denot_exp_eq; simpl.
      + (* défaut *)
        apply P_exps_impl, P_exps_impl, P_exps_k in H2; auto.
        revert H0 H2 Hess.
        unfold P_exp.
        gen_sub_exps.
        cases; intros; solve_err.
        rewrite curry_nprod_simpl.
        setoid_rewrite lift_nprod_nth; auto.
        rewrite uncurry_nprod_simpl.
        apply is_ncons_scase_def with (n := S n); auto.
        * rewrite lift_hd, (nprod_hd_app O).
          unfold eq_rect; cases; eauto.
        * rewrite lift_tl.
          apply forall_nprod_lift.
          unfold eq_rect_r, eq_rect, eq_sym; cases.
          apply forall_nprod_tl, (@forall_nprod_app _ _ 1); auto.
      + (* total *)
        revert H0 Hess.
        unfold P_exp.
        gen_sub_exps.
        cases; intros; solve_err.
        erewrite lift_nprod_nth; auto.
        eapply is_ncons_scase with (n := S n); auto.
        apply forall_nprod_lift.
        unfold eq_rect_r, eq_rect, eq_sym; cases; eauto.
    - (* Eapp *)
      rewrite denot_exp_eq; simpl in *.
      unfold eq_rect.
      inv Hwl; inv Hwx.
      destruct (find_node f G) eqn:?; cases; solve_err.
      apply forall_nprod_k; auto.
      apply forall_np_of_env, (Hnode (S n)); intros; eauto using find_node_name.
      unfold P_var. rewrite PROJ_simpl.
      apply forall_env_of_np; solve_err.
      apply k_forall_nprod_def with (d := errTy); intros; solve_err.
      rewrite annots_numstreams in *.
      apply P_exps_k; eauto using P_exps_impl.
  Qed.

  Lemma equation_n :
    forall xs es n k ins envI bs,
      let env := FIXP (DS_prod SI) (denot_equation G ins (xs,es) envG envI bs) in
      (forall x, is_ncons n (envI x)) ->
      NoDup (ins ++ xs) ->
      k < length xs ->
      P_exps (P_exp n ins envI bs env) es k ->
      P_var n env (nth k xs xH).
  Proof.
    intros ??????? env Hins Hnd Hk Hes.
    subst env.
    unfold P_var.
    rewrite FIXP_eq, PROJ_simpl, denot_equation_eq.
    unfold denot_var.
    cases_eqn HH.
    erewrite env_of_np_nth; eauto using P_exps_k.
    apply mem_nth_nth; eauto using NoDup_app_r.
  Qed.

  Lemma P_var_input_eq :
    forall Γ ins envI bs e x n,
      wt_equation G Γ e ->
      In x ins ->
      P_vars n envI ins ->
      P_var n (FIXP (DS_prod SI) (denot_equation G ins e envG envI bs)) x.
  Proof.
    intros * Hwt Hin Hins.
    unfold P_vars, P_var in *.
    rewrite FIXP_eq, PROJ_simpl.
    erewrite denot_equation_input, Forall_forall, <- PROJ_simpl in *;
      eauto using wt_equation_wl_equation.
  Qed.

  Lemma P_var_input_node :
    forall nd envI x n,
      wt_node G nd ->
      In x (map fst (n_in nd)) ->
      P_vars n envI (map fst (n_in nd)) ->
      P_var n (FIXP (DS_prod SI) (denot_node G nd envG envI)) x.
  Proof.
    intros * Hwt Hx Hins.
    unfold denot_node, denot_block.
    destruct Hwt as (?&?&?& Hwt).
    cases.
    { autorewrite with cpodb.
      inv Hwt; try congruence; eauto using P_var_input_eq. }
    (* cas restreints *)
    all: rewrite FIXP_eq; simpl; eauto using P_vars_In.
  Qed.

  Lemma P_vars_weaken :
    forall n l env,
      (forall x, P_var n env x) ->
      P_vars n env l.
  Proof.
    unfold P_vars.
    setoid_rewrite Forall_forall.
    auto.
  Qed.

  Lemma is_ncons_bss :
    forall n (env : DS_prod SI) l,
      (forall x, (* on pourrait affiner *)
          is_ncons n (env x)) ->
      is_ncons n (bss l env).
  Proof.
    intros * Hx.
    induction l as [|?[]].
    - apply is_ncons_DS_const.
    - simpl. unfold AC. autorewrite with cpodb.
      unfold is_ncons. cases.
      rewrite nrem_map.
      apply is_cons_map, Hx.
    - simpl. unfold AC. autorewrite with cpodb.
      apply is_ncons_zip; auto.
      unfold is_ncons. cases.
      rewrite nrem_map.
      apply is_cons_map, Hx.
  Qed.

  Lemma denot_S :
    forall nd envI n,
      wt_node G nd ->
      node_causal nd ->
      (forall x, P_var (S n) envI x) ->
      P_vars n (FIXP _ (denot_node G nd envG envI)) (map fst nd.(n_out)) ->
      P_vars (S n) (FIXP _ (denot_node G nd envG envI)) (map fst nd.(n_out)).
  Proof.
    intros * Hwt Hcaus Hins Hn.
    destruct nd.(n_block) eqn:Hnd.
    (* cas restreints *)
    2-5: unfold denot_node, denot_block; rewrite Hnd, FIXP_eq;
      unfold P_vars; rewrite Forall_forall; now auto.
    eapply P_vars_app_l.
    rewrite <- map_app, <- idcaus_map.
    rewrite <- (@app_nil_r (ident*ident)) at 1.
    assert (idcaus_of_locals (n_block nd) = []) as <- by now rewrite Hnd.
    eapply node_causal_ind; auto.
    - unfold P_vars. now intros ?? ->.
    - now red.
    - intros x xs' [Hx|Hx] Hxs' Hdep.
      2: { rewrite Hnd in *; inv Hx. }
      constructor; auto.
      rewrite idcaus_app, map_app, in_app_iff, 2 idcaus_map in Hx.
      destruct Hx as [|Hx]; eauto using P_var_input_node, P_vars_weaken.
      (* TODO: nettoyer *)

      destruct (n_defd nd) as (ys & Hvd & Hperm).
      destruct Hwt as (?&?&?& Hwt).
      unfold denot_node, denot_block in *.
      rewrite Hnd in *.
      inv Hvd.
      destruct e as (xs, es); simpl in *.
      rewrite <- Hperm in Hx.
      apply In_nth with (d := xH) in Hx as (k & Hlen & Hnth); subst.
      autorewrite with cpodb; simpl.
      apply equation_n with (n := S n); auto.
      { unfold idents. rewrite Hperm, <- map_app; apply node_NoDup. }
      eapply Pexp_Pexps with
        (Γ := (senv_of_inout (n_in nd ++ n_out nd)))
        (P_var := P_var (S n) (FIXP _ (denot_equation G (map fst (n_in nd)) (xs, es) envG envI _))); eauto.
      + inv Hwt.  assert(Wte := H4). destruct H4 as [Hwt].
        apply Forall_wt_exp_wx_exp in Hwt as Hwx.
        apply Forall_wt_exp_wl_exp in Hwt as Hwl.
        apply Forall_forall.
        intros e Hin k' Hk' Hdp.
        pose proof (Forall_In _ _ _ Hwx Hin) as Hwxe.
        pose proof (Forall_In _ _ _ Hwl Hin) as Hwle.
        pose proof (Forall_In _ _ _ Hwt Hin) as Hwte.
        eapply exp_S; eauto using P_vars_weaken.
        { apply is_ncons_bss; auto. }
        (* TODO: lemma pour ça : *)
        intros x cx Hc.
        apply HasCausInj in Hc as ?; subst.
        eapply or_introl, idcaus_of_senv_In in Hc.
        rewrite idcaus_of_senv_inout in Hc.
        apply In_list_pair_l in Hc.
        rewrite map_fst_idcaus, map_app, in_app_iff in Hc.
        destruct Hc as [Hc|]; eauto using P_vars_In, P_var_input_eq, P_vars_S, P_vars_weaken.
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
    forall nd envI n,
      wt_node G nd ->
      node_causal nd ->
      (forall x, P_var n envI x) ->
      P_vars n (FIXP _ (denot_node G nd envG envI)) (map fst nd.(n_out)).
  Proof.
    induction n; intros Hwt Hcaus Hins.
    - apply P_vars_O.
    - apply denot_S; auto using is_ncons_S, P_var_S.
  Qed.

  (* Avec l'hypothèse [restr_node] actuelle, toutes les variables du nœud
     sont définies dans une seule équation et [denot_equation] associe
     [DS_const err] aux autres variables. On peut donc en déduire que
     tous les flots dans le point fixe de denot_equation sont P_vars n.
   *)
  Lemma P_vars_node_all :
    forall nd envI n,
      wt_node G nd ->
      (forall x, P_var n envI x) ->
      P_vars n (FIXP _ (denot_node G nd envG envI)) (map fst nd.(n_out)) ->
      forall x, P_var n (FIXP _ (denot_node G nd envG envI)) x.
  Proof.
    intros * Hwt Hins Hn x.
    destruct (mem_ident x (map fst (n_out nd))) eqn:Hout.
    { rewrite mem_ident_spec in Hout. eapply Forall_In in Hn; eauto. }
    rewrite FIXP_eq.
    destruct (n_defd nd) as (ys & Hvd & Hperm).
    revert Hvd.
    unfold denot_node, denot_block.
    cases; intros; inv Hvd.
    destruct e as (xs,es); simpl in *.
    unfold P_var.
    autorewrite with cpodb.
    rewrite denot_equation_eq.
    unfold denot_var.
    cases.
    - apply Hins.
    - rewrite <- Hperm, mem_ident_false in Hout.
      rewrite env_of_np_eq.
      cases_eqn HH; try apply is_ncons_DS_const.
      apply mem_nth_In in HH; contradiction.
  Qed.

  Corollary denot_n_all_vars :
    forall nd envI n,
      wt_node G nd ->
      node_causal nd ->
      (forall x, P_var n envI x) ->
      forall x, P_var n (FIXP _ (denot_node G nd envG envI)) x.
  Proof.
    intros.
    apply P_vars_node_all; auto using denot_n.
  Qed.

  End Node_n.


  (** Using the well-ordered property of programs, show that all nodes
      receiving streams of length n outputs streams of length n. *)

  Theorem denot_global_n :
    forall n G envI,
      wt_global G ->
      Forall node_causal (nodes G) ->
      (forall x, P_var n envI x) ->
      forall f x, P_var n (denot_global G f envI) x.
  Proof.
    intros * Hwt Hcaus Hins f x.
    assert (Ordered_nodes G) as Hord.
    now apply wl_global_Ordered_nodes, wt_global_wl_global.
    unfold denot_global.
    rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl, denot_global_eq.
    destruct (find_node f G) as [nd|] eqn:Hfind.
    - remember (FIXP (Dprodi FI) (denot_global_ G)) as envG eqn:HF.
      (* pour réussir l'induction sur (nodes G), on doit relâcher la
         contrainte sur envG : en gardant la définition HF actuelle, on
         ne peut pas espérer réécrire denot_node2_cons sous le point fixe *)
      assert (forall f nd envI,
          find_node f G = Some nd ->
          envG f envI == FIXP _ (denot_node G nd envG envI)) as HenvG.
      { intros * Hf; subst.
        now rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl, denot_global_eq, Hf at 1. }
      (* maintenant HenvG contient tout ce qu'on doit savoir sur envG *)
      clear HF.
      (* il faut généraliser à tous les nœuds *)
      revert Hins HenvG Hfind. revert envI envG n f x nd.
      destruct G as [tys exts nds]; simpl in *.
      induction nds as [|a nds]; simpl; intros. inv Hfind.
      inv Hcaus.
      destruct (ident_eq_dec (n_name a) f); subst.
      + (* cas intéressant, où on utilise denot_n_all_vars *)
        rewrite find_node_now in Hfind; inv Hfind; auto.
        rewrite <- denot_node_cons;
          eauto using find_node_not_Is_node_in, find_node_now.
        apply denot_n_all_vars; auto using wt_global_uncons.
        intros m f envI2 Hin HI2 y.
        apply name_find_node in Hin as (ndf & Hfind).
        eapply find_node_uncons with (nd := nd) in Hfind as ?; auto.
        rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
        apply IHnds with (f := f); auto.
        eauto using wt_global_cons.
        eauto using Ordered_nodes_cons.
        (* montrons que HenvG tient toujours *)
        intros f' ndf' envI' Hfind'.
        eapply find_node_uncons with (nd := nd) in Hfind' as ?; auto.
        rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
      + rewrite find_node_other in Hfind; auto.
        rewrite <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
        apply IHnds with (f := f); auto.
        eauto using wt_global_cons.
        eauto using Ordered_nodes_cons.
        (* montrons que HenvG tient toujours *)
        intros f' ndf' envI' Hfind'.
        eapply find_node_uncons with (nd := a) in Hfind' as ?; auto.
        rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
    - unfold P_var, env_err_ty.
      cbn; eauto using is_ncons_DS_const.
  Qed.

  End Top.

(** Maintenant on passe à l'infini *)

Lemma infinite_P_vars :
  forall env, all_infinite env <-> (forall n x, P_var n env x).
Proof.
  intro env.
  unfold P_var, all_infinite.
  setoid_rewrite PROJ_simpl.
  split; eauto using nrem_inf, inf_nrem.
Qed.

Theorem denot_inf :
  forall (HasCausInj : forall Γ x cx, HasCaus Γ x cx -> x = cx),
  forall (G : global) envI,
    wt_global G ->
    Forall node_causal (nodes G) ->
    all_infinite envI ->
    forall f, all_infinite (denot_global G f envI).
Proof.
  intros.
  rewrite infinite_P_vars in *.
  intro.
  eapply denot_global_n; eauto.
Qed.

(** Une fois l'infinité des flots obtenue, on peut l'utiliser pour
    prouver l'infinité des expression. *)
Lemma infinite_exp :
  forall G ins envI (envG : Dprodi FI) bs env,
    (forall envI f, all_infinite envI -> all_infinite (envG f envI)) ->
    infinite bs ->
    all_infinite envI ->
    all_infinite env ->
    forall e,
    forall_nprod (@infinite _) (denot_exp G ins e envG envI bs env).
Proof.
  intros * HG Hbs Hins Hinf.
  assert (forall x, infinite (denot_var ins envI env x)) as Hvar.
  { unfold all_infinite, denot_var in *. intro. cases; eauto. }
  induction e using exp_ind2; intros; simpl; setoid_rewrite denot_exp_eq.
  (* cas restreints : *)
  all: try (simpl; now eauto using forall_nprod_const, DS_const_inf).
  - (* Econst *)
    apply sconst_inf; auto.
  - (* Eunop *)
    revert IHe.
    gen_sub_exps.
    intros; cases; simpl; eauto using sunop_inf, DS_const_inf.
  - (* Ebinop *)
    revert IHe1 IHe2.
    gen_sub_exps.
    intros; cases; simpl; eauto using sbinop_inf, DS_const_inf.
  - (* Efby *)
    apply forall_denot_exps in H, H0.
    unfold eq_rect.
    cases; eauto using forall_nprod_const, DS_const_inf.
    eapply forall_nprod_lift2; eauto using fby_inf; cases.
  - (* Ewhen *)
    apply forall_denot_exps in H.
    unfold eq_rect.
    cases; eauto using forall_nprod_const, DS_const_inf.
    eapply forall_nprod_llift; eauto using swhen_inf; cases.
  - (* Emerge *)
    destruct x, a.
    eapply forall_lift_nprod; eauto using smerge_inf.
    unfold eq_rect_r, eq_rect, eq_sym; cases.
    apply forall_denot_expss.
    unfold eq_rect.
    simpl_Forall.
    cases; eauto using forall_nprod_const, DS_const_inf, forall_denot_exps.
  - (* Ecase *)
    destruct a as [tys].
    eapply Forall_impl in H.
    2:{ intros ? HH. apply forall_denot_exps, HH. }
    eapply forall_forall_denot_expss with (n := length tys) in H as Hess;
      eauto using DS_const_inf.
    destruct d.
    + (* défaut *)
      apply forall_denot_exps in H0 as Hd.
      revert Hess IHe Hd.
      gen_sub_exps.
      unfold eq_rect_r, eq_rect, eq_sym; cases; intros;
        eauto using forall_nprod_const, DS_const_inf.
      rewrite curry_nprod_simpl.
      eapply forall_lift_nprod.
      { intros; rewrite uncurry_nprod_simpl.
        apply scase_def_inf; eauto using forall_nprod_tl.
        now apply forall_nprod_hd. }
      apply forall_nprod_app with (n := 1); auto.
    + (* total *)
      revert Hess IHe.
      gen_sub_exps.
      unfold eq_rect_r; cases; intros; eauto using forall_nprod_const, DS_const_inf.
      eapply forall_lift_nprod; eauto using scase_inf.
      unfold eq_rect, eq_sym; cases.
  - (* Eapp *)
    apply forall_denot_exps in H.
    unfold eq_rect.
    cases; eauto using forall_nprod_const, DS_const_inf.
    apply forall_np_of_env, HG; intro.
    apply forall_env_of_np; eauto using DS_const_inf.
Qed.

Corollary infinite_exps :
  forall G ins (envG : Dprodi FI) envI bs env,
    (forall envI f, all_infinite envI -> all_infinite (envG f envI)) ->
    infinite bs ->
    all_infinite envI ->
    all_infinite env ->
    forall es,
    forall_nprod (@infinite _) (denot_exps G ins es envG envI bs env).
Proof.
  induction es; simpl; auto.
  setoid_rewrite denot_exps_eq.
  auto using forall_nprod_app, infinite_exp.
Qed.

Corollary infinite_expss :
  forall G ins (envG : Dprodi FI) envI bs env,
    (forall envI f, all_infinite envI -> all_infinite (envG f envI)) ->
    infinite bs ->
    all_infinite envI ->
    all_infinite env ->
    forall I (ess : list (I * list exp)) n,
      forall_nprod (forall_nprod (@infinite _)) (denot_expss G ins ess n envG envI bs env).
Proof.
  induction ess as [| (i,es) ess]; intros.  { now simpl. }
  setoid_rewrite denot_expss_eq.
  unfold eq_rect.
  cases; eauto using forall_nprod_const, DS_const_inf.
  eapply (@forall_nprod_app _ _ 1); eauto using infinite_exps.
Qed.

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
       (Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord)
<: LDENOTINF Ids Op OpAux Cks Senv Syn Typ LCA Lord Den.
  Include LDENOTINF Ids Op OpAux Cks Senv Syn Typ LCA Lord Den.
End LDenotInfFun.
