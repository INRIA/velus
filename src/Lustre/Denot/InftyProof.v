From Coq Require Import String Morphisms.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import Environment.
From Velus Require Import FunctionalEnvironment.
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

  Fact idcaus_map :
    forall l : list (ident * (type * clock * ident)),
      map snd (idcaus l) = map fst l.
  Proof.
    intros.
    rewrite <- map_fst_senv_of_ins.
    unfold idcaus, senv_of_ins.
    rewrite 2 map_map.
    apply map_ext_in_iff.
    intros (x & (ty&c) &cx) Hin; simpl.
    apply symmetry, HasCausInj with (Γ := senv_of_ins l).
    econstructor.
    apply in_map_iff; esplit; split; eauto.
    all: eauto.
  Qed.

  Fact idcaus_of_decls_map :
    forall l : list (ident * (type * clock * ident * option ident)),
      (* hypothèse obtenue gâce au global, qui est [nolocal] *)
      Forall (fun '(_, (_, _, _, o)) => o = None) l ->
      map fst l = map snd (idcaus_of_decls l).
  Proof.
    intros.
    unfold idcaus_of_decls, idcaus_of_senv.
    unfold senv_of_decls.
    rewrite map_app, 2 map_map, map_filter_map, map_filter_nil, app_nil_r.
    2: simpl_Forall; subst; auto.
    apply map_ext_in_iff.
    intros (x & ([]&?) &cx) Hin; simpl.
    apply HasCausInj with (Γ := senv_of_decls l).
    econstructor.
    apply in_map_iff; esplit; split; eauto.
    all: eauto.
  Qed.

  Fact map_fst_idcaus_decls : forall l,
      (* hypothèse obtenue gâce au global, qui est [nolocal] *)
      Forall (fun '(_, (_, _, _, o)) => o = None) l ->
      map fst (idcaus_of_senv (senv_of_decls l)) = map fst l.
  Proof.
    intros * Hf.
    unfold idcaus_of_senv, senv_of_decls.
    rewrite map_filter_nil, app_nil_r. 2:simpl_Forall; subst; auto.
    erewrite 2 map_map, map_ext; eauto. intros; destruct_conjs; auto.
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

  Lemma P_vars_weaken :
    forall n l env,
      (forall x, P_var n env x) ->
      P_vars n env l.
  Proof.
    unfold P_vars.
    setoid_rewrite Forall_forall.
    auto.
  Qed.

  Lemma P_exps_k : forall n es ins envI bs env k,
      P_exps (P_exp n ins envI bs env) es k ->
      is_ncons n (get_nth k errTy (denot_exps G ins es envG envI bs env)).
  Proof.
    induction es as [| e es]; intros * Hp (* Hwl Hr *); inv Hp; simpl_Forall.
    - setoid_rewrite denot_exps_eq.
      setoid_rewrite nprod_app_nth1; eauto using Is_used_inst_list.
    - setoid_rewrite denot_exps_eq.
      setoid_rewrite nprod_app_nth2; eauto using Is_used_inst_list.
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
    apply forall_nprod_cons.
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

  Lemma is_ncons_sbools_ofs :
    forall n m (np : nprod m),
      forall_nprod (is_ncons n) np ->
      is_ncons n (sbools_ofs np).
  Proof.
    clear.
    induction m; intros * Hf; simpl.
    - apply is_ncons_DS_const.
    - apply forall_nprod_inv in Hf as [].
      autorewrite with cpodb.
      apply is_ncons_zip; auto.
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
        unfold eq_rect_r, eq_sym, eq_rect.
        cases; try congruence; intros; solve_err.
        setoid_rewrite lift_nprod_nth with (F := scase_defv _ _); auto.
        rewrite @lift_cons.
        apply is_ncons_scase_def, forall_nprod_cons, forall_nprod_lift; eauto.
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
      inv Hwl. apply Forall_impl_inside with (P := wl_exp _) in H, H0; auto.
      inv Hwx. apply Forall_impl_inside with (P := wx_exp _) in H, H0; auto.
      destruct (find_node f G) eqn:Hfind; cases; solve_err.
      apply forall_nprod_k; auto.
      apply forall_np_of_env; intro.
      apply is_ncons_sreset; intros.
      + apply Hnode; eauto using find_node_name.
      + apply is_ncons_sbools_ofs.
        apply k_forall_nprod_def with (d := errTy); intros; solve_err.
        now apply P_exps_k, Forall_P_exps.
      + apply forall_env_of_np; solve_err.
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
      (forall x, Is_used_inst Γ x k e -> P_var (S n) env x) ->
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
        setoid_rewrite lift_nprod_nth with (F := scase_defv _ _); auto.
        unfold eq_rect_r, eq_sym, eq_rect; cases.
        rewrite @lift_cons.
        apply is_ncons_scase_def with (n := S n),
            forall_nprod_cons, forall_nprod_lift; eauto.
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
      apply forall_np_of_env; intro.
      apply is_ncons_sreset with (n := S n); intros.
      + apply Hnode; eauto using find_node_name.
      + apply is_ncons_sbools_ofs.
        apply k_forall_nprod_def with (d := errTy); intros; solve_err.
        rewrite annots_numstreams in *.
        apply P_exps_k; eauto using P_exps_impl.
      + apply forall_env_of_np; solve_err.
        apply k_forall_nprod_def with (d := errTy); intros; solve_err.
        rewrite annots_numstreams in *.
        apply P_exps_k; eauto using P_exps_impl.
  Qed.

  Corollary exps_S :
    forall Γ n es ins envI bs env k,
      is_ncons (S n) bs ->
      P_vars (S n) envI ins ->
      k < list_sum (map numstreams es) ->
      (forall x, Is_used_inst_list Γ x k es -> P_var (S n) env x) ->
      Forall (wl_exp G) es ->
      Forall (wx_exp Γ) es ->
      (forall x cx, HasCaus Γ x cx -> P_var n env cx) ->
      P_exps (P_exp (S n) ins envI bs env) es k.
  Proof.
    induction es as [| e es]; simpl; intros; try lia; simpl_Forall.
    destruct (Nat.lt_ge_cases k (numstreams e)).
    - apply P_exps_now; auto.
      eapply exp_S; intros; eauto.
      take (forall x, _ -> _) and apply it; left; auto.
    - apply P_exps_later; auto.
      apply IHes; auto; try lia; intros.
      take (forall x, _ -> _) and apply it; right; auto.
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

  (* Si une variable est définie dans un bloc et que tous les flots
     des variables dont elle dépend instantanément sont de taille
     (S n) alors elle peut aussi être calculée sur (S n). *)
  Lemma P_var_inside_blocks :
    forall Γ ins envI bs env blks x n,
      Forall restr_block blks ->
      Forall (wl_block G) blks ->
      Forall (wx_block Γ) blks ->
      P_vars (S n) envI ins ->
      is_ncons (S n) bs ->
      (forall y, P_var n env y) ->
      (forall y, Exists (depends_on Γ x y) blks -> P_var (S n) env y) ->
      Exists (Syn.Is_defined_in (Var x)) blks ->
      P_var (S n) (denot_blocks G ins blks envG envI bs env) x.
  Proof.
    intros * Hr Hwl Hwx Hins Hbs Hn Hdep Hex.
    induction blks as [| blk blks]. inversion Hex.
    rewrite denot_blocks_eq_cons, denot_block_eq.
    inv Hr. inv Hwl. inv Hwx.
    take (restr_block blk) and inv it.
    take (wl_block _ _) and inv it.
    take (wx_block _ _) and inv it.
    take (wl_equation _ _) and inv it.
    take (wx_equation _ _) and inv it.
    unfold P_var.
    rewrite PROJ_simpl, env_of_np_ext_eq.
    destruct (mem_nth xs x) as [k|] eqn:Hmem.
    - apply mem_nth_Some in Hmem as Hk; auto.
      apply mem_nth_error in Hmem.
      rewrite annots_numstreams in *.
      apply P_exps_k.
      eapply exps_S; eauto using P_vars_weaken; try lia.
      intros y Hiuil.
      eapply Hdep, Exists_cons_hd, DepOnEq; eauto.
      eapply HasCausRefl, Forall_forall, nth_error_In; eauto.
    - apply IHblks; auto.
      inv Hex; auto.
      apply mem_nth_nin in Hmem; try tauto.
      now take (Syn.Is_defined_in _ _) and inv it.
  Qed.

  (* Si une variable n'est pas définie dans les blocs,
     alors [denot_blocks] l'associe à [errTy]. *)
  Lemma P_var_outside_blocks :
    forall ins envI bs env blks x n,
      P_vars n envI ins ->
      ~ (Exists (Syn.Is_defined_in (Var x)) blks)  ->
      P_var n (denot_blocks G ins blks envG envI bs env) x.
  Proof.
    intros * Hins Hnex; revert dependent blks.
    induction blks as [| blk blks]; simpl; intros.
    - apply is_ncons_DS_const.
    - rewrite denot_blocks_eq_cons, denot_block_eq.
      cases.
      unfold P_var; rewrite PROJ_simpl, env_of_np_ext_eq.
      cases_eqn Hmem.
      + contradict Hnex; left.
        apply mem_nth_In in Hmem.
        now constructor.
      + apply IHblks; auto.
  Qed.

  (* FIXME: c'est trop ad hoc mais je ne sais pas comment faire autrement *)
  Lemma not_var_not_defined :
    forall x (nd : node) locs blks,
      n_block nd = Blocal (Scope locs blks) ->
      ~ In x (map snd (idcaus (n_in nd) ++ idcaus_of_decls (n_out nd) ++ idcaus_of_locals (n_block nd))) ->
      ~ Exists (Syn.Is_defined_in (FunctionalEnvironment.Var x)) blks.
  Proof.
    intros * Hnd Hnin; contradict Hnin.
    pose proof (n_defd nd) as (vars & Vd & Perm).
    pose proof (n_syn nd) as Noloc.
    pose proof (n_nodup nd) as (_ & Ndl).
    rewrite Hnd in *.
    inv Vd.
    take (VarsDefinedScope _ _ _) and inversion_clear it as [II JJ ? (vars' & Vd' & Perm2)].
    clear II JJ.
    inversion_clear Noloc as [??? Noloc2 (?&? &?)]; inv Noloc2.
    inv Ndl. Syn.inv_scope.
    rewrite 2 map_app, idcaus_map; simpl.
    rewrite map_app, <- 2 idcaus_of_decls_map; auto.
    eapply Exists_VarsDefined_spec in Hnin; eauto.
    2:{ simpl_Forall. eapply NoDupLocals_incl; eauto.
        rewrite Perm2, Perm, map_app, 2 map_fst_senv_of_decls.
        solve_incl_app. }
    rewrite Perm2, Perm, fst_InMembers, map_app, 2 map_fst_senv_of_decls in Hnin.
    rewrite 3 in_app_iff in *; tauto.
  Qed.

  Lemma Is_defined_in_dec :
    forall x blk,
      restr_block blk ->
      Decidable.decidable (Syn.Is_defined_in x blk).
  Proof.
    intros * Hr; inv Hr.
    - (* Beq *)
      destruct x.
      + (* Var *)
        destruct (ListDec.In_decidable decidable_eq_ident x xs) as [Hin|Hnin].
        * left; constructor; auto.
        * right; contradict Hnin; now inv Hnin.
      + (* Last *)
        right; intro HH; inv HH.
  Qed.

  (** L'étape d'induction pour P_var sur les nœuds, qui utilise [exp_S].
      On le prouve direcement pour toute variable et pas seulement
      dans [n_out nd], grâce à [denot_blocks] qui initialise son
      accumulateur avec des flots infinis. *)
  Lemma denot_S :
    forall nd envI n,
      (forall x, P_var (S n) envI x) ->
      restr_node nd ->
      wl_node G nd ->
      wx_node nd ->
      node_causal nd ->
      (forall x, P_var n (FIXP _ (denot_node G nd envG envI)) x) ->
      forall x, P_var (S n) (FIXP _ (denot_node G nd envG envI)) x.
  Proof.
    unfold restr_node.
    intros * Hins Hr Hwl Hwx Hcaus.
    pose proof (n_defd nd) as (outs & Vd & Perm).
    take (wx_node _) and inv it.
    take (wl_node _ _) and inv it.
    destruct nd.(n_block) eqn:Hnd; inv Hr.
    unfold denot_node, denot_top_block, denot_block.
    rewrite Hnd.
    autorewrite with cpodb; simpl (fst _); simpl (snd _).
    set (ins := map fst (n_in nd)) in *.
    set (env := FIXP _ _).
    intro Hn.
    eapply node_causal_ind
      with (P_vars := P_vars (S n) env)
      in Hcaus as (lord & Perm3 & Hlord).
    - intro x.
      (* on regarde où est x *)
      edestruct (ListDec.In_decidable decidable_eq_ident x lord) as [Hin|Hnin].
      + unfold P_vars in Hlord.
        eapply Forall_In in Hin; eauto.
      + rewrite Perm3 in Hnin.
        eapply not_var_not_defined in Hnin; eauto.
        unfold env; rewrite FIXP_eq; fold env.
        eapply P_var_outside_blocks; auto using P_vars_weaken.
    - constructor.
    - intros x ys _ Hys Hdep.
      constructor; auto.
      unfold env; rewrite FIXP_eq; fold env.
      destruct (decidable_Exists (Syn.Is_defined_in (FunctionalEnvironment.Var x)) blks).
      + intros; apply Is_defined_in_dec; now simpl_Forall.
      + take (wl_block _ _) and inv it.
        take (wl_scope _ _ _) and inv it.
        take (wx_block _ _) and inv it.
        take (wx_scope _ _ _) and inv it.
        eapply P_var_inside_blocks; eauto using P_vars_weaken, is_ncons_bss.
        intros y Hex.
        eapply P_vars_In, Hdep; auto.
        constructor; rewrite Hnd; constructor; econstructor; eauto.
      + eapply P_var_outside_blocks; eauto using P_vars_weaken.
  Qed.

  Theorem denot_n :
    forall nd envI n,
      restr_node nd ->
      wl_node G nd ->
      wx_node nd ->
      node_causal nd ->
      (forall x, P_var n envI x) ->
      forall x, P_var n (FIXP _ (denot_node G nd envG envI)) x.
  Proof.
    induction n; intros Hr Hwl Hwx Hcaus Hins.
    - tauto.
    - apply denot_S; auto using is_ncons_S, P_var_S.
  Qed.

  End Node_n.


  (** Using the well-ordered property of programs, show that all nodes
      receiving streams of length n outputs streams of length n. *)

  Theorem denot_global_n :
    forall n G envI,
      restr_global G ->
      wt_global G ->
      Forall node_causal (nodes G) ->
      (forall x, P_var n envI x) ->
      forall f x, P_var n (denot_global G f envI) x.
  Proof.
    intros * Hr Hwt Hcaus Hins f x.
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
      inv Hcaus. inv Hr.
      destruct (ident_eq_dec (n_name a) f); subst.
      + (* cas intéressant, où on utilise denot_n_all_vars *)
        rewrite find_node_now in Hfind; inv Hfind; auto.
        rewrite <- denot_node_cons;
          eauto using find_node_not_Is_node_in, find_node_now.
        apply denot_n; eauto using wt_global_uncons, wt_node_wl_node, wt_node_wx_node.
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
    restr_global G ->
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

Lemma sbools_ofs_inf :
  forall n (np : nprod n),
    forall_nprod (@infinite _) np ->
    infinite (sbools_ofs np).
Proof.
  induction n; intros * Hf; simpl.
  - apply DS_const_inf.
  - apply forall_nprod_inv in Hf as [].
    autorewrite with cpodb.
    apply zip_inf; auto.
Qed.

(** Une fois l'infinité des flots obtenue, on peut l'utiliser pour
    prouver l'infinité des expressions. *)
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
    cases; eauto using forall_nprod_const, DS_const_inf.
    now apply forall_denot_exps.
  - (* Ecase *)
    destruct a as [tys].
    eapply Forall_impl in H.
    2:{ intros ? HH. eapply (proj2 (forall_denot_exps _ _ _ _ _ _ _ _ )), HH. }
    eapply forall_forall_denot_expss with (n := length tys) in H as Hess;
      eauto using DS_const_inf.
    destruct d.
    + (* défaut *)
      apply forall_denot_exps in H0 as Hd.
      revert Hess IHe Hd.
      gen_sub_exps.
      unfold eq_rect_r, eq_rect, eq_sym; cases; intros;
        eauto using forall_nprod_const, DS_const_inf.
      eapply forall_lift_nprod; eauto using scase_def_inf, forall_nprod_cons.
    + (* total *)
      revert Hess IHe.
      gen_sub_exps.
      unfold eq_rect_r; cases; intros; eauto using forall_nprod_const, DS_const_inf.
      eapply forall_lift_nprod; eauto using scase_inf.
      unfold eq_rect, eq_sym; cases.
  - (* Eapp *)
    apply forall_denot_exps in H, H0.
    unfold eq_rect.
    cases; eauto using forall_nprod_const, DS_const_inf.
    apply forall_np_of_env; intro.
    apply sreset_inf; auto.
    + apply sbools_ofs_inf; auto.
    + intro; apply forall_env_of_np; eauto using DS_const_inf.
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
  apply forall_nprod_cons; eauto using infinite_exps.
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
