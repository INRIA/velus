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
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LCausality Lustre.LSemantics Lustre.LOrdered.

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
       (Import Den   : LDENOT     Ids Op OpAux Cks Senv Syn CStr).

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

  Variable (G : global).
  (* Variable Γ : static_env. *)

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

  (* TODO: move, expliquer (si ça marche) *)
  Variable (envG : Dprodi FI).

  Definition P_exp (n : nat) ins envI bs env (e : exp) (k : nat) : Prop :=
    let ss := denot_exp G ins e envG envI bs env in
    is_cons (nrem n (get_nth k ss)).

  (* Hypothèse sur les nœuds *)
  Hypothesis Hnode :
    forall (n : nat) (f : ident) (envI : DS_prod SI),
      In f (map n_name G.(nodes)) ->
      (forall x, P_var n envI x) ->
      (forall x, P_var n (envG f envI) x).

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

  Lemma P_vars_app_l :
    forall n env xs ys,
      P_vars n env (xs ++ ys) ->
      P_vars n env ys.
  Proof.
    unfold P_vars.
    eauto using Forall_app_weaken.
  Qed.

  (* TODO: move? *)
  Lemma denot_equation_input :
    forall G Γ
      e ins envI bs env x,
      wt_equation G Γ e ->
      In x ins ->
      denot_equation G ins e envG envI bs env x = envI x.
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
      is_cons (nrem n (get_nth k (denot_exps G ins es envG envI bs env))).
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

  (* TODO: move *)
  Lemma get_nth_err :
    forall k n (np : nprod n),
      (n <= k)%nat ->
      get_nth k np = DS_const (err error_Ty).
  Proof.
    induction k; simpl; intros * Hn.
    - inv Hn. now simpl.
    - destruct n; cbn; auto.
      setoid_rewrite get_nth_skip.
      apply IHk; auto with arith.
  Qed.

  Lemma forall_env_of_ss :
    forall (P : DS (sampl value) -> Prop) l {n} (ss : nprod n),
      P (DS_const (err error_Ty)) ->
      forall_nprod P ss ->
      forall x, P (env_of_ss l ss x).
  Proof.
    intros.
    unfold env_of_ss.
    cbn; cases.
    destruct (Nat.lt_ge_cases n0 n).
    - apply forall_nprod_k'; auto.
    - rewrite get_nth_err; auto.
  Qed.

  Lemma forall_ss_of_env :
    forall (P : DS (sampl value) -> Prop) l env,
      (forall x, P (env x)) ->
      forall_nprod P (ss_of_env l env).
  Proof.
    induction l as [|? []]; intros * Hp; eauto.
    - now simpl.
    - apply Hp.
    - constructor.
      + apply Hp.
      + apply IHl, Hp.
  Qed.

  Lemma find_node_name :
    forall f (GG : global) n,
      find_node f GG = Some n ->
      In f (map n_name (nodes GG)).
  Proof.
    intros * Hf.
    pose proof (find_node_Exists f GG) as Hi.
    rewrite Exists_exists in Hi.
    destruct Hi as [[? []] ?]; subst; try congruence.
    now apply in_map.
  Qed.

  (* TODO: on peut voir exp_O comme un corollaire
     de exp_n, avec un peu de boulot pour la condition sur les varibles libres.
     Ça éviterait la duplication de preuves... *)
  Lemma exp_O :
    forall Γ e ins envI bs env k,
      is_cons (nrem O bs) ->
      P_vars O envI ins ->
      k < numstreams e ->
      (forall x, Is_free_left Γ x k e -> P_var O env x) ->
      wl_exp G e ->
      wx_exp Γ e ->
      P_exp O ins envI bs env e k.
  Proof.
    intros * Hbs Hins Hk Hdep Hwl Hwx.
    assert (Hwl' := Hwl).
    revert Hwl.
    assert ( (* cas des variables : *)
        forall x cx, HasCaus Γ x cx ->
                P_var 0 env0 cx ->
                is_cons (denot_var ins envI env0 x)) as Hvar.
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
    eapply exp_causal_ind with (15 := Hdep); eauto.
    all: intros; clear dependent e; unfold P_exp.
    (* cas restreints : *)
    all: try (rewrite denot_exp_eq, get_nth_const; simpl; cases;
              now apply is_consn_DS_const with (n := O)).
    - (* const *)
      rewrite denot_exp_eq.
      now apply is_consn_sconst.
    - (* var *)
      rewrite denot_exp_eq.
      eapply Hvar; eauto.
    - (* unop *)
      rewrite denot_exp_eq.
      cases_eqn HH; subst.
      1,3: inv Hwl; rewrite <- length_typeof_numstreams, HH in *; now simpl in *.
      assert (is_cons (nrem O (get_nth 0 (denot_exp G ins e1 envG envI bs env0)))) as He.
      { inv Hwl. apply H; auto. }
      revert He.
      generalize (denot_exp G ins e1 envG envI bs env0).
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
      rewrite annots_numstreams, H8, <- H7 in *.
      eapply P_exps_k with (n := O); eauto using P_exps_impl, P_exps_Forall.
    - (* when *)
      destruct ann0 as (tys,?).
      rewrite denot_exp_eq; simpl in *.
      unfold eq_rect_r, eq_rect.
      cases.
      2: rewrite get_nth_const; auto; apply (is_consn_DS_const _ O).
      rewrite llift_nth; auto; cases.
      apply is_cons_swhen; eauto.
      inv Hwl.
      rewrite annots_numstreams in *.
      eapply P_exps_k with (n := O); eauto using P_exps_impl, P_exps_Forall.
    - (* app *)
      rewrite denot_exp_eq; simpl in *.
      unfold eq_rect_r, eq_rect.
      inv Hwl. destruct (find_node f G) eqn:?; cases.
      2,3: rewrite get_nth_const; auto; apply (is_consn_DS_const _ O).
      apply forall_nprod_k'; auto.
      apply forall_ss_of_env, (Hnode 0); intros; eauto using find_node_name.
      unfold P_var. rewrite PROJ_simpl.
      apply forall_env_of_ss; eauto using is_cons_DS_const.
      apply forall_nprod_k; intros.
      rewrite annots_numstreams in *.
      apply P_exps_k with (n := O); eauto using P_exps_impl, P_exps_Forall.
  Qed.

  Lemma exp_n :
    forall Γ n e ins envI bs env k,
      is_cons (nrem n bs) ->
      P_vars n envI ins ->
      k < numstreams e ->
      wl_exp G e ->
      wx_exp Γ e ->
      (forall x cx, HasCaus Γ x cx -> P_var n env cx) ->
      P_exp n ins envI bs env e k.
  Proof.
    intros ?????? env ? Hbs Hins.
    intros Hk Hwl Hwx Hn.
    assert ( (* cas des variables : *)
        forall x, IsVar Γ x ->
             is_cons (nrem n (denot_var ins envI env x))) as Hvar.
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
    all: unfold P_exp.
    (* cas restreints : *)
    all: try (rewrite denot_exp_eq, get_nth_const; simpl; cases;
              now apply is_consn_DS_const).
    - (* const *)
      assert (k = O) by lia; subst.
      rewrite denot_exp_eq.
      now apply is_consn_sconst.
    - (* var *)
      assert (k = O) by lia; subst.
      setoid_rewrite denot_exp_eq.
      inv Hwx. now apply Hvar.
    - (* unop *)
      assert (k = O) by lia; subst.
      rewrite denot_exp_eq.
      cases_eqn HH; subst.
      1,3: inv Hwl; rewrite <- length_typeof_numstreams, HH in *; now simpl in *.
      assert (is_cons (nrem n (get_nth 0 (denot_exp G ins e envG envI bs env)))) as He.
      { inv Hwl. inv Hwx. eapply IHe; auto; lia. }
      revert He.
      generalize (denot_exp G ins e envG envI bs env).
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
        inv Hwx. clear dependent es. take (length _ = length _) and clear it.
        revert dependent k. induction e0s; intros; simpl in *. lia.
        simpl_Forall.
        destruct (Nat.lt_ge_cases k (numstreams a0)); auto using P_exps.
        constructor 2; auto. apply IHe0s; auto; lia.
      + (* es *)
        assert (k < list_sum (map numstreams es))
          by (rewrite annots_numstreams in *; congruence).
        apply P_exps_k.
        inv Hwx. clear dependent e0s. take (length _ = length _) and clear it.
        revert dependent k. induction es; intros; simpl in *. lia.
        simpl_Forall.
        destruct (Nat.lt_ge_cases k (numstreams a0)); auto using P_exps.
        constructor 2; auto. apply IHes; auto; lia.
    - (* when *)
      rewrite denot_exp_eq; simpl.
      unfold eq_rect_r, eq_rect.
      cases.
      2: rewrite get_nth_const; auto; apply (is_consn_DS_const _ n).
      rewrite llift_nth; auto; cases.
      inv Hwl.
      apply is_consn_swhen.
      + (* es *)
        assert (k < list_sum (map numstreams es))
          by (rewrite annots_numstreams in *; congruence).
        apply P_exps_k.
        inv Hwx. take (length _ = length _) and clear it.
        revert dependent k. induction es as [|a es]; intros; simpl in *. lia.
        simpl_Forall.
        destruct (Nat.lt_ge_cases k (numstreams a)); auto using P_exps.
        constructor 2; auto. apply IHes; auto; lia.
      + (* x *)
        inv Hwx. now apply Hvar.
    - (* app *)
      rewrite denot_exp_eq; simpl in *.
      unfold eq_rect_r, eq_rect.
      inv Hwl; inv Hwx. destruct (find_node f G) eqn:?; cases.
      2,3: rewrite get_nth_const; auto; apply (is_consn_DS_const _ n).
      apply forall_nprod_k'; auto.
      apply forall_ss_of_env, (Hnode n); intros; eauto using find_node_name.
      unfold P_var. rewrite PROJ_simpl.
      apply forall_env_of_ss; eauto using is_consn_DS_const.
      apply forall_nprod_k; intros.
      apply P_exps_k.
      repeat take (length _ = length _) and clear it.
      revert dependent k0. induction es; intros; simpl in *. lia.
      simpl_Forall.
      destruct (Nat.lt_ge_cases k0 (numstreams a0)); auto using P_exps.
      constructor 2; auto. apply IHes; auto; try lia.
  Qed.

  Lemma exps_n :
    forall Γ n es ins envI bs env k,
      is_cons (nrem n bs) ->
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
      is_cons (nrem (S n) bs) ->
      P_vars (S n) envI ins ->
      k < numstreams e ->
      (forall x, Is_free_left Γ x k e -> P_var (S n) env x) ->
      wl_exp G e ->
      wx_exp Γ e ->
      (forall x cx, HasCaus Γ x cx -> P_var n env cx) ->
      P_exp (S n) ins envI bs env e k.
  Proof.
    intros ?????? env ? Hbs Hins Hk Hdep Hwl Hwx Hn.
    assert ( (* cas des variables : *)
        forall x cx, HasCaus Γ x cx ->
                P_var (S n) env cx ->
                is_cons (nrem (S n) (denot_var ins envI env x))) as Hvar.
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
    eapply exp_causal_ind with (15 := Hdep); eauto.
    all: clear dependent e; clear k.
    all: intros; unfold P_exp.
    (* cas restreints : *)
    all: try (rewrite denot_exp_eq, get_nth_const; simpl; cases;
              now apply is_consn_DS_const with (n := S n)).
    - (* const *)
      rewrite denot_exp_eq.
      now apply is_consn_sconst.
    - (* var *)
      setoid_rewrite denot_exp_eq.
      eapply Hvar; eauto.
    - (* unop *)
      rewrite denot_exp_eq.
      cases_eqn HH; subst.
      1,3: inv Hwl; rewrite <- length_typeof_numstreams, HH in *; now simpl in *.
      assert (is_cons (nrem (S n) (get_nth 0 (denot_exp G ins e1 envG envI bs env)))) as He.
      { inv Hwl. inv Hwx. apply H; auto. }
      revert He.
      generalize (denot_exp G ins e1 envG envI bs env).
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
        do 2 (apply P_exps_impl in H0; eauto using P_exps_Forall).
        now apply P_exps_k.
      + (* es *)
        eapply P_exps_k, exps_n; eauto using is_consn_S, P_vars_S.
    - (* when *)
      destruct ann0 as (tys,?).
      rewrite denot_exp_eq; simpl in *.
      unfold eq_rect_r, eq_rect.
      cases.
      2: rewrite get_nth_const; auto; apply (is_consn_DS_const _ (S n)).
      rewrite llift_nth; auto; cases.
      inv Hwl. inv Hwx.
      apply is_consn_swhen with (n := S n).
      + (* es *)
        assert (k < list_sum (map numstreams es))
          by (rewrite annots_numstreams in *; congruence).
        do 2 (apply P_exps_impl in H0; eauto using P_exps_Forall).
        now apply P_exps_k.
      + (* x *)
        eapply Hvar; eauto.
    - (* app *)
      rewrite denot_exp_eq; simpl in *.
      unfold eq_rect_r, eq_rect.
      inv Hwl; inv Hwx. destruct (find_node f G) eqn:?; cases.
      2,3: rewrite get_nth_const; auto; apply (is_consn_DS_const _ (S n)).
      apply forall_nprod_k'; auto.
      apply forall_ss_of_env, (Hnode (S n)); intros; eauto using find_node_name.
      unfold P_var. rewrite PROJ_simpl.
      apply forall_env_of_ss; eauto using is_consn_DS_const.
      apply forall_nprod_k; intros.
      rewrite annots_numstreams in *.
      apply P_exps_k with (n := S n); eauto 6 using P_exps_impl, P_exps_Forall.
  Qed.

  Lemma equation_n :
    forall xs es n k ins envI bs,
      let env := FIXP (DS_prod SI) (denot_equation G ins (xs,es) envG envI bs) in
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
      P_var n (FIXP (DS_prod SI) (denot_equation G ins e envG envI bs)) x.
  Proof.
    intros * Hwt Hin Hins.
    unfold P_vars, P_var in *.
    rewrite FIXP_eq, PROJ_simpl.
    erewrite denot_equation_input, Forall_forall, <- PROJ_simpl in *; eauto.
  Qed.

  (* TODO: move *)
  Global Add Parametric Morphism n : (P_var n) with signature
      Oeq (O := DS_prod SI) ==> eq ==> iff as P_var_morph.
  Proof.
    unfold P_var.
    intros ?? H ?.
    now rewrite H.
  Qed.

  (* TODO: move *)
  Global Add Parametric Morphism n : (P_vars n) with signature
      Oeq (O := DS_prod SI) ==> eq ==> iff as P_vars_morph.
  Proof.
    unfold P_vars.
    setoid_rewrite Forall_forall.
    intros ?? H ?.
    now setoid_rewrite H.
  Qed.

  Lemma P_var_input_node :
    forall nd envI bs x n,
      wt_node G nd ->
      In x (map fst (n_in nd)) ->
      P_vars n envI (map fst (n_in nd)) ->
      P_var n (FIXP (DS_prod SI) (denot_node G nd envG envI bs)) x.
  Proof.
    intros * Hwt Hx Hins.
    unfold denot_node, denot_block.
    destruct Hwt as (?&?&?& Hwt).
    cases.
    inv Hwt; try congruence; eauto using P_var_input_eq.
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

  Lemma denot_S :
    forall nd envI bs n,
      wt_node G nd ->
      node_causal nd ->
      is_cons (nrem (S n) bs) ->
      (forall x, P_var (S n) envI x) ->
      P_vars n (FIXP _ (denot_node G nd envG envI bs)) (map fst nd.(n_out)) ->
      P_vars (S n) (FIXP _ (denot_node G nd envG envI bs)) (map fst nd.(n_out)).
  Proof.
    intros * Hwt Hcaus Hbs Hins Hn.
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
      eapply equation_n; eauto.
      { rewrite Hperm, <- map_app; apply node_NoDup. }
      eapply Pexp_Pexps with
        (Γ := (senv_of_inout (n_in nd ++ n_out nd)))
        (P_var := P_var (S n) (FIXP _ (denot_equation G (map fst (n_in nd)) (xs, es) envG envI bs))); eauto.
      + inv Hwt.  assert(Wte := H4). destruct H4 as [Hwt].
        apply Forall_wt_exp_wx_exp in Hwt as Hwx.
        apply Forall_wt_exp_wl_exp in Hwt as Hwl.
        apply Forall_forall.
        intros e Hin k' Hk' Hdp.
        pose proof (Forall_In _ _ _ Hwx Hin) as Hwxe.
        pose proof (Forall_In _ _ _ Hwl Hin) as Hwle.
        pose proof (Forall_In _ _ _ Hwt Hin) as Hwte.
        eapply exp_S; eauto using P_vars_weaken.
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

  (* TODO: ressemble beaucoup à denot_S... *)
  Lemma denot_O :
    forall nd envI bs,
      wt_node G nd ->
      node_causal nd ->
      is_cons (nrem O bs) ->
      (forall x, P_var O envI x) ->
      P_vars O (FIXP _ (denot_node G nd envG envI bs)) (map fst nd.(n_out)).
  Proof.
    intros * Hwt Hcaus Hbs Hins.
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
      eapply equation_n; eauto.
      { rewrite Hperm, <- map_app; apply node_NoDup. }
      eapply Pexp_Pexps with
        (Γ := (senv_of_inout (n_in nd ++ n_out nd)))
        (P_var := P_var O (FIXP _ (denot_equation G (map fst (n_in nd)) (xs, es) envG envI bs))); eauto.
      + inv Hwt. assert(Wte := H4). destruct H4 as [Hwt].
        apply Forall_wt_exp_wx_exp in Hwt as Hwx.
        apply Forall_wt_exp_wl_exp in Hwt as Hwl.
        apply Forall_forall.
        intros e Hin k' Hk' Hdp.
        pose proof (Forall_In _ _ _ Hwx Hin) as Hwxe.
        pose proof (Forall_In _ _ _ Hwl Hin) as Hwle.
        pose proof (Forall_In _ _ _ Hwt Hin) as Hwte.
        eapply exp_O; eauto using P_vars_weaken.
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
      wt_node G nd ->
      node_causal nd ->
      is_cons (nrem n bs) ->
      (forall x, P_var n envI x) ->
      P_vars n (FIXP _ (denot_node G nd envG envI bs)) (map fst nd.(n_out)).
  Proof.
    induction n; intros Hwt Hcaus Hbs Hins.
    - apply denot_O; auto.
    - apply denot_S; auto using is_consn_S, P_var_S.
  Qed.

  (* Avec l'hypothèse [restr_node] actuelle, toutes les variables du nœud
     sont définies dans une seule équation et [denot_equation] associe
     [DS_const err] aux autres variables. On peut donc en déduire que
     tous les flots dans le point fixe de denot_equation sont P_vars n.
   *)
  Lemma P_vars_node_all :
    forall nd envI bs n,
      wt_node G nd ->
      (forall x, P_var n envI x) ->
      P_vars n (FIXP _ (denot_node G nd envG envI bs)) (map fst nd.(n_out)) ->
      forall x, P_var n (FIXP _ (denot_node G nd envG envI bs)) x.
  Proof.
    intros * Hwt Hins Hn x.
    destruct (mem_ident x (map fst (n_in nd))) eqn:Hin.
    { rewrite mem_ident_spec in Hin. eauto using P_var_input_node, P_vars_weaken. }
    destruct (mem_ident x (map fst (n_out nd))) eqn:Hout.
    { rewrite mem_ident_spec in Hout. eapply Forall_In in Hn; eauto. }
    destruct (n_defd nd) as (ys & Hvd & Hperm).
    rewrite FIXP_eq.
    unfold denot_node, denot_block.
    destruct nd.(n_block) eqn:Hnd; auto.
    inv Hvd. destruct e as (xs,es); simpl in *.
    rewrite <- Bool.not_true_iff_false, mem_ident_spec, <- Hperm in Hout.
    unfold P_var.
    rewrite PROJ_simpl, denot_equation_eq.
    cases_eqn HH; try congruence; auto using is_consn_DS_const.
    destruct Hout; eauto using mem_nth_In.
  Qed.

  Corollary denot_n_all_vars :
    forall nd envI bs n,
      wt_node G nd ->
      node_causal nd ->
      is_cons (nrem n bs) ->
      (forall x, P_var n envI x) ->
      forall x, P_var n (FIXP _ (denot_node G nd envG envI bs)) x.
  Proof.
    intros.
    apply P_vars_node_all; auto using denot_n.
  Qed.

  Lemma is_consn_bss :
    forall n env l,
      (forall x, (* on pourrait affiner *)
          is_cons (nrem n (env x))) ->
      is_cons (nrem n (bss l env)).
  Proof.
    intros * Hx.
    induction l.
    - apply is_consn_DS_const.
    - simpl.
      autorewrite with cpodb.
      apply is_consn_zip; auto.
      rewrite nrem_map.
      apply is_cons_map, Hx.
  Qed.

  Corollary denot2_n_all_vars :
    forall nd envI n,
      wt_node G nd ->
      node_causal nd ->
      (forall x, P_var n envI x) ->
      forall x, P_var n (FIXP _ (denot_node2 G nd envG envI)) x.
  Proof.
    intros.
    rewrite denot_node2_eq.
    apply denot_n_all_vars; auto using is_consn_bss.
  Qed.

  End Node_n.

  (** Here we show that a node can be removed from the environment if it
      is not evaluated during the computations. *)
  Section Denot_global_cons.

    (* TODO: move *)
  Lemma nprod_app_Oeq_compat :
    forall {n p} (p1 p2 : nprod n) (p3 p4 : nprod p),
      p1 == p2 ->
      p3 == p4 ->
      nprod_app p1 p3 == nprod_app p2 p4.
  Proof.
    induction n; auto.
  Qed.

  Lemma denot_exp_cons :
    forall nd nds tys
      ins envG envI bs env e,
      ~ Is_node_in_exp nd.(n_name) e ->
      denot_exp (Global tys nds) ins e envG envI bs env
      == denot_exp (Global tys (nd :: nds)) ins e envG envI bs env.
  Proof.
    Ltac solve_nin Hnin :=
        let H := fresh in
        intro H; apply Hnin; constructor; auto.
    (* TODO: utiliser ça partout, vraiment ! *)
    Ltac gen_denot :=
      repeat match goal with
      | |- context [ denot_exp ?a ?b ?c ] => generalize (denot_exp a b c)
      | |- context [ denot_exps ?a ?b ?c ] => generalize (denot_exps a b c)
      end.
    induction e using exp_ind2; intro Hnin.
    all: setoid_rewrite denot_exp_eq; auto.
    - (* unop *)
      revert IHe.
      gen_denot.
      cases; simpl; intros.
      rewrite IHe; auto.
      intro H; apply Hnin; constructor; auto.
    - (* fby *)
      assert (denot_exps (Global tys nds) ins e0s envG envI bs env0
              == denot_exps (Global tys (nd::nds)) ins e0s envG envI bs env0) as He0s.
      { induction e0s. trivial.
        inv H.
        (* TODO: faire mieux, cette preuve est un enfer *)
        rewrite 2 denot_exps_eq.
        apply nprod_app_Oeq_compat.
        - apply H3. solve_nin Hnin.
        - apply IHe0s; auto.
          intro HH; inv HH. apply Hnin. constructor.
          destruct H2; eauto using Exists_cons_tl. }
      assert (denot_exps (Global tys nds) ins es envG envI bs env0
              == denot_exps (Global tys (nd::nds)) ins es envG envI bs env0) as Hes.
      { induction es. trivial.
        inv H0.
        (* TODO: faire mieux, cette preuve est un enfer *)
        rewrite 2 denot_exps_eq.
        apply nprod_app_Oeq_compat.
        - apply H3. solve_nin Hnin.
        - apply IHes; auto.
          intro HH; inv HH. apply Hnin. constructor.
          destruct H2; eauto using Exists_cons_tl. }
      revert He0s Hes; simpl; unfold eq_rect_r, eq_rect, eq_sym.
      gen_denot; cases.
    - (* when *)
      assert (denot_exps (Global tys nds) ins es envG envI bs env0
              == denot_exps (Global tys (nd::nds)) ins es envG envI bs env0) as Hes.
      { induction es. trivial.
        inv H.
        (* TODO: faire mieux, cette preuve est un enfer *)
        rewrite 2 denot_exps_eq.
        apply nprod_app_Oeq_compat.
        - apply H2. solve_nin Hnin.
        - apply IHes; auto.
          intro HH; inv HH. apply Hnin.
          constructor; eauto using Exists_cons_tl. }
      revert Hes; simpl; unfold eq_rect_r, eq_rect, eq_sym.
      gen_denot; cases.
    - (* eapp, seul cas intéressant *)
      simpl.
      destruct (ident_eq_dec nd.(n_name) f) as [|Hf]; subst.
      { (* si oui, contradiction *)
        destruct Hnin. apply INEapp2. }
      rewrite (find_node_other _ _ _ _ Hf).
      assert (denot_exps (Global tys nds) ins es envG envI bs env0
              == denot_exps (Global tys (nd::nds)) ins es envG envI bs env0) as Hes.
      { induction es. trivial.
        inv H.
        (* TODO: faire mieux, cette preuve est un enfer *)
        rewrite 2 denot_exps_eq.
        apply nprod_app_Oeq_compat.
        - apply H3. solve_nin Hnin.
        - apply IHes; auto.
          intro HH; inv HH; auto.
          apply Hnin; constructor.
          destruct H2; eauto using Exists_cons_tl.
      }
      revert Hes; simpl; unfold eq_rect_r, eq_rect, eq_sym.
      gen_denot; cases.
      now intros ?? ->.
  Qed.

  Lemma denot_node_cons :
    forall n nd nds tys,
      ~ Is_node_in_block nd.(n_name) n.(n_block) ->
      denot_node (Global tys nds) n
      == denot_node (Global tys (nd :: nds)) n.
  Proof.
    intros * Hnin.
    unfold denot_node, denot_block.
    destruct n.(n_block).
    2-5: trivial.
    destruct e as (xs,es).
    apply fcont_eq_intro; intro envG.
    apply fcont_eq_intro; intro envI.
    apply fcont_eq_intro; intro bs.
    apply fcont_eq_intro; intro env.
    apply Oprodi_eq_intro; intro x.
    setoid_rewrite denot_equation_eq.
    cases_eqn HH; simpl.
    apply get_nth_Oeq_compat.
    clear - Hnin.
    induction es. reflexivity.
    rewrite 2 denot_exps_eq.
    apply nprod_app_Oeq_compat.
    - apply denot_exp_cons. intro.
      apply Hnin. constructor. now constructor.
    - apply IHes. intro H. inv H.
      apply Hnin. constructor.
      unfold Is_node_in_eq in *; eauto using Exists_cons_tl.
  Qed.

  Corollary denot_node2_cons :
    forall n nd nds tys,
      ~ Is_node_in_block nd.(n_name) n.(n_block) ->
      denot_node2 (Global tys nds) n
      == denot_node2 (Global tys (nd :: nds)) n.
  Proof.
    intros.
    apply fcont_eq_intro; intro envG.
    apply fcont_eq_intro; intro envI.
    rewrite 2 denot_node2_eq, denot_node_cons; eauto.
  Qed.

  (* Lemma denot_global_cons_ : *)
  (*   forall nd nds tys f envG, *)
  (*     Ordered_nodes (Global tys (nd :: nds)) -> *)
  (*     nd.(n_name) <> f -> *)
  (*     denot_global_ (Global tys (nd::nds)) envG f *)
  (*     == denot_global_ (Global tys nds) envG f. *)
  (* Proof. *)
  (*   intros * Hord Hneq. *)
  (*   apply fcont_eq_intro; intro envI. *)
  (*   rewrite 2 denot_global_eq, (find_node_other _ _ _ _ Hneq). *)
  (*   destruct (find_node _ _) eqn:Hfind. 2: auto. *)
  (*   rewrite <- denot_node2_cons; eauto using find_node_later_not_Is_node_in. *)
  (* Qed. *)

  End Denot_global_cons.


  (** Using the well-ordered property of programs, show that all nodes
      receiving streams of length n outputs streams of length n. *)
  Section Global_n.

  Lemma wt_global_cons :
    forall tys (nd : node) nds,
      wt_global (Global tys (nd :: nds)) ->
      wt_global (Global tys nds).
  Proof.
    inversion 1 as [? Hi]. inv Hi.
    constructor; auto.
  Qed.

  Lemma wt_global_uncons :
    forall tys (nd : node) nds,
      wt_global (Global tys (nd :: nds)) ->
      wt_node (Global tys nds) nd.
  Proof.
    intros * [? Wt]. now inv Wt.
  Qed.

  (* utile car on n'a pas envie d'inverser Ordered_nodes dans
     un environnement de preuve... *)
  Lemma Ordered_nodes_cons :
    forall tys (nd : node) nds,
      Ordered_nodes (Global tys (nd :: nds)) ->
      Ordered_nodes (Global tys nds).
  Proof.
    inversion 1; auto.
  Qed.

  (* TODO: move *)
  Lemma name_find_node :
    forall f (G : global),
      In f (map n_name (nodes G)) ->
      exists nd, find_node f G = Some nd.
  Proof.
    intros * Hin.
    destruct G as [tys nds].
    induction nds as [|nd]; simpl in *. contradiction.
    destruct (ident_eq_dec (n_name nd) f).
    - rewrite find_node_now; eauto.
    - rewrite find_node_other; firstorder; auto.
  Qed.

  (* TODO: move *)
  Lemma find_node_uncons :
    forall f tys (nd ndf : node) nds,
      wt_global (Global tys (nd :: nds)) ->
      find_node f (Global tys nds) = Some ndf ->
      find_node f (Global tys (nd :: nds)) = Some ndf.
  Proof.
    intros * Hwt Hfind.
    inv Hwt.
    apply CommonTyping.wt_program_NoDup in H0.
    inv H0.
    destruct (ident_eq_dec (n_name nd) f); subst.
    - apply find_node_name in Hfind. exfalso. auto.
    - setoid_rewrite find_node_other; auto.
  Qed.

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
          envG f envI == FIXP _ (denot_node2 G nd envG envI)) as HenvG.
      { intros * Hf; subst.
        now rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl, denot_global_eq, Hf at 1. }
      (* maintenant HenvG contient tout ce qu'on doit savoir sur envG *)
      clear HF.
      (* il faut généraliser à tous les nœuds *)
      revert Hins HenvG Hfind. revert envI envG n f x nd.
      destruct G as [tys nds]; simpl in *.
      induction nds as [|a nds]; simpl; intros. inv Hfind.
      inv Hcaus.
      destruct (ident_eq_dec (n_name a) f); subst.
      + (* cas intéressant, où on utilise denot2_n_all_vars *)
        rewrite find_node_now in Hfind; inv Hfind; auto.
        rewrite <- denot_node2_cons;
          eauto using find_node_not_Is_node_in, find_node_now.
        apply denot2_n_all_vars; auto using wt_global_uncons.
        intros m f envI2 Hin HI2 y.
        apply name_find_node in Hin as (ndf & Hfind).
        eapply find_node_uncons with (nd := nd) in Hfind as ?; auto.
        rewrite HenvG, <- denot_node2_cons; eauto using find_node_later_not_Is_node_in.
        apply IHnds with (f := f); auto.
        eauto using wt_global_cons.
        eauto using Ordered_nodes_cons.
        (* montrons que HenvG tient toujours *)
        intros f' ndf' envI' Hfind'.
        eapply find_node_uncons with (nd := nd) in Hfind' as ?; auto.
        rewrite HenvG, <- denot_node2_cons; eauto using find_node_later_not_Is_node_in.
      + rewrite find_node_other in Hfind; auto.
        rewrite <- denot_node2_cons; eauto using find_node_later_not_Is_node_in.
        apply IHnds with (f := f); auto.
        eauto using wt_global_cons.
        eauto using Ordered_nodes_cons.
        (* montrons que HenvG tient toujours *)
        intros f' ndf' envI' Hfind'.
        eapply find_node_uncons with (nd := a) in Hfind' as ?; auto.
        rewrite HenvG, <- denot_node2_cons; eauto using find_node_later_not_Is_node_in.
    - unfold P_var, env_err_ty.
      cbn; eauto using is_consn_DS_const.
  Qed.

  End Global_n.
  End Top.

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
  assert (forall x, infinite (denot_var ins envI env0 x)) as Hvar.
  { unfold all_infinite, denot_var in *. intro. cases; eauto. }
  induction e using exp_ind2; intros; simpl; setoid_rewrite denot_exp_eq.
  (* cas restreints : *)
  all: try (simpl; now auto using forall_nprod_const, DS_const_inf).
  - (* const *)
    apply sconst_inf; auto.
  - (* unop *)
    assert (forall_nprod (@infinite _) (denot_exp G ins e envG envI bs env0)) as He by eauto.
    revert He.
    generalize (denot_exp G ins e envG envI bs env0).
    generalize (numstreams e).
    intros.
    cases; simpl; auto using sunop_inf, DS_const_inf.
  - (* fby *)
    assert (forall_nprod (@infinite _) (denot_exps G ins e0s envG envI bs env0)) as He0s.
    { induction e0s; simpl_Forall; auto.
      setoid_rewrite denot_exps_eq; auto using forall_nprod_app. }
    assert (forall_nprod (@infinite _) (denot_exps G ins es envG envI bs env0)) as Hes.
    { induction es; simpl_Forall; auto.
      setoid_rewrite denot_exps_eq; auto using forall_nprod_app. }
    revert He0s Hes.
    generalize (denot_exps G ins e0s envG envI bs env0).
    generalize (denot_exps G ins es envG envI bs env0).
    generalize (list_sum (List.map numstreams e0s)).
    generalize (list_sum (List.map numstreams es)).
    intros; unfold eq_rect_r, eq_rect, eq_sym.
    cases; subst; auto using forall_nprod_const, DS_const_inf, forall_nprod_lift2, fby_inf.
  - (* when *)
    assert (forall_nprod (@infinite _) (denot_exps G ins es envG envI bs env0)) as Hes.
    { induction es; simpl_Forall; auto.
      setoid_rewrite denot_exps_eq; auto using forall_nprod_app. }
    revert Hes.
    generalize (denot_exps G ins es envG envI bs env0).
    generalize (list_sum (List.map numstreams es)).
    intros; unfold eq_rect_r, eq_rect, eq_sym.
    cases; subst; eauto using forall_nprod_const, DS_const_inf, forall_nprod_llift, swhen_inf.
  - (* app *)
    assert (forall_nprod (@infinite _) (denot_exps G ins es envG envI bs env0)) as Hes.
    { induction es; simpl_Forall; auto.
      setoid_rewrite denot_exps_eq; auto using forall_nprod_app. }
    revert Hes.
    generalize (denot_exps G ins es envG envI bs env0).
    generalize (list_sum (List.map numstreams es)).
    intros; unfold eq_rect_r, eq_rect, eq_sym.
    cases; subst; eauto using forall_nprod_const, DS_const_inf.
    apply forall_ss_of_env, HG; intro.
    apply forall_env_of_ss; auto using DS_const_inf.
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
  intros; simpl_Forall.
  setoid_rewrite denot_exps_eq.
  auto using forall_nprod_app, infinite_exp.
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
       (CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Den   : LDENOT     Ids Op OpAux Cks Senv Syn CStr)
<: LDENOTINF Ids Op OpAux Cks Senv Syn Typ LCA Lord CStr Den.
  Include LDENOTINF Ids Op OpAux Cks Senv Syn Typ LCA Lord CStr Den.
End LDenotInfFun.
