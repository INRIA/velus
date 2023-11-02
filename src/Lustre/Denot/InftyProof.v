From Coq Require Import String Morphisms.
From Coq Require Import List Permutation.
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
Require Import SDfuns Denot Infty CommonList2.

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
    forall Γ x cx, HasCaus Γ x cx -> cx = x.

  Lemma HasCausRefl : forall Γ x, IsVar Γ x -> HasCaus Γ x x.
  Proof.
    intros * Hv.
    inv Hv.
    apply InMembers_In in H as [e Hin].
    econstructor; eauto.
    erewrite <- HasCausInj; eauto using HasCaus.
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
    apply HasCausInj with (Γ := senv_of_ins l).
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
    apply symmetry, HasCausInj with (Γ := senv_of_decls l).
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
    forall x, In x cxs -> P_var n env x.

  Definition P_exp (n : nat) ins envI bs env (e : exp) (k : nat) : Prop :=
    let ss := denot_exp G ins e envG envI bs env in
    is_ncons n (get_nth k errTy ss).

  (* Hypothèse sur les nœuds *)
  Hypothesis Hnode :
    forall (n : nat) (f : ident) (nd : node) (envI : DS_prod SI),
      find_node f G = Some nd ->
      (P_vars n envI (map fst (n_in nd))) ->
      (P_vars n (envG f envI) (map fst (n_out nd))).


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
    intros ?? H ?.
    now setoid_rewrite H.
  Qed.

  Lemma P_vars_In :
    forall n env xs x,
      P_vars n env xs ->
      In x xs ->
      P_var n env x.
  Proof.
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
    setoid_rewrite in_app_iff.
    auto.
  Qed.

  Lemma P_vars_app_r :
    forall n env xs ys,
      P_vars n env (xs ++ ys) ->
      P_vars n env xs.
  Proof.
    unfold P_vars.
    setoid_rewrite in_app_iff.
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

  Lemma is_ncons_sbools_of :
    forall n m (np : nprod m),
      forall_nprod (is_ncons n) np ->
      is_ncons n (sbools_of np).
  Proof.
    clear.
    induction m; intros * Hf; auto.
    - apply is_ncons_DS_const.
    - apply forall_nprod_inv in Hf as [Hh Ht].
      unfold sbools_of.
      autorewrite with cpodb.
      rewrite Fold_eq, lift_hd, lift_tl.
      apply is_ncons_zip.
      + apply is_ncons_map; auto.
      + apply (IHm _ Ht).
  Qed.

  Ltac solve_err :=
    try (repeat (rewrite get_nth_const; [|simpl; cases]);
         match goal with
         | |- is_cons (nrem _ (Cpo_streams_type.map _ _)) =>
             apply (is_ncons_map _ _ _ _ (S _)); auto 1
         | _ => idtac
         end;
         now (apply is_ncons_DS_const || apply is_consn_DS_const)).



      (* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
      Set Nested Proofs Allowed.
      (* TODO: move, attention au solve_err *)
      Lemma P_vars_env_of_np :
          forall n l m (mp : nprod m),
            forall_nprod (is_ncons n) mp ->
            P_vars n (env_of_np l mp) l.
        Proof.
          clear.
          unfold P_vars, P_var.
          intros.
          rewrite PROJ_simpl.
          rewrite env_of_np_eq.
          destruct (mem_nth l x) as [i|] eqn:Hmem.
          - apply forall_nprod_k_def; auto; solve_err.
          - apply mem_nth_nin in Hmem; tauto.
        Qed.

        Lemma P_vars_app :
          forall n X Y l,
            P_vars 1 X l ->
            P_vars n Y l ->
            P_vars (S n) (APP_env X Y) l.
        Proof.
          clear.
          unfold P_vars, P_var.
          setoid_rewrite PROJ_simpl.
          simpl; intros * Px Py x Hin.
          rewrite APP_env_eq.
          destruct n; simpl; auto.
          rewrite rem_app; auto; apply Py, Hin.
        Qed.
        Lemma P_vars_1 :
          forall n X l,
            P_vars (S n) X l ->
            P_vars 1 X l.
        Proof.
          induction n; auto using P_vars_S.
        Qed.

          Lemma is_cons_sreset_aux :
            forall (f:DS_prod SI -C-> DS_prod SI) ins outs R X Y,
              (forall envI, P_vars 1 envI ins -> P_vars 1 (f envI) outs) ->
              is_cons R ->
              P_vars 1 X ins ->
              P_vars 1 Y outs ->
              P_vars 1 (sreset_aux f R X Y) outs.
          Proof.
            clear.
            intros * Cf Cr Cx Cy.
            apply is_cons_elim in Cr as (vr & R' & Hr).
            rewrite Hr, sreset_aux_eq.
            destruct vr; [rewrite sreset_aux_eq |];
              apply P_vars_app; auto using P_vars_O.
          Qed.

      Lemma is_ncons_sreset :
        forall (f:DS_prod SI -C-> DS_prod SI) ins outs R X,
          (forall n envI, P_vars n envI ins -> P_vars n (f envI) outs) ->
          forall n,
            is_ncons n R ->
            P_vars n X ins ->
            P_vars n (sreset f R X) outs.
      Proof.
        clear.
        intros * Cf n Cr Cx.
        rewrite sreset_eq.
        assert (Hy : P_vars n (f X) outs) by auto.
        remember (_ f X) as Y eqn:HH; clear HH.
        revert dependent R.
        revert dependent X.
        revert dependent Y.
        induction n as [|[]]; intros; eauto using is_cons_sreset_aux.
        apply is_ncons_is_cons in Cr as Hr.
        apply is_cons_elim in Hr as (vr & R' & Hr).
        rewrite Hr, sreset_aux_eq in *.
        simpl in Cr; rewrite rem_cons in Cr.
        destruct vr; [rewrite sreset_aux_eq |].
        all: apply P_vars_app; eauto using P_vars_1.
        apply IHn; auto.
        now apply (Cf (S (S n))).
      Qed.
      (* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

  Lemma exp_n :
    forall Γ n e ins envI bs env k,
      is_ncons n bs ->
      P_vars n envI ins ->
      k < numstreams e ->
      wl_exp G e ->
      wx_exp Γ e ->
      (forall x cx, HasCaus Γ x cx -> ~ In x ins -> P_var n env cx) ->
      P_exp n ins envI bs env e k.
  Proof.
    intros * Hbs Hins.
    intros Hk Hwl Hwx Hn.
    (* cas des variables, mutualisé *)
    assert (forall x, IsVar Γ x -> is_ncons n (denot_var ins envI env x)) as Hvar.
    { unfold P_vars, P_var in Hins; intros.
      unfold denot_var. cases_eqn HH.
      * (* in *)
        rewrite mem_ident_spec in HH.
        now apply Hins.
      * (* out *)
        apply mem_ident_false in HH.
        eapply Hn; eauto using HasCausRefl.
    }
    revert dependent k.
    induction e using exp_ind2; simpl; intros.
    (* cas restreints : *)
    all: unfold P_exp; try (rewrite denot_exp_eq; now solve_err).
    - (* Econst *)
      assert (k = O) by lia; subst.
      rewrite denot_exp_eq.
      now apply is_ncons_sconst.
    - (* Eenum *)
      assert (k0 = O) by lia; subst.
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
      take (find_node _ _ = _) and rewrite it; cases; solve_err.
      apply forall_nprod_k; auto.
      apply forall_np_of_env'; setoid_rewrite <- PROJ_simpl; rewrite <- Forall_forall.
      eapply Forall_forall, is_ncons_sreset; eauto.
      + apply is_ncons_sbools_of.
        apply k_forall_nprod_def with (d := errTy); intros; solve_err.
        now apply P_exps_k, Forall_P_exps.
      + apply P_vars_env_of_np.
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
      (forall x cx, HasCaus Γ x cx -> ~ In x ins -> P_var n env cx) ->
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
      (forall x, Is_used_inst Γ x k e -> ~ In x ins -> P_var (S n) env x) ->
      wl_exp G e ->
      wx_exp Γ e ->
      (forall x cx, HasCaus Γ x cx -> ~ In x ins -> P_var n env cx) ->
      P_exp (S n) ins envI bs env e k.
  Proof.
    intros * Hbs Hins Hk Hdep Hwl Hwx Hn.
    (* cas des variables, mutualisé *)
    assert (Hvar : forall x cx,
               HasCaus Γ x cx ->
               (~ In cx ins -> P_var (S n) env cx) ->
               is_ncons (S n) (denot_var ins envI env x)).
    { unfold P_vars, P_var in Hins.
      intros x cx Hc Hx.
      unfold denot_var; cases_eqn HH.
      + (* in *)
        rewrite mem_ident_spec in HH.
        now apply Hins.
      + (* out *)
        apply mem_ident_false in HH.
        apply HasCausInj in Hc; subst.
        now apply Hx.
    }
    assert (Hwl' := Hwl).
    assert (Hwx' := Hwx).
    revert Hwl Hwx.
    eapply exp_causal_ind with (16 := Hdep); eauto.
    all: clear dependent e; clear k; intros; unfold P_exp.
    (* cas restreints : *)
    all: try (rewrite denot_exp_eq; now solve_err).
    - (* Econst *)
      rewrite denot_exp_eq.
      now apply is_ncons_sconst.
    - (* Eenum *)
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
      apply forall_np_of_env'; setoid_rewrite <- PROJ_simpl.
      eapply is_ncons_sreset with (n := S n); intros.
      + apply Hnode; eauto using find_node_name.
      + apply is_ncons_sbools_of.
        apply k_forall_nprod_def with (d := errTy); intros; solve_err.
        rewrite annots_numstreams in *.
        apply P_exps_k; eauto using P_exps_impl.
      + apply P_vars_env_of_np.
        apply k_forall_nprod_def with (d := errTy); intros; solve_err.
        rewrite annots_numstreams in *.
        apply P_exps_k; eauto using P_exps_impl.
  Qed.

  Corollary exps_S :
    forall Γ n es ins envI bs env k,
      is_ncons (S n) bs ->
      P_vars (S n) envI ins ->
      k < list_sum (map numstreams es) ->
      (forall x, Is_used_inst_list Γ x k es -> ~ In x ins -> P_var (S n) env x) ->
      Forall (wl_exp G) es ->
      Forall (wx_exp Γ) es ->
      (forall x cx, HasCaus Γ x cx -> ~ In x ins -> P_var n env cx) ->
      P_exps (P_exp (S n) ins envI bs env) es k.
  Proof.
    induction es as [| e es]; simpl; intros; try lia; simpl_Forall.
    destruct (Nat.lt_ge_cases k (numstreams e)).
    - apply P_exps_now; auto.
      eapply exp_S; intros; eauto.
      take (forall x, _ -> _) and apply it; auto; left; auto.
    - apply P_exps_later; auto.
      apply IHes; auto; try lia; intros.
      take (forall x, _ -> _) and apply it; auto; right; auto.
  Qed.

  Lemma is_ncons_bss :
    forall n (env : DS_prod SI) l,
      P_vars n env l ->
      is_ncons n (bss l env).
  Proof.
    unfold P_vars.
    induction l; intros * Hv.
    - apply is_ncons_DS_const.
    - rewrite bss_cons.
      simpl (In _ _) in *.
      apply is_ncons_zip; auto.
      apply is_ncons_map, Hv; auto.
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
      (forall x cx : ident, HasCaus Γ x cx -> ~ In x ins -> P_var n env cx) ->
      (forall y, Exists (depends_on Γ x y) blks -> ~ In y ins -> P_var (S n) env y) ->
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
      eapply exps_S; eauto; try lia.
      intros y Hiuil.
      eapply Hdep, Exists_cons_hd, DepOnEq; eauto.
      eapply HasCausRefl, Forall_forall, nth_error_In; eauto.
    - apply IHblks; auto.
      inv Hex; auto.
      apply mem_nth_nin in Hmem; try tauto.
      now take (Syn.Is_defined_in _ _) and inv it.
  Qed.

  (* (* Si une variable n'est pas définie dans les blocs, *)
  (*    alors [denot_blocks] l'associe à [errTy]. *) *)
  (* Lemma P_var_outside_blocks : *)
  (*   forall ins envI bs env blks x n, *)
  (*     (forall x, P_var n envI x) -> *)
  (*     ~ (Exists (Syn.Is_defined_in (Var x)) blks)  -> *)
  (*     P_var n (denot_blocks G ins blks envG envI bs env) x. *)
  (* Proof. *)
  (*   intros * Hins Hnex; revert dependent blks. *)
  (*   induction blks as [| blk blks]; simpl; intros. *)
  (*   - apply Hins. *)
  (*   - rewrite denot_blocks_eq_cons, denot_block_eq. *)
  (*     cases. *)
  (*     unfold P_var; rewrite PROJ_simpl, env_of_np_ext_eq. *)
  (*     cases_eqn Hmem. *)
  (*     + contradict Hnex; left. *)
  (*       apply mem_nth_In in Hmem. *)
  (*       now constructor. *)
  (*     + apply IHblks; auto. *)
  (* Qed. *)

  (* (* FIXME: c'est trop ad hoc mais je ne sais pas comment faire autrement *) *)
  (* Lemma not_var_not_defined : *)
  (*   forall x (nd : node) locs blks, *)
  (*     n_block nd = Blocal (Scope locs blks) -> *)
  (*     ~ In x (map snd (idcaus (n_in nd) ++ idcaus_of_decls (n_out nd) ++ idcaus_of_locals (n_block nd))) -> *)
  (*     ~ Exists (Syn.Is_defined_in (FunctionalEnvironment.Var x)) blks. *)
  (* Proof. *)
  (*   intros * Hnd Hnin; contradict Hnin. *)
  (*   pose proof (n_defd nd) as (vars & Vd & Perm). *)
  (*   pose proof (n_syn nd) as Noloc. *)
  (*   pose proof (n_nodup nd) as (_ & Ndl). *)
  (*   rewrite Hnd in *. *)
  (*   inv Vd. *)
  (*   take (VarsDefinedScope _ _ _) and inversion_clear it as [II JJ ? (vars' & Vd' & Perm2)]. *)
  (*   clear II JJ. *)
  (*   inversion_clear Noloc as [??? Noloc2 (?&? &?)]; inv Noloc2. *)
  (*   inv Ndl. Syn.inv_scope. *)
  (*   rewrite 2 map_app, idcaus_map; simpl. *)
  (*   rewrite map_app, <- 2 idcaus_of_decls_map; auto. *)
  (*   eapply Exists_VarsDefined_spec in Hnin; eauto. *)
  (*   2:{ simpl_Forall. eapply NoDupLocals_incl; eauto. *)
  (*       rewrite Perm2, Perm, map_app, 2 map_fst_senv_of_decls. *)
  (*       solve_incl_app. } *)
  (*   rewrite Perm2, Perm, fst_InMembers, map_app, 2 map_fst_senv_of_decls in Hnin. *)
  (*   rewrite 3 in_app_iff in *; tauto. *)
  (* Qed. *)

  (* Lemma Is_defined_in_dec : *)
  (*   forall x blk, *)
  (*     restr_block blk -> *)
  (*     Decidable.decidable (Syn.Is_defined_in x blk). *)
  (* Proof. *)
  (*   intros * Hr; inv Hr. *)
  (*   - (* Beq *) *)
  (*     destruct x. *)
  (*     + (* Var *) *)
  (*       destruct (ListDec.In_decidable decidable_eq_ident x xs) as [Hin|Hnin]. *)
  (*       * left; constructor; auto. *)
  (*       * right; contradict Hnin; now inv Hnin. *)
  (*     + (* Last *) *)
  (*       right; intro HH; inv HH. *)
  (* Qed. *)

  Section COMMUN_SAFE.

  Lemma NoDup_senv_loc :
    forall (nd : node) vars blks,
      n_block nd = Blocal (Scope vars blks) ->
      NoDupMembers (senv_of_ins (n_in nd) ++ senv_of_decls (n_out nd) ++ senv_of_decls vars).
  Proof.
    intros * Hn.
    pose proof (n_nodup nd) as [Nd Ndl].
    rewrite Hn in Ndl; inv Ndl.
    take (NoDupScope _ _ _) and inversion_clear it as [???? ndm Hf].
    rewrite fst_NoDupMembers, 2 map_app, map_fst_senv_of_ins, 2 map_fst_senv_of_decls.
    rewrite app_assoc.
    apply fst_NoDupMembers in ndm.
    apply NoDup_app'_iff; repeat split; auto.
    setoid_rewrite fst_InMembers in Hf.
    simpl_Forall.
    contradict Hf; eauto.
  Qed.

    (* TODO: définition un peu foireuse, qui doit correspondre aux
     inversions de wt_block... *)
  Definition get_locals (blk : block) : static_env :=
    match blk with
    | Blocal (Scope vars _) => senv_of_decls vars
    | _ => []
    end.

  Corollary NoDup_iol :
    forall (n : node),
      NoDupMembers (senv_of_ins (n_in n) ++ senv_of_decls (n_out n) ++ get_locals (n_block n)).
  Proof.
    intro.
    pose proof (node_NoDupMembers n) as ND.
    destruct (n_block n) eqn:Hn; simpl; try rewrite app_nil_r; auto.
    destruct s.
    apply NoDup_senv_loc in Hn; auto.
  Qed.

  Fixpoint get_defined (blk : block) : list ident :=
    match blk with
    | Beq (xs,es) => xs
    | Blocal (Scope vars blks) => flat_map get_defined blks
    | _ => []
    end.

  Lemma NoDup_vars_ins :
    forall (nd : node) vars blks,
      Forall restr_block blks ->
      n_block nd = Blocal (Scope vars blks) ->
      NoDup (flat_map get_defined blks ++ List.map fst (n_in nd)).
  Proof.
    intros * Hr Hn.
    apply NoDup_senv_loc in Hn as ndm.
    pose proof (n_defd nd) as (outs & Vd & Perm).
    rewrite Hn in Vd.
    inv Vd. Syn.inv_scope.
    rewrite Perm in H0.
    assert (Permutation (List.map fst (concat x)) (flat_map get_defined blks)) as <-.
    { clear - H Hr.
      induction H; inv Hr; simpl; auto.
      rewrite map_app.
      apply Permutation_app; auto.
      take (restr_block _) and inv it.
      inv H; simpl in *; subst.
      reflexivity.
    }
    rewrite Permutation_app_comm, H0, <- map_fst_senv_of_ins, <- map_app.
    now rewrite <- fst_NoDupMembers.
  Qed.

  Lemma nin_defined :
    forall (n : node) vars blks x,
      n_block n = Blocal (Scope vars blks) ->
      In x (List.map fst (senv_of_decls (n_out n) ++ senv_of_decls vars)) ->
      List.Exists (Syn.Is_defined_in (Var x)) blks.
  Proof.
    intros * Hn Hxin.
    pose proof (n_nodup n) as (Nd & Ndl).
    pose proof (n_defd n) as (?& Vd & Perm).
    rewrite Hn in Vd, Ndl.
    inv Ndl; take (NoDupScope _ _ _) and inv it.
    inv Vd; Syn.inv_scope.
    eapply Forall_VarsDefined_Is_defined; eauto.
    + take (Permutation (concat _) _) and rewrite it.
      take (Permutation x0 _) and rewrite it.
      rewrite map_app, 2 map_fst_senv_of_decls.
      simpl_Forall.
      eapply NoDupLocals_incl; eauto.
      solve_incl_app.
    + take (Permutation (concat _) _) and rewrite it.
      take (Permutation x0 _) and rewrite it.
      rewrite fst_InMembers; auto.
  Qed.
  End COMMUN_SAFE.

  (* TODO: généraliser, bouger dans Denot ? *)
  Lemma denot_node_input :
    forall G nd envG envI env x,
      restr_node nd ->
      In x (List.map fst nd.(n_in)) ->
      denot_node G nd envG envI env x = 0.
  Proof.
    clear.
    intros * Hr Hin.
    rewrite denot_node_eq, denot_top_block_eq.
    inversion Hr as [?? Hfr Hnd].
    apply symmetry, NoDup_vars_ins in Hnd; auto.
    rewrite denot_blocks_eq.
    induction blks; simpl in *; inv Hfr; auto.
    rewrite denot_block_eq.
    rewrite <- app_assoc in Hnd.
    cases; eauto using NoDup_app_r.
    rewrite env_of_np_ext_eq.
    cases_eqn Hmem; eauto using NoDup_app_r.
    apply mem_nth_In in Hmem.
    contradict Hnd; simpl; intro.
    eapply NoDup_app_In in Hin; eauto.
    rewrite Permutation_app_comm; solve_NoDup_app.
  Qed.

  (* TODO: move, inutile ?? *)
  Lemma P_vars_cons :
    forall n env x l,
      P_var n env x ->
      P_vars n env l ->
      P_vars n env (x :: l).
  Proof.
    unfold P_vars.
    simpl; intros * ??? []; subst; eauto.
  Qed.

  (* TODO: move *)
  Lemma locals_restr_blocks :
    forall (blks : list block),
      Forall restr_block blks ->
      flat_map idcaus_of_locals blks = [].
  Proof.
    induction 1 as [|?? Hr]; auto; now inv Hr.
  Qed.


  (* TODO: move *)
  Lemma get_idcaus_locals :
    forall (nd : node),
      restr_node nd ->
      map fst (get_locals (n_block nd)) = map snd (idcaus_of_locals (n_block nd)).
  Proof.
    intros * Hr.
    pose proof (n_syn nd) as Noloc; inv Noloc.
    inversion Hr as [?? Hrb Hnd]; rewrite <- Hnd in *; simpl.
    rewrite locals_restr_blocks, app_nil_r; auto.
    take (nolocal_top_block _) and inv it.
    rewrite <- idcaus_of_decls_map, map_fst_senv_of_decls; auto.
  Qed.
          Lemma HasCaus_In :
          forall x cx Γ,
            HasCaus Γ x cx ->
            In x (map fst Γ).
          Proof.
            intros * Hc.
            inv Hc.
            now apply (in_map fst) in H.
          Qed.

  (** L'étape d'induction pour P_var sur les nœuds, qui utilise [exp_S].
      On le prouve direcement pour toute variable et pas seulement
      dans [n_out nd], grâce à [denot_blocks] qui initialise son
      accumulateur avec des flots infinis. *)
  (* TODO: màj du commentaire s'il n'est plus vrai *)
  Lemma denot_S :
    forall nd envI n,
      restr_node nd ->
      wl_node G nd ->
      wx_node nd ->
      node_causal nd ->
      P_vars (S n) envI (map fst (n_in nd)) ->
      P_vars n (FIXP _ (denot_node G nd envG envI)) (map fst (n_out nd) ++ map fst (get_locals (n_block nd))) ->
      P_vars (S n) (FIXP _ (denot_node G nd envG envI)) (map fst (n_out nd) ++ map fst (get_locals (n_block nd))).
  Proof.
    intros * Hr Hwl Hwx Hcaus Hins.
    set (ins := map fst (n_in nd)) in *.
    set (env := FIXP _ _).
    intro Hn.
    eapply node_causal_ind
      (* le résultat n'est pas vrai sur les ins ! *)
      (* with (P_vars := P_vars (S n) env) *)
      with (P_vars := fun l => forall x, In x l -> ~ In x ins -> P_var (S n) env x)
      in Hcaus as (lord & Perm3 & Hlord).
    - intros x Hin; apply Hlord.
      + (* on prouve l'inclusion : *)
        pose proof (n_syn nd) as Noloc; inv Noloc.
        rewrite Perm3, 2 map_app, <- idcaus_of_decls_map, <- get_idcaus_locals; auto.
        rewrite 2 in_app_iff in *; tauto.
      + (* et la non-duplication *)
        pose proof (Nd := NoDup_iol nd).
        apply fst_NoDupMembers in Nd.
        rewrite 2 map_app, Permutation_app_comm, map_fst_senv_of_ins, map_fst_senv_of_decls in Nd.
        eapply NoDup_app_In in Nd; eauto.
    - inversion 1.
    - intros y ys Hxin Hys Hdep.
      intros x [] Hxnins; subst; auto.
      rewrite <- in_app_iff, map_app, <- app_assoc, in_app_iff in Hxin.
      destruct Hxin as [Hxin|Hxin].
      + (* x ∈ ins, contradiction *)
        rewrite idcaus_map in Hxin; contradiction.
      + (* x est une sortie ou une locale, on utilise laborieusement P_var_inside_blocks *)
        inv Hwx; inv Hwl.
        inversion Hr as [??? Hnd].
        rewrite <- Hnd in *; simpl in Hxin, Hn.
        rewrite locals_restr_blocks, app_nil_r in Hxin; auto.
        unfold env; rewrite FIXP_eq; fold env.
        rewrite denot_node_eq, denot_top_block_eq, <- Hnd.
        take (wl_block _ _) and inv it.
        take (wl_scope _ _ _) and inv it.
        take (wx_block _ _) and inv it.
        take (wx_scope _ _ _) and inv it.
        eapply P_var_inside_blocks; eauto using is_ncons_bss.
        * subst Γ' Γ; intros y cy Hin Hnins.
          apply HasCausInj in Hin as ?; subst.
          apply HasCaus_In in Hin.
          rewrite 2 map_app, 2 map_fst_senv_of_decls, map_fst_senv_of_ins, <- app_assoc in *.
          apply in_app_or in Hin as []; auto; contradiction.
        * intros y Hex Hnins.
          apply Hys in Hnins; auto; apply Hdep.
          constructor; rewrite <- Hnd; constructor; econstructor; eauto.
        * pose proof (n_syn nd) as Noloc; inv Noloc.
          rewrite <- Hnd in *; inv H0.
          (* TODO: faire des idcaus_of_decls_map spécialisés aux nœuds, là c'est vraiment trop chiant *)
          rewrite <- 2 idcaus_of_decls_map in Hxin; auto.
          eapply nin_defined; eauto.
          now rewrite map_app, 2 map_fst_senv_of_decls.
  Qed.

  Theorem denot_n :
    forall nd envI n,
      restr_node nd ->
      wl_node G nd ->
      wx_node nd ->
      node_causal nd ->
      P_vars n envI (map fst (n_in nd)) ->
      P_vars n (FIXP _ (denot_node G nd envG envI)) (map fst (n_out nd) ++ map fst (get_locals (n_block nd))).
  Proof.
    intros * Hr Hwl Hwx Hcaus Hins.
    revert Hr Hwl Hwx Hcaus Hins.
    revert nd envI.
    induction n; intros.
    - apply P_vars_O.
    - apply denot_S; auto.
      apply IHn; auto using P_vars_S.
  Qed.

  End Node_n.


  (** Using the well-ordered property of programs, show that all nodes
      receiving streams of length n outputs streams of length n. *)

  Theorem denot_global_n :
    forall n G f nd envI,
      restr_global G ->
      wt_global G ->
      Forall node_causal (nodes G) ->
      find_node f G = Some nd ->
      P_vars n envI (map fst (n_in nd)) ->
      P_vars n (denot_global G f envI) (map fst (n_out nd) ++ map fst (get_locals (n_block nd))).
  Proof.
    intros * Hr Hwt Hcaus Hfind Hins.
    assert (Ordered_nodes G) as Hord.
    now apply wl_global_Ordered_nodes, wt_global_wl_global.
    unfold denot_global.
    rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl, denot_global_eq.
    rewrite Hfind.
    remember (FIXP (Dprodi FI) (denot_global_ G)) as envG eqn:HF.
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
    revert Hins HenvG Hfind. revert envI envG n f nd.
    destruct G as [tys exts nds]; simpl in *.
    induction nds as [|a nds]; simpl; intros. inv Hfind.
    inv Hcaus. inv Hr.
    destruct (ident_eq_dec (n_name a) f); subst.
    + (* cas intéressant *)
      rewrite find_node_now in Hfind; inv Hfind; auto.
      rewrite <- denot_node_cons;
        eauto using find_node_not_Is_node_in, find_node_now.
      apply denot_n; eauto using wt_global_uncons, wt_node_wl_node, wt_node_wx_node.
      intros m f nd2 envI2 Hfind2 HI2.
      eapply find_node_uncons with (nd := nd) in Hfind2 as ?; auto.
      rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
      eapply P_vars_app_r.
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
  Qed.

  End Top.

Section MOVE_ME.

Lemma inf_dom_env_of_np :
  forall  l m (mp : nprod m),
    forall_nprod (@infinite _) mp ->
    infinite_dom (env_of_np l mp) l.
Proof.
  unfold infinite_dom.
  intros.
  rewrite env_of_np_eq.
  destruct (mem_nth l x) as [i|] eqn:Hmem.
  - apply forall_nprod_k_def; auto; apply DS_const_inf.
  - apply mem_nth_nin in Hmem; tauto.
Qed.


End MOVE_ME.

(** Maintenant on passe à l'infini *)

Lemma infinite_P_vars :
  forall env l, infinite_dom env l <-> (forall n, P_vars n env l).
Proof.
  intro env.
  unfold P_vars, P_var, infinite_dom.
  setoid_rewrite PROJ_simpl.
  split; eauto using nrem_inf, inf_nrem.
Qed.

Theorem denot_inf :
  forall (HasCausInj : forall Γ x cx, HasCaus Γ x cx -> cx = x),
  forall (G : global),
    restr_global G ->
    wt_global G ->
    Forall node_causal (nodes G) ->
    forall f nd envI,
      find_node f G = Some nd ->
      infinite_dom envI (List.map fst (n_in nd)) ->
      infinite_dom (denot_global G f envI) (List.map fst (n_out nd) ++ map fst (get_locals (n_block nd))).
Proof.
  intros.
  rewrite infinite_P_vars in *.
  intro.
  eapply denot_global_n; eauto.
Qed.

Lemma sbools_ofs_inf :
  forall n (np : nprod n),
    forall_nprod (@infinite _) np ->
    infinite (sbools_of np).
Proof.
  induction n; intros * Hf; simpl.
  - apply DS_const_inf.
  - apply forall_nprod_inv in Hf as [Hh Ht].
    unfold sbools_of.
    autorewrite with cpodb.
    rewrite Fold_eq, lift_hd, lift_tl.
    apply zip_inf.
    + apply map_inf; auto.
    + apply (IHn _ Ht).
Qed.


(** Une fois l'infinité des flots obtenue, on peut l'utiliser pour
    prouver l'infinité des expressions. *)
Lemma infinite_exp :
  forall G ins envI (envG : Dprodi FI) bs env,
    (forall f nd envI,
        find_node f G = Some nd ->
        infinite_dom envI (List.map fst (n_in nd)) ->
        infinite_dom (envG f envI) (List.map fst (n_out nd))) ->
    infinite bs ->
    forall Γ, (forall x, IsVar Γ x -> infinite (denot_var ins envI env x)) ->
    forall e, wx_exp Γ e -> wl_exp G e ->
    forall_nprod (@infinite _) (denot_exp G ins e envG envI bs env).
Proof.
  intros * HG Hbs ? Hvar e Hwx Hwl.
  induction e using exp_ind2; inv Hwx; inv Hwl; simpl; setoid_rewrite denot_exp_eq.
  (* cas restreints : *)
  all: eauto; try apply forall_nprod_const; try apply DS_const_inf.
  - (* Econst *)
    apply sconst_inf; auto.
  - (* Eenum *)
    apply sconst_inf; auto.
  - (* Eunop *)
    revert IHe.
    gen_sub_exps.
    intros; cases; simpl in *; eauto using sunop_inf, DS_const_inf.
  - (* Ebinop *)
    revert IHe1 IHe2.
    gen_sub_exps.
    intros; cases; simpl in *; eauto using sbinop_inf, DS_const_inf.
  - (* Efby *)
    apply Forall_impl_inside with (P := wx_exp _) in H0,H; auto.
    apply Forall_impl_inside with (P := wl_exp _) in H0,H; auto.
    apply forall_denot_exps in H, H0.
    unfold eq_rect.
    cases; eauto using forall_nprod_const, DS_const_inf.
    eapply forall_nprod_lift2; eauto using fby_inf; cases.
  - (* Ewhen *)
    apply Forall_impl_inside with (P := wx_exp _) in H; auto.
    apply Forall_impl_inside with (P := wl_exp _) in H; auto.
    apply forall_denot_exps in H.
    unfold eq_rect.
    cases; eauto using forall_nprod_const, DS_const_inf.
    eapply forall_nprod_llift; eauto using swhen_inf; cases.
  - (* Emerge *)
    eapply forall_lift_nprod; eauto using smerge_inf.
    unfold eq_rect_r, eq_rect, eq_sym; cases.
    apply forall_denot_expss.
    unfold eq_rect.
    simpl_Forall.
    apply Forall_impl_inside with (P := wx_exp _) in H; auto.
    apply Forall_impl_inside with (P := wl_exp _) in H; auto.
    cases; eauto using forall_nprod_const, map_inf.
    now apply forall_denot_exps.
  - (* Ecase *)
    eapply Forall_impl_In in H.
    2:{ intros ? Hin HH.
        apply Forall_impl_inside with (P := wx_exp _) in HH;[| now simpl_Forall].
        apply Forall_impl_inside with (P := wl_exp _) in HH;[| now simpl_Forall].
        eapply (proj2 (forall_denot_exps _ _ _ _ _ _ _ _ )), HH. }
    eapply forall_forall_denot_expss with (n := length tys) in H as Hess;
      eauto using map_inf.
    destruct d.
    + (* défaut *)
      apply Forall_impl_inside with (P := wx_exp _) in H0; auto.
      apply Forall_impl_inside with (P := wl_exp _) in H0; auto.
      apply forall_denot_exps in H0 as Hd.
      revert Hess IHe Hd.
      gen_sub_exps.
      unfold eq_rect_r, eq_rect, eq_sym; cases; intros;
        eauto using forall_nprod_const, DS_const_inf.
      simpl in *|-.
      eapply forall_lift_nprod; eauto using scase_def_inf, forall_nprod_cons.
    + (* total *)
      revert Hess IHe.
      gen_sub_exps.
      unfold eq_rect_r; cases; intros; eauto using forall_nprod_const, DS_const_inf.
      simpl in *|-.
      eapply forall_lift_nprod; eauto using scase_inf.
      unfold eq_rect, eq_sym; cases.
  - (* Eapp *)
    apply Forall_impl_inside with (P := wx_exp _) in H, H0; auto.
    apply Forall_impl_inside with (P := wl_exp _) in H, H0; auto.
    apply forall_denot_exps in H, H0.
    unfold eq_rect.
    take (find_node _ _ = _) and rewrite it.
    cases; eauto using forall_nprod_const, DS_const_inf.
    apply forall_np_of_env'; intros x Hxout.
    eapply sreset_inf_dom; eauto.
    + apply sbools_ofs_inf; auto.
    + apply inf_dom_env_of_np; auto.
Qed.

Corollary infinite_exps :
  forall G ins (envG : Dprodi FI) envI bs env,
    (forall f nd envI,
        find_node f G = Some nd ->
        infinite_dom envI (List.map fst (n_in nd)) ->
        infinite_dom (envG f envI) (List.map fst (n_out nd))) ->
    infinite bs ->
    forall Γ, (forall x, IsVar Γ x -> infinite (denot_var ins envI env x)) ->
    forall es, Forall (wx_exp Γ) es -> Forall (wl_exp G) es ->
    forall_nprod (@infinite _) (denot_exps G ins es envG envI bs env).
Proof.
  induction es; simpl; auto; intros; simpl_Forall.
  setoid_rewrite denot_exps_eq.
  eauto using forall_nprod_app, infinite_exp.
Qed.

Corollary infinite_expss :
  forall G ins (envG : Dprodi FI) envI bs env,
    (forall f nd envI,
        find_node f G = Some nd ->
        infinite_dom envI (List.map fst (n_in nd)) ->
        infinite_dom (envG f envI) (List.map fst (n_out nd))) ->
    infinite bs ->
    forall Γ, (forall x, IsVar Γ x -> infinite (denot_var ins envI env x)) ->
    forall I (ess : list (I * list exp)) n,
    Forall (fun es => Forall (wx_exp Γ) (snd es)) ess ->
    Forall (fun es => Forall (wl_exp G) (snd es)) ess ->
    forall_nprod (forall_nprod (@infinite _)) (denot_expss G ins ess n envG envI bs env).
Proof.
  induction ess as [| (i,es) ess]; intros * Hwx Hwl. { now simpl. }
  setoid_rewrite denot_expss_eq.
  inv Hwx; inv Hwl.
  unfold eq_rect.
  cases; eauto using forall_nprod_const, map_inf.
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
