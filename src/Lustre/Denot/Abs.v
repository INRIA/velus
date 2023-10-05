From Coq Require Import Datatypes List.
Import List.ListNotations.

From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LOrdered.

From Velus Require Import Lustre.Denot.Cpo.
Require Import CommonDS SDfuns Denot CommonList2.


(** ** Pas de réaction et pas de changement d'état en cas d'absence, soit
 * f (abs.x) = abs.f(x)
 * remarque (pour la thèse) : ça n'est pas vrai en signal,
 * à cause de la construction default *)

(* TODO: expliquer le <= ? , renommage général dans ce fichier !! *)
(* TODO: trouver un nom au prédicat. Propositions :
   - stutter independence
   - absence commutation
   - postpone
   - stall (voiture qui cale ?)
 *)
Module Type ABS_INDEP
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Typ   : LTYPING       Ids Op OpAux Cks Senv Syn)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Import Den   : LDENOT        Ids Op OpAux Cks Senv Syn Lord).


(* TODO: mettre dans Denot.v *)
(* XXXXXXXXXXXXXXXXXXXXXXXXX *)
Lemma np_of_env_cons :
  forall i l env,
    np_of_env (i :: l) env
    = nprod_cons (env i) (np_of_env l env).
Proof.
  trivial.
Qed.

(* XXXXXXXXXXXXXXXXXXXXXXXXX *)

(** ** Résultats généraux sur l'indépendance aux absences *)

Lemma np_of_env_abs :
  forall l env,
    np_of_env l (APP_env abs_env env) == lift (CONS abs) (np_of_env l env).
Proof.
  induction l; intros.
  - cbn; unfold abss.
    now rewrite <- DS_const_eq.
  - rewrite 2 (np_of_env_cons a l), IHl.
    setoid_rewrite (lift_cons (CONS abs) _ (env a) (np_of_env l env)).
    apply nprod_cons_Oeq_compat; auto.
    unfold abs_env, abss.
    now rewrite DS_const_eq, APP_env_eq, APP_simpl, app_cons.
Qed.

Lemma env_of_np_abs :
  forall l (np : nprod (length l)),
    env_of_np l (lift (CONS abs) np) <= APP_env abs_env (env_of_np l np).
Proof.
  intros; subst; intro x.
  rewrite APP_env_eq, 2 env_of_np_eq.
  cases_eqn HH.
  apply mem_nth_Some with (d := xH) in HH as []; subst.
  unfold abs_env, abss.
  erewrite DS_const_eq, APP_simpl, app_cons, nth_lift; auto.
Qed.

Lemma env_of_np_ext_abs :
  forall l n (np : nprod n) acc,
    n = length l ->
    env_of_np_ext l (lift (CONS abs) np) (APP_env abs_env acc)
    == APP_env abs_env (env_of_np_ext l np acc).
Proof.
  intros; subst.
  apply Oprodi_eq_intro; intro x.
  rewrite APP_env_eq, 2 env_of_np_ext_eq, APP_env_eq.
  cases_eqn HH.
  apply mem_nth_Some with (d := xH) in HH as []; subst.
  unfold abs_env, abss.
  erewrite DS_const_eq, APP_simpl, app_cons, nth_lift; auto.
Qed.


(** ** On montre que chaque opérateur du langage a cette propriété *)

Lemma abs_indep_fby :
  forall A (xs ys : DS (sampl A)),
    fby (cons abs xs) (cons abs ys) == cons abs (fby xs ys).
Proof.
  intros.
  now rewrite fby_eq, fbyA_eq.
Qed.

Corollary abs_indep_lift_fby :
  forall A n (xs ys : @nprod (DS (sampl A)) n),
    lift2 fby (lift (CONS abs) xs) (lift (CONS abs) ys)
    == lift (CONS abs) (lift2 fby xs ys).
Proof.
  induction n as [|[]]; intros.
  - apply abs_indep_fby.
  - apply abs_indep_fby.
  - apply Dprod_eq_intro.
    + simpl; apply abs_indep_fby.
    + apply IHn.
Qed.

Lemma abs_indep_swhenv :
  forall b xs cs,
    swhenv b (cons abs xs) (cons abs cs) == cons abs (swhenv b xs cs).
Proof.
  intros.
  unfold swhenv.
  now rewrite swhen_eq.
Qed.

Corollary abs_indep_lift_swhenv :
  forall b n (np : nprod n) cs,
    llift (swhenv b) (lift (CONS abs) np) (cons abs cs)
    == lift (CONS abs) (llift (swhenv b) np cs).
Proof.
  induction n as [|[]]; intros.
  - apply abs_indep_swhenv.
  - apply abs_indep_swhenv.
  - apply Dprod_eq_intro.
    + destruct np as (t1,t2).
      setoid_rewrite (llift_simpl _ (swhenv b) _ cs t1 t2).
      now setoid_rewrite <- abs_indep_swhenv.
    + apply IHn.
Qed.

Lemma abs_indep_smergev :
  forall l xs np,
    smergev l (cons abs xs) (lift (CONS abs) np) == cons abs (smergev l xs np).
Proof.
  intros.
  unfold smergev.
  rewrite 2 smerge_eq.
  induction l as [|i l].
  - now rewrite 2 Foldi_nil, map_eq_cons.
  - now rewrite 2 Foldi_cons, lift_tl, lift_hd, IHl, CONS_simpl, zip3_cons.
Qed.

Corollary abs_indep_lift_smergev :
  forall l xs n (np : @nprod (nprod n) _),
    lift_nprod (smergev l (cons abs xs)) (lift (lift (CONS abs)) np)
    == lift_nprod (CONS abs @_ smergev l xs) np.
Proof.
  induction n; intro.
  - apply abs_indep_smergev.
  - rewrite 2 lift_nprod_simpl.
    apply nprod_cons_Oeq_compat.
    + setoid_rewrite <- abs_indep_smergev.
      rewrite 2 lift_lift.
      apply fcont_stable, lift_ext.
      destruct n; auto.
    + rewrite <- IHn.
      rewrite 2 lift_lift.
      apply fcont_stable, lift_ext.
      destruct n; auto.
Qed.

Lemma abs_indep_scasev :
  forall l xs np,
    scasev l (cons abs xs) (lift (CONS abs) np) == cons abs (scasev l xs np).
Proof.
  intros.
  unfold scasev.
  rewrite 2 scase_eq.
  induction l as [|i l].
  - now rewrite 2 Foldi_nil, map_eq_cons.
  - now rewrite 2 Foldi_cons, lift_tl, lift_hd, IHl, CONS_simpl, zip3_cons.
Qed.

Corollary abs_indep_lift_scasev :
  forall l xs n (np : @nprod (nprod n) _),
    lift_nprod (scasev l (cons abs xs)) (lift (lift (CONS abs)) np)
    == lift_nprod (CONS abs @_ scasev l xs) np.
Proof.
  induction n; intro.
  - apply abs_indep_scasev.
  - rewrite 2 lift_nprod_simpl.
    apply nprod_cons_Oeq_compat.
    + setoid_rewrite <- abs_indep_scasev.
      rewrite 2 lift_lift.
      apply fcont_stable, lift_ext.
      destruct n; auto.
    + rewrite <- IHn.
      rewrite 2 lift_lift.
      apply fcont_stable, lift_ext.
      destruct n; auto.
Qed.

Lemma abs_indep_scase_defv :
  forall l xs ds np,
    scase_defv l (cons abs xs) (nprod_cons (cons abs ds) (lift (CONS abs) np))
    == cons abs (scase_defv l xs (nprod_cons ds np)).
Proof.
  intros.
  unfold scase_defv.
  rewrite 2 scase_def_eq, 2 scase_def__eq.
  induction l as [|i l].
  - now rewrite 2 Foldi_nil, zip_cons.
  - now rewrite 2 Foldi_cons, lift_tl, lift_hd, IHl, CONS_simpl, zip3_cons.
Qed.

Corollary abs_indep_lift_scase_defv :
  forall l xs n ds (np : @nprod (nprod n) _),
    lift_nprod (scase_defv l (cons abs xs)) (nprod_cons (lift (CONS abs) ds) (lift (lift (CONS abs)) np))
    == lift_nprod (CONS abs @_ scase_defv l xs) (nprod_cons ds np).
Proof.
  induction n; intros.
  - apply abs_indep_scase_defv.
  - rewrite 2 lift_nprod_simpl, 4 lift_cons.
    rewrite <- IHn, lift_tl, lift_hd, fcont_comp_simpl.
    apply nprod_cons_Oeq_compat.
    + rewrite <- (abs_indep_scase_defv _ xs (nprod_hd ds) (lift nprod_hd np)), 2 lift_lift.
      apply fcont_stable, nprod_cons_Oeq_compat; auto.
      apply lift_ext; destruct n; auto.
    + apply fcont_stable, nprod_cons_Oeq_compat; auto.
      rewrite 2 lift_lift.
      apply lift_ext; destruct n; auto.
Qed.

Lemma abs_indep_sreset_aux :
  forall f bs (X Y : DS_prod SI),
    sreset_aux f (cons false bs) (APP_env abs_env X) (APP_env abs_env Y)
    == APP_env abs_env (sreset_aux f bs X Y).
Proof.
  intros.
  rewrite sreset_aux_eq.
  rewrite 2 rem_app_env; try apply all_cons_abs_env.
  apply Oprodi_eq_intro; intro x.
  unfold abs_env, abss.
  now rewrite DS_const_eq, 3 APP_env_eq, 3 APP_simpl, 3 app_cons.
Qed.

Lemma bss_app_abs :
  forall l (env : DS_prod SI),
    bss l (APP_env abs_env env) == cons false (bss l env).
Proof.
  induction l as [| x l]; intro env.
  - simpl.
    autorewrite with cpodb.
    now rewrite <- DS_const_eq.
  - unfold abs_env, abss.
    now rewrite 2 bss_cons, IHl, APP_env_eq, DS_const_eq,
      APP_simpl, app_cons, AC_cons, zip_cons.
Qed.

Lemma sbools_of_abs :
  forall n (np : nprod n),
    sbools_of (lift (CONS abs) np) == cons false (sbools_of np).
Proof.
  induction n; intros.
  - cbn; now rewrite <- DS_const_eq.
  - unfold sbools_of.
    autorewrite with cpodb.
    rewrite 2 Fold_eq.
    rewrite 3 lift_tl, 3 lift_hd, (IHn (nprod_tl np)).
    unfold sbool_of at 1.
    rewrite MAP_map, CONS_simpl, map_eq_cons, zip_cons; auto.
Qed.


(** ** Raisonnement sur les nœuds *)

Section Abs_indep_node.

  Variables
    (G : global)
    (envG : Dprodi FI).

  Hypothesis Hnode :
    forall f n envI,
      (* TODO: hypothèse qui va sauter avec une induction sur le point fixe global ? *)
      find_node f G = Some n ->
      envG f (APP_env abs_env envI) <= APP_env abs_env (envG f envI).


 (* utile pour les cas récursifs *)
  Lemma lift_IH :
    forall ins es envG envI bs env aenv,
      Forall (fun e => denot_exp G ins e envG (APP_env abs_env envI) (cons false bs) aenv
                    <= lift (CONS abs) (denot_exp G ins e envG envI bs env)) es ->
      denot_exps G ins es envG (APP_env abs_env envI) (cons false bs) aenv
      <= lift (CONS abs) (denot_exps G ins es envG envI bs env).
  Proof.
    induction es; intros * Hf; inv Hf.
    - now rewrite 2 denot_exps_nil, map_eq_cons.
    - rewrite 2 denot_exps_eq.
      setoid_rewrite lift_app; auto.
  Qed.

  (* idem *)
  Lemma lift_IHs :
    forall ins (ess : list (enumtag * _)) n envG envI bs env aenv,
      Forall (fun es =>
                Forall (fun e =>
                          denot_exp G ins e envG (APP_env abs_env envI) (cons false bs) aenv
                          <= lift (CONS abs) (denot_exp G ins e envG envI bs env)) (snd es)) ess ->
      denot_expss G ins ess n envG (APP_env abs_env envI) (cons false bs) aenv
      <= lift (lift (CONS abs)) (denot_expss G ins ess n envG envI bs env).
  Proof.
    intros * Hf.
    induction ess as [|(x,es)]; inv Hf.
    - rewrite 2 denot_expss_nil, map_eq_cons.
      cbn; now rewrite lift_nprod_const.
    - rewrite 2 denot_expss_eq.
      unfold eq_rect.
      cases; subst.
      + match goal with
          |-_ <= _ (_ (_ ?a) ?b) =>
            setoid_rewrite (lift_cons (lift (CONS abs)) _ a b)
        end; auto using lift_IH.
      + simpl (length _).
        now rewrite 2 lift_nprod_const, map_eq_cons.
  Qed.

  Lemma var_abs_le :
    forall ins x envI env aenv,
      aenv <= APP_env abs_env env ->
      denot_var ins (APP_env abs_env envI) aenv x
      <= cons abs (denot_var ins envI env x).
  Proof.
    intros * Hle.
    specialize (Hle x).
    revert Hle; unfold denot_var, abs_env, abss.
    rewrite 2 APP_env_eq, 2 APP_simpl, DS_const_eq, 2 app_cons; cases.
  Qed.

  Lemma abs_indep_exp :
    forall Γ ins e envI bs env aenv,
      restr_exp e ->
      wt_exp G Γ e ->
      wl_exp G e ->
      aenv <= APP_env abs_env env ->
      denot_exp G ins e envG (APP_env abs_env envI) (cons false bs) aenv
      <= lift (CONS abs) (denot_exp G ins e envG envI bs env).
  Proof.
    intros * Hr Hwt Hwl Hle.
    induction e using exp_ind2; inv Hr.
    - (* Econst *)
      rewrite 2 denot_exp_eq.
      unfold sconst.
      rewrite MAP_map, map_eq_cons; auto.
    - (* Evar *)
      rewrite 2 denot_exp_eq.
      now apply var_abs_le.
    - (* Eunop *)
      inv Hwt. inv Hwl.
      rewrite 2 (denot_exp_eq _ _ (Eunop _ _ _)).
      revert IHe.
      gen_sub_exps.
      take (numstreams _ = _) and rewrite it.
      take (typeof _ = _) and rewrite it.
      cbv zeta; intros t1 t2 IHe.
      eapply Ole_trans with (sunop _ (lift _ t1)); auto.
      setoid_rewrite (CONS_simpl abs).
      now rewrite sunop_eq.
    - (* Ebinop *)
      inv Hwt. inv Hwl.
      rewrite 2 (denot_exp_eq _ _ (Ebinop _ _ _ _)).
      revert IHe1 IHe2.
      gen_sub_exps.
      do 2 (take (numstreams _ = _) and rewrite it; clear it).
      do 2 (take (typeof _ = _) and rewrite it; clear it).
      cbv zeta; intros t1 t2 t3 t4 IHe1 IHe2.
      eapply Ole_trans with (sbinop _ (lift _ t3) (lift _ t1)); auto.
      setoid_rewrite (CONS_simpl abs).
      now rewrite sbinop_eq.
    - (* Efby *)
      inv Hwt. inv Hwl.
      apply Forall_impl_inside with (P := restr_exp) in H, H0; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H, H0; auto.
      apply Forall_impl_inside with (P := wl_exp _ ) in H, H0; auto.
      apply lift_IH in H, H0; revert H H0.
      rewrite 2 (denot_exp_eq _ _ (Efby _ _ _)).
      gen_sub_exps.
      rewrite annots_numstreams in *.
      simpl; unfold eq_rect; cases; try congruence.
      intros t1 t2 t3 t4 Le1 Le2.
      rewrite <- abs_indep_lift_fby; auto.
    - (* Ewhen *)
      inv Hwt. inv Hwl.
      apply Forall_impl_inside with (P := restr_exp) in H; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H; auto.
      apply Forall_impl_inside with (P := wl_exp _ ) in H; auto.
      apply lift_IH in H; revert H.
      rewrite 2 (denot_exp_eq _ _ (Ewhen _ _ _ _)).
      gen_sub_exps.
      rewrite annots_numstreams in *.
      simpl; unfold eq_rect; cases; try congruence.
      intros t1 t2 Le.
      rewrite <- abs_indep_lift_swhenv.
      auto using (var_abs_le ins x0 envI _ _ Hle).
    - (* Emerge *)
      inv Hwt. inv Hwl.
      rewrite 2 (denot_exp_eq _ _ (Emerge _ _ _)).
      pose proof (IH := lift_IHs ins es (length tys) envG envI bs env aenv).
      eassert (Le: _ <= _); [apply IH; simpl_Forall; auto|clear IH].
      cbv zeta; revert Le.
      gen_sub_exps; intros t1 t2 Le.
      unfold eq_rect_r, eq_rect, eq_sym; cases.
      rewrite lift_lift_nprod, <- abs_indep_lift_smergev.
      auto using (var_abs_le ins x0 envI _ _ Hle).
    - (* Ecase total *)
      inv Hwt. inv Hwl.
      rewrite 2 (denot_exp_eq _ _ (Ecase _ _ _ _)).
      pose proof (IH := lift_IHs ins es (length tys) envG envI bs env aenv).
      eassert (Le: _ <= _); [apply IH; simpl_Forall; auto|clear IH].
      cbv zeta; revert IHe Le; gen_sub_exps.
      take (numstreams e = 1) and rewrite it.
      unfold eq_rect_r, eq_rect, eq_sym; cases.
      intros t1 t2 t3 t4 Le1 Le2.
      rewrite lift_lift_nprod, <- abs_indep_lift_scasev; auto.
    - (* Ecase défaut *)
      inv Hwt. inv Hwl.
      set (typesof des) as tys.
      apply Forall_impl_inside with (P := restr_exp) in H0; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H0; auto.
      apply Forall_impl_inside with (P := wl_exp _ ) in H0; auto.
      apply lift_IH in H0.
      pose proof (IH := lift_IHs ins es (length tys) envG envI bs env aenv).
      eassert (Le: _ <= _); [apply IH; simpl_Forall; auto|clear H IH].
      rewrite 2 (denot_exp_eq _ _ (Ecase _ _ _ _)).
      cbv zeta; revert IHe H0 Le; gen_sub_exps.
      assert (Hl : list_sum (List.map numstreams des) = length tys)
        by (subst tys; now rewrite length_typesof_annots, annots_numstreams).
      take (numstreams e = 1) and rewrite it, Hl.
      simpl (numstreams _). (* dans les types... *)
      unfold eq_rect_r, eq_rect, eq_sym; cases; try congruence.
      intros t1 t2 t3 t4 t5 t6 Le1 Le2 Le3.
      rewrite lift_lift_nprod, <- abs_indep_lift_scase_defv; auto.
    - (* Eapp *)
      inv Hwt. inv Hwl.
      apply Forall_impl_inside with (P := restr_exp) in H, H0; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H, H0; auto.
      apply Forall_impl_inside with (P := wl_exp _ ) in H, H0; auto.
      apply lift_IH in H, H0; revert H H0.
      rewrite 2 (denot_exp_eq _ _ (Eapp _ _ _ _)).
      gen_sub_exps.
      take (find_node f G = _) and rewrite it in *.
      repeat take (Some _ = Some _) and inv it.
      assert (Hl : list_sum (List.map numstreams es) = length (idents (n_in n)))
        by (now unfold idents; rewrite map_length, annots_numstreams in * ).
      simpl; take (length a = _) and rewrite it, Hl.
      unfold eq_rect; cases; try (rewrite map_length in *; tauto).
      intros t1 t2 t3 t4 Le1 Le2.
      rewrite 2 sreset_eq, <- np_of_env_abs.
      rewrite <- abs_indep_sreset_aux, <- sbools_of_abs.
      apply fcont_monotonic, fcont_le_compat3; eauto 3 using env_of_np_abs.
      eapply Ole_trans, (Hnode _ n); eauto 4 using env_of_np_abs.
  Qed.

  Corollary abs_indep_exps :
    forall Γ ins es envI bs env aenv,
      Forall restr_exp es ->
      Forall (wt_exp G Γ) es ->
      Forall (wl_exp G) es ->
      aenv <= APP_env abs_env env ->
      denot_exps G ins es envG (APP_env abs_env envI) (cons false bs) aenv
      <= lift (CONS abs) (denot_exps G ins es envG envI bs env).
  Proof.
    induction es as [|e es]; intros * Hr Hwt Hwl Le; inv Hr; inv Hwl; inv Hwt.
    - now rewrite 2 denot_exps_nil, map_eq_cons.
    - rewrite 2 denot_exps_eq.
      match goal with
        |-_ <= _ (_ (_ ?a) ?b) => setoid_rewrite (lift_app (CONS abs) _ a _ b)
        end.
      apply fcont_le_compat2; eauto 2 using abs_indep_exp.
  Qed.

  Lemma abs_indep_block :
    forall Γ ins blk envI bs env aenv acc aacc,
      restr_block blk ->
      wt_block G Γ blk ->
      wl_block G blk ->
      aenv <= APP_env abs_env env ->
      aacc <= APP_env abs_env acc ->
      denot_block G ins blk envG (APP_env abs_env envI) (cons false bs) aenv aacc
      <= APP_env abs_env (denot_block G ins blk envG envI bs env acc).
  Proof.
    intros * Hr Hwt Hwl Lee Lea.
    rewrite 2 denot_block_eq; cases; inv Hr.
    inv Hwl; take (wl_equation _ _) and inv it.
    inv Hwt; take (wt_equation _ _ _) and inv it.
    rewrite annots_numstreams in *.
    rewrite <- env_of_np_ext_abs; eauto 3 using abs_indep_exps.
  Qed.

  Lemma abs_le_node :
    forall n envI env aenv,
      restr_node n ->
      wt_node G n ->
      aenv <= APP_env abs_env env ->
      denot_node G n envG (APP_env abs_env envI) aenv
      <= APP_env abs_env (denot_node G n envG envI env).
  Proof.
    intros n envI env aenv Hr Hwt Hale.
    rewrite 2 denot_node_eq.
    rewrite 2 denot_top_block_eq.
    apply wt_node_wl_node in Hwt as Hwl.
    inversion_clear Hwl as [? HH]; revert HH.
    inversion_clear Hwt as [????? HH]; revert HH.
    inversion_clear Hr as [?? Hfr].
    intro Hwt; inv Hwt; take (wt_scope _ _ _ _) and inv it.
    intro Hwl; inv Hwl; take (wl_scope _ _ _) and inv it.
    rewrite 2 denot_blocks_eq.
    induction blks as [|b blks]; simpl (fold_right _ _ _).
    - intro x.
      unfold abs_env, abss at 1 2.
      now rewrite APP_env_eq, DS_const_eq, APP_simpl, app_cons.
    - do 3 take (Forall _ (_::_)) and inv it.
      rewrite bss_app_abs.
      eapply abs_indep_block; eauto 2.
  Qed.

End Abs_indep_node.


Theorem abs_indep_global :
  forall (G : global),
    restr_global G ->
    wt_global G ->
    forall f envI,
      denot_global G f (APP_env abs_env envI)
      <= APP_env abs_env (denot_global G f envI).
Proof.
  intros * Hr Hwt f envI.
  apply wt_global_wl_global in Hwt as Hwl.
  apply wl_global_Ordered_nodes in Hwl as Hord.
  destruct (find_node f G) eqn:Hfind.
  2:{ (* si find_node = None, c'est gagné *)
    unfold denot_global.
    rewrite <- PROJ_simpl, 2 FIXP_eq, PROJ_simpl,
      2 denot_global_eq, Hfind.
    apply Dbot. }
  (* TODO: ce schéma (set envG, HenvG, etc. semble récurrent, en faire une tactique ? *)
  remember (denot_global G) as envG eqn:HG.
  assert (forall f nd envI,
             find_node f G = Some nd ->
             envG f envI == FIXP _ (denot_node G nd envG envI)) as HenvG.
  { intros * Hf; subst.
    unfold denot_global.
    now rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl, denot_global_eq, Hf at 1. }
  clear HG. (* maintenant HenvG contient tout ce qu'on doit savoir sur envG *)
  revert Hfind.
  revert f envI n.
  destruct G as [tys exts nds].
  induction nds as [|a nds]; intros.
  { inv Hfind. }
  destruct (ident_eq_dec (n_name a) f); subst.
  - (* cas qui nous intéresse *)
    rewrite 2 HenvG; auto using find_node_now.
    rewrite <- denot_node_cons; eauto 3 using find_node_not_Is_node_in, find_node_now.
    rewrite FIXP_fixp.
    apply fixp_ind; auto.
    + (* admissibilité, pas trop dur : *)
      intros f Hf; exact (lub_le Hf).
    + (* itération *)
      intros aenv Hle.
      rewrite FIXP_eq.
      inv Hr.
      apply wt_global_uncons in Hwt as Wt.
      apply wt_global_cons in Hwt.
      inversion_clear Hwl as [|?? [Wl]]; simpl in Wl.
      apply abs_le_node; auto.
      (* reste l'hypothèse de récurrence sur les nœuds *)
      clear dependent envI.
      intros f2 n2 envI2 Hfind2.
      eapply IHnds; auto; [ now eauto using Ordered_nodes_cons | | eassumption ].
      (* et que HenvG tient toujours *)
      intros f' ndf' envI' Hfind'.
      rewrite HenvG, <- denot_node_cons;
        eauto using find_node_uncons, find_node_later_not_Is_node_in.
  - rewrite find_node_other in Hfind; auto.
    eapply IHnds; auto.
    + inv Hr; auto.
    + apply wt_global_cons in Hwt; auto.
    + inv Hwl; auto.
    + inv Hord; auto.
    + intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := a) in Hfind' as ?; auto.
      rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
    + apply Hfind.
Qed.

End ABS_INDEP.

Module AbsIndepFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Senv  : STATICENV     Ids Op OpAux Cks)
       (Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ   : LTYPING Ids Op OpAux Cks Senv Syn)
       (Lord  : LORDERED     Ids Op OpAux Cks Senv Syn)
       (Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord)
<: ABS_INDEP Ids Op OpAux Cks Senv Syn Typ Lord Den.
  Include ABS_INDEP Ids Op OpAux Cks Senv Syn Typ Lord Den.
End AbsIndepFun.
