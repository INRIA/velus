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


(** ** Propriété de préservation des longueurs *)

(* TODO: expliquer les différentes formulations  *)

Module Type LP
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Typ   : LTYPING       Ids Op OpAux Cks Senv Syn)
       (* TODO: tenter fixp_ind global? *)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Import Den   : LDENOT        Ids Op OpAux Cks Senv Syn Lord).


(** ** On montre que chaque opérateur du langage a cette propriété *)

(* Lemma abs_indep_fby : *)
(*   forall A (xs ys : DS (sampl A)), *)
(*     fby (cons abs xs) (cons abs ys) == cons abs (fby xs ys). *)
(* Proof. *)
(*   intros. *)
(*   now rewrite fby_eq, fbyA_eq. *)
(* Qed. *)

(* Corollary abs_indep_lift_fby : *)
(*   forall A n (xs ys : @nprod (DS (sampl A)) n), *)
(*     lift2 fby (lift (CONS abs) xs) (lift (CONS abs) ys) *)
(*     == lift (CONS abs) (lift2 fby xs ys). *)
(* Proof. *)
(*   induction n as [|[]]; intros. *)
(*   - apply abs_indep_fby. *)
(*   - apply abs_indep_fby. *)
(*   - apply Dprod_eq_intro. *)
(*     + simpl; apply abs_indep_fby. *)
(*     + apply IHn. *)
(* Qed. *)

(* Lemma abs_indep_swhenv : *)
(*   forall b xs cs, *)
(*     swhenv b (cons abs xs) (cons abs cs) == cons abs (swhenv b xs cs). *)
(* Proof. *)
(*   intros. *)
(*   unfold swhenv. *)
(*   now rewrite swhen_eq. *)
(* Qed. *)

(* Corollary abs_indep_lift_swhenv : *)
(*   forall b n (np : nprod n) cs, *)
(*     llift (swhenv b) (lift (CONS abs) np) (cons abs cs) *)
(*     == lift (CONS abs) (llift (swhenv b) np cs). *)
(* Proof. *)
(*   induction n as [|[]]; intros. *)
(*   - apply abs_indep_swhenv. *)
(*   - apply abs_indep_swhenv. *)
(*   - apply Dprod_eq_intro. *)
(*     + destruct np as (t1,t2). *)
(*       setoid_rewrite (llift_simpl _ (swhenv b) _ cs t1 t2). *)
(*       now setoid_rewrite <- abs_indep_swhenv. *)
(*     + apply IHn. *)
(* Qed. *)

(* Lemma abs_indep_smergev : *)
(*   forall l xs np, *)
(*     smergev l (cons abs xs) (lift (CONS abs) np) == cons abs (smergev l xs np). *)
(* Proof. *)
(*   intros. *)
(*   unfold smergev. *)
(*   rewrite 2 smerge_eq. *)
(*   induction l as [|i l]. *)
(*   - now rewrite 2 Foldi_nil, map_eq_cons. *)
(*   - now rewrite 2 Foldi_cons, lift_tl, lift_hd, IHl, CONS_simpl, zip3_cons. *)
(* Qed. *)

(* Corollary abs_indep_lift_smergev : *)
(*   forall l xs n (np : @nprod (nprod n) _), *)
(*     lift_nprod (smergev l (cons abs xs)) (lift (lift (CONS abs)) np) *)
(*     == lift_nprod (CONS abs @_ smergev l xs) np. *)
(* Proof. *)
(*   induction n; intro. *)
(*   - apply abs_indep_smergev. *)
(*   - rewrite 2 lift_nprod_simpl. *)
(*     apply nprod_cons_Oeq_compat. *)
(*     + setoid_rewrite <- abs_indep_smergev. *)
(*       rewrite 2 lift_lift. *)
(*       apply fcont_stable, lift_ext. *)
(*       destruct n; auto. *)
(*     + rewrite <- IHn. *)
(*       rewrite 2 lift_lift. *)
(*       apply fcont_stable, lift_ext. *)
(*       destruct n; auto. *)
(* Qed. *)

(* Lemma abs_indep_scasev : *)
(*   forall l xs np, *)
(*     scasev l (cons abs xs) (lift (CONS abs) np) == cons abs (scasev l xs np). *)
(* Proof. *)
(*   intros. *)
(*   unfold scasev. *)
(*   rewrite 2 scase_eq. *)
(*   induction l as [|i l]. *)
(*   - now rewrite 2 Foldi_nil, map_eq_cons. *)
(*   - now rewrite 2 Foldi_cons, lift_tl, lift_hd, IHl, CONS_simpl, zip3_cons. *)
(* Qed. *)

(* Corollary abs_indep_lift_scasev : *)
(*   forall l xs n (np : @nprod (nprod n) _), *)
(*     lift_nprod (scasev l (cons abs xs)) (lift (lift (CONS abs)) np) *)
(*     == lift_nprod (CONS abs @_ scasev l xs) np. *)
(* Proof. *)
(*   induction n; intro. *)
(*   - apply abs_indep_scasev. *)
(*   - rewrite 2 lift_nprod_simpl. *)
(*     apply nprod_cons_Oeq_compat. *)
(*     + setoid_rewrite <- abs_indep_scasev. *)
(*       rewrite 2 lift_lift. *)
(*       apply fcont_stable, lift_ext. *)
(*       destruct n; auto. *)
(*     + rewrite <- IHn. *)
(*       rewrite 2 lift_lift. *)
(*       apply fcont_stable, lift_ext. *)
(*       destruct n; auto. *)
(* Qed. *)

(* Lemma abs_indep_scase_defv : *)
(*   forall l xs ds np, *)
(*     scase_defv l (cons abs xs) (nprod_cons (cons abs ds) (lift (CONS abs) np)) *)
(*     == cons abs (scase_defv l xs (nprod_cons ds np)). *)
(* Proof. *)
(*   intros. *)
(*   unfold scase_defv. *)
(*   rewrite 2 scase_def_eq, 2 scase_def__eq. *)
(*   induction l as [|i l]. *)
(*   - now rewrite 2 Foldi_nil, zip_cons. *)
(*   - now rewrite 2 Foldi_cons, lift_tl, lift_hd, IHl, CONS_simpl, zip3_cons. *)
(* Qed. *)

(* Corollary abs_indep_lift_scase_defv : *)
(*   forall l xs n ds (np : @nprod (nprod n) _), *)
(*     lift_nprod (scase_defv l (cons abs xs)) (nprod_cons (lift (CONS abs) ds) (lift (lift (CONS abs)) np)) *)
(*     == lift_nprod (CONS abs @_ scase_defv l xs) (nprod_cons ds np). *)
(* Proof. *)
(*   induction n; intros. *)
(*   - apply abs_indep_scase_defv. *)
(*   - rewrite 2 lift_nprod_simpl, 4 lift_cons. *)
(*     rewrite <- IHn, lift_tl, lift_hd, fcont_comp_simpl. *)
(*     apply nprod_cons_Oeq_compat. *)
(*     + rewrite <- (abs_indep_scase_defv _ xs (nprod_hd ds) (lift nprod_hd np)), 2 lift_lift. *)
(*       apply fcont_stable, nprod_cons_Oeq_compat; auto. *)
(*       apply lift_ext; destruct n; auto. *)
(*     + apply fcont_stable, nprod_cons_Oeq_compat; auto. *)
(*       rewrite 2 lift_lift. *)
(*       apply lift_ext; destruct n; auto. *)
(* Qed. *)

(* Lemma abs_indep_sreset_aux : *)
(*   forall f bs X Y, *)
(*     sreset_aux f (cons false bs) (APP_env abs_env X) (APP_env abs_env Y) *)
(*     == APP_env abs_env (sreset_aux f bs X Y). *)
(* Proof. *)
(*   intros. *)
(*   rewrite sreset_aux_eq. *)
(*   rewrite 2 rem_app_env; try apply all_cons_abs_env. *)
(*   apply Oprodi_eq_intro; intro x. *)
(*   unfold abs_env, abss. *)
(*   now rewrite DS_const_eq, 3 APP_env_eq, 3 APP_simpl, 3 app_cons. *)
(* Qed. *)

(* Lemma bss_app_abs : *)
(*   forall l env, *)
(*     bss l (APP_env abs_env env) == cons false (bss l env). *)
(* Proof. *)
(*   induction l as [| x l]; intro env. *)
(*   - simpl. *)
(*     autorewrite with cpodb. *)
(*     now rewrite <- DS_const_eq. *)
(*   - unfold abs_env, abss. *)
(*     now rewrite 2 bss_cons, IHl, APP_env_eq, DS_const_eq, *)
(*       APP_simpl, app_cons, AC_cons, zip_cons. *)
(* Qed. *)

(* Lemma sbools_of_abs : *)
(*   forall n (np : nprod n), *)
(*     sbools_of (lift (CONS abs) np) == cons false (sbools_of np). *)
(* Proof. *)
(*   induction n; intros. *)
(*   - cbn; now rewrite <- DS_const_eq. *)
(*   - unfold sbools_of. *)
(*     autorewrite with cpodb. *)
(*     rewrite 2 Fold_eq. *)
(*     rewrite 3 lift_tl, 3 lift_hd, (IHn (nprod_tl np)). *)
(*     unfold sbool_of at 1. *)
(*     rewrite MAP_map, CONS_simpl, map_eq_cons, zip_cons; auto. *)
(* Qed. *)

  (*XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXx TODO: move ? *)
  Lemma take_is_cons :
    forall A (s : DS A) n, is_cons (take n s) -> is_cons s.
  Proof.
    intros * Hc.
    rewrite take_eq in Hc.
    destruct n.
    - contradict Hc; apply not_is_consBot.
    - now apply app_is_cons in Hc.
  Qed.
  Lemma take_zip :
    forall A B C (op:A->B->C),
    forall n xs ys,
      take n (ZIP op xs ys) == ZIP op (take n xs) (take n ys).
  Proof.
    induction n; intros.
    - now rewrite zip_bot1.
    - rewrite 3 (take_eq (S n)).
      now rewrite <- zip_app, <- 2 APP_simpl, rem_zip, IHn.
  Qed.
  Lemma take_zip3 :
    forall A B C D (op:A->B->C->D),
    forall n xs ys zs,
      take n (ZIP3 op xs ys zs) == ZIP3 op (take n xs) (take n ys) (take n zs).
  Proof.
    intros.
    now rewrite 2 zip3_eq, 2 take_zip.
  Qed.

  Lemma zip_take_const :
    forall A B C (op:A->B->C),
    forall n xs c,
      ZIP op (take n xs) (DS_const c) == ZIP op (take n xs) (take n (DS_const c)).
  Proof.
    induction n; intros.
    - now rewrite 2 zip_bot1.
    - rewrite 2 (take_eq (S n)).
      setoid_rewrite DS_const_eq at 3.
      rewrite DS_const_eq, rem_cons at 1.
      rewrite <- (app_cons _ (DS_const c)), <- DS_const_eq.
      now rewrite <- 2 zip_app, IHn.
  Qed.
  Lemma take_cons :
    forall A n (x : A) xs,
      take (S n) (cons x xs) = cons x (take n xs).
  Proof.
    intros.
    now rewrite take_eq, app_cons, rem_cons.
  Qed.
  (* TODO: remplacer l'autre cons_decomp *)
  Lemma cons_decomp :
    forall D x (s : DS D) t,
      s == cons x t ->
      exists t', decomp x t' s /\ t == t'.
  Proof.
    intros * Hs.
    pose proof (is_cons_eq_compat (symmetry Hs) (isConCon _ _)) as Hc.
    destruct (uncons Hc) as (?&?& Hd).
    apply decomp_eqCon in Hd as Heq.
    rewrite Heq in Hs.
    apply Con_eq_simpl in Hs as []; subst.
    eauto.
  Qed.

  Lemma take_map :
    forall A B (f : A ->B),
    forall n xs,
      take n (map f xs) == map f (take n xs).
  Proof.
    induction n; intros.
    - now rewrite map_bot.
    - now rewrite 2 (take_eq (S n)), rem_map, IHn, app_map.
  Qed.

  Lemma lp_bss :
    forall l n (env : DS_prod SI),
      l <> [] ->
      bss l (take_env n env) == take n (bss l env).
  Proof.
    induction l as [|i [|j ]]; intros * Hl.
    - contradiction.
    - rewrite 2 bss_cons; simpl (bss [] _).
      rewrite take_zip, take_env_eq, 2 CTE_eq.
      unfold AC at 1.
      now rewrite MAP_map, <- take_map, zip_take_const.
    - rewrite 2 (bss_cons i), take_zip, <- IHl, take_env_eq; [|congruence].
      unfold AC.
      now rewrite 2 MAP_map, take_map.
  Qed.
  Lemma take_env_of_np_ext :
    forall l n m (np : nprod m) env,
      m = length l ->
      take_env n (env_of_np_ext l np env) == env_of_np_ext l (lift (take n) np) (take_env n env).
  Proof.
    intros; subst.
    apply Oprodi_eq_intro; intro i.
    rewrite take_env_eq, 2 env_of_np_ext_eq, take_env_eq.
    cases_eqn HH; apply mem_nth_Some in HH; auto.
    erewrite nth_lift; auto.
  Qed.
  Lemma take_sbinop :
    forall A B D (op : A -> B-> option D),
    forall n xs ys,
      take n (sbinop op xs ys) == sbinop op (take n xs) (take n ys).
  Proof.
    intros.
    unfold sbinop.
    autorewrite with cpodb; simpl.
    now rewrite take_map, take_zip.
  Qed.

  (** pour le fby, c'est compliqué *)

  Lemma take_fby1_le1 :
    forall A n oa (xs ys : DS (sampl A)),
      fby1 oa (take n xs) (take n ys) <= take n (fby1 oa xs ys).
  Proof.
    induction n; intros.
    { now rewrite fby1_bot1. }
    remember_ds (fby1 oa (take _ _) (take _ _)) as U.
    remember_ds (take _ (fby1 oa xs ys)) as V.
    (* TODO: le cofix simple, en faire une méthode générale pour trouver un cons ? *)
    revert dependent U; cofix Cof; intros; destruct U;
      [ rewrite <- eqEps in HU; eapply DSleEps, Cof; eauto
      | clear Cof].
    edestruct (@is_cons_elim _ xs) as (x & X & Hx).
    { eapply take_is_cons, fby1_cons; now rewrite <- HU. }
    rewrite Hx, take_cons, fby1_eq in HU.
    rewrite Hx, fby1_eq in HV.
    cases; rewrite take_cons in HV; apply Con_eq_simpl in HU as [? HU]; subst.
    3-6: now rewrite HV, HU, take_map.
    (* plus que 2 cas identique *)
    all: apply cons_decomp in HV as (V' & Hd & HV);
      econstructor; eauto; clear Hd Hx V xs.
    (* on cherche is_cons y  *)
    all: revert dependent U; cofix Cof; intros; destruct U;
      [rewrite <- eqEps in HU; eapply DSleEps, Cof; eauto
      |clear Cof].

    all: edestruct (@is_cons_elim _ ys) as (y & Y & Hy);
      [ eapply take_is_cons, fby1AP_cons; now rewrite <- HU |].
    all: rewrite Hy, take_cons, fby1AP_eq in HU.
    all: rewrite Hy, fby1AP_eq in HV.
    all: change (DSle _ _) with (cons s U <= V').
    all: cases; rewrite HU, <- HV, <- ?take_map; auto.
  Qed.

  Lemma take_fby1_le2 :
    forall A n oa (xs ys : DS (sampl A)),
      take n (fby1 oa xs ys) <= fby1 oa (take n xs) (take n ys).
  Proof.
    induction n; intros.
    { now rewrite fby1_bot1. }
    remember_ds (fby1 oa (take _ _) (take _ _)) as V.
    remember_ds (take _ (fby1 oa xs ys)) as U.
    revert dependent U; cofix Cof; intros; destruct U;
      [ rewrite <- eqEps in HU; eapply DSleEps, Cof; eauto
      | clear Cof].
    edestruct (@is_cons_elim _ xs) as (x & X & Hx).
    { eapply fby1_cons, take_is_cons; now rewrite <- HU. }
    rewrite Hx, take_cons, fby1_eq in HV.
    rewrite Hx, fby1_eq in HU.
    cases; rewrite take_cons in HU; apply Con_eq_simpl in HU as [? HU]; subst.
    3-6: now rewrite HV, HU, take_map.
    (* plus que 2 cas identique *)
    all: apply cons_decomp in HV as (V' & Hd & HV);
      econstructor; eauto; clear Hd Hx V xs.
    (* on cherche is_cons y  *)
    all: revert dependent U; cofix Cof; intros; destruct U;
      [rewrite <- eqEps in HU; eapply DSleEps, Cof; eauto
      |clear Cof].
    all: edestruct (@is_cons_elim _ ys) as (y & Y & Hy);
      [ eapply fby1AP_cons, take_is_cons; now rewrite <- HU |].
    all: rewrite Hy, take_cons, fby1AP_eq in HV.
    all: rewrite Hy, fby1AP_eq in HU.
    all: change (DSle _ _) with (cons s U <= V').
    all: cases; rewrite HU, <- HV, <- ?take_map; auto.
  Qed.

  Lemma take_fby1 :
    forall A n oa (xs ys : DS (sampl A)),
      take n (fby1 oa xs ys) == fby1 oa (take n xs) (take n ys).
  Proof.
    split.
    - apply take_fby1_le2.
    - apply take_fby1_le1.
  Qed.

  Lemma take_fby_le1 :
    forall A n (xs ys : DS (sampl A)),
      fby (take n xs) (take n ys) <= take n (fby xs ys).
  Proof.
    induction n; intros.
    { now rewrite fby_bot1. }
    remember_ds (fby (take _ _) (take _ _)) as U.
    remember_ds (take _ (fby xs ys)) as V.
    (* TODO: le cofix simple, en faire une méthode générale pour trouver un cons ? *)
    revert dependent U; cofix Cof; intros; destruct U;
      [ rewrite <- eqEps in HU; eapply DSleEps, Cof; eauto
      | clear Cof].
    edestruct (@is_cons_elim _ xs) as (x & X & Hx).
    { eapply take_is_cons, fby_cons; now rewrite <- HU. }
    rewrite Hx, take_cons, fby_eq in HU.
    rewrite Hx, fby_eq in HV.
    cases; rewrite take_cons in HV; apply Con_eq_simpl in HU as [? HU]; subst.
    3: now rewrite HV, HU, take_map.
    (* plus que 2 cas presque identiques *)
    all: apply cons_decomp in HV as (V' & Hd & HV);
      econstructor; eauto; clear Hd Hx V xs.
    (* on cherche is_cons y  *)
    all: revert dependent U; cofix Cof; intros; destruct U;
      [rewrite <- eqEps in HU; eapply DSleEps, Cof; eauto
      |clear Cof].
    1: edestruct (@is_cons_elim _ ys) as (y & Y & Hy);
    [ eapply take_is_cons, fbyA_cons; now rewrite <- HU |].
    2: edestruct (@is_cons_elim _ ys) as (y & Y & Hy);
    [ eapply take_is_cons, fby1AP_cons; now rewrite <- HU |].
    all: rewrite Hy, take_cons, ?fby1AP_eq, ?fbyA_eq in HU.
    all: rewrite Hy, ?fby1AP_eq, ?fbyA_eq in HV.
    all: change (DSle _ _) with (cons s U <= V').
    all: cases; rewrite HU, <- HV, ?take_fby1, <- ?take_map; auto.
  Qed.

  Lemma take_fby_le2 :
    forall A n (xs ys : DS (sampl A)),
      take n (fby xs ys) <= fby (take n xs) (take n ys).
  Proof.
    induction n; intros.
    { now rewrite fby_bot1. }
    remember_ds (fby (take _ _) (take _ _)) as V.
    remember_ds (take _ (fby xs ys)) as U.
    revert dependent U; cofix Cof; intros; destruct U;
      [ rewrite <- eqEps in HU; eapply DSleEps, Cof; eauto
      | clear Cof].
    edestruct (@is_cons_elim _ xs) as (x & X & Hx).
    { eapply fby_cons, take_is_cons; now rewrite <- HU. }
    rewrite Hx, take_cons, fby_eq in HV.
    rewrite Hx, fby_eq in HU.
    cases; rewrite take_cons in HU; apply Con_eq_simpl in HU as [? HU]; subst.
    3: now rewrite HV, HU, take_map.
    (* plus que 2 cas presque identiques *)
    all: apply cons_decomp in HV as (V' & Hd & HV);
      econstructor; eauto; clear Hd Hx V xs.
    (* on cherche is_cons y  *)
    all: revert dependent U; cofix Cof; intros; destruct U;
      [rewrite <- eqEps in HU; eapply DSleEps, Cof; eauto
      |clear Cof].
    1: edestruct (@is_cons_elim _ ys) as (y & Y & Hy);
    [ eapply fbyA_cons, take_is_cons; now rewrite <- HU |].
    2: edestruct (@is_cons_elim _ ys) as (y & Y & Hy);
    [ eapply fby1AP_cons, take_is_cons; now rewrite <- HU |].
    all: rewrite Hy, take_cons, ?fby1AP_eq, ?fbyA_eq in HV.
    all: rewrite Hy, ?fby1AP_eq, ?fbyA_eq in HU.
    all: change (DSle _ _) with (cons s U <= V').
    all: cases; rewrite HU, <- HV, ?take_fby1, <- ?take_map; auto.
  Qed.

  Lemma take_fby :
    forall A n (xs ys : DS (sampl A)),
      take n (fby xs ys) == fby (take n xs) (take n ys).
  Proof.
    split.
    - apply take_fby_le2.
    - apply take_fby_le1.
  Qed.

  Corollary take_lift_fby :
    forall A n m (xs ys : @nprod (DS (sampl A)) m),
      lift (take n) (lift2 fby xs ys)
      ==  lift2 fby (lift (take n) xs) (lift (take n) ys).
  Proof.
    induction m as [|[]]; intros.
    - apply take_fby.
    - apply take_fby.
    - apply Dprod_eq_intro.
      + simpl; apply take_fby.
      + apply IHm.
  Qed.


  Lemma take_swhenv :
    forall b n xs cs,
      take n (swhenv b xs cs) == swhenv b (take n xs) (take n cs).
  Proof.
    intros.
    unfold swhenv, swhen.
    now rewrite take_zip.
  Qed.

  Corollary take_lift_swhenv :
    forall b n m (np : nprod m) cs,
      lift (take n) (llift (swhenv b) np cs)
      == llift (swhenv b) (lift (take n) np) (take n cs).
  Proof.
    induction m as [|[]]; intros.
    - apply take_swhenv.
    - apply take_swhenv.
    - apply Dprod_eq_intro.
      + destruct np as (t1,t2).
        setoid_rewrite (llift_simpl _ (swhenv b) _ cs t1 t2).
        apply take_swhenv.
      + apply IHm.
  Qed.


  Lemma take_smergev :
    forall l xs np n,
      take n (smergev l xs np) == smergev l (take n xs) (lift (take n) np).
  Proof.
    intros.
    unfold smergev.
    rewrite 2 smerge_eq.
    induction l as [|i l].
    - now rewrite 2 Foldi_nil, take_map.
    - now rewrite 2 Foldi_cons, lift_tl, lift_hd, <- IHl, take_zip3.
  Qed.

  Corollary take_lift_smergev :
    forall l xs m (np : @nprod (nprod m) _) n,
      lift_nprod (take n @_ smergev l xs) np
      == lift_nprod (smergev l (take n xs)) (lift (lift (take n)) np).
  Proof.
    induction m; intros.
    - apply take_smergev.
    - rewrite 2 lift_nprod_simpl.
      apply nprod_cons_Oeq_compat.
      + setoid_rewrite take_smergev.
        rewrite 2 lift_lift.
        apply fcont_stable, lift_ext.
        destruct m; auto.
      + rewrite IHm.
        rewrite 2 lift_lift.
        apply fcont_stable, lift_ext.
        destruct m; auto.
  Qed.

  Lemma take_scasev :
    forall l xs np n,
      take n (scasev l xs np)
      == scasev l (take n xs) (lift (take n) np).
  Proof.
    intros.
    unfold scasev.
    rewrite 2 scase_eq.
    induction l as [|i l].
    - now rewrite 2 Foldi_nil, take_map.
    - now rewrite 2 Foldi_cons, lift_tl, lift_hd, <- IHl, take_zip3.
  Qed.

  Corollary take_lift_scasev :
    forall l xs m (np : @nprod (nprod m) _) n,
      lift_nprod (take n @_ scasev l xs) np
      == lift_nprod (scasev l (take n xs)) (lift (lift (take n)) np).
  Proof.
  induction m; intros.
  - apply take_scasev.
  - rewrite 2 lift_nprod_simpl.
    apply nprod_cons_Oeq_compat.
    + setoid_rewrite take_scasev.
      rewrite 2 lift_lift.
      apply fcont_stable, lift_ext.
      destruct m; auto.
    + rewrite IHm.
      rewrite 2 lift_lift.
      apply fcont_stable, lift_ext.
      destruct m; auto.
  Qed.

  Lemma take_scase_defv :
    forall l xs ds np n,
      take n (scase_defv l xs (nprod_cons ds np))
      == scase_defv l (take n xs) (nprod_cons (take n ds) (lift (take n) np)).
  Proof.
    intros.
    unfold scase_defv.
    rewrite 2 scase_def_eq, 2 scase_def__eq.
    induction l as [|i l].
    - now rewrite 2 Foldi_nil, take_zip.
    - now rewrite 2 Foldi_cons, lift_tl, lift_hd, <- IHl, take_zip3.
  Qed.

  Corollary take_lift_scase_defv :
    forall l xs m (np : @nprod (nprod m) _) ds n,
      lift (take n) (lift_nprod (scase_defv l xs) (nprod_cons ds np))
      == lift_nprod (scase_defv l (take n xs)) (nprod_cons (lift (take n) ds) (lift (lift (take n)) np)).
  Proof.
    induction m; intros.
    - simpl. apply take_scase_defv.
    - rewrite 2 lift_nprod_simpl, 4 lift_cons, IHm.
      apply nprod_cons_Oeq_compat.
      + rewrite (take_scase_defv _ xs (nprod_hd ds) (lift nprod_hd np)), 2 lift_lift, lift_hd.
        apply fcont_stable, nprod_cons_Oeq_compat; auto.
        apply lift_ext; destruct m; auto.
      + rewrite <- lift_tl, lift_cons.
        apply fcont_stable, nprod_cons_Oeq_compat; auto.
        rewrite 2 lift_lift.
        apply lift_ext; destruct m; auto.
  Qed.


  (* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXxxxx *)

(** ** Raisonnement sur les nœuds *)

Section LP_node.

  Variables
    (G : global)
    (envG : Dprodi FI).

  Hypothesis Hnode :
    forall f n envI,
      (* FIXME: find_node est totalement inutile, sauf pour faire
       passer l'induction sur OrderedNodes. À terme ça devrait sauter
       avec une induction sur le point fixe global *)
      find_node f G <> None ->
      envG f (take_env n envI) <= take_env n (envG f envI).

  Set Nested Proofs Allowed.
      (* FIXME: partagé avec Abs.v *)
      Lemma np_of_env_cons :
        forall i l env,
          np_of_env (i :: l) env
          = nprod_cons (env i) (np_of_env l env).
      Proof.
        trivial.
      Qed.
      Lemma take_np_of_env :
        forall l env n,
          0 < length l ->
          lift (take n) (np_of_env l env) == np_of_env l (take_env n env).
      Proof.
        induction l as [|i [|j]]; intros * Hl; simpl in Hl.
        - inversion Hl.
        - cbn; now rewrite take_env_eq.
        - rewrite 2 (np_of_env_cons i (j :: l)), <- IHl; [| simpl; lia].
          setoid_rewrite (lift_cons (take n) _ (env i) (np_of_env (j :: l) env)).
          now rewrite take_env_eq.
      Qed.
      Lemma take_bot : forall A n, @take A n 0 == 0.
      Proof.
        destruct n; rewrite take_eq; auto.
      Qed.

      Lemma take_env_of_np :
        forall l (np : nprod (length l)) n,
          env_of_np l (lift (take n) np) == take_env n (env_of_np l np).
      Proof.
        intros.
        apply Oprodi_eq_intro; intro x.
        rewrite take_env_eq, 2 env_of_np_eq.
        cases_eqn Hmem.
        - apply mem_nth_Some in Hmem; auto.
          erewrite nth_lift; eauto.
        - now rewrite take_bot.
      Qed.
        (* TODO: comment faire ça sans lemme ? *)
        Lemma Dprodi_le_elim : forall (I:Type)(D:I->cpo) (p q : Dprodi D), p<=q -> forall i, p i <= q i.
          intros ???? H; apply H.
        Qed.

        Lemma take_env_le : forall n (env:DS_prod SI), take_env n env <= env.
        Proof.
          induction n; simpl (take_env _ _); intros.
          - apply Dbot.
          - apply Ole_trans with (APP_env env (REM_env env)); auto.
            now rewrite app_rem_env.
        Qed.
        (* TODO: ça doit remplacer take_env_eq *)
        Lemma take_env_proj :
          forall n (X  : DS_prod SI) x, take_env n X x = take n (X x).
        Proof.
          induction n; simpl; intros; auto.
          now rewrite APP_env_eq, IHn, REM_env_eq.
        Qed.

          Lemma take_env_eq :
            forall n (env : DS_prod SI),
              take_env n env = match n with
                               | O => 0
                               | S n => APP_env env (take_env n (REM_env env))
                               end.
          Proof.
            destruct n; reflexivity.
          Qed.

          Lemma rem_app_env_le :
            forall (X Y: DS_prod SI), REM_env (APP_env X Y) <= Y.
          Proof.
            intros * i.
            rewrite REM_env_eq, APP_env_eq, APP_simpl.
            apply rem_app_le.
          Qed.

          Lemma rem_take_env :
            forall n (env : DS_prod SI),
              REM_env (take_env (S n) env) <= take_env n (REM_env env).
          Proof.
            intros.
            now rewrite take_env_eq, rem_app_env_le.
          Qed.

          Lemma sreset_aux_bot : forall f (X Y:DS_prod SI), sreset_aux f 0 X Y == 0.
          Proof.
            intros.
            unfold sreset_aux.
            apply Oprodi_eq_intro; intro i.
            rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl.
            now apply DScase_bot_eq.
          Qed.


        Lemma take_sreset_aux :
          forall f n rs (X Y : DS_prod SI),
            find_node f G <> None ->
          sreset_aux (envG f) (take n rs) (take_env n X) (take_env n Y)
          <= take_env n (sreset_aux (envG f) rs X Y).
        Proof.
          induction n; intros * Hfind.
        { now rewrite take_eq, (sreset_aux_bot (envG f)). }
        intro i.
        remember_ds (sreset_aux (envG f) (take (S n) rs) (take_env (S n) X) (take_env (S n) Y) i) as U.
        remember_ds (take_env (S n) (sreset_aux (envG f) rs X Y) i) as V.
        revert_all; cofix Cof; intros.
        (* TODO: unifier la tactique avec fby/fby1 *)
        destruct U.
        { constructor; rewrite <- eqEps in *; eapply Cof; eauto. }
        clear Cof.
        edestruct (@is_cons_elim _ rs) as (r & rs' & Hr).
        { eapply take_is_cons, is_cons_sreset_aux; now rewrite <- HU. }
        rewrite HU, HV; clear HU HV. clear U V s.
        apply Dprodi_le_elim.
        rewrite Hr, take_cons, 2 (sreset_aux_eq (envG f) r).
        destruct r; auto.
        - (* signal reçu *)
          rewrite 2 sreset_aux_eq.
          rewrite (take_env_eq (S n) (APP_env _ _)).
          rewrite app_app_env, app_rem_take_env.
          apply fcont_le_compat2; auto using take_env_le.
          eapply Ole_trans; [|apply IHn; intro; auto].
          apply (fcont_le_compat2); auto using rem_take_env.
          eapply Ole_trans; [| apply rem_take_env]; auto.
        - (* signal false *)
          rewrite (take_env_eq (S n) (APP_env _ _)).
          rewrite app_app_env, app_rem_take_env.
          apply (fcont_le_compat2); auto using take_env_le.
          eapply Ole_trans; [|apply IHn; intro; auto].
          apply (fcont_le_compat2); auto using rem_take_env.
      Qed.


  Lemma Fold_eq :
    forall A B (F : B -C-> A -C-> A) a n (np : @nprod B n),
      nprod_Fold F a np =
        match n return nprod n -> _ with
        | O => fun _ => a
        | S n => fun np => F (nprod_hd np) (nprod_Fold F a (nprod_tl np))
        end np.
  Proof.
    destruct n; reflexivity.
  Qed.

  Lemma take_sbools_of :
      forall m (mp : nprod m) n,
        0 < m ->
        take n (sbools_of mp) == sbools_of (lift (take n) mp).
    Proof.
      clear.
      intros * Hle.
      unfold sbools_of; autorewrite with cpodb.
      induction m as [|[|m]].
      - inv Hle.
      - rewrite 4 Fold_eq, take_zip, 2 lift_hd.
        rewrite <- zip_take_const.
        unfold sbool_of; rewrite 2 MAP_map, take_map.
        auto.
      - rewrite 2 Fold_eq with (n:=S (S m)), take_zip, 3 lift_hd, 3 lift_tl.
        rewrite IHm; auto with arith.
        unfold sbool_of; rewrite 2 MAP_map, take_map.
        auto.
    Qed.
      (* FIXME: prouvé dans Reset.v *)
      Lemma take_sreset_aux_false :
        forall n f R (X Y : DS_prod SI),
          take n R == take n (DS_const false) ->
          take_env n (sreset_aux f R X Y) == take_env n Y.
        clear.
      Admitted.
      Corollary sreset_aux_false :
        forall f R (X Y : DS_prod SI),
          R == DS_const false ->
          sreset_aux f R X Y == Y.
      Proof.
        intros * Hr.
        apply take_env_Oeq.
        intros.
        apply take_sreset_aux_false, fcont_stable, Hr.
      Qed.

        Lemma fcont_app_le_compat : forall (D1 D2:cpo) (f g : D1 -c> D2) (x y : D1),
            f <= g -> x <= y -> f x <= g y.
        Proof.
          intros.
          apply Ole_trans with (f y); auto.
        Qed.



  Lemma lp_var :
    forall ins x n envI env nenv,
      nenv <= take_env n env ->
      denot_var ins (take_env n envI) nenv x
      <= take n (denot_var ins envI env x).
  Proof.
    intros * Hle.
    specialize (Hle x).
    revert Hle; unfold denot_var.
    rewrite 2 take_env_proj; cases.
  Qed.

  (* utile pour les cas récursifs *)
  Lemma lift_IH :
    forall ins es envG envI bs env n nenv,
      Forall (fun e => denot_exp G ins e envG (take_env n envI) (take n bs) nenv
                    <= lift (take n) (denot_exp G ins e envG envI bs env)) es ->
      denot_exps G ins es envG (take_env n envI) (take n bs) nenv
      <= lift (take n) (denot_exps G ins es envG envI bs env).
  Proof.
    induction es; intros * Hf; inv Hf.
    - now rewrite 2 denot_exps_nil, <- take_map.
    - rewrite 2 denot_exps_eq.
      setoid_rewrite lift_app; auto.
  Qed.

  (* idem *)
  Lemma lift_IHs :
    forall ins (ess : list (enumtag * _)) m envG envI bs env n nenv,
      Forall (fun es =>
                Forall (fun e => denot_exp G ins e envG (take_env n envI) (take n bs) nenv
                    <= lift (take n) (denot_exp G ins e envG envI bs env)) (snd es)) ess ->
      denot_expss G ins ess m envG (take_env n envI) (take n bs) nenv
      <= lift (lift (take n)) (denot_expss G ins ess m envG envI bs env).
  Proof.
    intros * Hf.
    induction ess as [|(x,es)]; inv Hf.
    - rewrite 2 denot_expss_nil; simpl.
      now rewrite lift_nprod_const, take_map.
    - rewrite 2 denot_expss_eq.
      unfold eq_rect.
      cases; subst.
      + match goal with
          |-_ <= _ (_ (_ ?a) ?b) =>
            setoid_rewrite (lift_cons (lift (take n)) _ a b)
        end; auto using lift_IH.
      + simpl (length _).
        now rewrite 2 lift_nprod_const, take_map.
  Qed.

  Lemma lp_exp :
    forall Γ ins e n envI bs env nenv,
      restr_exp e ->
      wt_exp G Γ e ->
      wl_exp G e ->
      nenv <= take_env n env ->
      denot_exp G ins e envG (take_env n envI) (take n bs) nenv
      <= lift (take n) (denot_exp G ins e envG envI bs env).
  Proof.
    intros * Hr Hwt Hwl Hle.
    induction e using exp_ind2; inv Hr.
    - (* Econst *)
      rewrite 2 denot_exp_eq.
      unfold sconst.
      rewrite 2 MAP_map, <- take_map; auto.
    - (* Evar *)
      rewrite 2 denot_exp_eq.
      now apply lp_var.
    - (* Eunop *)
      inv Hwt. inv Hwl.
      rewrite 2 (denot_exp_eq _ _ (Eunop _ _ _)).
      revert IHe.
      gen_sub_exps.
      take (numstreams _ = _) and rewrite it.
      take (typeof _ = _) and rewrite it.
      cbv zeta; intros t1 t2 IHe.
      eapply Ole_trans with (sunop _ (take n t1)); auto.
      unfold sunop at 1.
      now rewrite MAP_map, <- take_map.
    - (* Ebinop *)
      inv Hwt. inv Hwl.
      rewrite 2 (denot_exp_eq _ _ (Ebinop _ _ _ _)).
      revert IHe1 IHe2.
      gen_sub_exps.
      do 2 (take (numstreams _ = _) and rewrite it; clear it).
      do 2 (take (typeof _ = _) and rewrite it; clear it).
      cbv zeta; intros t1 t2 t3 t4 IHe1 IHe2.
      setoid_rewrite take_sbinop; auto.
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
      rewrite take_lift_fby; auto.
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
      rewrite take_lift_swhenv; auto using lp_var.
    - (* Emerge *)
      inv Hwt. inv Hwl.
      rewrite 2 (denot_exp_eq _ _ (Emerge _ _ _)).
      pose proof (IH := lift_IHs ins es (length tys) envG envI bs env n nenv).
      eassert (Le: _ <= _); [apply IH; simpl_Forall; auto|clear IH].
      cbv zeta; revert Le.
      gen_sub_exps; intros t1 t2 Le.
      unfold eq_rect_r, eq_rect, eq_sym; cases.
      rewrite lift_lift_nprod, take_lift_smergev; auto using lp_var.
    - (* Ecase total *)
      inv Hwt. inv Hwl.
      rewrite 2 (denot_exp_eq _ _ (Ecase _ _ _ _)).
      pose proof (IH := lift_IHs ins es (length tys) envG envI bs env n nenv).
      eassert (Le: _ <= _); [apply IH; simpl_Forall; auto|clear IH].
      cbv zeta; revert IHe Le; gen_sub_exps.
      take (numstreams e = 1) and rewrite it.
      unfold eq_rect_r, eq_rect, eq_sym; cases.
      intros t1 t2 t3 t4 Le1 Le2.
      rewrite lift_lift_nprod, take_lift_scasev; auto.
    - (* Ecase défaut *)
      inv Hwt. inv Hwl.
      set (typesof des) as tys.
      apply Forall_impl_inside with (P := restr_exp) in H0; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H0; auto.
      apply Forall_impl_inside with (P := wl_exp _ ) in H0; auto.
      apply lift_IH in H0.
      pose proof (IH := lift_IHs ins es (length tys) envG envI bs env n nenv).
      eassert (Le: _ <= _); [apply IH; simpl_Forall; auto|clear H IH].
      rewrite 2 (denot_exp_eq _ _ (Ecase _ _ _ _)).
      cbv zeta; revert IHe H0 Le; gen_sub_exps.
      assert (Hl : list_sum (List.map numstreams des) = length tys)
        by (subst tys; now rewrite length_typesof_annots, annots_numstreams).
      take (numstreams e = 1) and rewrite it, Hl.
      simpl (numstreams _). (* dans les types... *)
      unfold eq_rect_r, eq_rect, eq_sym; cases; try congruence.
      intros t1 t2 t3 t4 t5 t6 Le1 Le2 Le3.
      rewrite take_lift_scase_defv; auto.
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
      assert (Hl : list_sum (List.map numstreams es) = length (idents (n_in n0)))
        by (now unfold idents; rewrite map_length, annots_numstreams in * ).
      simpl; take (length a = _) and rewrite it, Hl.
      unfold eq_rect; cases; try (rewrite map_length in *; tauto).
      intros t1 t2 t3 t4 Le1 Le2.
      rewrite 2 sreset_eq, take_np_of_env.
      2: rewrite map_length; apply n_outgt0.
      apply fcont_monotonic.
      (* clear - Le1 Le2 Hnode. *)
      destruct (list_sum (List.map numstreams er)).
      + (* s'il n'y a pas de signal reset *)
        rewrite take_sreset_aux_false, sreset_aux_false; auto.
        eapply Ole_trans, Hnode; [| intro; congruence].
        rewrite <- take_env_of_np; eauto.
      + (* sinon *)
        rewrite <- take_sreset_aux, <- take_env_of_np; [|intro; congruence].
        rewrite take_sbools_of; auto with arith.
        specialize (Hnode f n (env_of_np (idents (n_in n0)) t3)).
        rewrite <- take_env_of_np in Hnode.
        eapply Ole_trans, fcont_monotonic, Hnode; [|intro; congruence].
        apply fcont_app_le_compat; auto.
        apply (fcont_le_compat2 (sreset_aux _)); auto.
  Qed.

  Corollary lp_exps :
    forall Γ ins es n envI bs env nenv,
      Forall restr_exp es ->
      Forall (wt_exp G Γ) es ->
      Forall (wl_exp G) es ->
      nenv <= take_env n env ->
      denot_exps G ins es envG (take_env n envI) (take n bs) nenv
      <= lift (take n) (denot_exps G ins es envG envI bs env).
  Proof.
    induction es as [|e es]; intros * Hr Hwt Hwl Le; inv Hr; inv Hwl; inv Hwt.
    - now rewrite 2 denot_exps_nil, <- take_map.
    - rewrite 2 denot_exps_eq.
      match goal with
        |-_ <= _ (_ (_ ?a) ?b) => setoid_rewrite (lift_app (take n) _ a _ b)
      end.
      apply fcont_le_compat2; eauto 2 using lp_exp.
  Qed.

  Lemma lp_block :
    forall Γ ins blk n envI bs env nenv acc nacc,
      restr_block blk ->
      wt_block G Γ blk ->
      wl_block G blk ->
      nenv <= take_env n env ->
      nacc <= take_env n acc ->
      denot_block G ins blk envG (take_env n envI) (take n bs) nenv nacc
      <= take_env n (denot_block G ins blk envG envI bs env acc).
  Proof.
    intros * Hr Hwt Hwl Lee Lea.
    rewrite 2 denot_block_eq; cases; inv Hr.
    inv Hwl; take (wl_equation _ _) and inv it.
    inv Hwt; take (wt_equation _ _ _) and inv it.
    rewrite annots_numstreams in *.
    rewrite take_env_of_np_ext; eauto 3 using lp_exps.
  Qed.

  Lemma lp_node :
    forall n nd envI nenv env,
      restr_node nd ->
      wt_node G nd ->
      nenv <= take_env n env ->
      denot_node G nd envG (take_env n envI) nenv
      <= take_env n (denot_node G nd envG envI env).
  Proof.
    intros n nd envI nenv env Hr Hwt Hnle.
    rewrite 2 denot_node_eq.
    rewrite 2 denot_top_block_eq.
    apply wt_node_wl_node in Hwt as Hwl.
    inversion_clear Hwl as [? HH]; revert HH.
    inversion_clear Hwt as [????? HH]; revert HH.
    inversion_clear Hr as [?? Hfr].
    intro Hwt; inv Hwt; take (wt_scope _ _ _ _) and inv it.
    intro Hwl; inv Hwl; take (wl_scope _ _ _) and inv it.
    rewrite 2 denot_blocks_eq.
    induction blks as [|b blks]; simpl (fold_right _ _ _); auto.
    do 3 take (Forall _ (_::_)) and inv it.
    rewrite lp_bss.
    - eapply lp_block; auto; eauto.
    - pose proof (n_ingt0 nd).
      destruct (n_in nd); simpl in *; try congruence; lia.
  Qed.

End LP_node.


(* TODO: check hypotheses *)
Theorem lp_global :
  forall (G : global),
    restr_global G ->
    wt_global G ->
    forall f n envI,
      denot_global G f (take_env n envI) <= take_env n (denot_global G f envI).
Proof.
  intros * Hr Hwt f n envI.
  apply wt_global_wl_global in Hwt as Hwl.
  apply wl_global_Ordered_nodes in Hwl as Hord.
  destruct (find_node f G) as [nd|] eqn:Hfind.
  2:{ (* si find_node = None, c'est gagné *)
    unfold denot_global.
    rewrite <- PROJ_simpl, 2 FIXP_eq, PROJ_simpl, 2 denot_global_eq, Hfind.
    apply Dbot. }
  (* TODO: ce schéma (set envG, HenvG, etc. semble récurrent, en faire une tactique ? *)
  (* NON, car ça va dégager un jour *)
  remember (denot_global G) as envG eqn:HG.
  assert (forall f nd envI,
             find_node f G = Some nd ->
             envG f envI == FIXP _ (denot_node G nd envG envI)) as HenvG.
  { intros * Hf; subst.
    unfold denot_global.
    now rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl, denot_global_eq, Hf at 1. }
  clear HG. (* maintenant HenvG contient tout ce qu'on doit savoir sur envG *)
  revert Hfind.
  revert f envI nd n.
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
      intros env Hle.
      rewrite FIXP_eq.
      inv Hr.
      apply wt_global_uncons in Hwt as Wt.
      apply wt_global_cons in Hwt.
      inversion_clear Hwl as [|?? [Wl]]; simpl in Wl.
      apply lp_node; auto.
      (* reste l'hypothèse de récurrence sur les nœuds *)
      clear dependent envI.
      intros f2 n2 envI2 Find2.
      edestruct (find_node f2 _) eqn:?; try congruence.
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

End LP.

Module LpFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Senv  : STATICENV     Ids Op OpAux Cks)
       (Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ   : LTYPING Ids Op OpAux Cks Senv Syn)
       (Lord  : LORDERED     Ids Op OpAux Cks Senv Syn)
       (Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord)
<: LP Ids Op OpAux Cks Senv Syn Typ Lord Den.
  Include LP Ids Op OpAux Cks Senv Syn Typ Lord Den.
End LpFun.
