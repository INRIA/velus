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

      (* FIXME: partagé avec Abs.v *)
      Lemma np_of_env_cons :
        forall i l env,
          np_of_env (i :: l) env
          = nprod_cons (env i) (np_of_env l env).
      Proof.
        trivial.
      Qed.
          Lemma sreset_aux_bot : forall f (X Y:DS_prod SI), sreset_aux f 0 X Y == 0.
          Proof.
            intros.
            unfold sreset_aux.
            apply Oprodi_eq_intro; intro i.
            rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl.
            now apply DScase_bot_eq.
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


(** ** On montre que chaque opérateur du langage a cette propriété *)

Lemma take_np_of_env :
  forall l env n,
    0 < length l ->
    lift (take n) (np_of_env l env) == np_of_env l (take_env n env).
Proof.
  induction l as [|i [|j]]; intros * Hl; simpl in Hl.
  - inversion Hl.
  - cbn; now rewrite take_env_proj.
  - rewrite 2 (np_of_env_cons i (j :: l)), <- IHl; [| simpl; lia].
    setoid_rewrite (lift_cons (take n) _ (env i) (np_of_env (j :: l) env)).
    now rewrite take_env_proj.
Qed.

Lemma take_env_of_np :
  forall l (np : nprod (length l)) n,
    env_of_np l (lift (take n) np) == take_env n (env_of_np l np).
Proof.
  intros.
  apply Oprodi_eq_intro; intro x.
  rewrite take_env_proj, 2 env_of_np_eq.
  cases_eqn Hmem.
  - apply mem_nth_Some in Hmem; auto.
    erewrite nth_lift; eauto.
  - now rewrite take_bot.
Qed.

Lemma take_env_of_np_ext :
  forall l n m (np : nprod m) env,
    m = length l ->
    take_env n (env_of_np_ext l np env) == env_of_np_ext l (lift (take n) np) (take_env n env).
Proof.
  intros; subst.
  apply Oprodi_eq_intro; intro i.
  rewrite take_env_proj, 2 env_of_np_ext_eq, take_env_proj.
  cases_eqn HH; apply mem_nth_Some in HH; auto.
  erewrite nth_lift; auto.
Qed.

Lemma take_bss :
  forall l n (env : DS_prod SI),
    l <> [] ->
    bss l (take_env n env) == take n (bss l env).
Proof.
  induction l as [|i [|j ]]; intros * Hl.
  - contradiction.
  - rewrite 2 bss_cons; simpl (bss [] _).
    rewrite take_zip, take_env_proj, 2 CTE_eq.
    unfold AC at 1.
    now rewrite MAP_map, <- take_map, zip_take_const.
  - rewrite 2 (bss_cons i), take_zip, <- IHl, take_env_proj; [|congruence].
    unfold AC.
    now rewrite 2 MAP_map, take_map.
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

Lemma take_sunop :
  forall A B (op : A -> option B),
  forall n xs,
    take n (sunop op xs) == sunop op (take n xs).
Proof.
  intros.
  unfold sunop.
  autorewrite with cpodb; simpl.
  now rewrite take_map.
Qed.

Lemma take_sbinop :
  forall A B D (op : A -> B-> option D),
  forall n xs ys,
    take n (sbinop op xs ys) == sbinop op (take n xs) (take n ys).
Proof.
  intros.
  unfold sbinop.
  now rewrite take_zip.
Qed.

(** pour fby/fby1, c'est compliqué, on le fait en deux temps *)

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

(* TODO: comment faire ça sans lemme ? *)
Lemma Dprodi_le_elim : forall (I:Type)(D:I->cpo) (p q : Dprodi D), p<=q -> forall i, p i <= q i.
  intros ???? H; apply H.
Qed.

(* FIXME: pour l'instant on fait le reset en deux temps, mais comment faire mieux ?
   il faudrait un autre principe d'induction sur les environnement pour chercher
   une valeur de rs... *)
Lemma take_sreset_aux_le1 :
  forall (f : DS_prod SI -C-> DS_prod SI)
    (Hf : forall n envI, f (take_env n envI) == take_env n (f envI)),
  forall n rs X Y,
    take_env n (sreset_aux f rs X Y)
    <= sreset_aux f (take n rs) (take_env n X) (take_env n Y).
Proof.
  intros f Hf.
  induction n; intros.
  { now rewrite take_env_eq, sreset_aux_bot. }
  intro i.
  remember_ds (take_env _ (sreset_aux _ _ _ _) i) as U.
  remember_ds (sreset_aux _ _ _ _ i) as V.
  revert_all; cofix Cof; intros; destruct U; [|].
  { constructor; rewrite <- eqEps in *; eapply Cof; eauto. }
  clear Cof; rewrite HU, HV; apply Dprodi_le_elim.
  edestruct (@is_cons_elim _ rs) as (r & rs' & Hr); [| clear HU HV ].
  { eapply is_cons_sreset_aux, take_is_cons; now rewrite <- take_env_proj, <- HU. }
  rewrite 3 (take_env_eq (S n)), (take_eq (S n)).
  rewrite Hr, app_cons, rem_cons, 2 (sreset_aux_eq f r).
  destruct r.
  - rewrite 2 sreset_aux_eq.
    rewrite app_app_env, app_rem_take_env.
    rewrite <- (take_env_eq (S n)), (Hf (S n)), <- 2 take_rem_env.
    rewrite (take_env_eq (S n) (f X)), app_app_env; auto.
  - rewrite 2 app_app_env, app_rem_take_env.
    rewrite <- 2 (take_env_eq (S n)), <- 2 take_rem_env; auto.
Qed.

Lemma take_sreset_aux_le2 :
  forall (f : DS_prod SI -C-> DS_prod SI)
    (Hf : forall n envI, f (take_env n envI) == take_env n (f envI)),
  forall n rs X Y,
    sreset_aux f (take n rs) (take_env n X) (take_env n Y)
    <= take_env n (sreset_aux f rs X Y).
Proof.
  intros f Hf.
  induction n; intros.
  { now rewrite take_env_eq, sreset_aux_bot. }
  intro i.
  remember_ds (sreset_aux _ _ _ _ i) as U.
  remember_ds (take_env _ (sreset_aux _ _ _ _) i) as V.
  revert_all; cofix Cof; intros; destruct U; [|].
  { constructor; rewrite <- eqEps in *; eapply Cof; eauto. }
  clear Cof; rewrite HU, HV; apply Dprodi_le_elim.
  edestruct (@is_cons_elim _ rs) as (r & rs' & Hr); [| clear HU HV ].
  { eapply take_is_cons, is_cons_sreset_aux; now rewrite <- HU. }
  rewrite 3 (take_env_eq (S n)), (take_eq (S n)).
  rewrite Hr, app_cons, rem_cons, 2 (sreset_aux_eq f r).
  destruct r.
  - rewrite 2 sreset_aux_eq.
    rewrite app_app_env, app_rem_take_env.
    rewrite <- (take_env_eq (S n)), (Hf (S n)), <- 2 take_rem_env.
    rewrite (take_env_eq (S n) (f X)), app_app_env; auto.
  - rewrite 2 app_app_env, app_rem_take_env.
    rewrite <- 2 (take_env_eq (S n)), <- 2 take_rem_env; auto.
Qed.

Lemma take_sreset_aux :
  forall (f : DS_prod SI -C-> DS_prod SI)
    (Hf : forall n envI, f (take_env n envI) == take_env n (f envI)),
  forall n rs X Y,
    sreset_aux f (take n rs) (take_env n X) (take_env n Y)
    == take_env n (sreset_aux f rs X Y).
Proof.
  split.
  - now apply take_sreset_aux_le2.
  - now apply take_sreset_aux_le1.
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

        (* Lemma fcont_app_le_compat : forall (D1 D2:cpo) (f g : D1 -c> D2) (x y : D1), *)
        (*     f <= g -> x <= y -> f x <= g y. *)
        (* Proof. *)
        (*   intros. *)
        (*   apply Ole_trans with (f y); auto. *)
        (* Qed. *)


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
      envG f (take_env n envI) == take_env n (envG f envI).

  Lemma take_var :
    forall ins x n envI env,
      denot_var ins (take_env n envI) (take_env n env) x
      == take n (denot_var ins envI env x).
  Proof.
    intros.
    unfold denot_var.
    rewrite 2 take_env_proj; cases.
  Qed.

  (* utile pour les cas récursifs *)
  Lemma lift_IH :
    forall ins es envG envI env n,
      Forall (fun e => denot_exp G ins e envG (take_env n envI) (take_env n env)
                    == lift (take n) (denot_exp G ins e envG envI env)) es ->
      denot_exps G ins es envG (take_env n envI) (take_env n env)
      == lift (take n) (denot_exps G ins es envG envI env).
  Proof.
    induction es; intros * Hf; inv Hf.
    - rewrite 2 denot_exps_nil; auto.
    - rewrite 2 denot_exps_eq.
      setoid_rewrite lift_app; auto.
  Qed.

  (* idem *)
  Lemma lift_IHs :
    forall ins (ess : list (enumtag * _)) m envG envI bs env n,
      Forall (fun es =>
                Forall (fun e => denot_exp G ins e envG (take_env n envI) (take n bs) (take_env n env)
                    == lift (take n) (denot_exp G ins e envG envI bs env)) (snd es)) ess ->
      denot_expss G ins ess m envG (take_env n envI) (take n bs) (take_env n env)
      == lift (lift (take n)) (denot_expss G ins ess m envG envI bs env).
  Proof.
    intros * Hf.
    induction ess as [|(x,es)]; inv Hf.
    - rewrite 2 denot_expss_nil; simpl.
      now rewrite lift_nprod_const, take_map.
    - rewrite 2 denot_expss_eq.
      unfold eq_rect.
      cases; subst.
      + match goal with
          |-_ == _ (_ (_ ?a) ?b) =>
            setoid_rewrite (lift_cons (lift (take n)) _ a b)
        end; rewrite lift_IH; auto.
      + simpl (length _).
        now rewrite 2 lift_nprod_const, take_map.
  Qed.

  Lemma lp_exp :
    forall Γ ins e n envI bs env,
      wt_exp G Γ e ->
      wl_exp G e ->
      denot_exp G ins e envG (take_env n envI) (take n bs) (take_env n env)
      == lift (take n) (denot_exp G ins e envG envI bs env).
  Proof.
    intros * Hwt Hwl.
    induction e using exp_ind2.
    - (* Econst *)
      rewrite 2 denot_exp_eq.
      unfold sconst.
      rewrite 2 MAP_map, <- take_map; auto.
    - (* Eenum *)
      rewrite 2 denot_exp_eq.
      unfold sconst.
      rewrite 2 MAP_map, <- take_map; auto.
    - (* Evar *)
      rewrite 2 denot_exp_eq.
      now rewrite take_var.
    - (* Elast *)
      rewrite 2 denot_exp_eq.
      now setoid_rewrite take_bot.
    - (* Eunop *)
      inv Hwt. inv Hwl.
      rewrite 2 (denot_exp_eq _ _ (Eunop _ _ _)).
      revert IHe.
      gen_sub_exps.
      take (numstreams _ = _) and rewrite it.
      take (typeof _ = _) and rewrite it.
      cbv zeta; intros t1 t2 IHe.
      setoid_rewrite take_sunop.
      now rewrite IHe.
    - (* Ebinop *)
      inv Hwt. inv Hwl.
      rewrite 2 (denot_exp_eq _ _ (Ebinop _ _ _ _)).
      revert IHe1 IHe2.
      gen_sub_exps.
      do 2 (take (numstreams _ = _) and rewrite it; clear it).
      do 2 (take (typeof _ = _) and rewrite it; clear it).
      cbv zeta; intros t1 t2 t3 t4 IHe1 IHe2.
      setoid_rewrite take_sbinop; auto.
    - (* Eextcall *)
      rewrite 2 denot_exp_eq.
      now setoid_rewrite take_bot.
    - (* Efby *)
      inv Hwt. inv Hwl.
      apply Forall_impl_inside with (P := wt_exp _ _) in H, H0; auto.
      apply Forall_impl_inside with (P := wl_exp _ ) in H, H0; auto.
      apply lift_IH in H, H0; revert H H0.
      rewrite 2 (denot_exp_eq _ _ (Efby _ _ _)).
      gen_sub_exps.
      rewrite annots_numstreams in *.
      simpl; unfold eq_rect; cases; try congruence.
      intros t1 t2 t3 t4 Eq1 Eq2.
      rewrite take_lift_fby; auto.
    - (* Earrow *)
      rewrite 2 denot_exp_eq.
      simpl; induction (length a) as [|[]].
      + now setoid_rewrite take_bot.
      + now setoid_rewrite take_bot.
      + apply Dprod_eq_pair; auto.
        now setoid_rewrite take_bot.
    - (* Ewhen *)
      inv Hwt. inv Hwl.
      apply Forall_impl_inside with (P := wt_exp _ _) in H; auto.
      apply Forall_impl_inside with (P := wl_exp _ ) in H; auto.
      apply lift_IH in H; revert H.
      rewrite 2 (denot_exp_eq _ _ (Ewhen _ _ _ _)).
      gen_sub_exps.
      rewrite annots_numstreams in *.
      simpl; unfold eq_rect; cases; try congruence.
      intros t1 t2 Eq.
      rewrite take_lift_swhenv, take_var; auto.
    - (* Emerge *)
      inv Hwt. inv Hwl.
      rewrite 2 (denot_exp_eq _ _ (Emerge _ _ _)).
      pose proof (IH := lift_IHs ins es (length tys) envG envI bs env n).
      eassert (Heq: _ == _); [apply IH; simpl_Forall; auto|clear IH].
      cbv zeta; revert Heq.
      gen_sub_exps; intros t1 t2 Eq.
      unfold eq_rect_r, eq_rect, eq_sym; cases.
      rewrite lift_lift_nprod, take_lift_smergev, take_var; auto.
    - destruct d as [des|].
      { (* Ecase défaut *)
      inv Hwt. inv Hwl.
      set (typesof des) as tys.
      apply Forall_impl_inside with (P := wt_exp _ _) in H0; auto.
      apply Forall_impl_inside with (P := wl_exp _ ) in H0; auto.
      apply lift_IH in H0.
      pose proof (IH := lift_IHs ins es (length tys) envG envI bs env n).
      eassert (Eq: _ == _); [apply IH; simpl_Forall; auto|clear H IH].
      rewrite 2 (denot_exp_eq _ _ (Ecase _ _ _ _)).
      cbv zeta; revert IHe H0 Eq; gen_sub_exps.
      assert (Hl : list_sum (List.map numstreams des) = length tys)
        by (subst tys; now rewrite length_typesof_annots, annots_numstreams).
      take (numstreams e = 1) and rewrite it, Hl.
      simpl (numstreams _). (* dans les types... *)
      unfold eq_rect_r, eq_rect, eq_sym; cases; try congruence.
      intros t1 t2 t3 t4 t5 t6 Eq1 Eq2 Eq3.
      rewrite take_lift_scase_defv, Eq1; auto.
      }{ (* Ecase total *)
      inv Hwt. inv Hwl.
      rewrite 2 (denot_exp_eq _ _ (Ecase _ _ _ _)).
      pose proof (IH := lift_IHs ins es (length tys) envG envI bs env n).
      eassert (Heq: _ == _); [apply IH; simpl_Forall; auto|clear IH].
      cbv zeta; revert IHe Heq; gen_sub_exps.
      take (numstreams e = 1) and rewrite it.
      unfold eq_rect_r, eq_rect, eq_sym; cases.
      intros t1 t2 t3 t4 Eq1 Eq2.
      rewrite lift_lift_nprod, take_lift_scasev, Eq1; auto. }
    - (* Eapp *)
      inv Hwt. inv Hwl.
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
      intros t1 t2 t3 t4 Eq1 Eq2.
      rewrite 2 sreset_eq, take_np_of_env.
      2: rewrite map_length; apply n_outgt0.
      apply fcont_stable.
      (* clear - Eq1 Eq2 Hnode. *)
      destruct (list_sum (List.map numstreams er)).
      + (* s'il n'y a pas de signal reset *)
        rewrite take_sreset_aux_false, sreset_aux_false; auto.
        rewrite <- Hnode, <- take_env_of_np, Eq1; auto; congruence.
      + (* sinon *)
        rewrite <- take_sreset_aux, <- take_env_of_np.
        2: intros; apply Hnode; congruence.
        rewrite take_sbools_of; auto with arith.
        rewrite <- Hnode, <- take_env_of_np, Eq1, Eq2; auto; congruence.
  Qed.

  Corollary lp_exps :
    forall Γ ins es n envI bs env,
      Forall (wt_exp G Γ) es ->
      Forall (wl_exp G) es ->
      denot_exps G ins es envG (take_env n envI) (take n bs) (take_env n env)
      == lift (take n) (denot_exps G ins es envG envI bs env).
  Proof.
    induction es as [|e es]; intros * Hwt Hwl; inv Hwl; inv Hwt.
    - now rewrite 2 denot_exps_nil, <- take_map.
    - rewrite 2 denot_exps_eq.
      match goal with
        |-_ == _ (_ (_ ?a) ?b) => setoid_rewrite (lift_app (take n) _ a _ b)
      end.
      rewrite lp_exp, IHes; eauto.
  Qed.

  Lemma lp_block :
    forall Γ ins blk n envI bs env acc,
      wt_block G Γ blk ->
      wl_block G blk ->
      denot_block G ins blk envG (take_env n envI) (take n bs) (take_env n env) (take_env n acc)
      == take_env n (denot_block G ins blk envG envI bs env acc).
  Proof.
    intros * Hwt Hwl.
    rewrite 2 denot_block_eq; cases.
    inv Hwl; take (wl_equation _ _) and inv it.
    inv Hwt; take (wt_equation _ _ _) and inv it.
    rewrite annots_numstreams in *.
    rewrite take_env_of_np_ext; eauto 3 using lp_exps.
  Qed.

  Lemma lp_node :
    forall n nd envI env,
      wt_node G nd ->
      denot_node G nd envG (take_env n envI) (take_env n env)
      == take_env n (denot_node G nd envG envI env).
  Proof.
    intros n nd envI env Hwt.
    rewrite 2 denot_node_eq.
    rewrite 2 denot_top_block_eq.
    apply wt_node_wl_node in Hwt as Hwl.
    inversion_clear Hwl as [? HH]; revert HH.
    inversion_clear Hwt as [????? HH]; revert HH.
    destruct (n_block nd); intros Hwt Hwl; try now rewrite take_env_bot.
    inv Hwt; take (wt_scope _ _ _ _) and inv it.
    inv Hwl; take (wl_scope _ _ _) and inv it.
    rewrite 2 denot_blocks_eq.
    induction blks as [|b blks]; simpl (fold_right _ _ _).
    { apply symmetry, take_env_bot. }
    do 2 take (Forall _ (_::_)) and inv it.
    rewrite take_bss.
    - rewrite <- lp_block; auto; eauto.
    - pose proof (n_ingt0 nd).
      destruct (n_in nd); simpl in *; try congruence; lia.
  Qed.

End LP_node.

(* TODO: check hypotheses *)
Theorem lp_global :
  forall (G : global),
    wt_global G ->
    forall f n envI,
      denot_global G f (take_env n envI) == take_env n (denot_global G f envI).
Proof.
  intros * Hwt f n envI.
  apply wt_global_wl_global in Hwt as Hwl.
  apply wl_global_Ordered_nodes in Hwl as Hord.
  destruct (find_node f G) as [nd|] eqn:Hfind.
  2:{ (* si find_node = None, c'est gagné *)
    unfold denot_global.
    rewrite <- PROJ_simpl, 2 FIXP_eq, PROJ_simpl, 2 denot_global_eq, Hfind.
    now rewrite take_env_bot. }
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
    apply wt_global_uncons in Hwt as Wt.
    apply wt_global_cons in Hwt.
    inversion_clear Hwl as [|?? [Wl]]; simpl in Wl.
    (* On ne peut pas prouver l'égalité directement avec fixp_ind,
       car [take_env n envI] est pris dans le point fixe. On prouve donc
       l'inégalité dans les deux sens *)

    (* une spécialisation de IHnds utile dans les deux cas *)
    assert (IH : forall f n0 envI0,
               find_node f {| types := tys; externs := exts; nodes := nds |} <> None ->
               envG f (take_env n0 envI0) == take_env n0 (envG f envI0)).
    { clear dependent envI.
      intros f2 n2 envI2 Find2.
      edestruct (find_node f2 _) eqn:?; try congruence.
      eapply IHnds; auto; [ now eauto using Ordered_nodes_cons | | eassumption ].
      (* montrer que HenvG tient toujours *)
      intros f' ndf' envI' Hfind'.
      rewrite HenvG, <- denot_node_cons;
        eauto using find_node_uncons, find_node_later_not_Is_node_in. }
    split.
    + (* <= *)
      rewrite FIXP_fixp.
      apply fixp_ind; auto.
      * (* admissibilité, pas trop dur : *)
        intros f Hf; exact (lub_le Hf).
      * (* itération *)
        intros env Hle.
        rewrite FIXP_eq.
        rewrite <- lp_node; auto.
        apply fcont_monotonic, Hle.
    + (* >= *)
      rewrite FIXP_fixp.
      apply fixp_ind; auto.
      * (* admissibilité *)
       intros f Hf.
       rewrite (@lub_comp_eq _ _ (take_env n) f); auto.
      * (* init *)
        rewrite take_env_bot; auto.
      * (* itération *)
      intros env Hle.
      change (fcontit ?a ?b) with (a b).
      rewrite FIXP_eq, <- lp_node; auto.
  - rewrite find_node_other in Hfind; auto.
    eapply IHnds; auto.
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
