From Velus Require Import Common.
From Velus Require Import Lustre.Denot.Cpo.
Require Import SDfuns CommonDS.

(** * Infinity of streams defined in SDfuns  *)

(* TODO: à terme, virer *)
Ltac solve_err :=
  try match goal with
    | |- context [ DS_const _ ] =>
        repeat rewrite DS_const_eq, rem_cons;
        now (apply is_ncons_DS_const || apply is_consn_DS_const)
        || now auto using is_cons_DS_const, is_consn_DS_const, is_ncons_DS_const
    end.

(** ** Productivity of primitive stream functions  *)

Section Ncons_DS.

Context {A B D : Type}.

Lemma is_ncons_zip :
  forall (f : A -> B -> D) n xs ys,
    is_ncons n xs ->
    is_ncons n ys ->
    is_ncons n (ZIP f xs ys).
Proof.
  induction n as [|[]]; simpl; intros * Cx Cy; auto using is_cons_zip.
  apply is_ncons_is_cons in Cx as Hx.
  apply is_cons_rem in Hx as (?&?&?& Hx); rewrite Hx in *.
  apply is_ncons_is_cons in Cy as Hy.
  apply is_cons_rem in Hy as (?&?&?& Hy); rewrite Hy in *.
  rewrite zip_cons, rem_cons in *.
  apply IHn; auto.
Qed.

Lemma is_ncons_map :
  forall A B (f : A -> B) s n,
    is_ncons n s ->
    is_ncons n (map f s).
Proof.
  unfold is_ncons.
  intros; cases.
  rewrite nrem_map.
  now apply is_cons_map.
Qed.

End Ncons_DS.


(** ** Productivity of Lustre operators *)

Section Ncons_ops.

Context {A B D : Type}.

Lemma is_ncons_sconst :
  forall (c : A) bs n,
    is_ncons n bs ->
    is_ncons n (sconst c bs).
Proof.
  intros.
  now apply is_ncons_map.
Qed.

Lemma sconst_inf :
  forall (c : A) bs,
    infinite bs ->
    infinite (sconst c bs).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros.
  auto using is_ncons_sconst.
Qed.

Lemma is_ncons_sunop :
  forall (f : A -> option B) s n,
    is_ncons n s ->
    is_ncons n (sunop f s).
Proof.
  intros.
  now apply is_ncons_map.
Qed.

Lemma sunop_inf :
  forall (op : A -> option B) s,
    infinite s ->
    infinite (sunop op s).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros.
  auto using is_ncons_sunop.
Qed.

Lemma is_ncons_sbinop :
  forall (f : A -> B -> option D) s1 s2 n,
    is_ncons n s1 ->
    is_ncons n s2 ->
    is_ncons n (sbinop f s1 s2).
Proof.
  intros.
  unfold sbinop.
  autorewrite with cpodb; simpl.
  now apply is_ncons_map, is_ncons_zip.
Qed.

Lemma sbinop_inf :
  forall (f : A -> B -> option D) s1 s2,
    infinite s1 ->
    infinite s2 ->
    infinite (sbinop f s1 s2).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros.
  auto using is_ncons_sbinop.
Qed.

Lemma is_cons_fby :
  forall (xs ys : DS (sampl A)),
    is_cons xs ->
    is_cons (fby xs ys).
Proof.
  intros * Hx.
  apply is_cons_elim in Hx as (?&?&->).
  rewrite fby_eq.
  cases.
Qed.

Lemma is_ncons_S_fby1 :
  forall n v (xs ys : DS (sampl A)),
    is_ncons (S n) xs ->
    is_ncons n ys ->
    is_ncons (S n) (fby1 v xs ys).
Proof.
  induction n; intros * Hx Hy.
  - apply is_cons_elim in Hx as (?&?&->).
    rewrite fby1_eq; simpl; cases.
  - apply is_ncons_elim2 in Hx as (x1 & x2 & xs' & Hx & Hcx' & Hccx').
    apply is_ncons_elim in Hy as (y1 & ys' & Hy & Hcy').
    rewrite Hx, Hy, fby1_eq.
    cases; apply is_ncons_SS; rewrite rem_cons;
      auto using is_ncons_cons, is_ncons_map, is_ncons_S.
    all: rewrite fby1AP_eq; cases; auto using is_ncons_cons, is_ncons_map, is_ncons_S.
Qed.

Lemma is_ncons_S_fby :
  forall n (xs ys : DS (sampl A)),
    is_ncons (S n) xs ->
    is_ncons n ys ->
    is_ncons (S n) (fby xs ys).
Proof.
  induction n; intros * Hx Hy.
  - apply is_cons_elim in Hx as (?&?&->).
    rewrite fby_eq; simpl; cases.
  - apply is_ncons_elim2 in Hx as (x1 & x2 & xs' & Hx & Hcx' & Hccx').
    apply is_ncons_elim in Hy as (y1 & ys' & Hy & Hcy').
    rewrite Hx, Hy, fby_eq.
    cases; apply is_ncons_SS; rewrite rem_cons.
    + rewrite fbyA_eq; cases; auto using is_ncons_cons, is_ncons_map, is_ncons_S.
    + rewrite fby1AP_eq; cases; auto using is_ncons_S_fby1, is_ncons_cons, is_ncons_map, is_ncons_S.
    + auto using is_ncons_cons, is_ncons_map, is_ncons_S.
Qed.

Lemma is_ncons_fby :
  forall n (xs ys : DS (sampl A)),
    is_ncons n xs ->
    is_ncons n ys ->
    is_ncons n (SDfuns.fby xs ys).
Proof.
  intros.
  destruct n as [|[]]; auto.
  apply is_cons_fby; auto.
  apply is_ncons_S_fby, is_ncons_S; auto.
Qed.

Lemma fby_inf :
  forall (xs ys : DS (sampl A)),
    infinite xs ->
    infinite ys ->
    infinite (SDfuns.fby xs ys).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros.
  auto using is_ncons_fby.
Qed.

Lemma is_cons_swhen :
  forall T OT TB,
  forall k xs cs,
    is_cons xs ->
    is_cons cs ->
    is_cons (@swhen A B T OT TB k xs cs).
Proof.
  intros * Hx Hc.
  apply is_cons_elim in Hx as (?&?&->).
  apply is_cons_elim in Hc as (?&?&->).
  rewrite swhen_eq.
  cases.
Qed.

Lemma is_ncons_swhen :
  forall T OT TB,
  forall k n xs cs,
    is_ncons n xs ->
    is_ncons n cs ->
    is_ncons n (@swhen A B T OT TB k xs cs).
Proof.
  induction n as [|[]]; simpl; intros * Hx Hc; auto.
  - apply is_cons_swhen; auto.
  - unfold is_ncons in *.
    apply is_ncons_is_cons in Hx as Hx'.
    apply is_ncons_is_cons in Hc as Hc'.
    apply is_cons_rem in Hx' as (?&?&?& Hx').
    apply is_cons_rem in Hc' as (?&?&?& Hc').
    rewrite Hx', Hc' in *.
    rewrite swhen_eq.
    cases; rewrite rem_cons in *; auto.
    (* reste les cas d'erreur *)
    all: apply (is_ncons_map _ _ _ _ (S n)); auto using is_ncons_zip.
Qed.

Lemma swhen_inf :
  forall T OT TB,
  forall k xs cs,
    infinite xs ->
    infinite cs ->
    infinite (@swhen A B T OT TB k xs cs).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros.
  eauto using is_ncons_swhen.
Qed.

Lemma is_ncons_zip3 :
  forall A B C D (op : A -> B -> C -> D),
  forall xs ys zs n,
    is_ncons n xs /\ is_ncons n ys /\ is_ncons n zs ->
    is_ncons n (ZIP3 op xs ys zs).
Proof.
  intros * (Cx & Cy & Cz).
  rewrite zip3_eq.
  auto using is_ncons_zip.
Qed.

Lemma is_ncons_smerge :
  forall T OT TB,
  forall l n xs cs,
    is_ncons n cs ->
    forall_nprod (@is_ncons _ n) xs ->
    is_ncons n (@smerge A B T OT TB l cs xs).
Proof.
  intros * Hc Hx.
  rewrite smerge_eq.
  eapply forall_nprod_Foldi in Hx; eauto using is_ncons_map.
  simpl; intros.
  now apply is_ncons_zip3.
Qed.

Lemma smerge_inf :
  forall T OT TB,
  forall l xs cs,
    infinite cs ->
    forall_nprod (@infinite _) xs ->
    infinite (@smerge A B T OT TB l cs xs).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros * Inf Hf n.
  apply is_ncons_smerge; eauto using inf_nrem, forall_nprod_impl.
Qed.

Lemma is_ncons_scase :
  forall T OT TB,
  forall l n xs cs,
    is_ncons n cs ->
    forall_nprod (@is_ncons _ n) xs ->
    is_ncons n (@scase A B T OT TB l cs xs).
Proof.
  intros * Hc Hx.
  rewrite scase_eq.
  eapply forall_nprod_Foldi in Hx; eauto using is_ncons_map.
  simpl; intros.
  now apply is_ncons_zip3.
Qed.

Lemma scase_inf :
  forall T OT TB,
  forall l xs cs,
    infinite cs ->
    forall_nprod (@infinite _) xs ->
    infinite (@scase A B T OT TB l cs xs).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros * Inf Hf n.
  apply is_ncons_scase; eauto using inf_nrem, forall_nprod_impl.
Qed.

Lemma is_ncons_scase_def_ :
  forall T OT TB,
  forall l n cs ds xs,
    is_ncons n cs ->
    is_ncons n ds ->
    forall_nprod (@is_ncons _ n) xs ->
    is_ncons n (@scase_def_ A B T OT TB l cs ds xs).
Proof.
  intros * Hc Hd Hx.
  rewrite scase_def__eq.
  apply forall_nprod_Foldi with (Q := is_ncons n);
    auto using is_ncons_zip3, is_ncons_zip.
Qed.

Lemma is_ncons_scase_def :
  forall T OT TB,
  forall l n cs dxs,
    is_ncons n cs ->
    forall_nprod (@is_ncons _ n) dxs ->
    is_ncons n (@scase_def A B T OT TB l cs dxs).
Proof.
  intros * Hc [Hh Ht] % forall_nprod_inv.
  rewrite (nprod_hd_tl dxs).
  rewrite scase_def_eq; auto using is_ncons_scase_def_.
Qed.

Lemma scase_def__inf :
  forall T OT TB,
  forall l cs ds xs,
    infinite cs ->
    infinite ds ->
    forall_nprod (@infinite _) xs ->
    infinite (@scase_def_ A B T OT TB l cs ds xs).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros * Infc Infd Infx n.
  apply is_ncons_scase_def_; eauto using inf_nrem, forall_nprod_impl.
Qed.

Lemma scase_def_inf :
  forall T OT TB,
  forall l cs dxs,
    infinite cs ->
    forall_nprod (@infinite _) dxs ->
    infinite (@scase_def A B T OT TB l cs dxs).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros * Infc Infd n.
  apply is_ncons_scase_def; eauto using inf_nrem, forall_nprod_impl.
Qed.

Lemma is_cons_sreset :
  forall I,
  forall (f : DS_prod (fun _ : I => sampl A) -C-> DS_prod (fun _ : I => sampl A)) R X x,
    (forall envI, (forall x, is_cons (envI x)) -> (forall x, is_cons (f envI x))) ->
    is_cons R ->
    (forall x, is_cons (X x)) ->
    is_cons (@sreset I A f R X x).
Proof.
  intros * Cf Cr Cx.
  apply is_cons_elim in Cr as (vr & R' & Hr).
  rewrite <- PROJ_simpl, sreset_eq, Hr, sreset_aux_eq.
  cases; try apply is_cons_DS_const.
  rewrite sreset_aux_eq.
  all: rewrite PROJ_simpl, APP_env_eq; auto using is_cons_app.
Qed.

Lemma is_cons_sreset_aux :
  forall I,
  forall (f : DS_prod (fun _ : I => sampl A) -C-> DS_prod (fun _ : I => sampl A)) R X Y x,
    (forall envI, (forall x, is_cons (envI x)) -> (forall x, is_cons (f envI x))) ->
    is_cons R ->
    (forall x, is_cons (X x)) ->
    (forall x, is_cons (Y x)) ->
    is_cons (@sreset_aux I A f R X Y x).
Proof.
  intros * Cf Cr Cx Cy.
  apply is_cons_elim in Cr as (vr & R' & Hr).
  rewrite <- PROJ_simpl, Hr, sreset_aux_eq.
  cases; try apply is_cons_DS_const.
  rewrite sreset_aux_eq.
  all: rewrite PROJ_simpl, APP_env_eq; auto using is_cons_app.
Qed.

Lemma is_ncons_sreset :
  forall I,
  forall (f : DS_prod (fun _ : I => sampl A) -C-> DS_prod (fun _ : I => sampl A)) R X x,
    (forall n envI, (forall x, is_ncons n (envI x)) -> (forall x, is_ncons n (f envI x))) ->
    forall n,
      is_ncons n R ->
      (forall x, is_ncons n (X x)) ->
      is_ncons n (@sreset I A f R X x).
Proof.
  intros * Cf n Cr Cx.
  rewrite <- PROJ_simpl, sreset_eq.
  assert (Hy : forall x, is_ncons n (f X x)) by (subst; intros; eauto).
  remember (_ f X) as Y eqn:HH; clear HH.
  rewrite PROJ_simpl.
  revert dependent R.
  revert dependent X.
  revert dependent Y.
  induction n as [|[]]; intros; auto.
  { apply is_cons_sreset_aux; auto; now apply (Cf 1). }
  apply is_ncons_is_cons in Cr as Hr.
  apply is_cons_elim in Hr as (vr & R' & Hr).
  rewrite <- PROJ_simpl, Hr, sreset_aux_eq in *.
  simpl in Cr; rewrite rem_cons in Cr.
  cases; solve_err.
  rewrite sreset_aux_eq.
  all: rewrite PROJ_simpl, APP_env_eq, is_ncons_SS, rem_app;
    eauto using is_ncons_is_cons.
  all: apply IHn; auto.
  intros; rewrite REM_env_eq.
  apply (Cf (S (S n))); auto.
Qed.

Lemma sreset_inf :
  forall I,
  forall (f : DS_prod (fun _ : I => sampl A) -C-> DS_prod (fun _ : I => sampl A)) R X,
    (forall envI, all_infinite envI -> all_infinite (f envI)) ->
    infinite R ->
    all_infinite X ->
    all_infinite (@sreset I A f R X).
Proof.
  intros * If Ir Ix.
  rewrite sreset_eq.
  assert (all_infinite (f X)) as Iy by (subst; auto).
  remember (_ f X) as Y eqn:HH; clear HH.
  intro x.
  remember_ds (sreset_aux _ _ _ _ _) as tx.
  revert dependent tx.
  revert dependent X.
  revert dependent Y.
  revert dependent R.
  cofix Cof; intros.
  inversion_clear Ir as [Hc IIr].
  apply is_cons_elim in Hc as (vr & R' & Hr).
  rewrite Hr, rem_cons in IIr.
  apply REM_env_inf in Iy as Iry, Ix as Irx.
  rewrite <- PROJ_simpl, Hr, sreset_aux_eq in Htx.
  destruct (Iy x), (If X Ix x). (* utile *)
  constructor.
  - rewrite Htx.
    cases.
    rewrite sreset_aux_eq.
    all: rewrite PROJ_simpl, APP_env_eq; auto using is_cons_app.
  - apply rem_eq_compat in Htx.
    destruct (Iy x), (If X Ix x). (* pour plus tard *)
    cases.
    rewrite sreset_aux_eq in Htx.
    all: rewrite PROJ_simpl, APP_env_eq, rem_app in Htx; auto.
    all: eapply Cof in Htx; eauto using REM_env_inf.
Qed.

Lemma sreset_inf_dom :
  forall I,
  forall (f : DS_prod (fun _ : I => sampl A) -C-> DS_prod (fun _ : I => sampl A)) R X,
  forall ins outs,
    (forall envI, infinite_dom envI ins -> infinite_dom (f envI) outs) ->
    infinite R ->
    infinite_dom X ins ->
    infinite_dom (sreset f R X) outs.
Proof.
  intros * If Ir Ix.
  rewrite sreset_eq.
  assert (infinite_dom (f X) outs) as Iy by auto.
  remember (_ f X) as Y eqn:HH; clear HH.
  intros x Hin.
  remember_ds (sreset_aux _ _ _ _ _) as t.
  revert Ir Ix Iy Ht Hin.
  revert R X Y x t.
  cofix Cof; intros.
  apply infinite_decomp in Ir as (r & R' & Hr & Ir').
  rewrite <- PROJ_simpl, Hr, sreset_aux_eq in Ht.
  apply REM_env_inf_dom in Ix as Irx, Iy as Iry.
  destruct (Iy x), (If X Ix x); auto. (* pour plus tard *)
  apply If, REM_env_inf_dom in Ix as Ifx.
  constructor.
  - cases; rewrite Ht, ?sreset_aux_eq, PROJ_simpl, APP_env_eq;
      eauto using app_is_cons.
  - apply rem_eq_compat in Ht.
    destruct r; [rewrite sreset_aux_eq in Ht|];
      rewrite PROJ_simpl, APP_env_eq, rem_app in Ht; eauto 2.
Qed.

End Ncons_ops.
