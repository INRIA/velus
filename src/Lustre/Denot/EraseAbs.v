From Coq Require Import Datatypes List.
Import List.ListNotations.

From Velus Require Import Lustre.Denot.Cpo CommonTactics.
Require Import CommonDS SDfuns.

Definition safe_DS {A} : DS (sampl A) -> Prop :=
  DSForall (fun v => match v with err _ => False | _ => True end).

Definition safe_ty {A} : DS (sampl A) -> Prop :=
  DSForall (fun v => match v with err error_Ty => False | _ => True end).

Definition safe_cl {A} : DS (sampl A) -> Prop :=
  DSForall (fun v => match v with err error_Cl => False | _ => True end).

Definition safe_op {A} : DS (sampl A) -> Prop :=
  DSForall (fun v => match v with err error_Op => False | _ => True end).


Lemma nabs_dec : forall A (x : sampl A), {x <> abs} + {~ x <> abs}.
Proof. intros ? []; auto; now left. Qed.

Definition ea {A} : DS (sampl A) -C-> DS (sampl A).
  refine (FILTER (fun v => v <> abs) _).
  intros []; auto; now left.
Defined.

Lemma ea_cons :
  forall A (x : sampl A) xs,
    ea (cons x xs)
    == match x with
          | abs => ea xs
          | _ => cons x (ea xs)
       end.
Proof.
  intros.
  unfold ea at 1.
  rewrite FILTER_filter, filter_eq_cons.
  destruct (nabs_dec A x), x; try congruence; try reflexivity.
Qed.

Lemma ea_is_cons :
  forall A (xs : DS (sampl A)),
    is_cons (ea xs) ->
    isConP (fun v => v <> abs) xs.
Proof.
  unfold ea.
  intros * Hc%filter_is_cons; auto.
Qed.

Lemma isConP_is_cons :
  forall D (P:D->Prop) xs, isConP P xs -> is_cons xs.
Proof.
  induction 1; auto; now constructor.
Qed.

Theorem erase_unop :
  forall A B (op:A->option B) (xs : DS (sampl A)),
    ea (sunop op xs) == sunop op (ea xs).
Proof.
  intros.
  unfold ea,sunop.
  rewrite 2 MAP_map.
  rewrite 2 FILTER_filter.
  rewrite map_filter; eauto.
  intros []; split; intros; try congruence.
  destruct (op a); congruence.
Qed.


Lemma erase_sbinop_1 :
  forall A B C (op:A->B->option C) xs ys,
    safe_DS (sbinop op xs ys) ->
    ea (sbinop op xs ys) <= sbinop op (ea xs) (ea ys).
Proof.
  intros * Hs.
  apply DSle_rec_eq2 with
    (R := fun U V =>
            (exists xs ys,
                safe_DS (sbinop op xs ys)
                /\ U == ea (sbinop op xs ys)
                /\ V == sbinop op (ea xs) (ea ys))
    ).
  3: eauto.
  intros * ? Eq1 Eq2; setoid_rewrite <- Eq1; setoid_rewrite <- Eq2; eauto.
  clear; intros U V Hc (xs & ys & Hs & Hu & Hv).
  rewrite Hu, Hv in *.
  apply ea_is_cons in Hc as Hcp.
  remember_ds (sbinop op xs ys) as rs.
  revert dependent xs.
  revert dependent ys.
  revert dependent U.
  revert dependent V.
  induction Hcp; intros.
  { rewrite <- eqEps in *; eauto 2. }
  - assert (a = abs); subst.
    { inv Hs. cases. contradict H. congruence. }
    destruct (@is_cons_elim _ xs) as (x & xs' & Hxs).
    { eapply proj1, sbinop_is_cons; rewrite <- Hrs; auto. }
    destruct (@is_cons_elim _ ys) as (y & ys' & Hys).
    { eapply proj2, sbinop_is_cons; rewrite <- Hrs; auto. }
    rewrite Hxs, Hys, 3 ea_cons in *.
    rewrite sbinop_eq in Hrs.
    apply Con_eq_simpl in Hrs as [].
    inv Hs; cases; congruence.
  - destruct (@is_cons_elim _ xs) as (x & xs' & Hxs).
    { eapply proj1, sbinop_is_cons; rewrite <- Hrs; auto. }
    destruct (@is_cons_elim _ ys) as (y & ys' & Hys).
    { eapply proj2, sbinop_is_cons; rewrite <- Hrs; auto. }
    rewrite Hxs, Hys, 3 ea_cons in *.
    rewrite sbinop_eq in *.
    apply Con_eq_simpl in Hrs as [? Hrs].
    inv Hs.
    destruct x, y; try tauto.
    rewrite sbinop_eq, Hrs in *.
    cases_eqn HH; inv HH.
    rewrite 2 first_cons; split; auto.
    setoid_rewrite Hv.
    setoid_rewrite Hu.
    setoid_rewrite Hrs.
    rewrite 2 rem_cons; eauto.
Qed.

Lemma erase_sbinop_2 :
  forall A B C (op:A->B->option C) xs ys,
    safe_DS (sbinop op xs ys) ->
    sbinop op (ea xs) (ea ys) <= ea (sbinop op xs ys).
Proof.
  intros * Hs.
  apply DSle_rec_eq2 with
    (R := fun U V =>
            (exists xs ys,
                safe_DS (sbinop op xs ys)
                /\ U == sbinop op (ea xs) (ea ys)
                /\ V == ea (sbinop op xs ys))
    ).
  3: eauto.
  intros * ? Eq1 Eq2; setoid_rewrite <- Eq1; setoid_rewrite <- Eq2; eauto.
  clear; intros U V Hc (xs & ys & Hs & Hu & Hv).
  rewrite Hu, Hv in *.
  apply sbinop_is_cons in Hc as [Hc1 Hc2].
  apply ea_is_cons in Hc1.
  revert dependent ys.
  revert U V.
  induction Hc1; intros.
  - rewrite <- eqEps in *; apply IHHc1; auto.
  - apply ea_is_cons in Hc2 as Hc2'.
    induction Hc2'.
    + rewrite <- eqEps in *; apply IHHc2'; auto.
    + rewrite sbinop_eq in *.
      inv Hs.
      cases_eqn HH; subst.
      2: contradict H0; congruence.
      repeat rewrite ea_cons in *.
      eapply IHHc1; auto.
    + repeat rewrite ea_cons in *.
      repeat rewrite sbinop_eq in *.
      inv Hs.
      cases_eqn HH; subst; try congruence.
      repeat rewrite ea_cons in *.
      rewrite sbinop_eq in *.
      cases_eqn HH; subst; try congruence.
      inv HH2; inv HH.
      rewrite 2 first_cons; split; auto.
      do 2 esplit; rewrite Hu, Hv, 2 rem_cons; eauto.
  - apply ea_is_cons in Hc2 as Hc2'.
    induction Hc2'.
    + rewrite <- eqEps in *; apply IHHc2'; auto.
    + rewrite sbinop_eq in *.
      inv Hs.
      cases_eqn HH; subst.
      all: contradict H0; congruence.
    + repeat rewrite ea_cons in *.
      repeat rewrite sbinop_eq in *.
      inv Hs.
      cases_eqn HH; subst; try congruence.
      repeat rewrite ea_cons in *.
      rewrite sbinop_eq in *.
      cases_eqn HH; subst; try congruence.
      inv HH2; inv HH.
      rewrite 2 first_cons; split; auto.
      do 2 esplit; rewrite Hu, Hv, 2 rem_cons; eauto.
Qed.

Theorem erase_sbinop :
  forall A B C (op:A->B->option C) xs ys,
    safe_DS (sbinop op xs ys) ->
    sbinop op (ea xs) (ea ys) == ea (sbinop op xs ys).
Proof.
  split; auto using erase_sbinop_1, erase_sbinop_2.
Qed.


Lemma erase_fby1 :
  forall A v (xs ys : DS (sampl A)),
    safe_DS (fby1 (Some v) xs ys) ->
    ea (fby1 (Some v) xs ys) <= cons (pres v) (ea ys).
Proof.
  intros * Hs.

  apply DSle_rec_eq2 with
    (R := fun U V =>
            (exists v xs ys,
              safe_DS (fby1 (Some v) xs ys)
              /\ U == ea (fby1 (Some v) xs ys)
              /\ V == cons (pres v) (ea ys))
            \/
            (exists xs ys,
              safe_DS (fby1AP None xs ys)
              /\ U == ea (fby1AP None xs ys)
              /\ V == ea ys)
    ).
  3: eauto 12.
  intros * ? Eq1 Eq2; setoid_rewrite <- Eq1; setoid_rewrite <- Eq2; eauto 12.
  clear; intros U V Hc [(v & xs & ys & Sf & Hu & Hv) | (xs & ys & Sf & Hu & Hv)].
  - rewrite Hu, Hv in *.
  apply ea_is_cons in Hc as Hcp.
  remember_ds (fby1 (Some v) xs ys) as rs.
  revert dependent xs.
  revert dependent ys.
  revert dependent U.
  revert dependent V.
  revert dependent v.
  induction Hcp; intros.
  { rewrite <- eqEps in *; eauto 2. }
  all: destruct (@is_cons_elim _ xs) as (x & xs' & Hxs);
    [eapply fby1_cons; rewrite <- Hrs; eauto | rewrite Hxs in *].
  + assert (a = abs); subst.
    { apply Decidable.not_not in H; auto.
      unfold Decidable.decidable.
      destruct a; auto; right; congruence. }
    rewrite fby1_eq in Hrs.
    destruct x; apply Con_eq_simpl in Hrs as [? Hrs]; try congruence.
    rewrite ea_cons in *.
    all: destruct (@is_cons_elim _ ys) as (y & ys' & Hys);
      [eapply fby1AP_cons, isConP_is_cons; rewrite <- Hrs; eauto | rewrite Hys in *].
    inversion_clear Sf as [|??? Sf'].
    rewrite fby1AP_eq in Hrs.
    destruct y; rewrite ea_cons in *; eauto 2.
    all: exfalso; clear IHHcp.
    all: destruct (@is_cons_elim _ s) as (vs & s' & Hs);
      [eapply isConP_is_cons; eauto | rewrite Hs in *].
    all: apply symmetry, map_eq_cons_elim in Hrs as (?&?&?&?&?); subst;
      now inversion Sf'.
  + inversion_clear Sf as [|??? Sf'].
    rewrite fby1_eq in Hrs.
    destruct a, x; apply Con_eq_simpl in Hrs as [HH Ht];
      inversion_clear HH; try (tauto || congruence).
     rewrite ea_cons in *.
    rewrite 2 first_cons; split; auto.
    setoid_rewrite Hu.
    setoid_rewrite Hv.
    setoid_rewrite rem_cons.
    setoid_rewrite Ht.
    rewrite Ht in Sf'.
    right.
    exists xs', ys. split; auto.
  -
    rewrite Hu, Hv in *.
    destruct (@is_cons_elim _ ys) as (y & ys' & Hys);
      [eapply  fby1AP_cons, isConP_is_cons, ea_is_cons; eauto
      | rewrite Hys in *].
    rewrite fby1AP_eq in *.
    destruct y; rewrite ea_cons in *.
    1,3: destruct (@is_cons_elim _ xs) as (x & xs' & Hxs);
    [eapply map_is_cons, isConP_is_cons, ea_is_cons, Hc
    | rewrite Hxs, map_eq_cons in *]; now inversion_clear Sf.

    (* on se retrouve dans le même cas qu'avant !! *)
    { clear Hys ys.
      rename a into v.
      rename ys' into ys.
  apply ea_is_cons in Hc as Hcp.
  remember_ds (fby1 (Some v) xs ys) as rs.
  revert dependent xs.
  revert dependent ys.
  revert dependent U.
  revert dependent V.
  revert dependent v.
  induction Hcp; intros.
  { rewrite <- eqEps in *; eauto 2. }
  all: destruct (@is_cons_elim _ xs) as (x & xs' & Hxs);
    [eapply fby1_cons; rewrite <- Hrs; eauto | rewrite Hxs in *].
  + assert (a = abs); subst.
    { apply Decidable.not_not in H; auto.
      unfold Decidable.decidable.
      destruct a; auto; right; congruence. }
    rewrite fby1_eq in Hrs.
    destruct x; apply Con_eq_simpl in Hrs as [? Hrs]; try congruence.
    rewrite ea_cons in *.
    all: destruct (@is_cons_elim _ ys) as (y & ys' & Hys);
      [eapply fby1AP_cons, isConP_is_cons; rewrite <- Hrs; eauto | rewrite Hys in *].
    inversion_clear Sf as [|??? Sf'].
    rewrite fby1AP_eq in Hrs.
    destruct y; rewrite ea_cons in *; eauto 2.
    all: exfalso; clear IHHcp.
    all: destruct (@is_cons_elim _ s) as (vs & s' & Hs);
      [eapply isConP_is_cons; eauto | rewrite Hs in *].
    all: apply symmetry, map_eq_cons_elim in Hrs as (?&?&?&?&?); subst;
      now inversion Sf'.
  + inversion_clear Sf as [|??? Sf'].
    rewrite fby1_eq in Hrs.
    destruct a, x; apply Con_eq_simpl in Hrs as [HH Ht];
      inversion_clear HH; try (tauto || congruence).
     rewrite ea_cons in *.
    rewrite 2 first_cons; split; auto.
    setoid_rewrite Hu.
    setoid_rewrite Hv.
    setoid_rewrite rem_cons.
    setoid_rewrite Ht.
    rewrite Ht in Sf'.
    right.
    exists xs', ys. split; auto.
    }
Qed.

Theorem erase_fby :
  forall A (xs ys : DS (sampl A)),
    safe_DS (fby xs ys) ->
    ea (fby xs ys) <= app (ea xs) (ea ys).
Proof.
  intros * Hs.
  remember_ds (ea (fby xs ys)) as U.
  remember_ds (app (ea xs) (ea ys)) as V.
  revert_all; cofix Cof; intros.
  destruct U as [|u U]; [|clear Cof].
  { constructor; rewrite <- eqEps in *; eapply Cof; eauto. }
  (* on a une valeur sur U, donc un élément non absent dans xs *)
  remember_ds (fby xs ys) as t.
  apply symmetry in HU as HU2.
  apply cons_is_cons, ea_is_cons in HU2.
  rewrite HU, HV.
  clear HU HV U V u.
  revert dependent xs.
  revert dependent ys.
  induction HU2; intros.
  { rewrite <- eqEps in *; auto. }
  all: destruct (@is_cons_elim _ xs) as (x & xs' & Hxs);
    [eapply fby_cons; rewrite <- Ht; eauto | rewrite Hxs in *].
  - assert (a = abs); subst.
    { apply Decidable.not_not in H; auto.
      unfold Decidable.decidable.
      destruct a; auto; right; congruence. }
    rewrite fby_eq in Ht.
    destruct x; apply Con_eq_simpl in Ht as [? Ht]; try congruence.
    all: destruct (@is_cons_elim _ ys) as (y & ys' & Hys);
      [eapply fbyA_cons, isConP_is_cons; rewrite <- Ht; eauto | rewrite Hys in *].
    inversion_clear Hs as [|??? Hs'].
    rewrite fbyA_eq in Ht.
    destruct y; rewrite 3 ea_cons; auto.
    all: destruct (@is_cons_elim _ s) as (vs & s' & Hs);
      [eapply isConP_is_cons; eauto | rewrite Hs in *].
    all: apply symmetry, map_eq_cons_elim in Ht as (?&?&?&?&?); subst;
      now inversion Hs'.
  - inversion_clear Hs as [|??? Hs'].
    rewrite fby_eq in Ht.
    destruct a, x; try (tauto || congruence).
    all: apply Con_eq_simpl in Ht as [HH Ht]; try congruence.
    inversion_clear HH.
    rewrite 2 ea_cons, app_cons.
    apply cons_le_compat; auto.

    clear - Ht Hs'.

    remember_ds (ea s) as U.
    remember_ds (ea ys) as V.
    revert_all; cofix Cof; intros.
    destruct U as [|u U]; [|clear Cof].
    { constructor; rewrite <- eqEps in *; eapply Cof; eauto. }
    destruct (@is_cons_elim _ ys) as (y & ys' & Hys);
      [eapply fby1AP_cons, isConP_is_cons, ea_is_cons; rewrite <- Ht, <- HU; eauto
      | rewrite Hys in *].
    rewrite fby1AP_eq in Ht.
    destruct y; rewrite Ht in *.
    2: (* cas intéressant *)
      rewrite HU, HV, ea_cons, erase_fby1; now auto.
    all:
    destruct (@is_cons_elim _ xs') as (x & xs & Hxs);
      [eapply map_is_cons, isConP_is_cons, ea_is_cons; rewrite <- HU; eauto
      | rewrite Hxs, map_eq_cons in *; now inversion Hs'].
Qed.


(* FAUX. Par ex :
     xs = A 0 A A A A ...
     ys = A 1 A A A A ...
     ea (fby xs ys) = 0
     app (ea xs) (ea ys) = 0 1
 *)
Theorem erase_fby_inf :
  forall A (xs ys : DS (sampl A)),
    infinite (fby xs ys) ->
    safe_DS (fby xs ys) ->
    ea (fby xs ys) == app (ea xs) (ea ys).
Abort.
