Require Import List.
Require Import Cpo SDfuns CommonDS.
Open Scope bool_scope.
Import ListNotations.

(** An attempt to prove the equivalence between the reset construct
    of Lucid Synchrone and the one of Denot.SDfuns. *)

(* In "Modular Resetting of Synchronous Data-Flow Programs",
   Hamon & Pouzet encode the reset in two functions:

  let whilenot c = o where
    rec o = true -> if c then false else pre o

  let rec reset_up c x =
    let cond = whilenot c in
    merge cond
      (up (x when cond))
      (reset_up (c when not cond) (x when not cond))


  In Lustre (thèse de Lélio p.39), it gives :

  node true_until(r: bool) returns (c: bool)
  let
    c = true -> if r then false else (pre c);
  tel

  node reset_f(x: int; r: bool) returns (y: int)
  var c: bool;
  let
    c = true_until(r);
    y = merge c (f(x when c)) (reset_f((x, r) when not c));
  tel
 *)


(* en Vélus ?? :

   c = if r then false else (true fby c)

   ou bien, pour faire le même premier instant que LS
   (évite une récurrence instantanée dans le reset)

   c = true -> if r then false else (true fby c)

   mieux :
   c = true -> not r and (true fby c)
 *)

Arguments PROJ {I Di}.
Arguments FST {D1 D2}.
Arguments SND {D1 D2}.
Arguments curry {D1 D2 D3}.

Local Hint Rewrite
  curry_Curry Curry_simpl fcont_comp_simpl fcont_comp2_simpl fcont_comp3_simpl
  FST_simpl Fst_simpl SND_simpl Snd_simpl AP_simpl
  : localdb.


Definition DSForall_pres {A} (P : A -> Prop) : DS (sampl A) -> Prop :=
  DSForall (fun s => match s with pres v => P v | _ => True end).

Definition safe_DS {A} : DS (sampl A) -> Prop :=
  DSForall (fun v => match v with err _ => False | _ => True end).

(* when booléen *)
Definition when :  forall {A}, DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A) :=
  fun _ => ZIP (fun c x => match c, x with
      | abs, abs => abs
      | pres true, pres v => (pres v)
      | pres false, pres v => abs
      | _, _ => err error_Cl
      end).

Lemma when_eq :
  forall A c cs x xs,
    @when A (cons c cs) (cons x xs) ==
      match c, x with
      | abs, abs => cons abs (when cs xs)
      | pres true, pres v => cons (pres v) (when cs xs)
      | pres false, pres v => cons abs (when cs xs)
      | _, _ => cons (err error_Cl) (when cs xs)
      end.
Proof.
  intros.
  unfold when at 1.
  rewrite zip_cons.
  destruct c as [|[]|], x; auto.
Qed.

Lemma take_when :
  forall A n cs xs,
    take n (@when A cs xs) == when (take n cs) (take n xs).
Proof.
  intros; unfold when; apply take_zip.
Qed.

Lemma rem_when :
  forall A cs (xs:DS (sampl A)),
    rem (when cs xs) == when (rem cs) (rem xs).
Proof.
  intros.
  unfold when.
  apply rem_zip.
Qed.

Lemma nrem_when :
  forall A n cs (xs:DS (sampl A)),
    nrem n (when cs xs) == when (nrem n cs) (nrem n xs).
Proof.
  intros; unfold when.
  apply nrem_zip.
Qed.

Lemma when_true :
  forall A cs (xs:DS (sampl A)),
    safe_DS cs ->
    safe_DS xs ->
    AC cs == AC xs ->
    DSForall_pres (fun b => b = true) cs ->
    when cs xs == xs.
Proof.
  intros * Sc Sx Hac Ht.
  apply DS_bisimulation_allin1 with
    (R := fun U V => exists cs,
              AC cs == AC V
              /\ safe_DS cs
              /\ safe_DS V
              /\ DSForall_pres (fun b => b = true) cs
              /\ U == when cs V).
  3:eauto 8.
  clear; intros * ? Eq1 Eq2; now (setoid_rewrite <- Eq1; setoid_rewrite <- Eq2).
  clear; intros U V Hc (cs & Hac & Sc & Sv & Hf & Hu).
  destruct (@is_cons_elim _ cs) as (c & cs' & Hcs).
  { destruct Hc.
    unfold when in *; eapply proj1, zip_is_cons; now rewrite <- Hu.
    now eapply AC_is_cons; rewrite Hac; apply AC_is_cons. }
  destruct (@is_cons_elim _ V) as (v & V' & Hv).
  { now eapply AC_is_cons; rewrite <- Hac; apply AC_is_cons; rewrite Hcs. }
  rewrite Hv, Hcs, 2 AC_cons, when_eq, Hu in *.
  inversion_clear Hf.
  inversion_clear Sc.
  inversion_clear Sv.
  apply Con_eq_simpl in Hac as []; subst.
  split.
  - destruct c as [|[]|], v; try (tauto || congruence); rewrite first_cons; auto.
  - exists cs'.
    rewrite Hv, Hu, rem_cons.
    destruct c as [|[]|], v; try (tauto || congruence); rewrite rem_cons; auto.
Qed.

Lemma when_false :
  forall A cs (xs:DS (sampl A)),
    safe_DS cs ->
    safe_DS xs ->
    AC cs == AC xs ->
    DSForall_pres (fun b => b = false) cs ->
    when cs xs == map (fun _ => abs) cs.
Proof.
  intros * Sc Sx Hac Ht.
  apply DS_bisimulation_allin1 with
    (R := fun U V => exists cs xs,
              AC cs == AC xs
              /\ safe_DS cs
              /\ safe_DS xs
              /\ DSForall_pres (fun b => b = false) cs
              /\ U == when cs xs
              /\ V == map (fun _ => abs) cs
    ).
  3:eauto 8.
  clear; intros * ? Eq1 Eq2; now (setoid_rewrite <- Eq1; setoid_rewrite <- Eq2).
  clear; intros U V Hc (cs & xs & Hac & Sc & Sx & Hf & Hu & Hv).
  destruct (@is_cons_elim _ cs) as (c & cs' & Hcs).
  { destruct Hc.
    unfold when in *; eapply proj1, zip_is_cons; now rewrite <- Hu.
    eapply map_is_cons; rewrite <- Hv; auto. }
  destruct (@is_cons_elim _ xs) as (x & xs' & Hxs).
  { now eapply AC_is_cons; rewrite <- Hac; apply AC_is_cons; rewrite Hcs. }
  rewrite Hcs, Hxs, 2 AC_cons, when_eq, map_eq_cons in *.
  inversion_clear Hf.
  inversion_clear Sc.
  inversion_clear Sx.
  apply Con_eq_simpl in Hac as []; subst.
  split.
  - rewrite Hu, Hv.
    destruct c as [|[]|], x; try (tauto || congruence); rewrite first_cons; auto.
  - exists cs', xs'.
    rewrite Hu, Hv, rem_cons.
    destruct c as [|[]|], x; try (tauto || congruence); rewrite rem_cons; auto 7.
Qed.

Lemma safe_when :
  forall A cs (xs:DS (sampl A)),
    safe_DS cs ->
    safe_DS xs ->
    AC cs == AC xs ->
    safe_DS (when cs xs).
Proof.
  intros * Sc Sx Hac.
  remember_ds (when cs xs) as t.
  revert_all; cofix Cof; intros.
  destruct t.
  { constructor; rewrite <- eqEps in Ht; eapply Cof; eauto. }
  apply symmetry, cons_is_cons in Ht as HH.
  unfold when in HH.
  apply zip_is_cons in HH as [Cc Cx].
  apply is_cons_elim in Cc as (c & cs' & Hc).
  apply is_cons_elim in Cx as (x & cx' & Hx).
  rewrite Hc, Hx, when_eq, 2 AC_cons in *.
  inversion_clear Sc.
  inversion_clear Sx.
  destruct c as [|[]|], x; try (congruence || tauto).
  all: apply Con_eq_simpl in Ht as [], Hac as []; subst; try congruence.
  all: constructor; auto; eapply Cof; eauto.
Qed.

Definition whennot :  forall {A}, DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A) :=
  fun _ => ZIP (fun c x => match c, x with
      | abs, abs => abs
      | pres false, pres v => (pres v)
      | pres true, pres v => abs
      | _, _ => err error_Cl
      end).

Lemma whennot_eq :
  forall A c cs x xs,
    @whennot A (cons c cs) (cons x xs) ==
      match c, x with
      | abs, abs => cons abs (whennot cs xs)
      | pres false, pres v => cons (pres v) (whennot cs xs)
      | pres true, pres v => cons abs (whennot cs xs)
      | _, _ => cons (err error_Cl) (whennot cs xs)
      end.
Proof.
  intros.
  unfold whennot at 1.
  rewrite zip_cons.
  destruct c as [|[]|], x; auto.
Qed.

Lemma whennot_false :
  forall A cs (xs:DS (sampl A)),
    safe_DS cs ->
    safe_DS xs ->
    AC cs == AC xs ->
    DSForall_pres (fun b => b = false) cs ->
    whennot cs xs == xs.
Proof.
  intros * Sc Sx Hac Ht.
  apply DS_bisimulation_allin1 with
    (R := fun U V => exists cs,
              AC cs == AC V
              /\ safe_DS cs
              /\ safe_DS V
              /\ DSForall_pres (fun b => b = false) cs
              /\ U == whennot cs V).
  3:eauto 8.
  clear; intros * ? Eq1 Eq2; now (setoid_rewrite <- Eq1; setoid_rewrite <- Eq2).
  clear; intros U V Hc (cs & Hac & Sc & Sv & Hf & Hu).
  destruct (@is_cons_elim _ cs) as (c & cs' & Hcs).
  { destruct Hc.
    unfold whennot in *; eapply proj1, zip_is_cons; now rewrite <- Hu.
    now eapply AC_is_cons; rewrite Hac; apply AC_is_cons. }
  destruct (@is_cons_elim _ V) as (v & V' & Hv).
  { now eapply AC_is_cons; rewrite <- Hac; apply AC_is_cons; rewrite Hcs. }
  rewrite Hv, Hcs, 2 AC_cons, whennot_eq, Hu in *.
  inversion_clear Hf.
  inversion_clear Sc.
  inversion_clear Sv.
  apply Con_eq_simpl in Hac as []; subst.
  split.
  - destruct c as [|[]|], v; try (tauto || congruence); rewrite first_cons; auto.
  - exists cs'.
    rewrite Hv, Hu, rem_cons.
    destruct c as [|[]|], v; try (tauto || congruence); rewrite rem_cons; auto.
Qed.


(** Arrow operator initialized by a constant *)
Definition arrow {A} (a : A) : DS (sampl A) -C-> DS (sampl A).
  refine (FIXP _ (DSCASE _ _ @_ _)).
  apply ford_fcont_shift; intros [| v | e].
  - (* abs *)
    refine (curry (CONS abs @_ uncurry (AP _ _))).
  - (* pres v *)
    apply CTE, (CONS (pres a)).
  - (* err e *)
    apply CTE, (CONS (err e)).
Defined.

Lemma arrow_eq :
  forall A (a : A) x xs,
    arrow a (cons x xs) ==
      match x with
      | abs => cons abs (arrow a xs)
      | pres _ => cons (pres a) xs
      | err e => cons (err e) xs
      end.
Proof.
  unfold arrow at 1; intros.
  rewrite FIXP_eq, fcont_comp_simpl, DSCASE_simpl, DScase_cons.
  destruct x; auto.
Qed.

Lemma arrow_bot : forall A (a:A), arrow a 0 == 0.
Proof.
  intros; unfold arrow.
  rewrite FIXP_eq.
  apply DScase_bot_eq.
Qed.


(** A special [merge] operator that produces an [abs] as soon as an [abs]
    is read on the condition stream. Trying to read on both arguments when
    expecting absences could lead to causality issues in the recursive
    definition of reset. *)
Section MERGE.

Definition expecta : forall {A}, DS (sampl A) -C-> DS (sampl A) :=
  fun _ => DSCASE _ _ (fun v => match v with
                | abs => ID _
                | pres _ => MAP (fun _ => err error_Cl)
                | err e => MAP (fun _ => err e)
                    end).

Lemma expecta_eq :
  forall A c cs,
    @expecta A (cons c cs) ==
      match c with
      | abs => cs
      | pres _ => map (fun _ => err error_Cl) cs
      | err _ => map (fun _ => c) cs
      end.
Proof.
  intros.
  unfold expecta.
  rewrite DSCASE_simpl, DScase_cons.
  destruct c; reflexivity.
Qed.

Lemma expecta_bot : forall A, @expecta A 0 == 0.
Proof.
  unfold expecta.
  split; auto.
  apply DScase_bot.
Qed.

Definition merge {A} : DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A).
  refine (FIXP _ _).
  apply curry, curry, curry.
  refine ((DSCASE _ _ @2_ _) (SND @_ FST @_ FST)).
  apply ford_fcont_shift; intro c.
  apply curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (f := FST @_ FST @_ FST @_ (@FST pl pr))
      ; pose (X := SND @_ FST @_ (@FST pl pr))
      ; pose (Y := SND @_ (@FST pl pr))
      ; pose (C' := @SND pl pr)
  end.
  destruct c as [|[]| e].
  - (* abs *)
    refine (CONS abs @_ _).
    refine ((f @4_ ID _) C' (expecta @_ X) (expecta @_ Y)).
  - (* pres true *)
    refine ((APP _ @2_ X) _).
    refine ((f @4_ ID _) C' (REM _ @_ X) (expecta @_ Y)).
  - (* pres false *)
    refine ((APP _ @2_ Y) _).
    refine ((f @4_ ID _) C' (expecta @_ X) (REM _ @_ Y)).
  - (* err *)
    refine ((MAP (fun _ => err e) @_ CONS (err e) @_ C')).
Defined.

(* Parameter merge : forall {A}, DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A). *)
(* problèmes :
   - pres T/F ne vérifie pas la présence de tête de xs/ys
   - abs ne propage pas les erreurs de expecta
 *)
Lemma merge_eq :
  forall A c cs xs ys,
    @merge A (cons c cs) xs ys ==
      match c with
      | abs => cons abs (merge cs (expecta xs) (expecta ys))
      | pres true => app xs (merge cs (rem xs) (expecta ys))
      | pres false => app ys (merge cs (expecta xs) (rem ys))
      | err e => map (fun _ => err e) (cons c cs)
      end.
Proof.
  intros.
  unfold merge at 1.
  rewrite FIXP_eq.
  rewrite 3 curry_Curry, 3 Curry_simpl.
  rewrite fcont_comp2_simpl, 2 fcont_comp_simpl.
  rewrite DSCASE_simpl.
  setoid_rewrite DScase_cons.
  destruct c as [|[]|].
(* FIXME: beaucoup trop lent : *)
(*   - apply cons_eq_compat; reflexivity. *)
(*   - apply app_eq_compat; reflexivity. *)
(*   - apply app_eq_compat; reflexivity. *)
(*   - reflexivity. *)
(* Qed. *)
Admitted.

Global Opaque merge.

Lemma expecta_inf :
  forall A (xs:DS (sampl A)),
    infinite xs ->
    infinite (expecta xs).
Proof.
  intros * Infx.
  apply infinite_decomp in Infx as (vx & xs' & Hxs &Infx').
  rewrite Hxs, expecta_eq.
  destruct vx; auto using map_inf.
Qed.

(* merge does not have a lot of good properties, but this is enough *)
Lemma merge_false_merge:
  forall A cs cs2 (xs ys:DS (sampl A)),
    safe_DS cs ->
    safe_DS cs2 ->
    infinite cs ->
    infinite xs ->
    DSForall_pres (fun b => b = false) cs ->
    AC cs == AC cs2 ->
    merge cs (map (fun _ : sampl bool => abs) cs) (merge cs2 xs ys) == merge cs2 xs ys.
Proof.  intros * Sc Sc2 Infc Infx Hf Hac.
  coind_Oeq Cof; intros; constructor; intros Hcons.
  apply infinite_decomp in Infc as (vc & cs' & Hcs &Infc').
  destruct (@is_cons_elim _ cs2) as (vc2 & cs2' & Hcs2).
  { apply AC_is_cons; rewrite <- Hac, Hcs, AC_cons; auto. }
  rewrite Hcs, Hcs2, 2 AC_cons, map_eq_cons in *.
  apply Con_eq_simpl in Hac as [].
  inversion_clear Sc.
  inversion_clear Sc2.
  inversion_clear Hf.
  rewrite merge_eq in HU, HV.
  destruct vc as [|[]|], vc2 as [| [] |]; subst; try (congruence || tauto).
  - (* abs *)
    rewrite expecta_eq in HU.
    split. rewrite HU, HV, 2 first_cons; auto.
    eapply (Cof _ cs' cs2' (expecta xs) (expecta ys)); auto using expecta_inf.
    rewrite HV, rem_cons; reflexivity.
    rewrite HU, HV, 2 rem_cons, expecta_eq; auto.
  - (* vc2=true *)
    rewrite expecta_eq in HU.
    split. rewrite HU, HV, 2 first_app_first; auto.
    apply infinite_decomp in Infx as (vx & xs' & Hxs &Infx').
    rewrite Hxs, app_cons, rem_cons in HV.
    apply (Cof _ cs' cs2' xs' (expecta ys)); auto.
    rewrite HV, rem_cons; auto.
    rewrite HU, HV, app_cons, rem_cons; auto.
  - (* vc2=false *)
    rewrite HV, app_app, expecta_eq in HU.
    destruct (@is_cons_elim _ ys) as (vy & ys' & Hys).
    { rewrite HU, HV in Hcons; destruct Hcons as [Hc|Hc]; eapply app_is_cons, Hc. }
    rewrite Hys, app_cons in HU, HV.
    split. rewrite HU, HV, 2 first_cons; auto.
    apply (Cof _ cs' cs2' (expecta xs) ys'); auto using expecta_inf.
    rewrite HV, 2 rem_cons; auto.
    rewrite HU, HV, app_cons, 3 rem_cons; auto.
Qed.

End MERGE.

(** Definition and characterisations of true_until *)
Section TRUE_UNTIL.

(* c = true -> not r and (true fby c) *)
Definition true_until : DS (sampl bool) -C-> DS (sampl bool).
  refine (FIXP _ _).
  apply curry.
  refine (arrow true @_ _).
  refine ((sbinop (fun b1 b2 => Some (negb b1 && b2)) @2_ SND) _).
  refine ((fby @2_ sconst true @_ AC @_ SND) _).
  refine ((AP _ _ @2_ FST) SND).
Defined.

Lemma true_until_eq :
  forall r, true_until r ==
         arrow true
           (sbinop (fun b1 b2 => Some (negb b1 && b2)) r
              (fby (sconst true (AC r)) (true_until r))).
Proof.
  intros.
  unfold true_until at 1.
  rewrite FIXP_eq.
  reflexivity.
Qed.

Lemma true_until_abs :
  forall r, true_until (cons abs r) == cons abs (true_until r).
Proof.
  intros.
  rewrite true_until_eq at 1.
  rewrite AC_cons, sconst_cons, fby_eq, sbinop_eq, arrow_eq.
  apply cons_eq_compat; auto.
  unfold true_until.
  rewrite FIXP_fixp.
  apply fixp_ind.
  - intros h H.
    do 2 setoid_rewrite <- fmon_comp_simpl.
    setoid_rewrite lub_comp_eq; auto.
    apply lub_eq_compat; auto.
  - unfold sbinop.
    now rewrite fbyA_bot, zip_bot2, arrow_bot.
  - intros ftrue_until Hf.
    change (fcontit ?a ?b) with (a b).
    autorewrite with localdb; simpl.
    rewrite <- Hf.
    rewrite AC_cons, sconst_cons, fby_eq, sbinop_eq, arrow_eq, fbyA_eq.
    reflexivity.
Qed.

(* When a present value [v] is on rs, true_until outputs true,
   whatever the value of v. Then it enters in a state "U". *)
Lemma true_until_pres1 :
  forall b r,
    safe_DS r ->
    exists U,
      true_until (cons (pres b) r) == cons (pres true) U
      /\ U == (sbinop (fun b1 b2 => Some (negb b1 && b2)) r
                (fby1 (Some true) (sconst true (AC r)) U)).
Proof.
  intros * Hr.
  eexists.
  rewrite true_until_eq at 1.
  rewrite AC_cons, sconst_cons, fby_eq, sbinop_eq, arrow_eq.
  split. reflexivity.
  rewrite true_until_eq at 1.
  rewrite AC_cons, sconst_cons, fby_eq, sbinop_eq, arrow_eq.
  rewrite fby1AP_eq.
  reflexivity.
Qed.

(* when a reset has been triggered, the register of fby1 is false *)
Lemma cs_spec1 :
  forall cs rs,
    infinite rs ->
    safe_DS rs ->
    cs == sbinop (fun b1 b2 : bool => Some (negb b1 && b2)) rs
            (fby1 (Some false) (sconst true (AC rs)) cs) ->
    cs == map (fun v : sampl bool => match v with
                               | abs => abs
                               | pres _ => pres false
                               | err e => err e
                               end) rs.
Proof.
  intros * Infr Sr Hcs.
  apply take_Oeq; intro n.
  revert dependent cs.
  revert dependent rs.
  induction n; intros; auto.
  apply infinite_decomp in Infr as (vr & rs' & Hrs & Infr').
  rewrite Hrs in *.
  inversion_clear Sr.
  rewrite AC_cons, sconst_cons, fby1_eq in Hcs.
  destruct vr; try tauto.
  - (* abs *)
    rewrite Hcs, sbinop_eq, map_eq_cons, 2 take_cons.
    apply cons_eq_compat; auto.
    apply IHn; auto.
    now rewrite Hcs, sbinop_eq, fby1AP_eq at 1.
  - (* pres *)
    rewrite Hcs, sbinop_eq, map_eq_cons, 2 take_cons.
    destruct a; apply cons_eq_compat; auto.
    all: apply IHn; auto; now rewrite Hcs, sbinop_eq, fby1AP_eq at 1.
Qed.

Lemma cs_spec :
  forall n cs rs,
    infinite rs ->
    safe_DS rs ->
    cs == sbinop (fun b1 b2 : bool => Some (negb b1 && b2)) rs
            (fby1 (Some true) (sconst true (AC rs)) cs) ->
    exists m, (m <= n)%nat
         /\ take m cs == map (fun v => match v with
                                   | pres _ => pres true
                                   | abs => abs
                                   | err e => err e end) (take m rs)
         /\ take (n - m) (nrem m cs) ==
             map (fun v => match v with
                        | pres _ => pres false
                        | abs => abs
                        | err e => err e end) (take (n - m) (nrem m rs)).
Proof.
  induction n; intros * Infr Sr Hcs.
  { exists O; rewrite 3 take_eq, 2 map_bot; auto. }
  apply infinite_decomp in Infr as (vr & rs' & Hrs &Infr').
  rewrite Hrs in *.
  rewrite AC_cons, sconst_cons, fby1_eq in Hcs.
  inversion_clear Sr.
  destruct vr as [|r|]; try tauto.
  - (* abs *)
    rewrite sbinop_eq in Hcs.
    destruct (IHn (rem cs) (rem rs)) as (m & Hle & Ht1 & Ht2).
    rewrite Hrs, rem_cons; auto.
    rewrite Hrs, rem_cons; auto.
    { rewrite Hcs, Hrs, 2 rem_cons.
      rewrite Hcs at 1.
      now rewrite fby1AP_eq. }
    exists (S m); split; auto with arith.
    replace (S n - S m) with (n - m); auto with arith.
    rewrite Hrs, take_cons, nrem_S, map_eq_cons, nrem_S, rem_cons in *.
    split.
    + rewrite Hcs, take_cons, rem_cons in *; auto.
    + rewrite Hcs, rem_cons in *; auto.
  - (* pres *)
    rewrite sbinop_eq in Hcs.
    destruct r; simpl in Hcs.
    { (* reset *)
      exists O; split; auto with arith.
      rewrite Nat.sub_0_r, 2 (take_eq O), map_bot.
      split; simpl (nrem _ _); auto.
      pose proof (cs_spec1 (rem cs) rs').
      eapply take_morph_Proper with (n := n) in H1; auto.
      + rewrite Hrs, take_cons, map_eq_cons, <- take_map, <- H1.
        now rewrite Hcs, take_cons, rem_cons.
      + rewrite Hcs at 1 2.
        rewrite rem_cons.
        now rewrite Hcs, fby1AP_eq at 1. }
    (* comme dans abs *)
    destruct (IHn (rem cs) (rem rs)) as (m & Hle & Ht1 & Ht2).
    rewrite Hrs, rem_cons; auto.
    rewrite Hrs, rem_cons; auto.
    { rewrite Hcs, Hrs, 2 rem_cons.
      rewrite Hcs at 1.
      now rewrite fby1AP_eq. }
    exists (S m); split; auto with arith.
    replace (S n - S m) with (n - m); auto with arith.
    rewrite Hrs, take_cons, nrem_S, map_eq_cons, nrem_S, rem_cons in *.
    split.
    + rewrite Hcs, take_cons, rem_cons in *; auto.
    + rewrite Hcs, rem_cons in *; auto.
Qed.

(** combining previous lemmas, we get the characterisations of [true_until] *)
Lemma take_true_until_spec :
  forall n rs,
    infinite rs ->
    safe_DS rs ->
    exists m,
      (m <= n)%nat
      /\ take m (true_until rs) ==
          map (fun v => match v with
                     | pres _ => pres true
                     | abs => abs
                     | err e => err e end) (take m rs)
      /\ take (n - m) (nrem m (true_until rs)) ==
          map (fun v => match v with
                     | pres _ => pres false
                     | abs => abs
                     | err e => err e end) (take (n - m) (nrem m rs)).
Proof.
  induction n; intros * Infr Sr.
  exists O; rewrite 4 take_eq, 2 map_bot; auto.
  apply infinite_decomp in Infr as (vr & rs' & Hrs &Infr').
  rewrite Hrs in *.
  inversion_clear Sr.
  destruct vr as [|vr|]; try tauto.
  - (* abs *)
    destruct (IHn rs') as (m & Hlt & Ht1 & Ht2); auto.
    exists (S m).
    rewrite Hrs, true_until_abs, 2 nrem_S, 2 rem_cons, 2 take_cons, map_eq_cons.
    change (S n - S m) with (n - m); auto with arith.
  - (* pres *)
    destruct (true_until_pres1 vr rs') as (cs & Htu & Hc); auto.
    apply (cs_spec n) in Hc as (m & Hlt & Ht1 & Ht2); auto.
    exists (S m).
    rewrite Hrs, Htu, 2 nrem_S, 2 rem_cons, 2 take_cons, map_eq_cons.
    change (S n - S m) with (n - m); auto with arith.
Qed.

(** Other properties of true_until *)

Lemma true_until_is_cons :
  forall rs, is_cons (true_until rs) -> is_cons rs.
Proof.
  intro.
  rewrite true_until_eq.
  unfold arrow.
  rewrite FIXP_eq.
  intros Hc.
  now apply DScase_is_cons, sbinop_is_cons in Hc.
Qed.

Lemma AC_true_until :
  forall rs,
    safe_DS rs ->
    AC rs == AC (true_until rs).
Proof.
  intros * Sr.
  coind_Oeq Cof.
  constructor.
  intros Hc.
  destruct (@is_cons_elim _ rs) as (vr & rs' & Hrs).
  { rewrite HU, HV in Hc; destruct Hc. apply AC_is_cons; auto.
    apply true_until_is_cons, AC_is_cons; auto. }
  clear Hc.
  rewrite Hrs in *.
  inversion_clear Sr.
  destruct vr as [|vr|]; try tauto.
  { (* abs *)
    rewrite true_until_abs, AC_cons in *.
    split.
    rewrite HU, HV, 2 first_cons; auto.
    apply (Cof (rs')); rewrite ?HU, ?HV, ?rem_cons; auto. }
  clear Cof.
  (* on revient à l'induction *)
  enough (HH : U == V). { rewrite HH at 1; split; auto using Oeq_ds_eq. }
  rewrite HU,HV.
  destruct (true_until_pres1 vr rs') as (cs & Htu & Hcs); auto.
  rewrite Htu, 2 AC_cons.
  apply cons_eq_compat; auto.
  clear H Htu HU HV Hrs; clear U V vr rs.
  rename rs' into rs.
  revert Hcs; generalize (true) at 1; intros b Hcs.
  coind_Oeq Cof.
  constructor.
  intros Hc.
  destruct (@is_cons_elim _ rs) as (vr & rs' & Hrs).
  { rewrite HU, HV in Hc; destruct Hc. apply AC_is_cons; auto.
    apply AC_is_cons in H; rewrite Hcs in H; apply sbinop_is_cons in H; tauto. }
  clear Hc.
  rewrite Hrs in *.
  inversion_clear H0.
  rewrite HU, AC_cons, sconst_cons in Hcs.
  destruct vr as [|vr|]; try tauto.
  { (* abs *)
    rewrite fby1_eq, sbinop_eq in Hcs.
    split.
    rewrite HU, HV, Hcs, 2 AC_cons, first_cons; auto.
    eapply (Cof rs') with (cs := rem cs);
      rewrite ?HU, ?HV, ?rem_AC, ?rem_cons; auto.
    rewrite Hcs, rem_cons.
    rewrite Hcs at 1.
    now rewrite fby1AP_eq. }
  { (* pres *)
    rewrite fby1_eq, sbinop_eq in Hcs.
    split.
    rewrite HU, HV, Hcs, 2 AC_cons, first_cons; auto.
    eapply (Cof rs') with (cs := rem cs);
      rewrite ?HU, ?HV, ?rem_AC, ?rem_cons; auto.
    rewrite Hcs, rem_cons.
    rewrite Hcs at 1.
    now rewrite fby1AP_eq. }
Qed.

(* FIXME: en principe, pas besoin de [safe_DS rs] mais
   je n'ai pas envie de tout me retaper *)
Corollary true_until_inf :
  forall rs,
    safe_DS rs ->
    infinite rs ->
    infinite (true_until rs).
Proof.
  intros * Sr Infr.
  pose proof (Hac := AC_true_until rs Sr).
  unfold AC in *.
  rewrite 2 MAP_map in Hac.
  eapply inf_map; rewrite <- Hac.
  apply map_inf, Infr.
Qed.

Lemma safe_true_until :
  forall rs,
    safe_DS rs ->
    safe_DS (true_until rs).
Proof.
  intros * Sr.
  remember_ds (true_until rs) as t.
  revert_all; cofix Cof; intros.
  destruct t.
  { rewrite <- eqEps in Ht.
    constructor; eapply Cof; eauto. }
  destruct (@is_cons_elim _ rs) as (vr & rs' & Hrs).
  { apply true_until_is_cons; now rewrite <- Ht. }
  rewrite Hrs in *.
  inversion_clear Sr.
  destruct vr as [|vr|]; try tauto.
  { (* abs *)
    rewrite true_until_abs in Ht.
    apply Con_eq_simpl in Ht as []; subst.
    constructor; auto; eapply Cof; eauto. }
  (* pres : on recommence une induction *)
  clear Cof H.
  destruct (true_until_pres1 vr rs') as (cs & Htu & Hcs); auto.
  rewrite Ht, Htu; constructor; auto.
  clear - H0 Hcs.
  rename rs' into rs.
  revert Hcs; generalize true at 1; intros.
  revert_all; cofix Cof; intros.
  destruct cs.
  { rewrite <- eqEps in Hcs.
    constructor; eapply Cof; eauto. }
  destruct (@is_cons_elim _ rs) as (vr & rs' & Hrs).
  { eapply proj1, sbinop_is_cons; rewrite <- Hcs; auto. }
  rewrite Hrs, AC_cons, sconst_cons in *.
  inversion_clear H0.
  destruct vr; try tauto.
  { (* abs *)
    rewrite fby1_eq, sbinop_eq in Hcs.
    apply Con_eq_simpl in Hcs as [? Hcs]; subst.
    constructor; auto.
    eapply (Cof rs'); auto.
    rewrite Hcs.
    rewrite Hcs at 1.
    now rewrite fby1AP_eq. }
  { (* pres *)
    rewrite fby1_eq, sbinop_eq in Hcs.
    apply Con_eq_simpl in Hcs as [? Hcs]; subst.
    constructor; auto.
    eapply (Cof rs'); auto.
    rewrite Hcs.
    rewrite Hcs at 1.
    now rewrite fby1AP_eq. }
Qed.

End TRUE_UNTIL.


Section RESET.
(** Definition of the recursive reset operator, using true_until *)

Context {A : Type}.
Variable (f : DS (sampl A) -C-> DS (sampl A)).

Definition reset : DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A).
  refine (FIXP _ _).
  apply curry, curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (freset := FST @_ @FST pl pr)
      ; pose (r := SND @_ @FST pl pr)
      ; pose (x := @SND pl pr)
      ; pose (c := true_until @_ r)
  end.
  refine ((merge @3_ c) _ _).
  - (* true *)
    refine (f @_ (when @2_ c) x).
  - (* false *)
    refine ((AP _ _ @3_ freset)
              ((whennot @2_ c) r)
              ((whennot @2_ c) x)).
Defined.

Lemma reset_eq :
  forall r x,
    reset r x ==
      let c := true_until r in
      merge c (f (when c x))
              (reset (whennot c r) (whennot c x)).
Proof.
  intros.
  unfold reset at 1.
  rewrite FIXP_eq.
  reflexivity.
Qed.

End RESET.

(** simplified version of the denotational [sreset] (no environnements) *)
Section SRESET.

Parameter sreset' : forall {A}, (DS A -C-> DS A) -C-> DS bool -C-> DS A -C-> DS A -C-> DS A.
Conjecture sreset'_eq : forall A f r R X Y,
    @sreset' A f (cons r R) X Y ==
      if r
      then sreset' f (cons false R) X (f X)
      else app Y (sreset' f R (rem X) (rem Y)).

Definition sreset {A} : (DS A -C-> DS A) -C-> DS bool -C-> DS A -C-> DS A.
  apply curry, curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (f := FST @_ (@FST pl pr));
      pose (R := SND @_ (@FST pl pr));
      pose (X := @SND pl pr);
      idtac
  end.
  exact ((sreset' @4_ f) R X ((AP _ _ @2_ f) X)).
Defined.

Lemma sreset_eq : forall A f R X,
    @sreset A f R X == sreset' f R X (f X).
Proof.
  trivial.
Qed.

End SRESET.

(* We prove a simplified form, with a function of a single stream *)
Module RESET_OK.

Parameter (A : Type).
Parameter (f : DS (sampl A) -C-> DS (sampl A)).

Conjecture AbsF : forall xs, f (cons abs xs) == cons abs (f xs).

Corollary AbsConstF : f (DS_const abs) == DS_const abs.
Proof.
  apply take_Oeq.
  induction n; auto.
  rewrite DS_const_eq, AbsF, 2 (take_eq (S n)), 2 app_cons, 2 rem_cons.
  now rewrite IHn.
Qed.

Conjecture LpF : forall xs n, f (take n xs) == take n (f xs).

Conjecture SafeF : forall xs, safe_DS xs -> safe_DS (f xs).

(** we only consider functions of clock α → α *)
Conjecture AcF : forall xs, AC xs == AC (f xs).

Corollary InfF : forall xs, infinite xs -> infinite (f xs).
Proof.
  intros * Hinf.
  pose proof (HH := AcF xs); unfold AC in *.
  eapply inf_map.
  rewrite <- MAP_map, <- HH.
  apply map_inf, Hinf.
Qed.

Corollary AlignF :
  forall n xs,
    safe_DS xs ->
    first (nrem n xs) == cons abs 0 ->
    first (nrem n (f xs)) == cons abs 0.
Proof.
  intros * Sx Hf.
  pose proof (St := SafeF xs Sx).
  pose proof (Hac := AcF xs); revert St Hac; generalize (f xs); intros.
  revert dependent t.
  revert dependent xs.
  induction n; simpl (nrem _ _); intros.
  - destruct (@is_cons_elim _ xs) as (vx & xs' & Hxs).
    { apply first_is_cons; rewrite Hf; auto. }
    destruct (@is_cons_elim _ t) as (vt & t' & Ht).
    { apply AC_is_cons; rewrite <- Hac, Hxs, AC_cons; auto. }
    rewrite Hxs, Ht, 2 AC_cons, first_cons in *.
    inversion_clear St.
    apply Con_eq_simpl in Hf as [], Hac as []; subst.
    destruct vt; try (congruence|| tauto); auto.
  - apply rem_eq_compat in Hac.
    rewrite 2 rem_AC in Hac.
    apply DSForall_rem in Sx, St.
    rewrite (IHn (rem xs)); auto.
Qed.

Corollary AlignF_take :
  forall xs n m,
    safe_DS xs ->
    take m (nrem n xs) == take m (DS_const abs) ->
    take m (nrem n (f xs)) == take m (DS_const abs).
Proof.
  intros xs n m.
  revert xs n.
  induction m; intros * Sx Ht; auto.
  rewrite DS_const_eq in Ht|-*.
  rewrite 2 (take_eq (S m)), rem_cons, app_cons in *.
  destruct (@is_cons_elim _ (nrem n xs)) as (?&?& HH).
  { eapply app_is_cons; rewrite Ht; auto. }
  rewrite HH, app_cons, rem_cons in *.
  apply Con_eq_simpl in Ht as []; subst.
  rewrite <- app_app_first, AlignF, app_cons; auto.
  2: rewrite HH, first_cons; auto.
  rewrite <- nrem_rem, <- nrem_S, <- IHm; eauto 1.
  now rewrite nrem_S, nrem_rem, HH, rem_cons.
Qed.

Lemma f_cons_elim :
  forall x xs,
  exists y ys',
    f (cons (pres x) xs) == cons (pres y) ys'.
Proof.
  intros.
  pose proof (Hac := AcF (cons (pres x) xs)).
  destruct (@is_cons_elim _ (f (cons (pres x) xs))) as (u & U' & Hu).
  { apply AC_is_cons; rewrite <- Hac, AC_cons; auto. }
  rewrite Hu, 2 AC_cons in Hac.
  apply Con_eq_simpl in Hac as [].
  destruct u as [|u|]; try congruence.
  exists u,U'; auto.
Qed.

Lemma reset_abs :
  forall r x,
    reset f (cons abs r) (cons abs x) == cons abs (reset f r x).
Proof.
  intros.
  rewrite 2 reset_eq; cbv zeta.
  rewrite true_until_abs, when_eq, 2 whennot_eq, AbsF.
  rewrite merge_eq, expecta_eq.
  apply cons_eq_compat; auto.
  apply fcont_stable.
  unfold reset.
  rewrite FIXP_fixp.
  revert r x; apply fixp_ind.
  - intros h H r x.
    setoid_rewrite <- fmon_comp_simpl.
    setoid_rewrite lub_comp_eq at 1; auto.
    apply lub_eq_compat.
    apply ford_eq_intro; intro n.
    repeat rewrite ?fmon_comp_simpl, ?fmon_app_simpl.
    apply H.
  - intros.
    unfold expecta.
    rewrite DSCASE_simpl, DScase_bot_eq.
    auto.
  - intros freset Hf r x.
    change (fcontit ?a ?b) with (a b).
    autorewrite with localdb; simpl.
    rewrite true_until_abs, when_eq, 2 whennot_eq, AbsF, merge_eq, 2 expecta_eq.
    rewrite Hf; auto.
Qed.

(** Key lemma to prove the equivalence of resets *)
Lemma f_when :
  forall rs xs,
    infinite rs ->
    infinite xs ->
    safe_DS rs ->
    safe_DS xs ->
    AC xs == AC rs ->
    f (when (true_until rs) xs) == when (true_until rs) (f xs).
Proof.
  intros * Infr Infx Sr Sx Hac.
  apply take_Oeq; intro n.
  destruct (take_true_until_spec n rs) as (m & Hlt & Ht1 & Ht2); auto.
  replace n with (m + (n - m)); auto with arith.
  apply take_nrem_eq.
  - (* partie true *)
    clear Hlt Ht2.
    rewrite <- LpF, 2 take_when, Ht1.
    rewrite <- take_map, <- 2 take_when.
    rewrite 2 when_true, LpF; auto using SafeF.
    all: try (eapply DSForall_map, DSForall_impl, Sr; simpl; intros []; tauto).
    unfold AC in *; rewrite <- AcF, Hac, 2 MAP_map, map_comp; apply map_ext; intros []; auto.
    unfold AC in *; rewrite Hac, 2 MAP_map, map_comp; apply map_ext; intros []; auto.
  - (* partie false *)
    clear Ht1.
    apply Lt.le_lt_or_eq_stt in Hlt as [Hlt|]; subst.
    2: now rewrite Nat.sub_diag.
    rewrite nrem_when, take_when, Ht2.
    rewrite (when_false _ (map _ _)), map_comp, <- take_map; cycle 1.
    all: try (eapply DSForall_map, DSForall_take, DSForall_nrem, DSForall_impl, Sr; intros []; tauto).
    eapply DSForall_take, DSForall_nrem, SafeF, DSForall_impl, Sx; intros []; tauto.
    {
      unfold AC in *.
      rewrite 2 MAP_map, map_comp, <- 2 take_map, <- 2 nrem_map, <- (AcF xs), Hac, 2 nrem_map, 2 take_map in *.
      apply map_ext; intros []; auto.
    }
    assert (take (n - m) (map (fun _ : sampl bool => (abs:sampl A)) (nrem m rs)) ==
              take (n - m) (DS_const abs)) as Habs.
    {assert (Infn : infinite (nrem m rs)) by (apply nrem_infinite; auto).
      revert Infn; generalize (nrem m rs).
      clear; induction (n - m); intros ? [? (? & Ht & ?)]%infinite_decomp; auto.
      rewrite Ht, DS_const_eq, 2 (take_eq (S _)), map_eq_cons, 2 rem_cons, 2 app_cons; auto. }
    rewrite AlignF_take; auto.
    { apply safe_when; auto using safe_true_until.
      rewrite <- AC_true_until, Hac; auto. }
    rewrite nrem_when, take_when, Ht2, when_false, map_comp, <- take_map; auto.
    all: try (eapply DSForall_map, DSForall_take, DSForall_nrem, DSForall_impl, Sr; intros []; tauto).
    eapply DSForall_take, DSForall_nrem, DSForall_impl, Sx; intros []; tauto.
    unfold AC in *.
    rewrite 2 MAP_map, map_comp, <- 2 take_map, <- 2 nrem_map, Hac, 2 nrem_map, 2 take_map in *.
    apply map_ext; intros []; auto.
Qed.


Definition bool_of : sampl bool -> bool :=
  fun v => match v with pres true => true | _ => false end.

(* reset match in auxiliary state *)
Lemma sreset_match_aux :
  forall rs xs cs ys,
    infinite rs ->
    infinite xs ->
    infinite ys ->
    safe_DS rs ->
    safe_DS xs ->
    safe_DS ys ->
    AC xs == AC rs ->
    AC xs == AC ys ->
    cs == sbinop (fun b1 b2 : bool => Some (negb b1 && b2)) rs
            (fby1 (Some true) (sconst true (AC rs)) cs) ->
    merge cs (when cs ys) (reset f (whennot cs rs) (whennot cs xs))
    == sreset' f (map bool_of rs) xs ys.
Proof.
  intros * Infr Infx Infy Sr Sx Sy Hac Acy Hcs.
  coind_Oeq Cof.
  constructor; intros _.
  assert (Infr2 := Infr). assert (Infx2 := Infx). assert (Infy2 := Infy).
  apply infinite_decomp in Infr2 as (vr & rs' & Hrs &Infr').
  apply infinite_decomp in Infx2 as (vx & xs' & Hxs &Infx').
  apply infinite_decomp in Infy2 as (vy & ys' & Hys &Infy').
  rewrite Hrs, Hxs, Hys in *.
  repeat rewrite AC_cons in *.
  rewrite map_eq_cons in HV.
  apply Con_eq_simpl in Hac as [], Acy as [].
  assert (Sr2 := Sr). assert (Sx2 := Sx). assert (Sy2 := Sy).
  inversion_clear Sr2 as [|??? Sr']; inversion_clear Sx2; inversion_clear Sy2; subst.
  rewrite sreset'_eq, rem_cons in HV.
  destruct vr as [|vr|], vx, vy; simpl in HV; try (tauto || congruence).
  { (* abs *)
    rewrite app_cons, rem_cons in HV.
    rewrite sconst_cons, fby1_eq, sbinop_eq in Hcs.
    rewrite Hcs, 2 whennot_eq,merge_eq, reset_abs, when_eq, 2 expecta_eq in HU.
    split. rewrite HU, HV, 2 first_cons; auto.
    apply (Cof rs' xs' (rem cs) ys'); auto.
    + rewrite Hcs, rem_cons.
      rewrite Hcs at 1.
      now rewrite fby1AP_eq.
    + rewrite Hcs, HU, 2 rem_cons; reflexivity.
    + rewrite HV, rem_cons; reflexivity. }
  (* pres vr *)
  rewrite sconst_cons, fby1_eq, sbinop_eq in Hcs.
  destruct vr; simpl in Hcs; cycle 1.
  - (* vr = false *)
    rewrite app_cons, rem_cons in HV.
    rewrite Hcs, 2 whennot_eq,merge_eq, reset_abs, when_eq, expecta_eq in HU.
    rewrite app_cons, rem_cons in HU.
    split. rewrite HU, HV, 2 first_cons; reflexivity.
    apply (Cof rs' xs' (rem cs) ys'); auto.
    + rewrite Hcs, rem_cons.
      rewrite Hcs at 1.
      now rewrite fby1AP_eq.
    + rewrite Hcs, HU, 2 rem_cons; reflexivity.
    + rewrite HV, rem_cons; reflexivity.
  - (* vr = true, seul cas vraiment intéressant, on passe dans l'instance d'après *)
    rewrite sreset'_eq, rem_cons in HV.
    (* on refait toutes les propriétés cassées au dessus... *)
    rewrite <- Hxs, <- Hys, <- Hrs in *.
    assert (Hac : AC xs == AC rs).
    { now rewrite Hxs, Hrs, 2 AC_cons, H0. }
    assert (Acy : AC xs == AC ys).
    { now rewrite Hxs, Hys, 2 AC_cons, H2. }
    assert (Hcs2 : cs == sbinop (fun b1 b2 : bool => Some (negb b1 && b2)) rs (fby1 (Some false) (sconst true (AC rs)) cs)).
    { rewrite Hrs, AC_cons, sconst_cons, fby1_eq, sbinop_eq; simpl; now auto. }
    apply (cs_spec1 cs rs) in Sr as Hcs3; auto.
    assert (CsF : DSForall_pres (fun b => b = false) cs).
    { rewrite Hcs3; eapply DSForall_map, DSForall_impl, Sr; intros []; tauto. }
    assert (Acc : AC cs == AC xs).
    { unfold AC in *.
      rewrite Hcs3, Hac, 2 MAP_map, map_comp.
      apply map_ext; intros []; tauto. }
    assert (Sc : safe_DS cs).
    { rewrite Hcs3; eapply DSForall_map, DSForall_impl, Sr; intros []; tauto. }
    assert (Infc : infinite cs).
    { rewrite Hcs3; eapply map_inf, Infr. }

    rewrite when_false, 2 whennot_false in HU; eauto 2.
    rewrite reset_eq in HU; simpl in HU.
    rewrite merge_false_merge, f_when in HU; eauto 4 using safe_true_until, AC_true_until.
    2: unfold when; apply InfF, zip_inf; auto using true_until_inf.

    destruct (f_cons_elim a xs') as (?& rfx & Hfa).
    destruct (true_until_pres1 true rs') as (cs' & Htu & Hcs'); auto.
    rewrite Hrs, Htu, Hxs, 2 whennot_eq, reset_abs, merge_eq, expecta_eq, Hfa in HU.
    rewrite Hxs, Hfa in HV.
    split. rewrite HU, HV, 2 first_app_first, when_eq, 2 first_cons; auto.
    apply (Cof rs' xs' cs' (rem (f xs))); auto.
    + apply InfF; auto.
    + apply DSForall_rem, SafeF, Sx.
    + pose proof (Acf := rem_eq_compat (AcF xs)).
      rewrite Hxs, 2 rem_AC, rem_cons in Acf at 1; auto.
    + rewrite Hxs, Hfa, HU, when_eq, app_cons, 3 rem_cons; auto.
    + rewrite Hxs, Hfa, HV, app_cons, rem_cons; auto.
Qed.

Theorem reset_match :
  forall rs xs,
    infinite rs ->
    infinite xs ->
    safe_DS rs ->
    safe_DS xs ->
    AC xs == AC rs ->
    let rsb := map bool_of rs in
    reset f rs xs == sreset f rsb xs.
Proof.
  intros * Infr Infx Sr Sx Hac rsb; subst rsb.
  rewrite sreset_eq.
  rewrite reset_eq; cbv zeta.
  rewrite f_when; auto.
  pose proof (Sy := SafeF xs Sx); revert Sy.
  pose proof (Acy := AcF xs); revert Acy.
  pose proof (Infy := InfF xs Infx); revert Infy.
  intros.
  (* on commence par laisser passer les absences *)
  coind_Oeq Cof.
  constructor; intros _.
  apply infinite_decomp in Infr as (vr & rs' & Hrs &Infr').
  apply infinite_decomp in Infx as (vx & xs' & Hxs &Infx').
  apply infinite_decomp in Infy as (vy & ys' & Hys &Infy').
  rewrite Hrs, Hxs, Hys in *.
  repeat rewrite AC_cons in *.
  rewrite map_eq_cons in HV.
  apply Con_eq_simpl in Hac as [], Acy as [].
  inversion_clear Sr; inversion_clear Sx; inversion_clear Sy.
  rewrite sreset'_eq, 2 rem_cons in HV.
  destruct vr as [|vr|], vx, vy; simpl in HV; try (tauto || congruence).
  { (* abs : co-induction *)
    rewrite AbsF in Hys.
    apply Con_eq_simpl in Hys as [_ Hys'].
    rewrite true_until_abs, 2 whennot_eq,merge_eq, reset_abs,
      when_eq, 2 expecta_eq in HU.
    rewrite app_cons in HV.
    split. rewrite HU, HV, 2 first_cons; auto.
    apply (Cof rs' xs'); rewrite ?HU, ?HV, <- ?Hys', ?rem_cons, ?AbsF;
      auto using InfF, AcF, SafeF.
  } clear Cof.
  (* on se débarasse maintenant de true_until pour passer dans l'état récurrent *)
  destruct (true_until_pres1 vr rs') as (cs' & Htu & Hcs'); auto.
  rewrite Htu in HU; clear Htu.
  rewrite when_eq, 2 whennot_eq, reset_abs, merge_eq, expecta_eq, rem_cons, app_cons in HU.
  split.
  { rewrite HU, HV, first_cons; destruct vr.
    rewrite sreset'_eq, first_app_first, Hys, first_cons; auto.
    rewrite app_cons, first_cons; auto. }
  (* ce que l'on cherche vraiment à prouver *)
  enough (Heq :
           merge cs' (when cs' ys') (reset f (whennot cs' rs') (whennot cs' xs'))
           == sreset' f (map bool_of rs') xs' ys').
  { apply Oeq_ds_eq.
    rewrite HU, rem_cons.
    rewrite HV; destruct vr.
    rewrite sreset'_eq, Hys, 2 rem_cons, rem_app; auto.
    rewrite app_cons, rem_cons; auto. }
  apply sreset_match_aux; auto.
Qed.

End RESET_OK.
