Require Import List.
Require Import Cpo Reset SDfuns CommonDS.
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

(* TODO: move *)
Lemma inf_map :
  forall A B (f : A -> B) xs,
    infinite (Cpo_streams_type.map f xs) ->
    infinite xs.
Proof.
  cofix Cof; intros * Hf.
  inversion_clear Hf; rewrite rem_map in *.
  constructor; eauto using map_is_cons.
Qed.


(* TODO: move *)
Definition DSForall_pres {A} (P : A -> Prop) : DS (sampl A) -> Prop :=
  DSForall (fun s => match s with pres v => P v | _ => True end).
(* TODO: move *)
Lemma DSForall_take {A} (P : A -> Prop) :
  forall n xs,
  DSForall P xs ->
  DSForall P (take n xs).
Proof.
  induction n; intros * Hf; rewrite take_eq.
  apply DSForall_bot.
  apply DSForall_app; auto using DSForall_rem.
Qed.

Lemma nrem_nrem :
  forall A n1 n2 (xs:DS A), nrem n1 (nrem n2 xs) == nrem (n1 + n2) xs.
Proof.
  induction n1; simpl in *; intros; auto.
  now rewrite nrem_rem, IHn1, nrem_rem.
Qed.

Lemma nrem_infinite :
  forall A n (xs:DS A), infinite xs -> infinite (nrem n xs).
Proof.
  induction n; simpl; intros * H; inversion H; auto.
Qed.

Lemma DSForall_nrem :
  forall A (P:A-> Prop),
  forall s n, DSForall P s -> DSForall P (nrem n s).
Proof.
  induction n; intros; auto.
  rewrite nrem_S, nrem_rem.
  apply DSForall_rem; auto.
Qed.

(* TODO: move *)
Lemma sconst_cons :
    forall A (c:A) b bs,
      sconst c (cons b bs) == cons (if b then pres c else abs) (sconst c bs).
Proof.
  intros.
  apply map_eq_cons.
Qed.

Lemma nrem_zip :
  forall A B C (op :A->B->C),
    forall n xs ys,
      nrem n (ZIP op xs ys) == ZIP op (nrem n xs) (nrem n ys).
Proof.
  induction n; intros; auto.
  now rewrite 3 nrem_S, rem_zip, IHn.
Qed.

(* TODO: move *)
(* TODO: useless? *)
Lemma nrem_Oeq :
  forall A (xs ys:DS A),
    (forall n, first (nrem n xs) == first (nrem n ys)) ->
    xs == ys.
Proof.
  intros * Hf.
  eapply DS_bisimulation_allin1 with
    (R := fun U V => forall n, first (nrem n U) == first (nrem n V)); auto.
  intros * ? Eq1 Eq2; setoid_rewrite <- Eq1; setoid_rewrite <- Eq2; eauto.
  clear; intros U V Hc Hf.
  split.
  - apply (Hf O).
  - intro n.
  destruct (@is_cons_elim _ U) as (u & U' & Hu).
    { destruct Hc; auto.
      apply first_is_cons.
      rewrite (Hf O).
      now apply is_cons_first. }
    destruct (@is_cons_elim _ V) as (v & V' & Hv).
    { destruct Hc; auto.
      apply first_is_cons.
      rewrite <- (Hf O).
      now apply is_cons_first. }
    specialize (Hf (S n)).
    now rewrite Hu, Hv, 2 nrem_S, 2 rem_cons in *.
Qed.



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

Lemma nrem_when :
  forall A n cs (xs:DS (sampl A)),
    nrem n (when cs xs) == when (nrem n cs) (nrem n xs).
Proof.
  intros.
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


(* flèche avec constante à gauche *)
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

(* prédicat co-inductif, peut-être plus facile à manipuler ?
   équivalent de DS_bisimulation
   TODO: pareil avec firsn, nrem ?
 *)
Section DS_eq.
Variable (B : Type).
CoInductive ds_eq : DS B -> DS B -> Prop :=
| De :
  forall x y,
    (is_cons x \/ is_cons y ->
     first x == first y /\ ds_eq (rem x) (rem y)) ->
      ds_eq x y.

Lemma Oeq_ds_eq : forall x y, x == y -> ds_eq x y.
Proof.
  cofix Cof; intros.
  apply De; auto.
Qed.

Lemma ds_eq_Oeq : forall x y, ds_eq x y -> x == y.
Proof.
  intros.
  apply DS_bisimulation_allin1 with (R := fun U V => exists x y, ds_eq x y /\ U == x /\ V == y).
  - intros * Eq Eq1 Eq2.
    setoid_rewrite <- Eq1.
    setoid_rewrite <- Eq2.
    eauto.
  - clear.
    intros U V Hc (x & y & Eq & Hu & Hv).
    rewrite Hu, Hv in Hc.
    inversion_clear Eq.
    destruct H; auto.
    setoid_rewrite Hu.
    setoid_rewrite Hv.
    split; auto.
    exists (rem x), (rem y); split; auto.
  - eauto.
Qed.

Lemma ds_eq_Oeq_iff : forall x y, ds_eq x y <-> x == y.
Proof.
  split; eauto using ds_eq_Oeq, Oeq_ds_eq.
Qed.
End DS_eq.
Ltac coind_Oeq H :=
  intros
  ; match goal with
      |- ?l == ?r => remember_ds l as U
                   ; remember_ds r as V
    end
  ; apply ds_eq_Oeq
  ; revert_all; cofix H
  ; intros.

(* un principe d'induction n par n *)
Section DSn_eq.
Variable (B : Type).
CoInductive dsn_eq : DS B -> DS B -> Prop :=
| Den :
  forall x y,
    (exists n,
      take (S n) x == take (S n) y
      /\ dsn_eq (nrem (S n) x) (nrem (S n) y)) ->
      dsn_eq x y.

Lemma dsn_rem :
  forall U V, dsn_eq U V -> dsn_eq (rem U) (rem V).
Proof.
  intros * Hn.
  inversion_clear Hn as [?? (n &  Ht & Hdsn) ].
  destruct n; auto.
  apply Den; exists n; split; auto.
  apply take_rem; auto.
Qed.

Lemma Oeq_dsn_eq : forall x y, x == y -> dsn_eq x y.
Proof.
  cofix Cof; intros.
  apply Den; exists O; split.
  now rewrite H.
  simpl; now auto.
Qed.

Lemma dsn_eq_Oeq : forall x y, dsn_eq x y -> x == y.
Proof.
  intros * Hn.
  coind_Oeq Cof.
  constructor; intros Hc; split.
  - inversion_clear Hn as [?? (n & Ht & _) ].
    apply first_eq_compat in Ht.
    rewrite 2 (take_eq (S n)), 2 first_app_first in Ht.
    assumption.
  - apply (Cof (rem x) (rem y)); auto.
    apply dsn_rem; auto.
Qed.

Lemma dsn_eq_Oeq_iff : forall x y, dsn_eq x y <-> x == y.
Proof.
  split; eauto using dsn_eq_Oeq, Oeq_dsn_eq.
Qed.
End DSn_eq.

(* TEST: un merge initialisant *)
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

Parameter merge : forall {A}, DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A).
(* problèmes :
   - pres T/F ne vérifie pas la présence de tête de xs/ys
   - abs ne propage pas les erreurs de expecta
 *)
Conjecture merge_eq :
  forall A c cs xs ys,
    @merge A (cons c cs) xs ys ==
      match c with
      | abs => cons abs (merge cs (expecta xs) (expecta ys))
      | pres true => app xs (merge cs (rem xs) (expecta ys))
      | pres false => app ys (merge cs (expecta xs) (rem ys))
      | err e => map (fun _ => err e) (cons c cs)
      end.

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


(* version avec sreset simplifié : seulement des flots (pas d'environnement *)
Module VERSION3.

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
(* TODO: pas trop fort vis-à-vis des erreurs ??
   TODO: ça implique l'infinité !!!!!!!!!!!!!!!!!!!!!!!
   y en a-t-il vraiment besoin ? Je dirais oui à cause du merge optimise dans reset,
   alors que c'est un [app] dans sreset 
 *)
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

Lemma reset_abs :
  forall r x,
    reset (cons abs r) (cons abs x) == cons abs (reset r x).
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

(* version simplifiée du reset dénotationnel *)
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

    (* @sreset' A f (cons r R) X Y == *)
    (*   if r *)
    (*   then sreset' f (cons false R) X (f X) *)
    (*   else app Y (sreset' f R (rem X) (rem Y)). *)


(* Lemma sreset''_eq : forall A f r R X Y, *)
(*     @sreset' A f (cons r R) X Y == *)
(*       if r *)
(*       then app (f X) (sreset' f R (rem X) (rem (f X))) *)
(*       else app Y (sreset' f R (rem X) (rem Y)). *)

(* TODO: c'est sans doute n'importe quoi *)
Lemma bisim_n : forall D (R: DS D -> DS D -> Prop),
        (forall x1 x2 y1 y2, R x1 y1 -> x1==x2 -> y1==y2 -> R x2 y2)
        -> (forall (x y:DS D), (* (is_cons x \/ is_cons y) -> *)  R x y ->
                         exists n,
                           take (S n) x == take (S n) y /\ R (nrem (S n) x) (nrem (S n) y))
   -> forall x y, R x y -> x == y.
Proof.
  intros * IH Hfr x t Hr.
  idtac
  ; match goal with
      |- ?l == ?r => remember_ds l as U
                   ; remember_ds r as V
    end
  ; apply dsn_eq_Oeq
  ; revert_all; cofix Cof
  ; intros.
  constructor.
  apply Hfr in Hr as (n&Ht & Hr).
  exists n; split; auto.
  eapply Cof; eauto.
Qed.

(* TODO: move *)
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


(* Lemma is_cons_merge : *)
(*   forall A cs (xs ys:DS (sampl A)), *)
(*     is_cons cs -> *)
(*     is_cons (merge cs xs ys). *)
(* Proof. *)
(*   intros * (?&?&->)%is_cons_elim. *)
(*   rewrite merge_eq. *)
(*   destruct x; auto. *)
(*   destruct a; auto. *)
(* Qed. *)

(* Conjecture merge_is_cons : *)
(*   (* forall A cs (xs ys:DS (sampl A)), is_cons (merge cs xs ys) -> is_cons cs. *) *)
(*   forall A cs (xs ys:DS (sampl A)), is_cons (merge cs xs ys) -> is_cons cs. *)

Lemma reset_inf :
  forall rs xs,
    infinite rs ->
    infinite xs ->
    infinite (reset rs xs).
Proof.
  intros * Infr Infx.
  rewrite reset_eq; simpl.
  remember_ds (merge _ _ _) as t.
  revert_all; cofix Cof; intros.
  apply infinite_decomp in Infr as (vr & rs' & Hrs &Infr').
  apply infinite_decomp in Infx as (vx & xs' & Hxs &Infx').
  rewrite Hrs, Hxs in *.
  destruct vr, vx.
  2:{ rewrite true_until_abs in Ht.
      all: rewrite when_eq in Ht.
Abort.

Lemma merge_false :
  forall A cs ( ys:DS (sampl A)),
    infinite cs ->
    safe_DS cs ->
    (* safe_DS xs -> *)
    safe_DS ys ->
    (* AC cs == AC xs -> *)
    DSForall_pres (fun b => b = false) cs ->
    merge cs (map (fun _ : sampl bool => abs) cs) ys == ys.
Proof.
  intros * Infc Sc (* Sx *) Sy Cf.

  apply infinite_decomp in Infc as (vc & cs' & Hcs &Infc').
  rewrite Hcs in *.
  (* TODO: réfléchir ici... *)
  rewrite merge_eq.



  coind_Oeq Cof.
  constructor; intros _.
  apply infinite_decomp in Infc as (vc & cs' & Hcs &Infc').
  rewrite Hcs in *.
  inversion_clear Sc.
  inversion_clear Cf.
  destruct vc; subst; try (tauto || congruence).
  - (* abs *)
    rewrite merge_eq in HU.
    split. rewrite HV, HU, first_cons.
    admit. admit.
  - (* pres *)
    rewrite merge_eq, map_eq_cons, expecta_eq in HU.
    split. now rewrite HU, HV, first_app_first.
    eapply (Cof _ cs' (rem ys)); auto.
    apply DSForall_rem, Sy.
    rewrite HU, rem_app; auto.
Abort.


Theorem reset_match :
  forall rs xs,
    infinite rs ->
    infinite xs ->
    safe_DS rs ->
    safe_DS xs ->
    AC xs == AC rs ->
    let rsb := map bool_of rs in
    reset rs xs == sreset f rsb xs.
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
           merge cs' (when cs' ys') (reset (whennot cs' rs') (whennot cs' xs'))
           == sreset' f (map bool_of rs') xs' ys').
  { apply Oeq_ds_eq.
    rewrite HU, rem_cons.
    rewrite HV; destruct vr.
    rewrite sreset'_eq, Hys, 2 rem_cons, rem_app; auto.
    rewrite app_cons, rem_cons; auto. }

Set Nested Proofs Allowed.



(* TODO: renommer *)
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
    merge cs (when cs ys) (reset (whennot cs rs) (whennot cs xs))
    == sreset' f (map bool_of rs) xs ys.
Proof.
  intros * Infr Infx Infy Sr Sx Sy Hac Acy Hcs.
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
  - (* vr = true, seul cas vraiment intéressant*)
    rewrite sreset'_eq, rem_cons in HV.

    (* assert (Hcs : cs == cons (pres false) (map (fun v : sampl bool => match v with *)
    (*                                         | abs => abs *)
    (*                                         | pres _ => pres false *)
    (*                                         | err e => err e *)
    (*                                         end) rs')). *)
    (*     { rewrite Hccs. *)
    (*       apply cons_eq_compat; auto. *)
    (*       rewrite <- cs_spec1; auto. *)
    (*       now rewrite Hccs, fby1AP_eq at 1. } *)

    (* we know that cs is now false forever *)
    assert (CsF : DSForall_pres (fun b => b = false) cs).
    admit.
    rewrite when_false, 2 whennot_false in HU; auto.
    all: try (constructor; now auto).
    2-7: admit.
    
Qed.

apply sreset_match_aux; auto.
Qed.




Theorem reset_match :
  forall rs xs,
    infinite rs ->
    infinite xs ->
    safe_DS rs ->
    safe_DS xs ->
    AC xs == AC rs ->
    let rsb := map bool_of rs in
    reset rs xs == sreset f rsb xs.
Proof.
  intros * Infr Infx Sr Sx Hac rsb; subst rsb.
  rewrite sreset_eq.

  rewrite reset_eq; cbv zeta.
  rewrite f_when; auto.
  pose proof (Sy := SafeF xs Sx); revert Sy.
  pose proof (Acy := AcF xs); revert Acy.
  pose proof (Infy := InfF xs Infx); revert Infy.
  (* generalize (f xs); intros ys ???. *)
  intros.

  apply DS_bisimulation_allin1 with
    (R := fun U V =>
            exists rs xs cs ys,
             infinite rs
             /\ infinite xs
             /\ infinite ys
             /\ safe_DS rs
             /\ safe_DS xs
             /\ safe_DS ys
             /\ AC xs == AC rs
             /\ AC xs == AC ys
             /\ U == merge cs (when cs ys) (reset (whennot cs rs) (whennot cs xs))
             /\ V == sreset' f (map bool_of rs) xs ys
             /\ ( (* état 1, en attente d'un signal *)
                 (cs == true_until rs /\ ys == f xs)
                 \/
                 (* état 2, signal true reçu *)
                 (cs == (sbinop (fun b1 b2 => Some (negb b1 && b2)) rs
                           (fby1 (Some true) (sconst true (AC rs)) cs))
                  (* /\ ys == ys (* pas besoin ?? *) *)
                 )
               )

    ).
  3: exists rs,xs,(true_until rs),(f xs); auto 14.
  clear; intros * ? Eq1 Eq2; now (setoid_rewrite <- Eq1; setoid_rewrite <- Eq2).
  clear.
  intros U V Hc (rs & xs & cs & ys & Infr & Infx & Infy & Sr & Sx & Sy & Hac & Acy & Hu & Hv & HH).

  apply infinite_decomp in Infr as (vr & rs' & Hrs &Infr').
  apply infinite_decomp in Infx as (vx & xs' & Hxs &Infx').
  apply infinite_decomp in Infy as (vy & ys' & Hys &Infy').
  rewrite Hrs, Hxs, Hys in *.
  repeat rewrite AC_cons in *.
  rewrite map_eq_cons in Hv.
  apply Con_eq_simpl in Hac as [], Acy as [].
  inversion_clear Sr; inversion_clear Sx; inversion_clear Sy.
  rewrite sreset'_eq, rem_cons in Hv.
  destruct vr as [|vr|], vx, vy; simpl in Hv; try (tauto || congruence)
  ; cycle 1.
  - (* cas present *)
    rewrite sconst_cons, fby1_eq, sbinop_eq in HH.
    destruct vr; simpl (pres _) in *.
    + (* signal reçu : on va toujours dans l'état 2??????? *)
      rewrite sreset'_eq, rem_cons in Hv.
      destruct HH as [(Hccs& Hfy)|Hccs].
      * (* on était dans l'état 1 *)
        destruct (true_until_pres1 true rs') as (cs' & Htu & Hcs'); auto.
        rewrite Hccs, Htu, when_eq, 2 whennot_eq, reset_abs, merge_eq, expecta_eq, rem_cons, app_cons in Hu.
        rewrite <- Hfy, app_cons, rem_cons in Hv.
        split. now rewrite Hu, Hv, 2 first_cons.
        exists rs',xs',cs',ys'; do 8 (split; auto).
        rewrite Hu, Hv, 2 rem_cons; auto.
      * (* on était dans l'état 2, on y reste mais pour le reset d'après *)
        (* cs est faux pour toujours *)
        assert (Hcs : cs == cons (pres false) (map (fun v : sampl bool => match v with
                                            | abs => abs
                                            | pres _ => pres false
                                            | err e => err e
                                            end) rs')).
        { rewrite Hccs.
          apply cons_eq_compat; auto.
          rewrite <- cs_spec1; auto.
          now rewrite Hccs, fby1AP_eq at 1. }
        clear Hccs.

        rewrite merge_false, 2 whennot_false in Hu.
        2-13: admit. (* chiant mais ok, sauf peut-être safe(reset) *)
        rewrite reset_eq in Hu; cbv zeta in Hu.
        destruct (true_until_pres1 true rs') as (cs' & Htu & Hcs'); auto.
        rewrite f_when in Hu.
        rewrite Htu, 2 whennot_eq, reset_abs, merge_eq, expecta_eq in Hu.
        (* rewrite Htu, when_eq, 2 whennot_eq, reset_abs, merge_eq, expecta_eq in Hu. *)
        (* split. rewrite Hu, Hv, 2 first_app_first, <- 2 take_1, <- 2 LpF, 2 take_1, 2 first_cons; auto. *)
        split. rewrite Hu, Hv, 2 first_app_first. admit. (* ok *)
        exists rs',xs',cs',(rem (f (cons (pres a) xs'))).
        split; auto.
        split; auto.
        split; auto. admit.
        split; auto.
        split; auto.
        split; auto. admit.
        split; auto.
        split; auto. admit.
        rewrite Hu, Hv, 2 rem_app.
        split; auto.
        admit. (* ok *)
        all: admit.
    + (* signal false *)
      rewrite rem_cons in Hv.
      destruct HH as [(Hccs& Hfy)|Hccs].
      * (* on était dans l'état 1 *)
        destruct (true_until_pres1 false rs') as (cs' & Htu & Hcs'); auto.
        rewrite Hccs, Htu, when_eq, 2 whennot_eq, reset_abs, merge_eq, expecta_eq, rem_cons, app_cons in Hu.
        rewrite app_cons in Hv.
        split. now rewrite Hu, Hv, 2 first_cons.
        exists rs',xs',cs',ys'; do 8 (split; auto).
        rewrite Hu, Hv, 2 rem_cons; auto.
      * split.
        { rewrite Hv, app_cons, first_cons.
          rewrite Hu, Hccs, when_eq, 2 whennot_eq, merge_eq, first_app_first, first_cons.
          auto. }
        eexists rs',xs',(rem cs),ys'; do 8 (split; auto).
        split.
        { rewrite Hu, Hccs, when_eq, 2 whennot_eq, reset_abs, merge_eq, expecta_eq, app_cons, 3 rem_cons.
          reflexivity. }
        split.
        { rewrite Hv, app_cons, rem_cons; reflexivity. }
        right.
        { rewrite Hccs, rem_cons.
          rewrite Hccs at 1.
          now rewrite fby1AP_eq. }

  - (* cas absent : tout marche *)
    rewrite app_cons, rem_cons in Hv.
    rewrite AbsF in Hfy; apply Con_eq_simpl in Hfy as [_ Hfy].
    destruct Hu as [Hu|(cs & Hcs & Hu)].
    + (* cas initial *)
      rewrite true_until_abs, 2 whennot_eq,merge_eq, reset_abs,
        when_eq, 2 expecta_eq in Hu.
      split. now rewrite Hu, Hv, 2 first_cons.
      exists rs',xs',ys'; do 9 (split; auto).
      rewrite Hu, Hv, rem_cons; auto.
    + (* cas transitoire *)
      rewrite Hrs, AC_cons, sconst_cons, fby1_eq, sbinop_eq in Hcs.
      split.
      { rewrite Hv, first_cons.
        rewrite Hu.
        rewrite Hcs, Hrs, Hxs, Hys, when_eq, 2 whennot_eq, reset_abs,
          merge_eq, 2 expecta_eq, first_cons.
        reflexivity. }
      (* rewrite Hcs, Hrs, Hxs, Hys, when_eq, 2 whennot_eq, reset_abs, *)
      (*   merge_eq, 2 expecta_eq in Hu. *)
      (* split. now rewrite Hu, Hv, 2 first_cons. *)
      exists rs',xs',ys'; do 9 (split; auto).
      split; [|rewrite Hv, rem_cons; auto].
      right; exists (rem cs); split.
      * rewrite Hcs, rem_cons.
        rewrite Hcs at 1.
        now rewrite fby1AP_eq.
      * rewrite Hu.
        rewrite Hcs, rem_cons; auto.
        (* TODO: faire ces réécritures en commun avec celui d'avant !! *)
        now rewrite  Hrs, Hxs, Hys, when_eq, 2 whennot_eq, reset_abs,
          merge_eq, 2 expecta_eq, rem_cons.
  - (* présent *)
    destruct vr.
    + (* signal reçu : on échange les états *)
      rewrite sreset'_eq, rem_cons, <- Hfy, app_cons, rem_cons in Hv.
      destruct Hu as [Hu| (cs & Hcs & Hu)].
      * (* on était dans l'état 1, on passe dans le 2 *)
      destruct (true_until_pres1 true rs') as (cs & Htu & Hcs); auto.
      rewrite Htu, 2 whennot_eq, when_eq, merge_eq, reset_abs,
        expecta_eq, app_cons, rem_cons in Hu.
      split. now rewrite Hu, Hv, 2 first_cons.
      exists rs',xs',ys'; do 9 (split; auto).



  (*              ( (* cas 1 : état stable du début *) *)
  (*                U == merge (true_until rs) (when (true_until rs) ys) *)
  (*                      (reset (whennot (true_until rs) rs) (whennot (true_until rs) xs)) *)
  (*                \/ (* cas 2 : signal reçu, état transitoire *) *)
  (*                  (exists cs, *)
  (*                      cs == sbinop (fun b1 b2 => Some (negb b1 && b2)) rs (fby1 (Some true) (sconst true (AC rs)) cs) *)
  (*                      /\ U == merge cs (when cs ys) (reset (whennot cs rs) (whennot cs xs))) *)
  (*                  ) *)
  (*            /\ V == sreset' f (map bool_of rs) xs ys *)
  (*   ). *)
  (* 3: exists rs,xs,(f xs); auto 11. *)


  apply DS_bisimulation_allin1 with
    (R := fun U V =>
            exists rs xs ys,
              (* TODO: on va avoir un souci avec ys ? *)
             infinite rs
             /\ infinite xs
             /\ infinite ys
             /\ safe_DS rs
             /\ safe_DS xs
             /\ safe_DS ys
             /\ AC xs == AC rs
             /\ AC xs == AC ys
             /\ ys == f xs
             /\ ( (* cas 1 : état stable du début *)
                 U == merge (true_until rs) (when (true_until rs) ys)
                       (reset (whennot (true_until rs) rs) (whennot (true_until rs) xs))
                 \/ (* cas 2 : signal reçu, état transitoire *)
                   (exists cs,
                       cs == sbinop (fun b1 b2 => Some (negb b1 && b2)) rs (fby1 (Some true) (sconst true (AC rs)) cs)
                       /\ U == merge cs (when cs ys) (reset (whennot cs rs) (whennot cs xs)))
                   )
             /\ V == sreset' f (map bool_of rs) xs ys
    ).
  3: exists rs,xs,(f xs); auto 11.
  clear; intros * ? Eq1 Eq2; now (setoid_rewrite <- Eq1; setoid_rewrite <- Eq2).
  clear.
  intros U V Hc (rs & xs & ys & Infr & Infx & Infy & Sr & Sx & Sy & Hac & Acy & Hfy & Hu & Hv).

  apply infinite_decomp in Infr as (vr & rs' & Hrs &Infr').
  apply infinite_decomp in Infx as (vx & xs' & Hxs &Infx').
  apply infinite_decomp in Infy as (vy & ys' & Hys &Infy').
  rewrite Hrs, Hxs, Hys in *.
  repeat rewrite AC_cons in *.
  rewrite map_eq_cons in Hv.
  apply Con_eq_simpl in Hac as [], Acy as [].
  inversion_clear Sr; inversion_clear Sx; inversion_clear Sy.
  rewrite sreset'_eq, rem_cons in Hv.
  destruct vr as [|vr|], vx, vy; simpl in Hv; try (tauto || congruence).
  - (* cas absent : tout marche *)
    rewrite app_cons, rem_cons in Hv.
    rewrite AbsF in Hfy; apply Con_eq_simpl in Hfy as [_ Hfy].
    destruct Hu as [Hu|(cs & Hcs & Hu)].
    + (* cas initial *)
      rewrite true_until_abs, 2 whennot_eq,merge_eq, reset_abs,
        when_eq, 2 expecta_eq in Hu.
      split. now rewrite Hu, Hv, 2 first_cons.
      exists rs',xs',ys'; do 9 (split; auto).
      rewrite Hu, Hv, rem_cons; auto.
    + (* cas transitoire *)
      rewrite Hrs, AC_cons, sconst_cons, fby1_eq, sbinop_eq in Hcs.
      split.
      { rewrite Hv, first_cons.
        rewrite Hu.
        rewrite Hcs, Hrs, Hxs, Hys, when_eq, 2 whennot_eq, reset_abs,
          merge_eq, 2 expecta_eq, first_cons.
        reflexivity. }
      (* rewrite Hcs, Hrs, Hxs, Hys, when_eq, 2 whennot_eq, reset_abs, *)
      (*   merge_eq, 2 expecta_eq in Hu. *)
      (* split. now rewrite Hu, Hv, 2 first_cons. *)
      exists rs',xs',ys'; do 9 (split; auto).
      split; [|rewrite Hv, rem_cons; auto].
      right; exists (rem cs); split.
      * rewrite Hcs, rem_cons.
        rewrite Hcs at 1.
        now rewrite fby1AP_eq.
      * rewrite Hu.
        rewrite Hcs, rem_cons; auto.
        (* TODO: faire ces réécritures en commun avec celui d'avant !! *)
        now rewrite  Hrs, Hxs, Hys, when_eq, 2 whennot_eq, reset_abs,
          merge_eq, 2 expecta_eq, rem_cons.
  - (* présent *)
    destruct vr.
    + (* signal reçu : on échange les états *)
      rewrite sreset'_eq, rem_cons, <- Hfy, app_cons, rem_cons in Hv.
      destruct Hu as [Hu| (cs & Hcs & Hu)].
      * (* on était dans l'état 1, on passe dans le 2 *)
      destruct (true_until_pres1 true rs') as (cs & Htu & Hcs); auto.
      rewrite Htu, 2 whennot_eq, when_eq, merge_eq, reset_abs,
        expecta_eq, app_cons, rem_cons in Hu.
      split. now rewrite Hu, Hv, 2 first_cons.
      exists rs',xs',ys'; do 9 (split; auto).











    apply infinite_decomp in Infr as (vr & rs' & Hrs &Infr').
  apply infinite_decomp in Infx as (vx & xs' & Hxs &Infx').
  apply infinite_decomp in Infy as (vy & ys' & Hys &Infy').
  rewrite Hrs, Hxs, Hys in *.
  repeat rewrite AC_cons in *.
  rewrite map_eq_cons in HV.
  apply Con_eq_simpl in Hac as [], Acy as [].
  inversion_clear Sr; inversion_clear Sx; inversion_clear Sy.
  rewrite sreset'_eq, rem_cons in HV.
  destruct vr as [|vr|], vx, vy; simpl in HV; try (tauto || congruence).
  { (* abs : Cof *)
    rewrite AbsF in Hys.
    apply Con_eq_simpl in Hys as [_ Hys]; subst.
    rewrite <- Hys in *.
    rewrite true_until_abs, 2 whennot_eq,merge_eq, reset_abs,
      when_eq, 2 expecta_eq in HU.
    split. now rewrite HU, HV, first_app_first, 2 first_cons.
    apply (Cof rs' xs'); rewrite ?HU, ?HV, ?rem_cons, ?rem_app; eauto 1. }
   (* pres : plusieurs cas *)
  destruct (true_until_pres1 vr rs') as (cs & Htu & Hcs); auto.
  rewrite Htu, 2 whennot_eq, when_eq, merge_eq, reset_abs,
    expecta_eq, app_cons, rem_cons in HU.
  rewrite rem_cons, app_cons in HV.
  split.
  { (* first : vrai dans les deux cas *)
    rewrite HU, HV, first_cons.
    destruct vr; auto.
    apply first_eq_compat in Hys; revert Hys.
    now rewrite sreset'_eq, first_app_first, <- 2 take_1, <- LpF, 2 take_1, 2 first_cons.
  }
  destruct vr.
  - (* signal reçu *)
    rewrite sreset'_eq, Hys, 2 rem_cons, app_cons in HV.
    


    apply (Cof rs' xs'); rewrite ?HU, ?HV, ?rem_cons; auto.
    apply first_eq_compat in Hys as Hfys.
    rewrite


Qed.

apply DS_bisimulation_allin1 with
    (R:= fun U V =>
           exists rs xs n cs,
             infinite rs
             /\ infinite xs
             /\ safe_DS rs
             /\ safe_DS xs
             /\ AC xs == AC rs
             (* /\ cs == (sbinop (fun b1 b2 => Some (negb b1 && b2)) rs *)
             (*            (fby1 (Some true) (sconst true (AC rs)) cs)) *)
             (* TODO: quelle relation avec rs ??? *)
             /\ U == 

                 merge cs (nrem n (f (when cs xs))) (* sans doute pas le bon cs ici *)
                      (reset (nrem n (whennot cs rs)) (nrem n ((whennot cs xs))))
             /\ V == sreset' f (map bool_of rs) (nrem n xs) (nrem n (f xs))
    ).
  3:{ eexists rs,xs,O,_.
      repeat (split; [now auto|]). split; [|now auto].
      rewrite reset_eq; cbv zeta.
      eauto. }
  admit.
  clear.
  intros U V Hc (rs & xs & n & cs & Infr & Infx & Sr & Sx & Hac & Hu & Hv).

  (* idée: f (when cs xs) == when cs (f xs) -> non à cause des horloges... *)



  apply DS_bisimulation_allin1 with
    (R:= fun U V =>
           exists rs xs,
             infinite rs
             /\ infinite xs
             /\ safe_DS rs
             /\ safe_DS xs
             /\ AC xs == AC rs
             /\ (
                 (U == reset rs xs
                  /\ V == sreset' f (map bool_of rs) xs (f xs))
                 \/
                   (exists n cs,
                       (* cs est le true_until déroulé *)
                       cs == (sbinop (fun b1 b2 => Some (negb b1 && b2)) rs
                                (fby1 (Some true) (sconst true (AC rs)) cs))
                       /\
                         U ==
                           merge cs (nrem n (f (when cs xs))) (* sans doute pas le bon cs ici *)
                             (reset (nrem n (whennot cs rs)) (nrem n ((whennot cs xs))))
                       /\ V == sreset' f (map bool_of rs) (nrem n xs) (nrem n (f xs)))
               )
    ).
  3: eauto 10.
  { intros * ? Eq1 Eq2.
    setoid_rewrite <- Eq1.
    setoid_rewrite <- Eq2.
    eauto. }
  clear.
  intros U V Hc (rs & xs & Infr & Infx & Sr & Sx & Hac & HH).
  apply infinite_decomp in Infr as (vr & rs' & Hrs &Infr').
  apply infinite_decomp in Infx as (vx & xs' & Hxs &Infx').
  rewrite Hrs in Sr, Hac.
  rewrite Hxs in Sx, Hac.
  repeat rewrite AC_cons in Hac.
  apply Con_eq_simpl in Hac as [].
  inversion_clear Sr; inversion_clear Sx.
  setoid_rewrite Hrs in HH.
  setoid_rewrite Hxs in HH.
  split.
  - (* first = first *)
    destruct HH as [(Hu & Hv)|(n & cs & Hcs & Hu & Hv)].
    + admit.
    + rewrite Hu, Hv.
      rewrite map_eq_cons, sreset'_eq.
      rewrite Hcs, AC_cons, sconst_cons.
      rewrite fby1_eq.
      destruct vr, vx; try (congruence || tauto).
      * (* abs *)
        rewrite sbinop_eq; simpl.
        rewrite merge_eq, first_cons, first_app_first.
        admit. (* il faut une hypothèse d'alignement des absences en plus... *)
      * (* pres *)
        rewrite sbinop_eq; simpl.
        rewrite merge_eq.
        destruct a; simpl; repeat rewrite first_app_first, ?sreset'_eq.
        rewrite whennot_eq.
        2:rewrite when_eq.
        all: rewrite fby1AP_eq.
  - (* R (rem) *)
Qed.


Theorem reset_match :
  forall rs xs,
    infinite rs ->
    infinite xs ->
    safe_DS rs ->
    safe_DS xs ->
    AC xs == AC rs ->
    let rsb := map bool_of rs in
    reset rs xs == sreset f rsb xs.
Proof.
  intros * Infr Infx Sr Sx Hac rsb; subst rsb.
  rewrite reset_eq, sreset_eq.
  coind_Oeq Cof1.
  apply infinite_decomp in Infr as (vr & rs' & Hrs &Infr').
  apply infinite_decomp in Infx as (vx & xs' & Hxs &Infx').
  cbv zeta in HU.
  rewrite Hrs, Hxs in *.
  repeat rewrite AC_cons in *.
  rewrite map_eq_cons in HV.
  apply Con_eq_simpl in Hac as [].
  inversion_clear Sr; inversion_clear Sx.
  rewrite sreset'_eq, rem_cons in HV.
  destruct vr as [|r|], vx; simpl in HV; try tauto; try congruence.
  - (* abs *)
    rewrite true_until_abs, when_eq, 2 whennot_eq, AbsF,
      merge_eq, reset_abs, 2 expecta_eq in HU.
    rewrite AbsF, app_cons, rem_cons in HV.
    constructor.
    + rewrite HU, HV, 2 first_cons; auto.
    + apply (Cof1 rs' xs'); auto.
      * rewrite HU, rem_cons; auto.
      * rewrite HV, rem_cons; auto.
  - (* deux cas identiques : *)
    assert (HV' : V == app (f (cons (pres a) xs'))
                         (sreset' f (map bool_of rs') xs'
                            (rem (f (cons (pres a) xs'))))).
    { destruct r; rewrite HV, ?sreset'_eq, ?rem_cons; auto. } clear HV.
    destruct (true_until_pres1 r rs') as (U' & Htu & Hu'); auto.
    rewrite Htu, when_eq, 2 whennot_eq, merge_eq in HU.
    rewrite reset_abs, expecta_eq in HU.
    constructor.
    { rewrite HU, HV', 2 first_app_first.
      now rewrite <- 2 take_1, <- 2 LpF, 2 take_1, 2 first_cons. }
    apply Oeq_ds_eq.
    rewrite HU, HV', 2 rem_app. 2,3: admit. (* infty ? *)
    









      apply (Cof rs' xs'); auto.
      * cbv zeta.
        rewrite HU, rem_app. 2: admit.
        
      * rewrite HV', rem_app. 2:admit. (* facile *)
        (* ok, juste généraliser (f xs') comme un nrem *)
        admit.
Qed.


End VERSION3.
