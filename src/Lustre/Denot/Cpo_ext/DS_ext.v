From Coq Require Import Morphisms List.
From Velus Require Import Common.CommonList.
From Velus.Lustre.Denot.Cpo Require Import Cpo_streams_type Systems.

Import ListNotations.

Require Import Cpo_def_ext.

(** * Extension of the Cpo library *)

(** ** Cpo_streams_type.v *)

Global Hint Rewrite
  first_cons
  CONS_simpl Cons_simpl
  DSCASE_simpl DScase_cons
  REM_simpl rem_cons
  app_cons
  filter_eq_cons map_eq_cons
  rem_bot map_bot filter_bot first_eq_bot
  : cpodb.

Lemma bot_not_cons :
  forall D (x : D) s, 0 == cons x s -> False.
Proof.
  intros * H.
  apply (@not_is_consBot D).
  now rewrite H.
Qed.

Lemma Con_eq_simpl : forall D a b (s t : DS_ord D),
    (Con a s:DS_ord D) == Con b t-> a = b /\ s == t.
Proof.
  split.
  now apply Con_hd_simpl in H.
  now apply Con_tl_simpl in H.
Qed.

Lemma Con_le_simpl : forall D a b (s t : DS_ord D),
    (Con a s:DS_ord D) <= Con b t -> a = b /\ s <= t.
Proof.
  split.
  now apply DSleCon_hd in H.
  now apply DSleCon_tl in H.
Qed.

Lemma DSle_cons_elim :
  forall D (x :  DS D) a (s : DS D),
    (Con a s : DS D) <= x ->
    exists t, x == Con a t /\ s <= t.
Proof.
  intros * Hle.
  apply DSle_uncons in Hle as [? [ Hd]].
  apply decomp_eqCon in Hd; eauto.
Qed.

Lemma Con_le_le :
  forall D x xs y ys t,
    (Con x xs : DS D) <= t ->
    (Con y ys : DS D) <= t ->
    x = y.
Proof.
  intros * Le1 Le2.
  eapply DSle_cons_elim in Le1 as (?& Hx &?), Le2 as (?& Hy &?).
  rewrite Hx in Hy.
  now apply Con_eq_simpl in Hy as [].
Qed.

Lemma app_app : forall D (s t u : DS D),
    app (app s u) t == app s t.
Proof.
  intros.
  now rewrite <- app_app_first, first_app_first, app_app_first.
Qed.

Lemma FILTER_filter :
  forall D P Pdec (s: DS D), FILTER P Pdec s = filter P Pdec s.
Proof.
  reflexivity.
Qed.
Global Hint Rewrite FILTER_filter : cpodb.

Lemma MAP_map :
  forall D1 D2 (F:D1->D2) (s: DS D1), MAP F s = map F s.
Proof.
  reflexivity.
Qed.
Global Hint Rewrite MAP_map : cpodb.

Lemma DScase_bot_eq :
  forall D D' f, @DScase D D' f 0 == 0.
Proof.
  auto.
Qed.
Global Hint Rewrite DScase_bot_eq : cpodb.

Lemma DScase_bot2_le :
  forall D D' (f : D -> DS D -m> DS D') (Fbot : forall a x, f a x == 0),
  forall x,
    DScase f x <= 0.
Proof.
  intros * Fbot.
  cofix Cof.
  destruct x.
  - rewrite DScaseEps.
    apply DSleEps, Cof.
  - rewrite DScase_cons.
    apply Fbot.
Qed.

Lemma DScase_bot2 :
  forall D D' (f : D -> DS D -m> DS D') (Fbot : forall a x, f a x == 0),
  forall x,
    DScase f x == 0.
Proof.
  intros.
  eapply DScase_bot2_le in Fbot; eauto.
Qed.

Lemma cons_is_cons :
  forall D a (x t : DS D),
    x == cons a t -> is_cons x.
Proof.
  now intros * ->.
Qed.

Lemma Epsdecomp : forall D a (s x:DStr D), decomp a s (Eps x) -> decomp a s x.
Proof.
  destruct 1 as [[|k] Hp].
  inversion Hp.
  now exists k.
Qed.

Lemma decomp_decomp :
  forall A (s : DS A) x x' t t',
    decomp x t s ->
    decomp x' t' s ->
    x = x' /\ t = t'.
Proof.
  clear. intros * [k kth].
  revert dependent s.
  induction k; simpl; intros * Hp Hd; subst.
  - apply decompCon_eq in Hd. now inversion Hd.
  - destruct s; simpl in *.
    + apply Epsdecomp in Hd. eauto.
    + apply decompCon_eq in Hd.
      inversion Hd; subst; eauto.
Qed.

(** *** DS_bisimulation with two obligations in one *)
Lemma DS_bisimulation_allin1 : forall D (R: DS D -> DS D -> Prop),
        (forall x1 x2 y1 y2, R x1 y1 -> x1==x2 -> y1==y2 -> R x2 y2)
   -> (forall (x y:DS D), (is_cons x \/ is_cons y) -> R x y -> first x == first y /\ R (rem x) (rem y))
   -> forall x y, R x y -> x == y.
Proof.
  intros * IH Hfr x t.
  apply (DS_bisimulation R);
    auto; intros ?? Hic ?; now apply Hfr in Hic.
Qed.

Lemma first_rem_eq :
  forall D (xs ys : DS D),
    first xs == first ys ->
    rem xs == rem ys ->
    xs == ys.
Proof.
  intros.
  apply DS_bisimulation_allin1 with
    (R := fun U V => first U == first V
                  /\ rem U == rem V); auto.
  now intros * [] <- <-.
  clear; intros xs ys Hc [Hf Hr]; auto.
Qed.

(** *** Simpler principle than DSle_rec_eq  *)
Lemma DSle_rec_eq2 : forall D (R : DStr D -> DStr D -> Prop),
    (forall x1 x2 y1 y2:DS_ord D, R x1 y1 -> x1==x2 -> y1==y2 -> R x2 y2) ->
    (forall x y, is_cons x -> R x y -> first x == first y /\ R (rem x) (rem y))
    -> forall x y : DS_ord D, R x y -> x <= y.
Proof.
  intros * R1 R2 x y Hr.
  apply DSle_rec_eq with R; auto.
  intros ?? y' Hr'.
  eapply R2 in Hr' as (?&?); auto.
  autorewrite with cpodb in *.
  exists (rem y'); split; auto.
  apply symmetry, first_cons_elim in H as (?& -> &?).
  now autorewrite with cpodb.
Qed.

(** *** The constant stream *)
CoFixpoint DS_const {A} (a : A) : DS A := Con a (DS_const a).

Lemma DS_const_eq :
  forall {A} (a : A),
    DS_const a = cons a (DS_const a).
Proof.
  intros.
  now rewrite DS_inv at 1.
Qed.

Lemma is_cons_DS_const :
  forall {A} (a : A), is_cons (DS_const a).
Proof.
  intros.
  now rewrite DS_const_eq.
Qed.

Lemma DS_const_inf :
  forall {A} (a : A), infinite (DS_const a).
Proof.
  cofix Cof; intros.
  rewrite DS_const_eq.
  constructor; rewrite ?rem_cons; auto.
Qed.

Lemma map_DS_const :
  forall {A B} (f : A -> B) c,
    map f (DS_const c) == DS_const (f c).
Proof.
  intros.
  eapply DS_bisimulation_allin1
    with (R := fun U V => U == map f (DS_const c)
                       /\ V == DS_const (f c)).
  3: eauto.
  { now intros ????? <- <-. }
  intros U V Hc (Hu & Hv).
  rewrite Hu, Hv.
  split; [| split]; auto.
  now rewrite (DS_const_eq c), (DS_const_eq (f c)), map_eq_cons, 2 first_cons.
  now rewrite DS_const_eq, map_eq_cons, rem_cons at 1.
  now rewrite DS_const_eq, rem_cons at 1.
Qed.

Global Add Parametric Morphism A B : (@MAP A B)
    with signature (respectful eq eq) ==> @Oeq (DS A) ==> @Oeq (DS B)
      as MAP_morph.
Proof.
  intros f g Hfg ?? ->.
  eapply DS_bisimulation_allin1
    with (R := fun U V => exists xs,
                   U == MAP f xs
                   /\ V == MAP g xs).
  3: eauto.
  { intros ????(?&?&?&?)??. eauto. }
  intros U V Hc (xs & Hu & Hv).
  assert (is_cons xs) as Hcx.
  { rewrite Hu, Hv in Hc.
    destruct Hc as [?%map_is_cons|?%map_is_cons]; tauto. }
  apply is_cons_elim in Hcx as (vx & xs' & Hx).
  rewrite Hx in Hu, Hv.
  rewrite MAP_map, map_eq_cons in Hu, Hv.
  setoid_rewrite Hu.
  setoid_rewrite Hv.
  erewrite 2 first_cons, 2 rem_cons, Hfg; eauto.
Qed.

Lemma DSle_cons :
  forall D x (xs : DS D) y ys,
    cons x xs <= cons y ys -> xs <= ys.
Proof.
  intros * Hle.
  destruct (DSle_decomp (decompCon _ _) Hle) as (?&H&?).
  apply decompCon_eq in H.
  inversion H; subst; auto.
Qed.

Lemma app_rem :
  forall D (s : DS D),
    app s (rem s) == s.
Proof.
  intros.
  rewrite <- app_app_first.
  apply app_first_rem.
Qed.

Lemma infinite_rem :
  forall D (s : DS D),
    infinite (rem s) -> infinite s.
Proof.
  intros * Hi.
  constructor; auto.
  inversion Hi; auto.
Qed.

Lemma rem_infinite :
  forall D (s : DS D),
    infinite s -> infinite (rem s).
Proof.
  intros * Hi.
  inversion Hi; auto.
Qed.

Lemma infinite_app :
  forall D (U V : DS D),
    is_cons U ->
    infinite V ->
    infinite (app U V).
Proof.
  intros * Hc Hi.
  constructor; auto.
  now rewrite rem_app.
Qed.

Lemma infinite_le_eq : forall D (s t:DS D), s <= t -> infinite s -> s == t.
Proof.
  intros.
  apply DS_bisimulation_allin1 with
    (R := fun U V => U <= V /\ infinite U); auto.
  { intros * [] <- <-; auto. }
  clear.
  intros s t Hc [Hle Hinf].
  destruct Hinf as [H Hinf].
  apply is_cons_elim in H as (?&?& Hs).
  rewrite Hs in *.
  apply DSle_cons_elim in Hle as (?& Ht &?).
  now rewrite Ht, 2 first_cons, 2 rem_cons in *.
Qed.

Lemma is_cons_rem : forall D (s : DS D),
    is_cons (rem s) -> exists x y xs, s == cons x (cons y xs).
Proof.
  intros * Hc.
  apply rem_is_cons in Hc as Hc'.
  apply is_cons_elim in Hc' as (x & xs' & Hs).
  rewrite Hs, rem_cons in Hc.
  apply is_cons_elim in Hc as (y & xs & Hxs').
  rewrite Hxs' in Hs.
  eauto.
Qed.

Lemma rem_eq_cons : forall D (b:D) s t,
    rem s == cons b t ->
    exists a, s == cons a (cons b t).
Proof.
  intros * Hrs.
  destruct (is_cons_rem _ s) as (a' & b' & t' & Hs).
  rewrite Hrs; auto.
  apply rem_eq_compat in Hs as HH.
  rewrite rem_cons, Hrs in HH.
  apply Con_eq_simpl in HH as [? Ht]; subst.
  exists a'. now rewrite Hs, Ht.
Qed.

Lemma map_eq_cons_elim : forall D D' (f : D -> D') a s x,
    map f x == cons a s ->
    exists b, exists t, x == cons b t /\ f b = a /\ map f t == s.
Proof.
  intros * Hm.
  unfold map,MAP in Hm.
  setoid_rewrite FIXP_eq in Hm.
  fold (MAP f) in Hm.
  apply DScase_eq_cons_elim in Hm as (b & t & Heq & Hmapf).
  apply Con_hd_simpl in Hmapf as ?.
  apply Con_tl_simpl in Hmapf as ?.
  eauto.
Qed.

Lemma map_comp :
  forall A B C (f : A -> B) (g : B -> C),
  forall s, map g (map f s) == map (fun x => (g (f x))) s.
Proof.
  intros.
  apply DS_bisimulation_allin1 with
    (R := fun U V => exists s, U == map g (map f s) /\
                         V == map (fun x => (g (f x))) s).
  3: eauto.
  { intros ???? (?&?&?) ??; eauto. }
  intros X Y [Hcons|Hcons] (s1 & HX & HY);
    (split; [| exists (rem s1)]);
    rewrite HX,HY in *;
    repeat apply map_is_cons in Hcons;
    apply is_cons_elim in Hcons as (?&?&->);
    now autorewrite with cpodb.
Qed.

Lemma rem_map :
  forall A B (f : A -> B) xs,
    rem (map f xs) == map f (rem xs).
Proof.
  intros.
  apply DS_bisimulation_allin1 with
    (R := fun U V => exists xs, U == rem (map f xs)
                        /\ V == map f (rem xs)).
  3: eauto.
  { intros ???? (?& -> & ->) ??. eauto. }
  clear.
  intros U V Hc (? & Hu & Hv).
  assert (exists a b xs, x == cons a (cons b xs)) as (a & b & xs & Hx). {
    rewrite Hu, Hv in Hc.
    destruct Hc as [Hc | Hc].
    - apply is_cons_rem in Hc as (?&?&?& Hfx).
      apply map_eq_cons_elim in Hfx as (?&?& ? & ? & Hf'); subst.
      apply map_eq_cons_elim in Hf' as (?& ? & HH & ? &?); subst.
      rewrite HH in *; eauto.
    - now apply map_is_cons, is_cons_rem in Hc.
  }
  setoid_rewrite Hu.
  setoid_rewrite Hv.
  setoid_rewrite Hx.
  split; [| exists (cons b xs)]; now autorewrite with cpodb.
Qed.

Lemma first_map :
  forall A B (f : A -> B) s,
    first (map f s) == map f (first s).
Proof.
  intros.
  eapply DS_bisimulation_allin1
    with (R := fun U V => exists s, U == first (map f s) /\ V == map f (first s)).
  3: eauto.
  { intros * (?&?&?) ??. esplit; eauto. }
  clear.
  intros U V Hc (?& Hu & Hv).
  assert (is_cons x) as Hx.
  { rewrite Hu, Hv in *.
    destruct Hc as
      [Hc % first_is_cons % map_is_cons | Hc % map_is_cons]; auto. }
  apply is_cons_elim in Hx as (vx & xs & Hx).
  setoid_rewrite Hu.
  setoid_rewrite Hv.
  setoid_rewrite Hx.
  split; [| exists 0]; now autorewrite with cpodb.
Qed.

Lemma app_map :
  forall A B (f : A -> B) (U V : DS A),
    map f (app U V) == app (map f U) (map f V).
Proof.
  intros.
  apply DS_bisimulation_allin1 with
    (R := fun U V =>
            U == V
            \/
              exists X Y,
                (U == map f (app X Y) /\ V == app (map f X) (map f Y))).
  3: eauto.
  { intros * ? Eq1 Eq2.
    setoid_rewrite <- Eq1.
    now setoid_rewrite <- Eq2.
  }
  clear.
  intros U V Hc [HH | (X & Y & Hu & Hv)].
  { setoid_rewrite HH. eauto. }
  setoid_rewrite Hu.
  setoid_rewrite Hv.
  destruct (@is_cons_elim _ X) as (vx & X' & Hx).
  { destruct Hc.
    - eapply app_is_cons, map_is_cons.
      now rewrite <- Hu.
    - eapply map_is_cons, app_is_cons.
      now rewrite <- Hv. }
  setoid_rewrite Hx.
  rewrite app_cons, 2 map_eq_cons, first_cons, app_cons, first_cons, rem_cons.
  auto.
Qed.

Lemma map_ext :
  forall D D' (f g : D -> D'),
    (forall d, f d = g d) ->
    forall x, map f x == map g x.
Proof.
  intros * Hfg x.
  apply DS_bisimulation_allin1
    with (R := fun U V => exists x, U == map f x /\ V == map g x); eauto 3.
  { intros * ? Eq1 Eq2.
    setoid_rewrite <- Eq1.
    setoid_rewrite <- Eq2.
    auto. }
  clear - Hfg; intros U V Hc (xs & Hu & Hv).
  destruct (@is_cons_elim _ xs) as (x & xs' & Hxs).
  { rewrite Hu, Hv in Hc.
    now destruct Hc as [?%map_is_cons|?%map_is_cons]. }
  rewrite Hxs, map_eq_cons in *.
  split;[|exists xs']; now rewrite Hu, Hv, ?first_cons, ?rem_cons, ?Hfg.
Qed.

Lemma map_inf :
  forall A B (f : A -> B) xs,
    infinite xs ->
    infinite (map f xs).
Proof.
  intros * Hi. remember (map f xs) as fxs eqn:Hfxs.
  apply Oeq_refl_eq in Hfxs.
  revert Hi Hfxs.
  revert xs fxs.
  cofix Cof; intros.
  assert (Hi' := Hi).
  inversion Hi.
  constructor.
  now rewrite Hfxs; apply is_cons_map.
  apply Cof with (xs := rem xs); auto.
  now rewrite Hfxs, <- rem_map.
Qed.

Lemma cons_decomp :
  forall D x (s : DS D) t,
    s == cons x t ->
    exists t', decomp x t' s.
Proof.
  intros * Hs.
  pose proof (is_cons_eq_compat (symmetry Hs) (isConCon _ _)) as Hc.
  destruct (uncons Hc) as (?&?& Hd).
  apply decomp_eqCon in Hd as Heq.
  rewrite Heq in Hs.
  apply Con_eq_simpl in Hs as []; subst.
  eauto.
Qed.

(* Gives the first element that satisfies [P].
   Useful to reason with [filter] by induction. *)
Inductive isConP {D:Type} (P : D -> Prop) : DStr D -> Prop :=
| isConPEps : forall x, isConP P x -> isConP P (Eps x)
| isConPP : forall a s, P a -> isConP P (Con a s)
| isConPnP: forall a s, isConP P s -> ~ P a -> isConP P (Con a s).
Global Hint Constructors isConP : core.

Lemma isConP_pred : forall D (P:D->Prop) x, isConP P (pred x) -> isConP P x.
Proof.
  destruct x; simpl; auto.
Qed.

Lemma isConP_le_compat : forall D (P : D -> Prop) (x y : DS D),
    x <= y -> isConP P x -> isConP P y.
Proof.
  intros * Hle Hic.
  revert dependent y.
  induction Hic; intros; inversion_clear Hle; auto;
    destruct H0 as [n];
    revert dependent y;
    induction n; intros; simpl in *; subst; auto using isConP_pred.
Qed.

Lemma isConP_eq_compat : forall D (P:D->Prop) (x y:DS D),
    x == y -> isConP P x -> isConP P y.
Proof.
  intros; apply isConP_le_compat with x; auto.
Qed.

Add Parametric Morphism D P : (@isConP D P)
    with signature (@Oeq (DS D)) ==> iff as isConP_eq_iff.
Proof.
  intros x y; split; intro.
  apply isConP_eq_compat with x; auto.
  apply isConP_eq_compat with y; auto.
Qed.

Lemma filter_is_cons :
  forall (D : Type) (P : D -> Prop) Pdec xs,
    is_cons (filter P Pdec xs) ->
    isConP P xs.
Proof.
  intros ???.
  unfold filter, FILTER.
  rewrite FIXP_fixp.
  apply fixp_ind.
  - intros seq Hseq s Hic.
    apply is_cons_elim in Hic as (a&ls&Hlub).
    apply DS_lubCon_inv in Hlub as (x & tlc & n & Hn).
    specialize (Hn O).
    now apply (Hseq n), is_cons_eq_compat with (Con a (x O)).
  - intros * H; now apply not_is_consBot in H.
  - intros f Hf s Hic.
    apply DScase_is_cons in Hic as Hc.
    apply is_cons_elim in Hc as (x&s'&Hxs).
    rewrite Hxs in *.
    cbn in Hic.
    autorewrite with cpodb in Hic.
    destruct (Pdec x).
    + apply isConPP; auto.
    + apply isConPnP; auto.
Qed.

Lemma map_filter :
  forall A B (f : A -> B) (P : A -> Prop) Pdec (P' : B -> Prop) P'dec,
    (forall a, P a <-> P' (f a)) ->
    forall xs, map f (filter P Pdec xs) == filter P' P'dec (map f xs).
Proof.
  intros * HPP' xs.
  apply DS_bisimulation_allin1 with
    (R := fun U V => exists xs,
              U == map f (filter P Pdec xs)
              /\ V == filter P' P'dec (map f xs)).
  3: eauto.
  { intros ????(?&?&?&?)??. repeat esplit; eauto. }
  clear xs. intros xs ys Hic (s & Hx & Hy).
  destruct Hic as [Hic|Hic];
    rewrite Hx, Hy in *;
    setoid_rewrite Hx; setoid_rewrite Hy.
  - apply map_is_cons, filter_is_cons in Hic.
    revert Hx Hy. revert xs ys.
    induction Hic; intros.
    + rewrite <- eqEps in *. setoid_rewrite <- eqEps. eapply IHHic; eauto.
    + split; [|exists s];
        autorewrite with cpodb;
        destruct (Pdec a) as [Hp|Hnp], (P'dec (f a)) as [Hp'|Hnp']; try tauto.
      1,3: now autorewrite with cpodb.
      all: clear - HPP' Hp Hnp'; exfalso; firstorder 0.
    + autorewrite with cpodb in *|- ;
        destruct (Pdec a) as [Hp|Hnp], (P'dec (f a)) as [Hp'|Hnp']; try tauto.
      clear - HPP' Hnp Hp'; exfalso; firstorder 0.
      destruct (IHHic xs ys) as (? & x &?&?); auto.
      split; [| exists x];
        autorewrite with cpodb in *; destruct (Pdec a), (P'dec (f a)); tauto.
  - apply filter_is_cons in Hic.
    revert Hx Hy. revert xs ys.
    remember (map f s) as sm. apply Oeq_refl_eq in Heqsm.
    revert Heqsm. revert s.
    induction Hic; intros.
    + rewrite <- eqEps in *. setoid_rewrite <- eqEps. eapply IHHic; eauto.
    + apply symmetry, map_eq_cons_elim in Heqsm as (b & t& Hs &?&?); subst.
      setoid_rewrite Hs.
      split; [| exists t]; autorewrite with cpodb.
      all: destruct (Pdec b) as [Hp|Hnp], (P'dec (f b)) as [Hp'|Hnp']; try tauto.
      all: autorewrite with cpodb; auto.
      all: clear - HPP' Hnp Hp'; exfalso; firstorder 0.
    + apply symmetry, map_eq_cons_elim in Heqsm as (b &?& Hs &?& Hmap); subst.
      setoid_rewrite Hs.
      specialize (IHHic _ (symmetry Hmap) _ _ (Oeq_refl _) (Oeq_refl _))
        as (?& y &?&?).
      split; [|exists y];
        autorewrite with cpodb;
        destruct (Pdec b) as [Hp|Hnp], (P'dec (f b)) as [Hp'|Hnp']; try tauto;
        clear - HPP' Hp Hnp'; exfalso; firstorder 0.
Qed.

Lemma infinite_decomp :
  forall D (s : DS D),
    infinite s -> exists x t, s == cons x t /\ infinite t.
Proof.
  intros * [Hc Hinf].
  induction Hc as [s|].
  - destruct IHHc as (x & t &?&?).
    + unfold rem, Rem in Hinf.
      rewrite DSCase_simpl, DScaseEps in Hinf.
      now rewrite (infinite_morph (eqEps (rem s))).
    + exists x,t. split; auto.
      transitivity s; auto.
      apply symmetry, eqEps.
  - rewrite rem_cons in Hinf. eauto.
Qed.

Lemma infinite_cons :
  forall D x (xs : DS D),
    infinite xs -> infinite (cons x xs).
Proof.
  constructor; rewrite ?rem_cons; auto.
Qed.

Lemma cons_infinite :
  forall D x (xs : DS D),
    infinite (cons x xs) -> infinite xs.
Proof.
  destruct 1.
  now rewrite rem_cons in *.
Qed.


(** *** Take the prefix of length min(n,length(s)) from a stream s *)
Fixpoint take {A} (n : nat) : DS A -C-> DS A :=
  match n with
  | O => CTE _ _ 0
  | S n => (APP _ @2_ ID _) (take n @_ REM _)
  end.

Lemma take_eq :
  forall {A} n (s : DS A),
    take n s = match n with
               | O => 0
               | S n => app s (take n (rem s))
               end.
Proof.
  destruct n; reflexivity.
Qed.

Global Add Parametric Morphism A n : (take n)
       with signature @Oeq (DS A) ==> @Oeq (DS A)
         as take_morph.
Proof.
  induction n; auto; intros ?? Heq; simpl.
  autorewrite with cpodb.
  rewrite Heq at 1.
  rewrite (IHn _ (rem y)); auto.
Qed.

(** Definition and specification of [nrem] : [n] applications of [rem].
    It is useful to show the productivity of stream functions.
    A function [f] of a stream [xs] is producive/length-preserving if
    for all n, [is_cons (nrem n xs)] implies [is_cons (n_rem n (f xs))].
 *)
Section Nrem.

Context {A : Type}.

Fixpoint nrem (n : nat) (xs : DS A) : DS A :=
  match n with
  | O => xs
  | S n => nrem n (rem xs)
  end.

Lemma nrem_S : forall n (xs : DS A),
    nrem (S n) xs = nrem n (rem xs).
Proof.
  trivial.
Qed.

(** On prend True pour n = 0 afin de simplifier les cas de base dans
    les preuves d'InftyProof (voir [exp_n] par exemple). *)
Definition is_ncons (n : nat) (xs : DS A) : Prop :=
  match n with
  | O => True
  | S n => is_cons (nrem n xs)
  end.

Lemma nrem_inf :
  forall (s : DS A), (forall n, is_ncons n s) -> infinite s.
Proof.
  cofix Cof; intros * Hc.
  constructor.
  - apply (Hc 1).
  - apply Cof.
    intros []; simpl; auto.
    apply (Hc (S (S n))).
Qed.

Lemma inf_nrem :
  forall (s : DS A), infinite s -> forall n, is_ncons n s.
Proof.
  intros * Hf n.
  revert dependent s.
  induction n as [|[]]; intros; inversion Hf; simpl; auto.
  apply IHn; auto.
Qed.

Lemma nrem_inf_iff :
  forall (s : DS A), (forall n, is_ncons n s) <-> infinite s.
Proof.
  split; auto using nrem_inf, inf_nrem.
Qed.

Lemma is_consn_DS_const :
  forall (c : A) n,
    is_cons (nrem n (DS_const c)).
Proof.
  induction n; simpl; rewrite DS_const_eq, ?rem_cons; auto.
Qed.

Lemma is_ncons_DS_const :
  forall (c : A) n,
    is_ncons n (DS_const c).
Proof.
  induction n as [|[]]; simpl; auto; rewrite DS_const_eq, ?rem_cons; auto.
Qed.

Lemma nrem_rem :
  forall (s : DS A) n,
    nrem n (rem s) == rem (nrem n s).
Proof.
  intros.
  revert s.
  induction n; simpl; auto.
Qed.

Lemma is_ncons_S :
  forall (s : DS A) n,
    is_ncons (S n) s -> is_ncons n s.
Proof.
  induction n as [|[]]; simpl; auto.
  rewrite nrem_rem; auto.
Qed.

Lemma is_ncons_SS :
  forall n (xs : DS A),
    is_ncons (S (S n)) xs <-> is_ncons (S n) (rem xs).
Proof.
  destruct n; simpl; split; auto.
Qed.

Lemma is_ncons_is_cons :
  forall (s : DS A) n,
    is_ncons (S n) s -> is_cons s.
Proof.
  induction n; simpl; auto.
  rewrite nrem_rem.
  intro.
  now apply IHn, rem_is_cons.
Qed.

Lemma nrem_eq_compat : forall n (s t:DS A), s==t -> nrem n s == nrem n t.
Proof.
  induction n; simpl; auto.
Qed.

Global Add Parametric Morphism n : (nrem n)
       with signature (@Oeq (DS A)) ==> (@Oeq (DS A)) as nrem_eq_compat_morph.
Proof.
  exact (@nrem_eq_compat n).
Qed.

Global Add Parametric Morphism n : (is_ncons n)
       with signature (@Oeq (DS A)) ==> iff as is_ncons_morph.
Proof.
  unfold is_ncons.
  intros * H.
  destruct n; now rewrite ?H.
Qed.

End Nrem.

Lemma nrem_map :
  forall {A B} (f : A -> B) n xs,
    nrem n (map f xs) == map f (nrem n xs).
Proof.
  induction n; simpl; intros; auto.
  rewrite rem_map; auto.
Qed.

Module Alt_inf.
  (** example of usage *)
  Definition alt : DS bool := FIXP _ (CONS true @_ MAP negb).
  Lemma alt_inf : infinite alt.
  Proof.
    apply nrem_inf.
    induction n as [|[]]; simpl; auto.
    - unfold alt.
      rewrite FIXP_eq.
      autorewrite with cpodb; auto.
    - unfold alt in *.
      rewrite FIXP_eq.
      autorewrite with cpodb.
      rewrite nrem_map; auto.
  Qed.
End Alt_inf.


(** ** Lifting stream predicates & functions to environment of streams *)

Section ENV.

Context {I : Type}.
Context {SI : I -> Type}.

Definition all_cons (env : DS_prod SI) : Prop :=
  forall x, is_cons (env x).

Lemma all_cons_eq_compat :
  forall (env env' : DS_prod SI),
    all_cons env ->
    env == env' ->
    all_cons env'.
Proof.
  unfold all_cons.
  intros * Hi Heq x.
  now rewrite <- PROJ_simpl, <- Heq, PROJ_simpl.
Qed.

Global Add Parametric Morphism : all_cons
       with signature @Oeq (@DS_prod I SI) ==> iff
         as all_cons_morph.
Proof.
  split; intros; eapply all_cons_eq_compat; eauto.
Qed.

Definition all_infinite (env : DS_prod SI) : Prop :=
  forall x, infinite (env x).

Lemma all_infinite_eq_compat :
  forall (env env' : DS_prod SI),
    all_infinite env ->
    env == env' ->
    all_infinite env'.
Proof.
  unfold all_infinite.
  intros * Hi Heq x.
  now rewrite <- PROJ_simpl, <- Heq, PROJ_simpl.
Qed.

Global Add Parametric Morphism : all_infinite
       with signature @Oeq (@DS_prod I SI) ==> iff
         as all_inf_morph.
Proof.
  split; intros; eapply all_infinite_eq_compat; eauto.
Qed.

Lemma all_infinite_all_cons :
  forall env, all_infinite env -> all_cons env.
Proof.
  intros env Inf x; specialize (Inf x); now inversion Inf.
Qed.

Lemma all_infinite_le_eq :
  forall env env', env <= env' -> all_infinite env -> env == env'.
Proof.
  intros * Hle Inf; apply Oprodi_eq_intro; intro i.
  apply infinite_le_eq; auto; apply Hle.
Qed.

(** Couper la tête d'un environnement *)
Definition REM_env : DS_prod SI -C-> DS_prod SI := DMAPi (fun _ => REM _).

Lemma REM_env_eq :
  forall env i, REM_env env i = rem (env i).
Proof.
  reflexivity.
Qed.

Lemma REM_env_bot : REM_env 0 == 0.
Proof.
  apply Oprodi_eq_intro; intro.
  apply rem_eq_bot.
Qed.

Lemma REM_env_inf :
  forall env,
    all_infinite env ->
    all_infinite (REM_env env).
Proof.
  intros * Hinf x.
  rewrite REM_env_eq.
  specialize (Hinf x).
  now inversion Hinf.
Qed.

Lemma rem_env_eq_compat :
  forall X Y, X == Y -> REM_env X == REM_env Y.
Proof.
  intros.
  apply Oprodi_eq_intro; intro x.
  now rewrite 2 REM_env_eq, <- 2 PROJ_simpl, H.
Qed.

(** [REM_env] itéré *)
Fixpoint nrem_env (n : nat) : DS_prod SI -C-> DS_prod SI :=
  match n with
  | O => ID _
  | S n => REM_env @_ nrem_env n
  end.

Lemma nrem_env_0 : forall X, nrem_env 0 X = X.
Proof.
  reflexivity.
Qed.

Lemma nrem_rem_env :
  forall k X, nrem_env k (REM_env X) == REM_env (nrem_env k X).
Proof.
  induction k; auto; intros; simpl.
  autorewrite with cpodb.
  rewrite IHk; auto.
Qed.

Lemma nrem_env_inf :
  forall n X,
    all_infinite X ->
    all_infinite (nrem_env n X).
Proof.
  induction n; simpl; intros * HH; auto.
  apply REM_env_inf, IHn, HH.
Qed.

(** Prendre la tête dans env1, la queue dans env2 *)
Definition APP_env : DS_prod SI -C-> DS_prod SI -C-> DS_prod SI.
  apply curry, Dprodi_DISTR; intro i.
  exact ((APP _ @2_ (PROJ _ i @_ FST _ _)) (PROJ _ i @_ SND _ _)).
Defined.

Lemma APP_env_eq :
  forall env1 env2 i,
    APP_env env1 env2 i = APP _ (env1 i) (env2 i).
Proof.
  reflexivity.
Qed.

Lemma app_rem_env :
  forall s, APP_env s (REM_env s) == s.
Proof.
  intros.
  apply Oprodi_eq_intro; intro x.
  now rewrite APP_env_eq, REM_env_eq, APP_simpl, app_rem.
Qed.

Lemma rem_app_env :
  forall X Y, all_cons X -> REM_env (APP_env X Y) == Y.
Proof.
  intros * Hc.
  apply Oprodi_eq_intro; intro x.
  rewrite REM_env_eq, APP_env_eq, APP_simpl, rem_app; auto.
Qed.

Lemma app_app_env :
  forall X Y Z, APP_env (APP_env X Y) Z == APP_env X Z.
Proof.
  intros.
  apply Oprodi_eq_intro; intro x.
  rewrite 2 APP_env_eq, 2 APP_simpl, app_app; auto.
Qed.

Lemma APP_env_bot : APP_env 0 0 == 0.
Proof.
  intros.
  apply Oprodi_eq_intro; intro.
  now rewrite APP_env_eq, APP_simpl, app_eq_bot.
Qed.

Lemma app_env_cons :
  forall X Y, all_cons X -> all_cons (APP_env X Y).
Proof.
  intros * Hc i.
  apply is_cons_app, Hc.
Qed.

Lemma app_env_inf :
  forall X Y, all_cons X -> all_infinite Y -> all_infinite (APP_env X Y).
Proof.
  intros * Hc Hinf i.
  rewrite APP_env_eq, APP_simpl.
  eapply is_cons_elim in Hc as (?&?& ->).
  rewrite app_cons.
  constructor; auto.
  now rewrite rem_cons.
Qed.

(** Couper les queues *)
Definition FIRST_env : DS_prod SI -C-> DS_prod SI := DMAPi (fun _ => FIRST _).

Lemma FIRST_env_eq :
  forall X x, (FIRST_env X) x = first (X x).
Proof.
  reflexivity.
Qed.

Lemma first_env_eq_compat :
  forall X Y, X == Y -> FIRST_env X == FIRST_env Y.
Proof.
  intros * Heq.
  apply Oprodi_eq_intro; intro x.
  now rewrite 2 FIRST_env_eq, <- 2 PROJ_simpl, Heq.
Qed.

Lemma first_app_env :
  forall X Y, FIRST_env (APP_env X Y) == FIRST_env X.
Proof.
  intros.
  apply Oprodi_eq_intro; intro x.
  now rewrite FIRST_env_eq, APP_env_eq, APP_simpl, first_app_first.
Qed.

Lemma app_app_first_env :
  forall X Y, APP_env (FIRST_env X) Y == APP_env X Y.
Proof.
  intros.
  apply Oprodi_eq_intro; intro i.
  rewrite APP_env_eq, FIRST_env_eq.
  apply app_app_first.
Qed.


(** Un prédicat co-inductif pour décrire l'égalité d'environnements.
    Plus facile à manipuler dans les preuves mais nécessite souvent
    une hypothèse [all_infinite X] *)
Section Env_eq.

  CoInductive env_eq : DS_prod SI -> DS_prod SI -> Prop :=
  | Ee :
    forall X Y,
      env_eq (REM_env X) (REM_env Y) ->
      FIRST_env X == FIRST_env Y ->
      env_eq X Y.

  Lemma Oeq_env_eq : forall X Y, X == Y -> env_eq X Y.
  Proof.
    cofix Cof; intros.
    apply Ee; auto.
    - apply Cof.
      now rewrite H.
    - now rewrite H.
  Qed.

  Lemma env_eq_Oeq : forall X Y, env_eq X Y -> X == Y.
  Proof.
    intros * Heq.
    apply Oprodi_eq_intro; intro i.
    apply DS_bisimulation_allin1
      with (R := fun U V => exists X Y, env_eq X Y
                                /\ U == X i /\ V == Y i).
    3: eauto.
    { intros * ? Eq1 Eq2.
      setoid_rewrite <- Eq1.
      setoid_rewrite <- Eq2.
      auto. }
    clear.
    intros U V Hc (X & Y & Heq & Hu & Hv).
    inversion_clear Heq as [?? He Hf Eq1 Eq2].
    (* rewrite Eq1, Eq2 in Hf. *)
    split.
    - apply Oprodi_eq_elim with (i := i) in Hf.
      now rewrite Hu, Hv, <- 2 FIRST_env_eq.
    - exists (REM_env X), (REM_env Y); split; auto.
      now rewrite Hu, Hv.
  Qed.

  Lemma env_eq_ok : forall X Y, X == Y <-> env_eq X Y.
  Proof.
    split; auto using Oeq_env_eq, env_eq_Oeq.
  Qed.

  Global Add Parametric Morphism : env_eq
         with signature @Oeq (DS_prod SI) ==> @Oeq (DS_prod SI) ==> iff
           as env_eq_morph.
  Proof.
    intros * Eq1 * Eq2.
    split; intros Heq%env_eq_ok; apply env_eq_ok; eauto.
  Qed.

End Env_eq.


(** Extract a (min(n, length s))-prefix of all streams s *)
Fixpoint take_env n (env : DS_prod SI) : DS_prod SI :=
  match n with
  | O => 0
  | S n => APP_env env (take_env n (REM_env env))
  end.

Global Add Parametric Morphism n : (take_env n)
       with signature @Oeq (DS_prod SI) ==> @Oeq (DS_prod SI)
         as take_env_morph.
Proof.
  induction n; auto; intros ?? Heq; simpl.
  rewrite Heq at 1.
  rewrite (IHn _ (REM_env y)); auto.
  now rewrite Heq.
Qed.

Lemma take_env_1 : forall X, take_env 1 X = FIRST_env X.
Proof.
  reflexivity.
Qed.

Lemma take_1 : forall A (x : DS A), take 1 x = first x.
Proof.
  reflexivity.
Qed.

Lemma take_env_eq :
  forall n X x, take_env n X x = take n (X x).
Proof.
  induction n; simpl; intros; auto.
  now rewrite APP_env_eq, IHn, REM_env_eq.
Qed.

Lemma take_env_Oeq :
  forall X Y, (forall n, take_env n X == take_env n Y) -> X == Y.
Proof.
  intros * Ht.
  apply Oprodi_eq_intro; intro i.
  eapply DS_bisimulation_allin1 with
    (R := fun U V => forall n, take n U == take n V).
  3: now intro n; rewrite <- 2 take_env_eq, <- 2 PROJ_simpl, Ht.
  { intros * ? Eq1 Eq2.
    setoid_rewrite <- Eq1.
    setoid_rewrite <- Eq2.
    eauto. }
  clear; intros U V Hc Ht.
  split.
  - rewrite <- 2 take_1; auto.
  - intro n.
    destruct (@is_cons_elim _ U) as (u & U' & Hu).
    { destruct Hc; auto.
      apply first_is_cons.
      rewrite <- take_1, Ht, take_1.
      now apply is_cons_first. }
    destruct (@is_cons_elim _ V) as (v & V' & Hv).
    { destruct Hc; auto.
      apply first_is_cons.
      rewrite <- take_1, <- Ht, take_1.
      now apply is_cons_first. }
    specialize (Ht (S n)).
    rewrite 2 (take_eq (S n)), Hu, Hv, 2 rem_cons, 2 app_cons in *.
    now apply Con_eq_simpl in Ht as [].
Qed.

(** on peut éliminer [REM_env (APP_env X Y)] s'il est sous un [APP_env X] *)
Lemma app_rem_take_env :
  forall n X Y,
    APP_env X (take_env n (REM_env (APP_env X Y))) == APP_env X (take_env n Y).
Proof.
  intros.
  apply Oprodi_eq_intro; intro i.
  repeat rewrite ?APP_env_eq, ?REM_env_eq, ?take_env_eq.
  apply DS_bisimulation_allin1 with
    (R := fun U V =>
            U == V
            \/ exists X Y,
              U == app X (take n (rem (app X Y)))
              /\ V == app X (take n Y)).
  3: right; exists (X i), (Y i); auto.
  { intros * ? Eq1 Eq2.
    setoid_rewrite <- Eq1.
    setoid_rewrite <- Eq2.
    eauto. }
  clear.
  intros U V Hc [Heq | (X & Y & Hu & Hv)].
  { setoid_rewrite Heq; auto. }
  destruct (@is_cons_elim _ X) as (x & X' & Hx).
  { destruct Hc; eapply app_is_cons; [rewrite <- Hu| rewrite <- Hv]; auto. }
  rewrite Hx, app_cons, rem_app in Hu; auto.
  rewrite Hx, app_cons in Hv.
  split.
  - rewrite Hu, Hv; auto.
  - setoid_rewrite Hu.
    setoid_rewrite Hv.
    auto.
Qed.

End ENV.


(** ** First definition of zip using three functions *)
(* Section Tim. *)

(*   Context {A B D : Type}. *)
(*   Variable bop : A -> B -> D. *)

(*   (* let zip_f2 (ff, a, sa') b sb' = Cons ((a, b), lazy (ff sa' sb')) *) *)
(*   Definition zip_f2 : (DS A -C-> DS B -C-> DS D) -C-> A -O-> DS A -C-> B -O-> DS B -C-> DS D. *)
(*     apply ford_fcont_shift. *)
(*     intro a. *)
(*     apply curry. *)
(*     apply ford_fcont_shift. *)
(*     intro b. *)
(*     apply curry. *)
(*     match goal with *)
(*     | |- _ (_ (Dprod ?pl ?pr) _) => *)
(*       pose (f :=  FST _ _ @_ (FST pl pr)); *)
(*       pose (sa := SND _ _ @_ (FST pl pr)); *)
(*       pose (sb := SND pl pr) *)
(*     end. *)
(*     apply (fcont_comp (CONS (bop a b))). *)
(*     eapply fcont_comp3. exact f. apply ID. exact sa. exact sb. *)
(*   Defined. *)

(*   (* let zip_f1 (ff, sb) a sa' = ds_case (zip_f2 (ff, a, sa')) sb *) *)
(*   Definition zip_f1 : (DS A -C-> DS B -C-> DS D) -C-> DS B -C-> A -O-> DS A -C-> DS D. *)
(*     eapply fcont_comp. 2:apply zip_f2. *)
(*     apply curry. *)
(*     apply ford_fcont_shift. *)
(*     intro a. *)
(*     apply curry. *)
(*     match goal with *)
(*     | |- _ (_ (Dprod ?pl ?pr) _) => *)
(*       pose (z2 := FST _ _ @_ (FST pl pr)); *)
(*       pose (sb := SND _ _ @_ (FST pl pr)); *)
(*       pose (sa := SND pl pr) *)
(*     end. *)
(*     apply (fcont_comp2 (DSCASE B D)). 2:exact sb. *)
(*     apply fcont_ford_shift in z2. *)
(*     exact (fcont_comp2 (z2 a) (ID _) sa). *)
(*   Defined. *)

(*   (* let zipf ff sa sb = ds_case (zip_f1 (ff, sb)) sa *) *)
(*   Definition zipf_ : (DS A -C-> DS B -C-> DS D) -C-> DS A -C-> DS B -C-> DS D. *)
(*     apply curry. *)
(*     apply curry. *)
(*     match goal with *)
(*     | |- _ (_ (Dprod ?pl ?pr) _) => *)
(*       pose (f := FST _ _ @_ (FST pl pr)); *)
(*       pose (U := SND _ _ @_ (FST pl pr)); *)
(*       pose (V := SND pl pr) *)
(*     end. *)
(*     apply (fcont_comp2 (DSCASE A D)). *)
(*     2:exact U. *)
(*     apply (fcont_comp2 zip_f1). *)
(*     exact f. *)
(*     exact V. *)
(*   Defined. *)

(*   (* let rec zip sa sb = zipf zip sa sb *) *)
(*   Definition zip_ : (DS A -C-> DS B -C-> DS D) := FIXP _ zipf_. *)

(* End Tim. *)


(** ** ZIP primitive, combines elements of two streams *)
Section Zip.

  Context {A B D : Type}.
  Variable bop : A -> B -> D.

  Definition zipf : (DS A -C-> DS B -C-> DS D) -C-> DS A -C-> DS B -C-> DS D.
    apply curry.
    apply curry.
    apply (fcont_comp2 (DSCASE A D)).
    2:exact (SND _ _ @_ (FST _ _)).
    apply ford_fcont_shift. intro a.
    apply curry.
    apply (fcont_comp2 (DSCASE B D)).
    2:exact (SND _ _ @_ (FST _ _)).
    (* alternative : *)
    (* pose (V:= SND (Dprod (DS A -C-> DS B -C-> DS D) (DS A)) (DS B) @_ *)
    (*               (FST (Dprod (Dprod (DS A -C-> DS B -C-> DS D) (DS A)) (DS B)) (DS A))). *)
    (* 2:exact V. *)
    apply ford_fcont_shift. intro b.
    apply curry.
    apply (fcont_comp (CONS (bop a b))).
    eapply fcont_comp3.
    2: apply ID.
    (* ff *)
    exact (FST _ _ @_ (FST _ _ @_ (FST _ _ @_ (FST _ _)))).
    (* sa *)
    exact (SND _ _ @_ (FST _ _)).
    (* sb *)
    exact (SND _ _).
  Defined.

  Lemma zipf_eq : forall f u U v V,
      zipf f (cons u U) (cons v V) = cons (bop u v) (f U V).
  Proof.
    intros.
    unfold zipf.
    setoid_rewrite DSCASE_simpl.
    do 2 setoid_rewrite DScase_cons.
    now simpl.
  Qed.

  Definition ZIP : (DS A -C-> DS B -C-> DS D) := FIXP _ zipf.

  Lemma zip_cons : forall u U v V,
      ZIP (cons u U) (cons v V) == cons (bop u v) (ZIP U V).
  Proof.
    intros.
    unfold ZIP.
    rewrite FIXP_eq at 1.
    now rewrite zipf_eq.
  Qed.

  Hint Rewrite zip_cons : cpodb. (* !! local à la section *)

  (*  (* XXX notations de debug *) *)
  (* Notation "⋅FST" := (FST _ _) (at level 80, right associativity). *)
  (* Notation "⋅SND" := (SND _ _) (at level 80, right associativity). *)
  (* Notation "⋅DPROD" := (Dprod _ _) (at level 80, right associativity). *)
  (* Notation "⋅curry" := (@curry _ _ _) (at level 80, right associativity). *)
  (* Notation "⋅ford_fcont_shift" := (@ford_fcont_shift _ _ _) (at level 80, right associativity). *)
  (* (* XXX *) *)

  Lemma zipf_bot1 :
    forall f xs, zipf f 0 xs == 0.
  Proof.
    intros.
    unfold zipf.
    now autorewrite with cpodb.
  Qed.

  Lemma zipf_bot2 :
    forall f xs, zipf f xs 0 == 0.
  Proof.
    intros.
    unfold zipf.
    autorewrite with cpodb.
    rewrite DScase_bot2; auto.
    simpl; intros.
    now rewrite DScase_bot_eq.
  Qed.

  Lemma zipf_is_cons :
    forall f xs ys,
      is_cons (zipf f xs ys) -> is_cons xs /\ is_cons ys.
  Proof.
    intros * Hic; split.
    now apply DScase_is_cons in Hic.
    apply is_cons_elim in Hic as (a&s&Hic).
    apply DScase_eq_cons_elim in Hic as (b&s'&Hxs&Hic).
    now apply symmetry, is_cons_eq_compat, DScase_is_cons in Hic.
  Qed.

  Lemma zip_bot1 : forall xs, ZIP 0 xs == 0.
  Proof.
    intros.
    unfold ZIP.
    rewrite FIXP_eq.
    apply zipf_bot1.
  Qed.

  Lemma zip_bot2 : forall xs, ZIP xs 0 == 0.
  Proof.
    intros.
    unfold ZIP.
    rewrite FIXP_eq.
    apply zipf_bot2.
  Qed.

  Lemma zip_is_cons :
    forall xs ys,
      is_cons (ZIP xs ys) -> is_cons xs /\ is_cons ys.
  Proof.
    unfold ZIP.
    intros * Hic.
    rewrite FIXP_eq in Hic.
    now apply zipf_is_cons in Hic.
  Qed.

  Lemma is_cons_zip :
    forall xs ys,
      is_cons xs /\ is_cons ys ->
      is_cons (ZIP xs ys).
  Proof.
    intros * [Cx Cy].
    apply is_cons_elim in Cx as (?&?&->).
    apply is_cons_elim in Cy as (?&?&->).
    now rewrite zip_cons.
  Qed.

  Lemma rem_zip :
    forall xs ys,
      rem (ZIP xs ys) == ZIP (rem xs) (rem ys).
  Proof.
    intros.
    apply DS_bisimulation_allin1 with
      (R := fun U V => exists xs ys,
                U == rem (ZIP xs ys)
                /\ V == ZIP (rem xs) (rem ys)); eauto 4.
    - intros * (?&?&?&?) Eq1 Eq2.
      setoid_rewrite <- Eq1.
      setoid_rewrite <- Eq2.
      eauto.
    - clear.
      intros U V Hc (xs & ys & Hu & Hv).
      assert (is_cons xs /\ is_cons ys) as [Cx Cy].
      { destruct Hc as [Hc|Hc].
        + rewrite Hu in Hc.
          now apply rem_is_cons, zip_is_cons in Hc.
        + rewrite Hv in Hc.
          apply zip_is_cons in Hc as []; auto using rem_is_cons. }
      apply is_cons_elim in Cx as (?& xs' & Hx), Cy as (?& ys' & Hy).
      rewrite Hx, Hy in *; clear Hx Hy.
      assert (is_cons xs' /\ is_cons ys') as [Cx Cy].
      { destruct Hc as [Hc|Hc].
        + rewrite Hu in Hc.
          rewrite zip_cons, rem_cons in Hc.
          now apply zip_is_cons in Hc.
        + rewrite Hv in Hc.
          rewrite 2 rem_cons in Hc.
          now apply zip_is_cons in Hc. }
      apply is_cons_elim in Cx as (?& xs'' & Hx), Cy as (?& ys'' & Hy).
      rewrite Hx, Hy, Hu, Hv in *.
      split; autorewrite with cpodb; auto.
      exists xs', ys'.
      rewrite Hu, Hv, Hx, Hy; now autorewrite with cpodb.
  Qed.

  Lemma first_zip :
    forall xs ys,
      first (ZIP xs ys)
      == ZIP (first xs) (first ys).
  Proof.
    intros.
    apply DS_bisimulation_allin1 with
      (R := fun U V => exists xs ys,
                U == first (ZIP xs ys)
                /\ V == ZIP (first xs) (first ys)); eauto 4.
    - intros * (?&?&?&?) Eq1 Eq2.
      setoid_rewrite <- Eq1.
      setoid_rewrite <- Eq2.
      eauto.
    - clear.
      intros U V Hc (xs & ys & Hu & Hv).
      assert (is_cons xs /\ is_cons ys) as [Cx Cy].
      { destruct Hc as [Hc|Hc].
        + rewrite Hu in Hc.
          now apply first_is_cons, zip_is_cons in Hc.
        + rewrite Hv in Hc.
          apply zip_is_cons in Hc as []; auto. }
      apply is_cons_elim in Cx as (?& xs' & Hx), Cy as (?& ys' & Hy).
      rewrite Hx, Hy in *; clear Hx Hy.
      repeat rewrite first_cons, zip_cons, ?zip_bot1 in *.
      split; autorewrite with cpodb; eauto.
      exists 0,0.
      rewrite Hu, Hv, 2 first_eq_bot, rem_cons, zip_bot1; auto.
  Qed.

  Lemma zip_app:
    forall (xs1 xs2 : DS A) (ys1 ys2 : DS B),
      app (ZIP xs1 ys1) (ZIP xs2 ys2)
      == ZIP (app xs1 xs2) (app ys1 ys2).
  Proof.
    intros.
    apply DS_bisimulation_allin1 with
      (R := fun U V =>
              U == V
              \/
                exists X1 X2 Y1 Y2,
                  (U == app (ZIP X1 Y1) (ZIP X2 Y2)
                   /\ V == ZIP (app X1 X2) (app Y1 Y2))).
    3: eauto 12.
    { intros * ? Eq1 Eq2.
      setoid_rewrite <- Eq1.
      now setoid_rewrite <- Eq2.
    }
    clear.
    intros U V Hc [HH | (X1 & X2 & Y1 & Y2 & Hu & Hv)].
    { setoid_rewrite HH. eauto. }
    setoid_rewrite Hu.
    setoid_rewrite Hv.
    destruct (@is_cons_elim _ X1) as (vx1 & X1' & Hx1).
    { destruct Hc.
      - eapply proj1, zip_is_cons, app_is_cons.
        now rewrite <- Hu.
      - eapply app_is_cons, proj1, zip_is_cons.
        now rewrite <- Hv. }
    destruct (@is_cons_elim _ Y1) as (vy1 & Y1' & Hy1).
    { destruct Hc.
      - eapply proj2, zip_is_cons, app_is_cons.
        now rewrite <- Hu.
      - eapply app_is_cons, proj2, zip_is_cons.
        now rewrite <- Hv. }
    setoid_rewrite Hx1.
    setoid_rewrite Hy1.
    rewrite zip_cons, 3 app_cons, zip_cons, first_cons.
    auto.
  Qed.

  Lemma zip_uncons :
    forall xs ys r rs,
      ZIP xs ys == cons r rs ->
      exists x xs' y ys',
        xs == cons x xs'
        /\ ys == cons y ys'
        /\ rs == ZIP xs' ys'
        /\ r = bop x y.
  Proof.
    intros * HZ.
    assert (is_cons xs /\ is_cons ys) as [Hcx Hcy].
    { eapply zip_is_cons; rewrite HZ; auto. }
    apply is_cons_elim in Hcx as (x & xs' & Hx).
    apply is_cons_elim in Hcy as (y & ys' & Hy).
    rewrite Hx, Hy, zip_cons in HZ.
    apply Con_eq_simpl in HZ as [].
    now exists x,xs',y,ys'.
  Qed.

  Lemma zip_inf :
    forall U V,
      infinite U ->
      infinite V ->
      infinite (ZIP U V).
  Proof.
    clear.
    intros * InfU InfV.
    remember (ZIP U V) as t eqn:Ht.
    apply Oeq_refl_eq in Ht.
    revert InfU InfV Ht. revert t U V.
    cofix Cof; intros.
    destruct InfU as [Cu], InfV as [Cv].
    apply is_cons_elim in Cu as (?& U' & Hu), Cv as (?& V' & Hv).
    rewrite Hu, Hv, rem_cons, zip_cons in *.
    constructor.
    - now rewrite Ht.
    - eapply Cof with (U := U') (V := V'); auto.
      now rewrite Ht, rem_cons.
  Qed.

  Lemma inf_zip :
    forall s t,
      infinite (ZIP s t) ->
      infinite s /\ infinite t.
  Proof.
    intros * Hf.
    split; revert Hf; revert s t.
    all: cofix Cof; intros * Hf; inversion_clear Hf as [Hc Hinf].
    all: apply zip_is_cons in Hc as [(?&?& Hs)%is_cons_elim (?&?&Ht)%is_cons_elim].
    all: rewrite rem_zip in Hinf; constructor; eauto using cons_is_cons.
  Qed.

  Lemma zip_const :
    forall a V,
      ZIP (DS_const a) V == MAP (bop a) V.
  Proof.
    intros.
    eapply DS_bisimulation_allin1 with
      (R := fun U V => exists xs,
                U == ZIP (DS_const a) xs
                /\ V == MAP (bop a) xs).
    3: eauto.
    - intros ????(?&?&?&?)??. repeat esplit; eauto.
    - clear. intros U V Hc (xs & Hu & Hv).
      assert (is_cons xs) as Hcx.
      { rewrite Hu, Hv in Hc.
        destruct Hc as [Hc|Hc].
        + apply zip_is_cons in Hc; tauto.
        + apply map_is_cons in Hc; tauto. }
      apply is_cons_elim in Hcx as (vx & xs' & Hx).
      rewrite Hx in Hu, Hv.
      rewrite MAP_map, map_eq_cons in Hv.
      rewrite DS_const_eq, zip_cons in Hu.
      setoid_rewrite Hu.
      setoid_rewrite Hv.
      split.
      + autorewrite with cpodb; auto.
      + exists xs'. rewrite 2 rem_cons; auto.
  Qed.

End Zip.

Global Hint Rewrite @zip_cons @zip_bot1 @zip_bot2 : cpodb.

Lemma zip_ext :
  forall A B C (f g : A -> B -> C),
    (forall a b, f a b = g a b) ->
    forall x y, ZIP f x y == ZIP g x y.
Proof.
  intros * Hfg x y.
  apply DS_bisimulation_allin1
    with (R := fun U V => exists x y, U == ZIP f x y /\ V == ZIP g x y); eauto 4.
  { intros * ? Eq1 Eq2.
    setoid_rewrite <- Eq1.
    setoid_rewrite <- Eq2.
    auto. }
  clear - Hfg; intros U V Hc (xs & ys & Hu & Hv).
  destruct (@is_cons_elim _ xs) as (x & xs' & Hxs).
  { rewrite Hu, Hv in Hc.
    now destruct Hc as [?%zip_is_cons|?%zip_is_cons]. }
  destruct (@is_cons_elim _ ys) as (y & ys' & Hys).
  { rewrite Hu, Hv in Hc.
    now destruct Hc as [?%zip_is_cons|?%zip_is_cons]. }
  rewrite Hxs, Hys, zip_cons in *.
  split;[|exists xs', ys']; now rewrite Hu, Hv, ?first_cons, ?rem_cons, ?Hfg.
Qed.


(** ** Facts about zip, map  *)

(* TODO: on pourrait avoir le même pour (map f xs)  *)
Lemma zip_map :
    forall A B C (op : A -> B -> C) B' (f : B' -> B),
    forall xs ys,
      ZIP op xs (map f ys) == ZIP (fun x y => op x (f y)) xs ys.
Proof.
  intros.
  eapply DS_bisimulation with
    (R := fun U V => exists xs ys,
              U == ZIP op xs (map f ys)
              /\ V == ZIP (fun x y => op x (f y)) xs ys).
  4: eauto.
  - intros ????(?&?&?&?)??. repeat esplit; eauto.
  - clear xs ys. intros x y Hcons (xs & ys & Hx & Hy).
    destruct Hcons as [Hcons|Hcons];
      rewrite Hx,Hy in *;
      apply zip_is_cons in Hcons as (Hc1 & Hc2);
      try apply map_is_cons in Hc2;
      apply is_cons_elim in Hc1 as (?&?&->);
      apply is_cons_elim in Hc2 as (?&?&->);
      now autorewrite with cpodb.
  - clear xs ys. intros x y Hcons (xs & ys & Hx & Hy).
    destruct Hcons as [Hcons|Hcons];
      exists (rem xs), (rem ys);
      rewrite Hx,Hy in *;
      apply zip_is_cons in Hcons as (Hc1 & Hc2);
      try apply map_is_cons in Hc2;
      apply is_cons_elim in Hc1 as (?&?&->);
      apply is_cons_elim in Hc2 as (?&?&->);
      now autorewrite with cpodb.
Qed.

Lemma map_zip :
  forall A B C D (op : A -> B -> C) (f : C -> D),
    forall xs ys,
      ZIP (fun x y => f (op x y)) xs ys == map f (ZIP op xs ys).
Proof.
  intros.
  eapply DS_bisimulation with
    (R := fun U V => exists xs ys,
              U == ZIP (fun x y => f (op x y)) xs ys
              /\ V == map f (ZIP op xs ys)).
  4: eauto.
  - intros ????(?&?&?&?)??. repeat esplit; eauto.
  - clear xs ys. intros x y Hcons (xs & ys & Hx & Hy).
    destruct Hcons as [Hcons|Hcons];
      rewrite Hx,Hy in *;
      [| apply map_is_cons in Hcons];
      apply zip_is_cons in Hcons as (Hc1 & Hc2);
      apply is_cons_elim in Hc1 as (?&?&->);
      apply is_cons_elim in Hc2 as (?&?&->);
      now autorewrite with cpodb.
  - clear xs ys. intros x y Hcons (xs & ys & Hx & Hy).
    destruct Hcons as [Hcons|Hcons];
      exists (rem xs), (rem ys);
      rewrite Hx,Hy in *;
      [| apply map_is_cons in Hcons];
      apply zip_is_cons in Hcons as (Hc1 & Hc2);
      apply is_cons_elim in Hc1 as (?&?&->);
      apply is_cons_elim in Hc2 as (?&?&->);
      now autorewrite with cpodb.
Qed.

Lemma zip_comm :
  forall A B (f : A -> A -> B) xs ys,
    (forall x y, f x y = f y x) ->
    ZIP f xs ys == ZIP f ys xs.
Proof.
  intros * Fcomm.
  eapply DS_bisimulation_allin1 with
    (R := fun U V => exists xs ys,
              U == ZIP f xs ys
              /\ V == ZIP f ys xs); eauto 4.
  - intros * (?&?&?&?) Eq1 Eq2.
    setoid_rewrite <- Eq1.
    setoid_rewrite <- Eq2.
    eauto.
  - clear - Fcomm.
    intros U V Hc (xs & ys & Hu & Hv).
    assert (is_cons xs /\ is_cons ys) as [Hcx Hcy].
    { rewrite Hu, Hv in Hc.
      destruct Hc as [Hc|Hc]; apply zip_is_cons in Hc; tauto. }
    apply is_cons_elim in Hcx as (vx & xs' & Hx).
    apply is_cons_elim in Hcy as (vy & ys' & Hy).
    rewrite Hx, Hy, zip_cons in *.
    setoid_rewrite Hu.
    setoid_rewrite Hv.
    split.
    + autorewrite with cpodb; auto.
    + exists xs',ys'. rewrite 2 rem_cons; auto.
Qed.

Lemma zip_zip :
  forall D1 D2 D3 D4 D5,
  forall (f:D1->D4->D5) (g:D2->D3->D4) U V W,
    ZIP f U (ZIP g V W) == ZIP (fun h w => h w) (ZIP (fun x y => fun z => (f x (g y z))) U V) W.
Proof.
  intros.
  apply DS_bisimulation_allin1 with
    (R := fun R L => exists U V W,
              R == ZIP f U (ZIP g V W)
              /\ L ==  ZIP (fun h w => h w) (ZIP (fun x y z => f x (g y z)) U V) W).
  3: eauto.
  - intros ????(?&?&?&?) E1 E2.
    setoid_rewrite <- E1.
    setoid_rewrite <- E2.
    eauto.
  - clear.
    intros R L Hc (U & V & W & Hr & Hl).
    destruct Hc as [Hc | Hc].
    + apply is_cons_elim in Hc as (r & rs & Hrs).
      rewrite Hrs in *.
      apply symmetry, zip_uncons in Hr as (?&?&?&?& Hu & Hz &?&?).
      apply zip_uncons in Hz as (?&?&?&?& Hv & Hw &?&?).
      rewrite Hu, Hv, Hw, 2 zip_cons in *; subst.
      setoid_rewrite Hl.
      setoid_rewrite Hrs.
      rewrite 2 (rem_cons (f x _)).
      split.
      autorewrite with cpodb; auto.
      eauto 7.
    + apply is_cons_elim in Hc as (l & ls & Hls).
      rewrite Hls in *.
      apply symmetry, zip_uncons in Hl as (?&?&?&?& Hz & Hw &?&?).
      apply zip_uncons in Hz as (?&?&?&?& Hu & Hv &?&?).
      rewrite Hu, Hv, Hw, 2 zip_cons in *; subst.
      setoid_rewrite Hls.
      setoid_rewrite Hr.
      rewrite 2 (rem_cons (f _ _)).
      split.
      autorewrite with cpodb; auto.
      eauto 7.
Qed.

(** ** ZIP3 synchronizes three streams *)
Section Zip3.

  Context {A B C D : Type}.
  Variable op : A -> B -> C -> D.

  Definition ZIP3 : DS A -C-> DS B -C-> DS C -C-> DS D :=
    curry (ZIP (fun f x => f x) @_ uncurry (ZIP (fun x y => op x y))).

  (* another possible definition of ZIP3: *)
  (* intros. apply curry, curry. *)
  (* refine ((ZIP (fun '(x,y) z => op x y z) @2_ _) (SND _ _)). *)
  (* exact ((ZIP pair @2_ FST _ _ @_ FST _ _) (SND _ _ @_ FST _ _)). *)

  Lemma zip3_eq :
    forall xs ys zs,
      ZIP3 xs ys zs = ZIP (fun f x => f x) (ZIP (fun x y => op x y) xs ys) zs.
  Proof.
    reflexivity.
  Qed.

  Lemma zip3_cons :
    forall u U v V w W,
      ZIP3 (cons u U) (cons v V) (cons w W)
      == cons (op u v w) (ZIP3 U V W).
  Proof.
    intros.
    now rewrite 2 zip3_eq, 2 zip_cons.
  Qed.

  Lemma rem_zip3 :
    forall xs ys zs,
      rem (ZIP3 xs ys zs) == ZIP3 (rem xs) (rem ys) (rem zs).
  Proof.
    clear.
    intros.
    now rewrite 2 zip3_eq, 2 rem_zip.
  Qed.

  Lemma first_zip3 :
    forall xs ys zs,
      first (ZIP3 xs ys zs)
      == ZIP3 (first xs) (first ys) (first zs).
  Proof.
    intros.
    now rewrite 2 zip3_eq, 2 first_zip.
  Qed.

  Lemma zip3_is_cons :
    forall xs ys zs,
      is_cons (ZIP3 xs ys zs) ->
      is_cons xs /\ is_cons ys /\ is_cons zs.
  Proof.
    intros *.
    rewrite zip3_eq.
    now intros [Hc % zip_is_cons] % zip_is_cons.
  Qed.

  Lemma is_cons_zip3 :
    forall xs ys zs,
      is_cons xs /\ is_cons ys /\ is_cons zs ->
      is_cons (ZIP3 xs ys zs).
  Proof.
    intros * (Cx & Cy & Cz).
    rewrite zip3_eq.
    auto using is_cons_zip.
  Qed.

  Lemma zip3_bot1 :
    forall ys zs,
      ZIP3 0 ys zs == 0.
  Proof.
    intros.
    now rewrite zip3_eq, 2 zip_bot1.
  Qed.

End Zip3.


(** Une ancienne version de take, avec prédicat d'infinité *)
Module Inf_Take.

Context {A : Type}.

(** *** Take the prefix of length [n] from an infinite stream *)
Fixpoint take (n : nat) (s : DS A) (si : infinite s) : DS A :=
  match n with
  | O => 0
  | S n => match si with
            inf_intro _ rsi => app s (take n (rem s) rsi)
          end
  end.

Lemma take_1 : forall (s : DS A) (si : infinite s),
    take 1 s si == first s.
Proof.
  simpl.
  destruct si.
  now rewrite app_bot_right_first.
Qed.

Lemma take_le :
  forall n (s : DS A) (si : infinite s),
    take n s si <= take (S n) s si.
Proof.
  induction n; intros.
  - apply Dbot.
  - destruct si, si.
    apply app_mon_right, IHn.
Qed.

Lemma _take_eq :
  forall n (xs : DS A) xsi ys ysi,
    xs == ys ->
    take n xs xsi == take n ys ysi.
Proof.
  induction n; simpl; intros * Heq; auto.
  destruct xsi, ysi.
  rewrite Heq, IHn at 1; auto.
Qed.

Lemma take_eq :
  forall n (xs : DS A) xsi ys,
    xs == ys ->
    exists ysi,
    take n xs xsi == take n ys ysi.
Proof.
  intros.
  exists (proj1 (infinite_morph H) xsi).
  now apply _take_eq.
Qed.

Lemma take_cons :
  forall n x (xs : DS A) xsi,
    take (S n) (cons x xs) xsi == cons x (take n xs (cons_infinite _ _ _ xsi)).
Proof.
  intros.
  simpl; destruct xsi.
  rewrite app_cons.
  apply cons_eq_compat, _take_eq; auto.
Qed.

Lemma take_app :
  forall n (xs ys : DS A) inf inf2,
    take (S n) (app xs ys) inf == app xs (take n ys inf2).
Proof.
  intros.
  simpl; destruct inf.
  rewrite app_app.
  eapply app_eq_compat, _take_eq, rem_app, app_is_cons; eauto.
Qed.

Lemma rem_take :
  forall n (xs : DS A) inf inf2,
    rem (take (S n) xs inf) == take n (rem xs) inf2.
Proof.
  intros.
  simpl; destruct inf.
  rewrite rem_app, _take_eq; auto.
Qed.

Lemma n_eq :
  forall (s t : DS A) (si : infinite s) (ti : infinite t),
    (forall n, take n s si == take n t ti) ->
    s == t.
Proof.
  intros * Hn.
  eapply DS_bisimulation_allin1
    with (R := fun U V => exists Ui Vi, (forall n, take n U Ui == take n V Vi)).
  3: esplit; eauto.
  - intros ???? (I1 & I2 & HUV) HU HV.
    setoid_rewrite (_take_eq _ _ _ _ (proj1 (infinite_morph HU) I1) HU) in HUV.
    setoid_rewrite (_take_eq _ _ _ _ (proj1 (infinite_morph HV) I2) HV) in HUV.
    eauto.
  - clear. intros U V Hc (I1 & I2 & Hf).
    split.
    + specialize (Hf 1). now rewrite 2 take_1 in Hf.
    + destruct I1 as (?& I1), I2 as (? & I2).
      exists I1, I2. setoid_rewrite <- rem_take; auto.
Qed.

End Inf_Take.


(** *** Extract the [n] first elements (Con/Eps) of a stream *)
Fixpoint take_list {A} (n : nat) (xs : DS A) : list (option A) :=
  match n with
  | O => []
  | S n =>  match xs with
           | Eps xs => None :: take_list n xs
           | Con x xs => Some x :: take_list n xs
           end
  end.
