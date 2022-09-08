(** * Extension of the Cpo library *)

From Coq Require Import Morphisms.
From Velus Require Import Lustre.Denot.Cpo.

(* simplification by rewriting during proofs, usage:
   [autorewrite with cpodb] *)
Create HintDb cpodb.

Global Hint Rewrite
     CURRY_simpl UNCURRY_simpl
     Curry_simpl Uncurry_simpl
     fcont_comp_simpl
     fcont_comp2_simpl
     fcont_comp3_simpl
     FST_simpl SND_simpl
     CONS_simpl Cons_simpl
     Fst_simpl Snd_simpl
     PAIR_simpl Pair_simpl
     ID_simpl Id_simpl
     DSCASE_simpl DScase_cons
     first_cons
     REM_simpl rem_cons
     app_cons
     filter_eq_cons map_eq_cons
     rem_bot map_bot filter_bot
     PROJ_simpl
     PROD_map_simpl
  : cpodb.

(** ** Cpo_def.v  *)
Definition fcont_comp4 {D1 D2 D3 D4 D5 D6:cpo}
           (F:D2 -c> D3 -C->D4-C->D5-C->D6)(f:D1-c> D2)(g:D1 -c> D3)(h:D1-c>D4)(i:D1-c>D5): D1-c>D6
  := (AP _ _ @2_ ((F @3_ f) g h)) i.

Infix "@4_" := fcont_comp4 (at level 35, right associativity) : O_scope.

Lemma fcont_comp4_simpl : forall (D1 D2 D3 D4 D5 D6:cpo)
           (F:D2 -c> D3 -C->D4-C->D5-C->D6)(f:D1-c> D2)(g:D1 -c> D3)(h:D1-c>D4)(i:D1-c>D5) (x:D1),
                (F@4_ f) g h i x = F (f x) (g x) (h x) (i x).
trivial.
Qed.

Definition fcont_comp5 {D1 D2 D3 D4 D5 D6 D7:cpo}
           (F:D2 -c> D3 -C->D4-C->D5-C->D6-C->D7)(f:D1-c> D2)(g:D1 -c> D3)(h:D1-c>D4)(i:D1-c>D5)(j:D1-c>D6): D1-c>D7
  := (AP _ _ @2_ ((F @4_ f) g h i)) j.

Infix "@5_" := fcont_comp5 (at level 35, right associativity) : O_scope.

Lemma fcont_comp5_simpl : forall (D1 D2 D3 D4 D5 D6 D7:cpo)
           (F:D2 -c> D3 -C->D4-C->D5-C->D6-C->D7)(f:D1-c> D2)(g:D1 -c> D3)(h:D1-c>D4)(i:D1-c>D5)(j:D1-c>D6) (x:D1),
                (F@5_ f) g h i j x = F (f x) (g x) (h x) (i x) (j x).
trivial.
Qed.

Global Hint Rewrite fcont_comp4_simpl fcont_comp5_simpl : cpodb.

(* sub-typing of continuous functions *)
Definition fcont_sub : forall (D1 D2 D3 D4:cpo),
    (D2 -C-> D4) -> (D3 -C-> D1) -> (D1 -C-> D2) -C-> (D3 -C-> D4).
  intros * g f.
  exact (curry (g @_ (AP D1 D2 @2_ FST (D1 -C-> D2) D3)
                  (f @_ SND (D1 -C-> D2) D3))).
Defined.

Lemma ford_fcont_shift_simpl :
  forall A D1 D2 (f: A -o> (D1-c> D2)) (x:D1),
    ford_fcont_shift f x = fun a => f a x.
  trivial.
Qed.

Global Hint Rewrite ford_fcont_shift_simpl : cpodb.

Definition fcont_ford_shift (A:Type) (D1 D2:cpo) (f: D1 -c> A -O-> D2) : A -o> (D1-c> D2).
  intro a.
  apply fcont_comp with (2 := f).
  unshelve esplit.
  exists (fun g => g a).
  auto.
  red; auto.
Defined.

Add Parametric Morphism (D1 D2:cpo) : (@fconti_fun D1 D2)
    with signature Oeq (O:=D1-C->D2) ==> Oeq (O:=D1) ==> Oeq (O:=D2)
      as funconti_fun_compat1.
Proof.
  intros f g Hfg x y Hxy.
  rewrite (@ford_eq_elim _ _ f g Hfg x).
  now apply fcont_stable.
Qed.

(* Instance eq_oeq_subrelation (D:cpo): subrelation eq (Oeq (O:=D)). *)
(* intros ???. auto. *)
(* Qed. *)

(* TODO: on ne devrait pas avoir besoin de ce morphisme, il est plus
   faible que le précédent *)
Add Parametric Morphism (D1 D2:cpo)(F:D1-C->D2) : (@fconti_fun D1 D2 F)
    with signature Oeq (O:=D1) ==> Oeq (O:=D2)
      as funconti_fun_compat2.
Proof.
  apply fcont_stable.
Qed.

(** like [fixp_ind], with a stronger hypothesis on arguments
     of F, without having to prove the corresponding admissibility *)
Lemma fixp_inv : forall (D:cpo) (F:D -m> D) (P P' : D -> Prop),
    (forall x, P' x -> P x) ->
    admissible P ->
    P' 0 ->
    (forall x, P' x -> P' (F x)) ->
    P (fixp F).
Proof.
  intros; unfold fixp.
  apply X; intros.
  eapply proj2 with (A := P' (iter (D:=D) F n)).
  induction n; simpl; auto.
  destruct IHn.
  firstorder.
Qed.

Lemma admissible_and :
  forall (D:cpo) (P Q : D -> Prop),
    admissible P ->
    admissible Q ->
    admissible (fun x => P x /\ Q x).
Proof.
  firstorder.
Qed.

(** Prop version of admissibility, under which we can rewrite propositional
    equivalences *)
Definition admissibleP (D : cpo) (P : D -> Prop) :=
  forall f : natO -m> D, (forall n, P (f n)) -> P (lub f).

Fact admissiblePT :
  forall (D : cpo) (P : D -> Prop),
    admissibleP D P ->
    admissible P.
Proof.
  trivial.
Qed.

Global Add Parametric Morphism (D : cpo) : (@admissibleP D)
    with signature pointwise_relation D iff ==> iff
      as admissible_morph.
Proof.
  unfold pointwise_relation, admissibleP.
  intros * Hxy.
  split; intros HH ??; apply Hxy, HH; firstorder.
Qed.

Lemma le_admissible :
  forall (D D':cpo) (f g : D -C-> D'),
    @admissible D (fun s => f s <= g s).
Proof.
  intros ?????.
  setoid_rewrite lub_comp_eq; auto.
Qed.

(** function that ignore its 2nd argument *)
Definition CTE (D1 D2:cpo) : D1 -C-> D2 -C-> D1 := (curry (FST D1 D2)).

Lemma CTE_eq : forall (D1 D2 : cpo) a b, CTE D1 D2 a b = a.
Proof.
  trivial.
Qed.

Global Hint Rewrite CTE_eq : cpodb.

(** *** Continuous version of fcont_app  *)
Definition fcont_app2 {D1 D2 D3:cpo} (f: D1-C-> D2 -C-> D3) (x:D2) : D1 -c> D3 :=
  (f @2_ ID D1) (CTE D2 D1 x).

Infix "<___>" := fcont_app2 (at level 70) : O_scope.

Lemma fcont_app2_simpl : forall (D1 D2 D3:cpo) (f: D1-c> D2 -C-> D3) (x:D1)(y:D2),
            (f <___> y) x = f x y.
trivial.
Qed.

(** *** weaker version of Dmapi *)
Definition wDmapi : forall (I:Type)(Di Dj:I->cpo)(f:forall i, Dprodi Di -m> Dj i),
    Dprodi Di -m> Dprodi Dj.
  intros; exists (fun p i => f i p); red; auto.
Defined.

Lemma wDmapi_simpl : forall (I:Type)(Di Dj:I->cpo)(f:forall i, Dprodi Di -m> Dj i) (p:Dprodi Di) (i:I),
    wDmapi _ _ _ f p i = f i p.
Proof.
  trivial.
Qed.

Global Hint Rewrite wDmapi_simpl : cpodb.

Lemma wDMAPi : forall (I:Type)(Di Dj:I->cpo)(f:forall i, Dprodi Di -c> Dj i),
    Dprodi Di -c> Dprodi Dj.
  intros; exists (wDmapi _ _ _ (fun i => fcontit (f i))).
  red; intros; intro i. rewrite wDmapi_simpl.
  repeat (rewrite Dprodi_lub_simpl).
  apply Ole_trans with (lub (c:=Dj i) (Fcontit (Dprodi Di) (Dj i) (f i) @ h)); eauto.
Defined.


(** *** Some kind of distributivity for Dprodi  *)
Definition Dprodi_distr :
  forall (I:Type) (Di:I->cpo) (D:cpo) (f: Dprodi (fun i => D -C-> Di i)),
    D -m> Dprodi Di.
  intros.
  exists (fun d i => f i d); auto.
Defined.

Definition Dprodi_DISTR :
  forall (I:Type) (Di:I->cpo) (D:cpo) (f: Dprodi (fun i => D -C-> Di i)),
    D -C-> Dprodi Di.
  intros.
  exists (Dprodi_distr I Di D f).
  red; intros; intro i; simpl.
  eapply Ole_trans; eauto.
Defined.

Lemma Dprodi_DISTR_simpl :
  forall (I:Type) (Di:I->cpo) (D:cpo) (f: Dprodi (fun i => D -C-> Di i)) (d : D) (i : I),
    Dprodi_DISTR I Di D f d i = f i d.
Proof.
  trivial.
Qed.

Global Hint Rewrite Dprodi_DISTR_simpl : cpodb.

Lemma FIXP_fixp :
  forall D (F : D -C-> D), FIXP _ F = fixp (fcontit F).
Proof.
  trivial.
Qed.
(* Global Hint Rewrite FIXP_fixp : cpodb. *)

Lemma curry_Curry :
  forall (D1 D2 D3 : cpo) (f:Dprod D1 D2 -c> D3),
    curry f = Curry D1 D2 D3 f.
Proof.
  trivial.
Qed.
Global Hint Rewrite curry_Curry : cpodb.

Add Parametric Morphism (D1 D2 D3 : cpo) : (curry (D1:=D1) (D2:=D2) (D3:=D3))
      with signature Oeq (O:=Dprod D1 D2 -c> D3) ==> Oeq (O:=D1 -c> D2 -C-> D3)
        as curry_eq_compat.
  intros.
  unfold curry.
  now rewrite H.
Qed.

Lemma uncurry_Uncurry :
  forall (D1 D2 D3 : cpo) (f: D1 -c> D2 -C-> D3),
    uncurry f = Uncurry D1 D2 D3 f.
Proof.
  trivial.
Qed.
Global Hint Rewrite uncurry_Uncurry : cpodb.

Add Parametric Morphism (D1 D2 D3 : cpo) : (uncurry (D1:=D1) (D2:=D2) (D3:=D3))
      with signature Oeq (O:=D1 -c> D2 -C-> D3) ==> Oeq (O:=Dprod D1 D2 -c> D3)
        as uncurry_eq_compat.
  intros.
  unfold uncurry.
  now rewrite H.
Qed.

(** ** Cpo_streams_type.v  *)

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
  trivial.
Qed.
Global Hint Rewrite FILTER_filter : cpodb.

Lemma MAP_map :
  forall D1 D2 (F:D1->D2) (s: DS D1), MAP F s = map F s.
Proof.
  trivial.
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
  split.
  (apply Ole_trans with (2 := (DSle_app_first_rem _)); eauto).
  remember (app s (rem s)) as xs. apply Oeq_refl_eq in Heqxs.
  revert dependent s.
  cofix Cof; intros.
  destruct s.
  - constructor; apply Cof.
    now rewrite Heqxs, <- eqEps.
  - rewrite app_cons, rem_cons in Heqxs; eauto.
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
  rewrite Hx in Hu, Hv.
  (* repeat rewrite rem_cons, map_eq_cons in *. *)
  split; [| exists (cons b xs)];
    rewrite Hu, Hv;
    now repeat rewrite ?map_eq_cons, ?rem_cons.
Qed.

Lemma infinite_map :
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


(** ** First definition of zip using three functions *)
Section Tim.

  Context {A B D : Type}.
  Variable bop : A -> B -> D.

  (* let zip_f2 (ff, a, sa') b sb' = Cons ((a, b), lazy (ff sa' sb')) *)
  Definition zip_f2 : (DS A -C-> DS B -C-> DS D) -C-> A -O-> DS A -C-> B -O-> DS B -C-> DS D.
    apply ford_fcont_shift.
    intro a.
    apply curry.
    apply ford_fcont_shift.
    intro b.
    apply curry.
    match goal with
    | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (f :=  FST _ _ @_ (FST pl pr));
      pose (sa := SND _ _ @_ (FST pl pr));
      pose (sb := SND pl pr)
    end.
    apply (fcont_comp (CONS (bop a b))).
    eapply fcont_comp3. exact f. apply ID. exact sa. exact sb.
  Defined.

  (* let zip_f1 (ff, sb) a sa' = ds_case (zip_f2 (ff, a, sa')) sb *)
  Definition zip_f1 : (DS A -C-> DS B -C-> DS D) -C-> DS B -C-> A -O-> DS A -C-> DS D.
    eapply fcont_comp. 2:apply zip_f2.
    apply curry.
    apply ford_fcont_shift.
    intro a.
    apply curry.
    match goal with
    | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (z2 := FST _ _ @_ (FST pl pr));
      pose (sb := SND _ _ @_ (FST pl pr));
      pose (sa := SND pl pr)
    end.
    apply (fcont_comp2 (DSCASE B D)). 2:exact sb.
    apply fcont_ford_shift in z2.
    exact (fcont_comp2 (z2 a) (ID _) sa).
  Defined.

  (* let zipf ff sa sb = ds_case (zip_f1 (ff, sb)) sa *)
  Definition zipf_ : (DS A -C-> DS B -C-> DS D) -C-> DS A -C-> DS B -C-> DS D.
    apply curry.
    apply curry.
    match goal with
    | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (f := FST _ _ @_ (FST pl pr));
      pose (U := SND _ _ @_ (FST pl pr));
      pose (V := SND pl pr)
    end.
    apply (fcont_comp2 (DSCASE A D)).
    2:exact U.
    apply (fcont_comp2 zip_f1).
    exact f.
    exact V.
  Defined.

  (* let rec zip sa sb = zipf zip sa sb *)
  Definition zip_ : (DS A -C-> DS B -C-> DS D) := FIXP _ zipf_.

End Tim.


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

  Lemma zip_eq : forall u U v V,
      ZIP (cons u U) (cons v V) == cons (bop u v) (ZIP U V).
  Proof.
    intros.
    unfold ZIP.
    rewrite FIXP_eq at 1.
    now rewrite zipf_eq.
  Qed.

  Hint Rewrite zip_eq : cpodb. (* !! local à la section *)

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

End Zip.

Global Hint Rewrite @zip_eq @zip_bot1 @zip_bot2 : cpodb.


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


Section Take.

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

End Take.


(** *** Extract the [n] first elements (Con/Eps) of a stream *)
Fixpoint take_list {A} (n : nat) (xs : DS A) : list (option A) :=
  match n with
  | O => nil
  | S n =>  match xs with
           | Eps xs => None :: take_list n xs
           | Con x xs => Some x :: take_list n xs
           end
  end.
