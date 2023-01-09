(** * Extension of the Cpo library *)

From Coq Require Import Morphisms List.
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

(* TODO: utiliser plus souvent ? *)
(** like [fixp_ind], keeping in mind we are starting from 0 so
      we can use x <= F x in the reasoning *)
Lemma fixp_ind_le : forall (D:cpo)(F:D -m> D)(P:D->Type),
    admissible P -> P 0 -> (forall x, P x -> x <= F x -> P (F x)) -> P (fixp F).
Proof.
  intros; unfold fixp.
  apply X; intros.
  assert (forall n, iter_ F n <= iter_ F (S n)).
  intro m; induction m; simpl; auto.
  induction n; simpl; firstorder.
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

Definition all_infinite {I} {SI : I -> Type} (p : DS_prod SI) : Prop :=
  forall x, infinite (p x).

Lemma all_infinite_Oeq_compat :
  forall I (SI : I -> Type) (env env' : DS_prod SI),
    all_infinite env ->
    env == env' ->
    all_infinite env'.
Proof.
  unfold all_infinite.
  intros * Hi Heq x.
  now rewrite <- PROJ_simpl, <- Heq, PROJ_simpl.
Qed.

Global Add Parametric Morphism I SI : all_infinite
    with signature @Oeq (@DS_prod I SI) ==> iff
      as all_inf_morph.
Proof.
  split; intros; eapply all_infinite_Oeq_compat; eauto.
Qed.

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
  rewrite Hx in Hu, Hv.
  (* repeat rewrite rem_cons, map_eq_cons in *. *)
  split; [| exists (cons b xs)];
    rewrite Hu, Hv;
    now repeat rewrite ?map_eq_cons, ?rem_cons.
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

  Lemma is_cons_zip :
    forall xs ys,
      is_cons xs /\ is_cons ys ->
      is_cons (ZIP xs ys).
  Proof.
    intros * [Cx Cy].
    apply is_cons_elim in Cx as (?&?&->).
    apply is_cons_elim in Cy as (?&?&->).
    now rewrite zip_eq.
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
    rewrite Hu, Hv, rem_cons, zip_eq in *.
    constructor.
    - now rewrite Ht.
    - eapply Cof with (U := U') (V := V'); auto.
      now rewrite Ht, rem_cons.
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
      rewrite DS_const_eq, zip_eq in Hu.
      setoid_rewrite Hu.
      setoid_rewrite Hv.
      split.
      + autorewrite with cpodb; auto.
      + exists xs'. rewrite 2 rem_cons; auto.
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
    rewrite Hx, Hy, zip_eq in *.
    setoid_rewrite Hu.
    setoid_rewrite Hv.
    split.
    + autorewrite with cpodb; auto.
    + exists xs',ys'. rewrite 2 rem_cons; auto.
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


(** ** The cpo of n-uplets. *)
Section Nprod.

Context { D : cpo }.

Fixpoint nprod (n : nat) : cpo :=
  match n with
  | O => D
  | 1 => D
  | S n => Dprod D (nprod n)
  end.

(** nprod concatenation *)
Definition nprod_app : forall {n p}, nprod n -C-> nprod p -C-> nprod (n + p).
  induction n as [|[]]; intro p.
  - exact (CURRY _ _ _ (SND _ _ )).
  - destruct p.
    + exact (CTE _ _).
    + exact (PAIR _ _).
  - apply curry.
    exact ((PAIR _ _ @2_ (FST _ _ @_ FST _ _))
             ((IHn p @2_ (SND _ _ @_ FST _ _)) (SND _ _))).
Defined.
Opaque nprod_app.

(** extract the first element if 0 < n, [d] otherwise *)
Definition nprod_fst d {n} : nprod n -C-> D :=
  match n with
  | O => CTE _ _ d
  | 1 => ID _
  | (S n) => FST _ _
  end.

(** throw away the first element *)
Definition nprod_skip {n} : nprod (S n) -C-> nprod n :=
  match n with
  | O => 0
  | (S n) => SND _ _
  end.

Lemma nprod_fst_app :
  forall m n (mp : nprod (S m)) (np : nprod n) d,
    nprod_fst d (nprod_app mp np) = nprod_fst d mp.
Proof.
  destruct m, n; auto.
Qed.

(** extract the k-th element if k < n, [d] otherwise *)
Fixpoint get_nth (k : nat) (d : D) {n} : nprod n -C-> D :=
  match k with
  | O => nprod_fst d
  | S k => match n return nprod n -C-> _ with
          | O => CTE _ _ d
          | S _ => get_nth k d @_ nprod_skip
          end
  end.

Lemma get_nth_Oeq_compat :
  forall n k d (np np' : nprod n),
    np == np' ->
    get_nth k d np == get_nth k d np'.
Proof.
  induction n; simpl; intros * Heq.
  - destruct k; auto.
  - destruct n, k; auto.
    + unfold get_nth. now rewrite Heq.
    + simpl. autorewrite with cpodb. auto.
Qed.

Global Add Parametric Morphism n k d : (get_nth k d)
       with signature @Oeq (nprod n) ==> @Oeq D as get_nth_compat_morph.
Proof.
  exact (get_nth_Oeq_compat n k d).
Qed.

Lemma get_nth_skip :
  forall {n} (np : nprod (S n)) k d,
    get_nth k d (nprod_skip np) = get_nth (S k) d np.
Proof.
  induction k; auto.
Qed.

Lemma nprod_app_nth1 :
  forall m n (mp : nprod m) (np : nprod n) k d,
    k < m ->
    get_nth k d (nprod_app mp np) = get_nth k d mp.
Proof.
  induction m; intros * Hk.
  - inversion Hk.
  - destruct k; simpl.
    + now unshelve setoid_rewrite nprod_fst_app.
    + autorewrite with cpodb.
      rewrite <- (IHm n _ np); auto with arith.
      destruct m; simpl; auto; lia.
Qed.

Lemma nprod_app_nth2 :
  forall m n (mp : nprod m) (np : nprod n) k d,
    k >= m ->
    get_nth k d (nprod_app mp np) = get_nth (k-m) d np.
Proof.
  induction m; intros * Hk.
  - simpl in *. autorewrite with cpodb; repeat f_equal; auto with arith.
  - destruct k; simpl.
    + lia.
    + destruct m, n; auto with arith.
      * destruct k; simpl; now autorewrite with cpodb.
      * rewrite <- (IHm _ (nprod_skip mp)); auto with arith.
      * rewrite <- (IHm _ (nprod_skip mp)); auto with arith.
      * rewrite <- (IHm _ (nprod_skip mp)); auto with arith.
Qed.

Lemma nprod_app_Oeq_compat :
  forall {n p} (p1 p2 : nprod n) (p3 p4 : nprod p),
    p1 == p2 ->
    p3 == p4 ->
    nprod_app p1 p3 == nprod_app p2 p4.
Proof.
  induction n; auto.
Qed.

Fixpoint nprod_const (c : D) n {struct n} : nprod n :=
  match n with
  | O => 0
  | S n =>
      match n return nprod n -> nprod (S n) with
      | O => fun _ => c
      | S m => fun np => (c, np)
      end (nprod_const c n)
  end.

Lemma get_nth_const :
  forall c n k d,
    k < n ->
    get_nth k d (nprod_const c n) = c.
Proof.
  induction n as [|[]]; intros * Hk.
  - inversion Hk.
  - destruct k; auto; lia.
  - destruct k; auto.
    rewrite <- get_nth_skip, IHn; auto with arith.
Qed.

Lemma get_nth_err :
  forall k d n (np : nprod n),
    (n <= k)%nat ->
    get_nth k d np = d.
Proof.
  induction k; simpl; intros * Hn.
  - inversion Hn; subst. now simpl.
  - destruct n; cbn; auto.
    setoid_rewrite get_nth_skip.
    apply IHk; auto with arith.
Qed.


(** A Forall predicate for n-uplets  *)
Section Forall_Nprod.

Variable P : D -> Prop.

Definition forall_nprod {n} (np : nprod n) : Prop.
  induction n as [|[]]; simpl in *.
  - exact True.
  - exact (P np).
  - exact (P (fst np) /\ IHn (snd np)).
Defined.

Lemma forall_nprod_skip :
  forall {n} (np : nprod (S n)),
    forall_nprod np ->
    forall_nprod (nprod_skip np).
Proof.
  intros * Hnp.
  destruct n.
  - now simpl.
  - destruct Hnp. auto.
Qed.

Lemma k_forall_nprod :
  forall {n} (np : nprod n),
    (forall k d, k < n -> P (get_nth k d np)) ->
    forall_nprod np.
Proof.
  induction n as [|[]]; intros * Hk.
  - constructor.
  - unshelve eapply (Hk O _); auto.
  - split.
    + unshelve eapply (Hk O); auto with arith.
      destruct np; auto.
    + eapply IHn; intros.
      change (snd np) with (nprod_skip np).
      rewrite get_nth_skip; auto with arith.
Qed.

Lemma k_forall_nprod_def :
  forall {n} (np : nprod n) d,
    (forall k, k < n -> P (get_nth k d np)) ->
    forall_nprod np.
Proof.
  induction n as [|[]]; intros *  Hk.
  - constructor.
  - unshelve eapply (Hk O _); auto.
  - split.
    + unshelve eapply (Hk O); auto with arith.
    + eapply IHn; intros; eauto.
      change (snd np) with (nprod_skip np).
      rewrite get_nth_skip; auto with arith.
Qed.

Lemma forall_nprod_k :
  forall {n} (np : nprod n),
    forall_nprod np ->
    (forall k d, k < n -> P (get_nth k d np)).
Proof.
  induction n as [|[]]; intros * Hk.
  - lia.
  - intros.
    assert (k = O) by lia; subst.
    now simpl in Hk.
  - intros.
    specialize (IHn (nprod_skip np)).
    setoid_rewrite get_nth_skip in IHn.
    destruct k. { destruct Hk; auto. }
    apply IHn; auto using forall_nprod_skip with arith.
Qed.

Lemma forall_nprod_k_def :
  forall {n} (np : nprod n) d,
    P d ->
    forall_nprod np ->
    (forall k, P (get_nth k d np)).
Proof.
  intros * Hp Hf k.
  destruct (Nat.lt_ge_cases k n).
  - apply forall_nprod_k; auto.
  - rewrite get_nth_err; auto.
Qed.

Lemma forall_nprod_k_iff :
  forall {n} (np : nprod n),
    forall_nprod np <-> (forall k d, k < n -> P (get_nth k d np)).
Proof.
  split; auto using forall_nprod_k, k_forall_nprod.
Qed.

Lemma forall_nprod_app :
  forall {n m} (np : nprod n) (mp : nprod m),
    forall_nprod np ->
    forall_nprod mp ->
    forall_nprod (nprod_app np mp).
Proof.
  intros * Hnp Hmp.
  eapply k_forall_nprod.
  intros * Hk.
  destruct (Nat.lt_ge_cases k n).
  - rewrite nprod_app_nth1; auto using forall_nprod_k.
  - rewrite nprod_app_nth2; auto.
    apply forall_nprod_k; auto; lia.
Qed.

Lemma app_forall_nprod :
  forall {n m} (np : nprod n) (mp : nprod m),
    forall_nprod (nprod_app np mp) ->
    forall_nprod np
    /\ forall_nprod mp.
Proof.
  setoid_rewrite forall_nprod_k_iff.
  intros * Hf; split; intros k d Hk.
  - specialize (Hf k d).
    rewrite nprod_app_nth1 in Hf; auto with arith.
  - specialize (Hf (n + k) d).
    rewrite nprod_app_nth2, Nat.add_comm,
      Nat.add_sub in Hf; auto with arith.
    apply Hf; lia.
Qed.

Lemma forall_nprod_const :
  forall {n} c,
    P c ->
    forall_nprod (nprod_const c n).
Proof.
  intros.
  apply k_forall_nprod; intros.
  now rewrite get_nth_const.
Qed.

Global Add Parametric Morphism n
  (P_compat:  Morphisms.Proper (@Oeq D ==> iff) P)
  : (forall_nprod)
    with signature Oeq (O := nprod n) ==> iff
      as forall_nprod_morph.
Proof.
  unfold Morphisms.Proper, Morphisms.respectful, Basics.impl in *.
  intros * Heq.
  rewrite 2 forall_nprod_k_iff.
  split; intros.
  eapply P_compat; rewrite <- ?Heq; auto.
  eapply P_compat; rewrite ?Heq; auto.
Qed.

End Forall_Nprod.

Lemma forall_nprod_impl :
  forall (P Q : D -> Prop),
    (forall x, P x -> Q x) ->
    forall {n} (np : nprod n),
      forall_nprod P np ->
      forall_nprod Q np.
Proof.
  induction n as [|[]]; intros * Hf; auto.
  - now simpl in *; auto.
  - destruct Hf.
    split; auto.
    now apply IHn.
Qed.

Lemma forall_nprod_and :
  forall (P Q : D -> Prop),
    forall {n} (np : nprod n),
    forall_nprod P np ->
    forall_nprod Q np ->
    forall_nprod (fun x => P x /\ Q x) np.
Proof.
  induction n as [|[]]; intros * Hp Hq; auto.
  - constructor; auto.
  - inversion Hp. inversion Hq.
    constructor; auto; now apply IHn.
Qed.


(** From n-uplets, build lists of length n *)
Section List_of_nprod.

Import ListNotations.

Definition list_of_nprod_ {n} (np : nprod n) : list D.
  induction n as [|[]].
  - exact [].
  - exact [np].
  - exact (fst np :: IHn (snd np)).
Defined.

(* FIXME: la version explicite n'est pas vraiment plus lisible... *)
Fixpoint list_of_nprod {n} (np : nprod n) {struct n} : list D :=
  match n return nprod n -> list D with
  | O => fun _ => []
  | S n => fun np =>
            let l := list_of_nprod (nprod_skip np) in
            match n return nprod (S n) -> list D with
            | O => fun np => np :: l
            | _ => fun np => fst np :: l
            end np
  end np.

Lemma list_of_nprod_length :
  forall {n} (np : nprod n),
    length (list_of_nprod np) = n.
Proof.
  induction n as [|[]]; auto.
  intros []; simpl.
  f_equal. apply IHn.
Qed.

Lemma list_of_nprod_app :
  forall {n m} (np : nprod n) (mp : nprod m),
    list_of_nprod (nprod_app np mp) = list_of_nprod np ++ list_of_nprod mp.
Proof.
  induction n as [|[]]; intros; auto.
  - destruct m; auto.
  - destruct np as (p,np).
    specialize (IHn _ np mp).
    simpl; f_equal; auto.
Qed.

Lemma list_of_nprod_nth :
  forall {n} (np : nprod n) k d,
    nth k (list_of_nprod np) d = get_nth k d np.
Proof.
  induction n as [|[]]; intros.
  - destruct k; auto.
  - destruct k as [|[]]; auto.
  - destruct k; auto.
    apply IHn; auto with arith.
Qed.

Lemma list_of_nprod_nth_error :
  forall n (np : nprod n) k d x,
    nth_error (list_of_nprod np) k = Some x ->
    get_nth k d np = x.
Proof.
  intros * Hn.
  apply nth_error_nth with (d := d) in Hn as Hnt.
  now rewrite list_of_nprod_nth in Hnt.
Qed.

Lemma forall_nprod_Forall :
  forall P {n} (np : nprod n),
    forall_nprod P np ->
    Forall P (list_of_nprod np).
Proof.
  induction n as [|[]]; intros * Hf.
  - constructor.
  - constructor; auto.
  - inversion Hf.
    constructor; auto.
    now apply IHn.
Qed.

Lemma Forall_forall_nprod :
  forall P {n} (np : nprod n),
    Forall P (list_of_nprod np) ->
    forall_nprod P np.
Proof.
  induction n as [|[]]; intros * Hf.
  - constructor.
  - inversion Hf. auto.
  - inversion Hf.
    constructor; auto.
    now apply IHn.
Qed.

End List_of_nprod.


(** Lifting functions over n-uplets *)
Section Lift_nprod.

Fixpoint lift (F : D -C-> D) {n} : nprod n -C-> nprod n :=
  match n with
  | O => ID _
  | S n =>
      match n return nprod n -C-> nprod n -> nprod (S n) -C-> nprod (S n) with
      | O => fun _ => F
      | S _ => fun fn => PROD_map F fn
      end (@lift F n)
  end.

Definition llift {A} (F : D -C-> A -C-> D) {n} :
  nprod n -C-> A -C-> nprod n.
  (* match n with *)
  (* | O => CTE _ _ *)
  (* | S n => *)
  (*     match n return nprod n -C-> D -C-> nprod n -> nprod (S n) -C-> D -C-> nprod (S n) with *)
  (*     | O => fun _ => F *)
  (*     | S _ => fun fn => curry ((PAIR _ _ @2_ *)
  (*                              ((F @2_ (FST _ _ @_ FST _ _)) (SND _ _))) *)
  (*                             ((fn @2_ (SND _ _ @_ FST _ _)) (SND _ _))) *)
  (*     end (@llift _ F n) *)
  (*        end. *)
  induction n as [|[]].
  - apply CTE.
  - apply F.
  - apply curry.
    apply (fcont_comp2 (PAIR _ _)).
    exact ((F @2_ (FST _ _ @_ FST _ _)) (SND _ _)).
    exact ((IHn @2_ (SND _ _ @_ FST _ _)) (SND _ _)).
Defined.

Lemma llift_simpl :
  forall A F n d u U,
    @llift A F (S (S n)) (u, U) d = (F u d, @llift A F (S n) U d).
Proof.
  trivial.
Qed.

Lemma llift_nth :
  forall A (F : D -C-> A -C-> D) a,
  forall {n} (np : nprod n) k d,
    k < n ->
    get_nth k d (llift F np a) = F (get_nth k d np) a.
Proof.
  induction n as [|[]]; intros; auto; try lia.
  - destruct k; simpl; auto; lia.
  - destruct np.
    rewrite llift_simpl.
    destruct k; auto.
    rewrite <- get_nth_skip.
    setoid_rewrite <- IHn; auto with arith.
Qed.

Definition lift2
  (F : D -C-> D -C-> D) {n} :
  nprod n -C-> nprod n -C-> nprod n.
  induction n as [|[]].
  - exact 0. (* ? *)
  - exact F.
  - apply curry.
    apply (fcont_comp2 (PAIR _ _)).
    exact ((F @2_ (FST _ _ @_ FST _ _ )) (FST _ _ @_ SND _ _ )).
    exact ((IHn @2_ (SND _ _ @_ FST _ _ )) (SND _ _ @_ SND _ _ )).
Defined.

Lemma lift2_simpl :
  forall F n u U v V,
    @lift2 F (S (S n)) (u, U) (v, V) = (F u v, @lift2 F (S n) U V).
Proof.
  trivial.
Qed.

Lemma lift2_nth :
  forall F {n} (np np' : nprod n) k d,
    k < n ->
    get_nth k d (lift2 F np np') = F (get_nth k d np) (get_nth k d np').
Proof.
  induction n as [|[]]; intros; auto; try lia.
  - destruct k; simpl; auto; lia.
  - destruct np, np'.
    rewrite lift2_simpl.
    destruct k; auto.
    rewrite <- 3 get_nth_skip, <- IHn; auto with arith.
Qed.

Lemma forall_nprod_lift2 :
  forall (F : D -C-> D -C-> D),
  forall (P : D -> Prop),
    (forall x y, P x -> P y -> P (F x y)) ->
    forall {n} (np np' : nprod n),
      forall_nprod P np ->
      forall_nprod P np' ->
      forall_nprod P (lift2 F np np').
Proof.
  intros f P Hf.
  induction n as [|[]]; intros * H H'; auto.
  simpl in *; auto.
  destruct np,np',H,H'.
  rewrite lift2_simpl.
  split; simpl in *; auto .
  now apply IHn.
Qed.

Lemma forall_nprod_llift :
  forall A (F : D -C-> A -C-> D) d,
  forall (P Q : D -> Prop),
    (forall x, Q x -> P (F x d)) ->
    forall {n} (np : nprod n),
      forall_nprod Q np ->
      forall_nprod P (llift F np d).
Proof.
  intros A F d ?? Hf.
  induction n as [|[]]; intros * H; auto.
  simpl in *; auto.
  destruct np, H.
  rewrite llift_simpl.
  split; simpl in *; auto .
  now apply IHn.
Qed.

(* pas envie d'importer tout Common pour ça... *)
Ltac inv H := inversion H; clear H; subst.
Ltac simpl_Forall :=
  repeat
    (match goal with
     | H: Forall2 _ _ (_ :: _) |- _ => inv H
     end; subst).

Lemma Forall2_lift2 :
  forall A (F : D -C-> D -C-> D)
    (P Q : A -> D -> Prop),
    (forall a x y, P a x -> P a y -> Q a (F x y)) ->
    forall {n} (l1 l2 : nprod n) l,
      Forall2 P l (list_of_nprod l1) ->
      Forall2 P l (list_of_nprod l2) ->
      Forall2 Q l (list_of_nprod (lift2 F l1 l2)).
Proof.
  intros * PQ.
  induction n as [|[]]; intros * Hl1 Hl2.
  - simpl in *. now inversion Hl1.
  - simpl in *. simpl_Forall; auto.
  - inv Hl1. inv Hl2.
    constructor.
    + simpl; eauto.
    + apply IHn; auto.
Qed.

Lemma Forall2_llift :
  forall A B b (F : D -C-> B -C-> D)
    (P Q : A -> D -> Prop),
    (forall a x, P a x -> Q a (F x b)) ->
    forall {n} (l1 : nprod n) (l : list A),
      Forall2 P l (list_of_nprod l1) ->
      Forall2 Q l (list_of_nprod (llift F l1 b)).
Proof.
  intros * PQ.
  induction n as [|[]]; intros * Hl1.
  - simpl in *. now inversion Hl1.
  - simpl in *. simpl_Forall; auto.
  - inv Hl1.
    constructor.
    + simpl; eauto.
    + apply IHn; auto.
Qed.

Lemma Forall_llift :
  forall A a (F : D -C-> A -C-> D)
    (P Q : D -> Prop),
    (forall x, P x -> Q (F x a)) ->
    forall {n} (np : nprod n),
      Forall P (list_of_nprod np) ->
      Forall Q (list_of_nprod (llift F np a)).
Proof.
  intros * PQ.
  induction n as [|[]]; intros * Hp.
  - constructor.
  - inversion_clear Hp.
    constructor; auto.
  - inversion_clear Hp; constructor.
    + apply PQ; auto.
    + apply IHn; auto.
Qed.

End Lift_nprod.

End Nprod.
