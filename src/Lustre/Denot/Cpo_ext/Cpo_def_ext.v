From Coq Require Import Morphisms List.
From Velus.Lustre.Denot.Cpo Require Import Cpo_def.

Import ListNotations.

(** * Extension of the Cpo library *)

(** ** Cpo_def.v  *)


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
  Fst_simpl Snd_simpl
  PAIR_simpl Pair_simpl
  ID_simpl Id_simpl
  PROJ_simpl
  PROD_map_simpl
  : cpodb.

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

Lemma fcont_app_le_compat : forall (D1 D2:cpo) (f g : D1 -c> D2) (x y : D1),
    f <= g -> x <= y -> f x <= g y.
Proof.
  intros.
  apply Ole_trans with (f y); auto.
Qed.

(* TODO: comprendre pourquoi c'est si laborieux *)
Lemma fcont_le_compat3 :
  forall (D1 D2 D3 D4:cpo) (f : D1-C->D2-C->D3-C->D4)
    (a b : D1) (c d : D2) (x y : D3),
    a <= b -> c <= d -> x <= y -> f a c x <= f b d y.
Proof.
  intros.
  apply Ole_trans with (f a c y); auto.
  apply fcont_le_elim.
  apply Ole_trans with (f a d).
  - now apply (@fcont_monotonic _ _ (f a) c d).
  - apply (@fcont_le_elim _ _ (f a) (f b)).
    now apply (@fcont_monotonic _ _ f a b).
Qed.

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

Global Hint Rewrite fcont_app2_simpl : cpodb.

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
