From Coq Require Import Lia List Setoid Morphisms.
Import ListNotations.

From Velus Require Import Common CommonList.

(* TODO: faut-il ajouter ces trucs à Velus.CommonList ? *)


(* TODO: celui-là ne parle même pas de listes *)
Lemma and_impl :
  forall (A B C : Prop),
    (A -> B /\ C) <-> ((A -> B) /\ (A -> C)).
Proof.
  firstorder.
Qed.

Lemma map_eq_nnil : forall A B (f : A -> B) l, l <> [] -> List.map f l <> [].
Proof.
  intros.
  intro Hf; destruct l; [contradiction|].
  discriminate Hf.
Qed.

Lemma map_ignore :
  forall A B (b : B) (l : list A),
    map (fun _ => b) l = repeat b (length l).
Proof.
  induction l; simpl; auto.
Qed.

Lemma tl_length :
  forall A (l : list A),
    length (tl l) = Nat.pred (length l).
Proof.
  now destruct l.
Qed.

Lemma nth_nil :
  forall A n (d : A),
    nth n [] d = d.
Proof.
  destruct n; auto.
Qed.

Lemma hd_nth :
  forall A (l : list A) (d : A),
    nth O l d = hd d l.
Proof.
  destruct l; auto.
Qed.

Lemma tl_nth :
  forall A (l : list A) (d : A) n,
    nth (S n) l d = nth n (tl l) d.
Proof.
  destruct l, n; auto.
Qed.

Lemma map_hd_nth :
  forall A (l : list (list A)) d,
    map (hd d) l = map (fun l0 => nth 0 l0 d) l.
Proof.
  induction l; simpl; f_equal; auto using hd_nth.
Qed.

Lemma map_tl_nth :
  forall A (l : list (list A)) n d,
    map (fun l0 => nth (S n) l0 d) l = map (fun l0 => nth n (tl l0) d) l.
Proof.
  induction l; simpl; f_equal; auto using tl_nth.
Qed.

Lemma list_eq_ext :
  forall A (l1 l2 : list A) d,
    length l1 = length l2 ->
    (forall n, n < length l1 -> nth n l1 d = nth n l2 d) ->
    l1 = l2.
Proof.
  induction l1; simpl; intros * Hl Hn.
  - destruct l2; simpl in *; congruence.
  - destruct l2; try (simpl in *; congruence).
    f_equal.
    + apply (Hn O); auto with arith.
    + eapply IHl1 with d; intros; auto.
      rewrite (Hn (S n)); auto with arith.
Qed.

Lemma list_eq_ext2 :
  forall A (l1 l2 : list A),
    (forall n, nth_error l1 n = nth_error l2 n) ->
    l1 = l2.
Proof.
  induction l1; intros * Hn.
  - destruct l2; simpl in *; auto.
    specialize (Hn O); inv Hn.
  - destruct l2.
    specialize (Hn O); inv Hn.
    f_equal.
    + now injection (Hn O).
    + eapply IHl1; intros; auto.
      apply (Hn (S n)).
Qed.

Lemma Forall3_same_2_3:
  forall A B P (xs: list A) (ys : list B),
    Forall3 P xs ys ys <-> Forall2 (fun x y => P x y y) xs ys.
Proof.
  induction xs as [|x xs IH]; split; intros * H; inv H; constructor; auto.
  rewrite <- IH; auto.
  rewrite IH; auto.
Qed.

Lemma combine_map_2 :
  forall A B C D (f : A -> C -> D) (g : B -> C) xs ys,
    map (fun '(x,y) => f x (g y)) (combine xs ys)
    = map (fun '(x,z) => f x z) (combine xs (map g ys)).
Proof.
  induction xs, ys; simpl; auto.
Qed.

Lemma combine_length' :
  forall A B,
  forall (l : list A) (l' : list B),
    length l = length l' ->
    length (combine l l') = length l.
Proof.
  intros.
  rewrite combine_length.
  lia.
Qed.

Lemma In_list_pair_l :
  forall {A B} (l : list (A*B)) x y,
    In (x,y) l -> In x (map fst l).
Proof.
  induction l; simpl; firstorder; subst; auto.
Qed.

Lemma Forall_In :
  forall {A} (P : A -> Prop) l x,
    Forall P l ->
    In x l ->
    P x.
Proof.
  setoid_rewrite Forall_forall.
  auto.
Qed.

Lemma Forall_impl_inside :
  forall {A} (P Q : A -> Prop) xs,
    (Forall (fun x => P x -> Q x) xs) ->
    Forall P xs ->
    Forall Q xs.
Proof.
  induction xs; auto.
  intros FPQ FP. inv FPQ. inv FP.
  constructor; auto.
Qed.

Lemma Forall_iff :
  forall A (P Q : A -> Prop) l,
    Forall (fun x => P x <-> Q x) l ->
    Forall P l ->
    Forall Q l.
Proof.
  induction l; intros * Pq Hp; auto.
  inversion Hp; inversion Pq; subst.
  constructor; eauto; firstorder.
Qed.

Lemma in_app_weak' :
  forall A (x : A) l l',
    In x l' -> In x (l ++ l').
Proof.
  intros. apply in_app; auto.
Qed.

(* Lemma nth_In' : *)
(*   forall A n (l:list A) (x d : A), *)
(*     n < length l -> *)
(*     nth n l d = x -> *)
(*     In x l. *)
(* Proof. *)
(*   intros. *)
(*   subst. apply nth_In; auto. *)
(* Qed. *)

Lemma Forall2_Forall_eq :
  forall {A B} (P : A -> B -> Prop) a l1 l2,
    Forall (eq a) l1 ->
    Forall2 P l1 l2 ->
    Forall (P a) l2.
Proof.
  induction 2; auto.
  inversion H; subst.
  constructor; auto.
Qed.

Lemma Forall2_Forall3 :
  forall {A B C} (P : A -> B -> Prop) (Q : B -> C -> Prop) xs ys zs,
    Forall2 P xs ys ->
    Forall2 Q ys zs ->
    Forall3 (fun x y z => P x y /\ Q y z) xs ys zs.
Proof.
  intros * Hp Hq.
  revert dependent zs.
  induction Hp; intros; simpl_Forall.
  constructor.
  inversion_clear Hq. constructor; auto.
Qed.

Lemma Forall2_nth :
  forall {A B} (P : A -> B -> Prop) xs ys a b n,
    Forall2 P xs ys ->
    n < length xs ->
    P (nth n xs a) (nth n ys b).
Proof.
  intros * H HH.
  rewrite Forall2_forall2 in H.
  eapply H; eauto.
Qed.

Lemma Forall3_nth :
  forall {A B C} (P : A -> B -> C -> Prop) xs ys zs a b c n,
    Forall3 P xs ys zs ->
    n < length xs ->
    P (nth n xs a) (nth n ys b) (nth n zs c).
Proof.
  intros * H HH.
  rewrite Forall3_forall3 in H.
  eapply H; eauto.
Qed.

(* TODO: rename ? *)
Lemma Forall2_ignore1'': forall {A B} (P : B -> Prop) (xs : list A) ys,
    Forall2 (fun _ y => P y) xs ys ->
    Forall P ys.
Proof.
  intros ?? P xs ys; revert xs.
  induction ys; intros * Hf; inversion Hf; subst; eauto.
Qed.

Lemma concat_length_sum :
  forall {A} (l : list (list A)),
    length (concat l) = list_sum (List.map (@length A) l).
Proof.
  induction l; simpl; auto.
  rewrite app_length; lia.
Qed.

Lemma length_app_decomp :
  forall {A} (l : list A) n m,
    length l = (n + m)%nat ->
    exists l1 l2,
      l = l1 ++ l2
      /\ length l1 = n
      /\ length l2 = m.
Proof.
  induction n; simpl; intros * Hl.
  - exists [],l. auto.
  - destruct (IHn (S m)) as (l1 & [| x l2] &?&?&?); simpl in *; try lia.
    exists (l1 ++ [x]),l2.
    rewrite <- app_assoc, app_length; simpl.
    repeat split; auto; lia.
Qed.

Lemma flat_map_repeat :
  forall {A B} (f : B -> nat) (a : A) (l : list B),
    flat_map (fun e => repeat a (f e)) l = repeat a (list_sum (List.map f l)).
Proof.
  induction l; simpl; auto.
  now rewrite repeat_app, app_inv_head_iff.
Qed.

Lemma map_repeat :
  forall {A B} (f : A -> B) (a : A) n,
    List.map f (repeat a n) = repeat (f a) n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma nth_repeat_in :
  forall {A} (a d : A) (m n : nat),
    (n < m)%nat ->
    nth n (repeat a m) d = a.
Proof.
  induction m; simpl; intros; cases; try lia.
  auto with arith.
Qed.

Lemma Forall3_repeat :
  forall {A B C} (R : A -> B -> C -> Prop) a b c n,
    R a b c ->
    Forall3 R (repeat a n) (repeat b n) (repeat c n).
Proof.
  induction n; constructor; auto.
Qed.

Lemma Forall2_repeat :
  forall {A B} (R : A -> B -> Prop) a b n,
    R a b ->
    Forall2 R (repeat a n) (repeat b n).
Proof.
  induction n; constructor; auto.
Qed.


(** ** [mem_nth l x] returns the index of the first occurrence of x in l *)
Section Mem_nth.

  Variable (T : Type).
  Hypothesis T_eq_dec : forall x y : T, { x = y } + { x <> y }.

  Fixpoint mem_nth (l : list T) (x : T) : option nat :=
    match l with
    | [] => None
    | y :: l =>
        if T_eq_dec x y then Some O
        else option_map S (mem_nth l x)
    end.

  Lemma mem_nth_nth :
    forall l k d,
      NoDup l ->
      k < length l ->
      mem_nth l (nth k l d) = Some k.
  Proof.
    induction l; simpl; intros * Hdup Hk. lia.
    destruct k.
    - destruct T_eq_dec; congruence.
    - inversion_clear Hdup.
      destruct T_eq_dec; subst.
      + exfalso. auto using nth_In with arith.
      + rewrite IHl; auto with arith.
  Qed.

  Lemma mem_nth_In :
    forall l x n, mem_nth l x = Some n -> In x l.
  Proof.
    induction l as [|y l]; simpl; intros * Hm; try congruence.
    destruct (T_eq_dec x y); subst; auto.
    unfold option_map in Hm.
    destruct mem_nth eqn:?; inversion_clear Hm; eauto.
  Qed.

  Lemma mem_nth_Some :
    forall x l k d,
      mem_nth l x = Some k ->
      k < length l /\ nth k l d = x.
  Proof.
    induction l; simpl; intros * Hk; try congruence.
    destruct T_eq_dec; subst.
    - inversion Hk; auto with arith.
    - unfold option_map in Hk.
      destruct mem_nth eqn:?; inversion_clear Hk.
      edestruct IHl; eauto with arith.
  Qed.

  Lemma mem_nth_nin :
    forall x xs,
      mem_nth xs x = None ->
      In x xs ->
      False.
  Proof.
    intros * Hf Hin.
    induction xs; simpl in *; auto.
    destruct T_eq_dec; subst; inversion Hf.
    destruct Hin; auto.
    unfold option_map in *; destruct mem_nth eqn:?; auto; congruence.
  Qed.

  Lemma nth_mem_nth :
    forall l x k,
      NoDup l ->
      nth_error l k = Some x ->
      mem_nth l x = Some k.
  Proof.
    intros * ND. revert k x.
    induction ND; simpl; intros * Hn.
    - destruct k; simpl in *; congruence.
    - destruct T_eq_dec; subst.
      + destruct k; simpl in *; auto.
        now apply nth_error_In in Hn.
      + destruct k; simpl in *. congruence.
        erewrite IHND; now auto.
  Qed.

  Lemma mem_nth_error :
    forall l x k,
      mem_nth l x = Some k ->
      nth_error l k = Some x.
  Proof.
    induction l; simpl; intros * Hm.
    congruence.
    destruct T_eq_dec; subst; inversion Hm; subst; auto.
    unfold option_map in *.
    destruct mem_nth eqn:?; inversion Hm; subst; simpl; auto.
  Qed.

End Mem_nth.

Lemma mem_ident_nth :
  forall l x,
    mem_ident x l = true ->
    exists k, mem_nth _ ident_eq_dec l x = Some k.
Proof.
  intros * Hm.
  induction l; simpl in *; try congruence.
  cases; subst.
  exists O; auto with arith.
  apply Bool.orb_prop in Hm as [Hm|Hm].
  apply ident_eqb_eq in Hm; congruence.
  destruct IHl as [? ->]; simpl; eauto with arith.
Qed.


(** ** Lifting of a relation over a list of elements *)
(* TODO: EqSts comme instance de ça dans Vélus ? *)
Section Forall2_relation.

  Variables (A B : Type).
  Variables (RA : relation A) (RB : relation B).

  Global Add Parametric Morphism (a : A) `(Reflexive _ RA) : (hd a)
         with signature Forall2 RA ==> RA
           as hd_morph.
  Proof.
    induction 1; simpl; auto.
  Qed.

  Global Add Parametric Morphism : (@tl A)
         with signature Forall2 RA ==> Forall2 RA
           as tl_morph.
  Proof.
    induction 1; simpl; auto.
  Qed.

  Global Instance F2_refl : Reflexive RA -> Reflexive (Forall2 RA).
  Proof.
    intros Hr l; induction l; auto.
  Qed.

  Global Instance F2_sym : Symmetric RA -> Symmetric (Forall2 RA).
  Proof.
    intros Hs xs ys.
    induction 1; auto.
  Qed.

  Global Instance F2_trans : Transitive RA -> Transitive (Forall2 RA).
  Proof.
    intros Ht xs ys zs Hf.
    revert zs.
    induction Hf; intros * Hf'; inv Hf'; constructor; eauto.
  Qed.

  Global Instance F2_equiv : Equivalence RA -> Equivalence (Forall2 RA).
  Proof.
    intros [].
    constructor; auto using F2_refl, F2_sym, F2_trans.
  Qed.

  Global Add Parametric Morphism (f : A -> B) (Hf : Proper (RA ==> RB) f) : (map f)
         with signature Forall2 RA ==> Forall2 RB
           as map_morph2.
  Proof.
    induction 1; simpl; auto.
  Qed.

  Global Add Parametric Morphism : (@Forall2 A B)
         with signature (RA ==> RB ==> Basics.impl) ==> Forall2 RA ==> Forall2 RB ==> Basics.impl
           as F2_morph2.
  Proof.
    intros P Q PQ xs1 xs2 Ha ys1 ys2 Hb Hf.
    revert dependent xs2.
    revert dependent ys2.
    induction Hf; intros; inv Ha; inv Hb; constructor; eauto.
    eapply PQ; eauto.
  Qed.

  Global Add Parametric Morphism : (@Forall2 A B)
         with signature (RA ==> RB ==> iff) ==> Forall2 RA ==> Forall2 RB ==> iff
           as F2_morph2_iff.
  Proof.
    intros P Q PQ xs1 xs2 Ha ys1 ys2 Hb.
    split; intro Hf.
    - refine (F2_morph2 _ _ _ _ _ _ _ _ _ _); eauto.
      intros ???????; edestruct PQ; eauto.
    - revert dependent xs1.
      revert dependent ys1.
      induction Hf; intros; inv Ha; inv Hb; constructor; eauto.
      eapply PQ; eauto.
  Qed.

End Forall2_relation.

Global Instance : forall A, subrelation (Forall2 (@eq A)) (@eq (list A)).
Proof.
  intros A xs ys.
  induction 1; auto.
Qed.

Global Add Parametric Morphism A B : (@Forall2 A B)
    with signature (@eq A ==> @eq B ==> iff) ==> @eq (list A) ==> @eq (list B) ==> iff
      as F2_morph_eq.
Proof.
  intros P Q PQ xs ys.
  split; induction 1; constructor; auto.
  all: destruct (PQ x x eq_refl y y eq_refl); auto.
Qed.


(** ** Application d'un prédicat sur les lignes d'une matrice *)
(* La matrice est donnée colonne par colonne, on souhaite montrer
 * qu'un prédicat (P : list A -> Prop) est vérifié sur chaque ligne
 * de la matrice.
 *)
Section Forall2t.

  Context {A B : Type}.
  Variable (d : A). (* paramètre par défaut pour hd *)

  Variable (P : list A -> B -> Prop).

  (** On considère une matrice de A avec une colonne supplémentaire de B.
      Le prédicat P doit être vrai sur chaque ligne. *)
  Inductive Forall2t : list (list A) -> list B -> Prop :=
  | f2tnil : forall l,
      Forall (eq []) l ->
      Forall2t l []
  | f2tcons : forall (l : list (list A)) (h : B) (t : list B),
      P (List.map (hd d) l) h ->
      Forall2t (List.map (@tl A) l) t ->
      Forall2t l (h :: t).

  Lemma Forall2t_forall2 :
    forall ll l (b : B),
      Forall (fun xl => length xl = length l) ll ->
      Forall2t ll l
      <-> forall n,
          n < length l ->
          P (map (fun l => nth n l d) ll) (nth n l b).
  Proof.
    intros * Hl; split.
    - intros Ht.
      induction Ht; intros * Le.
      { now inv Le. }
      destruct n; simpl.
      + rewrite <- map_hd_nth; auto.
      + setoid_rewrite map_map in IHHt.
        rewrite map_tl_nth.
        apply IHHt; auto with arith.
        eapply Forall_map, Forall_impl; eauto.
        intros [] **; simpl in *; lia.
    - intro Nth.
      revert dependent ll.
      induction l as [| x l]; intros.
      { constructor; simpl_Forall; now apply symmetry, length_zero_iff_nil. }
      constructor.
      + rewrite map_hd_nth.
        apply (Nth O); simpl; auto with arith.
      + eapply IHl.
        { eapply Forall_map, Forall_impl; eauto.
          intros [] **; simpl in *; lia. }
        intros.
        rewrite map_map, <- map_tl_nth.
        apply (Nth (S n)); simpl; auto with arith.
  Qed.

  (** Calcul de la transposée d'une matrice. On donne sa spécification
      dans son type car raisonner sur la fonction direcement est rendu
      très pénible par la preuve de terminaison. *)
  Program Fixpoint transp (l : list (list A)) (k : { k | Forall (fun l => length l = k) l })
    {measure (length (concat l))}
    : { l' : list (list A)
      | (l <> [] -> length l' = k /\ Forall (fun ll => length ll = length l) l')
        /\ forall n m, nth n (nth m l' []) d = nth m (nth n l []) d } :=
    match l with
    | [] => []
    | [] :: _ => []
    | rows => List.map (hd d) rows :: transp (List.map (@tl _) rows) (exist _ (Nat.pred k) _)
    end.

  Next Obligation.
    simpl; split; intros; cases; congruence.
  Qed.

  Next Obligation.
    inv H.
    simpl; split; intros; auto.
    setoid_rewrite length_zero_iff_nil in H3.
    rewrite Forall_nth in H3.
    cases; simpl in *.
    - destruct (Nat.lt_ge_cases n (length wildcard')).
      + rewrite H3; auto.
      + do 2 (rewrite nth_overflow; auto).
    - destruct (Nat.lt_ge_cases n (length wildcard')).
      + rewrite H3; auto.
      + do 2 (rewrite nth_overflow; simpl; auto with arith).
  Qed.

  Next Obligation.
    rewrite Forall_map.
    setoid_rewrite tl_length.
    simpl_Forall; auto.
  Qed.

  Next Obligation.
    destruct l as [|[] l].
    1,2: contradict H; eauto.
    simpl.
    rewrite 2 app_length.
    assert (le (length (concat (map (tl (A:=A)) l))) (length (concat l))); auto with arith.
    clear.
    induction l; simpl; auto.
    rewrite 2 app_length.
    destruct a; simpl; auto with arith.
  Qed.

  Next Obligation.
    rename n into Hl'.
    destruct transp as [? [Heq Ht]]; simpl.
    destruct Heq as [Heq Hf]; auto using map_eq_nnil.
    split; intros.
    { rewrite Heq; simpl.
      split.
      - destruct k; auto.
        destruct l as [|[]]; simpl in *; try congruence.
        inv H; simpl in *; congruence.
      - constructor; auto using map_length.
        eapply Forall_impl in Hf; eauto.
        simpl; intros * HH.
        now rewrite map_length in HH.
    }
    destruct (Nat.lt_ge_cases n (length l)) as [Lt|Le].
    2:{ rewrite (nth_overflow _ _ Le), nth_nil.
        cases. rewrite nth_overflow; auto; now rewrite map_length.
        rewrite Ht, nth_overflow; auto.
        rewrite nth_overflow; simpl; auto with arith.
        now rewrite map_length.
    }
    cases; simpl.
    erewrite map_nth', hd_nth; eauto.
    erewrite Ht, map_nth', tl_nth; eauto.
  Qed.

  Next Obligation.
    split; intros; congruence.
  Qed.

  (** Forall2t est bien l'analogue de Forall2 sur la matrice tansposée. *)
  Lemma Forall2t_Forall2 :
    forall ll l (Hl : Forall (fun l' => length l' = length l) ll),
      ll <> [] ->
      Forall2t ll l ->
      Forall2 P (proj1_sig (transp ll (exist _ _ Hl))) l.
  Proof.
    intros * Nnil Hft.
    apply Forall2_forall2.
    destruct transp as [ll' [Hlt Ht]]; simpl in *.
    destruct Hlt as [Hlt Hf]; auto.
    split; auto.
    intros * Hn ??; subst.
    rewrite (nth_indep _ _ [] Hn).
    rewrite (Forall2t_forall2 _ _ b) in Hft; auto.
    assert ((nth n ll' []) =  (map (fun l => nth n l d) ll)) as ->.
    2: apply Hft; congruence.
    eapply list_eq_ext with d.
    - eapply Forall_nth in Hf as ->; auto using map_length.
    - intros m Hm.
      (* TODO: il y a sans doute plus propre à faire... *)
      erewrite Ht, map_nth'; auto.
      eapply Forall_nth in Hf; eauto.
      now rewrite Hf in Hm.
  Qed.

  Global Add Parametric Morphism
    (eqA : relation A) (eqB : relation B)
    (EqA : Equivalence eqA)
    (reB : Reflexive eqB)
    (P_compat : Proper (Forall2 eqA ==> eqB ==> iff) P)
    : Forall2t
         with signature (Forall2 (Forall2 eqA)) ==> Forall2 eqB ==> iff
           as F2t_morph.
  Proof.
    intros xss xss' Hxy ys ys' Heq.
    revert Hxy. revert xss xss'.
    induction Heq; split; intro Hf; inv Hf.
    - constructor.
      clear - Hxy H.
      induction Hxy; auto; inv H; inv H0; auto.
    - constructor.
      clear - Hxy H.
      induction Hxy; auto; inv H; inv H0; auto.
    - constructor.
      + now rewrite <- Hxy, <- H.
      + eapply IHHeq; eauto.
        now rewrite <- Hxy.
    - constructor.
      + now rewrite  H, Hxy.
      + eapply IHHeq; eauto.
        now rewrite Hxy.
  Qed.

End Forall2t.

(** Lorsque l'on combine chaque ligne de la matrice [ll] avec une même
    liste [la], typiquement une liste d'enumtag. *)
Lemma Forall2t_combine :
  forall A B C d1 d2 (P : list (A * B) -> C -> Prop) (ll : list (list B)) la lc,
    Forall (fun xl => length xl = length lc) ll ->
    Forall2t d1 (fun l c => P (combine la l) c) ll lc ->
    Forall2t d2 P (map (fun '(a,l) => map (pair a) l) (combine la ll)) lc.
Proof.
  intros * Hl.
  destruct lc as [|c lc].
  { (* si lc est vide *)
    intro Hd; inv Hd.
    constructor.
    simpl_Forall.
    apply in_combine_r in H0.
    simpl_Forall; subst; auto. }
  unshelve rewrite 2 Forall2t_forall2; auto.
  2:{ simpl_Forall; rewrite map_length.
      apply in_combine_r in H.
      eapply Forall_forall in Hl; eauto. }
  intros Hp k Hk.
  specialize (Hp k Hk).
  rewrite combine_map_snd in Hp.
  rewrite map_map.
  match goal with
  | _: P ?l1 _ |- P ?l2 _ => assert (l2 = l1) as ->; [clear Hp | eassumption]
  end.
  apply map_ext_in_iff.
  intros [] Hin; simpl.
  apply in_combine_r in Hin as Hr.
  eapply Forall_forall in Hl; eauto.
  erewrite nth_indep, map_nth; eauto.
  rewrite map_length; lia.
Qed.
