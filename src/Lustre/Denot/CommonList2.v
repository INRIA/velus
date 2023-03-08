From Coq Require Import Lia.
From Coq Require Import List.
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
