Require Import Setoid.

(** Non-empty lists *)


Set Implicit Arguments.
Require List. (* To check their equivalent versions *)


Inductive nelist (A : Set) : Set :=
  | nebase (e : A)
  | necons (e : A) (l : nelist A).

Fixpoint length {A} (l : nelist A) :=
  match l with
    | nebase _ => 1
    | necons _ l' => S (length l')
  end.

Fixpoint nelist2list {A} (l : nelist A) : list A :=
  match l with
    | nebase e => cons e nil
    | necons e l' => cons e (nelist2list l')
  end.

Lemma nelist_2list_non_empty : forall A (l : nelist A), nelist2list l <> nil.
Proof. intros A [e | e l]; simpl; discriminate. Qed.

(*
Fixpoint list2nelist {A : Set} (l : list A) (Hl : l <> nil) {struct l} : nelist A.
destruct l as [| e l'].
+ now elim Hl.
+ apply (@list_rec A (fun _ => nelist A) (nebase e)).
  - apply 
  - 
 destruct l'. exact (nebase e).
+ apply (necons e). apply (list2nelist _ (cons e' l')). Guarded.
  refine (match l as l' return l = l' -> nelist A with
    | nil => fun Heq => False_rect _ (Hl Heq)
    | cons e l' => fun Heq => 
        match l' as l'' return l' = l'' -> nelist A with
          | nil => fun _ => nebase e
          | cons e l' => fun _ => necons e (list2nelist _ l' _)
        end eq_refl
  end eq_refl).
Proof. discriminate. Defined.
*)

Fixpoint In {A : Set} (x : A) (l : nelist A) :=
  match l with
    | nebase e => x = e
    | necons e l' => x = e \/ In x l'
  end.

(** **  The [map] function  **)

Fixpoint map {A B : Set} (f : A -> B) l :=
  match l with
    | nebase e => nebase (f e)
    | necons e l' => necons (f e) (map f l')
  end.

Definition injective {A B} (f : A -> B) := forall x y, f x = f y -> x = y.

Lemma map_In : forall {A B : Set} (f : A -> B), injective f ->
  forall l x, In (f x) (map f l) <-> In x l.
Proof.
intros A B f Hf l x. induction l as [e | e l]; simpl.
+ split; intro Hin; inversion Hin; trivial; now apply Hf.
+ rewrite IHl. firstorder. subst. tauto.
Qed.

Lemma map_eq_nebase : forall {A B : Set} (f : A -> B) l y, map f l = nebase y <-> exists x, l = nebase x /\ f x = y.
Proof.
intros A B f l y. destruct l; simpl; split; intro H; decompose [ex and] H || inversion_clear H; subst; eauto.
- inversion H1. now subst.
- discriminate.
Qed.

Lemma map_eq_necons : forall {A B : Set} (f : A -> B) l y l',
  map f l = necons y l' <-> exists x l'', l = necons x l'' /\ f x = y /\ map f l'' = l'.
Proof.
intros A B f l y l'. destruct l; simpl; split; intro H; decompose [ex and] H || inversion_clear H; subst; eauto.
- discriminate. 
- inversion H0. now subst.
Qed.

Lemma map_length : forall  {A B : Set} (f : A -> B) l, length (map f l) = length l.
Proof. intros A B f l. induction l; simpl; auto. Qed.

(** **  The [fold_left] function  **)

Definition fold_left {A B : Set} (f : A -> B -> A) :=
fix fold_left (l : nelist B) (a0 : A) {struct l} : A :=
  match l with
  | nebase e => f a0 e
  | necons b t => fold_left t (f a0 b)
  end.

(** **  The [Forall] and [Exists] predicates  **)

Inductive Forall {A : Set} (P : A -> Prop) : nelist A -> Prop :=
  | Forall_nil : forall x : A, P x -> Forall P (nebase x)
  | Forall_cons : forall (x : A) (l : nelist A), P x -> Forall P l -> Forall P (necons x l).

Lemma Forall_forall : forall {A : Set} P l, Forall P l <-> forall x : A, In x l -> P x.
Proof.
intros A P l. induction l; simpl.
+ split; intro Hin.
  - intros. subst. now inversion_clear Hin.
  - constructor. now apply Hin.
+ split; intro Hin.
  - intros. inversion_clear Hin. rewrite IHl in *. destruct H; subst; auto.
  - constructor.
    * apply Hin. now left.
    * rewrite IHl. intros. apply Hin. auto.
Qed.

Inductive Forall2 {A B : Set} (R : A -> B -> Prop) : nelist A -> nelist B -> Prop :=
  | Forall2_nil : forall x y, R x y -> Forall2 R (nebase x) (nebase y)
  | Forall2_cons : forall x y l l', R x y -> Forall2 R l l' -> Forall2 R (necons x l) (necons y l').

Lemma Forall2_length: forall {A B : Set} (R : A -> B -> Prop) l1 l2,
  Forall2 R l1 l2 -> length l1 = length l2.
Proof. intros A B R l1. induction l1; intros [|] Hall; inversion_clear Hall; simpl; auto. Qed.

(*
Lemma Forall2_forall2 : forall {A B : Type} P l1 l2,
  Forall2 P l1 l2 <-> length l1 = length l2 /\
                      forall (a : A) (b : B) n x1 x2, n < length l1 -> nth n l1 a = x1 -> nth n l2 b = x2 -> P x1 x2.
Proof.
intros A B P l1. induction l1; intro l2.
* split; intro H.
  + inversion_clear H. split; simpl; auto. intros. omega.
  + destruct H as [H _]. destruct l2; try discriminate. constructor.
* split; intro H.
  + inversion_clear H. rewrite IHl1 in H1. destruct H1. split; simpl; auto.
    intros. destruct n; subst; trivial. eapply H1; eauto. omega.
  + destruct H as [Hlen H].
    destruct l2; simpl in Hlen; try discriminate. constructor.
    apply (H a b 0); trivial; simpl; try omega.
    rewrite IHl1. split; try omega.
    intros. eapply (H a0 b0 (S n)); simpl; eauto. simpl; omega.
Qed.

Corollary Forall2_length : forall {A B} (P : A -> B -> Prop) l1 l2,
  Forall2 P l1 l2 -> length l1 = length l2.
Proof. intros * Hall. rewrite Forall2_forall2 in Hall. now destruct Hall. Qed.
*)
Inductive Exists {A : Set} (P : A -> Prop) : nelist A -> Prop :=
  | Exists_base : forall x, P x -> Exists P (nebase x)
  | Exists_cons_hd : forall x l, P x -> Exists P (necons x l)
  | Exists_cons_tl : forall x l, Exists P l -> Exists P (necons x l).

Lemma Exists_exists : forall {A : Set} P l, Exists P l <-> exists x : A, In x l /\ P x.
Proof.
intros A P l. induction l; simpl.
* split; intro Hin.
  + exists e. inversion_clear Hin. tauto.
  + destruct Hin as [? [? ?]]. subst. now constructor.
* split; intro Hin.
  + inversion_clear Hin.
    - exists e. tauto.
    - rewrite IHl in H. destruct H as [x ?]. exists x. tauto.
  + destruct Hin as [x [[? | ?] ?]].
    - subst. now constructor 2.
    - constructor 3. rewrite IHl. exists x. tauto.
Qed.

