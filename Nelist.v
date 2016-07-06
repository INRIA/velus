Require Import Setoid.
Require Import Morphisms.

(** * Non-empty lists *)

(** 

  This module re-implements the [List] library, specialized to the
  case where the list is necessarily non-empty.

 *)

Set Implicit Arguments.
Require List. (* To check their equivalent versions *)

(** ** Datatype *)

Inductive nelist (A : Type) : Type :=
  | nebase (e : A)
  | necons (e : A) (l : nelist A).

(** ** Operations *)

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

(*
Fixpoint list2nelist {A : Type} (l : list A) (Hl : l <> nil) {struct l} : nelist A.
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

Definition map {A B : Type} (f : A -> B) :=
  fix map l :=
    match l with
    | nebase e => nebase (f e)
    | necons e l' => necons (f e) (map l')
    end.

Definition fold_left {A B : Type} (f : A -> B -> A) :=
fix fold_left (l : nelist B) (a0 : A) {struct l} : A :=
  match l with
  | nebase e => f a0 e
  | necons b t => fold_left t (f a0 b)
  end.

Definition fold_right {A B : Type} (f : B -> A -> A) (a0 : A) :=
  fix fold_right (l : nelist B) : A :=
  match l with
  | nebase b => f b a0
  | necons b t => f b (fold_right t)
  end.

Fixpoint combine {A B : Type} (l : nelist A) (l' : nelist B) {struct l} : nelist (A * B) :=
  match l, l' with
    | nebase a, nebase b => nebase (a, b)
    | nebase a, necons b lb => nebase (a, b)
    | necons a la, nebase b => nebase (a, b)
    | necons a la, necons b lb => necons (a, b) (combine la lb)
  end.

(* A constant list of the same size *)
Definition alls {A B} c (l : nelist A) : nelist B := map (fun _ => c) l.

(** ** Predicates **)

Fixpoint In {A : Type} (x : A) (l : nelist A): Prop :=
  match l with
    | nebase e => x = e
    | necons e l' => x = e \/ In x l'
  end.

Inductive Forall {A : Type} (P : A -> Prop) : nelist A -> Prop :=
  | Forall_nil : forall x : A, P x -> Forall P (nebase x)
  | Forall_cons : forall (x : A) (l : nelist A), P x -> Forall P l -> Forall P (necons x l).

Inductive Forall2 {A B : Type} (R : A -> B -> Prop) : nelist A -> nelist B -> Prop :=
  | Forall2_nil : forall x y, R x y -> Forall2 R (nebase x) (nebase y)
  | Forall2_cons : forall x y l l', R x y -> Forall2 R l l' -> Forall2 R (necons x l) (necons y l').

Inductive Exists {A : Type} (P : A -> Prop) : nelist A -> Prop :=
  | Exists_base : forall x, P x -> Exists P (nebase x)
  | Exists_cons_hd : forall x l, P x -> Exists P (necons x l)
  | Exists_cons_tl : forall x l, Exists P l -> Exists P (necons x l).

Inductive NoDup {A : Type} : nelist A -> Prop :=
    NoDup_base : forall x, NoDup (nebase x)
  | NoDup_cons : forall x l, ~In x l -> NoDup l -> NoDup (necons x l).

Definition map_fst {A B: Type} (l: nelist (A * B)): nelist A :=
  map (@fst A B) l.

(** ** Properties *)

Ltac inv H := inversion H; subst; clear H.

(** *** About [length] *)

Lemma diff_length_nebase_necons : forall {A B} (a : A) (b : B) l, length (nebase a) <> length (necons b l).
Proof. intros A B a b [? | ? ?]; simpl; discriminate. Qed.

Lemma nelist2list_length: forall {A} (l: nelist A),
  length l = List.length (nelist2list l).
Proof. induction l; simpl; auto. Qed.

(** *** About [nelist2list] *)

Lemma nelist2list_non_empty : forall {A} (l : nelist A), nelist2list l <> nil.
Proof. intros A [e | e l]; simpl; discriminate. Qed.

Lemma nelist2list_cons: forall {A} x (l : nelist A), nelist2list (necons x l) = cons x (nelist2list l).
Proof. reflexivity. Qed.
  
Lemma nelist2list_In : forall {A} (x : A) l, List.In x (nelist2list l) <-> In x l.
Proof. intros A x l. induction l; simpl; try rewrite IHl; intuition. Qed.

(** *** About [map] *)

Lemma map_compat {A B : Type} : Proper ((eq ==> eq) ==> eq ==> eq) (@map A B).
Proof. intros f g Hfg l l' Hl. subst l'. induction l; simpl; f_equal; auto. Qed.

Lemma map_compose:
  forall A B C (f: A -> B)(g: B -> C) xs,
    map g (map f xs) = map (fun x => g (f x)) xs.
Proof.
  intros until xs.
  induction xs as [|x xs IH]; simpl; congruence.
Qed.

Definition injective {A B} (f : A -> B) := forall x y, f x = f y -> x = y.

Lemma map_In : forall {A B : Type} (f : A -> B), injective f ->
  forall l x, In (f x) (map f l) <-> In x l.
Proof.
intros A B f Hf l x. induction l as [e | e l]; simpl.
+ split; intro Hin; inversion Hin; trivial; now apply Hf.
+ rewrite IHl. firstorder. subst. tauto.
Qed.

Lemma map_eq_nebase : forall {A B : Type} (f : A -> B) l y, map f l = nebase y <-> exists x, l = nebase x /\ f x = y.
Proof.
intros A B f l y. destruct l; simpl; split; intro H; decompose [ex and] H || inversion_clear H; subst; eauto.
- inversion H1. now subst.
- discriminate.
Qed.

Lemma map_eq_necons : forall {A B : Type} (f : A -> B) l y l',
  map f l = necons y l' <-> exists x l'', l = necons x l'' /\ f x = y /\ map f l'' = l'.
Proof.
intros A B f l y l'. destruct l; simpl; split; intro H; decompose [ex and] H || inversion_clear H; subst; eauto.
- discriminate. 
- inversion H0. now subst.
Qed.

Lemma map_length : forall  {A B : Type} (f : A -> B) l, length (map f l) = length l.
Proof. intros A B f l. induction l; simpl; auto. Qed.

Lemma nelist2list_map : forall {A B : Type} (f : A -> B) l,
  nelist2list (map f l) = List.map f (nelist2list l).
Proof. intros A B f l. induction l; simpl; try rewrite IHl; reflexivity. Qed.
   
(** *** About [Forall] *)

Lemma Forall_forall : forall {A : Type} P l, Forall P l <-> forall x : A, In x l -> P x.
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

Lemma nelist2list_Forall : forall {A} P (l : nelist A), List.Forall P (nelist2list l) <-> Forall P l.
Proof. intros A P l. rewrite Forall_forall, List.Forall_forall. now setoid_rewrite nelist2list_In. Qed.

Lemma Forall_map : forall {A B} (f : A -> B) P l, Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof. intros A B f P l. induction l; split; intro Hl; inv Hl; constructor; try rewrite IHl in *; auto. Qed.

Lemma Forall2_length: forall {A B : Type} (R : A -> B -> Prop) l1 l2,
  Forall2 R l1 l2 -> length l1 = length l2.
Proof. intros A B R l1. induction l1; intros [|] Hall; inversion_clear Hall; simpl; auto. Qed.

Lemma Forall2_det : forall {A B : Type} (R : A -> B -> Prop),
  (forall x y1 y2, R x y1 -> R x y2 -> y1 = y2) ->
  forall xs ys1 ys2, Forall2 R xs ys1 -> Forall2 R xs ys2 -> ys1 = ys2.
Proof.
intros A B R HR xs. induction xs as [x | x xs]; intros ys1 ys2 Hall1 Hall2.
- inv Hall1. inv Hall2. f_equal. eauto.
- inv Hall1. inv Hall2. f_equal; eauto.
Qed.

Lemma Forall2_map_l : forall {A B C} (f : A -> B) (R : B -> C -> Prop) l1 l2,
  Forall2 R (map f l1) l2 <-> Forall2 (fun x y => R (f x) y) l1 l2.
Proof.
intros A B C f R l1. induction l1; intro l2; split; intro Hl; inv Hl; simpl;
now constructor; trivial; now apply IHl1.
Qed.

Lemma Forall2_map_r : forall {A B C} (f : A -> C) (R : B -> C -> Prop) l1 l2,
  Forall2 R l1 (map f l2) <-> Forall2 (fun x y => R x (f y)) l1 l2.
Proof.
intros A B C f R l1 l2. revert l1. induction l2; intro l1; split; intro Hl; inv Hl; simpl;
now constructor; trivial; now apply IHl2.
Qed.

Corollary Forall2_map_lr : forall {A B C D} (f : A -> C) (g : B -> D) (R : C -> D -> Prop) l1 l2,
  Forall2 R (map f l1) (map g l2) <-> Forall2 (fun x y => R (f x) (g y)) l1 l2.
Proof. intros. now rewrite Forall2_map_l, Forall2_map_r. Qed.

Lemma Forall2_eq : forall {A} l1 l2, Forall2 (@eq A) l1 l2 <-> l1 = l2.
Proof.
intros A l1 l2. split; intro Heq; subst.
- revert l2 Heq. induction l1; intros l2 Heq; inv Heq; trivial; f_equal; auto.
- induction l2; constructor; auto.
Qed.

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

(** *** About [Exists] *)

Lemma Exists_exists : forall {A : Type} P l, Exists P l <-> exists x : A, In x l /\ P x.
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

Lemma nelist2list_Exists : forall {A} P (l : nelist A), List.Exists P (nelist2list l) <-> Exists P l.
Proof. intros A P l. rewrite Exists_exists, List.Exists_exists. now setoid_rewrite nelist2list_In. Qed.

(** *** About [NoDup] **)

Lemma nelist2list_NoDup : forall {A} (l : nelist A), List.NoDup (nelist2list l) <-> NoDup l.
Proof.
intros A l. induction l; simpl.
- split; intro Hnodup; inv Hnodup; repeat constructor; intuition.
- split; intro Hnodup; inv Hnodup; repeat constructor;
  now rewrite ?IHl in *; try (rewrite <- nelist2list_In || rewrite nelist2list_In).
Qed.
