Require Import Coq.FSets.FMapPositive.
Require Import List.
Require Import Coq.Sorting.Permutation.
Require Import Morphisms.
Import ListNotations.
Require Coq.MSets.MSets.
Require Export PArith.
Require Import Omega.
Require Import Coq.Classes.EquivDec.

Open Scope list.

(** * Common definitions *)

(** ** Finite sets and finite maps *)

(** These modules are used to manipulate identifiers. *)

Ltac inv H := inversion H; clear H; subst.

Module PS := Coq.MSets.MSetPositive.PositiveSet.
Module PSP := MSetProperties.WPropertiesOn Pos PS.
Module PSF := MSetFacts.Facts PS.
Module PSdec := Coq.MSets.MSetDecide.WDecide PS.

Module PM := Coq.FSets.FMapPositive.PositiveMap.

Definition ident := positive.
Definition ident_eq_dec := Pos.eq_dec.
Definition ident_eqb := Pos.eqb. (* TODO: replace with equiv_decb *)

Instance: EqDec ident eq := { equiv_dec := ident_eq_dec }.

Implicit Type i j: ident.

Definition mem_assoc_ident {A} (x: ident): list (ident * A) -> bool :=
  existsb (fun y => ident_eqb (fst y) x).

Definition assoc_ident {A} (x: ident) (xs: list (ident * A)): option A :=
  match find (fun y => ident_eqb (fst y) x) xs with
  | Some (_, a) => Some a
  | None => None
  end.
       
Module Type IDS.
  Parameter self : ident.
  Parameter out  : ident.

  Parameter step  : ident.
  Parameter reset : ident.

  Definition reserved : list ident := [ self; out ].

  Definition methods  : list ident := [ step; reset ].

  Axiom reserved_nodup: NoDup reserved.
  Axiom methods_nodup: NoDup methods.

  Definition NotReserved {typ: Type} (xty: ident * typ) : Prop :=
    ~In (fst xty) reserved.

End IDS.

(** ** Properties *)

(** *** About identifiers **)

Lemma ident_eqb_neq:
  forall x y, ident_eqb x y = false <-> x <> y.
Proof.
  unfold ident_eqb; apply Pos.eqb_neq.
Qed.

Lemma ident_eqb_eq:
  forall x y, ident_eqb x y = true <-> x = y.
Proof.
  unfold ident_eqb; apply Pos.eqb_eq.
Qed.

Lemma ident_eqb_refl:
  forall f, ident_eqb f f = true.
Proof.
  unfold ident_eqb; apply Pos.eqb_refl.
Qed.

Lemma In_dec:
  forall x S, {PS.In x S}+{~PS.In x S}.
Proof.
  intros i m; unfold PS.In; case (PS.mem i m); auto.
Qed.

(** *** Operator abstraction *)

Generalizable Variables A.
  
Lemma equiv_decb_equiv:
  forall `{EqDec A} (x y : A),
    equiv_decb x y = true <-> equiv x y.
Proof.
  intros ** x y.
  split; intro; unfold equiv_decb in *;
    destruct (equiv_dec x y); intuition.
Qed.

Lemma equiv_decb_refl:
  forall `{EqDec A} (x: A),
    equiv_decb x x = true.
Proof.
  intros. now apply equiv_decb_equiv.
Qed.

Lemma not_equiv_decb_equiv:
  forall `{EqDec A} (x y: A),
    equiv_decb x y = false <-> ~(equiv x y).
Proof.
  split; intro Hne.
  - unfold equiv_decb in Hne.
    now destruct (equiv_dec x y).
  - unfold equiv_decb.
    destruct (equiv_dec x y); [|reflexivity].
    exfalso; now apply Hne.
Qed.

(** *** About Coq stdlib *)

Definition notb {A} (f: A -> bool) (x: A) := negb (f x).

Lemma filter_notb_app:
  forall {A} (p: A -> bool) xs,
    Permutation (filter p xs ++ filter (notb p) xs) xs.
Proof.
  induction xs as [|x xs]; auto.
  unfold notb, negb in *. simpl. destruct (p x); simpl.
  now rewrite IHxs.
  rewrite <-Permutation_middle. now rewrite IHxs.
Qed.

Lemma Forall_cons2:
  forall A P (x: A) l,
    List.Forall P (x :: l) <-> P x /\ List.Forall P l.
Proof. intros; split; inversion_clear 1; auto. Qed.

Lemma add_comm:
  forall {A} x x' (v v': A) m,
    x <> x' ->
    PM.add x v (PM.add x' v' m) = PM.add x' v' (PM.add x v m).
Proof.
  induction x, x', m; simpl; intro Neq;
  ((f_equal; apply IHx; intro Eq; apply Neq; now inv Eq) || now contradict Neq).
Qed.

Lemma pm_in_dec: forall A i m, PM.In (A:=A) i m \/ ~PM.In (A:=A) i m.
Proof.
  unfold PM.In, PM.MapsTo.
  intros A i m.
  case (PM.find i m).
  eauto.
  right; intro; destruct H; discriminate H.
Qed.

Lemma Some_injection:
  forall A (x:A) (y:A), x = y <-> Some x = Some y.
Proof.
  split; intro H; [rewrite H|injection H]; auto.
Qed.

(* TODO: Is there a more direct way to negate PS.mem_spec?
         I.e., without creating a distinct lemma. *)
Lemma mem_spec_false:
  forall s x, PS.mem x s = false <-> ~PS.In x s.
Proof.
  split.
  intros Hmem Hin.
  apply PS.mem_spec in Hin.
  rewrite Hin in Hmem.
  discriminate.
  intro Hnin.
  apply Bool.not_true_iff_false.
  intro Hnmem.
  rewrite PS.mem_spec in Hnmem.
  contradiction.
Qed.

Import List.ListNotations.
Open Scope list_scope.

Lemma List_shift_first:
  forall (A:Type) ll (x : A) lr,
    ll ++ (x :: lr) = (ll ++ [x]) ++ lr.
Proof.
  induction ll as [|? ? IH]; [auto|intros].
  rewrite <- List.app_comm_cons.
  rewrite IH.
  now do 2 rewrite List.app_comm_cons.
Qed.

Lemma List_shift_away:
  forall (A:Type) alleqs (eq : A) eqs,
    (exists oeqs, alleqs = oeqs ++ (eq :: eqs))
    -> exists oeqs', alleqs = oeqs' ++ eqs.
Proof.
  intros A alleqs eq eqs Hall.
  destruct Hall as [oeqs Hall].
  exists (oeqs ++ [eq]).
  rewrite Hall.
  now rewrite List_shift_first.
Qed.

Lemma Forall_app:
  forall A (P: A -> Prop) ll rr,
    Forall P (ll ++ rr) <-> (Forall P ll /\ Forall P rr).
Proof.
  intros A P ll rr.
  induction ll as [|x ll IH]; [intuition|].
  rewrite Forall_cons2.
  rewrite and_assoc.
  rewrite <-IH.
  rewrite <-List.app_comm_cons.
  now rewrite Forall_cons2.
Qed.

Lemma Exists_app:
  forall A (P: A -> Prop) ll rr,
    Exists P rr
    -> Exists P (ll ++ rr).
Proof.
  intros A P ll rr Hex.
  induction ll as [|x ll IH]; [intuition|].
  rewrite <-List.app_comm_cons.
  constructor 2.
  exact IH.
Qed.

Lemma Forall_Forall:
  forall A P Q (xs : list A),
    Forall P xs -> Forall Q xs -> Forall (fun x=>P x /\ Q x) xs.
Proof.
  induction xs as [|x xs IH]; [now constructor|].
  intros HPs HQs.
  inversion_clear HPs as [|? ? HP HPs'].
  inversion_clear HQs as [|? ? HQ HQs'].
  intuition.
Qed.

Lemma Forall_Exists:
  forall A (P Q: A -> Prop) xs,
    Forall P xs
    -> Exists Q xs
    -> Exists (fun x=>P x /\ Q x) xs.
Proof.
  induction xs as [|x xs IH]; [now inversion 2|].
  intros Ha He.
  inversion_clear Ha.
  inversion_clear He; auto.
Qed.

Lemma decidable_Exists:
  forall {A} (P: A->Prop) xs,
    (forall x, In x xs -> Decidable.decidable (P x)) ->
    Decidable.decidable (Exists P xs).
Proof.
  intros ** Hdec.
  induction xs as [|x xs].
  - right. now intro HH; apply Exists_nil in HH.
  - destruct (Hdec x) as [Hx|Hx].
    + now constructor.
    + destruct IHxs as [Hxs|Hxs];
        try (now left; constructor).
      intros y Hin.
      apply Hdec. constructor (assumption).
    + destruct IHxs as [Hxs|Hxs].
      * intros y Hin.
        apply Hdec. constructor (assumption).
      * left. constructor (assumption).
      * right. intro HH.
        apply Exists_cons in HH.
        intuition.
Qed.

Lemma decidable_Exists_not_Forall:
  forall {A} (P: A -> Prop) xs,
    (forall x, In x xs -> Decidable.decidable (P x)) ->
    (Exists P xs <-> ~Forall (fun x=>~(P x)) xs).
Proof.
  induction xs as [|x xs]; intro Hdec.
  - split; intro HH.
    + now apply Exists_nil in HH.
    + apply Exists_nil. now apply HH.
  - split; intro HH.
    + inversion_clear 1 as [|? ? HnP Hfa].
      inversion_clear HH as [|? ? Hex]; auto.
      apply IHxs in Hex; auto.
      intros y Hin. apply Hdec. intuition.
    + destruct (Hdec x) as [Hx|Hx]; auto. now intuition.
      right. apply IHxs; intuition.
Qed.
  
Lemma Permutation_Forall:
  forall {A} (l l': list A) P,
    Permutation l l' ->
    Forall P l ->
    Forall P l'.
Proof.
    induction 1; inversion 1; auto.
    match goal with H:Forall _ (_ :: _) |- _ => inversion H end.
    repeat constructor; auto.
Qed.

Instance Forall_Permutation_Proper (A:Type):
  Proper (eq ==> Permutation (A:=A) ==> iff) Forall.
Proof.
  intros P Q HPQ xs ys Hperm.
  subst P.
  split; intro HH; [|symmetry in Hperm];
    apply Permutation_Forall with (1:=Hperm) (2:=HH).
Qed.

Lemma Forall_app_weaken:
  forall {A} xs P (ys : list A),
    Forall P (xs ++ ys) ->
    Forall P ys.
Proof.
  intros ** HH. apply Forall_app in HH. intuition.
Qed.

Lemma not_None_is_Some:
  forall A (x : option A), x <> None <-> (exists v, x = Some v).
Proof.
  destruct x; intuition.
  exists a; reflexivity.
  discriminate.
  match goal with H:exists _, _ |- _ => destruct H end; discriminate.
Qed.

Lemma not_Some_is_None:
  forall A (x : option A),  (forall v, x <> Some v) <-> x = None.
Proof.
  destruct x; intuition.
  - exfalso; now apply (H a).
  - discriminate.
  - discriminate.
Qed.

Lemma combine_map_fst:
  forall {A B C} (f: A -> B) xs (ys: list C),
    combine (map f xs) ys = map (fun x=>(f (fst x), snd x)) (combine xs ys).
Proof.
  induction xs; try constructor.
  destruct ys; try constructor.
  simpl. now rewrite IHxs.
Qed.

Lemma combine_map_snd:
  forall {A B C} (f: A -> B) (xs: list C) ys,
    combine xs (map f ys) = map (fun x=>(fst x, f (snd x))) (combine xs ys).
Proof.
  induction xs; try constructor.
  destruct ys; try constructor.
  simpl. now rewrite IHxs.
Qed.

Lemma combine_map_both:
  forall {A B C D} (f: A -> B) (g: C -> D) xs ys,
    combine (map f xs) (map g ys)
    = map (fun x => (f (fst x), g (snd x))) (combine xs ys).
Proof.
  intros. now rewrite combine_map_fst, combine_map_snd, map_map.
Qed.

Definition not_In_empty: forall x : ident, ~(PS.In x PS.empty) := PS.empty_spec.

Ltac not_In_empty :=
  match goal with H:PS.In _ PS.empty |- _ => now apply not_In_empty in H end.

Lemma map_eq_cons : forall {A B} (f : A -> B) l y l',
  map f l = y :: l' -> exists x l'', l = x :: l'' /\ f x = y.
Proof.
intros A B f l y l' Hmap. destruct l; simpl in Hmap.
- discriminate.
- inversion_clear Hmap. eauto.
Qed.

Open Scope bool_scope.

Fixpoint forall2b {A B} (f : A -> B -> bool) l1 l2 :=
  match l1, l2 with
    | nil, nil => true
    | e1 :: l1, e2 :: l2 => f e1 e2 && forall2b f l1 l2
    | _, _ => false
  end.

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


Lemma Forall2_det : forall {A B : Type} (R : A -> B -> Prop),
  (forall x y1 y2, R x y1 -> R x y2 -> y1 = y2) ->
  forall xs ys1 ys2, Forall2 R xs ys1 -> Forall2 R xs ys2 -> ys1 = ys2.
Proof.
intros A B R HR xs. induction xs as [x | x xs]; intros ys1 ys2 Hall1 Hall2.
- inversion Hall1. inversion Hall2; reflexivity. 
- inversion Hall1. inversion Hall2. f_equal; eauto.
Qed.

Lemma Forall2_combine:
  forall {A B} P (xs: list A) (ys: list B),
    Forall2 P xs ys -> Forall (fun x=>P (fst x) (snd x)) (combine xs ys).
Proof.
  intros A B P xs ys Hfa2.
  induction Hfa2; now constructor.
Qed.

Instance Permutation_map_Proper {A B}:
  Proper ((@eq (A -> B)) ==> Permutation (A:=A) ==> (Permutation (A:=B)))
         (@map A B).
Proof.
  intros f g Heq xs ys Hperm.
  subst. now apply Permutation_map_aux.
Qed.

Section InMembers.
  Context {A B: Type}.

  Fixpoint InMembers (a:A) (l:list (A * B)) : Prop :=
    match l with
    | nil => False
    | (a', _) :: m => a' = a \/ InMembers a m
    end.

  Inductive NoDupMembers: list (A * B) -> Prop :=
  | NoDupMembers_nil:
      NoDupMembers nil
  | NoDupMembers_cons: forall a b l,
      ~ InMembers a l ->
      NoDupMembers l ->
      NoDupMembers ((a, b)::l).

  Theorem inmembers_eq:
    forall a b l, InMembers a ((a, b) :: l).
  Proof.
    intros. constructor. reflexivity.
  Qed.

  Theorem inmembers_cons:
    forall a a' l, InMembers a l -> InMembers a (a' :: l).
  Proof.
    intros. destruct a'. simpl. intuition.
  Qed.

  Theorem In_InMembers:
    forall a b xs,
      In (a, b) xs -> InMembers a xs.
  Proof.
    intros ** Hin.
    induction xs as [|x xs IH]; inversion_clear Hin; subst.
    - simpl. left. reflexivity.
    - simpl. destruct x. right. intuition.
  Qed.

  Theorem InMembers_In:
    forall a xs,
      InMembers a xs -> exists b, In (a, b) xs.
  Proof.
    intros ** Hin.
    induction xs as [|x xs IH]; simpl in Hin.
    - contradiction. 
    - simpl. destruct x. destruct Hin; subst.
      + exists b; now left.
      + destruct IH as (b'); auto.
        exists b'; now right. 
  Qed.

  Theorem nodupmembers_cons:
    forall id ty xs,
      NoDupMembers ((id, ty) :: xs) <->
      ~InMembers id xs /\ NoDupMembers xs.
  Proof.
    split.
    - inversion_clear 1. auto.
    - destruct 1 as [Hnin Hndup].
      constructor; auto.
  Qed.

  Theorem NotInMembers_NotIn:
    forall a b xs, ~ InMembers a xs -> ~ In (a, b) xs.
  Proof.
    intros ** Hnim Hin.
    apply In_InMembers in Hin.
    intuition.
  Qed.

  Theorem NotInMembers_cons:
    forall xs x y,
      ~InMembers y (x::xs) <-> ~InMembers y xs /\ y <> fst x.
  Proof.
    induction xs as [|x' xs IH]; split; intro Hnin.
    - split.
      + inversion 1.
      + intro Eq; apply Hnin.
        destruct x; simpl in *; now left.
    - destruct x; simpl. destruct Hnin as [? Diff].
      intro Hin; apply Diff.
      destruct Hin; try contradiction; auto.
    - split.
      + intro HH. apply Hnin.
        destruct x, x'.
        right. inversion HH; auto.
      + intro HH. apply Hnin.
        destruct x, x'.
        simpl in *; now left.
    - rewrite IH in Hnin; destruct Hnin as ((Hnin & Hx') & Hx).
      destruct x, x'; simpl in *.
      intro Hin; destruct Hin as [|[|]].
      + now apply Hx.
      + now apply Hx'.
      + now apply Hnin.
  Qed.

  Lemma InMembers_app:
    forall y ws xs,
      InMembers y (ws ++ xs) <-> (InMembers y ws) \/ (InMembers y xs).
  Proof.
    induction ws as [|y' ws IH].
    - intuition.
    - destruct y' as [y' yv]. simpl.
      split; intro HH; destruct HH as [HH|HH].
      + intuition.
      + apply IH in HH. intuition.
      + destruct HH as [HH|HH].
        * intuition.
        * right. apply IH. intuition.
      + right. apply IH. intuition.
  Qed.

  Global Instance InMembers_Permutation_Proper:
    Proper (eq ==> (@Permutation (A*B)) ==> iff) InMembers.
  Proof.
    intros x y Heq xs ys Hperm.
    rewrite Heq. clear Heq x.
    split; intro Hinm.
    - apply InMembers_In in Hinm.
      destruct Hinm as [b Hinm].
      apply Permutation_in with (2:=Hinm) in Hperm.
      apply In_InMembers with (1:=Hperm).
    - apply InMembers_In in Hinm.
      destruct Hinm as [b Hinm].
      symmetry in Hperm.
      apply Permutation_in with (2:=Hinm) in Hperm.
      apply In_InMembers with (1:=Hperm).
  Qed.

  (*
  Global Instance InMembers_Permutation_Proper' x:
    Proper ((@Permutation (A*B)) ==> iff) (InMembers x).
  Proof.
    intros xs ys Hperm.
    now rewrite Hperm.
  Qed.
  *)
    
  Theorem NotInMembers_app:
    forall y ws xs,
      ~InMembers y (ws ++ xs) <-> (~InMembers y xs /\ ~InMembers y ws).
  Proof.
    destruct ws; repeat split.
    - assumption.
    - inversion 1.
    - destruct 1. assumption.
    - intro HH. apply H.
      apply InMembers_app. auto.
    - intro. apply H.
      apply InMembers_app. auto.
    - destruct 1 as [H1 H2].
      intro H. apply InMembers_app in H. intuition.
  Qed.

  Theorem NotInMembers_app_comm:
    forall y ws xs,
      ~InMembers y (ws ++ xs) <-> ~InMembers y (xs ++ ws).
  Proof.
    split; intro HH; apply NotInMembers_app in HH;
    apply NotInMembers_app; intuition.
  Qed.

  Theorem NoDupMembers_NoDup:
    forall xs, NoDupMembers xs -> NoDup xs.
  Proof.
    induction xs as [|x xs IH]; [now constructor|].
    intro Hndm.
    inversion_clear Hndm.
    constructor; [|now apply IH].
    apply NotInMembers_NotIn. assumption.
  Qed.

  Lemma NoDupMembers_app_cons:
    forall ws x y xs,
      NoDupMembers (ws ++ (x, y) :: xs)
      <-> ~InMembers x (ws ++ xs) /\ NoDupMembers (ws ++ xs).
  Proof.
    induction ws as [|w ws IH]; repeat split.
    - apply nodupmembers_cons in H. intuition.
    - apply nodupmembers_cons in H. intuition.
    - destruct 1 as [HH1 HH2].
      apply nodupmembers_cons. intuition.
    - destruct w as [w ww].
      simpl in H. apply nodupmembers_cons in H.
      destruct H as [H1 H2].
      apply IH in H2.
      destruct H2 as [H2 H3].
      intro HH. destruct HH as [HH|HH].
      + subst. apply H1.
        apply InMembers_app. right.
        now constructor.
      + apply H2. assumption.
    - destruct w as [w ww].
      simpl in *. apply nodupmembers_cons in H.
      destruct H as [H1 H2].
      apply IH in H2.
      apply nodupmembers_cons.
      destruct H2 as [H2 H3].
      apply NotInMembers_app in H1.
      destruct H1 as [H1 H4].
      apply NotInMembers_cons in H1.
      split; try apply NotInMembers_app; intuition.
    - destruct 1 as [H1 H2].
      destruct w as [w ww].
      simpl in H2. apply nodupmembers_cons in H2.
      destruct H2 as [H2 H3].
      simpl. apply nodupmembers_cons.
      split.
      + intro HH. apply H2.
        apply InMembers_app.
        apply InMembers_app in HH.
        destruct HH as [HH|HH]; [now auto|].
        destruct HH as [HH|HH]; [|now auto].
        exfalso; apply H1. subst.
        now constructor.
      + apply IH.
        split; [|assumption].
        intro HH. apply H1.
        constructor 2. assumption.
  Qed.

  Lemma NoDupMembers_remove_1:
    forall ws x xs,
      NoDupMembers (ws ++ x :: xs) -> NoDupMembers (ws ++ xs).
  Proof.
    intros ** HH.
    destruct x. apply NoDupMembers_app_cons in HH. intuition.
  Qed.

   Lemma NoDupMembers_app_assoc:
    forall ws xs,
      NoDupMembers (ws ++ xs) <-> NoDupMembers (xs ++ ws).
  Proof.
    induction ws as [|w ws IH]; split; intro HH.
    - rewrite app_nil_r. assumption.
    - rewrite app_nil_r in HH. assumption.
    - destruct w as [w ww].
      simpl in HH; apply nodupmembers_cons in HH.
      destruct HH as [HH1 HH2].
      apply NoDupMembers_app_cons.
      apply NotInMembers_app_comm in HH1.
      split; [assumption|].
      apply IH. assumption.
    - destruct w as [w ww].
      apply NoDupMembers_app_cons in HH.
      destruct HH as [HH1 HH2].
      apply IH in HH2.
      simpl; apply NoDupMembers_cons.
      now apply NotInMembers_app_comm.
      assumption.
  Qed.

  Lemma NoDupMembers_app:
    forall ws xs,
      NoDupMembers (ws ++ xs) <-> NoDupMembers (xs ++ ws).
  Proof.
    induction ws as [|w ws IH]; split; intro HH.
    - rewrite app_nil_r. assumption.
    - rewrite app_nil_r in HH. assumption.
    - destruct w as [w ww].
      simpl in HH; apply nodupmembers_cons in HH.
      destruct HH as [HH1 HH2].
      apply NoDupMembers_app_cons.
      apply NotInMembers_app_comm in HH1.
      split; [assumption|].
      apply IH. assumption.
    - destruct w as [w ww].
      apply NoDupMembers_app_cons in HH.
      destruct HH as [HH1 HH2].
      apply IH in HH2.
      simpl; apply NoDupMembers_cons.
      now apply NotInMembers_app_comm.
      assumption.
  Qed.

  Lemma NoDupMembers_app_r:
    forall ws xs,
      NoDupMembers (ws ++ xs) -> NoDupMembers xs.
  Proof.
    induction ws as [|w ws IH]; auto.
    intros xs H.
    apply IH.
    rewrite <-app_comm_cons in H.
    destruct w; rewrite nodupmembers_cons in H; tauto.
  Qed.

  Lemma NoDupMembers_app_l:
    forall ws xs,
      NoDupMembers (ws ++ xs) -> NoDupMembers ws.
  Proof.
    intros ** Hndup.
    apply NoDupMembers_app_assoc in Hndup.
    apply NoDupMembers_app_r with (1:=Hndup).
  Qed.

  Lemma NoDupMembers_app_InMembers:
    forall x xs ws,
      NoDupMembers (xs ++ ws) ->
      InMembers x xs ->
      ~InMembers x ws.
  Proof.
    induction ws as [|w ws IH]; auto.
    intros Nodup Hin H.
    destruct w; simpl in H.
    destruct H.
    - apply NoDupMembers_app_cons in Nodup.
      destruct Nodup as (Notin & ?).
      apply NotInMembers_app in Notin.
      subst.
      destruct Notin as (? & Notin); now apply Notin. 
    - apply NoDupMembers_remove_1 in Nodup.
      apply IH; auto.
  Qed.
  
  Lemma NoDupMembers_det:
    forall x t t' xs,
      NoDupMembers xs ->
      In (x, t) xs ->
      In (x, t') xs ->
      t = t'.
  Proof.
    induction xs; intros H Hin Hin'.
    - contradict Hin.
    - inversion Hin; inversion Hin'; subst.
      + inversion H1; auto.
      + inversion H; subst.
        inversion Hin'.
        * inversion H0; auto.
        * exfalso. apply H3. eapply In_InMembers; eauto.
      + inversion H; subst.
        inversion Hin.
        * inversion H1; auto.
        * exfalso. apply H3. eapply In_InMembers; eauto.
      + apply IHxs; auto.
        destruct a; rewrite nodupmembers_cons in H; tauto. 
  Qed.

  Global Instance NoDupMembers_Permutation_Proper:
    Proper (Permutation (A:=A * B) ==> iff) NoDupMembers.
  Proof.
    intros xs ys Hperm.
    induction Hperm.
    - now intuition.
    - destruct x as [x y].
      rewrite 2 nodupmembers_cons, IHHperm, Hperm.
      reflexivity.
    - split; intro HH.
      + inversion HH as [|a b l' Hninm Hndup]. clear HH. subst.
        destruct x as [x y].
        inversion Hndup as [|c d l' Hinm' Hndup']. clear Hndup. subst.
        econstructor.
        * intro Hinm. apply Hinm'.
          inversion_clear Hinm; subst; auto.
          exfalso; apply Hninm. now constructor.
        * constructor; auto. intro Hinm.
          apply Hninm. constructor (assumption).
      + inversion HH as [|a b l' Hninm Hndup]. clear HH. subst.
        destruct y as [x y].
        inversion Hndup as [|c d l' Hinm' Hndup']. clear Hndup. subst.
        econstructor.
        * intro Hinm. apply Hinm'.
          inversion_clear Hinm; subst; auto.
          exfalso; apply Hninm. now constructor.
        * constructor; auto. intro Hinm.
          apply Hninm. constructor (assumption).
    - now rewrite IHHperm1.
  Qed.

  Lemma InMembers_neq:
    forall x y xs,
      InMembers x xs ->
      ~ InMembers y xs ->
      x <> y.
  Proof.
    intros ** Hx Hy; subst.
    now apply Hx.
  Qed.

  Remark fst_InMembers:
    forall x xs,
      InMembers x xs <-> In x (map (@fst A B) xs).
  Proof.
    induction xs; simpl; intuition.
  Qed.

  Remark fst_NoDupMembers:
    forall xs,
      NoDupMembers xs <-> NoDup (map (@fst A B) xs).
  Proof.
    induction xs as [|(x,y)].
    - split; constructor.
    - simpl; split; inversion 1.
      + inversion H as [|? ? ? Notin ? Heq]; subst.
        constructor.
        * now rewrite <-fst_InMembers.
        * now apply IHxs.
      + constructor.
        * now rewrite fst_InMembers.
        * now apply IHxs.
  Qed.

  Lemma InMembers_In_combine:
    forall x (xs: list A) (ys: list B),
      InMembers x (combine xs ys) ->
      In x xs.
  Proof.
    induction xs as [|x' xs]; auto.
    destruct ys; [contradiction|].
    destruct 1 as [Heq|Hin].
    now subst; constructor.
    constructor (apply IHxs with (1:=Hin)).
  Qed.

  Lemma In_InMembers_combine:
    forall x (xs: list A) (ys: list B),
      length xs = length ys ->
      (In x xs <-> InMembers x (combine xs ys)).
  Proof.
    intros x xs ys Hlen.
    split; [|now apply InMembers_In_combine].
    revert x xs ys Hlen.
    induction xs as [|x' xs]; auto.
    intros ys Hlen Hin.
    destruct ys; [discriminate|].
    inversion Hin; subst; [now left|right].
    apply IHxs; auto.
  Qed.

  Lemma NoDup_NoDupMembers_combine:
    forall (xs: list A) (ys: list B),
    NoDup xs -> NoDupMembers (combine xs ys).
  Proof.
    induction xs as [|x xs]; [now intros; constructor|].
    intros ys Hndup.
    destruct ys; simpl; constructor.
    - inversion_clear Hndup.
      intro Hin. apply InMembers_In_combine in Hin.
      contradiction.
    - apply IHxs; auto. now inversion Hndup.
  Qed.

  Remark InMembers_snd_In:
    forall {C} y l,
      InMembers y (map (@snd C (A * B)) l) ->
      exists x z, In (x, (y, z)) l.
  Proof.
    induction l as [|(x', (y', z'))]; simpl; intros ** Hin.
    - contradiction.
    - destruct Hin as [|Hin].
      + subst y'; exists x', z'; now left.
      + apply IHl in Hin; destruct Hin as (x & z & Hin).
        exists x, z; now right.
  Qed.

  Remark In_InMembers_snd:
    forall {C} x y z l,
      In (x, (y, z)) l ->
      InMembers y (map (@snd C (A * B)) l).
  Proof.
    induction l as [|(x', (y', z'))]; simpl; intros ** Hin; auto.
    destruct Hin as [Eq|Hin].
    - inv Eq; now left.
    - right; auto.
  Qed.
End InMembers.

Ltac app_NoDupMembers_det :=
  match goal with
  | H: NoDupMembers ?xs,
         H1: In (?x, ?t1) ?xs,
             H2: In (?x, ?t2) ?xs |- _ =>
      assert (t1 = t2) by (eapply NoDupMembers_det; eauto); subst t2; clear H2 
    end.

Section Lists.

  Context {A B : Type}.
  
  Fixpoint concat (l : list (list A)) : list A :=
    match l with
    | nil => nil
    | cons x l => x ++ concat l
    end.

  Lemma concat_nil : concat nil = nil.
  Proof eq_refl. 

  Lemma concat_cons : forall x l, concat (cons x l) = x ++ concat l.
  Proof. simpl; reflexivity. Qed.
                               
  Lemma concat_app : forall l1 l2, concat (l1 ++ l2) = concat l1 ++ concat l2.
  Proof.
    induction l1; auto.
    intro.
    rewrite <-app_comm_cons.
    repeat rewrite concat_cons.
    rewrite <-app_assoc.
    f_equal; auto.
  Qed.

  Global Instance In_Permutation_Proper (A:Type):
    Proper (eq ==> Permutation (A:=A) ==> iff) (@In A).
  Proof.
    intros x y Hxy xs ys Hperm.
    subst y.
    split; intro HH; [|symmetry in Hperm];
      now apply Permutation_in with (1:=Hperm) in HH.
  Qed.

  Remark not_In_app:
    forall (x: A) l1 l2,
      ~ In x l2 ->
      In x (l1 ++ l2) ->
      In x l1.
  Proof.
    intros ** HnIn Hin.
    induction l1.
    - contradiction.
    - rewrite <-app_comm_cons in Hin.
      inversion Hin; subst.
      + apply in_eq.
      + right; now apply IHl1.
  Qed.
  
  Remark In_Forall:
    forall (x: A) xs P,
      Forall P xs ->
      In x xs ->
      P x.
  Proof.
    intros ** Hforall Hin.
    induction xs; inversion Hin; inversion Hforall; subst; auto.
  Qed.

  Lemma map_cons (x:A)(l:list A) (f: A -> B) : map f (x::l) = (f x) :: (map f l).
  Proof.
    reflexivity.
  Qed.
                                                   
  Remark map_cons':
    forall (f: A -> A) l y ys,
      map f l = y :: ys ->
      exists x xs, y = f x /\ ys = map f xs.
  Proof.
    destruct l; simpl; intros ** H.
    - contradict H. apply nil_cons.
    - exists a, l. inversion H; auto.
  Qed.

  Remark map_app':
    forall (f: A -> A) l1 l l2,
      map f l = l1 ++ l2 ->
      exists k1 k2, l1 = map f k1 /\ l2 = map f k2.
  Proof.
    induction l1; simpl; intros ** H.
    - exists [], l; auto.
    - apply map_cons' in H.
      destruct H as (x & xs & Ha & Happ).
      symmetry in Happ.
      apply IHl1 in Happ.
      destruct Happ as (k1 & k2 & Hl1 & Hl2).
      exists (x :: k1), k2; simpl; split; auto.
      f_equal; auto.
  Qed.

  Lemma incl_cons':
    forall (x: A) xs ys,
      incl (x :: xs) ys -> In x ys /\ incl xs ys.
  Proof.
    unfold incl; intuition.
  Qed.

  Lemma incl_nil:
    forall (xs: list A),
      incl xs [] -> xs = [].
  Proof.
    intros xs H.
    induction xs; auto.
    unfold incl in H.
    specialize (H a (in_eq a xs)).
    contradict H.
  Qed.

  Lemma Permutation_incl1:
    forall (ws: list A) xs ys,
      Permutation xs ys ->
      (incl xs ws <-> incl ys ws).
  Proof.
    intros ** Hperm.
    induction Hperm.
    - reflexivity.
    - split; intro HH.
      + apply incl_cons' in HH.
        destruct HH as [Hin Hincl].
        apply IHHperm in Hincl.
        apply incl_cons; auto.
      + apply incl_cons' in HH.
        destruct HH as [Hin Hincl].
        apply IHHperm in Hincl.
        apply incl_cons; auto.
    - split; intro HH.
      + apply incl_cons' in HH.
        destruct HH as (Hiny & HH).
        apply incl_cons' in HH.
        destruct HH as (Hinx & Hincl).
        repeat (apply incl_cons; auto).
      + apply incl_cons' in HH.
        destruct HH as (Hinx & HH).
        apply incl_cons' in HH.
        destruct HH as (Hiny & Hincl).
        repeat (apply incl_cons; auto).
    - now rewrite IHHperm1, IHHperm2.
  Qed.      

  Global Instance Permutation_incl_Proper:
    Proper (@Permutation A ==> @Permutation A ==> iff) (@incl A).
  Proof.
    intros xs ys Hperm xs' ys' Hperm'.
    induction Hperm'; try rewrite (Permutation_incl1 _ _ _ Hperm).
    - reflexivity.
    - split; intro HH.
      + intros y Hin.
        apply HH in Hin.
        inversion_clear Hin as [|Hin'].
        now subst; constructor.
        rewrite Hperm' in Hin'.
        constructor (assumption).
      + intros y Hin.
        apply HH in Hin.
        inversion_clear Hin as [|Hin'].
        now subst; constructor.
        rewrite <-Hperm' in Hin'.
        constructor (assumption).
    - split; intro HH.
      + intros z Hin. apply HH in Hin. now rewrite perm_swap.
      + intros z Hin. apply HH in Hin. now rewrite perm_swap.
    - rewrite (Permutation_incl1 _ _ _ Hperm) in IHHperm'1.
      rewrite (Permutation_incl1 _ _ _ Hperm) in IHHperm'2.
      now rewrite IHHperm'1, IHHperm'2.
  Qed.

  Lemma app_last_app:
    forall xs xs' (x: A),
      (xs ++ [x]) ++ xs' = xs ++ x :: xs'.
  Proof.
    induction xs; simpl; auto.
    intros; f_equal; apply IHxs.
  Qed.

  Lemma Forall2_length :
    forall (P : A -> B -> Prop) l1 l2,
      Forall2 P l1 l2 -> length l1 = length l2.
  Proof.
    induction l1, l2; intros ** Hall; inversion Hall; clear Hall; subst; simpl; auto.    
  Qed.

  (* should be in standard lib... *)
  Lemma not_in_cons (x a : A) (l : list A):
    ~ In x (a :: l) <-> x <> a /\ ~ In x l.
  Proof.
    split.
    - intro Notin.
      split.
      + intro Eq.
        apply Notin.
        rewrite Eq.
        apply in_eq.
      + intro In.
        apply Notin.
        apply in_cons; auto.
    - intros [Neq Notin] In.
      apply in_inv in In.
      destruct In.
      + apply Neq; auto.
      + apply Notin; auto.
  Qed.

  Lemma Forall_impl_In :
    forall (P Q : A -> Prop) l,
      (forall a, In a l -> P a -> Q a) ->
      Forall P l -> Forall Q l.
  Proof.
    induction l; auto.
    intros H HP.
    inversion_clear HP.
    constructor.
    - apply H; auto.
      apply in_eq.
    - apply IHl; auto.
      intros a' Ha' HP.
      apply H; auto.
      apply in_cons; auto.
  Qed.

  Lemma NoDup_map_inv (f:A->B) l : NoDup (map f l) -> NoDup l.
  Proof.
    induction l; simpl; inversion_clear 1; subst; constructor; auto.
    intro H. now apply (in_map f) in H.
  Qed.

  Lemma NoDup_cons':
    forall {A} (x:A) xs,
      NoDup (x::xs) <-> ~In x xs /\ NoDup xs.
  Proof.
    split; intro HH.
    - inversion_clear HH. intuition.
    - destruct HH. constructor; auto.
  Qed.
  
  Global Instance NoDup_Permutation_Proper (A:Type):
    Proper (Permutation (A:=A) ==> iff) (@NoDup A).
  Proof.
    intros xs ys Hperm.
    induction Hperm.
    - now intuition.
    - rewrite 2 NoDup_cons', IHHperm, Hperm.
      reflexivity.
    - split; inversion_clear 1 as [|? ? Hnin Hndup];
        inversion_clear Hndup as [|? ? Hnin' Hndup'];
        (constructor; [|constructor]); auto; intro Hnin3;
          apply Hnin.
      + inversion Hnin3; [|contradiction].
        subst. now constructor.
      + constructor (assumption).
      + inversion Hnin3; [|contradiction].
        subst. now constructor.
      + constructor (assumption).
    - now rewrite IHHperm1, IHHperm2.
  Qed.

  Lemma NoDup_app_weaken:
    forall {A} (xs: list A) ys,
      NoDup (xs ++ ys) ->
      NoDup xs.
  Proof.
    Hint Constructors NoDup.
    intros ** Hndup.
    induction xs as [|x xs]; auto.
    inversion_clear Hndup as [|? ? Hnin Hndup'].
    apply IHxs in Hndup'.
    constructor; auto.
    intro Hin. apply Hnin.
    apply in_or_app; now left.
  Qed.
  
  Lemma cons_is_app:
    forall (x: A) xs,
      x :: xs = [x] ++ xs.
  Proof.
    destruct xs; simpl; auto.
  Qed.

  Lemma in_app:
  forall (x: A) (l1 l2: list A), In x (l1 ++ l2) <-> In x l1 \/ In x l2.
  Proof.
    intros. split; intro. apply in_app_or. auto. apply in_or_app. auto.
  Qed.

  Lemma permutation_partition:
    forall p (l: list A),
      Permutation l (fst (partition p l) ++ snd (partition p l)).
  Proof.
    induction l as [|x l].
    now constructor.
    simpl.
    destruct (p x).
    - rewrite (surjective_pairing (partition _ _)).
      now simpl; apply Permutation_cons.
    - rewrite (surjective_pairing (partition _ _)).
      now simpl; apply Permutation_cons_app.
  Qed.

  Lemma Permutation_app_assoc:
    forall (ws: list A) xs ys,
      Permutation ((ws ++ xs) ++ ys) (ws ++ xs ++ ys).
  Proof.
    intros.
    induction ws.
    reflexivity.
    now apply Permutation_cons.
  Qed.

  Global Instance Permutation_app_Proper2 (xs: list A):
    Proper (Permutation (A:=A) ==> Permutation (A:=A))
           (app (A:=A) xs).
  Proof.
    intros ys ws Hperm.
    now apply Permutation_app_head.
  Qed.
  
  Global Instance Permutation_app_Proper3:
    Proper (Permutation (A:=A) ==> (@eq (list A)) ==> Permutation (A:=A))
           (app (A:=A)).
  Proof.
    intros xs ys Hperm ws1 ws2 Heq.
    rewrite Heq.
    rewrite (Permutation_app_comm xs), (Permutation_app_comm ys).
    now apply Permutation_app_head.
  Qed.

  Lemma partition_switch:
    forall f g,
      (forall x:A, f x = g x) ->
      forall xs, partition f xs = partition g xs.
  Proof.
    intros ** Hfg xs.
    induction xs as [|x xs]; auto. simpl.
    specialize (Hfg x). symmetry in Hfg. rewrite Hfg, IHxs.
    reflexivity.
  Qed.

  Lemma partition_filter:
    forall P (xs: list A),
      Permutation (fst (partition P xs)) (filter P xs).
  Proof.
    induction xs as [|x xs]; auto.
    simpl; rewrite (surjective_pairing (partition P xs)).
    destruct (P x); auto.
    now apply Permutation_cons.
  Qed.
  
  Lemma filter_app:
    forall (p:A->bool) xs ys,
      filter p xs ++ filter p ys = filter p (xs ++ ys).
  Proof.
    induction xs as [|x xs]; intro ys; auto.
    simpl; destruct (p x); simpl; rewrite IHxs; auto.
  Qed.

  Global Instance Permutation_filter_Proper (p:A->bool):
    Proper (@Permutation A ==> @Permutation A) (filter p).
  Proof.
    Hint Constructors Permutation.
    intros xs ys Hperm.
    induction Hperm; simpl; auto.
    - destruct (p x); auto.
    - destruct (p x); destruct (p y); auto.
    - now rewrite IHHperm1, IHHperm2.
  Qed.
  
  Remark in_concat_cons:
    forall l' (l: list A) x xs,
      In x l ->
      In (xs :: l) l' ->
      In x (concat l').
  Proof.
    induction l' as [|y]; simpl; intros ** Hin Hin'.
    - contradiction.
    - destruct Hin' as [E|Hin'].
      + subst y.
        apply in_app; left; now apply in_cons.
      + apply in_app; right.
        eapply IHl'; eauto.
  Qed.

  Remark in_concat:
    forall l' (l: list A) x,
      In x l ->
      In l l' ->
      In x (concat l').
  Proof.
    induction l' as [|y]; simpl; intros ** Hin Hin'.
    - contradiction.
    - destruct Hin' as [E|Hin'].
      + subst y.
        apply in_app; now left.
      + apply in_app; right.
        eapply IHl'; eauto.
  Qed.

  Remark split_map:
    forall {C} (xs: list C) (l: list A) (l': list B) f f',
      split (map (fun x => (f x, f' x)) xs) = (l, l') ->
      l = map f xs /\ l' = map f' xs.
  Proof.
    induction xs; simpl; intros ** Split.
    - inv Split; auto.
    - destruct (split (map (fun x : C => (f x, f' x)) xs)) as (g, d) eqn: E.
      inv Split.
      edestruct IHxs as [G D]; eauto; rewrite <-G, <-D; auto.
  Qed.

  Remark In_singleton:
    forall (y x: A),
      In y [x] <-> y = x.
  Proof.
    split; intro H.
    - simpl in H; destruct H; auto.
      contradiction.
    - subst x; apply in_eq.
  Qed.
  
  Remark equiv_eq_singleton:
    forall (x: A) l,
      NoDup l ->
      ([x] = l <-> (forall y, In y l <-> In y [x])).
  Proof.
    intros ** Nodup.
    split.
    - intros; subst l; split; auto.
    - destruct l; intro H.
      + specialize (H x); destruct H as [? H'].
        exfalso; apply H'; now left.
      + inversion_clear Nodup as [|? ? Notin].
        destruct l.
        * specialize (H x); rewrite 2 In_singleton in H.
          f_equal; now apply H.
        * pose proof H as H'.
          specialize (H a); rewrite In_singleton in H.
          specialize (H' a0); rewrite In_singleton in H'.
          destruct H as [Ha].
          destruct H' as [Ha0].
          assert (a = a0).
          { transitivity x.
            - apply Ha, in_eq.
            - symmetry; apply Ha0, in_cons, in_eq.
          }
          exfalso; apply Notin.
          subst; apply in_eq.
  Qed.

  Lemma Forall_Forall':
    forall (A : Type) (P Q : A -> Prop) (xs : list A),
      Forall P xs /\ Forall Q xs <-> Forall (fun x : A => P x /\ Q x) xs.
  Proof.
    split.
    - intros [? ?]; now apply Forall_Forall.
    - intro HForall.
      induction xs as [|x xs]; split; auto; inv HForall; constructor; tauto.      
  Qed.

  Lemma NoDup_app_cons:
    forall ws (x: A) xs,
      NoDup (ws ++ x :: xs)
      <-> ~In x (ws ++ xs) /\ NoDup (ws ++ xs).
  Proof.
    induction ws; simpl; split; intros ** Nodup.
    - inv Nodup; auto. 
    - destruct Nodup; auto. 
    - inversion Nodup as [|? ? Notin Nodup']; clear Nodup; subst.
      split.
      + intro H; destruct H.
        * subst; apply Notin.
          apply in_app; right; apply in_eq.
        * apply NoDup_remove_2 in Nodup'.
          contradiction.
      + constructor.
        * intro Hin; apply Notin.
          apply in_app_or in Hin.
          destruct Hin; apply in_app; auto.
          right; now apply in_cons.
        * now apply NoDup_remove_1 in Nodup'.
    - destruct Nodup as [Notin Nodup].
      inversion Nodup as [|? ? Notin' Nodup']; clear Nodup; subst.
      constructor.
      + intro Hin.
        apply in_app_or in Hin.
        destruct Hin; apply Notin', in_app; auto.
        simpl in H; destruct H; auto.
        subst; contradict Notin; now left.  
      + rewrite IHws; split; auto.
  Qed.
  
  Lemma NoDup_app:
    forall (ws xs: list A),
      NoDup (ws ++ xs) <-> NoDup (xs ++ ws).
   Proof.
     induction ws; simpl; split; intros ** Nodup.
     - now rewrite app_nil_r.
     - now rewrite app_nil_r in Nodup.
     - inversion Nodup as [|? ? Notin' Nodup']; clear Nodup; subst.
       rewrite NoDup_app_cons; split.
       + intro Hin; apply in_app_or in Hin.
         destruct Hin; apply Notin', in_app; auto.
       + now rewrite <-IHws.
     - constructor.
       + apply NoDup_remove_2 in Nodup.
         intro Hin; apply in_app_or in Hin.
         destruct Hin; apply Nodup, in_app; auto.
       + rewrite NoDup_app_cons in Nodup.
         destruct Nodup.
         now rewrite IHws.
   Qed.
   
End Lists.

(** adds and its properties *)

Definition adds {A} xs (vs : list A) (e : PM.t A) :=
  fold_right (fun (xv: ident * A) env => 
                let (x , v) := xv in
                PM.add x v env) e (combine xs vs).

Lemma find_gsso:
  forall {A} x x' xs (vs: list A) S,
    x <> x' ->
    PM.find x (adds (x' :: xs) vs S) = PM.find x (adds xs (tl vs) S).
Proof.
  intros ** Hneq.
  unfold adds.
  destruct vs. destruct xs; reflexivity.
  simpl. rewrite PM.gso; auto.
Qed.      

Lemma NotInMembers_find_adds:
  forall {A} x xs (v: option A) vs S,
    ~In x xs ->
    PM.find x S = v ->
    PM.find x (adds xs vs S) = v.
Proof.
  induction xs as [|xty xs]; auto.
  intros v vs S Hnin Hfind.
  apply not_in_cons in Hnin.
  destruct Hnin as [Hnin Hneq].
  rewrite find_gsso; auto.
Qed.

Lemma adds_cons_cons:
  forall {A} xs x (v: A) vs e,
    ~ In x xs ->
    adds (x :: xs) (v :: vs) e = adds xs vs (PM.add x v e).
Proof.
  unfold adds.
  induction xs as [|x']; intros ** NotIn; simpl; auto.
  destruct vs as [|v']; simpl; auto.
  rewrite <-IHxs.
  - simpl.
    rewrite add_comm; auto.
    intro Eq.
    apply NotIn; subst.
    apply in_eq.
  - now apply not_in_cons in NotIn.
Qed.


Ltac induction_list_tac e I l H :=
  match type of e with
    list ?A =>
    let Eq := fresh in
    let Eql := H in
    remember e as l eqn:Eq;
      assert (exists l', e = l' ++ l) as Eql by (exists (@nil A); simpl; auto);
      clear Eq; move Eql at top; induction l as I;
      [clear Eql|
       match goal with
         IH: (exists l', e = l' ++ ?l'') -> ?P,
             EQ: (exists l', e = l' ++ ?x::?xs) |- _ =>
         let l' := fresh l in
         let E := fresh in
         destruct EQ as [l' Eql];
           rewrite <-app_last_app in Eql;
           assert (exists l', e = l' ++ xs) as E by (exists (l' ++ [x]); auto);
           specialize (IH E); clear E
       end]
  end.

(* Tactic Notation "induction_list" constr(E) "as" simple_intropattern(I) "with" ident(l) "eq:" ident(H) := *)
(*   induction_list_tac E I l H. *)
Tactic Notation "induction_list" constr(E) "as" simple_intropattern(I) "with" ident(l) :=
  let H := fresh "H" l in
  induction_list_tac E I l H.
Tactic Notation "induction_list" constr(E) "as" simple_intropattern(I) :=
  let l := fresh "l" in
  induction_list E as I with l.
Tactic Notation "induction_list" constr(E) :=
  induction_list E as [|].
(* Tactic Notation "induction_list" constr(E) "with" ident(l) "eq:" ident(H) := *)
(*   induction_list E as [|] with l eq:H. *)
(* Tactic Notation "induction_list" constr(E) "as" simple_intropattern(I) "eq:" ident(H) := *)
(*   let l := fresh "l" in *)
(*   induction_list E as I with l eq:H. *)
Tactic Notation "induction_list" constr(E) "with" ident(l) :=
  induction_list E as [|] with l.
(* Tactic Notation "induction_list" constr(E) "eq:" ident(H) := *)
(*   let l := fresh "l" in *)
(*   induction_list E as [|] with l eq:H. *)

(* Tactic Notation "induction_list" ident(E) "as" simple_intropattern(I) "with" ident(l) := *)
(*   let H := fresh "H" l in *)
(*   induction_list_tac E I l H. *)

