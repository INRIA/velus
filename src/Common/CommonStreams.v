From Coq Require Import Setoid.
From Coq Require Import Streams.

(** Additional streams utilities *)

Section map.
  Context {A B : Type}.

  Variable (f : (A -> B)).

  Lemma map_Cons : forall a (sa : Stream A),
      (map f (Cons a sa)) = (Cons (f a) (map f sa)).
  Proof.
    intros a sa; simpl.
    rewrite unfold_Stream at 1; reflexivity.
  Qed.
End map.

Section map2.
  Context {A B C : Type}.

  Variable (f : (A -> B -> C)).

  CoFixpoint map2 (sa : Stream A) (sb : Stream B) : Stream C :=
    match sa, sb with
    | Cons hda tla, Cons hdb tlb =>
      Cons (f hda hdb) (map2 tla tlb)
    end.

  Lemma map2_Cons : forall a b (sa : Stream A) (sb : Stream B),
      (map2 (Cons a sa) (Cons b sb)) = (Cons (f a b) (map2 sa sb)).
  Proof.
    intros a b sa sb; simpl.
    rewrite unfold_Stream at 1; reflexivity.
  Qed.

  Lemma map2_hd : forall (sa : Stream A) (sb : Stream B),
      f (hd sa) (hd sb) = hd (map2 sa sb).
  Proof. intros [a sa] [b sb]; reflexivity. Qed.

  Lemma map2_tl : forall (sa : Stream A) (sb : Stream B),
      map2 (tl sa) (tl sb) = tl (map2 sa sb).
  Proof. intros [a sa] [b sb]; reflexivity. Qed.

  Lemma Str_nth_tl_map2 : forall n (sa : Stream A) (sb : Stream B),
      Str_nth_tl n (map2 sa sb) = map2 (Str_nth_tl n sa) (Str_nth_tl n sb).
  Proof.
    induction n; intros sa sb; simpl.
    - reflexivity.
    - destruct sa. destruct sb. simpl.
      auto.
  Qed.

  Lemma Str_nth_map2 : forall n (sa : Stream A) (sb : Stream B),
      Str_nth n (map2 sa sb) = f (Str_nth n sa) (Str_nth n sb).
  Proof.
    unfold Str_nth.
    induction n; intros [hda tla] [hdb tlb].
    - reflexivity.
    - simpl. auto.
  Qed.
End map2.

Add Parametric Relation A : (Stream A) (@EqSt A)
    reflexivity proved by (@EqSt_reflex A)
    symmetry proved by (@sym_EqSt A)
    transitivity proved by (@trans_EqSt A)
      as EqStrel.

Add Parametric Morphism A B C f : (@map2 A B C f)
    with signature (@EqSt A) ==> (@EqSt B) ==> (@EqSt C) as map2_EqSt.
Proof.
  cofix map2_EqSt.
  intros [? ?] [? ?] Eqa [? ?] [? ?] Eqb.
  inversion Eqa; simpl in *; subst; clear Eqa.
  inversion Eqb; simpl in *; subst; clear Eqb.
  rewrite map2_Cons. rewrite map2_Cons.
  constructor; simpl; auto.
Qed.
