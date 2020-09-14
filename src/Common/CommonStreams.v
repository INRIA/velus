From Coq Require Import Setoid.
From Coq Require Import Streams.

(** Additional streams utilities *)

Delimit Scope stream_scope with Stream.
Infix "⋅" := Cons (at level 60, right associativity) : stream_scope.
Infix "≡" := EqSt (at level 70, no associativity) : stream_scope.
Notation "s # n " := (Str_nth n s) (at level 9) : stream_scope.
Open Scope stream_scope.

Fact Str_nth_0:
  forall {A} (xs: Stream A) x,
    (x ⋅ xs) # 0 = x.
Proof. reflexivity. Qed.

Fact Str_nth_S:
  forall {A} (xs: Stream A) x n,
    (x ⋅ xs) # (S n) = xs # n.
Proof. reflexivity. Qed.

Fact Str_nth_S_tl:
  forall {A} (xs: Stream A) n,
    xs # (S n) = (tl xs) # n.
Proof. reflexivity. Qed.

Section map.
  Context {A B : Type}.

  Variable (f : (A -> B)).

  Lemma map_Cons : forall a (sa : Stream A),
      (map f (a ⋅ sa)) = ((f a) ⋅ (map f sa)).
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
    | hda ⋅ tla, hdb ⋅ tlb =>
      (f hda hdb) ⋅ (map2 tla tlb)
    end.

  Lemma map2_Cons : forall a b (sa : Stream A) (sb : Stream B),
      (map2 (a ⋅ sa) (b ⋅ sb)) = ((f a b) ⋅ (map2 sa sb)).
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

Section Forall.
  Context {A : Type}.
  Variable (P : A -> Prop).

  CoInductive SForall : Stream A -> Prop :=
  | Forall_Cons : forall a sa,
      P a ->
      SForall sa ->
      SForall (a ⋅ sa).

  Lemma SForall_forall : forall sa,
      SForall sa <-> forall n, P (Str_nth n sa).
  Proof with auto.
    intros sa.
    split; intros H.
    - intro n; revert n sa H.
      induction n; intros [a sa] Hf; inversion Hf; subst.
      + rewrite Str_nth_0...
      + rewrite Str_nth_S...
    - revert sa H.
      cofix forall_Forall.
      intros [a sa] H. constructor.
      + specialize (H 0). rewrite Str_nth_0 in H...
      + apply forall_Forall.
        intro n. specialize (H (S n)).
        rewrite Str_nth_S in H...
  Qed.
End Forall.
