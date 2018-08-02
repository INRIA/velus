Require Import Velus.Common.
Require Import Velus.Operators.

Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Arith.EqNat.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * Extensional model of synchronous streams *)

(** Our model is extensional in the sense that it encodes a
coinductive, infinite datastructure (streams) with a function of
domain [nat]. To reason about this object, we shall use functional
extensionality [ Logic.FunctionalExtensionality]. This axiom is
believed to be consistent with Coq. *)

Module Type STREAM
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op).

  (** ** Datatypes *)

  (** A stream is represented by its characteristic function: *)

  Notation stream A := (nat -> A).

  Definition eq_str {A} (xs xs': stream A) := forall n, xs n = xs' n.
  Infix "≈" := eq_str (at level 70, no associativity).

  Lemma eq_str_refl:
    forall {A} (xs: stream A),
      xs ≈ xs.
  Proof.
    intros ** n; reflexivity.
  Qed.

  Lemma eq_str_sym:
    forall {A} (xs xs': stream A),
      xs ≈ xs' -> xs' ≈ xs.
  Proof.
    intros ** E n; auto.
  Qed.

  Lemma eq_str_trans:
    forall {A} (xs ys zs: stream A),
      xs ≈ ys -> ys ≈ zs -> xs ≈ zs.
  Proof.
    intros ** E1 E2 n; auto.
    rewrite E1; auto.
  Qed.

  Add Parametric Relation A : (stream A) (@eq_str A)
      reflexivity proved by (@eq_str_refl A)
      symmetry proved by (@eq_str_sym A)
      transitivity proved by (@eq_str_trans A)
        as eq_str_rel.

  (** A synchronous stream thus maps time to synchronous values: *)

  Notation vstream := (stream value).
  Implicit Type vs : vstream.

  (** A clock is a stream that returns [true] if the clocked stream
contains a value ([present c]) at the corresponding instant, [false]
if the clocked stream is [absent] at the corresponding instant. *)

  Notation cstream := (stream bool).
  Implicit Type cs : cstream.

  (** ** Synchronous functions *)

  Fixpoint hold (v0: val) (xs: stream value) (n: nat) : val :=
    match n with
    | 0 => v0
    | S m => match xs m with
            | absent => hold v0 xs m
            | present hv => hv
            end
    end.

  Definition fby (v0: val) (xs: stream value) : stream value :=
    fun n =>
      match xs n with
      | absent => absent
      | _ => present (hold v0 xs n)
      end.

  (** Count the number of resets ticks seen at [n] so far. *)
  (* Fixpoint count (rs: cstream) (n: nat) : nat := *)
  (*   match n, rs n with *)
  (*   | 0, false => 0 *)
  (*   | 0, true => 1 *)
  (*   | S m, false => count rs m *)
  (*   | S m, true => S (count rs m) *)
  (*   end. *)
  Fixpoint count (rs: cstream) (n: nat) : nat :=
    let c := match n with 0 => 0 | S n => count rs n end in
    if rs n then S c else c.

  (** [mask o k rs xs] is the stream which clips the stream [xs] between
      the [k]th and the [(k+1)]th reset, outputting [o] everywhere else. *)
  Definition mask {A} (opaque: A) (k: nat) (rs: cstream) (xs: stream A) : stream A :=
    fun n =>
      if beq_nat k (count rs n) then xs n else opaque.

  (* Definition masked {A} (k: nat) (rs: cstream) (xs xs': stream A) := *)
  (*   forall n, count rs n = k -> xs' n = xs n. *)

  (** ** Properties *)

  Lemma hold_abs:
    forall n c xs,
      xs n = absent ->
      hold c xs n = hold c xs (S n).
  Proof.
    destruct n; intros ** E; simpl; now rewrite E.
  Qed.

  Lemma hold_pres:
    forall v n c xs,
      xs n = present v ->
      v = hold c xs (S n).
  Proof.
    destruct n; intros ** E; simpl; now rewrite E.
  Qed.

  Lemma count_le:
    forall r n,
      count r n <= count r (S n).
  Proof.
    intros; simpl.
    destruct (r (S n)); omega.
  Qed.

  Lemma count_true_ge_1:
    forall n r,
      r n = true ->
      1 <= count r n.
  Proof.
    induction n; simpl; intros ** E; rewrite E; auto.
    apply Le.le_n_S; omega.
  Qed.

  Lemma count_positive:
    forall r n' n,
      r n = true ->
      n' < n ->
      count r n' < count r n.
  Proof.
    intros ** Rn Lt.
    destruct n; try omega.
    simpl; rewrite Rn.
    clear Rn.
    apply Lt.lt_n_Sm_le, Lt.le_lt_or_eq in Lt; destruct Lt.
    - induction n; try omega.
      apply Lt.lt_n_Sm_le, Lt.le_lt_or_eq in H; destruct H.
      + eapply Lt.lt_le_trans; eauto.
        apply Le.le_n_S, count_le.
      + subst.
        apply Lt.le_lt_n_Sm, count_le.
    - subst; omega.
  Qed.

  Lemma mask_opaque:
    forall {A} (xs: stream A) k r (opaque: A) n,
      count r n <> k ->
      (mask opaque k r xs) n = opaque.
  Proof.
    intros ** E.
    unfold mask.
    assert (EqNat.beq_nat k (count r n) = false) as ->
        by (apply EqNat.beq_nat_false_iff; omega); auto.
  Qed.

  Lemma mask_transparent:
    forall {A} (xs: stream A) k r (opaque: A) n,
      count r n = k ->
      (mask opaque k r xs) n = xs n.
  Proof.
    intros ** E.
    unfold mask.
    assert (EqNat.beq_nat k (count r n) = true) as ->
        by (apply EqNat.beq_nat_true_iff; omega); auto.
  Qed.

  Add Parametric Morphism : count
      with signature eq_str ==> eq ==> eq
        as count_eq_str.
  Proof.
    intros ** E n.
    induction n; simpl; rewrite E; auto.
    now rewrite IHn.
  Qed.

  Add Parametric Morphism (A: Type) : (@mask A)
      with signature eq ==> eq ==> eq_str ==> eq_str ==> eq_str
        as mask_eq_str.
  Proof.
    intros ** E1 ? ? E2 n; unfold mask.
    now rewrite E1, E2.
  Qed.

  (* Add Parametric Morphism (A: Type) : (@masked A) *)
  (*     with signature eq ==> eq_str ==> eq_str ==> eq_str ==> Basics.impl *)
  (*       as masked_eq_str. *)
  (* Proof. *)
  (*   unfold masked. *)
  (*   intros k r r' Err' x x' Exx' y y' Eyy' M n C. *)
  (*   rewrite <-Exx', <-Eyy'. *)
  (*   apply M. *)
  (*   now rewrite Err'. *)
  (* Qed. *)

  Lemma present_injection:
    forall x y, x = y <-> present x = present y.
  Proof.
    split; intro H; [rewrite H|injection H]; auto.
  Qed.

  Lemma not_absent_present:
    forall x, x <> absent <-> exists c, x = present c.
  Proof.
    intros x.
    split; intro HH.
    destruct x; [intuition|eauto].
    destruct HH as [c HH]; rewrite HH.
    intro; discriminate.
  Qed.

End STREAM.

Module StreamFun
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op) <: STREAM Op OpAux.
  Include STREAM Op OpAux.
End StreamFun.
