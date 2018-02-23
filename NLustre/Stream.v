Require Import Velus.Common.
Require Import Velus.Operators.

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

  (* (** ** Datatypes *) *)

  (** A stream is represented by its characteristic function: *)

  Notation stream A := (nat -> A).

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
  Fixpoint count (rs: cstream) (n: nat) : nat :=
    match n, rs n with
    | 0, false => 0
    | 0, true => 1
    | S m, false => count rs m
    | S m, true => 1 + count rs m
    end.

  (** [mask o k rs xs] is the stream which clips the stream [xs] between
      the [k]th and the [(k+1)]th reset, outputting [o] every elsewhere. *)
  Definition mask {A} (opaque: A) (k: nat) (rs: cstream) (xs: stream A) : stream A :=
    fun n =>
      if beq_nat k (count rs n) then xs n else opaque.

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

  Lemma count_true_ge_1:
    forall n r,
      r n = true ->
      1 <= count r n.
  Proof.
    induction n; simpl; intros ** E; rewrite E; auto.
    apply Le.le_n_S; omega.
  Qed.

  Lemma count_compat:
    forall n r r',
      (forall n, r n = r' n) ->
      count r n = count r' n.
  Proof.
    induction n; simpl; intros ** E; rewrite E; auto.
    erewrite IHn; eauto.
  Qed.

  Corollary mask_compat:
    forall {A} r r' k (o: A) xs,
      (forall n, r n = r' n) ->
      forall n, mask o k r xs n = mask o k r' xs n.
  Proof.
    intros; unfold mask.
    erewrite count_compat; eauto.
  Qed.

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
