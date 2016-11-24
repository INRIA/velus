Require Import Velus.Common.
Require Import Velus.Operators.

(** * Extensional model of synchronous streams *)

(** Our model is extensional in the sense that it encodes a
coinductive, infinite datastructure (streams) with a function of
domain [nat]. To reason about this object, we shall use functional
extensionality [ Logic.FunctionalExtensionality]. This axiom is
believed to be consistent with Coq. *)

Module Type STREAM (Import Op : OPERATORS).

  (** ** Datatypes *)

  (** A synchronous [value] is either an absence or a present constant *)

  Inductive value :=
  | absent
  | present (c : val).
  Implicit Type v : value.

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

  (* With auxiliary hold function. *)

  Fixpoint hold (v0: val) (xs: stream value) (n: nat) : val :=
    match n with
    | 0 => v0
    | S m => match xs m with
            | absent => hold v0 xs m
            | present hv => hv
            end
    end.

  Definition fby (v0: val) (xs: stream value) (n: nat) : value :=
    match xs n with
    | absent => absent
    | _ => present (hold v0 xs n)
    end.

  (** ** Properties *)

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

Module StreamFun (Import Op : OPERATORS) <: STREAM Op.
  Include STREAM Op.
End StreamFun.
