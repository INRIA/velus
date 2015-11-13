Require Import Rustre.Common.
Require Import Rustre.DataflowSyntax.

Inductive value :=
  | absent
  | present (v : const).
(* Coercion present : const >-> value. *)

Definition stream A := nat -> A.
Definition vstream := stream value.
Definition cstream := stream bool.

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

(** Synchronous functions *)

(* With auxiliary hold function. *)

Fixpoint hold (v0: const) (xs: stream value) (n: nat) : const :=
  match n with
  | 0 => v0
  | S m => match xs m with
           | absent => hold v0 xs m
           | present hv => hv
           end
  end.

Definition fby (v0: const) (xs: stream value) (n: nat) : value :=
  match xs n with
  | absent => absent
  | _ => present (hold v0 xs n)
  end.

