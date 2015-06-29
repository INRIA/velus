Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.
Require Import Rustre.DataflowSyntax.

Inductive value :=
  | absent
  | present (v : const).
Coercion present : const >-> value.

Module PM := PositiveMap.

Definition stream := nat -> value.
Definition cstream := nat -> bool.

(** Synchronous functions *)

(* With auxiliary hold function. *)

Inductive holdR (v0: const) (xs: stream) : nat -> value -> Prop :=
| holdR0:
    holdR v0 xs 0 v0
| holdR_absent:
    forall v n,
      xs n = absent ->
      holdR v0 xs n v ->
      holdR v0 xs (S n) v
| holdR_present:
    forall n,
      xs n <> absent ->
      holdR v0 xs (S n) (xs n).

Inductive fbyR (v0: const) (xs: stream) : nat -> value -> Prop :=
| fbyR_absent:
    forall n,
      xs n = absent ->
      fbyR v0 xs n absent
| fbyR_present:
    forall v n,
      xs n <> absent ->
      holdR v0 xs n v ->
      fbyR v0 xs n v.

Fixpoint hold (v0: const) (xs: stream) (n: nat) : value :=
  match n with
  | 0 => v0
  | S m => match xs m with
           | absent => hold v0 xs m
           | hv => hv
           end
  end.

Definition fby (v0: const) (xs: stream) (n: nat) : value :=
  match xs n with
  | absent => absent
  | _ => hold v0 xs n
  end.

Lemma hold_rel1: forall v0 xs n, holdR v0 xs n (hold v0 xs n).
Proof.
  induction n.
  - cbv; auto using holdR0.
  - simpl. case_eq (xs n).
    + auto using holdR_absent.
    + intros v xsn; rewrite <- xsn.
      apply holdR_present.
      rewrite xsn; discriminate.
Qed.

Lemma hold_rel2: forall v0 xs n v, holdR v0 xs n v -> hold v0 xs n = v.
Proof.
  induction n as [|n IH].
  - inversion 1; auto.
  - intros v H; inversion_clear H as [|? ? xsn HR|? H1].
    + simpl; rewrite xsn; apply (IH v HR).
    + simpl. case_eq (xs n). contradiction. trivial.
Qed.

Lemma hold_rel: forall v0 xs n v, hold v0 xs n = v <-> holdR v0 xs n v.
Proof.
  split.
  intro H; rewrite <- H; apply hold_rel1.
  apply hold_rel2.
Qed.
    
Lemma fby_rel1: forall v0 xs n, fbyR v0 xs n (fby v0 xs n).
Proof.
  intros v0 xs n.
  unfold fby.
  case_eq (xs n).
  - auto using fbyR_absent.
  - intros v xsn.
    apply fbyR_present.
    + rewrite xsn; discriminate.
    + apply hold_rel; reflexivity.
Qed.

Lemma fby_rel2: forall v0 xs n v, fbyR v0 xs n v -> fby v0 xs n = v.
Proof.
  induction n.
  - inversion_clear 1 as [ ? H0 | ? ? ? HR].
    + unfold fby; rewrite H0; reflexivity.
    + unfold fby; case_eq (xs 0).
      contradiction. intros v1 xsn; apply hold_rel2; exact HR.
  - inversion_clear 1 as [ ? H0 | ? ? ? HR].
    + unfold fby; rewrite H0; reflexivity.
    + unfold fby; case_eq (xs (S n)).
      contradiction. intros v1 xsn; apply hold_rel2; exact HR.
Qed.

Lemma fby_rel: forall v0 xs n v, fby v0 xs n = v <-> fbyR v0 xs n v.
Proof.
  split.
  intro H; rewrite <- H; apply fby_rel1.
  apply fby_rel2.
Qed.

