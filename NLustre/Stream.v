Require Import Velus.Common.
Require Import Velus.Operators.

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

  (* (** A synchronous [value] is either an absence or a present constant *) *)

  (* Inductive value := *)
  (* | absent *)
  (* | present (c : val). *)
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
  (* Fixpoint hold (r: stream bool) (v0: val) (xs: stream value) (n: nat) : val := *)
  (*   match n with *)
  (*   | 0 => v0 *)
  (*   | S m => *)
  (*       match xs m with *)
  (*       | absent => *)
  (*         if r m then v0 else hold r v0 xs m *)
  (*       | present hv => hv *)
  (*       end *)
  (*   end. *)

  (* Definition fby (r: stream bool) (v0: val) (xs: stream value) : stream value := *)
  (*   fun n => *)
  (*     match xs n with *)
  (*     | absent => absent *)
  (*     | _ => present (if r n then v0 else hold r v0 xs n) *)
  (*     end. *)

  (* Definition mfby (r: stream bool) (xs: stream value) (ms: stream val) (ys: stream value) : Prop := *)
  (*   forall n, *)
  (*     match xs n with *)
  (*     | absent => *)
  (*       ms (S n) = (if r n then ms 0 else ms n) *)
  (*       /\ ys n = absent *)
  (*     | present v => *)
  (*       ms (S n) = v *)
  (*       /\ ys n = present (if r n then ms 0 else ms n) *)
  (*     end. *)
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

  Require Import Coq.Arith.EqNat.
  Require Import List.
  Import List.ListNotations.
  Open Scope list_scope.

  (* Fixpoint take {A} (n: nat) (s: stream A) : list A := *)
  (*   match n with *)
  (*   | O => nil *)
  (*   | S m => take m s ++ [s m] *)
  (*   end. *)

  Fixpoint count (rs: cstream) (n: nat) : nat :=
    match n, rs n with
    | 0, false => 0
    | 0, true => 1
    | S m, false => count rs m
    | S m, true => 1 + count rs m
    end.

  Definition mask {A} (opaque: A) (k: nat) (rs: cstream) (xs: stream A) : stream A :=
    fun n =>
      if beq_nat k (count rs n) then xs n else opaque.

  Corollary count_true_ge_1:
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

  (* Definition  *)
  (* Definition mask_vs := @mask (list value) []. *)
  Definition mask_v := mask absent.
  Definition mask_b := mask false.

  (* Corollary mask_vs_compat: *)
  (*   forall r r' k xs, *)
  (*     (forall n, r n = r' n) -> *)
  (*     forall n, mask_vs k r xs n = mask_vs k r' xs n. *)
  (* Proof. *)
  (*   unfold mask_vs; intros; apply mask_compat; auto. *)
  (* Qed. *)

  (* Definition r := *)
  (*   fun n => *)
  (*     match n with *)
  (*     | 0 => false *)
  (*     | 1 => false *)
  (*     | 2 => false *)
  (*     | 3 => true *)
  (*     | 4 => false *)
  (*     | 5 => false *)
  (*     | 6 => false *)
  (*     | 7 => false *)
  (*     | 8 => false *)
  (*     | 9 => true *)
  (*     | 10 => false *)
  (*     | 11 => false *)
  (*     | 12 => false *)
  (*     | 13 => true *)
  (*     | n => false *)
  (*     end. *)

  (* Notation "⊥" := (absent) (at level 50). *)
  (* Notation "⇑" := (present true_val). *)
  (* Notation "⇓" := (present false_val). *)
  (* Notation "↑" := (true). *)
  (* Notation "↓" := (false). *)

  (* Fixpoint x n := *)
  (*   match n with *)
  (*   | 0 => ⇓ *)
  (*   | 1 => ⇑ *)
  (*   | S (S n) => x n *)
  (*   end. *)

  (* Compute (take 16 r, take 16 x, take 16 (count r), *)
  (*          take 16 (mask_v 0 r x), *)
  (*          take 16 (mask_v 1 r x), *)
  (*          take 16 (mask_v 2 r x), *)
  (*          take 16 (mask_v 3 r x), *)
  (*          take 16 (mask_v 4 r x) *)
  (*         ). *)

  (* Remark mask_const_opaque: *)
  (*   forall {A} n rs (opaque: A), *)
  (*     mask opaque n rs (Streams.const opaque) ≡ Streams.const opaque. *)
  (* Proof. *)
  (*   cofix Cofix; intros. *)
  (*   unfold_Stv rs; rewrite (unfold_Stream (Streams.const opaque)); *)
  (*     constructor; destruct n as [|[]]; simpl; auto; try apply Cofix. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* CoFixpoint flatten_masks (bs: Stream bool) (xss: Stream (Stream value)) : Stream value := *)
  (*   let xss := if hd bs then tl xss else xss in *)
  (*   hd (hd xss) ::: flatten_masks (tl bs) (map (@tl value) xss). *)

  (* CoFixpoint masks_from (n: nat) (rs: Stream bool) (xs: Stream value) : Stream (Stream value) := *)
  (*   mask_v n rs xs ::: masks_from (n + 1) rs xs. *)

  (* Definition masks := masks_from 0. *)

  (* Eval simpl in take 16 (flatten_masks r (masks r x)). *)

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

Module StreamFun
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op) <: STREAM Op OpAux.
  Include STREAM Op OpAux.
End StreamFun.
