From Velus Require Import Common.
From Velus Require Import Operators.

From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import Arith.EqNat.
From Coq Require Import Omega.
From Coq Require Import List.
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

  (** An indexed stream of lists is well-formed when the length of the lists
      is uniform over time. *)
  Definition wf_streams {A} (xss: stream (list A)) :=
    forall k' k, length (xss k) = length (xss k').

  Definition eq_str {A} (xs xs': stream A) := forall n, xs n = xs' n.
  Infix "≈" := eq_str (at level 70, no associativity).

  Lemma eq_str_refl:
    forall {A} (xs: stream A),
      xs ≈ xs.
  Proof.
    intros * n; reflexivity.
  Qed.

  Lemma eq_str_sym:
    forall {A} (xs xs': stream A),
      xs ≈ xs' -> xs' ≈ xs.
  Proof.
    intros * E n; auto.
  Qed.

  Lemma eq_str_trans:
    forall {A} (xs ys zs: stream A),
      xs ≈ ys -> ys ≈ zs -> xs ≈ zs.
  Proof.
    intros * E1 E2 n; auto.
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

  (** Count the number of resets ticks seen at [n] so far. *)
  Fixpoint count (rs: cstream) (n: nat) : nat :=
    let c := match n with 0 => 0 | S n => count rs n end in
    if rs n then S c else c.

  (** [mask o k rs xs] is the stream which clips the stream [xs] between
      the [k]th and the [(k+1)]th reset, outputting [o] everywhere else. *)
  Definition mask {A} (opaque: A) (k: nat) (rs: cstream) (xs: stream A) : stream A :=
    fun n => if beq_nat k (count rs n) then xs n else opaque.

  (** ** Properties *)

  Lemma count_le:
    forall r n,
      count r n <= count r (S n).
  Proof.
    intros; simpl.
    destruct (r (S n)); omega.
  Qed.

  Lemma count_le':
    forall r n' n,
      n' < n ->
      count r n' <= count r n.
  Proof.
    induction 1.
    - apply count_le.
    - simpl; destruct (r (S m)); omega.
  Qed.

  Lemma count_true_ge_1:
    forall n r,
      r n = true ->
      1 <= count r n.
  Proof.
    induction n; simpl; intros * E; rewrite E; auto.
    apply Le.le_n_S; omega.
  Qed.

  Lemma count_positive:
    forall r n' n,
      r n = true ->
      n' < n ->
      count r n' < count r n.
  Proof.
    intros * Rn Lt.
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
    intros * E.
    unfold mask.
    assert (EqNat.beq_nat k (count r n) = false) as ->
        by (apply EqNat.beq_nat_false_iff; omega); auto.
  Qed.

  Lemma mask_transparent:
    forall {A} (xs: stream A) k r (opaque: A) n,
      count r n = k ->
      (mask opaque k r xs) n = xs n.
  Proof.
    intros * E.
    unfold mask.
    assert (EqNat.beq_nat k (count r n) = true) as ->
        by (apply EqNat.beq_nat_true_iff; omega); auto.
  Qed.

  (* [memory_masked k rs] applies iff [n = k = 0] or [k = count rs (n - 1)]. *)
  Lemma memory_masked_alt_cond:
    forall rs k n,
      count rs n = (if rs n then S k else k)
      <->
      k = (match n with 0 => 0 | S m => count rs m end).
  Proof.
    induction n; simpl.
    - destruct (rs 0); intuition.
    - destruct (rs (S n)); [|now intuition].
      split; inversion 1; subst; auto.
  Qed.

  Lemma count_reset_now:
    forall rs i,
      rs i = true ->
      count rs i = S (match i with 0 => 0 | S m => count rs m end).
  Proof.
    destruct i; intro Hr; simpl; now rewrite Hr.
  Qed.

  Lemma count_reset_gt:
    forall rs i n,
      rs i = true ->
      n < i ->
      count rs n < count rs i.
  Proof.
    intros * Hrs Hn.
    rewrite count_reset_now with (1:=Hrs).
    destruct i; [now inv Hn|].
    inv Hn; auto.
    take (S n <= i) and rewrite PeanoNat.Nat.le_succ_l in it.
    now apply Lt.le_lt_n_Sm, count_le'.
  Qed.

  Add Parametric Morphism : count
      with signature eq_str ==> eq ==> eq
        as count_eq_str.
  Proof.
    intros * E n.
    induction n; simpl; rewrite E; auto.
    now rewrite IHn.
  Qed.

  Add Parametric Morphism (A: Type) : (@mask A)
      with signature eq ==> eq ==> eq_str ==> eq_str ==> eq_str
        as mask_eq_str.
  Proof.
    intros * E1 ? ? E2 n; unfold mask.
    now rewrite E1, E2.
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

  Definition absent_list (xs: list value): Prop :=
    Forall (fun v => v = absent) xs.

  Definition present_list (xs: list value): Prop :=
    Forall (fun v => v <> absent) xs.

  Definition all_absent {A} (l: list A) : list value :=
    map (fun _ => absent) l.

  Remark all_absent_spec:
    forall A (l: list A),
      absent_list (all_absent l).
  Proof.
    induction l; simpl; constructor; auto.
  Qed.

  Remark nth_all_absent:
    forall (xs: list value) n,
      nth n (all_absent xs) absent = absent.
  Proof.
    induction xs, n; simpl; auto.
  Qed.

  Lemma absent_list_spec:
    forall A xs (ys: list A),
      length xs = length ys ->
      absent_list xs ->
      xs = all_absent ys.
  Proof.
    induction xs, ys; simpl; inversion 1; auto.
    inversion_clear 1; subst; f_equal; auto.
  Qed.

  Lemma absent_list_spec':
    forall A xs (ys: list A),
      xs = all_absent ys ->
      absent_list xs.
  Proof.
    induction xs, ys; simpl; inversion 1; constructor; auto.
    match goal with H: _ = all_absent _ |- _ => rewrite <-H end.
    eapply IHxs; eauto.
  Qed.

  Lemma absent_list_spec_b:
    forall xs,
      absent_list xs <-> forallb (fun x => x ==b absent) xs = true.
  Proof.
    induction xs; simpl; split; auto.
    - constructor.
    - inversion_clear 1; subst; apply andb_true_intro; intuition.
    - intro H; apply andb_prop in H as (E & Hforall).
      rewrite equiv_decb_equiv in E; constructor; auto.
      apply IHxs; auto.
  Qed.

  Lemma all_absent_map:
    forall A B (l: list A) (f: A -> B),
      all_absent (map f l) = all_absent l.
  Proof.
    unfold all_absent; induction l; intros; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma present_list_spec:
    forall xs,
      present_list xs <-> exists (vs: list val), xs = map present vs.
  Proof.
    induction xs as [| x xs IHxs].
    - split; intro H.
      + exists []; eauto.
      + constructor.
    - split; intro H.
      + inversion H as [| ? ? Hx Hxs]; subst.
        apply not_absent_present in Hx as [v Hv].
        apply IHxs in Hxs as [vs Hvs].
        exists (v :: vs). simpl.
        congruence.
      + destruct H as [vs Hvs].
        destruct vs; simpl; try discriminate.
        apply Forall_cons.
        * intro. subst x; discriminate.
        * eapply IHxs.
          exists vs. now inv Hvs.
  Qed.

  Lemma present_list_spec_b:
    forall xs,
      present_list xs <-> forallb (fun x => x <>b absent) xs = true.
  Proof.
    induction xs; simpl; split; auto.
    - constructor.
    - inversion_clear 1 as [|?? NE]; apply andb_true_intro; intuition.
      apply Bool.negb_true_iff; rewrite not_equiv_decb_equiv; auto.
    - intro H; apply andb_prop in H as (E & Hforall).
      apply Bool.negb_true_iff in E; rewrite not_equiv_decb_equiv in E.
      constructor; auto.
      apply IHxs; auto.
  Qed.

  Lemma mask_length:
    forall k k' xss r n,
      wf_streams xss ->
      length (mask (all_absent (xss k')) k r xss n) = length (xss n).
  Proof.
    intros; unfold mask.
    destruct (EqNat.beq_nat k (count r n)); auto.
    unfold all_absent; rewrite map_length.
    induction k'; induction n; auto.
  Qed.

  (** If all masks ar well-formed then the underlying stream of lists
      is well-formed. *)
  Lemma wf_streams_mask:
    forall xss r m,
      (forall n, wf_streams (mask (all_absent (xss m)) n r xss)) ->
      wf_streams xss.
  Proof.
    unfold wf_streams, mask; intros * WF k k'.
    pose proof (WF (count r k) k' k) as WFk;
      pose proof (WF (count r k') k' k) as WFk'.
    rewrite <-EqNat.beq_nat_refl in WFk, WFk'.
    rewrite Nat.eqb_sym in WFk'.
    destruct (EqNat.beq_nat (count r k) (count r k')); auto.
    now rewrite WFk, <-WFk'.
  Qed.

 (** ** Presence and absence in non-empty lists *)

  Lemma not_absent_present_list:
    forall xs,
      0 < length xs ->
      present_list xs ->
      ~ absent_list xs.
  Proof.
    intros * Hnz Hpres Habs.
    unfold present_list in Hpres.
    unfold absent_list in Habs.
    destruct xs; [now inversion Hnz|].
    now inv Hpres; inv Habs; auto.
  Qed.


  Lemma all_absent_mask:
    forall xs k k' r n,
      wf_streams xs ->
      all_absent (mask (all_absent (xs k')) k r xs n) = all_absent (xs n).
  Proof.
    intros * Wf; unfold mask.
    destruct (EqNat.beq_nat k (count r n)); auto.
    specialize (Wf n k').
    assert (length (all_absent (xs k')) = length (xs n)) as Length
        by now (unfold all_absent; rewrite map_length).
    clear Wf; revert Length; generalize (xs n) as l, (all_absent (xs k')) as l'.
    induction l, l'; inversion 1; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma absent_list_mask:
    forall xs opaque k r n,
      absent_list (xs n) ->
      absent_list opaque ->
      absent_list (mask opaque k r xs n).
  Proof.
    intros * Abs. unfold mask.
    destruct (EqNat.beq_nat k (count r n)); auto.
  Qed.

  Definition vstr (xss: stream (list const)): stream (list value) :=
    fun n => map (fun c => present (sem_const c)) (xss n).

End STREAM.

Module StreamFun
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op) <: STREAM Op OpAux.
  Include STREAM Op OpAux.
End StreamFun.
