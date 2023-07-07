From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Clocks.

From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import Arith.EqNat.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Logic.FunctionalExtensionality.

(** * Extensional model of synchronous streams *)

(** Our model is extensional in the sense that it encodes a
coinductive, infinite datastructure (streams) with a function of
domain [nat]. To reason about this object, we shall use functional
extensionality [ Logic.FunctionalExtensionality]. This axiom is
believed to be consistent with Coq. *)

Module Type INDEXEDSTREAMS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Clocks : CLOCKS Ids Op OpAux).

  (** ** Datatypes *)

  (** A stream is represented by its characteristic function: *)

  Definition stream A := nat -> A.

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

  Notation vstream := (stream svalue).
  Implicit Type vs : vstream.

  (** A clock is a stream that returns [true] if the clocked stream
contains a value ([present c]) at the corresponding instant, [false]
if the clocked stream is [absent] at the corresponding instant. *)

  Notation cstream := (stream bool).
  Implicit Type cs : cstream.

  (** ** Synchronous functions *)

  Lemma present_injection:
    forall (x y : svalue), x = y <-> present x = present y.
  Proof.
    split; intro H; [rewrite H|injection H]; auto.
  Qed.

  Lemma not_absent_present:
    forall (x : svalue), x <> absent <-> exists c, x = present c.
  Proof.
    intros x.
    split; intro HH.
    destruct x; [intuition|eauto].
    destruct HH as [c HH]; rewrite HH.
    intro; discriminate.
  Qed.

  Definition absent_list (xs: list svalue): Prop :=
    Forall (fun v => v = absent) xs.

  Definition present_list (xs: list svalue): Prop :=
    Forall (fun v => v <> absent) xs.

  Definition all_absent {A} (l: list A) : list svalue :=
    map (fun _ => absent) l.

  Remark all_absent_spec:
    forall A (l: list A),
      absent_list (all_absent l).
  Proof.
    induction l; simpl; constructor; auto.
  Qed.

  Remark nth_all_absent:
    forall (xs: list svalue) n,
      nth n (all_absent xs) absent = absent.
  Proof.
    induction xs, n; simpl; auto.
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

  (** Count the number of resets ticks seen at [n] so far. *)
  Fixpoint count (rs: cstream) (n: nat) : nat :=
    let c := match n with 0 => 0 | S n => count rs n end in
    if rs n then S c else c.

  (** [mask k rs xss] is the list of streams which clips the list of streams
      [xss] between the [k]th and the [(k+1)]th reset, outputting absent
      everywhere else. *)
  Definition mask (k: nat) (rs: cstream) (xss: stream (list svalue))
    : stream (list svalue) :=
    fun n => if k =? (count rs n) then xss n else all_absent (xss 0).

  (** ** Properties *)

  Lemma count_le:
    forall r n,
      count r n <= count r (S n).
  Proof.
    intros; simpl.
    destruct (r (S n)); lia.
  Qed.

  Lemma count_le':
    forall r n' n,
      n' < n ->
      count r n' <= count r n.
  Proof.
    induction 1.
    - apply count_le.
    - simpl; destruct (r (S m)); lia.
  Qed.

  Lemma count_true_ge_1:
    forall n r,
      r n = true ->
      1 <= count r n.
  Proof.
    induction n; simpl; intros * E; rewrite E; auto.
    lia.
  Qed.

  Lemma count_positive:
    forall r n' n,
      r n = true ->
      n' < n ->
      count r n' < count r n.
  Proof.
    intros * Rn Lt.
    destruct n; try lia.
    simpl; rewrite Rn.
    clear Rn.
    rewrite Nat.lt_succ_r, Nat.lt_eq_cases in Lt. destruct Lt as [Lt|Lt].
    - induction n; try lia.
      rewrite Nat.lt_succ_r, Nat.lt_eq_cases in Lt. destruct Lt as [Lt|Lt].
      + eapply Nat.lt_le_trans; eauto.
        rewrite <-Nat.succ_le_mono. apply count_le.
      + subst.
        apply Nat.lt_succ_r, count_le.
    - subst; lia.
  Qed.

  Lemma mask_opaque:
    forall xss k r n,
      count r n <> k ->
      mask k r xss n = all_absent (xss 0).
  Proof.
    intros * E.
    unfold mask.
    assert ((k =? count r n) = false) as ->
        by (apply Nat.eqb_neq; lia); auto.
  Qed.

  Lemma mask_transparent:
    forall xss k r n,
      count r n = k ->
      mask k r xss n = xss n.
  Proof.
    intros * E.
    unfold mask.
    assert ((k =? count r n) = true) as ->
        by (apply Nat.eqb_eq; lia); auto.
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
    take (S n <= i) and rewrite Nat.le_succ_l in it.
    now apply Nat.lt_succ_r, count_le'.
  Qed.

  Add Parametric Morphism : count
      with signature eq_str ==> eq ==> eq
        as count_eq_str.
  Proof.
    intros * E n.
    induction n; simpl; rewrite E; auto.
    now rewrite IHn.
  Qed.

  Add Parametric Morphism k : (mask k)
      with signature eq_str ==> eq_str ==> eq_str
        as mask_eq_str.
  Proof.
    intros * E1 ? ? E2 n; unfold mask.
    now rewrite E1, 2 E2.
  Qed.

  Lemma mask_length:
    forall k xss r n,
      wf_streams xss ->
      length (mask k r xss n) = length (xss n).
  Proof.
    intros; unfold mask.
    destruct (k =? count r n); auto.
    unfold all_absent; rewrite map_length.
    induction n; auto.
  Qed.

  (** If all masks ar well-formed then the underlying stream of lists
      is well-formed. *)
  Lemma wf_streams_mask:
    forall xss r,
      (forall n, wf_streams (mask n r xss)) ->
      wf_streams xss.
  Proof.
    unfold wf_streams, mask; intros * WF k k'.
    pose proof (WF (count r k) k' k) as WFk;
      pose proof (WF (count r k') k' k) as WFk'.
    rewrite Nat.eqb_refl in WFk, WFk'.
    rewrite Nat.eqb_sym in WFk'.
    destruct (count r k =? count r k'); auto.
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

  Lemma absent_list_mask:
    forall xss k r n,
      absent_list (xss n) ->
      absent_list (mask k r xss n).
  Proof.
    intros; unfold mask.
    destruct (k =? count r n); auto using all_absent_spec.
  Qed.

  (** Restrictions of FEnvironments *)
  Section HistoryRestriction.

    Definition env {A} := @FEnv.t A svalue.
    Definition history' {A} := @FEnv.t A (stream svalue).

    Definition restr_hist {A} (H : @history' A) (n: nat): env :=
      FEnv.map (fun xs => xs n) H.

    Hint Unfold restr_hist : fenv.

    Lemma FEnv_find_restr_hist {A}:
      forall (H: @history' A) x i,
        (restr_hist H i) x = option_map (fun xs => xs i) (H x).
    Proof.
      unfold restr_hist. reflexivity.
    Qed.

    Lemma FEnv_add_restr_hist {A} `{FEnv.fenv_key A}:
      forall (H: @history' A) x s i,
        FEnv.Equiv eq (restr_hist (FEnv.add x s H) i) (FEnv.add x (s i) (restr_hist H i)).
    Proof.
      intros Hi x s i x'. simpl_fenv. destruct H.
      destruct (fenv_key_eqdec x' x). inv e.
      - subst. now setoid_rewrite FEnv.gss.
      - now setoid_rewrite FEnv.gso.
    Qed.

    Lemma FEnv_In_restr_hist {A} `{FEnv.fenv_key A}:
      forall (H: @history' A) x i,
        FEnv.In x H <-> FEnv.In x (restr_hist H i).
    Proof.
      intros. unfold restr_hist.
      now rewrite FEnv.map_in_iff.
    Qed.

    Lemma FEnv_dom_restr_hist {A} `{FEnv.fenv_key A}:
      forall (H: @history' A) xs i,
        FEnv.dom H xs <-> FEnv.dom (restr_hist H i) xs.
    Proof.
      split; intros HH x; specialize (HH x);
        now rewrite <-HH, FEnv_In_restr_hist.
    Qed.

  End HistoryRestriction.

  (** ** Instantaneous semantics *)

  Section InstantSemantics.

    (**

An history maps variables to streams of values (the variables'
histories). Taking a snapshot of the history at a given time yields an
environment.

     *)

    Definition history {A} := stream (@env A).

    Definition sem_var_instant {A} (R: @env A) x (v: svalue) : Prop :=
      R x = Some v.

    Variable base: bool.
    Variable R: @env ident.

    Inductive sem_clock_instant: clock -> bool -> Prop :=
    | Sbase:
        sem_clock_instant Cbase base
    | Son:
        forall ck x t b,
          sem_clock_instant ck true ->
          sem_var_instant R x (present (Venum b)) ->
          sem_clock_instant (Con ck x (t, b)) true
    | Son_abs1:
        forall ck x c,
          sem_clock_instant ck false ->
          sem_var_instant R x absent ->
          sem_clock_instant (Con ck x c) false
    | Son_abs2:
        forall ck x t b b',
          sem_clock_instant ck true ->
          sem_var_instant R x (present (Venum b')) ->
          b <> b' ->
          sem_clock_instant (Con ck x (t, b)) false.

  End InstantSemantics.

  Global Hint Constructors sem_clock_instant : indexedstreams.

  Add Parametric Morphism {A} : (@sem_var_instant A)
      with signature FEnv.Equiv eq ==> @eq _ ==> @eq _ ==> Basics.impl
        as sem_var_instant_morph.
  Proof.
    intros H H' EH x v Hvar.
    specialize (EH x). rewrite Hvar in EH. inv EH.
    symmetry in H1. eapply H1.
  Qed.

  Add Parametric Morphism : sem_clock_instant
      with signature eq ==> FEnv.Equiv eq ==> eq ==> eq ==> Basics.impl
        as sem_clock_instant_morph.
  Proof.
    intros b H H' EH ck. revert b.
    induction ck; intros b b' Sem; inv Sem.
    - constructor; auto.
    - apply Son; auto. apply IHck; auto.
      rewrite <-EH; auto.
    - apply Son_abs1; auto. apply IHck; auto.
      rewrite <-EH; auto.
    - eapply Son_abs2; eauto. apply IHck; auto.
      rewrite <-EH; auto.
  Qed.

  Fact sem_clock_instant_true_inv : forall b H ck,
      sem_clock_instant b H ck true ->
      b = true.
  Proof.
    intros * Hsem.
    induction ck; inv Hsem; auto.
  Qed.

  Section LiftSemantics.

    Variable bk : stream bool.

    Definition lift {K A B} (H: @history K) (sem: bool -> env -> A -> B -> Prop)
               x (ys: stream B): Prop :=
      forall n, sem (bk n) (H n) x (ys n).

    Definition lift' {K A B} (H: @history K) (sem: env -> A -> B -> Prop) x (ys: stream B): Prop :=
      forall n, sem (H n) x (ys n).

    Definition sem_var {K} (H: @history K) x (xs: stream svalue): Prop :=
      lift' H sem_var_instant x xs.

    Definition sem_clock H (ck: clock) (xs: stream bool): Prop :=
      lift H sem_clock_instant ck xs.

  End LiftSemantics.

  Global Hint Unfold lift lift' : indexedstreams.

  (** ** Determinism of the semantics *)

  (** *** Instantaneous semantics *)

  Section InstantDeterminism.

    Variable base: bool.

    Lemma sem_var_instant_det {K} (R: @env K):
      forall x v1 v2,
        sem_var_instant R x v1
        -> sem_var_instant R x v2
        -> v1 = v2.
    Proof.
      congruence.
    Qed.

    Lemma sem_clock_instant_det R:
      forall ck v1 v2,
        sem_clock_instant base R ck v1
        -> sem_clock_instant base R ck v2
        -> v1 = v2.
    Proof.
      induction ck; repeat inversion 1; subst; intuition;
        try repeat progress match goal with
                            | H1: sem_clock_instant ?bk ?R ?ck ?l,
                                  H2: sem_clock_instant ?bk ?R ?ck ?r |- _ =>
                              apply IHck with (1:=H1) in H2; discriminate
                            | H1: sem_var_instant ?R ?i (present ?l),
                                  H2: sem_var_instant ?R ?i (present ?r) |- _ =>
                              apply sem_var_instant_det with (1:=H1) in H2;
                                injection H2; intro; subst
                            end.
      1,2:exfalso; auto.
    Qed.

  End InstantDeterminism.

  Section LiftDeterminism.

    Variable bk : stream bool.

    Lemma lift_det:
      forall {K A B} (H: @history K) (P: bool -> env -> A -> B -> Prop) (bk: stream bool)
        x (xs1 xs2 : stream B),
        (forall b R v1 v2, P b R x v1 -> P b R x v2 -> v1 = v2) ->
        lift bk H P x xs1 -> lift bk H P x xs2 -> xs1 = xs2.
    Proof.
      intros * Hpoint H1 H2.
      extensionality n. specialize (H1 n). specialize (H2 n).
      eapply Hpoint; eassumption.
    Qed.

    Lemma lift'_det:
      forall {K A B} (H: @history K) (P: env -> A -> B -> Prop)
        x (xs1 xs2 : stream B),
        (forall R v1 v2, P R x v1 -> P R x v2 -> v1 = v2) ->
        lift' H P x xs1 -> lift' H P x xs2 -> xs1 = xs2.
    Proof.
      intros * Hpoint H1 H2.
      extensionality n. specialize (H1 n). specialize (H2 n).
      eapply Hpoint; eassumption.
    Qed.

    Ltac apply_lift sem_det :=
      intros; eapply lift_det; try eassumption;
      compute; intros; eapply sem_det; eauto.

    Ltac apply_lift' sem_det :=
      intros; eapply lift'_det; try eassumption;
      compute; intros; eapply sem_det; eauto.

    Lemma sem_var_det {K} (H: @history K):
      forall x xs1 xs2,
        sem_var H x xs1 -> sem_var H x xs2 -> xs1 = xs2.
    Proof.
      apply_lift' (@sem_var_instant_det K).
    Qed.

    Lemma sem_clock_det H:
      forall ck bs1 bs2,
        sem_clock bk H ck bs1 -> sem_clock bk H ck bs2 -> bs1 = bs2.
    Proof.
      apply_lift sem_clock_instant_det.
    Qed.

  End LiftDeterminism.

  Ltac sem_det :=
    match goal with
    | H1: sem_clock_instant ?bk ?H ?C ?X,
          H2: sem_clock_instant ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_clock_instant_det; eexact H1 || eexact H2
    | H1: sem_clock ?bk ?H ?C ?X,
          H2: sem_clock ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_clock_det; eexact H1 || eexact H2
    | H1: sem_var_instant ?H ?C ?X,
          H2: sem_var_instant ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_var_instant_det; eexact H1 || eexact H2
    | H1: sem_var ?H ?C ?X,
          H2: sem_var ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_var_det; eexact H1 || eexact H2
    end.

  Ltac by_sem_det :=
    repeat match goal with
           | H: exists _, _ |- _ => destruct H
           end;
    match goal with
    | H1: sem_clock_instant ?bk ?H ?C ?X,
          H2: sem_clock_instant ?bk ?H ?C ?Y |- _ =>
      assert (X = Y) by (eapply sem_clock_instant_det; eexact H1 || eexact H2)
    | H1: sem_var_instant ?H ?C ?X,
          H2: sem_var_instant ?H ?C ?Y |- _ =>
      assert (X = Y) by (eapply sem_var_instant_det; eexact H1 || eexact H2)
    end; discriminate.

  (** ** Interpreter *)

  Section InstantInterpreter.

    Variable base : bool.

    Definition interp_var_instant {K} (R: @env K) x: svalue :=
      match R x with
      | Some v => v
      | None => absent
      end.

    Lemma interp_var_instant_complete {K} (R: @env K):
      forall x v,
        sem_var_instant R x v ->
        v = interp_var_instant R x.
    Proof.
      unfold interp_var_instant; now intros * ->.
    Qed.

    Fixpoint interp_clock_instant R (c: clock): bool :=
      match c with
      | Cbase =>
        base
      | Con c x (t, b) =>
        let cb := interp_clock_instant R c in
        andb cb (interp_var_instant R x ==b present (Venum b))
      end.

    Ltac rw_exp_helper :=
      repeat match goal with
             | _: sem_var_instant ?R ?x ?v |- context[interp_var_instant ?R ?x] =>
               erewrite <-(interp_var_instant_complete R x v); eauto; simpl
             | H: sem_unop ?op ?c ?t = _ |- context[sem_unop ?op ?c ?t] =>
               rewrite H
             | H: sem_binop ?op ?c1 ?t1 ?c2 ?t2 = _ |- context[sem_binop ?op ?c1 ?t1 ?c2 ?t2] =>
               rewrite H
          end.

    Lemma interp_clock_instant_complete R:
      forall c b,
        sem_clock_instant base R c b ->
        b = interp_clock_instant R c.
    Proof.
      induction 1; auto; simpl; rw_exp_helper;
        rewrite <-IHsem_clock_instant; simpl; auto.
      - symmetry. apply equiv_decb_refl.
      - destruct c; auto.
      - symmetry. rewrite <-Bool.not_true_iff_false, svalue_eqb_eq.
        intro contra; inv contra; auto.
    Qed.

  End InstantInterpreter.

  (** ** Liftings of instantaneous semantics *)

  Section LiftInterpreter.

    Variable bk : stream bool.

    Definition lift_interp {K A B} (H: @history K) (interp: bool -> env -> A -> B) x: stream B :=
      fun n => interp (bk n) (H n) x.

    Definition lift_interp' {K A B} (H: @history K) (interp: env -> A -> B) x: stream B :=
      fun n => interp (H n) x.

    Definition interp_clock H (ck: clock): stream bool :=
      lift_interp H interp_clock_instant ck.

    Definition interp_var {K} (H: @history K) x: stream svalue :=
      lift_interp' H interp_var_instant x.

    Lemma lift_complete {K} (H: @history K):
      forall {A B} (sem: bool -> env -> A -> B -> Prop) interp x xs,
        (forall b R x v, sem b R x v -> v = interp b R x) ->
        lift bk H sem x xs ->
        xs ≈ lift_interp H interp x.
    Proof.
      intros * Instant Sem n.
      specialize (Sem n); unfold lift_interp; auto.
    Qed.

    Lemma lift'_complete {K} (H: @history K):
      forall {A B} (sem: env -> A -> B -> Prop) interp x xs,
        (forall R x v, sem R x v -> v = interp R x) ->
        lift' H sem x xs ->
        xs ≈ lift_interp' H interp x.
    Proof.
      intros * Instant Sem n.
      specialize (Sem n); unfold lift_interp'; auto.
    Qed.

    Corollary interp_clock_complete H:
      forall ck bs,
        sem_clock bk H ck bs ->
        bs ≈ interp_clock H ck.
    Proof.
      intros; eapply lift_complete; eauto;
        apply interp_clock_instant_complete.
    Qed.

    Corollary interp_var_complete {K} (H: @history K):
      forall x vs,
        sem_var H x vs ->
        vs ≈ interp_var H x.
    Proof.
      intros; eapply lift'_complete; eauto;
        apply interp_var_instant_complete.
    Qed.

  End LiftInterpreter.

End INDEXEDSTREAMS.

Module IndexedStreamsFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Clocks : CLOCKS Ids Op OpAux)
<: INDEXEDSTREAMS Ids Op OpAux Clocks.
  Include INDEXEDSTREAMS Ids Op OpAux Clocks.
End IndexedStreamsFun.
