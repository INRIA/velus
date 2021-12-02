From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Environment.
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
  Qed.

  Lemma present_list_spec:
    forall xs,
      present_list xs <-> exists (vs: list value), xs = map present vs.
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
    apply Le.le_n_S; lia.
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
    apply Lt.lt_n_Sm_le, Lt.le_lt_or_eq in Lt; destruct Lt.
    - induction n; try lia.
      apply Lt.lt_n_Sm_le, Lt.le_lt_or_eq in H; destruct H.
      + eapply Lt.lt_le_trans; eauto.
        apply Le.le_n_S, count_le.
      + subst.
        apply Lt.le_lt_n_Sm, count_le.
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
        by (apply EqNat.beq_nat_false_iff; lia); auto.
  Qed.

  Lemma mask_transparent:
    forall xss k r n,
      count r n = k ->
      mask k r xss n = xss n.
  Proof.
    intros * E.
    unfold mask.
    assert ((k =? count r n) = true) as ->
        by (apply EqNat.beq_nat_true_iff; lia); auto.
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
    rewrite <-EqNat.beq_nat_refl in WFk, WFk'.
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


  Lemma all_absent_mask:
    forall xss k r n,
      wf_streams xss ->
      all_absent (mask k r xss n) = all_absent (xss n).
  Proof.
    intros * Wf; unfold mask.
    destruct (k =? count r n); auto.
    specialize (Wf n).
    assert (length (all_absent (xss 0)) = length (xss n)) as Length
        by now (unfold all_absent; rewrite map_length).
    clear Wf; revert Length; generalize (xss n) as l, (all_absent (xss 0)) as l'.
    induction l, l'; inversion 1; simpl; auto.
  Qed.

  Lemma absent_list_mask:
    forall xss k r n,
      absent_list (xss n) ->
      absent_list (mask k r xss n).
  Proof.
    intros; unfold mask.
    destruct (k =? count r n); auto using all_absent_spec.
  Qed.

  Definition vstr (xss: stream (list cconst)): stream (list svalue) :=
    fun n => map (fun c => present (Vscalar (sem_cconst c))) (xss n).

  (** Restrictions of Environments *)
  Section HistoryRestriction.

    Definition env := Env.t svalue.
    Definition history' := Env.t (stream svalue).

    Definition restr_hist (H : history') (n: nat): env :=
      Env.map (fun xs => xs n) H.

    Lemma Env_find_restr_hist:
      forall H x i,
        Env.find x (restr_hist H i) = option_map (fun xs => xs i) (Env.find x H).
    Proof.
      unfold restr_hist. now setoid_rewrite Env.Props.P.F.map_o.
    Qed.

    Lemma Env_add_restr_hist:
      forall H x s i,
        Env.Equal (restr_hist (Env.add x s H) i) (Env.add x (s i) (restr_hist H i)).
    Proof.
      intros H x s i x'. unfold restr_hist.
      setoid_rewrite Env.Props.P.F.map_o.
      destruct (ident_eq_dec x' x).
      - subst. now setoid_rewrite Env.gss.
      - now setoid_rewrite Env.gso; auto; rewrite <-Env.Props.P.F.map_o.
    Qed.

    Lemma Env_In_restr_hist:
      forall H x i,
        Env.In x H <-> Env.In x (restr_hist H i).
    Proof.
      intros. unfold restr_hist.
      now rewrite Env.Props.P.F.map_in_iff.
    Qed.

    Lemma Env_dom_restr_hist:
      forall H xs i,
        Env.dom H xs <-> Env.dom (restr_hist H i) xs.
    Proof.
      split; intros HH; apply Env.dom_intro; intro x;
        apply Env.dom_use with (x0:=x) in HH;
        now rewrite <-HH, Env_In_restr_hist.
    Qed.

    Lemma stream_env_to_env_stream:
      forall xs (H : stream (Env.t svalue)),
        (forall i, Env.dom (H i) xs) ->
        (exists (H' : Env.t (stream svalue)),
            (forall i, Env.Equal (H i) (restr_hist H' i))
            /\ (forall x, In x xs -> Env.find x H' = Some (fun i => match Env.find x (H i) with
                                                            Some v => v | None => absent end))).
    Proof.
      setoid_rewrite <-(nub_same_elements ident_eq_dec).
      intros ys.
      pose proof (NoDup_nub ident_eq_dec ys) as NDN; revert NDN.
      induction (nub ident_eq_dec ys) as [|x xs IH]; clear ys;
        intros ND H DH.
      - (* environment is empty *)
        exists (Env.empty _). split; [|now inversion 1].
        intros i y. specialize (DH i).
        apply Env.dom_use with (x:=y) in DH.
        unfold Env.from_list. rewrite Env_find_restr_hist, Env.gempty; simpl.
        apply Env.Props.P.F.not_find_in_iff; rewrite DH; auto.
      - (* environment is not empty *)
        inversion ND as [|? ? Nx ND']; subst.
        exists (Env.add x (fun i => match Env.find x (H i) with Some y => y | None => absent end)
                   (Env.from_list (map (fun x => (x,
                                               fun i => match Env.find x (H i) with Some y => y | None => absent end)) xs))).
        setoid_rewrite Env_add_restr_hist.
        split.
        + (* show point-wise equality of H and H' *)
          intro i.
          assert (forall i, Env.In x (H i)) as Ix
              by (intro j; specialize (DH j);
                  apply Env.dom_use with (x0:=x) in DH; firstorder).
          setoid_rewrite Env.In_find in Ix.
          destruct (Ix i) as (v & Ixi). rewrite Ixi.
          apply Env.add_remove in Ixi. rewrite Ixi at 1.
          apply Env.Equal_add_both.
          assert (forall i, Env.dom (Env.remove x (H i)) xs) as Dr.
          { intro j. specialize (DH j).
            apply Env.dom_cons_remove with (x0:=x) in DH. simpl in DH.
            rewrite nequiv_decb_refl, not_in_filter_nequiv_decb in DH; auto. }
          specialize (IH ND' (fun i => Env.remove x (H i)) Dr) as (H' & IH1 & IH2).
          intro y. destruct (in_dec ident_eq_dec y xs) as [Iy|Ny].
          * (* element in domain of environment *)
            rewrite IH1.
            assert (y <> x) by (intro; subst; auto).
            repeat rewrite Env_find_restr_hist. rewrite IH2; auto; clear IH2.
            simpl. specialize (Dr i). apply Env.dom_use with (x0:=y) in Dr.
            destruct Dr as (Dr1 & Dr2). specialize (Dr2 Iy).
            rewrite Env.In_find in Dr2. destruct Dr2 as (yv & Fy); rewrite Fy.
            erewrite Env.find_In_from_list.
            2:now apply in_map_iff; eauto.
            now simpl; rewrite Env.gro in Fy; auto; rewrite Fy.
            now apply fst_NoDupMembers; rewrite map_map, map_id.
          * (* element outside domain of environment *)
            rewrite Env.find_not_In_dom with (1:=Dr i) (2:=Ny).
            rewrite Env.find_not_In_dom with (2:=Ny); auto.
            apply Env_dom_restr_hist, Env.dom_from_list_map_fst;
              [apply fst_NoDupMembers|]; now rewrite map_map, map_id.
        + (* show characterization of H' *)
          intros y Iy. inv Iy. now rewrite Env.gss.
          rewrite Env.gso; [|intro; subst; auto].
          erewrite Env.find_In_from_list. reflexivity.
          now apply in_map_iff; eauto.
          apply fst_NoDupMembers. rewrite map_map; simpl.
          rewrite map_id. inv ND; auto.
    Qed.

  End HistoryRestriction.

  (** ** Instantaneous semantics *)

  Section InstantSemantics.

    (**

An history maps variables to streams of values (the variables'
histories). Taking a snapshot of the history at a given time yields an
environment.

     *)

    Definition history := stream env.

    Variable base: bool.
    Variable R: env.

    Definition sem_var_instant (x: ident) (v: svalue) : Prop :=
      Env.find x R = Some v.

    Inductive sem_clock_instant: clock -> bool -> Prop :=
    | Sbase:
        sem_clock_instant Cbase base
    | Son:
        forall ck x t b,
          sem_clock_instant ck true ->
          sem_var_instant x (present (Venum b)) ->
          sem_clock_instant (Con ck x (t, b)) true
    | Son_abs1:
        forall ck x c,
          sem_clock_instant ck false ->
          sem_var_instant x absent ->
          sem_clock_instant (Con ck x c) false
    | Son_abs2:
        forall ck x t b b',
          sem_clock_instant ck true ->
          sem_var_instant x (present (Venum b')) ->
          b <> b' ->
          sem_clock_instant (Con ck x (t, b)) false.

  End InstantSemantics.

  Add Parametric Morphism : sem_var_instant
      with signature Env.Equiv eq ==> @eq _ ==> @eq _ ==> Basics.impl
        as sem_var_instant_morph.
  Proof.
    intros H H' EH x v Hvar.
    eapply Env.Equiv_orel in EH. rewrite Hvar in EH. inv EH.
    symmetry in H1. eapply H1.
  Qed.

  Add Parametric Morphism : sem_clock_instant
      with signature eq ==> Env.Equiv eq ==> eq ==> eq ==> Basics.impl
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
    Variable H : history.

    Definition lift {A B} (sem: bool -> env -> A -> B -> Prop)
               x (ys: stream B): Prop :=
      forall n, sem (bk n) (H n) x (ys n).
    Hint Unfold lift.

    Definition lift' {A B} (sem: env -> A -> B -> Prop) x (ys: stream B): Prop :=
      forall n, sem (H n) x (ys n).
    Hint Unfold lift'.

    Definition sem_var (x: ident) (xs: stream svalue): Prop :=
      lift' sem_var_instant x xs.

    Definition sem_clock (ck: clock) (xs: stream bool): Prop :=
      lift sem_clock_instant ck xs.

  End LiftSemantics.

  (** ** Determinism of the semantics *)

  (** *** Instantaneous semantics *)

  Section InstantDeterminism.

    Variable base: bool.
    Variable R: env.

    Lemma sem_var_instant_det:
      forall x v1 v2,
        sem_var_instant R x v1
        -> sem_var_instant R x v2
        -> v1 = v2.
    Proof.
      congruence.
    Qed.

    Lemma sem_clock_instant_det:
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
    Variable H : history.

    Lemma lift_det:
      forall {A B} (P: bool -> env -> A -> B -> Prop) (bk: stream bool)
        x (xs1 xs2 : stream B),
        (forall b R v1 v2, P b R x v1 -> P b R x v2 -> v1 = v2) ->
        lift bk H P x xs1 -> lift bk H P x xs2 -> xs1 = xs2.
    Proof.
      intros * Hpoint H1 H2.
      extensionality n. specialize (H1 n). specialize (H2 n).
      eapply Hpoint; eassumption.
    Qed.

    Lemma lift'_det:
      forall {A B} (P: env -> A -> B -> Prop)
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

    Lemma sem_var_det:
      forall x xs1 xs2,
        sem_var H x xs1 -> sem_var H x xs2 -> xs1 = xs2.
    Proof.
      apply_lift' sem_var_instant_det.
    Qed.

    Lemma sem_clock_det:
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
    Variable R: env.

    Definition interp_var_instant (x: ident): svalue :=
      match Env.find x R with
      | Some v => v
      | None => absent
      end.

    Lemma interp_var_instant_complete:
      forall x v,
        sem_var_instant R x v ->
        v = interp_var_instant x.
    Proof.
      unfold interp_var_instant; now intros * ->.
    Qed.

    Fixpoint interp_clock_instant (c: clock): bool :=
      match c with
      | Cbase =>
        base
      | Con c x (t, b) =>
        let cb := interp_clock_instant c in
        andb cb (interp_var_instant x ==b present (Venum b))
      end.

    Ltac rw_exp_helper :=
      repeat match goal with
             | _: sem_var_instant R ?x ?v |- context[interp_var_instant ?x] =>
               erewrite <-(interp_var_instant_complete x v); eauto; simpl
             | H: sem_unop ?op ?c ?t = _ |- context[sem_unop ?op ?c ?t] =>
               rewrite H
             | H: sem_binop ?op ?c1 ?t1 ?c2 ?t2 = _ |- context[sem_binop ?op ?c1 ?t1 ?c2 ?t2] =>
               rewrite H
          end.

    Lemma interp_clock_instant_complete:
      forall c b,
        sem_clock_instant base R c b ->
        b = interp_clock_instant c.
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
    Variable H: history.

    Definition lift_interp {A B} (interp: bool -> env -> A -> B) x: stream B :=
      fun n => interp (bk n) (H n) x.

    Definition lift_interp' {A B} (interp: env -> A -> B) x: stream B :=
      fun n => interp (H n) x.

    Definition interp_clock (ck: clock): stream bool :=
      lift_interp interp_clock_instant ck.

    Definition interp_var (x: ident): stream svalue :=
      lift_interp' interp_var_instant x.

    Lemma lift_complete:
      forall {A B} (sem: bool -> env -> A -> B -> Prop) interp x xs,
        (forall b R x v, sem b R x v -> v = interp b R x) ->
        lift bk H sem x xs ->
        xs ≈ lift_interp interp x.
    Proof.
      intros * Instant Sem n.
      specialize (Sem n); unfold lift_interp; auto.
    Qed.

    Lemma lift'_complete:
      forall {A B} (sem: env -> A -> B -> Prop) interp x xs,
        (forall R x v, sem R x v -> v = interp R x) ->
        lift' H sem x xs ->
        xs ≈ lift_interp' interp x.
    Proof.
      intros * Instant Sem n.
      specialize (Sem n); unfold lift_interp'; auto.
    Qed.

    Corollary interp_clock_complete:
      forall ck bs,
        sem_clock bk H ck bs ->
        bs ≈ interp_clock ck.
    Proof.
      intros; eapply lift_complete; eauto;
        apply interp_clock_instant_complete.
    Qed.

    Corollary interp_var_complete:
      forall x vs,
        sem_var H x vs ->
        vs ≈ interp_var x.
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
