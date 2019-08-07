From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Environment.

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

  Notation vstream := (stream value).
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

  (** Count the number of resets ticks seen at [n] so far. *)
  Fixpoint count (rs: cstream) (n: nat) : nat :=
    let c := match n with 0 => 0 | S n => count rs n end in
    if rs n then S c else c.

  (** [mask k rs xss] is the list of streams which clips the list of streams
      [xss] between the [k]th and the [(k+1)]th reset, outputting absent
      everywhere else. *)
  Definition mask (k: nat) (rs: cstream) (xss: stream (list value))
    : stream (list value) :=
    fun n => if k =? (count rs n) then xss n else all_absent (xss 0).

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
    forall xss k r n,
      count r n <> k ->
      mask k r xss n = all_absent (xss 0).
  Proof.
    intros * E.
    unfold mask.
    assert ((k =? count r n) = false) as ->
        by (apply EqNat.beq_nat_false_iff; omega); auto.
  Qed.

  Lemma mask_transparent:
    forall xss k r n,
      count r n = k ->
      mask k r xss n = xss n.
  Proof.
    intros * E.
    unfold mask.
    assert ((k =? count r n) = true) as ->
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
    f_equal; auto.
  Qed.

  Lemma absent_list_mask:
    forall xss k r n,
      absent_list (xss n) ->
      absent_list (mask k r xss n).
  Proof.
    intros; unfold mask.
    destruct (k =? count r n); auto using all_absent_spec.
  Qed.

  Definition vstr (xss: stream (list const)): stream (list value) :=
    fun n => map (fun c => present (sem_const c)) (xss n).

  (** Restrictions of Environments *)
  Section HistoryRestriction.

    Definition env := Env.t value.
    Definition history := Env.t (stream value).

    Definition restr_hist (H : history) (n: nat): env :=
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
      forall xs (H : stream (Env.t value)),
        (forall i, Env.dom (H i) xs) ->
        (exists (H' : Env.t (stream value)),
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

End STREAM.

Module StreamFun
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op) <: STREAM Op OpAux.
  Include STREAM Op OpAux.
End StreamFun.
