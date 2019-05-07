Require Import Velus.Common.Common.
Require Import List.

Require Import Morphisms.
Import Permutation.

Require Export ClockDefs.

(** ** Clocks *)

Inductive Is_free_in_clock : ident -> clock -> Prop :=
| FreeCon1:
    forall x ck' xc,
      Is_free_in_clock x (Con ck' x xc)
| FreeCon2:
    forall x y ck' xc,
      Is_free_in_clock x ck'
      -> Is_free_in_clock x (Con ck' y xc).

Require Import Coq.Classes.EquivDec.
Open Scope bool.

Fixpoint clock_eq (ck1 ck2: clock) : bool :=
  match ck1, ck2 with
  | Cbase, Cbase => true
  | Con ck1' x1 b1, Con ck2' x2 b2 =>
    (Pos.eqb x1 x2 && (b1 ==b b2)) && clock_eq ck1' ck2'
  | _, _ => false
  end.

Lemma clock_eq_spec:
  forall ck1 ck2,
    clock_eq ck1 ck2 = true <-> ck1 = ck2.
Proof.
  induction ck1, ck2; split; intro HH; auto;
    try now inversion HH.
  - inversion HH as [Heq].
    apply andb_prop in Heq.
    destruct Heq as (Heq & Hc).
    apply andb_prop in Heq.
    destruct Heq as (Hi & Hb).
    apply Peqb_true_eq in Hi.
    rewrite equiv_decb_equiv in Hb.
    apply IHck1 in Hc.
    subst. rewrite Hb. reflexivity.
  - inversion HH as [Heq].
    subst. simpl.
    rewrite Bool.andb_true_iff.
    split. 2:now apply IHck1.
    rewrite Bool.andb_true_iff.
    split. now apply Pos.eqb_eq.
    now apply equiv_decb_equiv.
Qed.

Instance clock_EqDec : EqDec clock eq.
Proof.
  intros ck1 ck2. compute.
  pose proof (clock_eq_spec ck1 ck2) as Heq.
  destruct (clock_eq ck1 ck2); [left|right].
  now apply Heq.
  intro HH. apply Heq in HH.
  discriminate.
Qed.

Lemma clock_not_in_clock:
  forall ck x b,
    ~(ck = Con ck x b).
Proof.
  intros * Hck.
  induction ck; try discriminate.
  injection Hck; intros.
  apply IHck. now subst b x.
Qed.

(** ** Well-clocking *)

Inductive wc_clock (vars: list (ident * clock)) : clock -> Prop :=
| CCbase:
    wc_clock vars Cbase
| CCon:
    forall ck x b,
      wc_clock vars ck ->
      In (x, ck) vars ->
      wc_clock vars (Con ck x b).

Hint Constructors wc_clock : lclocking.

Definition wc_env vars : Prop :=
  Forall (fun xck => wc_clock vars (snd xck)) vars.

Lemma wc_env_var:
  forall vars x ck,
    wc_env vars
    -> In (x, ck) vars
    -> wc_clock vars ck.
Proof.
  intros vars x ck Hwc Hcv.
  now apply Forall_forall with (2:=Hcv) in Hwc.
Qed.

Lemma wc_clock_add:
  forall x v env ck,
    ~InMembers x env ->
    wc_clock env ck ->
    wc_clock ((x, v) :: env) ck.
Proof.
  induction ck; auto using wc_clock.
  inversion 2.
  auto using wc_clock with datatypes.
Qed.

Lemma wc_env_add:
  forall x env ck,
    ~InMembers x env ->
    wc_clock env ck ->
    wc_env env ->
    wc_env ((x, ck) :: env).
Proof.
  intros * Hnm Hwc Hwce.
  constructor.
  now apply wc_clock_add; auto.
  apply Forall_forall.
  destruct x0 as (x' & ck').
  intro Hin.
  apply Forall_forall with (1:=Hwce) in Hin.
  apply wc_clock_add; auto.
Qed.

Lemma wc_clock_sub:
  forall vars ck x b,
    wc_env vars
    -> wc_clock vars (Con ck x b)
    -> In (x, ck) vars.
Proof.
  intros vars ck x b Hwc Hclock.
  inversion_clear Hclock as [|? ? ? Hclock' Hcv'].
  assumption.
Qed.

Instance wc_clock_Proper:
  Proper (@Permutation (ident * clock) ==> @eq clock ==> iff) wc_clock.
Proof.
  intros env' env Henv ck' ck Hck.
  rewrite Hck; clear Hck ck'.
  induction ck.
  - split; auto using wc_clock.
  - destruct IHck.
    split; inversion_clear 1; constructor;
      try rewrite Henv in *;
      auto using wc_clock.
Qed.

Instance wc_env_Proper:
  Proper (@Permutation (ident * clock) ==> iff) wc_env.
Proof.
  intros env' env Henv.
  unfold wc_env.
  split; intro HH.
  - apply Forall_forall.
    intros x Hin.
    rewrite <-Henv in Hin.
    apply Forall_forall with (1:=HH) in Hin.
    now rewrite Henv in Hin.
  - apply Forall_forall.
    intros x Hin.
    rewrite Henv in Hin.
    apply Forall_forall with (1:=HH) in Hin.
    now rewrite <-Henv in Hin.
Qed.

(** ** Parent relation *)

Inductive clock_parent ck : clock -> Prop :=
| CP0: forall x b,
    clock_parent ck (Con ck x b)
| CP1: forall ck' x b,
    clock_parent ck ck'
    -> clock_parent ck (Con ck' x b).

Lemma clock_parent_parent':
  forall ck' ck i b,
    clock_parent (Con ck i b) ck'
    -> clock_parent ck ck'.
Proof.
  Hint Constructors clock_parent.
  induction ck' as [|? IH]; [now inversion 1|].
  intros ck i' b' Hcp.
  inversion Hcp as [|? ? ? Hcp']; [now auto|].
  apply IH in Hcp'; auto.
Qed.

Lemma clock_parent_parent:
  forall ck' ck i b,
    clock_parent (Con ck i b) ck'
    -> clock_parent ck (Con ck' i b).
Proof.
  Hint Constructors clock_parent.
  destruct ck'; [now inversion 1|].
  intros ck i' b' Hcp.
  inversion Hcp as [|? ? ? Hcp']; [now auto|].
  apply clock_parent_parent' in Hcp'; auto.
Qed.

Lemma clock_parent_trans:
  forall ck1 ck2 ck3,
    clock_parent ck1 ck2 ->
    clock_parent ck2 ck3 ->
    clock_parent ck1 ck3.
Proof.
  induction ck2. now inversion 1.
  intros ck3 H12 H23.
  apply clock_parent_parent' in H23.
  inversion_clear H12; auto.
Qed.

Instance clock_parent_Transitive: Transitive clock_parent.
Proof clock_parent_trans.

Lemma clock_parent_Cbase:
  forall ck i b,
    clock_parent Cbase (Con ck i b).
Proof.
  induction ck as [|? IH]; [now constructor|].
  intros; constructor; apply IH.
Qed.

Lemma clock_parent_not_refl:
  forall ck,
    ~clock_parent ck ck.
Proof.
  induction ck as [|? IH]; [now inversion 1|].
  intro Hp; inversion Hp as [? ? HR|? ? ? Hp'].
  - rewrite HR in Hp; contradiction.
  - apply clock_parent_parent' in Hp'; contradiction.
Qed.

Lemma clock_parent_no_loops:
  forall ck ck',
    clock_parent ck ck'
    -> ck <> ck'.
Proof.
  intros ck ck' Hck Heq.
  rewrite Heq in Hck.
  apply clock_parent_not_refl with (1:=Hck).
Qed.

Lemma clock_no_loops:
  forall ck x b,
    Con ck x b <> ck.
Proof.
  induction ck as [|? IH]; [discriminate 1|].
  injection 1; intros ? Heq.
  apply IH.
Qed.

Lemma clock_parent_Con:
  forall ck ck' i b j c,
    clock_parent (Con ck i b) (Con ck' j c)
    -> clock_parent ck ck'.
Proof.
  destruct ck; induction ck' as [|? IH].
  - inversion 1 as [|? ? ? Hp].
    apply clock_parent_parent' in Hp; inversion Hp.
  - intros; now apply clock_parent_Cbase.
  - inversion 1 as [|? ? ? Hp]; inversion Hp.
  - intros i' b' j  c.
    inversion 1 as [? ? Hck'|? ? ? Hp];
      [rewrite Hck' in IH; now constructor|].
    apply IH in Hp; auto.
Qed.

Lemma clock_parent_strict':
  forall ck' ck,
    ~(clock_parent ck ck' /\ clock_parent ck' ck).
Proof.
  induction ck' as [|? IH]; destruct ck; destruct 1 as [Hp Hp'];
  try now (inversion Hp || inversion Hp').
  apply clock_parent_Con in Hp.
  apply clock_parent_Con in Hp'.
  eapply IH; split; eassumption.
Qed.

Lemma clock_parent_strict:
  forall ck' ck,
    (clock_parent ck ck' -> ~clock_parent ck' ck).
Proof.
  destruct ck'; [now inversion 1|].
  intros ck Hp Hp'.
  eapply clock_parent_strict'; split; eassumption.
Qed.

Lemma Con_not_clock_parent:
  forall ck x b,
    ~clock_parent (Con ck x b) ck.
Proof.
  intros ck x b Hp; apply clock_parent_strict with (1:=Hp); constructor.
Qed.

Lemma Is_free_in_clock_self_or_parent:
  forall x ck,
    Is_free_in_clock x ck
    -> exists ck' b, ck = Con ck' x b \/ clock_parent (Con ck' x b) ck.
Proof.
  Hint Constructors clock_parent.
  induction ck as [|? IH]; [now inversion 1|].
  intro Hfree.
  inversion Hfree as [|? ? ? ? Hfree']; clear Hfree; subst.
  - exists ck, b; now auto.
  - specialize (IH Hfree'); clear Hfree'.
    destruct IH as [ck' [b' Hcp]].
    exists ck', b'; right.
    destruct Hcp as [Hcp|Hcp]; [rewrite Hcp| inversion Hcp]; now auto.
Qed.

Lemma wc_clock_parent:
  forall C ck' ck,
    wc_env C
    -> clock_parent ck ck'
    -> wc_clock C ck'
    -> wc_clock C ck.
Proof.
  Hint Constructors wc_clock.
  induction ck' as [|ck' IH]; destruct ck as [|ck i' ty'];
  try now (inversion 3 || auto).
  intros Hwc Hp Hck.
  inversion Hp as [j c [HR1 HR2 HR3]|ck'' j c Hp' [HR1 HR2 HR3]].
  - rewrite <-HR1 in *; clear HR1 HR2 HR3.
    now inversion_clear Hck.
  - subst.
    apply IH with (1:=Hwc) (2:=Hp').
    now inversion Hck.
Qed.

Lemma instck_parent:
  forall bk sub ck ck',
    instck bk sub ck = Some ck' ->
    ck' = bk \/ clock_parent bk ck'.
Proof.
  induction ck.
  now inversion_clear 1; auto.
  simpl. intros ck' Hi. right.
  destruct (instck bk sub ck). 2:discriminate.
  destruct (sub i). 2:discriminate.
  specialize (IHck c eq_refl).
  inversion_clear Hi.
  destruct IHck; subst; auto.
Qed.

(* TODO: move elsewhere *)
Lemma instck_subclock_not_clock_eq:
  forall ck isub xck c x b,
    instck ck isub xck = Some c ->
    clock_eq ck (Con c x b) = false.
Proof.
  intros * Hck.
  apply Bool.not_true_is_false.
  intro Heq. apply clock_eq_spec in Heq.
  apply instck_parent in Hck as [Hck|Hck].
  now subst c; apply clock_not_in_clock in Heq.
  now subst ck; apply Con_not_clock_parent in Hck.
Qed.

(* Named clocks *)

Inductive wc_sclock (vars: list (ident * clock)) : sclock -> Prop :=
| CSbase:
    wc_sclock vars Sbase
| CSonI:
    forall sck i b,
      wc_sclock vars sck ->
      wc_sclock vars (Son sck (Vidx i) b)
| CSonN:
    forall sck ck x b,
      wc_sclock vars sck ->
      In (x, ck) vars ->
      sck = sclk ck ->
      wc_sclock vars (Son sck (Vnm x) b).

Hint Constructors wc_sclock : lclocking.

Inductive Is_index_in_sclock (i: positive) : sclock -> Prop :=
| IdxInSon0: forall sck b,
    Is_index_in_sclock i (Son sck (Vidx i) b)
| IdxInSon1: forall sck ni b,
    Is_index_in_sclock i sck ->
    Is_index_in_sclock i (Son sck ni b).

Inductive Is_index_in_nclock (i: positive) : nclock -> Prop :=
| IdxInStream: forall sck,
    Is_index_in_sclock i sck ->
    Is_index_in_nclock i (Cstream sck)
| IdxInNamed1: forall sck,
    Is_index_in_nclock i (Cnamed (Vidx i) sck)
| IdxInNamed2: forall sck ckid,
    Is_index_in_sclock i sck ->
    Is_index_in_nclock i (Cnamed ckid sck).

Definition Is_index_in_nclocks (i: positive) : list nclock -> Prop :=
  Exists (Is_index_in_nclock i).

Hint Unfold Is_index_in_nclocks : lclocking.

Inductive DisjointIndexes : list (list nclock) -> Prop :=
| DisjointIdxNil:
    DisjointIndexes nil
| DisjointIdxCons: forall ncks nckss,
    DisjointIndexes nckss ->
    (forall i, Is_index_in_nclocks i ncks ->
               Forall (fun ncks' => ~Is_index_in_nclocks i ncks') nckss) ->
    DisjointIndexes (ncks :: nckss).

Fixpoint sclock_eq (ck1 ck2: sclock) : bool :=
  match ck1, ck2 with
  | Sbase, Sbase => true
  | Son ck1' (Vnm x1) b1, Son ck2' (Vnm x2) b2 =>
    (Pos.eqb x1 x2 && (b1 ==b b2)) && sclock_eq ck1' ck2'
  | Son ck1' (Vidx i1) b1, Son ck2' (Vidx i2) b2 =>
    (Pos.eqb i1 i2 && (b1 ==b b2)) && sclock_eq ck1' ck2'
  | _, _ => false
  end.

Lemma sclock_eq_spec:
  forall ck1 ck2,
    sclock_eq ck1 ck2 = true <-> ck1 = ck2.
Proof.
  induction ck1, ck2; split; intro HH; auto;
    try now inversion HH.
  - inversion HH as [Heq].
    destruct c; inversion Heq.
  - inversion HH as [Heq].
    destruct c, c0; try (now inversion Heq).
    + apply andb_prop in Heq.
      destruct Heq as (Heq & Hc).
      apply andb_prop in Heq.
      destruct Heq as (Hi & Hb).
      apply Peqb_true_eq in Hi.
      rewrite equiv_decb_equiv in Hb.
      apply IHck1 in Hc.
      subst. rewrite Hb. reflexivity.
    + apply andb_prop in Heq.
      destruct Heq as (Heq & Hc).
      apply andb_prop in Heq.
      destruct Heq as (Hi & Hb).
      apply Peqb_true_eq in Hi.
      rewrite equiv_decb_equiv in Hb.
      apply IHck1 in Hc.
      subst. rewrite Hb. reflexivity.
  - inversion HH as [Heq].
    destruct c, c0; try (now inversion Heq).
    + subst. simpl.
      rewrite Bool.andb_true_iff.
      split. 2:now apply IHck1.
      rewrite Bool.andb_true_iff.
      split. now apply Pos.eqb_eq.
      now apply equiv_decb_equiv.
    + subst. simpl.
      rewrite Bool.andb_true_iff.
      split. 2:now apply IHck1.
      rewrite Bool.andb_true_iff.
      split. now apply Pos.eqb_eq.
      now apply equiv_decb_equiv.
Qed.

Instance sclock_EqDec : EqDec sclock eq.
Proof.
  intros ck1 ck2. compute.
  pose proof (sclock_eq_spec ck1 ck2) as Heq.
  destruct (sclock_eq ck1 ck2); [left|right].
  now apply Heq.
  intro HH. apply Heq in HH.
  discriminate.
Qed.

Lemma not_Is_index_in_sclk:
  forall i clk,
    ~Is_index_in_sclock i (sclk clk).
Proof.
  induction clk; now inversion_clear 1.
Qed.

(** Minor predicates on sclock structure *)

Inductive Name_only_sclock : sclock -> Prop :=
| NameOnlySbase:
    Name_only_sclock Sbase
| NameOnlySck: forall sck n b,
    Name_only_sclock sck ->
    Name_only_sclock (Son sck (Vnm n) b).

Inductive Name_only_core_sclock : sclock -> Prop :=
| NameOnlyCore0: forall sck,
    Name_only_sclock sck ->
    Name_only_core_sclock sck
| NameOnlyCore1: forall sck i b,
    Name_only_core_sclock sck ->
    Name_only_core_sclock (Son sck (Vidx i) b).

Lemma Name_only_sclk:
  forall ck,
    Name_only_sclock (sclk ck).
Proof.
  induction ck; simpl; auto using Name_only_sclock.
Qed.

Hint Constructors Name_only_sclock Name_only_core_sclock : name_only_sclock.
Hint Resolve Name_only_sclk : name_only_sclock.

Lemma No_index_in_Name_only_sclock:
  forall sck,
    Name_only_sclock sck ->
    (forall j, ~Is_index_in_sclock j sck).
Proof.
  induction sck. now inversion 2.
  destruct c; inversion_clear 1.
  inversion_clear 1.
  eapply IHsck; eauto.
Qed.
