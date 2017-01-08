Require Import Velus.Common.
Require Import List.

Module Type CLOCKS
       (Ids : IDS).

  (** ** Clocks *)

  Inductive clock : Type :=
  | Cbase : clock                            (* base clock *)
  | Con   : clock -> ident -> bool -> clock. (* subclock *)

  Inductive Is_free_in_clock : ident -> clock -> Prop :=
  | FreeCon1:
      forall x ck' xc,
        Is_free_in_clock x (Con ck' x xc)
  | FreeCon2:
      forall x y ck' xc,
        Is_free_in_clock x ck'
        -> Is_free_in_clock x (Con ck' y xc).
  
  (** ** Well-clocking *)

  Inductive wc_clock (vars: list (ident * clock)) : clock -> Prop :=
  | CCbase:
      wc_clock vars Cbase
  | CCon:
      forall ck x b,
        wc_clock vars ck ->
        In (x, ck) vars ->
        wc_clock vars (Con ck x b).

  Definition wc_env vars : Prop :=
    Forall (fun xck => wc_clock vars (snd xck)) vars.

  Lemma wc_env_var:
    forall vars x ck,
      wc_env vars
      -> In (x, ck) vars
      -> wc_clock vars ck.
  Proof.
    intros vars x ck Hwc Hcv.
    now apply In_Forall with (2:=Hcv) in Hwc.
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
    intros ** Hnm Hwc Hwce.
    constructor.
    now apply wc_clock_add; auto.
    apply all_In_Forall.
    destruct x0 as (x' & ck').
    intro Hin.
    apply In_Forall with (1:=Hwce) in Hin.
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

  Require Import Morphisms.
  Import Permutation.

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
    - apply all_In_Forall.
      intros x Hin.
      rewrite <-Henv in Hin.
      apply In_Forall with (1:=HH) in Hin.
      now rewrite Henv in Hin.
    - apply all_In_Forall.
      intros x Hin.
      rewrite Henv in Hin.
      apply In_Forall with (1:=HH) in Hin.
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
    induction ck' as [|ck' IH]; destruct ck as [|ck i' ty' b'];
    try now (inversion 3 || auto).
    intros Hwc Hp Hck.
    inversion Hp as [j c [HR1 HR2 HR3]|ck'' j c Hp' [HR1 HR2 HR3]].
    - rewrite <-HR1 in *; clear HR1 HR2 HR3.
      now inversion_clear Hck.
    - subst.
      apply IH with (1:=Hwc) (2:=Hp').
      now inversion Hck.
  Qed.
    
End CLOCKS.

Module ClocksFun (Ids : IDS) <: CLOCKS Ids.
  Include CLOCKS Ids.
End ClocksFun.
