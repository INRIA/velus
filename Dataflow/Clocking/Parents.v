Require Import Rustre.Common.
Require Import Dataflow.Syntax.
Require Import Dataflow.Clocking.

Module Type PARENTS
       (Op : OPERATORS)
       (Import Syn : SYNTAX Op)
       (Import Clo : CLOCKING Op Syn).
  
  Inductive clock_parent ck : clock -> Prop :=
  | CP0: forall x ty b,
      clock_parent ck (Con ck x ty b)
  | CP1: forall ck' x ty b,
      clock_parent ck ck'
      -> clock_parent ck (Con ck' x ty b).

  Lemma clock_parent_parent':
    forall ck' ck i ty b,
      clock_parent (Con ck i ty b) ck'
      -> clock_parent ck ck'.
  Proof.
    Hint Constructors clock_parent.
    induction ck' as [|? IH]; [now inversion 1|].
    intros ck i' ty' b' Hcp.
    inversion Hcp as [|? ? ? ? Hcp']; [now auto|].
    apply IH in Hcp'; auto.
  Qed.

  Lemma clock_parent_parent:
    forall ck' ck i ty b,
      clock_parent (Con ck i ty b) ck'
      -> clock_parent ck (Con ck' i ty b).
  Proof.
    Hint Constructors clock_parent.
    destruct ck'; [now inversion 1|].
    intros ck i' ty' b' Hcp.
    inversion Hcp as [|? ? ? ? Hcp']; [now auto|].
    apply clock_parent_parent' in Hcp'; auto.
  Qed.

  Lemma clock_parent_Cbase:
    forall ck i ty b,
      clock_parent Cbase (Con ck i ty b).
  Proof.
    induction ck as [|? IH]; [now constructor|].
    intros; constructor; apply IH.
  Qed.

  Lemma clock_parent_not_refl:
    forall ck,
      ~clock_parent ck ck.
  Proof.
    induction ck as [|? IH]; [now inversion 1|].
    intro Hp; inversion Hp as [? ? ? HR|? ? ? ? Hp'].
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

  Lemma clock_parent_Con:
    forall ck ck' i ty b j ty' c,
      clock_parent (Con ck i ty b) (Con ck' j ty' c)
      -> clock_parent ck ck'.
  Proof.
    destruct ck; induction ck' as [|? IH].
    - inversion 1 as [|? ? ? ? Hp].
      apply clock_parent_parent' in Hp; inversion Hp.
    - intros; now apply clock_parent_Cbase.
    - inversion 1 as [|? ? ? ? Hp]; inversion Hp.
    - intros i' ty b' j ty' c.
      inversion 1 as [? ? ? Hck'|? ? ? ? Hp];
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
    forall ck x ty b,
      ~clock_parent (Con ck x ty b) ck.
  Proof.
    intros ck x ty b Hp; apply clock_parent_strict with (1:=Hp); constructor.
  Qed.

  Lemma clk_clock_parent:
    forall C ck' ck,
      Well_clocked_env C
      -> clock_parent ck ck'
      -> clk_clock C ck'
      -> clk_clock C ck.
  Proof.
    Hint Constructors clk_clock.
    induction ck' as [|ck' IH]; destruct ck as [|ck i' ty' b'];
    try now (inversion 3 || auto).
    intros Hwc Hp Hck.
    inversion Hp as [j ty c [HR1 HR2 HR3]|ck'' j ty c Hp' [HR1 HR2 HR3]].
    - rewrite <-HR1 in *; clear HR1 HR2 HR3.
      inversion_clear Hck as [|? ? ? ? Hck' Hcv].
      inversion_clear Hck'; auto.
    - subst.
      apply IH with (1:=Hwc) (2:=Hp').
      inversion Hck; assumption.
  Qed.

End PARENTS.