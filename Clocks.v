Require Import Velus.Common.

Module Type CLOCKS
       (Ids : IDS).

  (** ** Clocks *)

  Inductive clock : Type :=
  | Cbase : clock                            (* base clock *)
  | Con   : clock -> ident -> bool -> clock. (* subclock *)

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

End CLOCKS.

Module ClocksFun (Ids : IDS) <: CLOCKS Ids.
  Include CLOCKS Ids.
End ClocksFun.
