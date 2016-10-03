Require Import Rustre.Common.
Require Import Rustre.Operators.
Require Import Dataflow.Syntax.
Require Import Dataflow.Clocking.
Require Import Dataflow.Clocking.Parents.

Require Import Dataflow.IsFree.
Require Import Dataflow.IsDefined.
Require Import Dataflow.Memories.

Module Type PROPERTIES
       (Ids : IDS)
       (Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (Import IsF : ISFREE Ids Op Syn)
       (Import Clo : CLOCKING Ids Op Syn)
       (Mem        : MEMORIES Ids Op Syn)
       (Import IsD : ISDEFINED Ids Op Syn Mem)
       (Import Par : PARENTS Ids Op Syn Clo).
  
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

Theorem Well_clocked_eq_not_Is_free_in_clock:
  forall C eq x ck,
    Well_clocked_env C
    -> Well_clocked_eq C eq
    -> Is_defined_in_eq x eq
    -> Has_clock_eq ck eq
    -> ~Is_free_in_clock x ck.
Proof.
  intros C eq x ck Hwc Hwce Hdef Hhasck Hfree.
  inversion Hwce as [x' ck' e Hcv Hexp Heq
                    |x' ck' f e Hcv Hexp Heq
                    |x' ck' v' e Hcv Hexp];
    subst; inversion Hdef; inversion Hhasck; clear Hdef Hhasck; subst;
    pose proof (Well_clocked_env_var _ _ _ Hwc Hcv) as Hclock;
    apply Is_free_in_clock_self_or_parent in Hfree;
    destruct Hfree as [ck [b [Hck|Hck]]];
    (rewrite Hck in *;
      apply clk_clock_sub with (1:=Hwc) in Hclock;
      apply clk_var_det with (1:=Hcv) in Hclock;
      apply clock_no_loops with (1:=Hclock))
    ||
    (apply clk_clock_parent with (1:=Hwc) (2:=Hck) in Hclock;
      apply clk_clock_sub with (1:=Hwc) in Hclock;
      apply clk_var_det with (1:=Hcv) in Hclock;
      apply clock_parent_parent' in Hck;
      rewrite <-Hclock in Hck;
      apply clock_parent_not_refl with (1:=Hck)).
Qed.

Corollary Well_clocked_EqDef_not_Is_free_in_clock:
  forall C x ce ck,
    Well_clocked_env C
    -> Well_clocked_eq C (EqDef x ck ce)
    -> ~Is_free_in_clock x ck.
Proof.
  intros C x ce ck Hwc Hwce.
  apply Well_clocked_eq_not_Is_free_in_clock with (1:=Hwc) (2:=Hwce);
    now constructor.
Qed.

Corollary Well_clocked_EqApp_not_Is_free_in_clock:
  forall C x f le ck,
    Well_clocked_env C
    -> Well_clocked_eq C (EqApp x ck f le)
    -> ~Is_free_in_clock x ck.
Proof.
  intros C x f le ck Hwc Hwce.
  apply Well_clocked_eq_not_Is_free_in_clock with (1:=Hwc) (2:=Hwce);
    now constructor.
Qed.

Corollary Well_clocked_EqFby_not_Is_free_in_clock:
  forall C x v0 le ck,
    Well_clocked_env C
    -> Well_clocked_eq C (EqFby x ck v0 le)
    -> ~Is_free_in_clock x ck.
Proof.
  intros C x v0 le ck Hwc Hwce.
  apply Well_clocked_eq_not_Is_free_in_clock with (1:=Hwc) (2:=Hwce);
    now constructor.
Qed.

End PROPERTIES.