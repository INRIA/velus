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

Section Well_clocked.


(** We work under a (valid) clocking environment *)
Variable C : clockenv.
Variable Hwc: Well_clocked_env C.

Theorem Well_clocked_eq_not_Is_free_in_clock:
  forall eq x ck,
      Well_clocked_eq C eq
    -> Is_defined_in_eq x eq
    -> Has_clock_eq ck eq
    -> ~Is_free_in_clock x ck.
Proof.
(* XXX: This proof is rather fragile *)
  intros eq x ck Hwce Hdef Hhasck Hfree.
  inversion Hwce as [x' ck' e Hcv Hexp Heq
                    |x' ck' f e Hcv Hexp Heq
                    |x' ck' v' e Hcv Hexp];
    subst; inversion Hdef; inversion Hhasck; clear Hdef Hhasck; subst;
      match goal with
      | _: context[ EqApp _ _ _ _ ],
        Hin: List.In ?x x' |- _ =>
        (* Case: eq ~ EqApp *)
        (assert (Hlen : 0 < length x')
          by now destruct x'; inv Hin; apply Lt.lt_0_Sn);
        pose proof (In_Forall _ _ _ Hcv Hin) as Hck_x;
        simpl in *;
        generalize (Well_clocked_env_vars _ _ _ Hlen Hwc Hcv)
      | _ =>
        (* Case: eq ~ EqDef or eq ~ EqFby *)
        generalize (Well_clocked_env_var _ _ _ Hwc Hcv)
      end;
      intro Hclock;
      apply Is_free_in_clock_self_or_parent in Hfree;
      destruct Hfree as [ck [b [Hck|Hck]]];
      try match goal with
      | _ : _ = Con _ _ _ |- _ =>
        rewrite Hck in *;
          apply clk_clock_sub with (1:=Hwc) in Hclock;
          match reverse goal with
          | H: clk_var C _ _ |- _ => apply clk_var_det with (1:=H) in Hclock
          end;
          apply clock_no_loops with (1:=Hclock)
      | _ : clock_parent _ _ |- _ =>
        apply clk_clock_parent with (1:=Hwc) (2:=Hck) in Hclock;
          apply clk_clock_sub with (1:=Hwc) in Hclock;
          match reverse goal with
          | H: clk_var C _ _ |- _ => apply clk_var_det with (1:=H) in Hclock
          end;
          apply clock_parent_parent' in Hck;
          rewrite <-Hclock in Hck;
          apply clock_parent_not_refl with (1 := Hck)
      end.
Qed.

Corollary Well_clocked_EqDef_not_Is_free_in_clock:
  forall x ce ck,
      Well_clocked_eq C (EqDef x ck ce)
    -> ~Is_free_in_clock x ck.
Proof.
  intros x ce ck Hwce Hwt.
  now eapply Well_clocked_eq_not_Is_free_in_clock;
    eauto using Has_clock_eq.
Qed.

Corollary Well_clocked_EqApp_not_Is_free_in_clock:
  forall xs f le ck,
      Well_clocked_eq C (EqApp xs ck f le)
    -> forall x, List.In x xs -> ~Is_free_in_clock x ck.
Proof.
  intros x f le ck Hwce Hwt y Hinx.
  now eapply Well_clocked_eq_not_Is_free_in_clock;
    eauto using Is_defined_in_eq, Has_clock_eq.
Qed.

Corollary Well_clocked_EqFby_not_Is_free_in_clock:
  forall x v0 le ck,
      Well_clocked_eq C (EqFby x ck v0 le)
    -> ~Is_free_in_clock x ck.
Proof.
  intros x v0 le ck Hwce Hwt.
  now eapply Well_clocked_eq_not_Is_free_in_clock;
    eauto using Has_clock_eq.
Qed.

End Well_clocked.

End PROPERTIES.