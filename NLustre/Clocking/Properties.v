Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import NLustre.NLSyntax.
Require Import NLustre.Clocking.

Require Import NLustre.IsFree.
Require Import NLustre.IsDefined.
Require Import NLustre.Memories.

Module Type PROPERTIES
       (Ids         : IDS)
       (Op          : OPERATORS)
       (Import Clks : CLOCKS Ids)
       (Import Syn  : NLSYNTAX  Ids Op Clks)
       (Import IsF  : ISFREE    Ids Op Clks Syn)
       (Import Clo  : CLOCKING  Ids Op Clks Syn)
       (Mem         : MEMORIES  Ids Op Clks Syn)
       (Import IsD  : ISDEFINED Ids Op Clks Syn Mem).

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
  
  Section Well_clocked.

    (** We work under a (valid) clocking environment *)
    Variable vars : list (ident * clock).
    Variable Hnd : NoDupMembers vars.
    Variable Hwc : wc_env vars.

    Theorem wc_equation_not_Is_free_in_clock:
      forall eq x ck,
        wc_equation vars eq
        -> Is_defined_in_eq x eq
        -> Has_clock_eq ck eq
        -> ~Is_free_in_clock x ck.
    Proof.
      intros eq x' ck' Hwce Hdef Hhasck Hfree.
      inversion Hwce as [x ck e Hcv Hexp Heq
                        |xs ck f e Hvars Hexp Heq
                        |x ck v' e Hcv Hexp].
      - subst eq. inv Hdef. inv Hhasck.
        pose proof (wc_env_var _ _ _ Hwc Hcv) as Hclock.
        apply Is_free_in_clock_self_or_parent in Hfree.
        destruct Hfree as (ck' & b & [Hck|Hck]).
        + subst ck.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          pose proof (NoDupMembers_det _ _ _ _ Hnd Hcv Hclock) as Hloop.
          apply clock_no_loops with (1:=Hloop).
        + apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          rewrite (NoDupMembers_det _ _ _ _ Hnd Hcv Hclock) in *.
          apply clock_parent_parent' in Hck.
          apply clock_parent_not_refl with (1:=Hck).
      - subst eq. rename x' into x. inv Hdef. inv Hhasck.
        match goal with H:List.In x xs |- _ => rename H into Hin end.
        pose proof (In_Forall _ _ _ Hvars Hin) as Hcv.
        pose proof (wc_env_var _ _ _ Hwc Hcv) as Hclock.
        apply Is_free_in_clock_self_or_parent in Hfree.
        destruct Hfree as (ck' & b & [Hck|Hck]).
        + subst ck.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          pose proof (NoDupMembers_det _ _ _ _ Hnd Hcv Hclock) as Hloop.
          apply clock_no_loops with (1:=Hloop).
        + apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          rewrite (NoDupMembers_det _ _ _ _ Hnd Hcv Hclock) in *.
          apply clock_parent_parent' in Hck.
          apply clock_parent_not_refl with (1:=Hck).
      - subst eq. inv Hdef. inv Hhasck.
        pose proof (wc_env_var _ _ _ Hwc Hcv) as Hclock.
        apply Is_free_in_clock_self_or_parent in Hfree.
        destruct Hfree as (ck' & b & [Hck|Hck]).
        + subst ck.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          pose proof (NoDupMembers_det _ _ _ _ Hnd Hcv Hclock) as Hloop.
          apply clock_no_loops with (1:=Hloop).
        + apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          rewrite (NoDupMembers_det _ _ _ _ Hnd Hcv Hclock) in *.
          apply clock_parent_parent' in Hck.
          apply clock_parent_not_refl with (1:=Hck).
    Qed.

    Corollary wc_EqDef_not_Is_free_in_clock:
      forall x ce ck,
        wc_equation vars (EqDef x ck ce)
        -> ~Is_free_in_clock x ck.
    Proof.
      intros x ce ck Hwce Hwt.
      now eapply wc_equation_not_Is_free_in_clock;
        eauto using Has_clock_eq.
    Qed.

    Corollary wc_EqApp_not_Is_free_in_clock:
      forall xs f le ck,
        wc_equation vars (EqApp xs ck f le)
        -> forall x, List.In x xs -> ~Is_free_in_clock x ck.
    Proof.
      intros x f le ck Hwce Hwt y Hinx.
      now eapply wc_equation_not_Is_free_in_clock;
        eauto using Is_defined_in_eq, Has_clock_eq.
    Qed.

    Corollary wc_EqFby_not_Is_free_in_clock:
      forall x v0 le ck,
        wc_equation vars (EqFby x ck v0 le)
        -> ~Is_free_in_clock x ck.
    Proof.
      intros x v0 le ck Hwce Hwt.
      now eapply wc_equation_not_Is_free_in_clock;
        eauto using Has_clock_eq.
    Qed.

  End Well_clocked.

End PROPERTIES.

Module PropertiesFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Clks : CLOCKS    Ids)
       (Syn  : NLSYNTAX  Ids Op Clks)
       (IsF  : ISFREE    Ids Op Clks Syn)
       (Clo  : CLOCKING  Ids Op Clks Syn)
       (Mem  : MEMORIES  Ids Op Clks Syn)
       (IsD  : ISDEFINED Ids Op Clks Syn Mem)
       <: PROPERTIES Ids Op Clks Syn IsF Clo Mem IsD.
  Include PROPERTIES Ids Op Clks Syn IsF Clo Mem IsD.
End PropertiesFun.
