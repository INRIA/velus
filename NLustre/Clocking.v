Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.
Require Import Rustre.Operators.
Require Import Rustre.NLustre.Syntax.
Require Import List.

(** * Well clocked programs *)

(** 

This family of predicates states that a program is well-clocked
wrt. its clock annotations.

 *)

Module Type CLOCKING
       (Import Ids : IDS)
       (Import Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op).

  Definition clockenv := PM.t clock.

  Implicit Type C: clockenv.

  Inductive wc_var C (x: ident) ck: Prop :=
  | Cv:
      PM.find x C = Some ck ->
      wc_var C x ck.

  Definition wc_vars C (xs: list ident) ck: Prop :=
    Forall (fun x => wc_var C x ck) xs.

  Inductive wc_clock C: clock -> Prop :=
  | CCbase:
      wc_clock C Cbase
  | CCon:
      forall ck x b,
        wc_clock C ck ->
        wc_var C x ck ->
        wc_clock C (Con ck x b).

  Inductive wc_lexp C: lexp -> clock -> Prop :=
  | Cconst:
      forall c,
        wc_lexp C (Econst c) Cbase
  | Cvar:
      forall x ck ty,
        wc_var C x ck ->
        wc_lexp C (Evar x ty) ck
  | Cwhen:
      forall e x b ck,
        wc_lexp C e ck ->
        wc_var C x ck ->
        wc_lexp C (Ewhen e x b) (Con ck x b)
  | Cunop:
      forall op e ck ty,
        wc_lexp C e ck ->
        wc_lexp C (Eunop op e ty) ck
  | Cbinop:
      forall op e1 e2 ck ty,
        wc_lexp C e1 ck ->
        wc_lexp C e2 ck ->
        wc_lexp C (Ebinop op e1 e2 ty) ck.

  Definition wc_lexps C (les: list lexp)(ck: clock): Prop :=
    Forall (fun le => wc_lexp C le ck) les.

  Inductive wc_cexp C: cexp -> clock -> Prop :=
  | Cmerge:
      forall x t f ck,
        wc_var C x ck ->
        wc_cexp C t (Con ck x true) ->
        wc_cexp C f (Con ck x false) ->
        wc_cexp C (Emerge x t f) ck
  | Cite:
      forall b t f ck,
        wc_lexp C b ck ->
        wc_cexp C t ck ->
        wc_cexp C f ck ->
        wc_cexp C (Eite b t f) ck
  | Cexp:
      forall e ck,
        wc_lexp C e ck ->
        wc_cexp C (Eexp e) ck.

  Inductive wc_equation C: equation -> Prop :=
  | CEqDef:
      forall x ck ce,
        wc_var C x ck ->
        wc_cexp C ce ck ->
        wc_equation C (EqDef x ck ce)
  | CEqApp:
      forall xs ck f les,
        wc_vars C xs ck ->
        wc_lexps C les ck ->
        wc_equation C (EqApp xs ck f les)
  | CEqFby:
      forall x ck v0 le,
        wc_var C x ck ->
        wc_lexp C le ck ->
        wc_equation C (EqFby x ck v0 le).

  Definition wc_env C : Prop :=
    forall x ck, PM.find x C = Some ck -> wc_clock C ck.
  
  Inductive wc_node : node -> Prop :=
  | SNode:
      forall f i o v eqs ingt0 outgt0 defd vout nodup good C,
        Forall (wc_equation C) eqs ->
        wc_vars C (map fst i) Cbase ->
        wc_vars C (map fst o) Cbase ->
        wc_env C ->
        wc_node (mk_node f i o v eqs ingt0 outgt0 defd vout nodup good).

  Definition wc_global G : Prop :=
    Forall (fun nd=> wc_node nd) G.

  Inductive Has_clock_eq: clock -> equation -> Prop :=
  | HcEqDef: forall x ck ce,
      Has_clock_eq ck (EqDef x ck ce)
  | HcEqApp: forall x f ck les,
      Has_clock_eq ck (EqApp x ck f les)
  | HcEqFby: forall x v0 ck le,
      Has_clock_eq ck (EqFby x ck v0 le).

  (** ** Basic properties of clocking *)

  Lemma wc_global_nil: wc_global nil.
  Proof.
    apply Forall_nil.
  Qed.

  Lemma wc_var_det:
    forall C x ck1 ck2,
      wc_var C x ck1
      -> wc_var C x ck2
      -> ck1 = ck2.
  Proof.
    intros C x ck1 ck2.
    do 2 inversion_clear 1.
    match goal with
    | H1: PM.find x C = _, H2: PM.find x C = _ |- _
      => rewrite H1 in H2; injection H2; now auto
    end.
  Qed.

  Lemma wc_env_var:
    forall C x ck,
      wc_env C
      -> wc_var C x ck
      -> wc_clock C ck.
  Proof.
    intros C x ck Hwc Hcv.
    unfold wc_env in Hwc.
    inversion_clear Hcv as [Hfv].
    apply Hwc with (1:=Hfv).
  Qed.

  Lemma wc_env_vars:
    forall C xs ck,
      0 < length xs 
      -> wc_env C
      -> wc_vars C xs ck
      -> wc_clock C ck.
  Proof.
    intros C xs ck Hlen Hwc Hcv.
    destruct xs; simpl in *; try now inv Hlen.
    eapply Forall_cons2 in Hcv as (? & _).
    eapply wc_env_var; eauto.
  Qed.

  Lemma wc_clock_lexp:
    forall C le ck,
      wc_env C
      -> wc_lexp C le ck
      -> wc_clock C ck.
  Proof.
    induction le as [| |le IH | |] (* using lexp_ind2 *).
    - inversion_clear 2; now constructor.
    - intros ck Hwc; inversion_clear 1 as [|? ? ? Hcv| | |].
      apply wc_env_var with (1:=Hwc) (2:=Hcv).
    - intros ck Hwc.
      inversion_clear 1 as [| |? ? ? ck' Hle Hcv | |].
      constructor; [now apply IH with (1:=Hwc) (2:=Hle)|assumption].
    - intros ck Hwc; inversion_clear 1; auto.
    - intros ck Hwc; inversion_clear 1; auto.    
  Qed.

  Lemma wc_clock_cexp:
    forall C ce ck,
      wc_env C
      -> wc_cexp C ce ck
      -> wc_clock C ck.
  Proof.
    induction ce as [i ce1 IH1 ce2 IH2| |].
    - intros ck Hwc.
      inversion_clear 1 as [? ? ? ? Hcv Hct Hcf| |].
      apply IH1 with (1:=Hwc) in Hct.
      inversion_clear Hct; assumption.
    - intros ck Hwc; inversion_clear 1 as [|? ? ? ? Hl H1 H2|].
      now apply IHce1.
    - intros ck Hwc; inversion_clear 1 as [| |? ? Hck].
      apply wc_clock_lexp with (1:=Hwc) (2:=Hck).
  Qed.

  Lemma clock_no_loops:
    forall ck x b,
      Con ck x b <> ck.
  Proof.
    induction ck as [|? IH]; [discriminate 1|].
    injection 1; intros ? Heq.
    apply IH.  
  Qed.

  Lemma wc_clock_sub:
    forall C ck x b,
      wc_env C
      -> wc_clock C (Con ck x b)
      -> wc_var C x ck.
  Proof.
    intros C ck x b Hwc Hclock.
    inversion_clear Hclock as [|? ? ? Hclock' Hcv'].
    assumption.
  Qed.

End CLOCKING.

Module ClockingFun
       (Import Ids : IDS)
       (Import Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       <: CLOCKING Ids Op Syn.
  Include CLOCKING Ids Op Syn.
End ClockingFun.
