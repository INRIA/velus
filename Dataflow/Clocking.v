Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.
Require Import Nelist.
Require Import List.

(** * Well clocked programs *)

(** 

This family of predicates states that a program is well-clocked
wrt. its clock annotations.

 *)

Module Type CLOCKING
       (Import Op : OPERATORS)
       (Import Syn : SYNTAX Op).

  Definition clockenv := PM.t clock.

  Implicit Type C: clockenv.


  Inductive clk_var C (x: ident) ck: Prop :=
  | Cv:
      PM.find x C = Some ck ->
      clk_var C x ck.

  Definition clk_vars C (xs: nelist ident) ck: Prop :=
    Nelist.Forall (fun x => clk_var C x ck) xs.

  Inductive clk_clock C: clock -> Prop :=
  | CCbase:
      clk_clock C Cbase
  | CCon:
      forall ck x b ty,
        clk_clock C ck ->
        clk_var C x ck ->
        clk_clock C (Con ck x ty b).

  Inductive clk_lexp C: lexp -> clock -> Prop :=
  | Cconst:
      forall c ty,
        clk_lexp C (Econst c ty) Cbase
  | Cvar:
      forall x ck ty,
        clk_var C x ck ->
        clk_lexp C (Evar x ty) ck
  | Cwhen:
      forall e x b ck ty,
        clk_lexp C e ck ->
        clk_var C x ck ->
        clk_lexp C (Ewhen e x b) (Con ck x ty b)
  (* | Cop: *)
  (*     forall op les ck, *)
  (*       Nelist.Forall (fun e => clk_lexp C e ck) les -> *)
  (*       clk_lexp C (Eop op les) ck *)
  | Cunop:
      forall op e ck ty,
        clk_lexp C e ck ->
        clk_lexp C (Eunop op e ty) ck
  | Cbinop:
      forall op e1 e2 ck ty,
        clk_lexp C e1 ck ->
        clk_lexp C e2 ck ->
        clk_lexp C (Ebinop op e1 e2 ty) ck.

  Definition clk_lexps C (les: nelist lexp)(ck: clock): Prop :=
    Nelist.Forall (fun le => clk_lexp C le ck) les.

  Inductive clk_cexp C: cexp -> clock -> Prop :=
  | Cmerge:
      forall x t f ck ty,
        clk_var C x ck ->
        clk_cexp C t (Con ck x ty true) ->
        clk_cexp C f (Con ck x ty false) ->
        clk_cexp C (Emerge x ty t f) ck
  | Cite:
      forall b t f ck,
        clk_lexp C b ck ->
        clk_cexp C t ck ->
        clk_cexp C f ck ->
        clk_cexp C (Eite b t f) ck
  | Cexp:
      forall e ck,
        clk_lexp C e ck ->
        clk_cexp C (Eexp e) ck.

  Inductive Well_clocked_eq C: equation -> Prop :=
  | CEqDef:
      forall x ck ce,
        clk_var C x ck ->
        clk_cexp C ce ck ->
        Well_clocked_eq C (EqDef x ck ce)
  | CEqApp:
      forall x ck f les ty,
        clk_var C x ck ->
        clk_lexps C les ck ->
        Well_clocked_eq C (EqApp x ck f les ty)
  | CEqFby:
      forall x ck v0 le,
        clk_var C x ck ->
        clk_lexp C le ck ->
        Well_clocked_eq C (EqFby x ck v0 le).

  Inductive Well_clocked_node C: node -> Prop :=
  | SNode:
      forall f i o v eqs,
        Forall (Well_clocked_eq C) eqs ->
        clk_vars C (Nelist.map_fst i) Cbase ->
        clk_var C (fst o) Cbase ->
        Well_clocked_node C (mk_node f i o v eqs).

  Definition Well_clocked_env C : Prop :=
    forall x ck, PM.find x C = Some ck -> clk_clock C ck.

  Definition Well_clocked G : Prop :=
    Forall (fun nd=> exists C, Well_clocked_node C nd) G.

  Inductive Has_clock_eq: clock -> equation -> Prop :=
  | HcEqDef: forall x ck ce,
      Has_clock_eq ck (EqDef x ck ce)
  | HcEqApp: forall x f ck les ty,
      Has_clock_eq ck (EqApp x ck f les ty)
  | HcEqFby: forall x v0 ck le,
      Has_clock_eq ck (EqFby x ck v0 le).

  (** ** Basic properties of clocking *)

  Lemma clk_var_det:
    forall C x ck1 ck2,
      clk_var C x ck1
      -> clk_var C x ck2
      -> ck1 = ck2.
  Proof.
    intros C x ck1 ck2.
    do 2 inversion_clear 1.
    match goal with
    | H1: PM.find x C = _, H2: PM.find x C = _ |- _
      => rewrite H1 in H2; injection H2; now auto
    end.
  Qed.

  Lemma Well_clocked_env_var:
    forall C x ck,
      Well_clocked_env C
      -> clk_var C x ck
      -> clk_clock C ck.
  Proof.
    intros C x ck Hwc Hcv.
    unfold Well_clocked_env in Hwc.
    inversion_clear Hcv as [Hfv].
    apply Hwc with (1:=Hfv).
  Qed.

  Lemma clk_clock_lexp:
    forall C le ck,
      Well_clocked_env C
      -> clk_lexp C le ck
      -> clk_clock C ck.
  Proof.
    induction le as [| |le IH | |] (* using lexp_ind2 *).
    - inversion_clear 2; now constructor.
    - intros ck Hwc; inversion_clear 1 as [|? ? ? Hcv| | |].
      apply Well_clocked_env_var with (1:=Hwc) (2:=Hcv).
    - intros ck Hwc.
      inversion_clear 1 as [| |? ? ? ? ck' Hle Hcv | |].
      constructor; [now apply IH with (1:=Hwc) (2:=Hle)|assumption].
    - intros ck Hwc; inversion_clear 1; auto.
    - intros ck Hwc; inversion_clear 1; auto.    
  Qed.

  Lemma clk_clock_cexp:
    forall C ce ck,
      Well_clocked_env C
      -> clk_cexp C ce ck
      -> clk_clock C ck.
  Proof.
    induction ce as [i ty ce1 IH1 ce2 IH2| |].
    - intros ck Hwc.
      inversion_clear 1 as [? ? ? ? ? Hcv Hct Hcf| |].
      apply IH1 with (1:=Hwc) in Hct.
      inversion_clear Hct; assumption.
    - intros ck Hwc; inversion_clear 1 as [|? ? ? ? Hl H1 H2|].
      now apply IHce1.
    - intros ck Hwc; inversion_clear 1 as [| |? ? Hck].
      apply clk_clock_lexp with (1:=Hwc) (2:=Hck).
  Qed.

  Lemma clock_no_loops:
    forall ck x ty b,
      Con ck x ty b <> ck.
  Proof.
    induction ck as [|? IH]; [discriminate 1|].
    injection 1; intros ? ? Heq.
    apply IH.  
  Qed.

  Lemma clk_clock_sub:
    forall C ck x ty b,
      Well_clocked_env C
      -> clk_clock C (Con ck x ty b)
      -> clk_var C x ck.
  Proof.
    intros C ck x ty b Hwc Hclock.
    inversion_clear Hclock as [|? ? ? Hclock' Hcv'].
    assumption.
  Qed.

End CLOCKING.
