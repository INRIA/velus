Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.NLustre.Syntax.
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

  Section WellClocked.

    Variable vars : list (ident * clock).

    Inductive wc_clock : clock -> Prop :=
    | CCbase:
        wc_clock Cbase
    | CCon:
        forall ck x b,
          wc_clock ck ->
          In (x, ck) vars ->
          wc_clock (Con ck x b).

    Inductive wc_lexp : lexp -> clock -> Prop :=
    | Cconst:
        forall c,
          wc_lexp (Econst c) Cbase
    | Cvar:
        forall x ck ty,
          In (x, ck) vars ->
          wc_lexp (Evar x ty) ck
    | Cwhen:
        forall e x b ck,
          wc_lexp e ck ->
          In (x, ck) vars ->
          wc_lexp (Ewhen e x b) (Con ck x b)
    | Cunop:
        forall op e ck ty,
          wc_lexp e ck ->
          wc_lexp (Eunop op e ty) ck
    | Cbinop:
        forall op e1 e2 ck ty,
          wc_lexp e1 ck ->
          wc_lexp e2 ck ->
          wc_lexp (Ebinop op e1 e2 ty) ck.

    Inductive wc_cexp : cexp -> clock -> Prop :=
    | Cmerge:
        forall x t f ck,
          In (x, ck) vars ->
          wc_cexp t (Con ck x true) ->
          wc_cexp f (Con ck x false) ->
          wc_cexp (Emerge x t f) ck
    | Cite:
        forall b t f ck,
          wc_lexp b ck ->
          wc_cexp t ck ->
          wc_cexp f ck ->
          wc_cexp (Eite b t f) ck
    | Cexp:
        forall e ck,
          wc_lexp e ck ->
          wc_cexp (Eexp e) ck.

    Inductive wc_equation : equation -> Prop :=
    | CEqDef:
        forall x ck ce,
          In (x, ck) vars ->
          wc_cexp ce ck ->
          wc_equation (EqDef x ck ce)
    | CEqApp:
        forall xs ck f les,
          Forall (fun x=>In (x, ck) vars) xs ->
          Forall (fun le => wc_lexp le ck) les ->
          wc_equation (EqApp xs ck f les)
    | CEqFby:
        forall x ck v0 le,
          In (x, ck) vars ->
          wc_lexp le ck ->
          wc_equation (EqFby x ck v0 le).

  End WellClocked.

  Definition wc_env vars : Prop :=
    Forall (fun xck => wc_clock vars (snd xck)) vars.

  Inductive wc_node : node -> Prop :=
  | SNode:
      forall n,
        wc_env (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
        Forall (wc_equation (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))))
                                                                    n.(n_eqs) ->
        Forall (fun xtc=> dck xtc = Cbase) n.(n_in) ->
        Forall (fun xtc=> dck xtc = Cbase) n.(n_out) ->
        wc_node n.

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

  Lemma wc_env_var:
    forall vars x ck,
      wc_env vars
      -> In (x, ck) vars
      -> wc_clock vars ck.
  Proof.
    intros vars x ck Hwc Hcv.
    now apply In_Forall with (2:=Hcv) in Hwc.
  Qed.

  Lemma wc_clock_lexp:
    forall vars le ck,
      wc_env vars
      -> wc_lexp vars le ck
      -> wc_clock vars ck.
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
    forall vars ce ck,
      wc_env vars
      -> wc_cexp vars ce ck
      -> wc_clock vars ck.
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
    forall vars ck x b,
      wc_env vars
      -> wc_clock vars (Con ck x b)
      -> In (x, ck) vars.
  Proof.
    intros vars ck x b Hwc Hclock.
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
