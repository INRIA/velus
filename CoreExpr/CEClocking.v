Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.CoreExpr.CESyntax.

Require Import List.
Require Import Morphisms.
Import Permutation.

(** * Well clocked expressions *)

Module Type CECLOCKING
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import Clks : CLOCKS Ids)
       (Import Syn  : CESYNTAX Op).

  (* TODO: move to Common *)
  Definition orelse {A B: Type}
             (f: A -> option B) (g: A -> option B) (x: A) : option B :=
    match f x with
    | None => g x
    | r => r
    end.

  Definition subvar_eq (vo : option ident) (le : lexp) : Prop :=
    match vo with
    | Some v => match le with
               | Evar x _ => v = x
               | _ => False
               end
    | None => True
    end.

  Section WellClocked.

    Variable vars : list (ident * clock).

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

  End WellClocked.

  (** ** Basic properties of clocking *)

  Lemma wc_clock_lexp:
    forall vars le ck,
      wc_env vars ->
      wc_lexp vars le ck ->
      wc_clock vars ck.
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
      wc_env vars ->
      wc_cexp vars ce ck ->
      wc_clock vars ck.
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

  Hint Constructors wc_clock wc_lexp wc_cexp : nlclocking.
  Hint Resolve Forall_nil : nlclocking.

  Instance wc_lexp_Proper:
    Proper (@Permutation (ident * clock) ==> @eq lexp ==> @eq clock ==> iff)
           wc_lexp.
  Proof.
    intros env' env Henv e' e He ck' ck Hck.
    rewrite He, Hck; clear He Hck e' ck'.
    revert ck.
    induction e;
      split; auto with nlclocking;
        inversion_clear 1;
        (rewrite Henv in * || rewrite <-Henv in * || idtac);
        try edestruct IHe;
        try edestruct IHe1, IHe2;
        auto with nlclocking.
  Qed.

  Instance wc_cexp_Proper:
    Proper (@Permutation (ident * clock) ==> @eq cexp ==> @eq clock ==> iff)
           wc_cexp.
  Proof.
    intros env' env Henv e' e He ck' ck Hck.
    rewrite He, Hck; clear He Hck e' ck'.
    revert ck.
    induction e;
      split; inversion_clear 1;
        (rewrite Henv in * || rewrite <-Henv in *);
         constructor; auto;
         now (rewrite <-IHe1 || rewrite IHe1
              || rewrite <-IHe2 || rewrite IHe2).
  Qed.

End CECLOCKING.

Module CEClockingFun
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import Clks : CLOCKS Ids)
       (Import Syn  : CESYNTAX Op)
  <: CECLOCKING Ids Op Clks Syn.
  Include CECLOCKING Ids Op Clks Syn.
End CEClockingFun.
