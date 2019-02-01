Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.IsFree.
Require Import Velus.NLustre.Memories.
Require Import Velus.NLustre.IsDefined.
Require Import List.

(** * Well clocked programs *)

(**

This family of predicates states that a program is well-clocked
wrt. its clock annotations.

 *)

Module Type NLCLOCKING
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import Clks    : CLOCKS    Ids)
       (Import ExprSyn : NLEXPRSYNTAX  Op)
       (Import Syn     : NLSYNTAX  Ids Op Clks ExprSyn)
       (Import Mem     : MEMORIES  Ids Op Clks ExprSyn Syn)
       (Import IsD     : ISDEFINED Ids Op Clks ExprSyn Syn Mem)
       (Import IsF     : ISFREE    Ids Op Clks ExprSyn Syn).

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

    Inductive wc_equation : equation -> Prop :=
    | CEqDef:
        forall x ck ce,
          In (x, ck) vars ->
          wc_cexp ce ck ->
          wc_equation (EqDef x ck ce)
    | CEqApp:
        forall xs ck f les,
          Forall (fun x => In (x, ck) vars) xs ->
          Forall (fun le => wc_lexp le ck) les ->
          wc_equation (EqApp xs ck f les None)
    | CEqReset:
        forall xs ck f les r,
          Forall (fun x => In (x, ck) vars) xs ->
          Forall (fun le => wc_lexp le ck) les ->
          In (r, ck) vars ->
          wc_equation (EqApp xs ck f les (Some r))
    | CEqFby:
        forall x ck v0 le,
          In (x, ck) vars ->
          wc_lexp le ck ->
          wc_equation (EqFby x ck v0 le).

  End WellClocked.

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
  | HcEqApp: forall x f ck les r,
      Has_clock_eq ck (EqApp x ck f les r)
  | HcEqFby: forall x v0 ck le,
      Has_clock_eq ck (EqFby x ck v0 le).

  (** ** Basic properties of clocking *)

  Lemma wc_global_nil: wc_global nil.
  Proof.
    apply Forall_nil.
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

  Hint Constructors wc_clock wc_lexp wc_cexp wc_equation wc_node : nlclocking.
  Hint Unfold wc_env : nlclocking.
  Hint Resolve wc_global_nil Forall_nil : nlclocking.

  Require Import Morphisms.
  Import Permutation.

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

  Instance wc_equation_Proper:
    Proper (@Permutation (ident * clock) ==> @eq equation ==> iff) wc_equation.
  Proof.
    intros env1 env2 Henv eq1 eq2 Heq.
    rewrite Heq; clear Heq.
    split; intro WTeq.
    - inv WTeq; try rewrite Henv in *; eauto with nlclocking;
        constructor; auto;
          match goal with H:Forall _ ?x |- Forall _ ?x =>
                          apply Forall_impl_In with (2:=H) end;
          intros; rewrite Henv in *; auto.
    - inv WTeq; try rewrite <-Henv in *; eauto with nlclocking;
        constructor; auto;
          match goal with H:Forall _ ?x |- Forall _ ?x =>
                          apply Forall_impl_In with (2:=H) end;
          intros; rewrite <-Henv in *; auto.
  Qed.

  (** Properties *)

  Section Well_clocked.

    (** We work under a (valid) clocking environment *)
    Variable vars : list (ident * clock).
    Variable Hnd : NoDupMembers vars.
    Variable Hwc : wc_env vars.

    Lemma wc_equation_not_Is_free_in_clock:
      forall eq x ck,
        wc_equation vars eq
        -> Is_defined_in_eq x eq
        -> Has_clock_eq ck eq
        -> ~Is_free_in_clock x ck.
    Proof.
      intros eq x' ck' Hwce Hdef Hhasck Hfree.
      inversion Hwce as [x ck e Hcv Hexp Heq
                        |xs ck f e Hvars Hexp Heq
                        |xs ck f e r Hvars Hexp Heq
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
      forall xs f le ck r,
        wc_equation vars (EqApp xs ck f le r)
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

End NLCLOCKING.

Module NLClockingFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (Clks    : CLOCKS    Ids)
       (ExprSyn : NLEXPRSYNTAX  Op)
       (Syn     : NLSYNTAX  Ids Op Clks ExprSyn)
       (Mem     : MEMORIES  Ids Op Clks ExprSyn Syn)
       (IsD     : ISDEFINED Ids Op Clks ExprSyn Syn Mem)
       (IsF     : ISFREE    Ids Op Clks ExprSyn Syn)
       <: NLCLOCKING Ids Op Clks ExprSyn Syn Mem IsD IsF.
  Include NLCLOCKING Ids Op Clks ExprSyn Syn Mem IsD IsF.
End NLClockingFun.
