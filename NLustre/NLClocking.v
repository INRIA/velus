Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.IsFree.
Require Import Velus.NLustre.Memories.
Require Import Velus.NLustre.IsDefined.
Require Import Velus.NLustre.Ordered.
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
       (Import Ord     : ORDERED   Ids Op Clks ExprSyn Syn)
       (Import Mem     : MEMORIES  Ids Op Clks ExprSyn Syn)
       (Import IsD     : ISDEFINED Ids Op Clks ExprSyn Syn Mem)
       (Import IsF     : ISFREE    Ids Op Clks ExprSyn Syn).

  Section WellClocked.

    Variable G    : global.
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

    Inductive wc_equation : equation -> Prop :=
    | CEqDef:
        forall x ck ce,
          In (x, ck) vars ->
          wc_cexp ce ck ->
          wc_equation (EqDef x ck ce)
    | CEqApp:
        forall xs ck f les r n,
          find_node f G = Some n ->
          (exists isub osub,
              Forall2 (fun xtc le => subvar_eq (isub (fst xtc)) le
                                  /\ (exists lck, wc_lexp le lck
                                            /\ instck ck isub (dck xtc) = Some lck))
                      n.(n_in) les
              /\ Forall2 (fun xtc x => orelse isub osub (fst xtc) = Some x
                                   /\ (exists xck, In (x, xck) vars
                                             /\ instck ck (orelse isub osub)
                                                      (dck xtc) = Some xck))
                        n.(n_out) xs
              /\ (forall x, ~InMembers x n.(n_out) -> osub x = None)) ->
          (forall y, r = Some y -> In (y, ck) vars) ->
          wc_equation (EqApp xs ck f les r)
    | CEqFby:
        forall x ck v0 le,
          In (x, ck) vars ->
          wc_lexp le ck ->
          wc_equation (EqFby x ck v0 le).

  End WellClocked.

  Definition wc_node (G: global) (n: node) : Prop :=
    wc_env (idck (n.(n_in))) /\
    wc_env (idck (n.(n_in) ++ n.(n_out))) /\
    wc_env (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) /\
    Forall (wc_equation G (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))))
           n.(n_eqs).

  Inductive wc_global : global -> Prop :=
  | wc_global_nil:
      wc_global nil
  | wc_global_cons: forall n ns,
      wc_global ns ->
      wc_node ns n ->
      wc_global (n::ns).

  Inductive Has_clock_eq: clock -> equation -> Prop :=
  | HcEqDef: forall x ck ce,
      Has_clock_eq ck (EqDef x ck ce)
  | HcEqApp: forall x f ck les r,
      Has_clock_eq ck (EqApp x ck f les r)
  | HcEqFby: forall x v0 ck le,
      Has_clock_eq ck (EqFby x ck v0 le).

  (** ** Basic properties of clocking *)

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

  Hint Constructors wc_clock wc_lexp wc_cexp wc_equation wc_global : nlclocking.
  Hint Unfold wc_env wc_node : nlclocking.
  Hint Resolve Forall_nil : nlclocking.

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
    Proper (@eq global ==> @Permutation (ident * clock) ==> @eq equation ==> iff)
           wc_equation.
  Proof.
    intros G1 G2 Hg env1 env2 Henv eq1 eq2 Heq.
    rewrite Heq, Hg; clear Heq Hg.
    split; intro WTeq.
    - inv WTeq; try rewrite Henv in *; eauto with nlclocking.
      match goal with H: exists isub osub, _ |- _ =>
        destruct H as (isub & osub & Hin & Hout & Hnos) end.
      econstructor; eauto.
      + exists isub, osub; repeat split; auto.
        * apply Forall2_impl_In with (2:=Hin).
          destruct 3 as (lck & Hwc & Hi).
          rewrite Henv in *. eauto.
        * apply Forall2_impl_In with (2:=Hout).
          destruct 3 as (lck & Hwc & Hi).
          rewrite Henv in *. eauto.
      + now setoid_rewrite <-Henv.
    - inv WTeq; try rewrite <-Henv in *; eauto with nlclocking.
      match goal with H: exists isub osub, _ |- _ =>
        destruct H as (isub & osub & Hin & Hout & Hnos) end.
      econstructor; eauto.
      + exists isub, osub; repeat split; auto.
        * apply Forall2_impl_In with (2:=Hin).
          destruct 3 as (lck & Hwc & Hi).
          rewrite <-Henv in *. eauto.
        * apply Forall2_impl_In with (2:=Hout).
          destruct 3 as (lck & Hwc & Hi).
          rewrite <-Henv in *. eauto.
      + now setoid_rewrite Henv.
  Qed.

  Lemma wc_global_app_weaken:
    forall G G',
      wc_global (G' ++ G) ->
      wc_global G.
  Proof.
    induction G'; auto.
    inversion_clear 1. auto.
  Qed.

  Lemma wc_find_node:
    forall G f node,
      wc_global G ->
      find_node f G = Some node ->
      exists G'' G',
        G = G'' ++ node :: G' /\ wc_node G' node.
  Proof.
    intros ** WCG Hfind.
    apply find_node_split in Hfind as (G'' & G' & HG).
    rewrite HG in *.
    apply wc_global_app_weaken in WCG.
    inversion_clear WCG. eauto.
  Qed.

  Lemma wc_equation_global_cons:
    forall vars nd G eq,
      Ordered_nodes (nd :: G) ->
      wc_equation G vars eq ->
      wc_equation (nd :: G) vars eq.
  Proof.
    intros ** OnG WCnG.
    inversion_clear OnG as [|? ? OG ? HndG].
    inversion_clear WCnG; eauto using wc_equation.
    econstructor; eauto.
    simpl. destruct (ident_eqb nd.(n_name) f) eqn:Hf; auto.
    apply ident_eqb_eq in Hf.
    rewrite Hf in *.
    assert (find_node f G <> None) as Hfind by congruence.
    apply find_node_Exists in Hfind.
    apply decidable_Exists_not_Forall in Hfind.
    - contradiction.
    - auto using decidable_eq_ident.
  Qed.

  Lemma wc_equation_global_app:
    forall vars G' G eq,
      Ordered_nodes (G' ++ G) ->
      wc_equation G vars eq ->
      wc_equation (G' ++ G) vars eq.
  Proof.
    induction G'; auto.
    simpl. intros ** OG WCeq.
    eapply wc_equation_global_cons in OG; eauto.
    inv OG. auto.
  Qed.

  Lemma wc_find_node':
    forall G f node,
      Ordered_nodes G ->
      wc_global G ->
      find_node f G = Some node ->
      wc_node G node.
  Proof.
    intros ** OG WCG Hfind.
    induction G as [|n' G IH]. discriminate.
    simpl in *.
    destruct (ident_eqb n'.(n_name) f) eqn:Heq.
    - inv Hfind. inversion_clear WCG as [|? ? WCG' (WCi & WCo & WCv & WCeqs)].
      constructor; repeat (try split; auto).
      apply Forall_impl_In with (2:=WCeqs).
      intros. apply wc_equation_global_cons; auto.
    - assert (OG' := OG).
      inversion_clear OG as [|? ? OG'' ? ?].
      inversion_clear WCG as [|? ? WCG'].
      specialize (IH OG'' WCG' Hfind).
      destruct IH as (WCi & WCo & WCv & WCeqs).
      repeat (try split; auto).
      apply Forall_impl_In with (2:=WCeqs).
      intros. apply wc_equation_global_cons; auto.
  Qed.

  (** Properties *)

  Section Well_clocked.

    (** We work under a (valid) clocking environment *)
    Variable G : global.
    Variable vars : list (ident * clock).
    Variable Hnd : NoDupMembers vars.
    Variable Hwc : wc_env vars.

    Lemma wc_equation_not_Is_free_in_clock:
      forall eq x ck,
        wc_equation G vars eq
        -> Is_defined_in_eq x eq
        -> Has_clock_eq ck eq
        -> ~Is_free_in_clock x ck.
    Proof.
      intros eq x' ck' Hwce Hdef Hhasck Hfree.
      inversion Hwce as [x ck e Hcv Hexp Heq
                        |xs ck f e r n Hfind HH Heq
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
        destruct HH as (isub & osub & Hisub & Hosub & Hnos).
        destruct (Forall2_in_right _ _ _ _ Hosub Hin)
          as (o & Ho & (Hxeq & xck & Hxck & Hxi)).
        pose proof (wc_env_var _ _ _ Hwc Hxck) as Hclock.
        apply Is_free_in_clock_self_or_parent in Hfree.
        apply instck_parent in Hxi.
        destruct Hxi as [Hxi|Hxi]; destruct Hfree as (ck' & b & [Hck|Hck]).
        + subst ck xck.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          pose proof (NoDupMembers_det _ _ _ _ Hnd Hxck Hclock) as Hloop.
          apply clock_no_loops with (1:=Hloop).
        + subst ck.
          apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          rewrite (NoDupMembers_det _ _ _ _ Hnd Hxck Hclock) in *.
          apply clock_parent_parent' in Hck.
          apply clock_parent_not_refl with (1:=Hck).
        + subst ck.
          apply wc_clock_parent with (1:=Hwc) (2:=Hxi) in Hclock.
          apply clock_parent_parent' in Hxi.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          rewrite (NoDupMembers_det _ _ _ _ Hnd Hxck Hclock) in *.
          apply clock_parent_not_refl with (1:=Hxi).
        + apply wc_clock_parent with (1:=Hwc) (2:=Hxi) in Hclock.
          apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          rewrite (NoDupMembers_det _ _ _ _ Hnd Hxck Hclock) in *.
          apply clock_parent_parent' in Hck.
          apply clock_parent_trans with (1:=Hck) in Hxi.
          apply clock_parent_not_refl with (1:=Hxi).
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
        wc_equation G vars (EqDef x ck ce)
        -> ~Is_free_in_clock x ck.
    Proof.
      intros x ce ck Hwce Hwt.
      now eapply wc_equation_not_Is_free_in_clock;
        eauto using Has_clock_eq.
    Qed.

    Corollary wc_EqApp_not_Is_free_in_clock:
      forall xs f le r ck,
        wc_equation G vars (EqApp xs ck f le r)
        -> forall x, List.In x xs -> ~Is_free_in_clock x ck.
    Proof.
      intros x f le ck Hwce Hwt y Hinx.
      now eapply wc_equation_not_Is_free_in_clock;
        eauto using Is_defined_in_eq, Has_clock_eq.
    Qed.

    Corollary wc_EqFby_not_Is_free_in_clock:
      forall x v0 le ck,
        wc_equation G vars (EqFby x ck v0 le)
        -> ~Is_free_in_clock x ck.
    Proof.
      intros x v0 le ck Hwce Hwt.
      now eapply wc_equation_not_Is_free_in_clock;
        eauto using Has_clock_eq.
    Qed.

  End Well_clocked.

End NLCLOCKING.

Module NLClockingFun
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import Clks    : CLOCKS    Ids)
       (Import ExprSyn : NLEXPRSYNTAX  Op)
       (Import Syn     : NLSYNTAX  Ids Op Clks ExprSyn)
       (Import Ord     : ORDERED   Ids Op Clks ExprSyn Syn)
       (Import Mem     : MEMORIES  Ids Op Clks ExprSyn Syn)
       (Import IsD     : ISDEFINED Ids Op Clks ExprSyn Syn Mem)
       (Import IsF     : ISFREE    Ids Op Clks ExprSyn Syn)
  <: NLCLOCKING Ids Op Clks ExprSyn Syn Ord Mem IsD IsF.
  Include NLCLOCKING Ids Op Clks ExprSyn Syn Ord Mem IsD IsF.
End NLClockingFun.
