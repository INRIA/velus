From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import CoreExpr.CEClocking.

From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import Permutation.

(** * Well clocked programs *)

(**

This family of predicates states that a program is well-clocked
wrt. its clock annotations.

 *)

Module Type NLCLOCKING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX       Op)
       (Import Syn   : NLSYNTAX   Ids Op CESyn)
       (Import Ord   : NLORDERED  Ids Op CESyn Syn)
       (Import Mem   : MEMORIES   Ids Op CESyn Syn)
       (Import IsD   : ISDEFINED  Ids Op CESyn Syn Mem)
       (Import CEIsF : CEISFREE   Ids Op CESyn)
       (Import IsF   : ISFREE     Ids Op CESyn Syn CEIsF)
       (Import CEClo : CECLOCKING Ids Op CESyn).

  Inductive wc_equation (G: global) (vars: list (ident * clock)): equation -> Prop :=
  | CEqDef:
      forall x ck ce,
        In (x, ck) vars ->
        wc_cexp vars ce ck ->
        wc_equation G vars (EqDef x ck ce)
  | CEqApp:
      forall xs ck f les r n sub,
        find_node f G = Some n ->
        Forall2 (fun '(x, (_, xck)) le =>
                   SameVar (sub x) le
                   /\ exists lck, wc_exp vars le lck
                            /\ instck ck sub xck = Some lck)
                n.(n_in) les ->
        Forall2 (fun '(y, (_, yck)) x =>
                   sub y = Some x
                   /\ exists xck, In (x, xck) vars
                            /\ instck ck sub yck = Some xck)
                n.(n_out) xs ->
        (forall yck, r = Some yck -> In yck vars) ->
        wc_equation G vars (EqApp xs ck f les r)
  | CEqFby:
      forall x ck v0 le,
        In (x, ck) vars ->
        wc_exp vars le ck ->
        wc_equation G vars (EqFby x ck v0 le).

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

  Hint Constructors wc_clock wc_exp wc_cexp wc_equation wc_global : nlclocking.
  Hint Unfold wc_env wc_node : nlclocking.
  Hint Resolve Forall_nil : nlclocking.

  Instance wc_equation_Proper:
    Proper (@eq global ==> @Permutation (ident * clock) ==> @eq equation ==> iff)
           wc_equation.
  Proof.
    intros G1 G2 Hg env1 env2 Henv eq1 eq2 Heq.
    rewrite Heq, Hg; clear Heq Hg.
    split; intro WTeq.
    - inv WTeq; try rewrite Henv in *; eauto with nlclocking.
      econstructor; eauto.
      + eapply Forall2_impl_In; eauto.
        intros (?&(?&?)) ??? (?&?&?); simpl.
        rewrite Henv in *; eauto.
      + eapply Forall2_impl_In; eauto.
        intros (?&(?&?)) ??? (?&?&?); simpl.
        rewrite Henv in *; eauto.
      + now setoid_rewrite <-Henv.
    - inv WTeq; try rewrite <-Henv in *; eauto with nlclocking.
      econstructor; eauto.
      + eapply Forall2_impl_In; eauto.
        intros (?&(?&?)) ??? (?&?&?); simpl.
        rewrite <-Henv in *; eauto.
      + eapply Forall2_impl_In; eauto.
        intros (?&(?&?)) ??? (?&?&?); simpl.
        rewrite <-Henv in *; eauto.
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
    intros * WCG Hfind.
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
    intros * OnG WCnG.
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
    simpl. intros * OG WCeq.
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
    intros * OG WCG Hfind.
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
                        |xs ck f e r n sub Hfind Hisub Hosub Heq
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
        destruct (Forall2_in_right _ _ _ _ Hosub Hin)
          as ((?&?&?) & Ho & (Hxeq & xck & Hxck & Hxi)).
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
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX       Op)
       (Import Syn   : NLSYNTAX   Ids Op CESyn)
       (Import Ord   : NLORDERED  Ids Op CESyn Syn)
       (Import Mem   : MEMORIES   Ids Op CESyn Syn)
       (Import IsD   : ISDEFINED  Ids Op CESyn Syn Mem)
       (Import CEIsF : CEISFREE   Ids Op CESyn)
       (Import IsF   : ISFREE     Ids Op CESyn Syn CEIsF)
       (Import CEClo : CECLOCKING Ids Op CESyn)
  <: NLCLOCKING Ids Op CESyn Syn Ord Mem IsD CEIsF IsF CEClo.
  Include NLCLOCKING Ids Op CESyn Syn Ord Mem IsD CEIsF IsF CEClo.
End NLClockingFun.
