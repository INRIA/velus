From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import Stc.StcIsReset.
From Velus Require Import Stc.StcIsNext.
From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsSystem.
From Velus Require Import Stc.StcOrdered.

From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import Permutation.

(** * Well clocked programs *)

(**

This family of predicates states that a program is well-clocked
wrt. its clock annotations.

 *)

Module Type STCCLOCKING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX     Ids Op OpAux Cks CESyn)
       (Import Reset : STCISRESET    Ids Op OpAux Cks CESyn Syn)
       (Import Var   : STCISVARIABLE Ids Op OpAux Cks CESyn Syn)
       (Import Syst  : STCISSYSTEM   Ids Op OpAux Cks CESyn Syn)
       (Import Ord   : STCORDERED    Ids Op OpAux Cks CESyn Syn Syst)
       (Import CEClo : CECLOCKING    Ids Op OpAux Cks CESyn).

  Inductive wc_trconstr (P: program) (vars: list (ident * clock)): trconstr -> Prop :=
  | CTcDef:
      forall x ck e,
        In (x, ck) vars ->
        wc_cexp vars e ck ->
        wc_trconstr P vars (TcDef x ck e)
  | CTcReset:
      forall x ck ckr ty c0,
        In (x, ck) vars ->
        wc_clock vars ckr ->
        wc_trconstr P vars (TcReset x ckr ty c0)
  | CTcNext:
      forall x ck ckrs e,
        In (x, ck) vars ->
        wc_exp vars e ck ->
        wc_trconstr P vars (TcNext x ck ckrs e)
  | CTcIReset:
      forall i ck f,
        wc_clock vars ck ->
        wc_trconstr P vars (TcInstReset i ck f)
  | CTcApp:
      forall i xs ck rst f es s P' sub,
        find_system f P = Some (s, P') ->
        Forall2 (fun '(x, (_, xck)) le =>
                   SameVar (sub x) le
                   /\ exists lck, wc_exp vars le lck
                            /\ instck ck sub xck = Some lck)
                s.(s_in) es ->
        Forall2 (fun '(y, (_, yck)) x =>
                   sub y = Some x
                   /\ exists xck, In (x, xck) vars
                            /\ instck ck sub yck = Some xck)
                s.(s_out) xs ->
        wc_trconstr P vars (TcStep i xs ck rst f es).

  Definition wc_system (P: program) (s: system) : Prop :=
    wc_env (idck (s.(s_in))) /\
    wc_env (idck (s.(s_in) ++ s.(s_out))) /\
    wc_env (idck (s.(s_in) ++ s.(s_vars) ++ s.(s_out)) ++ idck s.(s_nexts)) /\
    Forall (wc_trconstr P (idck (s.(s_in) ++ s.(s_vars) ++ s.(s_out)) ++ idck s.(s_nexts)))
           s.(s_tcs).

  Definition wc_program (P: program) :=
    Forall' (fun P' => wc_system (Program P.(enums) P')) P.(systems).

  Inductive Has_clock_tc: clock -> trconstr -> Prop :=
  | HcTcDef:
      forall x ck e,
        Has_clock_tc ck (TcDef x ck e)
  | HcTcReset:
      forall x ckr ty c0,
        Has_clock_tc ckr (TcReset x ckr ty c0)
  | HcTcNext:
      forall x ck ckrs e,
        Has_clock_tc ck (TcNext x ck ckrs e)
  | HcTcIReset:
      forall s ck f,
        Has_clock_tc ck (TcInstReset s ck f)
  | HcTcStep:
      forall s xs ck ckrs f es,
        Has_clock_tc ck (TcStep s xs ck ckrs f es).

  Hint Constructors wc_clock wc_exp wc_cexp wc_trconstr.
  Hint Unfold wc_env wc_system.
  Hint Resolve Forall_nil.

  Instance wc_trconstr_Proper:
    Proper (@eq program ==> @Permutation (ident * clock) ==> @eq trconstr ==> iff)
           wc_trconstr.
  Proof.
    intros ??? env1 env2 Henv eq1 eq2 Htc; subst.
    split; intro WTtc.
    - inv WTtc; try rewrite Henv in *; eauto.
      econstructor; eauto.
      + eapply Forall2_impl_In; eauto.
        intros (?&(?&?)) ??? (?&?&?).
        rewrite Henv in *; eauto.
      + eapply Forall2_impl_In; eauto.
        intros (?&(?&?)) ??? (?&?&?).
        rewrite Henv in *; eauto.
    - inv WTtc; try rewrite <-Henv in *; eauto with nlclocking.
      econstructor; eauto.
      + eapply Forall2_impl_In; eauto.
        intros (?&(?&?)) ??? (?&?&?).
        rewrite <-Henv in *; eauto.
      + eapply Forall2_impl_In; eauto.
        intros (?&(?&?)) ??? (?&?&?).
        rewrite <-Henv in *; eauto.
  Qed.

  Lemma wc_program_app_weaken:
    forall P P' enums,
      wc_program (Program enums (P' ++ P)) ->
      wc_program (Program enums P).
  Proof.
    induction P'; auto.
    inversion_clear 1; auto.
  Qed.

  Lemma wc_find_system:
    forall P f b P',
      wc_program P ->
      find_system f P = Some (b, P') ->
      wc_system P' b.
  Proof.
    intros (enumsP &P) * WCG Hfind.
    assert (enumsP = enums P')
      by (apply find_unit_equiv_program in Hfind; specialize (Hfind nil); inv Hfind; auto).
    apply find_unit_spec in Hfind as (?&?&?&?); simpl in *; subst.
    apply wc_program_app_weaken in WCG.
    inversion_clear WCG; destruct P'; auto.
  Qed.

  Lemma wc_trconstr_program_cons:
    forall vars b P tc enums,
      Ordered_systems (Program enums (b :: P)) ->
      wc_trconstr (Program enums P) vars tc ->
      wc_trconstr (Program enums (b :: P)) vars tc.
  Proof.
    intros * OnG WCnG.
    inversion_clear OnG as [|?? []].
    inversion_clear WCnG as [| | | |????????? Find]; eauto using wc_trconstr.
    econstructor; eauto.
    rewrite find_system_other; eauto.
    intro; subst.
    apply find_unit_In in Find as (?& Hin).
    eapply Forall_forall in Hin; eauto; simpl in *; congruence.
  Qed.

  Lemma wc_trconstr_program_app:
    forall vars P' P tc enums,
      Ordered_systems (Program enums (P' ++ P)) ->
      wc_trconstr (Program enums P) vars tc ->
      wc_trconstr (Program enums (P' ++ P)) vars tc.
  Proof.
    induction P'; auto.
    simpl. intros * OG WCtc.
    eapply wc_trconstr_program_cons in OG; eauto.
    inv OG. auto.
  Qed.

  Lemma wc_find_system':
    forall P f b P',
      Ordered_systems P ->
      wc_program P ->
      find_system f P = Some (b, P') ->
      wc_system P b.
  Proof.
    intros (?& P) * OG WCG Hfind.
    induction P as [|b' P IH]; try discriminate.
    eapply find_unit_cons in Hfind as [[E Hfind]|[E Hfind]]; simpl; eauto.
    - inv Hfind. inversion WCG as [|?? (WCi & WCo & WCv & WCtcs) WCG']; subst.
      constructor; repeat (try split; auto).
      apply Forall_impl_In with (2:=WCtcs).
      intros. apply wc_trconstr_program_cons; auto.
    - assert (OG' := OG).
      inversion_clear OG as [|?? [] OG''].
      inversion_clear WCG as [|??? WCG'].
      specialize (IH OG'' WCG' Hfind).
      destruct IH as (WCi & WCo & WCv & WCtcs).
      repeat (try split; auto).
      apply Forall_impl_In with (2:=WCtcs).
      intros. apply wc_trconstr_program_cons; auto.
  Qed.

  (** Properties *)

  Section Well_clocked.

    (** We work under a (valid) clocking environment *)
    Variable P : program.
    Variable vars : list (ident * clock).
    Variable Hnd : NoDupMembers vars.
    Variable Hwc : wc_env vars.

    Corollary wc_TcDef_not_Is_free_in_clock:
      forall x ce ck,
        wc_trconstr P vars (TcDef x ck ce) ->
        ~ Is_free_in_clock x ck.
    Proof.
      intros * Hwctr Hfree.
      inversion_clear Hwctr as [??? Hin| | | |].
      pose proof (wc_env_var _ _ _ Hwc Hin) as Hclock.
      apply Is_free_in_clock_self_or_parent in Hfree as (ck' & b & [Hck|Hck]).
      - subst.
        apply wc_clock_sub with (1:=Hwc) in Hclock.
        eapply NoDupMembers_det with (2 := Hin) in Hclock; eauto.
        eapply clock_no_loops; eauto.
      - apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
        apply wc_clock_sub with (1:=Hwc) in Hclock.
        eapply NoDupMembers_det with (2 := Hin) in Hclock; eauto; subst.
        apply clock_parent_parent' in Hck.
        eapply clock_parent_not_refl; eauto.
    Qed.

    Lemma wc_TcNext_not_Is_free_in_clock:
      forall x ck ckrs le,
        wc_trconstr P vars (TcNext x ck ckrs le) ->
        ~ Is_free_in_clock x ck.
    Proof.
      intros * Hwctr Hfree.
      inversion_clear Hwctr as [| |???? Hin He| |].
      pose proof (wc_env_var _ _ _ Hwc Hin) as Hclock.
      apply Is_free_in_clock_self_or_parent in Hfree as (ck' & b & [Hck|Hck]).
      - subst.
        apply wc_clock_sub with (1:=Hwc) in Hclock.
        eapply NoDupMembers_det with (2 := Hin) in Hclock; eauto.
        eapply clock_no_loops; eauto.
      - apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
        apply wc_clock_sub with (1:=Hwc) in Hclock.
        eapply NoDupMembers_det with (2 := Hin) in Hclock; eauto; subst.
        apply clock_parent_parent' in Hck.
        eapply clock_parent_not_refl; eauto.
    Qed.

    Corollary wc_TcStep_not_Is_free_in_clock:
      forall s xs rst f es ck,
        wc_trconstr P vars (TcStep s xs ck rst f es) ->
        forall x, In x xs -> ~ Is_free_in_clock x ck.
    Proof.
      intros * Hwctr ? Hin Hfree.
      inversion_clear Hwctr as [| | | |?????? b P' sub Hfind Hisub Hosub].
      match goal with H:List.In x xs |- _ => rename H into Hin end.
      destruct (Forall2_in_right _ _ _ _ Hosub Hin) as ((?&(?&?)) & Ho & Hxtc & xck & Hxck & Hxi).
      pose proof (wc_env_var _ _ _ Hwc Hxck) as Hclock.
      apply Is_free_in_clock_self_or_parent in Hfree.
      apply instck_parent in Hxi.
      destruct Hxi as [Hxi|Hxi]; destruct Hfree as (ck' & bb & [Hck|Hck]).
      - subst ck xck.
        apply wc_clock_sub with (1:=Hwc) in Hclock.
        pose proof (NoDupMembers_det _ _ _ _ Hnd Hxck Hclock) as Hloop.
        apply clock_no_loops with (1:=Hloop).
      - subst ck.
        apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
        apply wc_clock_sub with (1:=Hwc) in Hclock.
        rewrite (NoDupMembers_det _ _ _ _ Hnd Hxck Hclock) in *.
        apply clock_parent_parent' in Hck.
        apply clock_parent_not_refl with (1:=Hck).
      - subst ck.
        apply wc_clock_parent with (1:=Hwc) (2:=Hxi) in Hclock.
        apply clock_parent_parent' in Hxi.
        apply wc_clock_sub with (1:=Hwc) in Hclock.
        rewrite (NoDupMembers_det _ _ _ _ Hnd Hxck Hclock) in *.
        apply clock_parent_not_refl with (1:=Hxi).
      - apply wc_clock_parent with (1:=Hwc) (2:=Hxi) in Hclock.
        apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
        apply wc_clock_sub with (1:=Hwc) in Hclock.
        rewrite (NoDupMembers_det _ _ _ _ Hnd Hxck Hclock) in *.
        apply clock_parent_parent' in Hck.
        apply clock_parent_trans with (1:=Hck) in Hxi.
        apply clock_parent_not_refl with (1:=Hxi).
    Qed.

  End Well_clocked.

End STCCLOCKING.

Module StcClockingFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX     Ids Op OpAux Cks CESyn)
       (Import Reset : STCISRESET    Ids Op OpAux Cks CESyn Syn)
       (Import Var   : STCISVARIABLE Ids Op OpAux Cks CESyn Syn)
       (Import Syst  : STCISSYSTEM   Ids Op OpAux Cks CESyn Syn)
       (Import Ord   : STCORDERED    Ids Op OpAux Cks CESyn Syn Syst)
       (Import CEClo : CECLOCKING    Ids Op OpAux Cks CESyn)
  <: STCCLOCKING Ids Op OpAux Cks CESyn Syn Reset Var Syst Ord CEClo.
  Include STCCLOCKING Ids Op OpAux Cks CESyn Syn Reset Var Syst Ord CEClo.
End StcClockingFun.
