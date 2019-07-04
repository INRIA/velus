From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import Stc.StcIsLast.
From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsDefined.
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
       (Import CESyn : CESYNTAX          Op)
       (Import Syn   : STCSYNTAX     Ids Op CESyn)
       (Import Last  : STCISLAST     Ids Op CESyn Syn)
       (Import Var   : STCISVARIABLE Ids Op CESyn Syn)
       (Import Def   : STCISDEFINED  Ids Op CESyn Syn Var Last)
       (Import Syst  : STCISSYSTEM   Ids Op CESyn Syn)
       (Import Ord   : STCORDERED    Ids Op CESyn Syn Syst)
       (Import CEClo : CECLOCKING    Ids Op CESyn).

  Inductive wc_trconstr (P: program) (vars: list (ident * clock)): trconstr -> Prop :=
  | CTcDef:
      forall x ck e,
        In (x, ck) vars ->
        wc_cexp vars e ck ->
        wc_trconstr P vars (TcDef x ck e)
  | CTcFby:
      forall x ck e,
        In (x, ck) vars ->
        wc_exp vars e ck ->
        wc_trconstr P vars (TcNext x ck e)
  | CTcReset:
      forall i ck f,
        wc_clock vars ck ->
        wc_trconstr P vars (TcReset i ck f)
  | CTcApp:
      forall i xs ck rst f es s P',
          find_system f P = Some (s, P') ->
          (exists isub osub,
              Forall2 (fun xtc le => subvar_eq (isub (fst xtc)) le
                                  /\ (exists lck, wc_exp vars le lck
                                            /\ instck ck isub (dck xtc) = Some lck))
                      s.(s_in) es
              /\ Forall2 (fun xtc x => orelse isub osub (fst xtc) = Some x
                                   /\ (exists xck, In (x, xck) vars
                                             /\ instck ck (orelse isub osub)
                                                      (dck xtc) = Some xck))
                        s.(s_out) xs
              /\ (forall x, ~InMembers x s.(s_out) -> osub x = None)) ->
        wc_trconstr P vars (TcCall i xs ck rst f es).

  Definition wc_system (P: program) (s: system) : Prop :=
    wc_env (idck (s.(s_in))) /\
    wc_env (idck (s.(s_in) ++ s.(s_out))) /\
    wc_env (idck (s.(s_in) ++ s.(s_vars) ++ s.(s_out)) ++ idck s.(s_lasts)) /\
    Forall (wc_trconstr P (idck (s.(s_in) ++ s.(s_vars) ++ s.(s_out)) ++ idck s.(s_lasts)))
           s.(s_tcs).

  Inductive wc_program : program -> Prop :=
  | wc_global_nil:
      wc_program nil
  | wc_global_cons:
      forall b P,
      wc_program P ->
      wc_system P b ->
      wc_program (b :: P).

  Inductive Has_clock_tc: clock -> trconstr -> Prop :=
  | HcTcDef:
      forall x ck e,
        Has_clock_tc ck (TcDef x ck e)
  | HcTcNext:
      forall x ck e,
        Has_clock_tc ck (TcNext x ck e)
  | HcTcReset:
      forall s ck f,
      Has_clock_tc ck (TcReset s ck f)
  | HcTcCall:
      forall s xs ck rst f es,
      Has_clock_tc ck (TcCall s xs ck rst f es).

  Hint Constructors wc_clock wc_exp wc_cexp wc_trconstr wc_program.
  Hint Unfold wc_env wc_system.
  Hint Resolve Forall_nil.

  Instance wc_trconstr_Proper:
    Proper (@eq program ==> @Permutation (ident * clock) ==> @eq trconstr ==> iff)
           wc_trconstr.
  Proof.
    intros ??? env1 env2 Henv eq1 eq2 Htc; subst.
    split; intro WTtc.
    - inv WTtc; try rewrite Henv in *; eauto.
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
    - inv WTtc; try rewrite <-Henv in *; eauto with nlclocking.
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
  Qed.

  Lemma wc_program_app_weaken:
    forall P P',
      wc_program (P' ++ P) ->
      wc_program P.
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
    intros * WCG Hfind.
    apply find_system_app in Hfind as (?&?&?); subst.
    apply wc_program_app_weaken in WCG.
    inversion_clear WCG; auto.
  Qed.

  Lemma wc_trconstr_program_cons:
    forall vars b P tc,
      Ordered_systems (b :: P) ->
      wc_trconstr P vars tc ->
      wc_trconstr (b :: P) vars tc.
  Proof.
    intros * OnG WCnG.
    inversion_clear OnG as [|? ? OG ? HndG].
    inversion_clear WCnG as [| | |???????? Find]; eauto using wc_trconstr.
    econstructor; eauto.
    rewrite find_system_other; eauto.
    intro; subst.
    pose proof Find as Find'; apply find_system_name in Find'.
    eapply find_system_In, Forall_forall in Find; eauto.
    congruence.
  Qed.

  Lemma wc_trconstr_program_app:
    forall vars P' P tc,
      Ordered_systems (P' ++ P) ->
      wc_trconstr P vars tc ->
      wc_trconstr (P' ++ P) vars tc.
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
    intros * OG WCG Hfind.
    induction P as [|b' P IH]; try discriminate.
    simpl in *.
    destruct (ident_eqb b'.(s_name) f) eqn:Heq.
    - inv Hfind. inversion_clear WCG as [|? ? WCG' (WCi & WCo & WCv & WCtcs)].
      constructor; repeat (try split; auto).
      apply Forall_impl_In with (2:=WCtcs).
      intros. apply wc_trconstr_program_cons; auto.
    - assert (OG' := OG).
      inversion_clear OG as [|? ? OG'' ? ?].
      inversion_clear WCG as [|? ? WCG'].
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

    Lemma wc_trconstr_not_Is_free_in_clock:
      forall tc x ck,
        wc_trconstr P vars tc ->
        Is_defined_in_tc x tc ->
        Has_clock_tc ck tc ->
        ~ Is_free_in_clock x ck.
    Proof.
      intros tc x' ck' Hwce Hdef Hhasck Hfree.
      inversion Hwce as [??? Hin|??? Hin| |?????? b P' Hfind
                                                  (isub & osub & Hisub & Hosub & Hnos)];
        clear Hwce; subst; inv Hdef; inv Hhasck.
      - pose proof (wc_env_var _ _ _ Hwc Hin) as Hclock.
        apply Is_free_in_clock_self_or_parent in Hfree as (ck' & b & [Hck|Hck]).
        + subst.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          eapply NoDupMembers_det with (2 := Hin) in Hclock; eauto.
          eapply clock_no_loops; eauto.
        + apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          eapply NoDupMembers_det with (2 := Hin) in Hclock; eauto; subst.
          apply clock_parent_parent' in Hck.
          eapply clock_parent_not_refl; eauto.
      - pose proof (wc_env_var _ _ _ Hwc Hin) as Hclock.
        apply Is_free_in_clock_self_or_parent in Hfree as (ck' & b & [Hck|Hck]).
        + subst.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          eapply NoDupMembers_det with (2 := Hin) in Hclock; eauto.
          eapply clock_no_loops; eauto.
        + apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
           eapply NoDupMembers_det with (2 := Hin) in Hclock; eauto; subst.
          apply clock_parent_parent' in Hck.
          eapply clock_parent_not_refl; eauto.
      - rename x' into x.
        match goal with H:List.In x xs |- _ => rename H into Hin end.
        destruct (Forall2_in_right _ _ _ _ Hosub Hin)
          as (o & Ho & (Hxtc & xck & Hxck & Hxi)).
        pose proof (wc_env_var _ _ _ Hwc Hxck) as Hclock.
        apply Is_free_in_clock_self_or_parent in Hfree.
        apply instck_parent in Hxi.
        destruct Hxi as [Hxi|Hxi]; destruct Hfree as (ck' & bb & [Hck|Hck]).
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
          apply clock_parent_not_refl with (1:=Hxi).    Qed.

    Corollary wc_TcDef_not_Is_free_in_clock:
      forall x ce ck,
        wc_trconstr P vars (TcDef x ck ce) ->
        ~ Is_free_in_clock x ck.
    Proof.
      intros; eapply wc_trconstr_not_Is_free_in_clock;
        eauto using Has_clock_tc, Is_defined_in_tc.
    Qed.

    Corollary wc_TcNext_not_Is_free_in_clock:
      forall x le ck,
        wc_trconstr P vars (TcNext x ck le) ->
        ~ Is_free_in_clock x ck.
    Proof.
      intros; eapply wc_trconstr_not_Is_free_in_clock;
        eauto using Has_clock_tc, Is_defined_in_tc.
    Qed.

    Corollary wc_TcCall_not_Is_free_in_clock:
      forall s xs rst f es ck,
        wc_trconstr P vars (TcCall s xs ck rst f es) ->
        forall x, In x xs -> ~ Is_free_in_clock x ck.
    Proof.
      intros; eapply wc_trconstr_not_Is_free_in_clock;
        eauto using Is_defined_in_tc, Has_clock_tc.
    Qed.

  End Well_clocked.

End STCCLOCKING.

Module StcClockingFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX         Op)
       (Import Syn   : STCSYNTAX     Ids Op CESyn)
       (Import Last  : STCISLAST     Ids Op CESyn Syn)
       (Import Var   : STCISVARIABLE Ids Op CESyn Syn)
       (Import Def   : STCISDEFINED  Ids Op CESyn Syn Var Last)
       (Import Syst : STCISSYSTEM    Ids Op CESyn Syn)
       (Import Ord   : STCORDERED    Ids Op CESyn Syn Syst)
       (Import CEClo : CECLOCKING   Ids Op CESyn)
  <: STCCLOCKING Ids Op CESyn Syn Last Var Def Syst Ord CEClo.
  Include STCCLOCKING Ids Op CESyn Syn Last Var Def Syst Ord CEClo.
End StcClockingFun.
