Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.CoreExpr.CEClocking.
Require Import Velus.SyBloc.SBIsLast.
Require Import Velus.SyBloc.SBIsVariable.
Require Import Velus.SyBloc.SBIsDefined.
Require Import Velus.SyBloc.SBIsBlock.
Require Import Velus.SyBloc.SBOrdered.

Require Import List.
Require Import Morphisms.
Import Permutation.

(** * Well clocked programs *)

(**

This family of predicates states that a program is well-clocked
wrt. its clock annotations.

 *)

Module Type SBCLOCKING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX         Op)
       (Import Syn   : SBSYNTAX     Ids Op CESyn)
       (Import Last  : SBISLAST     Ids Op CESyn Syn)
       (Import Var   : SBISVARIABLE Ids Op CESyn Syn)
       (Import Def   : SBISDEFINED  Ids Op CESyn Syn Var Last)
       (Import Block : SBISBLOCK    Ids Op CESyn Syn)
       (Import Ord   : SBORDERED    Ids Op CESyn Syn Block)
       (Import CEClo : CECLOCKING   Ids Op CESyn).


  Inductive wc_equation (P: program) (vars: list (ident * clock)): equation -> Prop :=
  | CEqDef:
      forall x ck e,
        In (x, ck) vars ->
        wc_cexp vars e ck ->
        wc_equation P vars (EqDef x ck e)
  | CEqFby:
      forall x ck e,
        In (x, ck) vars ->
        wc_lexp vars e ck ->
        wc_equation P vars (EqNext x ck e)
  | CEqReset:
      forall s ck f,
        wc_clock vars ck ->
        wc_equation P vars (EqReset s ck f)
  | CEqApp:
      forall s xs ck rst f es b P',
          find_block f P = Some (b, P') ->
          (exists isub osub,
              Forall2 (fun xtc le => subvar_eq (isub (fst xtc)) le
                                  /\ (exists lck, wc_lexp vars le lck
                                            /\ instck ck isub (dck xtc) = Some lck))
                      b.(b_in) es
              /\ Forall2 (fun xtc x => orelse isub osub (fst xtc) = Some x
                                   /\ (exists xck, In (x, xck) vars
                                             /\ instck ck (orelse isub osub)
                                                      (dck xtc) = Some xck))
                        b.(b_out) xs
              /\ (forall x, ~InMembers x b.(b_out) -> osub x = None)) ->
        wc_equation P vars (EqCall s xs ck rst f es).

  Definition wc_block (P: program) (b: block) : Prop :=
    wc_env (idck (b.(b_in))) /\
    wc_env (idck (b.(b_in) ++ b.(b_out))) /\
    wc_env (idck (b.(b_in) ++ b.(b_vars) ++ b.(b_out)) ++ idck b.(b_lasts)) /\
    Forall (wc_equation P (idck (b.(b_in) ++ b.(b_vars) ++ b.(b_out)) ++ idck b.(b_lasts)))
           b.(b_eqs).

  Inductive wc_program : program -> Prop :=
  | wc_global_nil:
      wc_program nil
  | wc_global_cons:
      forall b P,
      wc_program P ->
      wc_block P b ->
      wc_program (b :: P).

  Inductive Has_clock_eq: clock -> equation -> Prop :=
  | HcEqDef:
      forall x ck e,
        Has_clock_eq ck (EqDef x ck e)
  | HcEqNext:
      forall x ck e,
        Has_clock_eq ck (EqNext x ck e)
  | HcEqReset:
      forall s ck f,
      Has_clock_eq ck (EqReset s ck f)
  | HcEqCall:
      forall s xs ck rst f es,
      Has_clock_eq ck (EqCall s xs ck rst f es).

  Hint Constructors wc_clock wc_lexp wc_cexp wc_equation wc_program.
  Hint Unfold wc_env wc_block.
  Hint Resolve Forall_nil.

  Instance wc_equation_Proper:
    Proper (@eq program ==> @Permutation (ident * clock) ==> @eq equation ==> iff)
           wc_equation.
  Proof.
    intros ??? env1 env2 Henv eq1 eq2 Heq; subst.
    split; intro WTeq.
    - inv WTeq; try rewrite Henv in *; eauto.
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
  Qed.

  Lemma wc_program_app_weaken:
    forall P P',
      wc_program (P' ++ P) ->
      wc_program P.
  Proof.
    induction P'; auto.
    inversion_clear 1; auto.
  Qed.

  Lemma wc_find_block:
    forall P f b P',
      wc_program P ->
      find_block f P = Some (b, P') ->
      wc_block P' b.
  Proof.
    intros * WCG Hfind.
    apply find_block_app in Hfind as (?&?&?); subst.
    apply wc_program_app_weaken in WCG.
    inversion_clear WCG; auto.
  Qed.

  Lemma wc_equation_program_cons:
    forall vars b P eq,
      Ordered_blocks (b :: P) ->
      wc_equation P vars eq ->
      wc_equation (b :: P) vars eq.
  Proof.
    intros * OnG WCnG.
    inversion_clear OnG as [|? ? OG ? HndG].
    inversion_clear WCnG as [| | |???????? Find]; eauto using wc_equation.
    econstructor; eauto.
    rewrite find_block_other; eauto.
    intro; subst.
    pose proof Find as Find'; apply find_block_name in Find'.
    eapply find_block_In, Forall_forall in Find; eauto.
    congruence.
  Qed.

  Lemma wc_equation_program_app:
    forall vars P' P eq,
      Ordered_blocks (P' ++ P) ->
      wc_equation P vars eq ->
      wc_equation (P' ++ P) vars eq.
  Proof.
    induction P'; auto.
    simpl. intros * OG WCeq.
    eapply wc_equation_program_cons in OG; eauto.
    inv OG. auto.
  Qed.

  Lemma wc_find_block':
    forall P f b P',
      Ordered_blocks P ->
      wc_program P ->
      find_block f P = Some (b, P') ->
      wc_block P b.
  Proof.
    intros * OG WCG Hfind.
    induction P as [|b' P IH]; try discriminate.
    simpl in *.
    destruct (ident_eqb b'.(b_name) f) eqn:Heq.
    - inv Hfind. inversion_clear WCG as [|? ? WCG' (WCi & WCo & WCv & WCeqs)].
      constructor; repeat (try split; auto).
      apply Forall_impl_In with (2:=WCeqs).
      intros. apply wc_equation_program_cons; auto.
    - assert (OG' := OG).
      inversion_clear OG as [|? ? OG'' ? ?].
      inversion_clear WCG as [|? ? WCG'].
      specialize (IH OG'' WCG' Hfind).
      destruct IH as (WCi & WCo & WCv & WCeqs).
      repeat (try split; auto).
      apply Forall_impl_In with (2:=WCeqs).
      intros. apply wc_equation_program_cons; auto.
  Qed.

  (** Properties *)

  Section Well_clocked.

    (** We work under a (valid) clocking environment *)
    Variable P : program.
    Variable vars : list (ident * clock).
    Variable Hnd : NoDupMembers vars.
    Variable Hwc : wc_env vars.

    Lemma wc_equation_not_Is_free_in_clock:
      forall eq x ck,
        wc_equation P vars eq ->
        Is_defined_in_eq x eq ->
        Has_clock_eq ck eq ->
        ~ Is_free_in_clock x ck.
    Proof.
      intros eq x' ck' Hwce Hdef Hhasck Hfree.
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
          as (o & Ho & (Hxeq & xck & Hxck & Hxi)).
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

    Corollary wc_EqDef_not_Is_free_in_clock:
      forall x ce ck,
        wc_equation P vars (EqDef x ck ce) ->
        ~ Is_free_in_clock x ck.
    Proof.
      intros; eapply wc_equation_not_Is_free_in_clock;
        eauto using Has_clock_eq, Is_defined_in_eq.
    Qed.

    Corollary wc_EqNext_not_Is_free_in_clock:
      forall x le ck,
        wc_equation P vars (EqNext x ck le) ->
        ~ Is_free_in_clock x ck.
    Proof.
      intros; eapply wc_equation_not_Is_free_in_clock;
        eauto using Has_clock_eq, Is_defined_in_eq.
    Qed.

    Corollary wc_EqCall_not_Is_free_in_clock:
      forall s xs rst f es ck,
        wc_equation P vars (EqCall s xs ck rst f es) ->
        forall x, In x xs -> ~ Is_free_in_clock x ck.
    Proof.
      intros; eapply wc_equation_not_Is_free_in_clock;
        eauto using Is_defined_in_eq, Has_clock_eq.
    Qed.

  End Well_clocked.

End SBCLOCKING.

Module SBClockingFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX         Op)
       (Import Syn   : SBSYNTAX     Ids Op CESyn)
       (Import Last  : SBISLAST     Ids Op CESyn Syn)
       (Import Var   : SBISVARIABLE Ids Op CESyn Syn)
       (Import Def   : SBISDEFINED  Ids Op CESyn Syn Var Last)
       (Import Block : SBISBLOCK    Ids Op CESyn Syn)
       (Import Ord   : SBORDERED    Ids Op CESyn Syn Block)
       (Import CEClo : CECLOCKING   Ids Op CESyn)
  <: SBCLOCKING Ids Op CESyn Syn Last Var Def Block Ord CEClo.
  Include SBCLOCKING Ids Op CESyn Syn Last Var Def Block Ord CEClo.
End SBClockingFun.
