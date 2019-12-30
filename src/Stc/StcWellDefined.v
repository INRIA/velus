(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Clocks.

From Velus Require Import Stc.StcIsSystem.
From Velus Require Import Stc.StcOrdered.

From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsInit.
From Velus Require Import Stc.StcIsDefined.

From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import Stc.StcIsFree.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Omega.

Module Type STCWELLDEFINED
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX          Op)
       (Import Syn   : STCSYNTAX     Ids Op CESyn)
       (Import Syst  : STCISSYSTEM   Ids Op CESyn Syn)
       (Import Ord   : STCORDERED    Ids Op CESyn Syn Syst)
       (Import Var   : STCISVARIABLE Ids Op CESyn Syn)
       (Import Init  : STCISINIT     Ids Op CESyn Syn)
       (Import Def   : STCISDEFINED  Ids Op CESyn Syn Var Init)
       (Import CEIsF : CEISFREE      Ids Op CESyn)
       (Import Free  : STCISFREE     Ids Op CESyn Syn CEIsF).

  Inductive Is_well_sch (inputs: list ident) (mems: PS.t): list trconstr -> Prop :=
  | WSchNil:
      Is_well_sch inputs mems []
  | WSchTc:
      forall tc tcs,
        Is_well_sch inputs mems tcs ->
        (forall x,
            Is_free_in_tc x tc ->
            if PS.mem x mems
            then ~ Is_defined_in x tcs
            else Is_variable_in x tcs \/ In x inputs) ->
        (forall s k,
            Is_sub_in_tc s k tc ->
            Forall (fun tc => forall k', Is_sub_in_tc s k' tc -> k' < k) tcs) ->
        Is_well_sch inputs mems (tc :: tcs).

  Definition Well_scheduled: program -> Prop :=
    Forall (fun s => Is_well_sch (map fst (s_in s)) (ps_from_list (map fst (s_inits s))) (s_tcs s)).

  Lemma Is_well_sch_app:
    forall inputs mems tcs tcs',
      Is_well_sch inputs mems (tcs ++ tcs') ->
      Is_well_sch inputs mems tcs'.
  Proof.
    induction tcs; auto; simpl.
    inversion 1; auto.
  Qed.

  Lemma Reset_not_Step_in:
    forall tcs inputs mems i ck f,
      Is_well_sch inputs mems (TcReset i ck f :: tcs) ->
      ~ Step_in i tcs.
  Proof.
    inversion_clear 1 as [|???? Subs].
    unfold Step_in, Is_sub_in.
    rewrite Exists_exists.
    intros (tc' & Hin & IsStin).
    assert (Forall (fun tc => forall k', Is_sub_in_tc i k' tc -> k' < 0) tcs)
      by (apply Subs; auto using Is_sub_in_tc).
    eapply Forall_forall in Hin; eauto.
    apply Hin in IsStin.
    omega.
  Qed.

  Lemma Reset_not_Reset_in:
    forall tcs inputs mems i ck f,
      Is_well_sch inputs mems (TcReset i ck f :: tcs) ->
      ~ Reset_in i tcs.
  Proof.
    inversion_clear 1 as [|???? Subs].
    unfold Reset_in, Is_sub_in.
    rewrite Exists_exists.
    intros (tc' & Hin & IsStin).
    assert (Forall (fun tc => forall k', Is_sub_in_tc i k' tc -> k' < 0) tcs)
      by (apply Subs; auto using Is_sub_in_tc).
    eapply Forall_forall in Hin; eauto.
    apply Hin in IsStin.
    omega.
  Qed.

   (** The [normal_args] predicate defines a normalization condition on
      node arguments -- those that are not on the base clock can only
      be instantiated with constants or variables -- that is necessary
      for correct generation of Obc/Clight.

      To see why this is necessary. Consider the NLustre trconstr: y =
            f(1, 3 when ck / x)

      with x on the clock ck, and y on the base clock. The generated
            Obc code is y := f(1, 3 / x)

      which has no semantics when ck = false, since x = None then 3 /
      x is not given a meaning.

      Consider what would happen were the semantics of 3 / x =
      None. There are two possible problems.

      If x is a local variable, then x = None in Obc implies that x =
      VUndef in Clight and 3 / VUndef has no semantics. I.e., the Obc
      program having a semantics would not be enough to guarantee that
      the Clight program generated from it does.

      If x is a state variable, then x = None in Obc implies that x
      could be anything in Clight (though it would be defined since
      state variables are stored in a global structure). We might then
      prove that x is never 0 (when ck = true) in the original Lustre
      program. This would guarantee the absence of division by zero in
      the generated Obc (since x is None when ck = false), but not in
      the generated Clight code; since None in Obc means "don't care"
      in Clight, x may well contain the value 0 when ck is false (for
      instance, if ck = false at the first reaction).
 *)


  Inductive normal_args_tc (P: program) : trconstr -> Prop :=
  | CTcDef:
      forall x ck e,
        normal_args_tc P (TcDef x ck e)
  | CTcNext:
      forall x ck e,
        normal_args_tc P (TcNext x ck e)
  | CTcReset:
      forall s ck f,
        normal_args_tc P (TcReset s ck f)
  | CTcCall:
      forall s xs ck rst f es b P',
        find_system f P = Some (b, P') ->
        Forall2 noops_exp (map (fun '(_,(_, ck)) => ck) b.(s_in)) es ->
        normal_args_tc P (TcCall s xs ck rst f es).

  Definition normal_args_system (P: program) (s: system) : Prop :=
    Forall (normal_args_tc P) s.(s_tcs).

  Fixpoint normal_args (P: list system) : Prop :=
    match P with
    | [] => True
    | b :: P' => normal_args_system P b /\ normal_args P'
    end.

  Lemma normal_args_system_cons:
    forall system P,
      normal_args_system (system :: P) system ->
      ~ Is_system_in system.(s_name) system.(s_tcs) ->
      normal_args_system P system.
  Proof.
    intros system P Hnarg Hord.
    apply Forall_forall.
    intros tc Hin.
    destruct tc; eauto using normal_args_tc.
    apply Forall_forall with (2:=Hin) in Hnarg.
    inversion_clear Hnarg as [| | |???????? Hfind Hnargs].
    rewrite find_system_other in Hfind;
      eauto using normal_args_tc.
    intro; subst; apply Hord.
    apply Exists_exists.
    eexists; intuition eauto using Is_system_in_tc.
  Qed.

  Definition Well_defined (P: program) : Prop :=
    Ordered_systems P /\ Well_scheduled P /\ normal_args P.

  Lemma reset_consistency_app:
    forall tcs tcs' inputs mems,
      Is_well_sch inputs mems (tcs ++ tcs') ->
      reset_consistency (tcs ++ tcs') ->
      reset_consistency tcs'.
  Proof.
    unfold reset_consistency.
    induction tcs as [|[]]; simpl; auto; intros * Wsch Spec ?? Step;
      inversion_clear Wsch as [|??? Free Subs]; clear Free;
        try (eapply IHtcs; eauto; intros j r Step';
             specialize (Spec j r); rewrite Step_with_reset_in_cons_not_call in Spec;
             [|now discriminate]).
    - apply Spec in Step'; destruct r.
      + inversion_clear Step' as [?? Rst|]; auto; inv Rst.
      + intro; apply Step'; right; auto.
    - apply Spec in Step'; destruct r.
      + inversion_clear Step' as [?? Rst|]; auto; inv Rst.
      + intro; apply Step'; right; auto.
    - assert (j <> i).
      { assert (Is_sub_in_tc i 0 (TcReset i c i0)) as Sub by constructor.
        apply Subs in Sub.
        eapply Forall_Exists, Exists_exists in Sub as (?&?& SubSpec & Step_tc); eauto.
        inv Step_tc; intro; subst.
        assert (1 < 0) by (apply SubSpec; constructor).
        omega.
      }
      apply Spec in Step'; destruct r.
      + inversion_clear Step' as [?? Rst|]; auto; inv Rst.
        congruence.
      + intro; apply Step'; right; auto.
    - eapply IHtcs; eauto; intros j r ?.
      assert (Step_with_reset_in j r (TcCall i l c b i0 l0 :: tcs ++ tcs')) as Step'
          by (right; auto).
      apply Spec in Step'.
      destruct r.
      + inversion_clear Step' as [?? Rst|]; auto; inv Rst.
      + intro; apply Step'; right; auto.
  Qed.

  Lemma Step_not_Step_Reset_in:
    forall tcs inputs mems i ys ck rst f es,
      let tcs' := TcCall i ys ck rst f es :: tcs in
      Is_well_sch inputs mems tcs' ->
      reset_consistency tcs' ->
      ~ Step_in i tcs
      /\ if rst then Reset_in i tcs else ~ Reset_in i tcs.
  Proof.
    inversion_clear 1 as [|??? Free Subs]; clear Free.
    intros * Spec.
    split.
    - setoid_rewrite Exists_exists.
      intros (tc' & Hin & IsStin).
      assert (Forall (fun tc => forall k', Is_sub_in_tc i k' tc -> k' < 1) tcs)
        by (apply Subs; auto using Is_sub_in_tc).
      eapply Forall_forall in Hin; eauto.
      apply Hin in IsStin.
      omega.
    - assert (Step_with_reset_in i rst tcs') as Step by do 2 constructor.
      apply Spec in Step.
      destruct rst.
      + inversion_clear Step as [?? Step'|]; auto; inv Step'.
      + intro; apply Step.
        right; auto.
  Qed.

End STCWELLDEFINED.

Module StcWellDefinedFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX          Op)
       (Syn   : STCSYNTAX     Ids Op CESyn)
       (Syst  : STCISSYSTEM   Ids Op CESyn Syn)
       (Ord   : STCORDERED    Ids Op CESyn Syn Syst)
       (Var   : STCISVARIABLE Ids Op CESyn Syn)
       (Init  : STCISINIT     Ids Op CESyn Syn)
       (Def   : STCISDEFINED  Ids Op CESyn Syn Var Init)
       (CEIsF : CEISFREE      Ids Op CESyn)
       (Free  : STCISFREE     Ids Op CESyn Syn CEIsF)
<: STCWELLDEFINED Ids Op CESyn Syn Syst Ord Var Init Def CEIsF Free.
  Include STCWELLDEFINED Ids Op CESyn Syn Syst Ord Var Init Def CEIsF Free.
End StcWellDefinedFun.
