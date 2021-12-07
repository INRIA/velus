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
From Velus Require Import Stc.StcIsReset.
From Velus Require Import Stc.StcIsNext.
From Velus Require Import Stc.StcIsDefined.

From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import Stc.StcIsFree.

From Velus Require Import Stc.StcWellDefined.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCSCHEDULINGVALIDATOR
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX  Ids Op)
       (Import Cks   : CLOCKS         Ids Op OpAux)
       (Import CESyn : CESYNTAX       Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX      Ids Op OpAux Cks CESyn)
       (Import Syst  : STCISSYSTEM    Ids Op OpAux Cks CESyn Syn)
       (Import Ord   : STCORDERED     Ids Op OpAux Cks CESyn Syn Syst)
       (Import Var   : STCISVARIABLE  Ids Op OpAux Cks CESyn Syn)
       (Import Reset : STCISRESET     Ids Op OpAux Cks CESyn Syn)
       (Import Next  : STCISNEXT      Ids Op OpAux Cks CESyn Syn)
       (Import CEIsF : CEISFREE       Ids Op OpAux Cks CESyn)
       (Import Free  : STCISFREE      Ids Op OpAux Cks CESyn Syn CEIsF)
       (Import Wdef  : STCWELLDEFINED Ids Op OpAux Cks CESyn Syn Syst Ord Var Reset Next CEIsF Free).


  Module PN_as_OT := OrdersEx.PairOrderedType OrdersEx.Positive_as_OT OrdersEx.Nat_as_OT.
  Module PNS := MSetList.Make PN_as_OT.

  Section Decide.

    Variable mems : PS.t.

    (* TODO: rewrite using a strong specification?  *)

    Open Scope bool_scope.

    Definition check_var (nexts: PS.t) (variables: PS.t) (x: ident) : bool :=
      if PS.mem x mems
      then negb (PS.mem x nexts)
      else PS.mem x variables.

    Definition check_reset (frees: PS.t) (nexts: PS.t) (x : ident) : bool :=
      andb (negb (PS.mem x frees)) (negb (PS.mem x nexts)).

    Definition ireset_tc (tc: trconstr) : option ident :=
      match tc with
      | TcInstReset i _ _      => Some i
      | _ => None
      end.

    Definition step_tc (tc: trconstr) : list ident :=
      match tc with
      | TcStep i _ _ _ _ _ => [i]
      | _ => []
      end.

    Definition check_ireset (steps: PS.t) (i: ident) : bool :=
      negb (PS.mem i steps).

    Definition check_tc (tc: trconstr) (acc: bool * PS.t * PS.t * PS.t * PS.t)
      : bool * PS.t * PS.t * PS.t * PS.t :=
      match acc with
      | (true, frees, nexts, vars, steps) =>
        let b1 := PS.for_all (check_var nexts vars) (free_in_tc tc PS.empty) in
        let frees := free_in_tc tc frees in
        let b := b1 && forallb (check_reset frees nexts) (resets_of [tc]) in
        let nexts := ps_adds (map fst (nexts_of [tc])) nexts in
        let vars := ps_adds (variables_tc tc) vars in
        let steps' := ps_adds (step_tc tc) steps in
        match ireset_tc tc with
        | Some i =>
          (check_ireset steps i && b, frees, nexts, vars, steps')
        | None => (b, frees, nexts, vars, steps')
        end
      | acc => acc
      end.

    Definition well_sch (args: list ident) (tcs: list trconstr) : bool :=
      fst (fst (fst (fst (fold_right check_tc
                                     (true, PS.empty, PS.empty, ps_from_list args, PS.empty)
                                     tcs)))).

    Lemma check_var_spec:
      forall nexts variables x,
        check_var nexts variables x = true
        <->
        (PS.In x mems -> ~PS.In x nexts)
        /\ (~PS.In x mems -> PS.In x variables).
    Proof.
      intros *.
      unfold check_var.
      repeat rewrite <-PS.mem_spec. repeat rewrite Bool.not_true_iff_false.
      split.
      - intro Hif.
        split; intro Hin; rewrite Hin in Hif; auto.
        rewrite <-Bool.negb_true_iff; auto.
      - destruct 1 as [Hin Hnin].
        destruct (PS.mem x mems); auto.
        rewrite Bool.negb_true_iff; auto.
    Qed.

    Lemma check_reset_spec:
      forall frees nexts x,
        check_reset frees nexts x = true
        <-> ~PS.In x frees /\ ~PS.In x nexts.
    Proof.
      intros *. unfold check_reset.
      rewrite Bool.andb_true_iff.
      repeat rewrite PSF.mem_iff, Bool.negb_true_iff, Bool.not_true_iff_false.
      reflexivity.
    Qed.

    Lemma Is_ireset_in_ireset_tc:
      forall tc i,
        (exists ck, Is_ireset_in_tc i ck tc) <-> ireset_tc tc = Some i.
    Proof.
      destruct tc; simpl; split; try inversion_clear 1; subst; eauto using Is_ireset_in_tc.
      1-5:inv H0; auto.
    Qed.

    Lemma Is_step_in_step_tc:
      forall tc i,
        Is_step_in_tc i tc <-> In i (step_tc tc).
    Proof.
      destruct tc; simpl; split; try inversion_clear 1; subst; auto using Is_step_in_tc.
      inv H0.
    Qed.

    Lemma check_ireset_spec:
      forall steps i,
        check_ireset steps i = true
        <-> ~PS.In i steps.
    Proof.
      intros *. unfold check_ireset.
      rewrite PSF.mem_iff, Bool.not_true_iff_false, Bool.negb_true_iff.
      reflexivity.
    Qed.

    Lemma PS_not_for_all_spec:
      forall (s : PS.t) (f : BinNums.positive -> bool),
        SetoidList.compat_bool PS.E.eq f ->
        (PS.for_all f s = false <-> ~ PS.For_all (fun x => f x = true) s).
    Proof.
      intros s f HSL.
      split.
      - intros Hfa HFa.
        apply (PS.for_all_spec _ HSL) in HFa.
        rewrite Hfa in HFa.
        discriminate.
      - intro HFa.
        apply Bool.not_true_iff_false.
        intro Hfa; apply HFa.
        apply (PS.for_all_spec _ HSL).
        assumption.
    Qed.

    Lemma free_spec:
      forall tcs args nexts vars tc x,
        (forall x, PS.In x nexts <-> Is_next_in x tcs) ->
        (forall x, PS.In x vars <-> Is_variable_in x tcs \/ In x args) ->
        PS.For_all (fun x => check_var nexts vars x = true) (free_in_tc tc PS.empty) ->
        Is_free_in_tc x tc ->
        if PS.mem x mems then ~ Is_next_in x tcs else Is_variable_in x tcs \/ In x args.
    Proof.
      intros * NextSpec VarSpec E Hfree.
      apply free_in_tc_spec', E, check_var_spec in Hfree as (Hin & Hnin).
      destruct (PS.mem x mems) eqn: Mem.
      - rewrite <-NextSpec; apply PSE.MP.Dec.F.mem_iff, Hin in Mem; auto.
      - rewrite <-VarSpec; apply PSE.MP.Dec.F.not_mem_iff, Hnin in Mem; auto.
    Qed.

    Lemma check_var_compat:
      forall next variables,
        SetoidList.compat_bool PS.E.eq (check_var next variables).
    Proof.
      intros * x y Htc.
      unfold PS.E.eq in Htc.
      rewrite Htc.
      reflexivity.
    Qed.
    Local Hint Resolve check_var_compat : core.

    Lemma not_well_sch_vars_defs_spec:
      forall tcs args nexts vars tc,
        (forall x, PS.In x nexts <-> Is_next_in x tcs) ->
        (forall x, PS.In x vars <-> Is_variable_in x tcs \/ In x args) ->
        PS.for_all (check_var nexts vars) (free_in_tc tc PS.empty) = false ->
        ~ Is_well_sch args mems (tc :: tcs).
    Proof.
      intros * NextSpec VarSpec E Wsch.
      inversion_clear Wsch as [|?? (Hfree&Hdefs&?) ?].
      apply PS_not_for_all_spec in E; auto.
      apply E; intros ? Hin; apply free_in_tc_spec' in Hin.
      apply Hfree in Hin.
      apply check_var_spec; split.
      - rewrite PSE.MP.Dec.F.mem_iff; intro Hin'; rewrite Hin' in Hin.
        now rewrite NextSpec.
      - rewrite PSE.MP.Dec.F.not_mem_iff; intro Hin'; rewrite Hin' in Hin.
        now rewrite VarSpec.
    Qed.

    Lemma not_well_sch_resets_spec:
      forall tcs args frees nexts tc,
        (forall x, PS.In x frees <-> Is_free_in x (tc::tcs)) ->
        (forall x, PS.In x nexts <-> Is_next_in x tcs) ->
        forallb (check_reset frees nexts) (resets_of [tc]) = false ->
        ~ Is_well_sch args mems (tc :: tcs).
    Proof.
      intros * FreeSpec ResetSpec E Wsch.
      inversion_clear Wsch as [|?? (?&?&Hreset) _].
      apply forallb_exists in E as (?&Hin&Hcheck).
      apply resets_of_In in Hin as (?&Hin).
      inv Hin. 2:inv H2.
      rewrite <- Bool.not_true_iff_false, check_reset_spec, FreeSpec, ResetSpec in Hcheck.
      eauto.
    Qed.

    Lemma Is_free_in_free_tc:
      forall tcs frees tc x,
        (forall x, PS.In x frees <-> Is_free_in x tcs) ->
        (PS.In x (free_in_tc tc frees) <-> Is_free_in x (tc :: tcs)).
    Proof.
      intros * FreeSpec.
      rewrite free_in_tc_spec, FreeSpec.
      split; intro Hin; (inv Hin; [left|right]); auto.
    Qed.

    Lemma Is_reset_in_adds_resets_tc:
      forall tcs resets tc x,
        (forall x, PS.In x resets <-> exists ck, Is_reset_in x ck tcs) ->
        (PS.In x (ps_adds (resets_of [tc]) resets) <-> exists ck, Is_reset_in x ck (tc :: tcs)).
    Proof.
      intros * ResetSpec; split; [intro Hin|intros (?&Hin)];
        [apply ps_adds_spec in Hin as [|]|apply ps_adds_spec; inv Hin].
      - apply resets_of_In in H as (ck&H). apply Exists_singl in H. exists ck.
        left; auto.
      - apply ResetSpec in H as (ck&H). exists ck. right; auto.
      - left. apply resets_of_In. exists x0. left; auto.
      - right. rewrite ResetSpec; eauto.
    Qed.

    Lemma Is_next_in_adds_next_tc:
      forall tcs defs tc x,
        (forall x, PS.In x defs <-> Is_next_in x tcs) ->
        (PS.In x (ps_adds (map fst (nexts_of [tc])) defs) <-> Is_next_in x (tc :: tcs)).
    Proof.
      intros * NextSpec; split; intro Hin;
        [apply ps_adds_spec in Hin as [|]|apply ps_adds_spec; inv Hin];
        try (now right; apply NextSpec; auto); auto.
      - apply nexts_of_In, Exists_singl in H. left; auto.
      - left. apply nexts_of_In. left; auto.
    Qed.

    Lemma Is_step_in_adds_step_tc:
      forall tcs steps tc x,
        (forall x, PS.In x steps <-> Is_step_in x tcs) ->
        (PS.In x (ps_adds (step_tc tc) steps) <-> Is_step_in x (tc :: tcs)).
    Proof.
      intros * StepSpec; split; intro Hin;
        [apply ps_adds_spec in Hin as [|]|apply ps_adds_spec; inv Hin];
        try (now right; apply StepSpec; auto); auto.
      1,2:left; apply Is_step_in_step_tc; auto.
    Qed.

    Lemma Is_variable_in_variables_tc:
      forall tcs args vars tc x,
        (forall x, PS.In x vars <-> Is_variable_in x tcs \/ In x args) ->
        (PS.In x (ps_adds (variables_tc tc) vars) <-> Is_variable_in x (tc :: tcs) \/ In x args).
    Proof.
      intros * VarSpec; split; intro Hin;
        [apply ps_adds_spec in Hin as [|]|apply ps_adds_spec; inv Hin];
        try (now right; apply VarSpec; auto); auto.
      - rewrite Is_variable_in_variables; simpl.
        rewrite in_app; intuition.
      - rewrite Is_variable_in_variables; simpl.
        rewrite in_app.
        apply VarSpec in H as [|]; intuition.
        rewrite <-Is_variable_in_variables; intuition.
      - rewrite Is_variable_in_variables in H; simpl in H;
          rewrite in_app in H; destruct H; intuition.
        rewrite <-Is_variable_in_variables in H.
        right; apply VarSpec; auto.
    Qed.

    Lemma well_sch_pre_spec:
      forall args tcs ok frees nexts vars steps,
        fold_right check_tc (true,
                             PS.empty,
                             PS.empty,
                             ps_from_list args,
                             PS.empty) tcs = (ok, frees, nexts, vars, steps) ->
        if ok
        then
          Is_well_sch args mems tcs
          /\ (forall x, PS.In x frees <-> Is_free_in x tcs)
          /\ (forall x, PS.In x nexts <-> Is_next_in x tcs)
          /\ (forall x, PS.In x vars <-> Is_variable_in x tcs \/ In x args)
          /\ (forall i, PS.In i steps <-> Is_step_in i tcs)
        else
          ~Is_well_sch args mems tcs.
    Proof.
      induction tcs as [|tc].
      - simpl; inversion_clear 1; intuition; try (now constructor);
          repeat match goal with
                 | H:PS.In _ PS.empty |- _ => apply PS.empty_spec in H; contradiction
                 | H:Is_free_in _ nil |- _ => inversion H
                 | H:Is_next_in _ nil |- _ => inversion H
                 | H:Is_variable_in _ nil |- _ => inversion H
                 | H:Is_step_in _ nil |- _ => inversion H
                 | H: context[ps_from_list _] |- _ =>
                   apply ps_from_list_In in H
                 | _ => intuition
                 end.
        apply ps_from_list_In; auto.
      - simpl; intros * HH.
        destruct (fold_right check_tc (true, PS.empty, PS.empty, ps_from_list args, PS.empty) tcs)
          as [[[[ok' frees'] nexts'] vars'] steps'].
        specialize (IHtcs ok' frees' nexts' vars' steps' eq_refl).
        simpl in HH.
        destruct ok'.
        + destruct IHtcs as (Wsch & FreeSpec & NextSpec & VarSpec & StepSpec).
          assert (forall x, PS.In x (free_in_tc tc frees') <-> Is_free_in x (tc :: tcs)) as FreeSpec'
            by (intros; eapply Is_free_in_free_tc; eauto).
          assert (forall x, PS.In x (ps_adds (map fst (nexts_of [tc])) nexts') <-> Is_next_in x (tc :: tcs))
            by (intros; eapply Is_next_in_adds_next_tc; eauto).
          assert (forall x, PS.In x (ps_adds (variables_tc tc) vars') <-> Is_variable_in x (tc :: tcs) \/ In x args)
            by (intros; eapply Is_variable_in_variables_tc; eauto).
          assert (forall x, PS.In x (ps_adds (step_tc tc) steps') <-> Is_step_in x (tc :: tcs))
            by (intros; eapply Is_step_in_adds_step_tc; eauto).
          destruct (ireset_tc tc) as [i|] eqn: St.
          *{ destruct ok; inversion HH as [E]; clear HH.
             - repeat rewrite Bool.andb_true_iff in E. destruct E as (E & E' & E'').
               apply check_ireset_spec in E; auto.
               apply PS.for_all_spec in E'; auto.
               apply forallb_Forall in E''.
               split; [|split; [|split; [|split]]]; auto.
               constructor; auto. split; [|split].
               + intros; eapply free_spec; eauto.
               + intros * Hreset.
                 assert (In x (resets_of [tc])) as Hin by (eapply reset_of_In; eauto).
                 eapply Forall_forall in Hin; eauto.
                 rewrite check_reset_spec, FreeSpec', NextSpec in Hin; auto.
               + intros * Hin. inv Hin. inv St.
                 rewrite <- StepSpec; auto.

             - repeat rewrite Bool.andb_false_iff in E. destruct E as [E|[E|E]].
               + inversion_clear 1 as [|?? (?&?&Hsubs) ?].
                 apply Is_ireset_in_ireset_tc in St as (?&St).
                 apply Hsubs in St.
                 rewrite <-StepSpec, <-check_ireset_spec in St.
                 congruence.
               + eapply not_well_sch_vars_defs_spec; eauto.
               + eapply not_well_sch_resets_spec; eauto.
           }
          *{ destruct ok; inversion HH as [E].
             - repeat rewrite Bool.andb_true_iff in E. destruct E as (E&E').
               apply PS.for_all_spec in E; try apply check_var_compat.
               split; [|split; [|split; [|split]]]; auto.
               constructor; auto. split; [|split].
               + intros; eapply free_spec; eauto.
               + intros * Hreset.
                 rewrite forallb_Forall in E'.
                 assert (In x (resets_of [tc])) as Hin by (eapply reset_of_In; eauto).
                 eapply Forall_forall in Hin; eauto.
                 rewrite check_reset_spec, FreeSpec', NextSpec in Hin; auto.
               + intros * Hin. inv Hin. inv St.
             - repeat rewrite Bool.andb_false_iff in E. destruct E as [E|E].
               + eapply not_well_sch_vars_defs_spec; eauto.
               + eapply not_well_sch_resets_spec; eauto.
           }

        + inv HH; inversion 1; auto.
    Qed.

    Theorem well_sch_spec:
      forall args tcs,
        if well_sch args tcs
        then Is_well_sch args mems tcs
        else ~ Is_well_sch args mems tcs.
    Proof.
      intros.
      pose proof (well_sch_pre_spec args tcs) as Spec.
      unfold well_sch.
      destruct (fold_right check_tc
                  (true, PS.empty, PS.empty, ps_from_list args, PS.empty) tcs)
        as [[[[ok resets] nexts] vars] subs]; simpl.
      specialize (Spec ok resets nexts vars subs eq_refl).
      destruct ok; intuition.
    Qed.

    Lemma Is_well_sch_by_refl:
      forall args tcs,
        well_sch args tcs = true <-> Is_well_sch args mems tcs.
    Proof.
      intros.
      pose proof (well_sch_spec args tcs) as Hwss.
      split; intro H.
      rewrite H in Hwss; assumption.
      destruct (well_sch args tcs); [reflexivity|].
      exfalso; apply Hwss; apply H.
    Qed.

    Lemma well_sch_dec:
      forall args tcs,
        {Is_well_sch args mems tcs} + {~ Is_well_sch args mems tcs}.
    Proof.
      intros.
      pose proof (well_sch_spec args tcs) as Hwss.
      destruct (well_sch args tcs); [left|right]; assumption.
    Qed.

  End Decide.

End STCSCHEDULINGVALIDATOR.

Module StcSchedulingValidatorFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (Cks   : CLOCKS         Ids Op OpAux)
       (CESyn : CESYNTAX       Ids Op OpAux Cks)
       (Syn   : STCSYNTAX      Ids Op OpAux Cks CESyn)
       (Syst  : STCISSYSTEM    Ids Op OpAux Cks CESyn Syn)
       (Ord   : STCORDERED     Ids Op OpAux Cks CESyn Syn Syst)
       (Var   : STCISVARIABLE  Ids Op OpAux Cks CESyn Syn)
       (Reset : STCISRESET     Ids Op OpAux Cks CESyn Syn)
       (Next  : STCISNEXT      Ids Op OpAux Cks CESyn Syn)
       (CEIsF : CEISFREE       Ids Op OpAux Cks CESyn)
       (Free  : STCISFREE      Ids Op OpAux Cks CESyn Syn CEIsF)
       (Wdef  : STCWELLDEFINED Ids Op OpAux Cks CESyn Syn Syst Ord Var Reset Next CEIsF Free)
<: STCSCHEDULINGVALIDATOR Ids Op OpAux Cks CESyn Syn Syst Ord Var Reset Next CEIsF Free Wdef.
  Include STCSCHEDULINGVALIDATOR Ids Op OpAux Cks CESyn Syn Syst Ord Var Reset Next CEIsF Free Wdef.
End StcSchedulingValidatorFun.
