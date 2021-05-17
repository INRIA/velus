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
       (Import Reset : STCISRESET     Ids Op CESyn Syn)
       (Import Next  : STCISNEXT     Ids Op CESyn Syn)
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
            then ~Is_next_in x tcs
            else Is_variable_in x tcs \/ In x inputs) ->
        (* reset must happen before usage and update *)
        (forall x ck, Is_reset_in_tc x ck tc -> ~Is_free_in x (tc::tcs) /\ ~Is_next_in x tcs) ->
        (* Idem, reset must happen before steps *)
        (forall s ck, Is_ireset_in_tc s ck tc -> ~Is_step_in s tcs) ->
        Is_well_sch inputs mems (tc :: tcs).

  Definition Well_scheduled: program -> Prop :=
    Forall (fun s => Is_well_sch (map fst (s_in s)) (ps_from_list (map fst (s_nexts s))) (s_tcs s)).

  Lemma Is_well_sch_app:
    forall inputs mems tcs tcs',
      Is_well_sch inputs mems (tcs ++ tcs') ->
      Is_well_sch inputs mems tcs'.
  Proof.
    induction tcs; auto; simpl.
    inversion 1; auto.
  Qed.

  Lemma Reset_not_Is_step_in:
    forall tcs inputs mems i ck f,
      Is_well_sch inputs mems (TcInstReset i ck f :: tcs) ->
      ~ Is_step_in i tcs.
  Proof.
    inversion_clear 1 as [|????? Subs].
    eapply Subs; econstructor; eauto.
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
  | CTcReset:
      forall x ck c0,
        normal_args_tc P (TcReset x ck c0)
  | CTcNext:
      forall x ck ckrs e,
        normal_args_tc P (TcNext x ck ckrs e)
  | CTcIReset:
      forall s ck f,
        normal_args_tc P (TcInstReset s ck f)
  | CTcStep:
      forall s xs ck rst f es b P',
        find_system f P = Some (b, P') ->
        Forall2 noops_exp (map (fun '(_,(_, ck)) => ck) b.(s_in)) es ->
        normal_args_tc P (TcStep s xs ck rst f es).

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
    inversion_clear Hnarg as [| | | |???????? Hfind Hnargs].
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
    induction tcs as [|[]]; simpl; auto; intros * Wsch Spec;
      inversion_clear Wsch as [|??? _ Nexts _];
        try (eapply IHtcs; eauto; intros j r Step' ckr;
             specialize (Spec j r); rewrite Next_with_reset_in_cons_not_next in Spec;
             [|now discriminate]).
    - eapply Spec in Step'. rewrite Step'.
      repeat rewrite Is_reset_in_reflect. reflexivity.
    - assert (j <> i) as Hneq.
      { assert (Is_reset_in_tc i c (TcReset i c c0)) as Reset by constructor.
        apply Nexts in Reset as (?&Next).
        apply Next_with_reset_in_Is_next_in in Step'.
        intro contra; subst. contradiction. }
      eapply Spec in Step'. rewrite Step'.
      apply ident_eqb_neq in Hneq.
      repeat rewrite Is_reset_in_reflect; simpl.
      rewrite Hneq; reflexivity.
    - eapply IHtcs; eauto; intros j r ckr ?.
      assert (Next_with_reset_in j r (TcNext i c l e :: tcs ++ tcs')) as Step'
          by (right; auto).
      eapply Spec in Step'. rewrite Step'.
      repeat rewrite Is_reset_in_reflect. reflexivity.
    - eapply Spec in Step'. rewrite Step'.
      repeat rewrite Is_reset_in_reflect. reflexivity.
    - eapply Spec in Step'. rewrite Step'.
      repeat rewrite Is_reset_in_reflect. reflexivity.
  Qed.

  Lemma ireset_consistency_app:
    forall tcs tcs' inputs mems,
      Is_well_sch inputs mems (tcs ++ tcs') ->
      ireset_consistency (tcs ++ tcs') ->
      ireset_consistency tcs'.
  Proof.
    unfold ireset_consistency.
    induction tcs as [|[]]; simpl; auto; intros * Wsch Spec;
      inversion_clear Wsch as [|??? Free Next Subs]; clear Free Next;
        try (eapply IHtcs; eauto; intros j r Step' ckr;
             specialize (Spec j r); rewrite Step_with_ireset_in_cons_not_step in Spec;
             [|now discriminate]).
    - eapply Spec in Step'. rewrite Step'.
      repeat rewrite Is_ireset_in_reflect. reflexivity.
    - eapply Spec in Step'. rewrite Step'.
      repeat rewrite Is_ireset_in_reflect. reflexivity.
    - eapply Spec in Step'. rewrite Step'.
      repeat rewrite Is_ireset_in_reflect. reflexivity.
    - assert (j <> i) as Hneq.
      { assert (Is_ireset_in_tc i c (TcInstReset i c i0)) as Sub by constructor.
        apply Subs in Sub.
        apply Step_with_ireset_in_Is_step_in in Step'.
        intro contra; subst. contradiction. }
      eapply Spec in Step'. rewrite Step'.
      apply ident_eqb_neq in Hneq.
      repeat rewrite Is_ireset_in_reflect; simpl.
      rewrite Hneq; reflexivity.
    - eapply IHtcs; eauto; intros j r ckr ?.
      assert (Step_with_ireset_in j r (TcStep i l c l0 i0 l1 :: tcs ++ tcs')) as Step'
          by (right; auto).
      eapply Spec in Step'. rewrite Step'.
      repeat rewrite Is_ireset_in_reflect. reflexivity.
  Qed.

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
        let nexts := ps_adds (nexts_of [tc]) nexts in
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
    Hint Resolve check_var_compat.

    Lemma not_well_sch_vars_defs_spec:
      forall tcs args nexts vars tc,
        (forall x, PS.In x nexts <-> Is_next_in x tcs) ->
        (forall x, PS.In x vars <-> Is_variable_in x tcs \/ In x args) ->
        PS.for_all (check_var nexts vars) (free_in_tc tc PS.empty) = false ->
        ~ Is_well_sch args mems (tc :: tcs).
    Proof.
      intros * NextSpec VarSpec E Wsch.
      inversion_clear Wsch as [|??? Hfree Hdefs].
      apply PS_not_for_all_spec in E; auto.
      apply E; intros x Hin; apply free_in_tc_spec' in Hin.
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
      inversion_clear Wsch as [|??? _ Hreset _].
      apply forallb_exists in E as (?&Hin&Hcheck).
      apply resets_of_In in Hin as (?&Hin).
      inv Hin. 2:inv H1.
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
        (PS.In x (ps_adds (nexts_of [tc]) defs) <-> Is_next_in x (tc :: tcs)).
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
          assert (forall x, PS.In x (ps_adds (nexts_of [tc]) nexts') <-> Is_next_in x (tc :: tcs))
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
               constructor; auto.
               + intros; eapply free_spec; eauto.
               + intros * Hreset.
                 assert (In x (resets_of [tc])) as Hin by (eapply reset_of_In; eauto).
                 eapply Forall_forall in Hin; eauto.
                 rewrite check_reset_spec, FreeSpec', NextSpec in Hin; auto.
               + intros * Hin. inv Hin. inv St.
                 rewrite <- StepSpec; auto.

             - repeat rewrite Bool.andb_false_iff in E. destruct E as [E|[E|E]].
               + inversion_clear 1 as [|????? Hsubs].
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
               constructor; auto.
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

  (** *** Result of scheduling : Reset constraints always appear before Nexts,
          and Resets always appear before Steps *)

  Lemma Is_well_sch_Reset_Next : forall inputs mems x ck ro tcs,
      Is_well_sch inputs mems (TcReset x ck ro :: tcs) ->
      ~Is_next_in x tcs.
  Proof.
    intros * Sch.
    inversion_clear Sch.
    specialize (H1 _ _ (ResetTcReset _ _ _)) as (?&?); auto.
  Qed.

  Lemma Is_well_sch_Reset_Step : forall inputs mems i ck f tcs,
      Is_well_sch inputs mems (TcInstReset i ck f :: tcs) ->
      ~Is_step_in i tcs.
  Proof.
    intros * Sch.
    inversion_clear Sch.
    eapply H2. constructor.
  Qed.

  Lemma Is_well_sch_free_Reset : forall inputs mems tcs tc tcs' x,
      Is_well_sch inputs mems ((tcs ++ [tc]) ++ tcs') ->
      Is_free_in_tc x tc ->
      ~exists ck, Is_reset_in x ck (tcs ++ [tc]).
  Proof.
    induction tcs; intros * Wsch Free (ck&Reset); simpl in *;
      inversion_clear Wsch as [|?? Wsch' _ Resets _].
    - inv Reset. 2:inv H0.
      apply Resets in H0 as (NFree&_).
      apply NFree. left; auto.
    - inv Reset.
      + inv H0.
        specialize (Resets _ _ (ResetTcReset _ _ _)) as (NFree&_).
        apply NFree. right. repeat rewrite Exists_app'; auto.
      + eapply IHtcs in Wsch'; eauto.
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
       (Reset : STCISRESET     Ids Op CESyn Syn)
       (Next  : STCISNEXT     Ids Op CESyn Syn)
       (CEIsF : CEISFREE      Ids Op CESyn)
       (Free  : STCISFREE     Ids Op CESyn Syn CEIsF)
<: STCWELLDEFINED Ids Op CESyn Syn Syst Ord Var Reset Next CEIsF Free.
  Include STCWELLDEFINED Ids Op CESyn Syn Syst Ord Var Reset Next CEIsF Free.
End StcWellDefinedFun.
