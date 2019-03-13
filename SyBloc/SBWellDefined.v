Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.Clocks.

Require Import Velus.SyBloc.SBIsBlock.
Require Import Velus.SyBloc.SBOrdered.

Require Import Velus.SyBloc.SBIsVariable.
Require Import Velus.SyBloc.SBIsLast.
Require Import Velus.SyBloc.SBIsDefined.

Require Import Velus.NLustre.NLSyntax.
Require Import Velus.SyBloc.SBIsFree.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type SBWELLDEFINED
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import Clks    : CLOCKS       Ids)
       (Import ExprSyn : NLEXPRSYNTAX     Op)
       (Import Syn     : SBSYNTAX     Ids Op Clks ExprSyn)
       (Import Block   : SBISBLOCK    Ids Op Clks ExprSyn Syn)
       (Import Ord     : SBORDERED    Ids Op Clks ExprSyn Syn Block)
       (Import Var     : SBISVARIABLE Ids Op Clks ExprSyn Syn)
       (Import Last    : SBISLAST     Ids Op Clks ExprSyn Syn)
       (Import Def     : SBISDEFINED  Ids Op Clks ExprSyn Syn Var Last)
       (SynNL          : NLSYNTAX     Ids Op Clks ExprSyn)
       (Import IsF     : ISFREE       Ids Op Clks ExprSyn     SynNL)
       (Import Free    : SBISFREE     Ids Op Clks ExprSyn Syn SynNL IsF).

  Inductive Is_well_sch (inputs: list ident) (mems: PS.t): list equation -> Prop :=
  | WSchNil:
      Is_well_sch inputs mems []
  | WSchEq:
      forall eq eqs,
        Is_well_sch inputs mems eqs ->
        (forall x,
            Is_free_in_eq x eq ->
            if PS.mem x mems
            then ~ Is_defined_in x eqs
            else Is_variable_in x eqs \/ In x inputs) ->
        (forall x, Is_defined_in_eq x eq -> ~ Is_defined_in x eqs) ->
        (forall s k,
            Is_state_in_eq s k eq ->
            Forall (fun eq => forall k', Is_state_in_eq s k' eq -> k' < k) eqs) ->
        Is_well_sch inputs mems (eq :: eqs).

  Inductive Well_scheduled: program -> Prop :=
    | Well_scheduled_nil:
        Well_scheduled []
    | Well_scheduled_cons:
        forall bl P,
          Well_scheduled P ->
          Is_well_sch (map fst (b_in bl)) (ps_from_list (map fst (b_lasts bl))) (b_eqs bl) ->
          Well_scheduled (bl :: P).

  Definition Well_defined (P: program) : Prop :=
    Ordered_blocks P /\ Well_scheduled P.

  Lemma Is_well_sch_app:
    forall mems inputs eqs eqs',
      Is_well_sch mems inputs (eqs ++ eqs') ->
      Is_well_sch mems inputs eqs'.
  Proof.
    induction eqs; auto; simpl.
    inversion 1; auto.
  Qed.

  Lemma Reset_not_Step_in:
    forall eqs inputs mems s ck b,
      Is_well_sch inputs mems (EqReset s ck b :: eqs) ->
      ~ Step_in s eqs.
  Proof.
    inversion_clear 1 as [|????? States].
    unfold Step_in, Is_state_in.
    rewrite Exists_exists.
    intros (eq' & Hin & IsStin).
    assert (Forall (fun eq => forall k', Is_state_in_eq s k' eq -> k' < 0) eqs)
      by (apply States; auto using Is_state_in_eq).
    eapply Forall_forall in Hin; eauto.
    apply Hin in IsStin.
    omega.
  Qed.

  Lemma Reset_not_Reset_in:
    forall eqs inputs mems s ck b,
      Is_well_sch inputs mems (EqReset s ck b :: eqs) ->
      ~ Reset_in s eqs.
  Proof.
    inversion_clear 1 as [|????? States].
    unfold Reset_in, Is_state_in.
    rewrite Exists_exists.
    intros (eq' & Hin & IsStin).
    assert (Forall (fun eq => forall k', Is_state_in_eq s k' eq -> k' < 0) eqs)
      by (apply States; auto using Is_state_in_eq).
    eapply Forall_forall in Hin; eauto.
    apply Hin in IsStin.
    omega.
  Qed.

  Inductive Step_with_reset_spec: list equation -> Prop :=
  | Step_with_reset_nil:
      Step_with_reset_spec []
  | Step_with_reset_EqDef:
      forall x ck e eqs,
        Step_with_reset_spec eqs ->
        Step_with_reset_spec (EqDef x ck e :: eqs)
  | Step_with_reset_EqNext:
      forall x ck e eqs,
        Step_with_reset_spec eqs ->
        Step_with_reset_spec (EqNext x ck e :: eqs)
  | Step_with_reset_EqReset:
      forall s ck b eqs,
        Step_with_reset_spec eqs ->
        Step_with_reset_spec (EqReset s ck b :: eqs)
  | Step_with_reset_EqCall:
      forall s xs ck (rst: bool) b es eqs,
        Step_with_reset_spec eqs ->
        (if rst then Reset_in s eqs else ~ Reset_in s eqs) ->
        Step_with_reset_spec (EqCall s xs ck rst b es :: eqs).

  Lemma Step_with_reset_spec_app:
    forall eqs eqs',
      Step_with_reset_spec (eqs ++ eqs') ->
      Step_with_reset_spec eqs'.
  Proof.
    induction eqs; auto; simpl.
    inversion 1; auto.
  Qed.

  Lemma Step_not_Step_Reset_in:
    forall eqs inputs mems s ys ck rst b es,
      Is_well_sch inputs mems (EqCall s ys ck rst b es :: eqs) ->
      Step_with_reset_spec (EqCall s ys ck rst b es :: eqs) ->
      ~ Step_in s eqs
      /\ if rst then Reset_in s eqs else ~ Reset_in s eqs.
  Proof.
    inversion_clear 1 as [|????? States].
    inversion_clear 1.
    split; auto.
    setoid_rewrite Exists_exists.
    intros (eq' & Hin & IsStin).
    assert (Forall (fun eq => forall k', Is_state_in_eq s k' eq -> k' < 1) eqs)
        by (apply States; auto using Is_state_in_eq).
    eapply Forall_forall in Hin; eauto.
    apply Hin in IsStin.
    omega.
  Qed.

  Lemma Is_well_sch_Step_with_reset_spec:
    forall eqs inputs mems,
      (forall s rst, Step_with_reset_in s rst eqs ->
                if rst then Reset_in s eqs else ~ Reset_in s eqs) ->
      Is_well_sch inputs mems eqs ->
      Step_with_reset_spec eqs.
  Proof.
    induction eqs as [|[]]; intros ** Spec WSCH;
      inversion_clear WSCH as [|??? Free Def States];
      constructor;
      clear Free Def;
      try (eapply IHeqs; eauto; intros ** Step; specialize (Spec s rst));
      try (setoid_rewrite Step_with_reset_in_cons_not_call in Spec; [|discriminate]).
    - apply Spec in Step.
      destruct rst.
      + inversion_clear Step as [?? Step'|]; auto; inv Step'.
      + intro; apply Step; right; auto.
    - apply Spec in Step.
      destruct rst.
      + inversion_clear Step as [?? Step'|]; auto; inv Step'.
      + intro; apply Step; right; auto.
    - assert (s <> i).
      { assert (Is_state_in_eq i 0 (EqReset i c i0)) as State by constructor.
        apply States in State.
        eapply Forall_Exists, Exists_exists in State as (?&?& StateSpec & Step_eq); eauto.
        inv Step_eq; intro; subst.
        assert (1 < 0) by (apply StateSpec; constructor).
        omega.
      }
      apply Spec in Step.
      destruct rst.
      + inversion_clear Step as [?? Step'|]; auto; inv Step'.
        congruence.
      + intro; apply Step; right; auto.
    - assert (s <> i).
      { assert (Is_state_in_eq i 1 (EqCall i i0 c b i1 l)) as State by constructor.
        apply States in State.
        eapply Forall_Exists, Exists_exists in State as (?&?& StateSpec & Step_eq); eauto.
        inv Step_eq; intro; subst.
        assert (1 < 1) by (apply StateSpec; constructor).
        omega.
      }
      rewrite Step_with_reset_in_cons_call in Spec; auto.
      apply Spec in Step.
      destruct rst.
      + inversion_clear Step as [?? Step'|]; auto; inv Step'.
      + intro; apply Step; right; auto.
    - assert (Step_with_reset_in i b (EqCall i i0 c b i1 l :: eqs)) as Step
          by (left; constructor).
      apply Spec in Step.
      destruct b.
      + inversion_clear Step as [?? Step'|]; auto; inv Step'.
      + intro; apply Step; right; auto.
  Qed.

End SBWELLDEFINED.
