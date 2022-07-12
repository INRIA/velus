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

Module Type STCWELLDEFINED
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX     Ids Op OpAux Cks CESyn)
       (Import Syst  : STCISSYSTEM   Ids Op OpAux Cks CESyn Syn)
       (Import Ord   : STCORDERED    Ids Op OpAux Cks CESyn Syn Syst)
       (Import Var   : STCISVARIABLE Ids Op OpAux Cks CESyn Syn)
       (Import Reset : STCISRESET    Ids Op OpAux Cks CESyn Syn)
       (Import Next  : STCISNEXT     Ids Op OpAux Cks CESyn Syn)
       (Import CEIsF : CEISFREE      Ids Op OpAux Cks CESyn)
       (Import Free  : STCISFREE     Ids Op OpAux Cks CESyn Syn CEIsF).

  Definition Is_well_sch (inputs: list ident) (mems: PS.t): list trconstr -> Prop :=
    Forall' (fun tcs tc =>
               (forall x,
                   Is_free_in_tc x tc ->
                   if PS.mem x mems
                   then ~Is_next_in x tcs
                   else Is_variable_in x tcs \/ In x inputs) /\
               (* reset must happen before usage and update *)
               (forall x ck, Is_reset_in_tc x ck tc -> ~Is_free_in x (tc::tcs) /\ ~Is_next_in x tcs) /\
               (* Idem, reset must happen before steps *)
               (forall s ck, Is_ireset_in_tc s ck tc -> ~Is_step_in s tcs)).

  Definition Well_scheduled (P: program) :=
    Forall (fun s => Is_well_sch (map fst (s_in s)) (ps_from_list (map fst (s_nexts s))) (s_tcs s)) P.(systems).

  Lemma Is_well_sch_app:
    forall inputs mems tcs tcs',
      Is_well_sch inputs mems (tcs ++ tcs') ->
      Is_well_sch inputs mems tcs'.
  Proof.
    induction tcs; auto; simpl.
    inversion 1; auto.
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
      forall x ck ty c0,
        normal_args_tc P (TcReset x ck ty c0)
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

  Definition normal_args (P: program) : Prop :=
    Forall' (fun ss => normal_args_system (Program P.(types) P.(externs) ss)) P.(systems).

  Lemma normal_args_system_cons:
    forall system P enums externs,
      normal_args_system (Program enums externs (system :: P)) system ->
      ~ Is_system_in system.(s_name) system.(s_tcs) ->
      normal_args_system (Program enums externs P) system.
  Proof.
    intros system P enums externs Hnarg Hord.
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
      inversion_clear Wsch as [|?? (_&Nexts&_)];
        try (eapply IHtcs; eauto; intros j ckrs Step' ckr;
             specialize (Spec j ckrs); rewrite Next_with_reset_in_cons_not_next in Spec;
             [|now discriminate]).
    - eapply Spec in Step'. rewrite Step'.
      repeat rewrite Is_reset_in_reflect. reflexivity.
    - assert (j <> i) as Hneq.
      { assert (Is_reset_in_tc i c (TcReset i c t c0)) as Reset by constructor.
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
      inversion_clear Wsch as [|?? (Free&Next&Subs)]; clear Free Next;
        try (eapply IHtcs; eauto; intros j ckrs Step' ckr;
             specialize (Spec j ckrs); rewrite Step_with_ireset_in_cons_not_step in Spec;
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

  (** *** Result of scheduling : Reset constraints always appear before Nexts,
          and Resets always appear before Steps *)

  Lemma Is_well_sch_Reset_Next : forall inputs mems x ck ty ro tcs,
      Is_well_sch inputs mems (TcReset x ck ty ro :: tcs) ->
      ~Is_next_in x tcs.
  Proof.
    intros * Sch.
    inversion_clear Sch as [|?? (?&Reset&?)].
    specialize (Reset _ _ (ResetTcReset _ _ _ _)) as (?&?); auto.
  Qed.

  Lemma Is_well_sch_IReset_Step : forall inputs mems i ck f tcs,
      Is_well_sch inputs mems (TcInstReset i ck f :: tcs) ->
      ~Is_step_in i tcs.
  Proof.
    intros * Sch.
    inversion_clear Sch as [|?? (?&?&Steps)].
    eapply Steps. constructor.
  Qed.

  Lemma Is_well_sch_free_Reset : forall inputs mems tcs tc tcs' x,
      Is_well_sch inputs mems ((tcs ++ [tc]) ++ tcs') ->
      Is_free_in_tc x tc ->
      ~exists ck, Is_reset_in x ck (tcs ++ [tc]).
  Proof.
    induction tcs; intros * Wsch Free (ck&Reset); simpl in *;
      inversion_clear Wsch as [|?? (_&Resets&_) Wsch'].
    - inv Reset. 2:inv H0.
      apply Resets in H0 as (NFree&_).
      apply NFree. left; auto.
    - inv Reset.
      + inv H0.
        specialize (Resets _ _ (ResetTcReset _ _ _ _)) as (NFree&_).
        apply NFree. right. repeat rewrite Exists_app'; auto.
      + eapply IHtcs in Wsch'; eauto.
  Qed.

  Lemma Is_well_sch_free_Next: forall inputs mems tcs tc tcs' x,
      PS.mem x mems = true ->
      Is_well_sch inputs mems ((tcs ++ [tc]) ++ tcs') ->
      Is_free_in_tc x tc ->
      ~Is_next_in x tcs'.
  Proof.
    induction tcs; intros * Mems Wsch Free Next; simpl in *;
      inversion_clear Wsch as [|?? (Frees&_&_) Wsch'].
    - eapply Frees in Free. rewrite Mems in Free; auto.
    - eapply IHtcs; eauto.
  Qed.

  Corollary reset_consistency_cons:
    forall tc tcs inputs mems,
      Is_well_sch inputs mems (tc :: tcs) ->
      reset_consistency (tc :: tcs) ->
      reset_consistency tcs.
  Proof.
    setoid_rewrite cons_is_app; intros; eapply reset_consistency_app; eauto.
  Qed.

  (* Lemma Is_well_sch_Step_not_Step: *)
  (*   forall tcs inputs mems i ys ck ckrs f es, *)
  (*     let tcs' := TcStep i ys ck ckrs f es :: tcs in *)
  (*     Is_well_sch inputs mems tcs' -> *)
  (*     reset_consistency tcs' -> *)
  (*     ~ Is_step_in i tcs. *)
  (* Proof. *)
  (*   inversion_clear 1 as [|?? (Free&_&Subs)]; clear Free. *)
  (*   intros * Spec. *)
  (*   split. *)
  (*   - setoid_rewrite Exists_exists. *)
  (*     intros (tc' & Hin & IsStin). *)
  (*     assert (Forall (fun tc => forall ~Is_sub_in_tc i k' tc -> k' < 1) tcs) *)
  (*       by (apply Subs; auto using Is_sub_in_tc). *)
  (*     eapply Forall_forall in Hin; eauto. *)
  (*     apply Hin in IsStin. *)
  (*     lia. *)
  (*   - assert (Step_with_reset_in i rst tcs') as Step by do 2 constructor. *)
  (*     apply Spec in Step. *)
  (*     destruct rst. *)
  (*     + inversion_clear Step as [?? Step'|]; auto; inv Step'. *)
  (*     + intro; apply Step. *)
  (*       right; auto. *)
  (* Qed. *)

End STCWELLDEFINED.

Module StcWellDefinedFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Syn   : STCSYNTAX     Ids Op OpAux Cks CESyn)
       (Syst  : STCISSYSTEM   Ids Op OpAux Cks CESyn Syn)
       (Ord   : STCORDERED    Ids Op OpAux Cks CESyn Syn Syst)
       (Var   : STCISVARIABLE Ids Op OpAux Cks CESyn Syn)
       (Reset : STCISRESET    Ids Op OpAux Cks CESyn Syn)
       (Next  : STCISNEXT     Ids Op OpAux Cks CESyn Syn)
       (CEIsF : CEISFREE      Ids Op OpAux Cks CESyn)
       (Free  : STCISFREE     Ids Op OpAux Cks CESyn Syn CEIsF)
<: STCWELLDEFINED Ids Op OpAux Cks CESyn Syn Syst Ord Var Reset Next CEIsF Free.
  Include STCWELLDEFINED Ids Op OpAux Cks CESyn Syn Syst Ord Var Reset Next CEIsF Free.
End StcWellDefinedFun.
