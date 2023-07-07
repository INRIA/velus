From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Clocks.

From Velus Require Import Stc.StcOrdered.

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
       (Import Ord   : STCORDERED    Ids Op OpAux Cks CESyn Syn)
       (Import CEIsF : CEISFREE      Ids Op OpAux Cks CESyn)
       (Import Free  : STCISFREE     Ids Op OpAux Cks CESyn Syn CEIsF).

  Definition Is_well_sch (inputs: list ident) (mems: list ident) : list trconstr -> Prop :=
    Forall' (fun tcs tc =>
               (* Variables can be used after they are defined *)
               (forall x, Is_free_in_tc (Var x) tc -> Is_defined_in x tcs \/ In x inputs \/ In x mems)
               (* Last variables can only be used before they are updated *)
               /\ (forall x, Is_free_in_tc (Last x) tc -> ~Is_update_last_in x tcs)
               (* State variables can only be used before they are updated *)
               /\ (forall x, Is_free_in_tc (Var x) tc -> ~Is_update_next_in x tcs)
               (* Reset of a state variable must happen before usage and update *)
               /\ (forall x ck, Is_reset_state_in_tc x ck tc ->
                          ~Is_free_in (Last x) (tc::tcs) /\ ~Is_free_in (Var x) (tc::tcs)
                          /\ ~Is_update_last_in x tcs /\ ~Is_update_next_in x tcs)
               (* Idem, reset must happen before steps *)
               /\ (forall s ck, Is_reset_inst_in_tc s ck tc -> ~Is_update_inst_in s tcs)).

  Definition Well_scheduled {prefs} (P: @program prefs) :=
    Forall (fun s => Is_well_sch (map fst (s_in s)) (map fst (s_nexts s)) (s_tcs s)) P.(systems).

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

  Inductive normal_args_tc {prefs} (P: @program prefs) : trconstr -> Prop :=
  | CTcDef:
      forall x ck e,
        normal_args_tc P (TcDef x ck e)
  | CTcReset:
      forall ck resconstr,
        normal_args_tc P (TcReset ck resconstr)
  | CTcUpdateLast:
      forall x ck ckrs e,
        normal_args_tc P (TcUpdate ck ckrs (UpdLast x e))
  | CTcUpdateNext:
      forall x ck ckrs e,
        normal_args_tc P (TcUpdate ck ckrs (UpdNext x e))
  | CTcUpdateInst:
      forall ck ckrs s xs f es b P',
        find_system f P = Some (b, P') ->
        Forall2 noops_exp (map (fun '(_,(_, ck)) => ck) b.(s_in)) es ->
        normal_args_tc P (TcUpdate ck ckrs (UpdInst s xs f es)).
  Global Hint Constructors normal_args_tc : stcsyn.

  Definition normal_args_system {prefs} (P: @program prefs) (s: @system prefs) : Prop :=
    Forall (normal_args_tc P) s.(s_tcs).

  Definition normal_args {prefs} (P: @program prefs) : Prop :=
    Forall' (fun ss => normal_args_system (Program P.(types) P.(externs) ss)) P.(systems).

  Lemma normal_args_system_cons {prefs} :
    forall (system: @system prefs) P enums externs,
      normal_args_system (Program enums externs (system :: P)) system ->
      ~ Is_system_in system.(s_name) system.(s_tcs) ->
      normal_args_system (Program enums externs P) system.
  Proof.
    intros system P enums externs Hnarg Hord.
    apply Forall_forall.
    intros tc Hin.
    destruct tc; eauto with stcsyn. destruct u; try constructor.
    apply Forall_forall with (2:=Hin) in Hnarg.
    inversion_clear Hnarg as [| | | |???????? Hfind Hnargs].
    rewrite find_system_other in Hfind; eauto with stcsyn.
    intro; subst; apply Hord.
    apply Exists_exists.
    eexists; intuition eauto using Is_system_in_tc.
  Qed.

  Definition Well_defined {prefs} (P: @program prefs) : Prop :=
    Ordered_systems P /\ Well_scheduled P /\ normal_args P.

  Lemma last_consistency_app:
    forall tcs tcs' inputs mems,
      Is_well_sch inputs mems (tcs ++ tcs') ->
      last_consistency (tcs ++ tcs') ->
      last_consistency tcs'.
  Proof.
    unfold last_consistency.
    induction tcs as [|[|? []|?? []]]; simpl; auto; intros * Wsch Spec;
      inversion_clear Wsch as [|?? (_&_&_&Lasts&_)];
        try (eapply IHtcs; eauto; intros j ckrs Step' ckr;
             specialize (Spec j ckrs); rewrite Last_with_reset_in_cons_not_last in Spec;
             [|now discriminate]).
    all:try (eapply Spec in Step'; rewrite Step';
             repeat rewrite Is_reset_state_in_reflect; reflexivity).
    - assert (j <> i) as Hneq.
      { assert (Is_reset_state_in_tc i c (TcReset _ _)) as Reset by constructor.
        apply Lasts in Reset as (_&_&Last&_).
        apply Last_with_reset_in_Is_update_last_in in Step'.
        intro contra; subst; eauto. }
      eapply Spec in Step'. rewrite Step'.
      apply ident_eqb_neq in Hneq.
      repeat rewrite Is_reset_state_in_reflect; simpl.
      rewrite Hneq; reflexivity.
    - eapply IHtcs; eauto; intros j ckrs ckr ?.
      assert (Last_with_reset_in j ckrs (TcUpdate c l (UpdLast i c0) :: tcs ++ tcs')) as Step'
          by (right; auto).
      eapply Spec in Step'. rewrite Step'.
      repeat rewrite Is_reset_state_in_reflect. reflexivity.
  Qed.

  Lemma next_consistency_app:
    forall tcs tcs' inputs mems,
      Is_well_sch inputs mems (tcs ++ tcs') ->
      next_consistency (tcs ++ tcs') ->
      next_consistency tcs'.
  Proof.
    unfold next_consistency.
    induction tcs as [|[|? []|?? []]]; simpl; auto; intros * Wsch Spec;
      inversion_clear Wsch as [|?? (_&_&_&Nexts&_)];
        try (eapply IHtcs; eauto; intros j ckrs Step' ckr;
             specialize (Spec j ckrs); rewrite Next_with_reset_in_cons_not_next in Spec;
             [|now discriminate]).
    all:try (eapply Spec in Step'; rewrite Step';
             repeat rewrite Is_reset_state_in_reflect; reflexivity).
    - assert (j <> i) as Hneq.
      { assert (Is_reset_state_in_tc i c (TcReset _ _)) as Reset by constructor.
        apply Nexts in Reset as (_&_&_&Next).
        apply Next_with_reset_in_Is_update_next_in in Step'.
        intro contra; subst; eauto. }
      eapply Spec in Step'. rewrite Step'.
      apply ident_eqb_neq in Hneq.
      repeat rewrite Is_reset_state_in_reflect; simpl.
      rewrite Hneq; reflexivity.
    - eapply IHtcs; eauto; intros j ckrs ckr ?.
      assert (Next_with_reset_in j ckrs (TcUpdate c l (UpdNext i e) :: tcs ++ tcs')) as Step'
          by (right; auto).
      eapply Spec in Step'. rewrite Step'.
      repeat rewrite Is_reset_state_in_reflect. reflexivity.
  Qed.

  Lemma inst_consistency_app:
    forall tcs tcs' inputs mems,
      Is_well_sch inputs mems (tcs ++ tcs') ->
      inst_consistency (tcs ++ tcs') ->
      inst_consistency tcs'.
  Proof.
    unfold inst_consistency.
    induction tcs as [|[|? []|?? []]]; simpl; auto; intros * Wsch Spec;
      inversion_clear Wsch as [|?? (Free&Last&Subs)]; clear Free Last;
        try (eapply IHtcs; eauto; intros j ckrs Step' ckr;
             specialize (Spec j ckrs); rewrite Inst_with_reset_in_cons_not_step in Spec;
             [|now discriminate]).
    all:try (eapply Spec in Step'; rewrite Step';
             repeat rewrite Is_reset_inst_in_reflect; reflexivity).
    - assert (j <> i) as Hneq.
      { assert (Is_reset_inst_in_tc i c (TcReset _ _)) as Sub by constructor.
        apply Subs in Sub.
        apply Inst_with_reset_in_Is_update_inst_in in Step'.
        intro contra; subst. contradiction. }
      eapply Spec in Step'. rewrite Step'.
      apply ident_eqb_neq in Hneq.
      repeat rewrite Is_reset_inst_in_reflect; simpl.
      rewrite Hneq; reflexivity.
    - eapply IHtcs; eauto; intros j r ckr ?.
      eassert (Inst_with_reset_in j r (TcUpdate _ _ _ :: tcs ++ tcs')) as Step'
          by (right; auto).
      eapply Spec in Step'. rewrite Step'.
      repeat rewrite Is_reset_inst_in_reflect. reflexivity.
  Qed.

  (** *** Result of scheduling : Reset constraints always appear before Lasts,
          and Resets always appear before Steps *)

  Lemma Is_well_sch_Reset_Last: forall inputs mems x ck ty ro tcs,
      Is_well_sch inputs mems (TcReset ck (ResState x ty ro) :: tcs) ->
      ~Is_update_last_in x tcs.
  Proof.
    intros * Sch.
    inversion_clear Sch as [|?? (_&_&_&Reset&_)].
    edestruct Reset as (?&?&?&?); eauto. constructor.
  Qed.

  Lemma Is_well_sch_Reset_Next: forall inputs mems x ck ty ro tcs,
      Is_well_sch inputs mems (TcReset ck (ResState x ty ro) :: tcs) ->
      ~Is_update_next_in x tcs.
  Proof.
    intros * Sch.
    inversion_clear Sch as [|?? (_&_&_&Reset&_)].
    edestruct Reset as (?&?&?&?); eauto. constructor.
  Qed.

  Lemma Is_well_sch_Reset_Inst : forall inputs mems i ck f tcs,
      Is_well_sch inputs mems (TcReset ck (ResInst i f) :: tcs) ->
      ~Is_update_inst_in i tcs.
  Proof.
    intros * Sch.
    inversion_clear Sch as [|?? (_&_&_&Steps)].
    eapply Steps. constructor.
  Qed.

  Lemma Is_well_sch_free_Reset : forall inputs mems tcs tc tcs' x,
      Is_well_sch inputs mems ((tcs ++ [tc]) ++ tcs') ->
      Is_free_in_tc (Var x) tc ->
      ~exists ck, Is_reset_state_in x ck (tcs ++ [tc]).
  Proof.
    induction tcs; intros * Wsch Free (ck&Reset); simpl in *;
      inversion_clear Wsch as [|?? (_&_&_&Resets&_) Wsch'].
    - inv Reset. 2:inv H0.
      apply Resets in H0 as (_&NFree&_).
      apply NFree. left; auto.
    - inv Reset.
      + inv H0.
        specialize (Resets _ _ (ResetTcReset _ _ _ _)) as (_&NFree&_).
        apply NFree. right. repeat rewrite Exists_app'; auto.
      + eapply IHtcs in Wsch'; eauto.
  Qed.

  Lemma Is_well_sch_free_ResetLast : forall inputs mems tcs tc tcs' x,
      Is_well_sch inputs mems ((tcs ++ [tc]) ++ tcs') ->
      Is_free_in_tc (Last x) tc ->
      ~exists ck, Is_reset_state_in x ck (tcs ++ [tc]).
  Proof.
    induction tcs; intros * Wsch Free (ck&Reset); simpl in *;
      inversion_clear Wsch as [|?? (_&_&_&Resets&_) Wsch'].
    - inv Reset; inv H0. inv Free.
    - inv Reset.
      + inv H0.
        specialize (Resets _ _ (ResetTcReset _ _ _ _)) as (NFree&_).
        apply NFree. right. unfold Is_free_in. repeat rewrite Exists_app'; auto.
      + eapply IHtcs in Wsch'; eauto.
  Qed.

End STCWELLDEFINED.

Module StcWellDefinedFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Syn   : STCSYNTAX     Ids Op OpAux Cks CESyn)
       (Ord   : STCORDERED    Ids Op OpAux Cks CESyn Syn)
       (CEIsF : CEISFREE      Ids Op OpAux Cks CESyn)
       (Free  : STCISFREE     Ids Op OpAux Cks CESyn Syn CEIsF)
<: STCWELLDEFINED Ids Op OpAux Cks CESyn Syn Ord CEIsF Free.
  Include STCWELLDEFINED Ids Op OpAux Cks CESyn Syn Ord CEIsF Free.
End StcWellDefinedFun.
