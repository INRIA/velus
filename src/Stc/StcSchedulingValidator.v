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
From Velus Require Import FunctionalEnvironment.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Clocks.

From Velus Require Import Stc.StcOrdered.

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
       (Import Ord   : STCORDERED     Ids Op OpAux Cks CESyn Syn)
       (Import CEIsF : CEISFREE       Ids Op OpAux Cks CESyn)
       (Import Free  : STCISFREE      Ids Op OpAux Cks CESyn Syn CEIsF)
       (Import Wdef  : STCWELLDEFINED Ids Op OpAux Cks CESyn Syn Ord CEIsF Free).


  Module PN_as_OT := OrdersEx.PairOrderedType OrdersEx.Positive_as_OT OrdersEx.Nat_as_OT.
  Module PNS := MSetList.Make PN_as_OT.

  Section Decide.

    Open Scope bool_scope.

    Definition validator_state : Type := (bool * (PS.t * PS.t) * PS.t * PS.t * PS.t * PS.t).

    (* A Var should only be used after its definition, and before its next *)
    Definition check_free_var (defs nexts: PS.t) (x: ident) : bool :=
      PS.mem x defs && negb (PS.mem x nexts).

    (* A Last should not be used after its update *)
    Definition check_free_last (upds: PS.t) (x: ident) : bool :=
      negb (PS.mem x upds).

    (* A reset should appear before all usages and its update *)
    Definition check_state_reset (frees freesl defs nexts: PS.t) (x : ident) : bool :=
      negb (PS.mem x freesl) && negb (PS.mem x frees)
      && negb (PS.mem x defs) && negb (PS.mem x nexts).

    (* An instance reset should not appear after the instance update *)
    Definition check_inst_reset (insts: PS.t) (i: ident) : bool :=
        negb (PS.mem i insts).

    Definition update_next_tc (tc: trconstr) : list ident :=
      match tc with
      | TcUpdate _ _ (UpdNext i _) => [i]
      | _ => []
      end.

    Definition update_inst_tc (tc: trconstr) : list ident :=
      match tc with
      | TcUpdate _ _ (UpdInst i _ _ _) => [i]
      | _ => []
      end.

    Definition check_tc (tc: trconstr) (st: validator_state) : validator_state :=
      (* Check free variables *)
      match st with
      | (true, frees, defs, upds, nexts, insts) =>
          let frees' := free_in_tc tc (PS.empty, PS.empty) in
          let frees'' := free_in_tc tc frees in
          let b := PS.for_all (check_free_var defs nexts) (fst frees')
                   && PS.for_all (check_free_last upds) (snd frees') in
          let b := b && forallb (check_state_reset (fst frees'') (snd frees) upds nexts) (state_resets_of [tc]) in
          let defs := ps_adds (defined_tc tc) defs in
          let upds := ps_adds (map fst (lasts_of [tc])) upds in
          let nexts := ps_adds (update_next_tc tc) nexts in
          let b := b && forallb (check_inst_reset insts) (map fst (inst_resets_of [tc])) in
          let insts := ps_adds (update_inst_tc tc) insts in
          (b, frees'', defs, upds, nexts, insts)
      | st => st
      end.

    Definition well_sch (args mems: list ident) (tcs: list trconstr) : bool :=
      fst (fst (fst (fst (fst (fold_right check_tc
                                 (true, (PS.empty, PS.empty), (PS.union (ps_from_list args) (ps_from_list mems)), PS.empty, PS.empty, PS.empty)
                                 tcs))))).

    Lemma check_free_var_spec:
      forall defs nexts x,
        check_free_var defs nexts x = true <-> PS.In x defs /\ ~PS.In x nexts.
    Proof.
      intros. unfold check_free_var.
      rewrite Bool.andb_true_iff, ? Bool.orb_true_iff, Bool.negb_true_iff, ? PS.mem_spec, <-PSF.not_mem_iff, <- ?or_assoc.
      reflexivity.
    Qed.

    Lemma check_free_last_spec:
      forall defs x,
        check_free_last defs x = true <-> ~PS.In x defs.
    Proof.
      intros. unfold check_free_last.
      rewrite Bool.negb_true_iff.
      symmetry. apply PSF.not_mem_iff.
    Qed.

    Lemma check_state_reset_spec:
      forall frees freesl defs nexts i,
        check_state_reset frees freesl defs nexts i = true
        <-> ~PS.In i freesl /\ ~PS.In i frees /\ ~PS.In i defs /\ ~PS.In i nexts.
    Proof.
      intros *. unfold check_state_reset.
      rewrite ? Bool.andb_true_iff, ? Bool.negb_true_iff, <-? PSF.not_mem_iff, ? and_assoc.
      reflexivity.
    Qed.

    Lemma check_inst_reset_spec:
      forall steps i,
        check_inst_reset steps i = true
        <-> ~PS.In i steps.
    Proof.
      intros *. unfold check_inst_reset.
      rewrite PSF.mem_iff, Bool.not_true_iff_false, Bool.negb_true_iff.
      reflexivity.
    Qed.

    Lemma Is_free_in_free_tc1:
      forall tcs frees tc x,
        (forall x, PS.In x (fst frees) <-> Is_free_in (Var x) tcs) ->
        (PS.In x (fst (free_in_tc tc frees)) <-> Is_free_in (Var x) (tc :: tcs)).
    Proof.
      intros * FreeSpec.
      rewrite free_in_tc_spec1, FreeSpec.
      split; intro Hin; (inv Hin; [left|right]); auto.
    Qed.

    Lemma Is_free_in_free_tc2:
      forall tcs frees tc x,
        (forall x, PS.In x (snd frees) <-> Is_free_in (Last x) tcs) ->
        (PS.In x (snd (free_in_tc tc frees)) <-> Is_free_in (Last x) (tc :: tcs)).
    Proof.
      intros * FreeSpec.
      rewrite free_in_tc_spec2, FreeSpec.
      split; intro Hin; (inv Hin; [left|right]); auto.
    Qed.

    Lemma Is_last_in_adds_last_tc:
      forall tcs defs tc x,
        (forall x, PS.In x defs <-> Is_update_last_in x tcs) ->
        (PS.In x (ps_adds (map fst (lasts_of [tc])) defs) <-> Is_update_last_in x (tc :: tcs)).
    Proof.
      intros * Spec. unfold Is_update_last_in.
      rewrite ps_adds_spec, <-lasts_of_In, Spec, Exists_cons.
      apply or_iff_compat_r.
      split; intros In; [apply Exists_singl in In|left]; auto.
    Qed.

    Lemma Is_next_in_adds_next_tc:
      forall tcs nexts tc x,
        (forall x, PS.In x nexts <-> Is_update_next_in x tcs) ->
        (PS.In x (ps_adds (update_next_tc tc) nexts) <-> Is_update_next_in x (tc :: tcs)).
    Proof.
      intros * StepSpec. unfold Is_update_next_in.
      rewrite ps_adds_spec, StepSpec, Exists_cons.
      apply or_iff_compat_r.
      unfold update_next_tc; cases.
      all:split; intros In; inv In; auto with datatypes.
      - constructor.
      - inv H.
    Qed.

    Lemma Is_inst_in_adds_inst_tc:
      forall tcs insts tc x,
        (forall x, PS.In x insts <-> Is_update_inst_in x tcs) ->
        (PS.In x (ps_adds (update_inst_tc tc) insts) <-> Is_update_inst_in x (tc :: tcs)).
    Proof.
      intros * StepSpec. unfold Is_update_inst_in.
      rewrite ps_adds_spec, StepSpec, Exists_cons.
      apply or_iff_compat_r.
      unfold update_inst_tc; cases.
      all:split; intros In; inv In; auto with datatypes.
      - constructor.
      - inv H.
    Qed.

    Lemma Is_defined_in_defined_tc:
      forall tcs args mems vars tc x,
        (forall x, PS.In x vars <-> Is_defined_in x tcs \/ In x args \/ In x mems) ->
        (PS.In x (ps_adds (defined_tc tc) vars) <-> Is_defined_in x (tc :: tcs) \/ In x args \/ In x mems).
    Proof.
      intros * VarSpec; split; intro Hin;
        [apply ps_adds_spec in Hin as [|]|apply ps_adds_spec; inv Hin];
        try (now right; apply VarSpec; auto); auto.
      - rewrite Is_defined_in_defined; simpl.
        rewrite in_app; intuition.
      - rewrite Is_defined_in_defined; simpl.
        rewrite in_app.
        apply VarSpec in H as [|]; intuition.
        rewrite <-Is_defined_in_defined; intuition.
      - rewrite Is_defined_in_defined in H; simpl in H;
          rewrite in_app in H; destruct H; intuition.
        rewrite <-Is_defined_in_defined in H.
        right; apply VarSpec; auto.
    Qed.

    Opaque state_resets_of lasts_of inst_resets_of.

    Lemma well_sch_pre_spec:
      forall inputs mems tcs ok frees defs upds nexts insts,
        fold_right check_tc (true,
            (PS.empty, PS.empty),
            (PS.union (ps_from_list inputs) (ps_from_list mems)),
            PS.empty,
            PS.empty,
            PS.empty) tcs = (ok, frees, defs, upds, nexts, insts) ->
        if ok
        then
          Is_well_sch inputs mems tcs
          /\ (forall x, PS.In x (fst frees) <-> Is_free_in (Var x) tcs)
          /\ (forall x, PS.In x (snd frees) <-> Is_free_in (Last x) tcs)
          /\ (forall x, PS.In x defs <-> Is_defined_in x tcs \/ In x inputs \/ In x mems)
          /\ (forall x, PS.In x upds <-> Is_update_last_in x tcs)
          /\ (forall x, PS.In x nexts <-> Is_update_next_in x tcs)
          /\ (forall i, PS.In i insts <-> Is_update_inst_in i tcs)
        else
          ~Is_well_sch inputs mems tcs.
    Proof.
      induction tcs as [|tc].
      - simpl; inversion_clear 1; simpl.
        split; [|split; [|split; [|split; [|split; [|split]]]]].
        all:(intros; unfold Is_free_in, Is_defined_in, Is_update_last_in, Is_update_next_in, Is_update_inst_in;
             rewrite ?PSF.empty_iff, ?PSF.union_iff, ?In_of_list, ?Exists_nil, ?ps_from_list_In).
        all:try reflexivity.
        + constructor.
        + split; [intros|intros [[]|]]; auto.
      - simpl; intros * HH.
        destruct (fold_right check_tc (true, (PS.empty, PS.empty), _, _, _, _) tcs)
          as [[[[[ok' frees'] defs'] upds'] nexts'] steps'].
        specialize (IHtcs _ _ _ _ _ _ eq_refl).
        simpl in HH.
        destruct ok'; inv HH.
        + destruct IHtcs as (Wsch & FreeSpec & LastSpec & DefSpec & UpdSpec & NextSpec & InstSpec).
          assert (forall x, PS.In x (fst (free_in_tc tc frees')) <-> Is_free_in (Var x) (tc :: tcs)) as FreeSpec'
            by (intros; eapply Is_free_in_free_tc1; eauto).
          assert (forall x, PS.In x (snd (free_in_tc tc frees')) <-> Is_free_in (Last x) (tc :: tcs)) as LastSpec'
            by (intros; eapply Is_free_in_free_tc2; eauto).
          assert (forall x, PS.In x (ps_adds (defined_tc tc) defs') <-> Is_defined_in x (tc :: tcs) \/ In x inputs \/ In x mems)
            by (intros; eapply Is_defined_in_defined_tc; eauto).
          assert (forall x, PS.In x (ps_adds (map fst (lasts_of [tc])) upds') <-> Is_update_last_in x (tc :: tcs))
            by (intros; apply Is_last_in_adds_last_tc; auto).
          assert (forall x, PS.In x (ps_adds (update_next_tc tc) nexts') <-> Is_update_next_in x (tc :: tcs))
            by (intros; apply Is_next_in_adds_next_tc; auto).
          assert (forall x, PS.In x (ps_adds (update_inst_tc tc) steps') <-> Is_update_inst_in x (tc :: tcs))
            by (intros; eapply Is_inst_in_adds_inst_tc; eauto).
          cases_eqn E.
          *{ repeat (split; auto).
             repeat rewrite Bool.andb_true_iff in E. destruct E as (((E1 & E2) & E3) & E4).
             constructor; auto.
             split; [|split; [|split; [|split]]]; auto.
             - apply PS.for_all_spec in E1. 2:intros ?? Eq; inv Eq; auto.
               intros * In. rewrite <-DefSpec.
               eapply or_introl, free_in_tc_spec1, E1, check_free_var_spec in In as (?&?); eauto.
             - apply PS.for_all_spec in E2. 2:intros ?? Eq; inv Eq; auto.
               intros * In1 In2. eapply check_free_last_spec.
               + eapply E2. eapply or_introl, free_in_tc_spec2 in In1; eauto.
               + apply UpdSpec; auto.
             - apply PS.for_all_spec in E1. 2:intros ?? Eq; inv Eq; auto.
               intros * In1 In2. rewrite <-NextSpec in In2.
               eapply or_introl, free_in_tc_spec1, E1, check_free_var_spec in In1 as (?&?); eauto.
             - intros * In1.
               eapply forallb_Forall, Forall_forall in E3.
               2:apply reset_states_of_In; esplit; left; eauto. inv In1.
               rewrite check_state_reset_spec, LastSpec, FreeSpec', UpdSpec, NextSpec, ?not_or' in E3.
               destruct E3 as (Nlast&Nfree&Nupd&Nnext). repeat (split; auto).
               + contradict Nlast. inv Nlast; auto. inv H4.
             - intros * In1 In2.
               eapply forallb_Forall, Forall_forall in E4.
               2:apply reset_insts_of_In; esplit; left; eauto.
               eapply check_inst_reset_spec; eauto. apply InstSpec; auto.
           }
          *{ intro contra. inv contra. clear H6. destruct H5 as (Free&Last&Next&ResetLast&ResetInst).
             repeat rewrite Bool.andb_false_iff in E. destruct E as [[[E1|E1]|E1]|E1].
             all:eapply Bool.not_true_iff_false; eauto.
             - apply PS.for_all_spec. intros ?? Eq; inv Eq; auto.
               intros ? In. rewrite check_free_var_spec, DefSpec, NextSpec.
               eapply free_in_tc_spec1 in In as [In|In]; [|apply not_In_empty in In as []].
               split; auto.
             - apply PS.for_all_spec. intros ?? Eq; inv Eq; auto.
               intros ? In. apply free_in_tc_spec2', Last in In.
               rewrite check_free_last_spec, UpdSpec; auto.
             - apply forallb_Forall. simpl_Forall.
               eapply reset_states_of_In in H3 as (?&In). apply Exists_singl in In.
               apply ResetLast in In as (Last'&?&?&?).
               rewrite check_state_reset_spec, LastSpec, FreeSpec', UpdSpec, NextSpec. repeat split; auto.
               + contradict Last'. now right.
             - apply forallb_Forall. simpl_Forall.
               eapply in_map, reset_insts_of_In in H3 as (?&In). apply Exists_singl in In.
               rewrite check_inst_reset_spec, InstSpec.
               eapply ResetInst; eauto.
           }

        + inversion 1; auto.
    Qed.

    Theorem well_sch_spec:
      forall args mems tcs,
        if well_sch args mems tcs
        then Is_well_sch args mems tcs
        else ~ Is_well_sch args mems tcs.
    Proof.
      intros.
      pose proof (well_sch_pre_spec args mems tcs) as Spec.
      unfold well_sch.
      destruct (fold_right check_tc
                  (true, (PS.empty, PS.empty), PS.union (ps_from_list args) (ps_from_list mems), PS.empty, PS.empty, PS.empty) tcs)
        as [[[[[ok frees] defs] upds] nexts] insts]; simpl.
      specialize (Spec ok frees defs upds nexts insts eq_refl).
      destruct ok; intuition.
    Qed.

    Lemma Is_well_sch_by_refl:
      forall args mems tcs,
        well_sch args mems tcs = true <-> Is_well_sch args mems tcs.
    Proof.
      intros.
      pose proof (well_sch_spec args mems tcs) as Hwss.
      split; intro H.
      rewrite H in Hwss; assumption.
      destruct (well_sch args mems tcs); [reflexivity|].
      exfalso; apply Hwss; apply H.
    Qed.

    Lemma well_sch_dec:
      forall args mems tcs,
        {Is_well_sch args mems tcs} + {~ Is_well_sch args mems tcs}.
    Proof.
      intros.
      pose proof (well_sch_spec args mems tcs) as Hwss.
      destruct (well_sch args mems tcs); [left|right]; assumption.
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
       (Ord   : STCORDERED     Ids Op OpAux Cks CESyn Syn)
       (CEIsF : CEISFREE       Ids Op OpAux Cks CESyn)
       (Free  : STCISFREE      Ids Op OpAux Cks CESyn Syn CEIsF)
       (Wdef  : STCWELLDEFINED Ids Op OpAux Cks CESyn Syn Ord CEIsF Free)
<: STCSCHEDULINGVALIDATOR Ids Op OpAux Cks CESyn Syn Ord CEIsF Free Wdef.
  Include STCSCHEDULINGVALIDATOR Ids Op OpAux Cks CESyn Syn Ord CEIsF Free Wdef.
End StcSchedulingValidatorFun.
