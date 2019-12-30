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

From Velus Require Import Stc.StcWellDefined.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Omega.

Module Type STCSCHEDULINGVALIDATOR
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX           Op)
       (Import Syn   : STCSYNTAX      Ids Op CESyn)
       (Import Syst  : STCISSYSTEM    Ids Op CESyn Syn)
       (Import Ord   : STCORDERED     Ids Op CESyn Syn Syst)
       (Import Var   : STCISVARIABLE  Ids Op CESyn Syn)
       (Import Init  : STCISINIT      Ids Op CESyn Syn)
       (Import Def   : STCISDEFINED   Ids Op CESyn Syn Var Init)
       (Import CEIsF : CEISFREE       Ids Op CESyn)
       (Import Free  : STCISFREE      Ids Op CESyn Syn CEIsF)
       (Import Wdef  : STCWELLDEFINED Ids Op CESyn Syn Syst Ord Var Init Def CEIsF Free).


  Module PN_as_OT := OrdersEx.PairOrderedType OrdersEx.Positive_as_OT OrdersEx.Nat_as_OT.
  Module PNS := MSetList.Make PN_as_OT.

  Section Decide.

    Variable mems : PS.t.

    (* TODO: rewrite using a strong specification?  *)

    Open Scope bool_scope.

    Definition check_var (defined: PS.t) (variables: PS.t) (x: ident) : bool :=
      if PS.mem x mems then negb (PS.mem x defined) else PS.mem x variables.

    Definition sub_tc (tc: trconstr) : option (ident * nat) :=
      match tc with
      | TcReset i _ _      => Some (i, 0)
      | TcCall i _ _ _ _ _ => Some (i, 1)
      | _ => None
      end.

    Definition check_sub (i: ident) (k: nat) (ik': ident * nat) : bool :=
      negb (ident_eqb (fst ik') i) || Nat.ltb (snd ik') k.

    Definition check_tc (tc: trconstr) (acc: bool * PS.t * PS.t * PNS.t)
      : bool * PS.t * PS.t * PNS.t :=
      match acc with
      | (true, defs, vars, subs) =>
        let b := PS.for_all (check_var defs vars) (free_in_tc tc PS.empty) in
        let defs := ps_adds (defined_tc tc) defs in
        let vars := ps_adds (variables_tc tc) vars in
        match sub_tc tc with
        | Some (i, k) =>
          (PNS.for_all (check_sub i k) subs && b, defs, vars, PNS.add (i, k) subs)
        | None => (b, defs, vars, subs)
        end
      | acc => acc
      end.

    Definition is_well_sch_tcs (args: list ident) (tcs: list trconstr) : bool :=
      fst (fst (fst (fold_right check_tc
                                (true, PS.empty, ps_from_list args, PNS.empty)
                                tcs))).

    Lemma check_var_spec:
      forall defined variables x,
        check_var defined variables x = true
        <->
        (PS.In x mems -> ~PS.In x defined)
        /\ (~PS.In x mems -> PS.In x variables).
    Proof.
      (*  TODO: how to automate all of this? *)
      intros defined variables x.
      unfold check_var.
      split.
      - intro Hif.
        split; intro Hin.
        + apply PS.mem_spec in Hin.
          rewrite Hin, Bool.negb_true_iff in Hif.
          apply PSP.Dec.F.not_mem_iff in Hif. exact Hif.
        + apply PSP.Dec.F.not_mem_iff in Hin.
          rewrite Hin, PS.mem_spec in Hif. exact Hif.
      - destruct 1 as [Hin Hnin].
        destruct PSP.In_dec with x mems as [H|H].
        + assert (PS.mem x mems = true) as H' by auto.
          rewrite H', Bool.negb_true_iff, <-PSP.Dec.F.not_mem_iff.
          now apply Hin with (1:=H).
        + assert (PS.mem x mems = false) as H' by now apply PSP.Dec.F.not_mem_iff.
          rewrite H', PS.mem_spec.
          now apply Hnin with (1:=H).
    Qed.

    Lemma Is_sub_in_sub_tc:
      forall tc i k,
        Is_sub_in_tc i k tc <-> sub_tc tc = Some (i, k).
    Proof.
      destruct tc; simpl; split; try inversion_clear 1; auto using Is_sub_in_tc.
    Qed.

    Lemma check_sub_spec:
      forall i k i' k',
        check_sub i k (i', k') = true
        <->
        (i = i' -> k' < k).
    Proof.
      intros; unfold check_sub; simpl.
      split.
      - intros * E Tc; subst.
        rewrite ident_eqb_refl in E.
        apply Nat.ltb_lt; auto.
      - intros Spec.
        destruct (ident_eqb i' i) eqn: E; auto.
        apply Nat.ltb_lt, Spec.
        symmetry; apply ident_eqb_eq; auto.
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

    Lemma pair_tc:
      forall A B (x y: A * B),
        RelationPairs.RelProd Logic.eq Logic.eq x y <-> x = y.
    Proof.
      split; intros * E; subst; auto.
      destruct x, y.
      inversion_clear E as [Fst Snd]; inv Fst; inv Snd; simpl in *; subst; auto.
    Qed.

    Lemma PNS_compat:
      forall A (f: (positive * nat) -> A),
        Morphisms.Proper (Morphisms.respectful (RelationPairs.RelProd Logic.eq Logic.eq) Logic.eq) f.
    Proof.
      intros * x y E.
      apply pair_tc in E; subst; auto.
    Qed.
    Hint Resolve PNS_compat.

    Lemma PNS_not_for_all_spec:
      forall (s : PNS.t) (f : positive * nat -> bool),
        PNS.for_all f s = false <-> ~ PNS.For_all (fun x => f x = true) s.
    Proof.
      split.
      - intros Hfa HFa.
        apply PNS.for_all_spec in HFa; auto.
        rewrite Hfa in HFa.
        discriminate.
      - intro HFa.
        apply Bool.not_true_iff_false.
        intro Hfa; apply HFa.
        apply PNS.for_all_spec; auto.
    Qed.

    Lemma free_spec:
      forall tcs args defs vars tc x,
        (forall x, PS.In x defs <-> Is_defined_in x tcs) ->
        (forall x, PS.In x vars <-> Is_variable_in x tcs \/ In x args) ->
        PS.For_all (fun x => check_var defs vars x = true) (free_in_tc tc PS.empty) ->
        Is_free_in_tc x tc ->
        if PS.mem x mems then ~ Is_defined_in x tcs else Is_variable_in x tcs \/ In x args.
    Proof.
      intros * DefSpec VarSpec E Hfree.
      apply free_in_tc_spec', E, check_var_spec in Hfree as (Hin & Hnin).
      destruct (PS.mem x mems) eqn: Mem.
      - rewrite <-DefSpec; apply PSE.MP.Dec.F.mem_iff, Hin in Mem; auto.
      - rewrite <-VarSpec; apply PSE.MP.Dec.F.not_mem_iff, Hnin in Mem; auto.
    Qed.

    Lemma def_spec:
      forall tcs defs tc x,
        (forall x, PS.In x defs <-> Is_defined_in x tcs) ->
        existsb (fun x => PS.mem x defs) (defined_tc tc) = false ->
        Is_defined_in_tc x tc ->
        ~ Is_defined_in x tcs.
    Proof.
      intros * DefSpec E Hdef Hdefs.
      apply DefSpec in Hdefs; apply Is_defined_in_defined_tc in Hdef.
      apply In_nth with (d := Ids.default) in Hdef as (?&?&?); subst.
      eapply existsb_nth with (d := Ids.default) in E; eauto.
      apply PSE.MP.Dec.F.not_mem_iff in E; auto.
    Qed.

    Lemma check_var_compat:
      forall defined variables,
        SetoidList.compat_bool PS.E.eq (check_var defined variables).
    Proof.
      intros defined variables x y Htc.
      unfold PS.E.eq in Htc.
      rewrite Htc.
      reflexivity.
    Qed.
    Hint Resolve check_var_compat.

    Lemma not_well_sch_vars_defs_spec:
      forall tcs args defs vars tc,
        (forall x, PS.In x defs <-> Is_defined_in x tcs) ->
        (forall x, PS.In x vars <-> Is_variable_in x tcs \/ In x args) ->
        PS.for_all (check_var defs vars) (free_in_tc tc PS.empty) = false ->
        ~ Is_well_sch args mems (tc :: tcs).
    Proof.
      intros * DefSpec VarSpec E Wsch.
      inversion_clear Wsch as [|??? Hfree Hdefs].
      apply PS_not_for_all_spec in E; auto.
      apply E; intros x Hin; apply free_in_tc_spec' in Hin.
      apply Hfree in Hin.
      apply check_var_spec; split.
      - rewrite PSE.MP.Dec.F.mem_iff; intro Hin'; rewrite Hin' in Hin.
        now rewrite DefSpec.
      - rewrite PSE.MP.Dec.F.not_mem_iff; intro Hin'; rewrite Hin' in Hin.
        now rewrite VarSpec.
    Qed.

    Lemma Is_defined_in_adds_defined_tc:
      forall tcs defs tc x,
        (forall x, PS.In x defs <-> Is_defined_in x tcs) ->
        (PS.In x (ps_adds (defined_tc tc) defs) <-> Is_defined_in x (tc :: tcs)).
    Proof.
      intros * DefSpec; split; intro Hin;
        [apply ps_adds_spec in Hin as [|]|apply ps_adds_spec; inv Hin];
        try (now left; apply Is_defined_in_defined_tc; auto);
        try (now right; apply DefSpec; auto); auto.
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
      forall args tcs ok defs vars subs,
        fold_right check_tc (true,
                             PS.empty,
                             ps_from_list args,
                             PNS.empty) tcs = (ok, defs, vars, subs) ->
        if ok
        then
          Is_well_sch args mems tcs
          /\ (forall x, PS.In x defs <-> Is_defined_in x tcs)
          /\ (forall x, PS.In x vars <-> Is_variable_in x tcs \/ In x args)
          /\ (forall i k, PNS.In (i, k) subs <-> Is_sub_in i k tcs)
        else
          ~Is_well_sch args mems tcs.
    Proof.
      induction tcs as [|tc].
      - simpl; inversion_clear 1; intuition; try (now constructor);
          repeat match goal with
                 | H:PS.In _ PS.empty |- _ => apply PS.empty_spec in H; contradiction
                 | H:PNS.In _ PNS.empty |- _ => apply PNS.empty_spec in H; contradiction
                 | H:Is_defined_in _ nil |- _ => inversion H
                 | H:Is_variable_in _ nil |- _ => inversion H
                 | H:Is_sub_in _ _ nil |- _ => inversion H
                 | H: context[ps_from_list _] |- _ =>
                   apply ps_from_list_In in H
                 | _ => intuition
                 end.
        apply ps_from_list_In; auto.
      - simpl; intros * HH.
        destruct (fold_right check_tc (true, PS.empty, ps_from_list args, PNS.empty) tcs)
          as [[[ok' defs'] vars'] subs'].
        specialize (IHtcs ok' defs'  vars' subs' eq_refl).
        simpl in HH.
        destruct ok'.
        + destruct IHtcs as (Wsch & DefSpec & VarSpec & SubSpec).
          assert (forall x, PS.In x (ps_adds (defined_tc tc) defs') <-> Is_defined_in x (tc :: tcs))
            by (intros; eapply Is_defined_in_adds_defined_tc; eauto).
          assert (forall x, PS.In x (ps_adds (variables_tc tc) vars') <-> Is_variable_in x (tc :: tcs) \/ In x args)
            by (intros; eapply Is_variable_in_variables_tc; eauto).
          destruct (sub_tc tc) as [(i, k)|] eqn: St.
          *{ destruct ok; inversion HH as [E]; clear HH.
             - apply Bool.andb_true_iff in E as (E & E').
               apply PNS.for_all_spec in E; auto.
               apply PS.for_all_spec in E'; auto.
               split; [|split; [|split]]; auto.
               + constructor; auto.
                 * intros; eapply free_spec; eauto.
                 * intros * Hin; apply Is_sub_in_sub_tc in Hin; rewrite Hin in St; inv St.
                   apply Forall_forall; intros.
                   assert (Is_sub_in i k' tcs) as Hst
                       by (apply Exists_exists; eexists; intuition; eauto).
                   apply SubSpec in Hst; apply E in Hst.
                   apply check_sub_spec in Hst; auto.
               + rewrite <-Is_sub_in_sub_tc in St.
                 intros i' k'; split; rewrite PNS.add_spec.
                 *{ intros [Tc|Hin].
                    - apply pair_tc in Tc; inv Tc; left; auto.
                    - apply SubSpec in Hin; right; auto.
                  }
                 *{ rewrite pair_tc; inversion_clear 1 as [?? St'|].
                    - inv St; inv St'; auto.
                    - right; apply SubSpec; auto.
                  }

             - apply Bool.andb_false_iff in E as [E|];
                 [|eapply not_well_sch_vars_defs_spec; eauto].
               inversion_clear 1 as [|???? Hsubs].
               rewrite <-Is_sub_in_sub_tc in St.
               apply Hsubs in St.
               apply PNS_not_for_all_spec in E; apply E; clear E.
               intros (i', k') Hin.
               apply check_sub_spec; intros; subst.
               apply SubSpec in Hin.
               eapply Forall_Exists, Exists_exists in Hin as (?&?& Spec & St'); eauto; auto.
           }
          *{ destruct ok; inversion HH as [E].
             - apply PS.for_all_spec in E; try apply check_var_compat.
               split; [|split; [|split]]; auto.
               + constructor; auto.
                 * intros; eapply free_spec; eauto.
                 * intros * Hin; apply Is_sub_in_sub_tc in Hin; rewrite Hin in St; inv St.
               + subst; setoid_rewrite SubSpec.
                 split.
                 * right; auto.
                 * rewrite <-not_Some_is_None in St.
                   specialize (St (i, k)).
                   rewrite <-Is_sub_in_sub_tc in St.
                   inversion 1; auto; contradiction.
             - eapply not_well_sch_vars_defs_spec; eauto.
           }

        + inv HH; inversion 1; auto.
    Qed.

    Theorem well_sch_spec:
      forall args tcs,
        if is_well_sch_tcs args tcs
        then Is_well_sch args mems tcs
        else ~ Is_well_sch args mems tcs.
    Proof.
      intros.
      pose proof (well_sch_pre_spec args tcs) as Spec.
      unfold is_well_sch_tcs.
      destruct (fold_right check_tc
                  (true, PS.empty, ps_from_list args, PNS.empty) tcs)
        as [[[ok defs] vars] subs]; simpl.
      specialize (Spec ok defs vars subs eq_refl).
      destruct ok; intuition.
    Qed.

    Corollary Is_well_sch_by_refl:
      forall args tcs,
        is_well_sch_tcs args tcs = true <-> Is_well_sch args mems tcs.
    Proof.
      intros.
      pose proof (well_sch_spec args tcs) as Hwss.
      split; intro H.
      rewrite H in Hwss; assumption.
      destruct (is_well_sch_tcs args tcs); [reflexivity|].
      exfalso; apply Hwss; apply H.
    Qed.

    Corollary well_sch_dec:
      forall args tcs,
        {Is_well_sch args mems tcs} + {~ Is_well_sch args mems tcs}.
    Proof.
      intros.
      pose proof (well_sch_spec args tcs) as Hwss.
      destruct (is_well_sch_tcs args tcs); [left|right]; assumption.
    Qed.

  End Decide.

End STCSCHEDULINGVALIDATOR.

Module StcSchedulingValidatorFun
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
       (Wdef  : STCWELLDEFINED Ids Op CESyn Syn Syst Ord Var Init Def CEIsF Free)
<: STCSCHEDULINGVALIDATOR Ids Op CESyn Syn Syst Ord Var Init Def CEIsF Free Wdef.
  Include STCSCHEDULINGVALIDATOR Ids Op CESyn Syn Syst Ord Var Init Def CEIsF Free Wdef.
End StcSchedulingValidatorFun.
