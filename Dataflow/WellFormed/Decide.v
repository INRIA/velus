Require Import Rustre.Common.
Require Import Rustre.Operators.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.IsFree.
Require Import Rustre.Dataflow.IsFree.Decide.
Require Import Rustre.Dataflow.IsVariable.
Require Import Rustre.Dataflow.IsVariable.Decide.
Require Import Rustre.Dataflow.IsDefined.
Require Import Rustre.Dataflow.IsDefined.Decide.
Require Import Rustre.Dataflow.WellFormed.

Require Import Rustre.Dataflow.Ordered.
Require Import Rustre.Dataflow.Memories.
Require Import Rustre.Dataflow.NoDup.

Require Import List.

(** * Well formed CoreDF programs: decision procedure *)

(** 

Decision procedure for the [Is_well_sch] predicate. We show that it is
equivalent to its specification.

Remark: This development is not formally part of the correctness proof.

 *)

Module Type DECIDE
       (Ids           : IDS)
       (Op            : OPERATORS)
       (Import Syn    : SYNTAX Ids Op)
       (IsF           : ISFREE Ids Op Syn)
       (Import IsFDec : IsFree.Decide.DECIDE Ids Op Syn IsF)
       (Import Ord    : ORDERED Ids Op Syn)
       (Import Mem    : MEMORIES Ids Op Syn)
       (Import IsD    : ISDEFINED Ids Op Syn Mem)
       (Import IsV    : ISVARIABLE Ids Op Syn Mem IsD)
       (Import IsDDec : IsDefined.Decide.DECIDE Ids Op Syn Mem IsD)
       (Import IsVDec : IsVariable.Decide.DECIDE Ids Op Syn Mem IsD IsV)
       (Import NoD    : NODUP Ids Op Syn Mem IsD IsV)
       (Import Wef    : WELLFORMED Ids Op Syn IsF Ord Mem IsD IsV NoD).

  Section Decide.

    Variable mems : PS.t.

    (* TODO: rewrite using a strong specification?  *)

    Open Scope bool_scope.

    Definition check_var (defined: PS.t) (variables: PS.t) (x: ident) : bool :=
      if PS.mem x mems
      then negb (PS.mem x defined)
      else PS.mem x variables.

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
          apply mem_spec_false in Hif. exact Hif.
        + apply mem_spec_false in Hin.
          rewrite Hin, PS.mem_spec in Hif. exact Hif.
      - destruct 1 as [Hin Hnin].
        destruct Common.In_dec with x mems as [H|H].
        + assert (PS.mem x mems = true) as H' by auto.
          rewrite H', Bool.negb_true_iff, mem_spec_false.
          now apply Hin with (1:=H).
        + assert (PS.mem x mems = false) as H' by now apply mem_spec_false.
          rewrite H', PS.mem_spec.
          now apply Hnin with (1:=H).
    Qed.

    Definition check_eq (eq: equation) (acc: bool*PS.t*PS.t)
      : bool*PS.t*PS.t :=
      match acc with
      | (true, defined, variables) =>
        match var_defined eq with
        | x => ((PS.for_all (check_var defined variables)
                            (free_in_equation eq PS.empty))
                  && (negb (PS.mem x defined)),
                PS.add x defined, variable_eq variables eq)
        end
      | (false, _, _) => (false, PS.empty, PS.empty)
      end.

    Definition well_sch (args: list ident) (eqs: list equation) : bool :=
      fst (fst (List.fold_right check_eq
                                (true,
                                 PS.empty,
                                 fold_left (fun a b => PS.add b a) args PS.empty)
                                eqs)).

    Lemma not_for_all_spec:
      forall (s : PS.t) (f : BinNums.positive -> bool),
        SetoidList.compat_bool PS.E.eq f ->
        (PS.for_all f s = false <-> ~(PS.For_all (fun x : PS.elt => f x = true) s)).
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

    Lemma check_var_compat:
      forall defined variables,
        SetoidList.compat_bool PS.E.eq (check_var defined variables).
    Proof.
      intros defined variables x y Heq.
      unfold PS.E.eq in Heq.
      rewrite Heq.
      reflexivity.
    Qed.

    Lemma in_fold_left_add:
      forall x xs S,
        PS.In x (fold_left (fun S' x => PS.add x S') xs S)
        <->
        In x xs \/ PS.In x S.
    Proof.
      induction xs as [|y xs IH].
      split; intro H; simpl in *;
        intuition.
      intro S; split; intro H.
      - apply IH in H.
        destruct H.
        now left; constructor (assumption).
        apply PS.add_spec in H; simpl; intuition.
      - simpl; apply IH; simpl in H; intuition.
    Qed.

    Lemma well_sch_pre_spec:
      forall args eqs good defined variables,
        (good, defined, variables)
        = List.fold_right check_eq (true, PS.empty,
                            fold_left (fun a b => PS.add b a) args PS.empty) eqs
        ->
        (good = true
         -> (Is_well_sch mems args eqs
             /\ (forall x, PS.In x defined <-> Is_defined_in_eqs x eqs)
             /\ (forall x, PS.In x variables <->
                              Is_variable_in_eqs x eqs \/ In x args)))
        /\ (good = false -> ~Is_well_sch mems args eqs).
    Proof.
      induction eqs as [|eq].
      - (* case nil: *)
        simpl. injection 1. intros.
        subst variables0; subst defined0; subst good.
        intuition;
          repeat match goal with
                 | H:PS.In _ PS.empty |- _ => apply PS.empty_spec in H; contradiction
                 | H:Is_defined_in_eqs _ nil |- _ => inversion H
                 | H:Is_variable_in_eqs _ nil |- _ => inversion H
                 | H: context[fold_left _ _ _] |- _ =>
                   apply in_fold_left_add in H
                 | _ => intuition
                 end.
        apply in_fold_left_add; auto.
      - (* case cons: *)
        intros good defined variables HH.
        destruct (fold_right check_eq (true, PS.empty,
                    fold_left (fun (a : PS.t) (b : positive) => PS.add b a)
                              args PS.empty) eqs)
          as [[good' defined'] variables'] eqn:Heq.
        specialize IHeqs with good' defined' variables'.
        pose proof (IHeqs (eq_refl (good', defined', variables'))) as IH;
          clear IHeqs.
        destruct IH as [IHt IHf].
        split; intro Hg; rewrite Hg in *; clear Hg.
        + (* good=true *)
          simpl in HH; rewrite Heq in HH.
          simpl in HH.
          destruct good'; [|discriminate].
          specialize (IHt eq_refl).
          clear IHf; destruct IHt as [IHwsch [IHdef IHvar]].
          injection HH; clear HH; intros Hv Hd H.
          subst variables; subst defined.
          symmetry in H.
          apply Bool.andb_true_iff in H.
          destruct H as [H1 H2].
          apply PS.for_all_spec in H1; [|now apply check_var_compat].
          apply Bool.negb_true_iff in H2.
          apply mem_spec_false in H2.
          split; [|split].
          * (* Is_well_sch *)
            constructor.
            assumption.
            intros x Hfree.
            apply free_in_equation_spec' in Hfree.
            apply H1 in Hfree.
            apply check_var_spec in Hfree.
            destruct Hfree as [Hfree1 Hfree2].
            split; intro HH; (apply Hfree1 in HH || apply Hfree2 in HH).
            intro Hdef; apply IHdef in Hdef; apply HH; assumption.
            apply IHvar; assumption.
            intros x Hdef Hdefs; apply IHdef in Hdefs.
            apply Is_defined_in_eqs_var_defined in Hdef.
            rewrite Hdef in *. auto.
          * (* defined set *)
            intro x; split; intro HH.
            apply PS.add_spec in HH.
            destruct HH as [HH|HH].
            subst x; constructor; now apply Is_defined_in_eqs_var_defined.
            apply IHdef in HH.
            constructor (assumption).
            apply PS.add_spec.
            inversion_clear HH.
            apply Is_defined_in_eqs_var_defined in H; subst x; auto.
            right; apply IHdef; assumption.
          * (* variables set *)
            intro x; split; intro HH.
            apply variable_eq_empty in HH.
            destruct HH as [HH|HH].
            destruct eq;
              ((apply PS.add_spec in HH;
                destruct HH as [HH|HH];
                [subst i; left; now repeat constructor
                |apply PS.empty_spec in HH; contradiction])
               || apply PS.empty_spec in HH; contradiction).
            apply IHvar in HH; intuition; left; constructor (assumption).
            apply variable_eq_empty.
            destruct HH as [HH|HH].
            apply Is_variable_in_cons in HH.
            destruct HH as [HH|HH]; [left|right].
            destruct eq; inversion_clear HH; simpl; now intuition.
            apply IHvar; intuition.
            right; apply IHvar; auto.
        + (* good=false *)
          intro Hwsch.
          simpl in HH; rewrite Heq in HH; clear Heq; simpl in HH.
          destruct good'; [specialize (IHt eq_refl); clear IHf
                          | specialize (IHf eq_refl);
                            apply Is_well_sch_cons in Hwsch;
                            apply IHf with (1:=Hwsch)].
          destruct IHt as [_ [IHdef IHvar]].
          injection HH; clear HH; intros Hv Hd HH.
          subst variables; subst defined; symmetry in HH.
          apply Bool.andb_false_iff in HH.
          inversion_clear Hwsch as [|Ha Hb Hwschs Hfree Hdefd].
          destruct HH as [HH|HH].
          * (* check_var of free fails *)
            apply not_for_all_spec in HH; [|apply check_var_compat].
            apply HH; clear HH.
            intros x HH.
            apply free_in_equation_spec in HH.
            destruct HH as [HH|HH]; [|apply PS.empty_spec in HH].
            apply Hfree in HH.
            destruct HH as [Hmem Hvar];
              apply check_var_spec; split; intro HHm;
                (specialize (Hmem HHm) || specialize (Hvar HHm)).
            intro Hdef; apply IHdef in Hdef; apply Hmem; assumption.
            apply IHvar; intuition.
            contradiction.
          * (* already defined *)
            apply Bool.negb_false_iff in HH.
            rewrite PS.mem_spec in HH.
            apply Hdefd with (i:=var_defined eq).
            apply Is_defined_in_eqs_var_defined; reflexivity.
            apply IHdef; assumption.
    Qed.
    
    Lemma well_sch_spec:
      forall args eqns,
        if well_sch args eqns
        then Is_well_sch mems args eqns
        else ~Is_well_sch mems args eqns.
    Proof.
      intros args eqns.
      pose proof (well_sch_pre_spec args eqns).
      unfold well_sch.
      destruct (fold_right check_eq
                  (true, PS.empty,
                   fold_left (fun a b => PS.add b a) args PS.empty) eqns)
        as [[good defined] variables].
      simpl.
      specialize H with good defined variables.
      pose proof (H (eq_refl _)) as H'; clear H.
      destruct H' as [Ht Hf].
      destruct good;
        intuition.
    Qed.

    Lemma Is_well_sch_by_refl:
      forall args eqns,
        well_sch args eqns = true <-> Is_well_sch mems args eqns.
    Proof.
      intros args eqns.
      pose proof (well_sch_spec args eqns) as Hwss.
      split; intro H.
      rewrite H in Hwss; assumption.
      destruct (well_sch args eqns); [reflexivity|].
      exfalso; apply Hwss; apply H.
    Qed.
    
    Lemma well_sch_dec:
      forall args eqns,
        {Is_well_sch mems args eqns}+{~Is_well_sch mems args eqns}.
    Proof.
      intros args eqns.
      pose proof (well_sch_spec args eqns) as Hwss.
      destruct (well_sch args eqns); [left|right]; assumption.
    Qed.
    
  End Decide.

End DECIDE.

Module Decide
       (Ids           : IDS)
       (Op            : OPERATORS)
       (Import Syn    : SYNTAX Ids Op)
       (IsF           : ISFREE Ids Op Syn)
       (Import IsFDec : IsFree.Decide.DECIDE Ids Op Syn IsF)
       (Import Ord    : ORDERED Ids Op Syn)
       (Import Mem    : MEMORIES Ids Op Syn)
       (Import IsD    : ISDEFINED Ids Op Syn Mem)
       (Import IsV    : ISVARIABLE Ids Op Syn Mem IsD)
       (Import IsDDec : IsDefined.Decide.DECIDE Ids Op Syn Mem IsD)
       (Import IsVDec : IsVariable.Decide.DECIDE Ids Op Syn Mem IsD IsV)
       (Import NoD    : NODUP Ids Op Syn Mem IsD IsV)
       (Import Wef    : WELLFORMED Ids Op Syn IsF Ord Mem IsD IsV NoD)
       <: DECIDE Ids Op Syn IsF IsFDec Ord Mem IsD IsV IsDDec IsVDec NoD Wef.
  
  Include DECIDE Ids Op Syn IsF IsFDec Ord Mem IsD IsV IsDDec IsVDec NoD Wef.
End Decide.
  
