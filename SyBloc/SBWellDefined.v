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
        destruct PSP.In_dec with x mems as [H|H].
        + assert (PS.mem x mems = true) as H' by auto.
          rewrite H', Bool.negb_true_iff, mem_spec_false.
          now apply Hin with (1:=H).
        + assert (PS.mem x mems = false) as H' by now apply mem_spec_false.
          rewrite H', PS.mem_spec.
          now apply Hnin with (1:=H).
    Qed.

    Definition state_eq (eq: equation) : option (ident * nat) :=
      match eq with
      | EqReset s _ _ => Some (s, 0)
      | EqCall s _ _ _ _ _ => Some (s, 1)
      | _ => None
      end.

    Lemma Is_state_in_state_eq:
      forall eq s k,
        Is_state_in_eq s k eq <-> state_eq eq = Some (s, k).
    Proof.
      destruct eq; simpl; split; try inversion_clear 1; auto using Is_state_in_eq.
    Qed.

    Definition check_eq (eq: equation) (acc: bool * PS.t * PS.t * Env.t nat) : bool * PS.t * PS.t * Env.t nat :=
      match acc with
      | (true, defs, vars, states) =>
        let xs := defined_eq eq in
        let b := PS.for_all (check_var defs vars) (free_in_eq eq PS.empty)
                            && negb (existsb (fun x => PS.mem x defs) xs) in
        let defs := ps_adds xs defs in
        let vars := variables_eq vars eq in
        match state_eq eq with
        | Some (s, k) =>
          (match Env.find s states with
           | Some k' => NPeano.ltb k' k && b
           | None => b
           end,
           defs, vars, Env.add s k states)
        | None => (b, defs, vars, states)
        end
      | (false, _, _, _) => (false, PS.empty, PS.empty, Env.empty _)
      end.

    Definition well_sch (args: idents) (eqs: list equation) : bool :=
      fst (fst (fst (fold_right check_eq (true,
                                          PS.empty,
                                          ps_from_list args,
                                          Env.empty _) eqs))).

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

    (* Lemma in_fold_left_add: *)
    (*   forall x xs S, *)
    (*     PS.In x (fold_left (fun S' x => PS.add x S') xs S) *)
    (*     <-> *)
    (*     In x xs \/ PS.In x S. *)
    (* Proof. *)
    (*   induction xs as [|y xs IH]. *)
    (*   split; intro H; simpl in *; *)
    (*     intuition. *)
    (*   intro S; split; intro H. *)
    (*   - apply IH in H. *)
    (*     destruct H. *)
    (*     now left; constructor (assumption). *)
    (*     apply PS.add_spec in H; simpl; intuition. *)
    (*   - simpl; apply IH; simpl in H; intuition. *)
    (* Qed. *)

    Lemma well_sch_pre_spec:
      forall args eqs ok defs vars states,
        fold_right check_eq (true,
                             PS.empty,
                             ps_from_list args,
                             Env.empty _) eqs = (ok, defs, vars, states) ->
        if ok
        then
          Is_well_sch args mems eqs
          /\ (forall x, PS.In x defs <-> Is_defined_in x eqs)
          /\ (forall x, PS.In x vars <-> Is_variable_in x eqs \/ In x args)
          /\ (forall s k, Env.find s states = Some k <-> Is_state_in s k eqs)
        else
          ~Is_well_sch args mems eqs.
    Proof.
      induction eqs as [|eq].
      - simpl; inversion_clear 1; intuition; try (now constructor);
          repeat match goal with
                 | H:PS.In _ PS.empty |- _ => apply PS.empty_spec in H; contradiction
                 | H:Env.find _ (Env.empty _) = _ |- _ => rewrite Env.gempty in H; discriminate
                 | H:Is_defined_in _ nil |- _ => inversion H
                 | H:Is_variable_in _ nil |- _ => inversion H
                 | H:Is_state_in _ _ nil |- _ => inversion H
                 | H: context[ps_from_list _] |- _ =>
                   apply ps_from_list_In in H
                 | _ => intuition
                 end.
        apply ps_from_list_In; auto.
      - simpl; intros ** HH.
        destruct (fold_right check_eq (true, PS.empty, ps_from_list args, Env.empty nat) eqs)
          as [[[ok' defs'] vars'] states'].
        specialize (IHeqs ok' defs'  vars' states' eq_refl).
        simpl in HH.
        destruct ok'.
        + destruct IHeqs as (Wsch & DefSpec & VarSpec & StateSpec).
          destruct (state_eq eq) eqn: St.
          * admit.
          *{ destruct ok; inversion HH as [E]; [apply Bool.andb_true_iff in E as (E & E')|].
             - apply PS.for_all_spec in E; try now apply check_var_compat.
               apply Bool.negb_true_iff in E'.
               split; [|split; [|split]].
               + constructor; auto.
                 *{ intros ** Hfree.
                    apply free_in_eq_spec', E, check_var_spec in Hfree as (Hin & Hnin).
                    destruct (PS.mem x mems) eqn: Mem.
                    - rewrite <-DefSpec; apply PSE.MP.Dec.F.mem_iff, Hin in Mem; auto.
                    - rewrite <-VarSpec; apply PSE.MP.Dec.F.not_mem_iff, Hnin in Mem; auto.
                  }
                 * setoid_rewrite <-DefSpec; setoid_rewrite Is_defined_in_defined_eq.
                   intros x Hin.
                   apply In_ex_nth with (d := Ids.default) in Hin as (?&?&?); subst.
                   eapply existsb_nth with (d := Ids.default) in E'; eauto.
                   now apply PSE.MP.Dec.F.not_mem_iff.
                 * setoid_rewrite Is_state_in_state_eq; rewrite St; discriminate.
               + intro x; split; intro Hin;
                   [apply ps_adds_spec in Hin as [|]|apply ps_adds_spec; inv Hin];
                   try (now left; apply Is_defined_in_defined_eq; auto);
                   try (now right; apply DefSpec; auto); auto.
               + intro x; split; intro Hin.
                 *
                 (* variables set *)
            intro x; split; intro HH.
            apply variable_eq_empty in HH.
            destruct HH as [HH|HH].
            destruct eq;
              match goal with
              | |- context[ EqApp _ _ _ _ ] =>
                generalize ps_adds_spec; intro add_spec
              | _ =>
                generalize PS.add_spec; intro add_spec
              end;
              ((apply add_spec in HH;
                destruct HH as [HH|HH];
                [try subst i; left; now repeat constructor
                |apply PS.empty_spec in HH; contradiction])
               || apply PS.empty_spec in HH; contradiction).
            apply IHvar in HH; intuition; left; constructor (assumption).
            apply variable_eq_empty.
            destruct HH as [HH|HH].
            apply Is_variable_in_cons in HH.
            destruct HH as [HH|HH]; [left|right].
            destruct eq;
              match goal with
              | |- context[ EqApp _ _ _ _ ] =>
                generalize ps_adds_spec; intro add_spec
              | _ =>
                generalize PS.add_spec; intro add_spec
              end;
              inversion_clear HH; simpl;
                try (rewrite add_spec; auto);
                intuition.
            apply IHvar; intuition.
            right; apply IHvar; auto.

               SearchAbout (_ && _) true. inv HH.

        + inv HH.
          inversion_clear 1; contradiction.




          simpl in HH.
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

          assert (forall x, In x (var_defined eq) -> ~ PS.In x defined')
            as Hnot_def.
          {
            intros x Hin.

            assert (exists n,
                       n < length (var_defined eq)
                     /\ nth n (var_defined eq) Ids.default = x)
              as (n & Hlen & Hnth)
                by now apply In_ex_nth.

            assert (PS.mem x defined' = false)
              by now subst x;
                     eapply existsb_nth
                       with (f := (fun x => PS.mem x defined')).

            now apply mem_spec_false.
          }

          split; [|split].
          * (* Is_well_sch *)
            assert (forall i,
                       IsF.Is_free_in_eq i eq ->
                       (PS.In i mems -> ~ Is_defined_in_eqs i eqs) /\
                       (~ PS.In i mems -> Is_variable_in_eqs i eqs \/ In i args)).
            {
              intros x Hfree.
              apply free_in_equation_spec' in Hfree.
              apply H1 in Hfree.
              apply check_var_spec in Hfree.
              destruct Hfree as [Hfree1 Hfree2].
              split; intro HH; (apply Hfree1 in HH || apply Hfree2 in HH).
              - now intro; apply HH; apply IHdef.
              - now apply IHvar.
            }

            assert (forall i, Is_defined_in_eq i eq -> ~ Is_defined_in_eqs i eqs).
            {
              intros x Hdef Hdefs; apply IHdef in Hdefs.
              apply Is_defined_in_eqs_var_defined in Hdef.
              now eapply Hnot_def; eauto.
            }

            now constructor.
          * (* defined set *)
            intro x; split; intro HH.
            apply ps_adds_spec in HH.
            destruct HH as [HH|HH].
            constructor; now apply Is_defined_in_eqs_var_defined.
            apply IHdef in HH.
            constructor (assumption).
            apply ps_adds_spec.
            inversion_clear HH.
            apply Is_defined_in_eqs_var_defined in H; auto.
            right; apply IHdef; assumption.
          * (* variables set *)
            intro x; split; intro HH.
            apply variable_eq_empty in HH.
            destruct HH as [HH|HH].
            destruct eq;
              match goal with
              | |- context[ EqApp _ _ _ _ ] =>
                generalize ps_adds_spec; intro add_spec
              | _ =>
                generalize PS.add_spec; intro add_spec
              end;
              ((apply add_spec in HH;
                destruct HH as [HH|HH];
                [try subst i; left; now repeat constructor
                |apply PS.empty_spec in HH; contradiction])
               || apply PS.empty_spec in HH; contradiction).
            apply IHvar in HH; intuition; left; constructor (assumption).
            apply variable_eq_empty.
            destruct HH as [HH|HH].
            apply Is_variable_in_cons in HH.
            destruct HH as [HH|HH]; [left|right].
            destruct eq;
              match goal with
              | |- context[ EqApp _ _ _ _ ] =>
                generalize ps_adds_spec; intro add_spec
              | _ =>
                generalize PS.add_spec; intro add_spec
              end;
              inversion_clear HH; simpl;
                try (rewrite add_spec; auto);
                intuition.
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

            assert (exists x, In x (var_defined eq) /\ PS.In x defined')
              as (x & Hdef & Hdef').
            {
              apply existsb_exists in HH.
              destruct HH as (x & Hvar_def & Hmem).
              rewrite PS.mem_spec in Hmem.
              now eexists; eauto.
            }

            assert (Is_defined_in_eq x eq)
              by now apply Is_defined_in_eqs_var_defined.

            assert (Is_defined_in_eqs x eqs)
              by now apply IHdef.

            eapply Hdefd; now eauto.
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

End SBWELLDEFINED.

Module SBWellDefinedFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (Clks    : CLOCKS       Ids)
       (ExprSyn : NLEXPRSYNTAX     Op)
       (Syn     : SBSYNTAX     Ids Op Clks ExprSyn)
       (Block   : SBISBLOCK    Ids Op Clks ExprSyn Syn)
       (Ord     : SBORDERED    Ids Op Clks ExprSyn Syn Block)
       (Var     : SBISVARIABLE Ids Op Clks ExprSyn Syn)
       (Last    : SBISLAST     Ids Op Clks ExprSyn Syn)
       (Def     : SBISDEFINED  Ids Op Clks ExprSyn Syn Var Last)
       (SynNL          : NLSYNTAX     Ids Op Clks ExprSyn)
       (IsF     : ISFREE       Ids Op Clks ExprSyn     SynNL)
       (Free    : SBISFREE     Ids Op Clks ExprSyn Syn SynNL IsF)
<: SBWELLDEFINED Ids Op Clks ExprSyn Syn Block Ord Var Last Def SynNL IsF Free.
  Include SBWELLDEFINED Ids Op Clks ExprSyn Syn Block Ord Var Last Def SynNL IsF Free.
End SBWellDefinedFun.
