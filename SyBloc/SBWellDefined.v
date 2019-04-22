Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.Clocks.

Require Import Velus.SyBloc.SBIsBlock.
Require Import Velus.SyBloc.SBOrdered.

Require Import Velus.SyBloc.SBIsVariable.
Require Import Velus.SyBloc.SBIsLast.
Require Import Velus.SyBloc.SBIsDefined.

Require Import Velus.CoreExpr.CEIsFree.
Require Import Velus.SyBloc.SBIsFree.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Omega.

Module Type SBWELLDEFINED
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX     Op)
       (Import Syn   : SBSYNTAX     Ids Op CESyn)
       (Import Block : SBISBLOCK    Ids Op CESyn Syn)
       (Import Ord   : SBORDERED    Ids Op CESyn Syn Block)
       (Import Var   : SBISVARIABLE Ids Op CESyn Syn)
       (Import Last  : SBISLAST     Ids Op CESyn Syn)
       (Import Def   : SBISDEFINED  Ids Op CESyn Syn Var Last)
       (Import CEIsF : CEISFREE   Ids Op CESyn)
       (Import Free  : SBISFREE     Ids Op CESyn Syn CEIsF).

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

  Definition Well_scheduled: program -> Prop :=
    Forall (fun bl => Is_well_sch (map fst (b_in bl)) (ps_from_list (map fst (b_lasts bl))) (b_eqs bl)).

  Lemma Is_well_sch_app:
    forall inputs mems eqs eqs',
      Is_well_sch inputs mems (eqs ++ eqs') ->
      Is_well_sch inputs mems eqs'.
  Proof.
    induction eqs; auto; simpl.
    inversion 1; auto.
  Qed.

  Lemma Is_last_in_not_Is_variable_in:
    forall eqs inputs mems x,
      Is_well_sch inputs mems eqs ->
      Is_last_in x eqs ->
      ~ Is_variable_in x eqs.
  Proof.
    induction eqs; intros * Wsch Last Var;
      inversion_clear Last as [?? IsLast|];
      inversion_clear Var as [?? IsVar|?? IsVar_in];
      inversion_clear Wsch as [|???? Defs].
    - inv IsLast; inv IsVar.
    - apply Is_variable_in_Is_defined_in in IsVar_in.
      eapply Defs; eauto.
      inv IsLast; constructor.
    - apply Is_variable_in_eq_Is_defined_in_eq in IsVar.
      eapply Defs; eauto.
      apply Is_defined_Is_variable_Is_last_in; auto.
    - eapply IHeqs; eauto.
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

   (** The [normal_args] predicate defines a normalization condition on
      node arguments -- those that are not on the base clock can only
      be instantiated with constants or variables -- that is necessary
      for correct generation of Obc/Clight.

      To see why this is necessary. Consider the NLustre equation: y =
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


  Inductive normal_args_eq (P: program) : equation -> Prop :=
  | CEqDef:
      forall x ck e,
        normal_args_eq P (EqDef x ck e)
  | CEqNext:
      forall x ck e,
        normal_args_eq P (EqNext x ck e)
  | CEqReset:
      forall s ck f,
        normal_args_eq P (EqReset s ck f)
  | CEqCall:
      forall s xs ck rst f es b P',
        find_block f P = Some (b, P') ->
        Forall2 noops_lexp (map dck b.(b_in)) es ->
        normal_args_eq P (EqCall s xs ck rst f es).

  Definition normal_args_block (P: program) (b: block) : Prop :=
    Forall (normal_args_eq P) b.(b_eqs).

  Fixpoint normal_args (P: list block) : Prop :=
    match P with
    | [] => True
    | b :: P' => normal_args_block P b /\ normal_args P'
    end.

  Lemma normal_args_block_cons:
    forall block P,
      normal_args_block (block :: P) block ->
      ~ Is_block_in block.(b_name) block.(b_eqs) ->
      normal_args_block P block.
  Proof.
    intros block P Hnarg Hord.
    apply Forall_forall.
    intros eq Hin.
    destruct eq; eauto using normal_args_eq.
    apply Forall_forall with (2:=Hin) in Hnarg.
    inversion_clear Hnarg as [| | |???????? Hfind Hnargs].
    rewrite find_block_other in Hfind;
      eauto using normal_args_eq.
    intro; subst; apply Hord.
    apply Exists_exists.
    eexists; intuition eauto using Is_block_in_eq.
  Qed.

  Definition Well_defined (P: program) : Prop :=
    Ordered_blocks P /\ Well_scheduled P /\ normal_args P.

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
    induction eqs as [|[]]; intros * Spec WSCH;
      inversion_clear WSCH as [|??? Free Def States];
      constructor;
      clear Free Def;
      try (eapply IHeqs; eauto; intros * Step; specialize (Spec s rst));
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

  Module PN_as_OT := OrdersEx.PairOrderedType OrdersEx.Positive_as_OT OrdersEx.Nat_as_OT.
  Module PNS := MSetList.Make PN_as_OT.

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

    Definition check_state (s: ident) (k: nat) (sk: ident * nat) : bool :=
      if ident_eqb (fst sk) s then Nat.ltb (snd sk) k else true.

    Lemma check_state_spec:
      forall s k s' k',
        check_state s k (s', k') = true
        <->
        (s = s' -> k' < k).
    Proof.
      intros; unfold check_state; simpl.
      split.
      - intros * E Eq; subst.
        rewrite ident_eqb_refl in E.
        apply Nat.ltb_lt; auto.
      - intros Spec.
        destruct (ident_eqb s' s) eqn: E; auto.
        apply Nat.ltb_lt, Spec.
        symmetry; apply ident_eqb_eq; auto.
    Qed.

    Definition check_eq (eq: equation) (acc: bool * PS.t * PS.t * PNS.t) : bool * PS.t * PS.t * PNS.t :=
      match acc with
      | (true, defs, vars, states) =>
        let xs := defined_eq eq in
        let b := PS.for_all (check_var defs vars) (free_in_eq eq PS.empty)
                            && negb (existsb (fun x => PS.mem x defs) xs) in
        let defs := ps_adds xs defs in
        let vars := variables_eq vars eq in
        match state_eq eq with
        | Some (s, k) =>
          (PNS.for_all (check_state s k) states && b,
           defs, vars, PNS.add (s, k) states)
        | None => (b, defs, vars, states)
        end
      | (false, _, _, _) => (false, PS.empty, PS.empty, PNS.empty)
      end.

    Definition well_sch (args: idents) (eqs: list equation) : bool :=
      fst (fst (fst (fold_right check_eq (true,
                                          PS.empty,
                                          ps_from_list args,
                                          PNS.empty) eqs))).

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

    Lemma pair_eq:
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
      apply pair_eq in E; subst; auto.
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

    Lemma free_spec:
      forall eqs args defs vars eq x,
        (forall x, PS.In x defs <-> Is_defined_in x eqs) ->
        (forall x, PS.In x vars <-> Is_variable_in x eqs \/ In x args) ->
        PS.For_all (fun x => check_var defs vars x = true) (free_in_eq eq PS.empty) ->
        Is_free_in_eq x eq ->
        if PS.mem x mems then ~ Is_defined_in x eqs else Is_variable_in x eqs \/ In x args.
    Proof.
      intros * DefSpec VarSpec E Hfree.
      apply free_in_eq_spec', E, check_var_spec in Hfree as (Hin & Hnin).
      destruct (PS.mem x mems) eqn: Mem.
      - rewrite <-DefSpec; apply PSE.MP.Dec.F.mem_iff, Hin in Mem; auto.
      - rewrite <-VarSpec; apply PSE.MP.Dec.F.not_mem_iff, Hnin in Mem; auto.
    Qed.

    Lemma def_spec:
      forall eqs defs eq x,
        (forall x, PS.In x defs <-> Is_defined_in x eqs) ->
        existsb (fun x => PS.mem x defs) (defined_eq eq) = false ->
        Is_defined_in_eq x eq ->
        ~ Is_defined_in x eqs.
    Proof.
      intros * DefSpec E Hdef Hdefs.
      apply DefSpec in Hdefs; apply Is_defined_in_defined_eq in Hdef.
      apply In_ex_nth with (d := Ids.default) in Hdef as (?&?&?); subst.
      eapply existsb_nth with (d := Ids.default) in E; eauto.
      apply PSE.MP.Dec.F.not_mem_iff in E; auto.
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
    Hint Resolve check_var_compat.

    Lemma not_well_sch_vars_defs_spec:
      forall eqs args defs vars eq,
         (forall x, PS.In x defs <-> Is_defined_in x eqs) ->
         (forall x, PS.In x vars <-> Is_variable_in x eqs \/ In x args) ->
         PS.for_all (check_var defs vars) (free_in_eq eq PS.empty) &&
                 negb (existsb (fun x => PS.mem x defs) (defined_eq eq)) = false ->
        ~ Is_well_sch args mems (eq :: eqs).
    Proof.
      intros * DefSpec VarSpec E Wsch.
      inversion_clear Wsch as [|??? Hfree Hdefs].
      apply Bool.andb_false_iff in E as [E|E].
      - apply PS_not_for_all_spec in E; auto.
        apply E; intros x Hin; apply free_in_eq_spec' in Hin.
        apply Hfree in Hin.
        apply check_var_spec; split.
        + rewrite PSE.MP.Dec.F.mem_iff; intro Hin'; rewrite Hin' in Hin.
          now rewrite DefSpec.
        + rewrite PSE.MP.Dec.F.not_mem_iff; intro Hin'; rewrite Hin' in Hin.
          now rewrite VarSpec.
      - apply Bool.negb_false_iff, existsb_exists in E as (?& Hin & Hin').
        apply Is_defined_in_defined_eq in Hin.
        apply PSE.MP.Dec.F.mem_iff, DefSpec in Hin'.
        eapply Hdefs; eauto.
    Qed.

    Lemma Is_defined_in_adds_defined_eq:
      forall eqs defs eq x,
        (forall x, PS.In x defs <-> Is_defined_in x eqs) ->
        (PS.In x (ps_adds (defined_eq eq) defs) <-> Is_defined_in x (eq :: eqs)).
    Proof.
      intros * DefSpec; split; intro Hin;
        [apply ps_adds_spec in Hin as [|]|apply ps_adds_spec; inv Hin];
        try (now left; apply Is_defined_in_defined_eq; auto);
        try (now right; apply DefSpec; auto); auto.
    Qed.

    Lemma Is_variable_in_variables_eq:
      forall eqs args vars eq x,
        (forall x, PS.In x vars <-> Is_variable_in x eqs \/ In x args) ->
        (PS.In x (variables_eq vars eq) <-> Is_variable_in x (eq :: eqs) \/ In x args).
    Proof.
      intros * VarSpec; split; intro Hin.
      - apply variables_eq_empty in Hin as [Hin|Hin].
        + destruct eq; simpl in *; try (contradict Hin; apply not_In_empty).
          *{ apply PSE.MP.Dec.F.add_iff in Hin as [|Hin]; subst.
             - left; left; constructor.
             - contradict Hin; apply not_In_empty.
           }
          *{ apply ps_adds_spec in Hin as [|Hin].
             - left; left; constructor; auto.
             - contradict Hin; apply not_In_empty.
           }
        + apply VarSpec in Hin as [|]; intuition.
          left; right; auto.
      - apply variables_eq_empty; destruct Hin as [Hin|].
        + inversion_clear Hin as [?? Hin'|].
          *{ destruct eq; simpl; inv Hin'.
             - rewrite PSE.MP.Dec.F.add_iff; auto.
             - rewrite ps_adds_spec; auto.
           }
          * rewrite VarSpec; auto.
        + rewrite VarSpec; auto.
    Qed.


    Lemma well_sch_pre_spec:
      forall args eqs ok defs vars states,
        fold_right check_eq (true,
                             PS.empty,
                             ps_from_list args,
                             PNS.empty) eqs = (ok, defs, vars, states) ->
        if ok
        then
          Is_well_sch args mems eqs
          /\ (forall x, PS.In x defs <-> Is_defined_in x eqs)
          /\ (forall x, PS.In x vars <-> Is_variable_in x eqs \/ In x args)
          /\ (forall s k, PNS.In (s, k) states <-> Is_state_in s k eqs)
        else
          ~Is_well_sch args mems eqs.
    Proof.
      induction eqs as [|eq].
      - simpl; inversion_clear 1; intuition; try (now constructor);
          repeat match goal with
                 | H:PS.In _ PS.empty |- _ => apply PS.empty_spec in H; contradiction
                 | H:PNS.In _ PNS.empty |- _ => apply PNS.empty_spec in H; contradiction
                 | H:Is_defined_in _ nil |- _ => inversion H
                 | H:Is_variable_in _ nil |- _ => inversion H
                 | H:Is_state_in _ _ nil |- _ => inversion H
                 | H: context[ps_from_list _] |- _ =>
                   apply ps_from_list_In in H
                 | _ => intuition
                 end.
        apply ps_from_list_In; auto.
      - simpl; intros * HH.
        destruct (fold_right check_eq (true, PS.empty, ps_from_list args, PNS.empty) eqs)
          as [[[ok' defs'] vars'] states'].
        specialize (IHeqs ok' defs'  vars' states' eq_refl).
        simpl in HH.
        destruct ok'.
        + destruct IHeqs as (Wsch & DefSpec & VarSpec & StateSpec).
          assert (forall x, PS.In x (ps_adds (defined_eq eq) defs') <-> Is_defined_in x (eq :: eqs))
            by (intros; eapply Is_defined_in_adds_defined_eq; eauto).
          assert (forall x, PS.In x (variables_eq vars' eq) <-> Is_variable_in x (eq :: eqs) \/ In x args)
            by (intros; eapply Is_variable_in_variables_eq; eauto).
          destruct (state_eq eq) as [(s, k)|] eqn: St.
          *{ destruct ok; inversion HH as [E]; clear HH.
             - apply Bool.andb_true_iff in E as (E & E');
                 apply Bool.andb_true_iff in E' as (E' & E'').
               apply PNS.for_all_spec in E; auto.
               apply PS.for_all_spec in E'; auto.
               apply Bool.negb_true_iff in E''.
               split; [|split; [|split]]; auto.
               + constructor; auto.
                 * intros; eapply free_spec; eauto.
                 * intros; eapply def_spec; eauto.
                 * intros * Hin; apply Is_state_in_state_eq in Hin; rewrite Hin in St; inv St.
                   apply Forall_forall; intros.
                   assert (Is_state_in s k' eqs) as Hst
                       by (apply Exists_exists; eexists; intuition; eauto).
                   apply StateSpec in Hst; apply E in Hst.
                   apply check_state_spec in Hst; auto.
               + rewrite <-Is_state_in_state_eq in St.
                 intros s' k'; split; rewrite PNS.add_spec.
                 *{ intros [Eq|Hin].
                    - apply pair_eq in Eq; inv Eq; left; auto.
                    - apply StateSpec in Hin; right; auto.
                  }
                 *{ rewrite pair_eq; inversion_clear 1 as [?? St'|].
                    - inv St; inv St'; auto.
                    - right; apply StateSpec; auto.
                  }

             - apply Bool.andb_false_iff in E as [E|];
                 [|eapply not_well_sch_vars_defs_spec; eauto].
               inversion_clear 1 as [|????? Hstates].
               rewrite <-Is_state_in_state_eq in St.
               apply Hstates in St.
               apply PNS_not_for_all_spec in E; apply E; clear E.
               intros (s', k') Hin.
               apply check_state_spec; intros; subst.
               apply StateSpec in Hin.
               eapply Forall_Exists, Exists_exists in Hin as (?&?& Spec & St'); eauto; auto.
           }
          *{ destruct ok; inversion HH as [E].
             - apply Bool.andb_true_iff in E as (E & E').
               apply PS.for_all_spec in E; try apply check_var_compat.
               apply Bool.negb_true_iff in E'.
               split; [|split; [|split]]; auto.
               + constructor; auto.
                 * intros; eapply free_spec; eauto.
                 * intros; eapply def_spec; eauto.
                 * intros * Hin; apply Is_state_in_state_eq in Hin; rewrite Hin in St; inv St.
               + subst; setoid_rewrite StateSpec.
                 split.
                 * right; auto.
                 * rewrite <-not_Some_is_None in St.
                   specialize (St (s, k)).
                   rewrite <-Is_state_in_state_eq in St.
                   inversion 1; auto; contradiction.
             - eapply not_well_sch_vars_defs_spec; eauto.
           }

        + inv HH; inversion 1; auto.
    Qed.

    Lemma well_sch_spec:
      forall args eqns,
        if well_sch args eqns
        then Is_well_sch args mems eqns
        else ~ Is_well_sch args mems eqns.
    Proof.
      intros args eqns.
      pose proof (well_sch_pre_spec args eqns) as Spec.
      unfold well_sch.
      destruct (fold_right check_eq
                  (true, PS.empty, ps_from_list args, PNS.empty) eqns)
        as [[[ok defs] vars] states]; simpl.
      specialize (Spec ok defs vars states eq_refl).
      destruct ok; intuition.
    Qed.

    Lemma Is_well_sch_by_refl:
      forall args eqns,
        well_sch args eqns = true <-> Is_well_sch args mems eqns.
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
        {Is_well_sch args mems eqns} + {~ Is_well_sch args mems eqns}.
    Proof.
      intros args eqns.
      pose proof (well_sch_spec args eqns) as Hwss.
      destruct (well_sch args eqns); [left|right]; assumption.
    Qed.

  End Decide.

End SBWELLDEFINED.

Module SBWellDefinedFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX     Op)
       (Syn   : SBSYNTAX     Ids Op CESyn)
       (Block : SBISBLOCK    Ids Op CESyn Syn)
       (Ord   : SBORDERED    Ids Op CESyn Syn Block)
       (Var   : SBISVARIABLE Ids Op CESyn Syn)
       (Last  : SBISLAST     Ids Op CESyn Syn)
       (Def   : SBISDEFINED  Ids Op CESyn Syn Var Last)
       (CEIsF : CEISFREE   Ids Op CESyn)
       (Free  : SBISFREE     Ids Op CESyn Syn CEIsF)
<: SBWELLDEFINED Ids Op CESyn Syn Block Ord Var Last Def CEIsF Free.
  Include SBWELLDEFINED Ids Op CESyn Syn Block Ord Var Last Def CEIsF Free.
End SBWellDefinedFun.
