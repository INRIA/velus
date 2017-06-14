Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.IsFree.
Require Import Velus.NLustre.IsVariable.
Require Import Velus.NLustre.IsDefined.
Require Import Velus.NLustre.Memories.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.NoDup.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.

(** * Well formed NLustre programs *)

Module Type WELLFORMED
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import Clks : CLOCKS     Ids)
       (Import Syn  : NLSYNTAX   Ids Op Clks)
       (Import IsF  : ISFREE     Ids Op Clks Syn)
       (Import Ord  : ORDERED    Ids Op Clks Syn)
       (Import Mem  : MEMORIES   Ids Op Clks Syn)
       (Import IsD  : ISDEFINED  Ids Op Clks Syn Mem)
       (Import IsV  : ISVARIABLE Ids Op Clks Syn Mem IsD)
       (Import NoD  : NODUP      Ids Op Clks Syn Mem IsD IsV).

  Section IsWellSch.

    Variable memories : PS.t.
    Variable arg: idents.

    (**

A list of equations is well scheduled if
  - the free stack variables ([~PS.In _ memories]) are defined before
    (i.e. in [eqs]), or they belong to the input argument
  - the free memory variables ([PS.In _ memories]) have not been
    re-assigned before (i.e. in [eqs])
  - the variable defined by an equation must be defined for the first
    time

Remark: we assume that the list of equations is in reverse order: the
first equation to execute should be the last in the list.

     *)
    (* =Is_well_sch= *)
    Inductive Is_well_sch : list equation -> Prop :=
    | WSchNil: Is_well_sch nil
    | WSchEq: forall eq eqs,
        Is_well_sch eqs ->
        (forall i, Is_free_in_eq i eq ->
              (PS.In i memories -> ~Is_defined_in_eqs i eqs)
              /\ (~PS.In i memories -> Is_variable_in_eqs i eqs \/ In i arg)) ->
        (forall i, Is_defined_in_eq i eq -> ~Is_defined_in_eqs i eqs) ->
        Is_well_sch (eq :: eqs).
    (* =end= *)

  End IsWellSch.

  (**

An NLustre program is well defined if
  - Each node is well-defined, that is
    - The equations are well scheduled
  - Every node call points to a previously-defined node
  - Each of the nodes' name is distinct
   *)

  Inductive Welldef_global : list node -> Prop :=
  | WGnil:
      Welldef_global []
  | WGcons:
      forall nd nds,
        Welldef_global nds ->
        let eqs := nd.(n_eqs) in
        Is_well_sch (memories eqs) (map fst nd.(n_in)) eqs
        -> ~Is_node_in nd.(n_name) eqs
        -> (forall f, Is_node_in f eqs -> find_node f nds <> None)
        -> Forall (fun nd'=> nd.(n_name) <> nd'.(n_name)) nds
        -> Welldef_global (nd::nds).


  (** ** Properties of [Is_well_sch] *)

  Hint Constructors Is_well_sch.

  Lemma Is_well_sch_NoDup_defs:
    forall mems argIn eqs,
      Is_well_sch mems argIn eqs
      -> NoDup_defs eqs.
  Proof.
    induction eqs as [|eq eqs IH]; [now constructor|].
    inversion_clear 1; destruct eq; constructor; try apply IH; auto; try apply H2; constructor.
  Qed.

  Lemma Is_well_sch_cons:
    forall m argIn eq eqs, Is_well_sch m argIn (eq :: eqs) -> Is_well_sch m argIn eqs.
  Proof. inversion 1; auto. Qed.

  Lemma Is_well_sch_free_variable:
    forall argIn x eq eqs mems,
      Is_well_sch mems argIn (eq :: eqs)
      -> Is_free_in_eq x eq
      -> ~ PS.In x mems
      -> Is_variable_in_eqs x eqs \/ In x argIn.
  Proof.
    intros argIn x eq eqs mems Hwsch Hfree Hnim.
    destruct eq;
      inversion_clear Hwsch;
      inversion_clear Hfree as [? ? ? ? Hc | ? ? ? ? ? Hc | ? ? ? ? ? Hc];
      subst; intuition;
      match goal with
      | H: context[ Is_variable_in_eqs _ _ \/ In _ _] |- _ =>
        eapply H; eauto
      end.
  Qed.

  Lemma Is_well_sch_free_variable_in_mems:
    forall argIn y eq eqs mems,
      Is_well_sch mems argIn (eq :: eqs)
      -> Is_free_in_eq y eq
      -> PS.In y mems
      -> ~Is_defined_in_eqs y eqs.
  Proof.
    intros argIn x eq eqs mems Hwsch Hfree Hnim.
    destruct eq;
      inversion_clear Hwsch;
      inversion_clear Hfree as [? ? ? ? Hc | ? ? ? ? ? Hc | ? ? ? ? ? Hc];
      match goal with
      | H: context[In _ _ ] |- _ => eapply H
      end;
      auto.
  Qed.

  (* Lemma Is_wsch_is_defined_in: *)
  (*   forall x eq eqs mems argIn, *)
  (*     Is_well_sch mems argIn (eq :: eqs) -> *)
  (*     Is_defined_in_eqs x (eq :: eqs) -> *)
  (*     Is_defined_in_eq x eq *)
  (*     \/ (~Is_defined_in_eq x eq /\ Is_defined_in_eqs x eqs). *)
  (* Proof. *)
  (*   intros x eq eqs mems argIn Hwsch Hdef. *)
  (*   apply Exists_cons in Hdef. *)
  (*   destruct (Is_defined_in_eq_dec x eq); intuition. *)
  (* Qed. *)

  (** ** Properties of [Welldef_global] *)

  Lemma Welldef_global_cons:
    forall node G,
      Welldef_global (node::G) -> Welldef_global G.
  Proof.
    inversion 1; assumption.
  Qed.

  (* TODO: Write a function 'welldef_global' to decide this. *)

  Lemma Welldef_global_Ordered_nodes:
    forall G, Welldef_global G -> Ordered_nodes G.
  Proof.
    induction G as [|node G IH]; [constructor|].
    intro Hwdef.
    constructor.
    - apply IH; apply Welldef_global_cons with (1:=Hwdef).
    - intros f Hini.
      inversion Hwdef.
      split; [ intro; subst | ];
      repeat match goal with
             | eqs:=n_eqs node |- _ => unfold eqs in *; clear eqs
                  | H1:~Is_node_in _ _, H2:Is_node_in _ _ |- False => contradiction
                  | H1: Is_node_in _ _,
                        H2: context[Is_node_in _ _ -> find_node _ _ <> None] |- _ =>
                    apply H2 in H1; apply find_node_Exists in H1; exact H1
             end.
    - inversion Hwdef; assumption.
  Qed.

  (** * Decision procedure *)

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
        | xs => ((PS.for_all (check_var defined variables)
                            (free_in_equation eq PS.empty))
                  && (negb (List.existsb (fun x => PS.mem x defined) xs)),
                fold_left (fun defined x => PS.add x defined) xs defined, variable_eq variables eq)
        end
      | (false, _, _) => (false, PS.empty, PS.empty)
      end.

    Definition well_sch (args: idents) (eqs: list equation) : bool :=
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
              | |- context[ EqApp _ _ _ _ _ ] =>
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
              | |- context[ EqApp _ _ _ _ _ ] =>
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
End WELLFORMED.

Module WellFormedFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Clks : CLOCKS Ids)
       (Syn  : NLSYNTAX   Ids Op Clks)
       (IsF  : ISFREE     Ids Op Clks Syn)
       (Ord  : ORDERED    Ids Op Clks Syn)
       (Mem  : MEMORIES   Ids Op Clks Syn)
       (IsD  : ISDEFINED  Ids Op Clks Syn Mem)
       (IsV  : ISVARIABLE Ids Op Clks Syn Mem IsD)
       (NoD  : NODUP Ids Op Clks Syn Mem IsD IsV)
       <: WELLFORMED Ids Op Clks Syn IsF Ord Mem IsD IsV NoD.
  Include WELLFORMED Ids Op Clks Syn IsF Ord Mem IsD IsV NoD.
End WellFormedFun.
