Require Import Coq.FSets.FMapPositive.
Require Import PArith.

Require Import Velus.SyBloc.
Require Import Velus.Obc.
Require Import Velus.SyBlocToObc.Translation.

Require Import Velus.Common.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type SB2OBCINVARIANTS
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX       Op)
       (Import Clks   : CLOCKS          Ids)
       (Import Str    : STREAM              Op OpAux)
       (Import CE     : COREEXPR       Ids Op OpAux Clks Str)
       (Import SB     : SYBLOC          Ids Op OpAux Clks Str CE)
       (Import Obc    : OBC             Ids Op OpAux)
       (Import Trans  : TRANSLATION     Ids Op OpAux Clks CE.Syn SB.Syn Obc.Syn).

  (** ** Show that the Obc code that results from translating a SyBloc
         program satisfies the [Fusible] invariant, and thus that fusion
         preserves its semantics. *)

  Lemma not_Can_write_in_translate_cexp:
    forall x mems e y,
      x <> y -> ~ Can_write_in y (translate_cexp mems x e).
  Proof.
    induction e; intros ** Hcw; inv Hcw; intuition eauto.
  Qed.

  Lemma Is_free_in_tovar:
    forall mems x y ty,
      Is_free_in_exp y (tovar mems (x, ty)) <-> x = y.
  Proof.
    unfold tovar; intros.
    cases; split; intro HH;
      (inversion_clear HH; reflexivity || subst; now constructor).
  Qed.

  Lemma Is_free_translate_lexp:
    forall x mems e,
      Is_free_in_exp x (translate_lexp mems e) -> Is_free_in_lexp x e.
  Proof.
    induction e; simpl; intro H; auto.
    - inversion H.
    - now apply Is_free_in_tovar in H; subst.
    - constructor; inversion H; auto.
    - constructor; inversion_clear H as [| | |????? [?|?]]; subst;
        [left; auto | right; auto].
  Qed.

  Lemma Fusible_translate_cexp:
    forall mems x e,
      (forall y, Is_free_in_cexp y e -> x <> y) ->
      Fusible (translate_cexp mems x e).
  Proof.
    intros ** Hfree.
    induction e; eauto using Fusible.
    - simpl; constructor;
        [apply IHe1; now auto|apply IHe2; now auto|].
      intros ** Hfree'; split;
        (apply not_Can_write_in_translate_cexp;
         apply Is_free_in_tovar in Hfree';
         subst; apply Hfree; constructor).
    - simpl; constructor;
        [apply IHe1; now auto|apply IHe2; now auto|].
      intros ** Hfree'; split;
        apply not_Can_write_in_translate_cexp;
        apply Hfree;
        now constructor; apply Is_free_translate_lexp with mems.
  Qed.

  Lemma Fusible_Control_caexp:
    forall mems ck f e,
      (forall x, Is_free_in_caexp x ck e -> ~ Can_write_in x (f e)) ->
      Fusible (f e) ->
      Fusible (Control mems ck (f e)).
  Proof.
    induction ck as [|ck IH i b]; [now intuition|].
    intros ** Hxni Hfce; simpl.
    cases.
    - apply IH with (f := fun ce => Ifte (tovar mems (i, bool_type)) (f ce) Skip).
      + intros j Hfree Hcw.
        apply Hxni with (x := j); [inversion_clear Hfree; eauto|].
        inversion_clear Hcw as [| | |? ? ? ? Hskip| | |];
          [assumption|inversion Hskip].
      + repeat constructor; [assumption| |now inversion 1].
        apply Hxni.
        match goal with
        | H:Is_free_in_exp _ (tovar mems _) |- _ => rename H into Hfree
        end.
        unfold tovar in Hfree.
        destruct (PS.mem i mems); inversion Hfree; subst; eauto.
    - apply IH with (f := fun ce => Ifte (tovar mems (i, bool_type)) Skip (f ce)).
      + intros j Hfree Hcw.
        apply Hxni with (x := j); [inversion_clear Hfree; eauto|].
        inversion_clear Hcw as [| |? ? ? ? Hskip| | | |];
          [inversion Hskip|assumption].
      + repeat constructor; [assumption|now inversion 1|].
        apply Hxni.
        match goal with
        | H:Is_free_in_exp _ (tovar mems _) |- _ => rename H into Hfree
        end.
        unfold tovar in Hfree.
        destruct (PS.mem i mems); inversion Hfree; subst; eauto.
  Qed.

  Lemma Fusible_Control_laexp:
    forall mems ck s,
      (forall x, Is_free_in_clock x ck -> ~ Can_write_in x s) ->
      Fusible s ->
      Fusible (Control mems ck s).
  Proof.
    induction ck as [|ck IH i b]; [now intuition|].
    intros ** Hxni Hfce; simpl.
    cases; apply IH.
    - intros j Hfree Hcw.
      apply Hxni with (x := j); [inversion_clear Hfree; eauto|].
      inversion_clear Hcw as [| | |? ? ? ? Hskip| | |];
        [assumption|inversion Hskip].
    - repeat constructor; [assumption| |now inversion 1].
      apply Hxni.
      rename H into Hfree.
      unfold bool_var, tovar in *.
      cases; inversion Hfree; subst; eauto.
    - intros j Hfree Hcw.
      apply Hxni with (x := j); [inversion_clear Hfree; eauto|].
      inversion_clear Hcw as [| |? ? ? ? Hskip| | | | ];
        [inversion Hskip|assumption].
    - repeat constructor; [assumption|now inversion 1|].
      apply Hxni.
      rename H into Hfree.
      unfold bool_var, tovar in *.
      cases; inversion Hfree; subst; eauto.
  Qed.

  Lemma translate_eqns_Fusible:
    forall vars mems inputs eqs,
      wc_env vars ->
      NoDupMembers vars ->
      Forall (wc_equation vars) eqs ->
      Is_well_sch inputs mems eqs ->
      (forall x, PS.In x mems -> ~ Is_variable_in x eqs) ->
      (forall input, In input inputs -> ~ Is_defined_in input eqs) ->
      Fusible (translate_eqns mems eqs).
  Proof.
    intros ** Hwk Hnd Hwks Hwsch Hnvi Hnin.
    induction eqs as [|eq eqs IH]; [now constructor|].
    inversion_clear Hwks as [|?? Hwkeq];
      inversion_clear Hwsch as [|??? HH Hndef].
    unfold translate_eqns.
    simpl; apply Fusible_fold_left_shift.
    split.
    - apply IH; auto.
      + intros x Hin; apply Hnvi in Hin.
        intro; apply Hin; right; auto.
      + intros x Hin; apply Hnin in Hin.
        intro; apply Hin; right; auto.
    - clear IH.
      repeat constructor.
      destruct eq as [x ck e|x ck e|x ck v0 e|s xs ck ? f es]; simpl.
      + assert (~PS.In x mems) as Hnxm
            by (intro Hin; apply Hnvi with (1:=Hin); repeat constructor).
        assert (forall i, Is_free_in_caexp i ck e -> x <> i) as Hfni.
        { intros i Hfree.
          assert (Hfree': Is_free_in_eq i (EqDef x ck e)) by auto.
          eapply HH in Hfree'.
          intro; subst.
          apply mem_spec_false in Hnxm; rewrite Hnxm in Hfree'.
          destruct Hfree' as [Hvar|Hin].
          - eapply Hndef; eauto using Is_defined_in_eq.
            apply Is_variable_in_Is_defined_in; auto.
          - eapply Hnin; eauto.
            left; constructor.
        }
        apply Fusible_Control_caexp.
        * intros; apply not_Can_write_in_translate_cexp.
          eapply Hfni; auto.
        * apply Fusible_translate_cexp.
          intros; apply Hfni; intuition.
      + apply Fusible_Control_laexp; auto.
        assert (~Is_free_in_clock x ck) as Hnfree
            by (eapply wc_EqNext_not_Is_free_in_clock; eauto).
        inversion 2; subst;  contradiction.
      + apply Fusible_Control_laexp; auto.
        inversion 2; contradiction.
      + apply Fusible_Control_laexp; auto.
        intros ** Hwrite.
        assert (In x xs) by now inv Hwrite.
        now eapply wc_EqCall_not_Is_free_in_clock; eauto.
  Qed.

  Lemma reset_mems_Fusible:
    forall mems,
      Fusible (reset_mems mems).
  Proof.
    intro; unfold reset_mems.
    assert (Fusible Skip) as Hf by auto.
    revert Hf; generalize Skip.
    induction mems as [|(x, (c, ck))]; intros s Hf; simpl; auto.
  Qed.
  Hint Resolve reset_mems_Fusible.

  Lemma reset_insts_Fusible:
    forall blocks,
      Fusible (reset_insts blocks).
  Proof.
    intro; unfold reset_insts.
    assert (Fusible Skip) as Hf by auto.
    revert Hf; generalize Skip.
    induction blocks as [|(x, f)]; intros s Hf; simpl; auto.
  Qed.
  Hint Resolve reset_insts_Fusible.

  Lemma ClassFusible_translate:
    forall P,
      wc_program P ->
      Well_scheduled P ->
      Forall ClassFusible (translate P).
  Proof.
    induction P as [|b]; intros ** WC Wsch;
      inversion_clear WC as [|??? WCb];
      inversion_clear Wsch as [|??? Wsch'];
      simpl; constructor; auto.
    unfold translate_block, ClassFusible; simpl.
    repeat constructor; simpl; auto.
    inversion_clear WCb as [? (?&?&?)].
    eapply translate_eqns_Fusible; eauto.
    - rewrite fst_NoDupMembers, map_app, 2 map_fst_idck.
      rewrite 2 map_app, <-app_assoc, NoDup_swap.
      apply NoDup_comm; rewrite <-app_assoc; apply b_nodup.
    - intros; eapply Is_last_in_not_Is_variable_in; eauto.
      rewrite lasts_of_In, <-ps_from_list_In, <-b_lasts_in_eqs; auto.
    - intros; apply b_ins_not_def, fst_InMembers; auto.
  Qed.

End SB2OBCINVARIANTS.

Module SB2ObcInvariantsFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX       Op)
       (Clks   : CLOCKS          Ids)
       (Str    : STREAM              Op OpAux)
       (CE     : COREEXPR       Ids Op OpAux Clks Str)
       (SB     : SYBLOC          Ids Op OpAux Clks Str CE)
       (Obc    : OBC             Ids Op OpAux)
       (Trans  : TRANSLATION     Ids Op OpAux Clks CE.Syn SB.Syn Obc.Syn)
  <: SB2OBCINVARIANTS Ids Op OpAux Clks Str CE SB Obc Trans.
  Include SB2OBCINVARIANTS Ids Op OpAux Clks Str CE SB Obc Trans.
End SB2ObcInvariantsFun.
