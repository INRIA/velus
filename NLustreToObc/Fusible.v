Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.

Require Import Velus.NLustre.
Require Import Velus.Obc.
Require Import Velus.NLustreToObc.Translation.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type FUSIBLE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS Ids)
       (Import NLus  : Velus.NLustre.NLUSTRE Ids Op OpAux Clks)
       (Import Obc   : Velus.Obc.OBC Ids Op OpAux)
       (Import Trans : Velus.NLustreToObc.Translation.TRANSLATION
                         Ids Op OpAux Clks NLus.ExprSyn NLus.Syn Obc.Syn NLus.Mem).

  (** ** Show that the Obc code that results from translating an NLustre
         program satisfies the [Fusible] invariant, and thus that fusion
         preserves its semantics. *)

  Lemma not_Can_write_in_translate_cexp:
    forall x mems ce i,
      x <> i -> ~ Can_write_in i (translate_cexp mems x ce).
  Proof.
    induction ce; intros j Hxni Hcw.
    - specialize (IHce1 _ Hxni).
      specialize (IHce2 _ Hxni).
      inversion_clear Hcw; intuition.
    - specialize (IHce1 _ Hxni).
      specialize (IHce2 _ Hxni).
      inversion_clear Hcw; intuition.
    - inversion Hcw; intuition.
  Qed.

  Lemma Is_free_in_tovar:
    forall mems i j ty,
      Is_free_in_exp j (tovar mems (i, ty)) <-> i = j.
  Proof.
    unfold tovar.
    intros mems i j ty.
    destruct (PS.mem i mems); split; intro HH;
      (inversion_clear HH; reflexivity || subst; now constructor).
  Qed.

  Lemma Is_free_translate_lexp:
    forall j mems l,
      Is_free_in_exp j (translate_lexp mems l) -> Is_free_in_lexp j l.
  Proof.
    induction l; simpl; intro H.
    - inversion H.
    - now apply Is_free_in_tovar in H; subst.
    - constructor; auto.
    - constructor; inversion H; auto.
    - constructor; inversion H; subst.
      destruct H2; [left; auto | right; auto].
  Qed.

  Lemma Fusible_translate_cexp:
    forall mems x ce,
      (forall i, Is_free_in_cexp i ce -> x <> i)
      -> Fusible (translate_cexp mems x ce).
  Proof.
    intros ** Hfree.
    induction ce.
    - simpl; constructor;
        [apply IHce1; now auto|apply IHce2; now auto|].
      intros j Hfree'; split;
        (apply not_Can_write_in_translate_cexp;
         apply Is_free_in_tovar in Hfree';
         subst; apply Hfree; constructor).
    - simpl; constructor;
        [apply IHce1; now auto|apply IHce2; now auto|].
      intros j Hfree'; split;
        apply not_Can_write_in_translate_cexp;
        apply Hfree;
        now constructor; apply Is_free_translate_lexp with mems.
    - now constructor.
  Qed.

  Lemma Fusible_Control_caexp:
    forall mems ck f ce,
      (forall i, Is_free_in_caexp i ck ce -> ~Can_write_in i (f ce))
      -> Fusible (f ce)
      -> Fusible (Control mems ck (f ce)).
  Proof.
    induction ck as [|ck IH i b]; [now intuition|].
    intros f ce Hxni Hfce.
    simpl.
    destruct b.
    - apply IH with (f:=fun ce=>Ifte (tovar mems (i, bool_type)) (f ce) Skip).
      + intros j Hfree Hcw.
        apply Hxni with (i0:=j); [inversion_clear Hfree; now auto|].
        inversion_clear Hcw as [| | |? ? ? ? Hskip| | |];
          [assumption|inversion Hskip].
      + repeat constructor; [assumption| |now inversion 1].
        apply Hxni.
        match goal with
        | H:Is_free_in_exp _ (tovar mems _) |- _ => rename H into Hfree
        end.
        unfold tovar in Hfree.
        destruct (PS.mem i mems); inversion Hfree; subst; now auto.
    - apply IH with (f:=fun ce=>Ifte (tovar mems (i, bool_type)) Skip (f ce)).
      + intros j Hfree Hcw.
        apply Hxni with (i0:=j); [inversion_clear Hfree; now auto|].
        inversion_clear Hcw as [| |? ? ? ? Hskip| | | |];
          [inversion Hskip|assumption].
      + repeat constructor; [assumption|now inversion 1|].
        apply Hxni.
        match goal with
        | H:Is_free_in_exp _ (tovar mems _) |- _ => rename H into Hfree
        end.
        unfold tovar in Hfree.
        destruct (PS.mem i mems); inversion Hfree; subst; now auto.
  Qed.

  Lemma Fusible_Control_laexp:
    forall mems ck s,
      (forall i, Is_free_in_clock i ck -> ~Can_write_in i s)
      -> Fusible s
      -> Fusible (Control mems ck s).
  Proof.
    induction ck as [|ck IH i b]; [now intuition|].
    intros s Hxni Hfce.
    simpl.
    destruct b; apply IH.
    - intros j Hfree Hcw.
      apply Hxni with (i0:=j); [inversion_clear Hfree; now auto|].
      inversion_clear Hcw as [| | |? ? ? ? Hskip| | |];
        [assumption|inversion Hskip].
    - repeat constructor; [assumption| |now inversion 1].
      apply Hxni.
      rename H into Hfree.
      destruct (PS.mem i mems); inversion Hfree; subst; now auto.
    - intros j Hfree Hcw.
      apply Hxni with (i0:=j); [inversion_clear Hfree; now auto|].
      inversion_clear Hcw as [| |? ? ? ? Hskip| | | | ];
        [inversion Hskip|assumption].
    - repeat constructor; [assumption|now inversion 1|].
      apply Hxni.
      rename H into Hfree.
      destruct (PS.mem i mems); inversion Hfree; subst; now auto.
  Qed.

  Lemma translate_eqns_Fusible:
    forall vars mems inputs eqs,
      wc_env vars
      -> NoDupMembers vars
      -> Forall (wc_equation vars) eqs
      -> Is_well_sch mems inputs eqs
      -> (forall x, PS.In x mems -> ~Is_variable_in_eqs x eqs)
      -> (forall input, In input inputs -> ~ Is_defined_in_eqs input eqs)
      -> Fusible (translate_eqns mems eqs).
  Proof.
    intros ** Hwk Hnd Hwks Hwsch Hnvi Hnin.
    induction eqs as [|eq eqs IH]; [now constructor|].
    inversion Hwks as [|eq' eqs' Hwkeq Hwks']; subst.
    specialize (IH Hwks' (Is_well_sch_cons _ _ _ _ Hwsch)).
    unfold translate_eqns.
    simpl; apply Fusible_fold_left_shift.
    split.
    - apply IH.
      + intros x Hin; apply Hnvi in Hin.
        apply not_Is_variable_in_cons in Hin.
        now intuition.
      + intros x Hin. apply Hnin in Hin.
        apply not_Is_defined_in_cons in Hin.
        now intuition.
    - clear IH.
      repeat constructor.
      destruct eq as [x ck e|x ck f e|x ck v0 e]; simpl.
      + assert (~PS.In x mems) as Hnxm
            by (intro Hin; apply Hnvi with (1:=Hin); repeat constructor).
        inversion_clear Hwsch as [|? ? Hwsch' HH Hndef].
        assert (forall i, Is_free_in_caexp i ck e -> x <> i) as Hfni.
        { intros i Hfree.
          assert (Hfree': Is_free_in_eq i (EqDef x ck e)) by auto.
          eapply HH in Hfree'.
          destruct Hfree' as [Hm Hnm].
          assert (~ In x inputs) as Hninp
              by (intro Hin; eapply Hnin; eauto; do 2 constructor).
          assert (~PS.In x mems) as Hnxm' by intuition.
          intro Hxi; rewrite Hxi in *; clear Hxi.
          specialize (Hnm Hnxm').
          eapply Hndef; intuition.
          now eapply Is_variable_in_eqs_Is_defined_in_eqs.
        }
        apply Fusible_Control_caexp.
        intros i Hfree.
        apply not_Can_write_in_translate_cexp.
        eapply Hfni; auto.
        apply Fusible_translate_cexp.
        intros i Hfree; apply Hfni; intuition.
      + assert (forall i,
                   Is_free_in_clock i ck ->
                   ~ Can_write_in i (Call x f (hd Ids.default x)
                                          step (map (translate_lexp mems) e))).
        {
          intros ** Hwrite.
          assert (In i x) by now inv Hwrite.
          now eapply wc_EqApp_not_Is_free_in_clock; eauto.
        }

        now apply Fusible_Control_laexp.
      + assert (~Is_free_in_clock x ck) as Hnfree
            by (eapply wc_EqFby_not_Is_free_in_clock; eauto).
        apply Fusible_Control_laexp;
          [intros i Hfree Hcw; inversion Hcw; subst; contradiction|intuition].
  Qed.

  Lemma translate_reset_eqns_Fusible:
    forall eqs,
      Fusible (translate_reset_eqns eqs).
  Proof.
    intro eqs.
    unfold translate_reset_eqns.
    assert (Fusible Skip) as Hf by auto.
    revert Hf. generalize Skip.
    induction eqs as [|eq eqs]; intros s Hf; auto.
    simpl. apply IHeqs.
    destruct eq; simpl; auto.
  Qed.

  Lemma ClassFusible_translate:
    forall G,
      wc_global G ->
      Welldef_global G ->
      Forall ClassFusible (translate G).
  Proof.
    induction G as [|n G].
    now intros; simpl; auto using Forall_nil.
    intros WcG WdG.
    inversion_clear WcG as [|? ? Wcn].
    simpl; constructor; auto.
    unfold translate_node, ClassFusible.
    repeat constructor; simpl.
    - rewrite ps_from_list_gather_eqs_memories.
      assert (NoDup_defs n.(n_eqs)).
      apply NoDup_defs_NoDup_vars_defined.
      apply NoDup_var_defined_n_eqs.
      pose proof (not_Exists_Is_defined_in_eqs_n_in n) as Hin.
      inv Wcn. inv WdG. simpl in *.
      eapply translate_eqns_Fusible; eauto.
      + apply NoDupMembers_idck, n_nodup.
      + intros.
        apply not_Is_variable_in_memories; auto.
      + intros i' Hin' Hdef.
        apply Hin, Exists_exists.
        exists i'. intuition.
    - apply translate_reset_eqns_Fusible.
    - inv WdG. apply IHG; auto.
  Qed.

End FUSIBLE.

Module FusibleFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Clks  : CLOCKS Ids)
       (NLus  : Velus.NLustre.NLUSTRE Ids Op OpAux Clks)
       (Obc   : Velus.Obc.OBC Ids Op OpAux)
       (Trans : Velus.NLustreToObc.Translation.TRANSLATION
                         Ids Op OpAux Clks NLus.Syn Obc.Syn NLus.Mem)
       <: FUSIBLE Ids Op OpAux Clks NLus Obc Trans.
  Include FUSIBLE Ids Op OpAux Clks NLus Obc Trans.
End FusibleFun.
