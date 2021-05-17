From Coq Require Import FSets.FMapPositive.
From Coq Require Import PArith.

From Velus Require Import Stc.
From Velus Require Import Obc.
From Velus Require Import StcToObc.Translation.

From Velus Require Import Common.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STC2OBCINVARIANTS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import Str   : INDEXEDSTREAMS  Op OpAux)
       (Import CE    : COREEXPR    Ids Op OpAux Str)
       (Import Stc   : STC         Ids Op OpAux Str CE)
       (Import Obc   : OBC         Ids Op OpAux)
       (Import Trans : TRANSLATION Ids Op OpAux CE.Syn Stc.Syn Obc.Syn).

  (** ** Show that the Obc code that results from translating a Stc
         program satisfies the [Fusible] invariant, and thus that fusion
         preserves its semantics. *)

  Lemma not_Can_write_in_translate_cexp:
    forall x mems e y,
      x <> y -> ~ Can_write_in y (translate_cexp mems x e).
  Proof.
    induction e; intros ?? Hcw; inv Hcw; intuition eauto.
  Qed.

  Lemma Is_free_in_tovar:
    forall mems x y ty,
      Is_free_in_exp y (tovar mems (x, ty)) <-> x = y.
  Proof.
    unfold tovar; intros.
    cases; split; intro HH;
      (inversion_clear HH; reflexivity || subst; now constructor).
  Qed.

  Lemma Is_free_translate_exp:
    forall x mems e,
      Is_free_in_exp x (translate_exp mems e) -> CE.IsF.Is_free_in_exp x e.
  Proof.
    induction e; simpl; intro H; auto.
    - inversion H.
    - now apply Is_free_in_tovar in H; subst.
    - constructor; inversion H; auto.
    - constructor; inversion_clear H as [| | |????? [?|?]|]; subst;
        [left; auto | right; auto].
  Qed.

  Lemma Fusible_translate_cexp:
    forall mems x e,
      ~ Is_free_in_cexp x e ->
      Fusible (translate_cexp mems x e).
  Proof.
    intros * Hfree.
    induction e; eauto using Fusible.
    - simpl; constructor;
        [apply IHe1; now auto|apply IHe2; now auto|].
      intros * Hfree'; split;
        apply not_Can_write_in_translate_cexp;
        apply Is_free_in_tovar in Hfree';
        intro; subst;
          apply Hfree; constructor.
    - simpl; constructor;
        [apply IHe1; now auto|apply IHe2; now auto|].
      intros * Hfree'; split;
        apply not_Can_write_in_translate_cexp;
        apply Is_free_translate_exp in Hfree';
        intro; subst;
          apply Hfree; constructor; auto.
  Qed.

  Lemma Fusible_Control:
    forall mems ck s,
      (forall x, Is_free_in_clock x ck -> ~ Can_write_in x s) ->
      Fusible s ->
      Fusible (Control mems ck s).
  Proof.
    induction ck as [|ck IH i b]; [now intuition|].
    intros * Hxni Hfce; simpl.
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

  Lemma translate_tcs_Fusible:
    forall P vars mems clkvars inputs tcs,
      wc_env vars ->
      NoDupMembers vars ->
      Forall (wc_trconstr P vars) tcs ->
      NoDup (variables tcs) ->
      Is_well_sch inputs mems tcs ->
      (forall x, PS.In x mems -> ~ Is_variable_in x tcs) ->
      (forall input, In input inputs -> ~ Is_variable_in input tcs) ->
      Fusible (translate_tcs mems clkvars tcs).
  Proof.
    intros * Hwk Hnd Hwks Vars Hwsch Hnvi Hnin.
    induction tcs as [|tc tcs IH]; [now constructor|].
    assert (NoDup (variables tcs))
      by (simpl in Vars; rewrite Permutation.Permutation_app_comm in Vars;
          apply NoDup_app_weaken in Vars; auto).
    inversion_clear Hwks as [|?? Hwktc];
      inversion_clear Hwsch as [|??? HH HN].
    unfold translate_tcs.
    simpl; apply Fusible_fold_left_shift.
    split.
    - apply IH; auto.
      + intros x Hin; apply Hnvi in Hin.
        intro; apply Hin; right; auto.
      + intros x Hin; apply Hnin in Hin.
        intro; apply Hin; right; auto.
    - clear IH.
      repeat constructor.
      destruct tc as [x ck e|x ckr c0|x ck|x ck v0|s xs ck ? f es]; simpl.
      + assert (~PS.In x mems) as Hnxm
            by (intro Hin; apply Hnvi with (1:=Hin); repeat constructor).
        assert (forall i, Is_free_in_caexp i ck e -> x <> i) as Hfni.
        { intros i Hfree.
          assert (Hfree': Is_free_in_tc i (TcDef x ck e)) by auto.
          eapply HH in Hfree'.
          intro; subst.
          apply PSE.MP.Dec.F.not_mem_iff in Hnxm; rewrite Hnxm in Hfree'.
          destruct Hfree' as [Hvar|Hin].
          - simpl in Vars.
            inversion_clear Vars as [|?? Hin]; apply Hin, Is_variable_in_variables; auto.
          - eapply Hnin; eauto.
            left; constructor.
        }
        apply Fusible_Control.
        * intros; apply not_Can_write_in_translate_cexp.
          eapply Hfni; auto.
        * apply Fusible_translate_cexp.
          intro; eapply Hfni; eauto.
      + apply Fusible_Control; auto.
        intros x' Hfree CanWrite. inv CanWrite.
        specialize (HN _ _ (ResetTcReset _ _ _)) as (HN&_).
        apply HN; left; auto.
      + apply Fusible_Control; auto.
        assert (~Is_free_in_clock x ck) as Hnfree
            by (eapply wc_TcNext_not_Is_free_in_clock; eauto).
        inversion 2; subst;  contradiction.
      + apply Fusible_Control; auto.
        inversion 2; contradiction.
      + apply Fusible_Control; auto.
        intros ?? Hwrite.
        assert (In x xs) by now inv Hwrite.
        now eapply wc_TcStep_not_Is_free_in_clock; eauto.
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

  Lemma Is_next_in_not_Is_variable_in:
    forall s x,
      Is_next_in x (s_tcs s) ->
      ~ Is_variable_in x (s_tcs s).
  Proof.
    intros * Hreset Hvar.
    assert (In x (nexts_of (s_tcs s))) as Hreset' by (eapply nexts_of_In; eauto).
    rewrite <-s_nexts_in_tcs in Hreset'.
    rewrite Is_variable_in_variables, <-s_vars_out_in_tcs in Hvar.
    pose proof (s_nodup s) as Nodup.
    repeat rewrite app_assoc in *.
    eapply NoDup_app_In in Nodup; eauto.
    repeat rewrite in_app_iff in *. destruct Hvar; auto.
  Qed.

  Theorem ClassFusible_translate:
    forall P,
      wc_program P ->
      Well_scheduled P ->
      Forall ClassFusible (translate P).
  Proof.
    induction P as [|s]; intros * WC Wsch;
      inversion_clear WC as [|??? WCb];
      inversion_clear Wsch as [|??? Wsch'];
      simpl; constructor; auto.
    unfold translate_system, ClassFusible; simpl.
    repeat constructor; simpl; auto.
    inversion_clear WCb as [? (?&?&?)].
    assert (NoDup (variables (s_tcs s))) by apply s_nodup_variables.
    eapply translate_tcs_Fusible; eauto.
    - rewrite fst_NoDupMembers, map_app, 2 map_fst_idck.
      rewrite 2 map_app, <-2 app_assoc.
      apply s_nodup.
    - intros * Hin.
      rewrite ps_from_list_In, s_nexts_in_tcs in Hin; auto.
      eapply nexts_of_In in Hin.
      eapply Is_next_in_not_Is_variable_in; eauto.
    - intros; apply s_ins_not_var, fst_InMembers; auto.
  Qed.

  (** Translating gives [No_Overwrites] Obc. *)

  Lemma Can_write_in_Control:
    forall mems ck s x,
      Can_write_in x (Control mems ck s) <-> Can_write_in x s.
  Proof.
    induction ck; simpl; try reflexivity.
    destruct b; setoid_rewrite IHck; split; auto;
      inversion_clear 1; auto;
        match goal with H:Can_write_in _ Skip |- _ => inv H end.
  Qed.

  Lemma Can_write_in_var_Control:
    forall mems ck s x,
      Can_write_in_var x (Control mems ck s) <-> Can_write_in_var x s.
  Proof.
    induction ck; simpl; try reflexivity.
    destruct b; setoid_rewrite IHck; split; auto;
      inversion_clear 1; auto;
        match goal with H:Can_write_in_var _ Skip |- _ => inv H end.
  Qed.

  Lemma No_Overwrites_Control:
    forall mems ck s,
      No_Overwrites (Control mems ck s) <-> No_Overwrites s.
  Proof.
    induction ck; simpl; try reflexivity.
    destruct b; setoid_rewrite IHck; split; auto;
      inversion_clear 1; auto.
  Qed.

  Lemma Can_write_in_translate_cexp:
    forall mems e x y,
      Can_write_in x (translate_cexp mems y e) <-> x = y.
  Proof.
    induction e; simpl;
      try setoid_rewrite Can_write_in_Ifte;
      try setoid_rewrite IHe1;
      try setoid_rewrite IHe2.
    now intuition. now intuition.
    split. now inversion_clear 1.
    now intro; subst; auto.
  Qed.

  Lemma Can_write_in_var_translate_cexp:
    forall mems e x y,
      Can_write_in_var x (translate_cexp mems y e) <-> x = y.
  Proof.
    induction e; simpl;
      try setoid_rewrite Can_write_in_var_Ifte;
      try setoid_rewrite IHe1;
      try setoid_rewrite IHe2.
    now intuition. now intuition.
    split. now inversion_clear 1.
    now intro; subst; auto.
  Qed.

  Lemma No_Overwrites_translate_cexp:
    forall mems x e,
      No_Overwrites (translate_cexp mems x e).
  Proof.
    induction e; simpl; auto.
  Qed.

  Lemma Can_write_in_var_translate_tc_Is_variable_in_tc:
    forall mems clkvars tc x,
      Can_write_in_var x (translate_tc mems clkvars tc) <-> Is_variable_in_tc x tc.
  Proof.
    destruct tc; simpl; split; intros * HH;
      try destruct o as [(?&?)|];
      try rewrite Can_write_in_var_Control in *;
      try rewrite Can_write_in_var_translate_cexp in *;
      subst; try inversion_clear HH; auto using Is_variable_in_tc.
    contradiction.
  Qed.

  Lemma Can_write_in_var_translate_tcs_Is_variable_in:
    forall mems clkvars tcs x,
      Can_write_in_var x (translate_tcs mems clkvars tcs) <-> Is_variable_in x tcs.
  Proof.
    unfold translate_tcs.
    intros mems clkvars tcs x.
    match goal with |- ?P <-> ?Q => cut (P <-> (Q \/ Can_write_in_var x Skip)) end.
    now intros HH; setoid_rewrite HH; split; auto; intros [|H]; [intuition|inv H].
    generalize Skip.
    induction tcs as [|tc tcs IH]; simpl; intros s.
    now split; intro HH; auto; destruct HH as [HH|HH]; auto; inv HH.
    rewrite IH, Can_write_in_var_Comp, Can_write_in_var_translate_tc_Is_variable_in_tc.
    split.
    - intros [HH|[HH|HH]]; auto; left; now constructor.
    - intros [HH|HH]; [inv HH|]; auto.
  Qed.

  (* Here, we use [Is_well_sch] because it simplifies the inductive proof
     (many of the required lemmas already exist), but in fact, the weaker
     property that no two trconstrs define the same variable is sufficient. *)

  Lemma translate_tcs_No_Overwrites:
    forall clkvars mems inputs tcs,
      NoDup (variables tcs) ->
      Is_well_sch inputs mems tcs ->
      No_Overwrites (translate_tcs mems clkvars tcs).
  Proof.
    unfold translate_tcs.
    intros clkvars mems inputs tcs.
    pose proof NoOSkip as Hs; revert Hs.
    assert (forall x, Is_variable_in x tcs -> ~Can_write_in_var x Skip) as Hdcw
        by inversion 2; revert Hdcw.
    assert (forall x, Can_write_in_var x Skip -> ~Is_variable_in x tcs) as Hcwd
        by inversion 1; revert Hcwd.
    generalize Skip.
    induction tcs as [|tc tcs IH]; auto.
    intros s Hcwd Hdcw Hno Nodup Hwsch.
    inversion_clear Hwsch as [|? ? Hwsch' Hfree Hnext _].
    assert (forall x, Is_variable_in_tc x tc -> ~ Is_variable_in x tcs) as Defs
        by (intro; rewrite Is_variable_in_variables, Is_variable_in_tc_variables;
            simpl in Nodup; intros; eapply NoDup_app_In in Nodup; eauto).
    simpl. apply IH; auto.
    - setoid_rewrite Can_write_in_var_Comp.
      setoid_rewrite Can_write_in_var_translate_tc_Is_variable_in_tc.
      intros x [Hvar|Hcw]; auto.
      apply Hcwd, not_Is_variable_in_cons in Hcw as (? & ?); auto.
    - setoid_rewrite cannot_write_in_var_Comp.
      setoid_rewrite Can_write_in_var_translate_tc_Is_variable_in_tc.
      intros ? Hdef. split; intro Hcw.
      + eapply Defs; eauto.
      + apply Hdcw in Hcw; auto. now constructor 2.
    - constructor; auto.
      + setoid_rewrite Can_write_in_var_translate_tc_Is_variable_in_tc.
        intros x Hdef. apply Hdcw; left; auto.
      + setoid_rewrite Can_write_in_var_translate_tc_Is_variable_in_tc.
        intros x Hcw. apply Hcwd, not_Is_variable_in_cons in Hcw as (? & ?); auto.
      + destruct tc; simpl;
          try destruct o as [(?&?)|];
          try setoid_rewrite No_Overwrites_Control;
          auto using No_Overwrites_translate_cexp.
    - simpl in Nodup; rewrite Permutation.Permutation_app_comm in Nodup;
        apply NoDup_app_weaken in Nodup; auto.
  Qed.

  Lemma not_Can_write_in_var_reset_insts:
    forall x subs,
      ~ Can_write_in_var x (reset_insts subs).
  Proof.
    unfold reset_insts; intros.
    assert (~ Can_write_in_var x Skip) as CWIS by inversion 1.
    revert CWIS; generalize Skip.
    induction subs; simpl; auto.
    intros; apply IHsubs.
    inversion_clear 1 as [| | | | |??? CWI]; try inv CWI; contradiction.
  Qed.

  Lemma No_Overwrites_reset_inst:
    forall subs,
      No_Overwrites (reset_insts subs).
  Proof.
    unfold reset_insts; intros.
    assert (No_Overwrites Skip) as NOS by constructor.
    revert NOS; generalize Skip.
    induction subs; simpl; auto.
    intros; apply IHsubs.
    constructor; auto.
    - inversion 2; contradiction.
    - inversion 1; contradiction.
  Qed.

  Lemma No_Overwrites_reset_mems:
    forall resets,
      NoDupMembers resets ->
      No_Overwrites (reset_mems resets).
  Proof.
    unfold reset_mems; intros * Nodup.
    assert (No_Overwrites Skip) as NOS by constructor.
    assert (forall x, InMembers x resets -> ~ Can_write_in x Skip) as CWIS by inversion 2.
    revert NOS CWIS; generalize Skip.
    induction resets as [|(x, (c0, ck))]; simpl; auto; inv Nodup.
    intros; apply IHresets; auto.
    - constructor; auto.
      + inversion 2; subst; eapply CWIS; eauto.
      + inversion_clear 1; auto.
    - inversion_clear 2 as [| | | | | |??? CWI];
        try inv CWI; subst; auto.
      eapply CWIS; eauto.
  Qed.

  Corollary translate_reset_No_Overwrites:
    forall b,
      No_Overwrites (translate_reset b).
  Proof.
    intro; unfold translate_reset.
    constructor.
    - intros; apply not_Can_write_in_var_reset_insts.
    - intros * CWI ?; eapply not_Can_write_in_var_reset_insts; eauto.
    - apply No_Overwrites_reset_mems, s_nodup_nexts.
    - apply No_Overwrites_reset_inst.
  Qed.

  Lemma translate_system_No_Overwrites:
    forall b m,
      Is_well_sch (map fst (s_in b)) (ps_from_list (map fst (s_nexts b))) (s_tcs b) ->
      In m (translate_system b).(c_methods) ->
      No_Overwrites m.(m_body).
  Proof.
    intros ??? Hin.
    destruct Hin as [|[|]]; simpl in *; subst; simpl;
      try contradiction.
    - eapply translate_tcs_No_Overwrites; eauto.
      apply s_nodup_variables.
    - apply translate_reset_No_Overwrites.
  Qed.

  Corollary translate_No_Overwrites:
    forall P,
      Well_scheduled P ->
      Forall_methods (fun m => No_Overwrites m.(m_body)) (translate P).
  Proof.
    intros * Wsch; apply Forall_forall; intros * HinP; apply Forall_forall; intros.
    unfold translate in HinP; apply in_map_iff in HinP as (?&?&?); subst; eauto.
    eapply Forall_forall in Wsch; eauto.
    eapply translate_system_No_Overwrites; eauto.
  Qed.

  (** ** The node doesn't write its inputs *)

  Lemma Can_write_in_translate_tc_Is_variable_in_tc:
    forall mems clkvars tc x,
      Can_write_in x (translate_tc mems clkvars tc) ->
      Is_variable_in_tc x tc \/ (exists ck, Is_reset_in_tc x ck tc) \/ Is_next_in_tc x tc.
  Proof.
    destruct tc; simpl; intros * HH;
      try destruct o as [(?&?)|];
      try rewrite Can_write_in_Control in *;
      try rewrite Can_write_in_translate_cexp in *;
      subst; try inversion_clear HH; eauto using Is_variable_in_tc, Is_reset_in_tc, Is_next_in_tc.
    contradiction.
  Qed.

  Lemma Can_write_in_translate_tcs_Is_variable_in:
    forall mems clkvars tcs x,
      Can_write_in x (translate_tcs mems clkvars tcs) ->
      Is_variable_in x tcs \/ (exists ck, Is_reset_in x ck tcs) \/ Is_next_in x tcs.
  Proof.
    unfold translate_tcs.
    intros mems clkvars tcs x.
    match goal with |- ?P -> ?Q => cut (P -> (Q \/ Can_write_in x Skip)) end.
    now intros HH H; apply HH in H as [?|?]; auto; inv H.
    generalize Skip.
    induction tcs as [|tc tcs IH]; simpl; intros s HH; auto.
    apply IH in HH as [HH|HH]; [|inv HH]; auto.
    - left. destruct HH as [HH|[(ck&HH)|HH]]; [left|right;left|right;right]; try exists ck; right; auto.
    - left. apply Can_write_in_translate_tc_Is_variable_in_tc in H1 as [?|[(ck&?)|?]];
              [left|right;left|right;right]; try exists ck; left; auto.
  Qed.

  Lemma translate_system_cannot_write_inputs:
    forall s m,
      In m (translate_system s).(c_methods) ->
      Forall (fun x => ~Can_write_in x m.(m_body)) (map fst m.(m_in)).
  Proof.
    intros * Hin.
    destruct Hin as [|[|]]; simpl in *; subst; simpl;
      auto; try contradiction.
    apply Forall_forall; intros x Hin.
    apply fst_InMembers, InMembers_idty in Hin. intro contra.
    apply Can_write_in_translate_tcs_Is_variable_in in contra as [H|[(?&H)|H]].
    - eapply s_ins_not_var in H; eauto.
    - eapply s_ins_not_reset in H; eauto.
    - eapply s_ins_not_next in H; eauto.
  Qed.

  Corollary translate_cannot_write_inputs:
    forall P,
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in x (m_body m)) (map fst (m_in m)))
                     (translate P).
  Proof.
    intros; apply Forall_forall; intros * HinP; apply Forall_forall; intros.
    unfold translate in HinP; apply in_map_iff in HinP as (?&?&?); subst; eauto.
    eapply translate_system_cannot_write_inputs; eauto.
  Qed.

End STC2OBCINVARIANTS.

Module Stc2ObcInvariantsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Op)
       (Str   : INDEXEDSTREAMS  Op OpAux)
       (CE    : COREEXPR    Ids Op OpAux Str)
       (Stc   : STC         Ids Op OpAux Str CE)
       (Obc   : OBC         Ids Op OpAux)
       (Trans : TRANSLATION Ids Op OpAux CE.Syn Stc.Syn Obc.Syn)
  <: STC2OBCINVARIANTS Ids Op OpAux Str CE Stc Obc Trans.
  Include STC2OBCINVARIANTS Ids Op OpAux Str CE Stc Obc Trans.
End Stc2ObcInvariantsFun.
