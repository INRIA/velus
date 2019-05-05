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
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX       Op)
       (Import Str   : STREAM              Op OpAux)
       (Import CE    : COREEXPR    Ids Op OpAux Str)
       (Import SB    : SYBLOC      Ids Op OpAux Str CE)
       (Import Obc   : OBC         Ids Op OpAux)
       (Import Trans : TRANSLATION Ids Op OpAux CE.Syn SB.Syn Obc.Syn).

  (** ** Show that the Obc code that results from translating a SyBloc
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

  Lemma Is_free_translate_lexp:
    forall x mems e,
      Is_free_in_exp x (translate_lexp mems e) -> Is_free_in_lexp x e.
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
      (forall y, Is_free_in_cexp y e -> x <> y) ->
      Fusible (translate_cexp mems x e).
  Proof.
    intros * Hfree.
    induction e; eauto using Fusible.
    - simpl; constructor;
        [apply IHe1; now auto|apply IHe2; now auto|].
      intros * Hfree'; split;
        (apply not_Can_write_in_translate_cexp;
         apply Is_free_in_tovar in Hfree';
         subst; apply Hfree; constructor).
    - simpl; constructor;
        [apply IHe1; now auto|apply IHe2; now auto|].
      intros * Hfree'; split;
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
    intros * Hxni Hfce; simpl.
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

  Lemma translate_eqns_Fusible:
    forall P vars mems clkvars inputs eqs,
      wc_env vars ->
      NoDupMembers vars ->
      Forall (wc_equation P vars) eqs ->
      Is_well_sch inputs mems eqs ->
      (forall x, PS.In x mems -> ~ Is_variable_in x eqs) ->
      (forall input, In input inputs -> ~ Is_defined_in input eqs) ->
      Fusible (translate_eqns mems clkvars eqs).
  Proof.
    intros * Hwk Hnd Hwks Hwsch Hnvi Hnin.
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
      destruct eq as [x ck e|x ck|x ck v0|s xs ck ? f es]; simpl.
      + assert (~PS.In x mems) as Hnxm
            by (intro Hin; apply Hnvi with (1:=Hin); repeat constructor).
        assert (forall i, Is_free_in_caexp i ck e -> x <> i) as Hfni.
        { intros i Hfree.
          assert (Hfree': Is_free_in_eq i (EqDef x ck e)) by auto.
          eapply HH in Hfree'.
          intro; subst.
          apply PSE.MP.Dec.F.not_mem_iff in Hnxm; rewrite Hnxm in Hfree'.
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
        intros ?? Hwrite.
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
    induction P as [|b]; intros * WC Wsch;
      inversion_clear WC as [|??? WCb];
      inversion_clear Wsch as [|??? Wsch'];
      simpl; constructor; auto.
    unfold translate_block, ClassFusible; simpl.
    repeat constructor; simpl; auto.
    inversion_clear WCb as [? (?&?&?)].
    eapply translate_eqns_Fusible; eauto.
    - rewrite fst_NoDupMembers, map_app, 2 map_fst_idck.
      rewrite 2 map_app, <-2 app_assoc.
      apply b_nodup.
    - intros; eapply Is_last_in_not_Is_variable_in; eauto.
      rewrite lasts_of_In, <-ps_from_list_In, <-b_lasts_in_eqs; auto.
    - intros; apply b_ins_not_def, fst_InMembers; auto.
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

  Lemma No_Overwrites_translate_cexp:
    forall mems x e,
      No_Overwrites (translate_cexp mems x e).
  Proof.
    induction e; simpl; auto.
  Qed.

  Lemma Can_write_in_translate_eqn_Is_defined_in_eq:
    forall mems clkvars eq x,
      Can_write_in x (translate_eqn mems clkvars eq) <-> Is_defined_in_eq x eq.
  Proof.
    destruct eq; simpl; split; intro HH;
      rewrite Can_write_in_Control in *;
      try rewrite Can_write_in_translate_cexp in *;
      subst; try inversion_clear HH; auto using Is_defined_in_eq.
    contradiction.
  Qed.

  Lemma Can_write_in_translate_eqns_Is_defined_in:
    forall mems clkvars eqs x,
      Can_write_in x (translate_eqns mems clkvars eqs) <-> Is_defined_in x eqs.
  Proof.
    unfold translate_eqns.
    intros mems clkvars eqs x.
    match goal with |- ?P <-> ?Q => cut (P <-> (Q \/ Can_write_in x Skip)) end.
    now intro HH; setoid_rewrite HH; split; auto; intros [|H]; [intuition| inv H].
    generalize Skip.
    induction eqs as [|eq eqs IH]; simpl; intro s.
    now split; intro HH; auto; destruct HH as [HH|HH]; auto; inv HH.
    rewrite IH, Can_write_in_Comp, Can_write_in_translate_eqn_Is_defined_in_eq.
    split.
    - intros [HH|[HH|HH]]; auto; left; now constructor.
    - intros [HH|HH]; [inv HH|]; auto.
  Qed.

  Lemma translate_node_cannot_write_inputs:
    forall b m,
      In m (translate_block b).(c_methods) ->
      Forall (fun x => ~Can_write_in x m.(m_body)) (map fst m.(m_in)).
  Proof.
    intros * Hin.
    destruct Hin as [|[|]]; simpl in *; subst; simpl;
      auto; try contradiction.
    apply Forall_forall; intros x Hin.
    apply fst_InMembers, InMembers_idty in Hin.
    rewrite Can_write_in_translate_eqns_Is_defined_in.
    now apply b_ins_not_def.
  Qed.

  Corollary translate_cannot_write_inputs:
    forall P,
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in x (m_body m)) (map fst (m_in m)))
                     (translate P).
  Proof.
    intros; apply Forall_forall; intros * HinP; apply Forall_forall; intros.
    unfold translate in HinP; apply in_map_iff in HinP as (?&?&?); subst; eauto.
    eapply translate_node_cannot_write_inputs; eauto.
  Qed.

  (* Here, we use [Is_well_sch] because it simplifies the inductive proof
     (many of the required lemmas already exist), but in fact, the weaker
     property that no two equations define the same variable is sufficient. *)

  Lemma translate_eqns_No_Overwrites:
    forall clkvars mems inputs eqs,
      Is_well_sch inputs mems eqs ->
      No_Overwrites (translate_eqns mems clkvars eqs).
  Proof.
    unfold translate_eqns.
    intros clkvars mems inputs eqs.
    pose proof NoOSkip as Hs; revert Hs.
    assert (forall x, Is_defined_in x eqs -> ~Can_write_in x Skip) as Hdcw
        by inversion 2; revert Hdcw.
    assert (forall x, Can_write_in x Skip -> ~Is_defined_in x eqs) as Hcwd
        by inversion 1; revert Hcwd.
    generalize Skip.
    induction eqs as [|eq eqs IH]; auto.
    intros s Hcwd Hdcw Hno Hwsch.
    inversion_clear Hwsch as [|? ? Hwsch' Hfree Hddef Hstates];
      clear Hfree Hstates.
    simpl. apply IH; auto.
    - setoid_rewrite Can_write_in_Comp.
      setoid_rewrite Can_write_in_translate_eqn_Is_defined_in_eq.
      intros x [Hdef|Hcw]; auto.
      apply Hcwd, not_Is_defined_in_cons in Hcw as (? & ?); auto.
    - setoid_rewrite cannot_write_in_Comp.
      setoid_rewrite Can_write_in_translate_eqn_Is_defined_in_eq.
      intros H Hdefs. split.
      + intro Hdef; apply Hddef in Hdef. contradiction.
      + apply Hdcw. now constructor 2.
    - constructor; auto.
      + setoid_rewrite Can_write_in_translate_eqn_Is_defined_in_eq.
        intros x Hdef. apply Hdcw. now constructor.
      + setoid_rewrite Can_write_in_translate_eqn_Is_defined_in_eq.
        intros x Hcw. apply Hcwd, not_Is_defined_in_cons in Hcw as (? & ?); auto.
      + destruct eq; simpl; setoid_rewrite No_Overwrites_Control;
          auto using No_Overwrites_translate_cexp.
  Qed.

  Lemma not_Can_write_in_reset_insts:
    forall x blocks,
      ~ Can_write_in x (reset_insts blocks).
  Proof.
    unfold reset_insts; intros.
    assert (~ Can_write_in x Skip) as CWIS by inversion 1.
    revert CWIS; generalize Skip.
    induction blocks; simpl; auto.
    intros; apply IHblocks.
    inversion_clear 1 as [| | | | | |??? CWI]; try inv CWI; contradiction.
  Qed.

  Lemma No_Overwrites_reset_inst:
    forall blocks,
      No_Overwrites (reset_insts blocks).
  Proof.
    unfold reset_insts; intros.
    assert (No_Overwrites Skip) as NOS by constructor.
    revert NOS; generalize Skip.
    induction blocks; simpl; auto.
    intros; apply IHblocks.
    constructor; auto.
    - inversion 2; contradiction.
    - inversion 1; contradiction.
  Qed.

  Lemma No_Overwrites_reset_mems:
    forall lasts,
      NoDupMembers lasts ->
      No_Overwrites (reset_mems lasts).
  Proof.
    unfold reset_mems; intros * Nodup.
    assert (No_Overwrites Skip) as NOS by constructor.
    assert (forall x, InMembers x lasts -> ~ Can_write_in x Skip) as CWIS by inversion 2.
    revert NOS CWIS; generalize Skip.
    induction lasts as [|(x, (c0, ck))]; simpl; auto; inv Nodup.
    intros; apply IHlasts; auto.
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
    - intros; apply not_Can_write_in_reset_insts.
    - intros * CWI ?; eapply not_Can_write_in_reset_insts; eauto.
    - apply No_Overwrites_reset_mems, b_nodup_lasts.
    - apply No_Overwrites_reset_inst.
  Qed.

  Lemma translate_node_No_Overwrites:
    forall b m,
      Is_well_sch (map fst (b_in b)) (ps_from_list (map fst (b_lasts b))) (b_eqs b) ->
      In m (translate_block b).(c_methods) ->
      No_Overwrites m.(m_body).
  Proof.
    intros ??? Hin.
    destruct Hin as [|[|]]; simpl in *; subst; simpl;
      try contradiction.
    - eapply translate_eqns_No_Overwrites; eauto.
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
    eapply translate_node_No_Overwrites; eauto.
  Qed.

End SB2OBCINVARIANTS.

Module SB2ObcInvariantsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Op)
       (Str   : STREAM          Op OpAux)
       (CE    : COREEXPR    Ids Op OpAux Str)
       (SB    : SYBLOC      Ids Op OpAux Str CE)
       (Obc   : OBC         Ids Op OpAux)
       (Trans : TRANSLATION Ids Op OpAux CE.Syn SB.Syn Obc.Syn)
  <: SB2OBCINVARIANTS Ids Op OpAux Str CE SB Obc Trans.
  Include SB2OBCINVARIANTS Ids Op OpAux Str CE SB Obc Trans.
End SB2ObcInvariantsFun.
