From Coq Require Import FSets.FMapPositive.
From Coq Require Import PArith.

From Velus Require Import Stc.
From Velus Require Import Obc.
From Velus Require Import StcToObc.Translation.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import FunctionalEnvironment.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STC2OBCINVARIANTS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import ComTyp: COMMONTYPING    Ids Op OpAux)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (Import CE    : COREEXPR    Ids Op OpAux ComTyp Cks Str)
       (Import Stc   : STC         Ids Op OpAux ComTyp Cks Str CE)
       (Import Obc   : OBC         Ids Op OpAux ComTyp)
       (Import Trans : TRANSLATION Ids Op OpAux        Cks CE.Syn Stc.Syn Obc.Syn).

  (** ** Show that the Obc code that results from translating a Stc
         program satisfies the [Fusible] invariant, and thus that fusion
         preserves its semantics. *)

  Lemma Can_write_in_translate_cexp:
    forall assign mems e y,
      Can_write_in y (translate_cexp mems assign e) -> exists oe, Can_write_in y (assign oe).
  Proof.
    induction e using cexp_ind2; intros * Hcw; simpl in *.
    - inv Hcw. simpl_Exists. simpl_Forall. eauto.
    - inv Hcw. simpl_Exists. simpl_Forall.
      destruct x; simpl in *; eauto.
    - eauto.
  Qed.

  Lemma Is_free_in_tovar:
    forall mems x y ty,
      Is_free_in_exp (RCurrent y) (tovar mems (x, ty)) <-> x = y.
  Proof.
    unfold tovar; intros.
    cases; split; intro HH;
      (inversion_clear HH; reflexivity || subst; now constructor).
  Qed.

  Lemma Is_free_current_translate_exp:
    forall x mems e,
      Is_free_in_exp (RCurrent x) (translate_exp mems e) ->
      CE.IsF.Is_free_in_exp (FunctionalEnvironment.Var x) e.
  Proof.
    induction e; simpl; intro H; auto with stcfree; try now inv H.
    - apply Is_free_in_tovar in H; subst; auto with stcfree.
    - constructor; inversion H; auto.
    - constructor; inv H; take (_ \/ _) and destruct it; subst; auto.
  Qed.

  Lemma Is_free_last_translate_exp:
    forall x mems e,
      Is_free_in_exp (RLast x) (translate_exp mems e) ->
      CE.IsF.Is_free_in_exp (FunctionalEnvironment.Last x) e.
  Proof.
    induction e; simpl; intro H; auto with stcfree; try now inv H.
    - cases; inv H.
    - inv H. constructor.
    - constructor; inversion H; auto.
    - constructor; inv H; take (_ \/ _) and destruct it; subst; auto.
  Qed.

  Lemma Is_free_last_translate_arg:
    forall x mems ckvars ck e,
      Is_free_in_exp (RLast x) (translate_arg mems ckvars ck e) ->
      CE.IsF.Is_free_in_exp (FunctionalEnvironment.Last x) e.
  Proof.
    destruct e; simpl; intro H; auto with stcfree; try now inv H.
    - cases; inv H.
    - inv H. constructor.
    - constructor; eauto using Is_free_last_translate_exp.
    - constructor; inv H; eauto using Is_free_last_translate_exp.
    - constructor; inv H; take (_ \/ _) and destruct it; eauto using Is_free_last_translate_exp.
  Qed.

  Lemma Is_free_last_translate_cexp:
    forall assign x mems e,
      (forall x oe, Is_free_in_stmt x (assign oe) -> Is_free_in_exp x oe) ->
      Is_free_in_stmt (RLast x) (translate_cexp mems assign e) ->
      CE.IsF.Is_free_in_cexp (FunctionalEnvironment.Last x) e.
  Proof.
    induction e using cexp_ind2; simpl; intros Exp Free.
    - inv Free.
      + unfold tovar in *. cases; inv H2.
      + constructor. solve_Exists. simpl_Forall. eauto.
    - inv Free.
      + constructor. eauto using Is_free_last_translate_exp.
      + simpl_Exists. simpl_Forall. destruct x0; simpl in *.
        * apply FreeEcase_branches. solve_Exists.
        * apply FreeEcase_default. eauto.
    - constructor. eauto using Is_free_last_translate_exp.
  Qed.

  Lemma Is_free_last_Control:
    forall x mems ck stmt,
      Is_free_in_stmt (RLast x) (Control mems ck stmt) ->
      Is_free_in_stmt (RLast x) stmt.
  Proof.
    induction ck; intros * Free; simpl in *; auto.
    destruct p, t. inv Free.
    apply IHck in Free. inv Free.
    - cases; inv H1.
    - simpl_Exists. destruct x0; simpl in *; [|inv H1].
      eapply skip_branches_with_In_det in Hin; subst; eauto.
  Qed.

  Lemma Is_free_last_translate_tc:
    forall x mems clkvars tc,
      Is_free_in_stmt (RLast x) (translate_tc mems clkvars tc) ->
      Is_free_in_tc (FunctionalEnvironment.Last x) tc.
  Proof.
    intros * Free.
    destruct tc as [|? []|?? []]; simpl in *.
    - destruct r.
      1,2:eapply Is_free_last_Control in Free.
      + inv Free. simpl_Exists. do 3 constructor. solve_Exists.
        eauto using Is_free_last_translate_exp.
      + eapply Is_free_last_translate_cexp in Free; eauto with stcfree.
        intros * F. now inv F.
    - eapply Is_free_last_Control in Free. inv Free.
      destruct c0; simpl in *; inv H1.
    - eapply Is_free_last_Control in Free. inv Free. inv H1.
    - eapply Is_free_last_Control, Is_free_last_translate_cexp in Free; eauto with stcfree.
      intros * F. now inv F.
    - eapply Is_free_last_Control in Free. inv Free.
      eauto using Is_free_last_translate_exp with stcfree.
    - eapply Is_free_last_Control in Free. inv Free.
      do 2 constructor. solve_Exists; eauto using Is_free_last_translate_arg.
  Qed.

  Lemma Can_write_in_Control :
    forall x mems ck s,
      Can_write_in x (Control mems ck s) ->
      Can_write_in x s.
  Proof.
    induction ck; intros * Cw; simpl in *; auto.
    destruct p, t; [inv Cw|].
    eapply IHck in Cw. inv Cw. simpl_Exists.
    destruct x0; simpl in *; [|inv H1].
    eapply skip_branches_with_In_det in Hin; subst; auto.
  Qed.

  Lemma Can_write_in_translate_tc:
    forall x mems clkvars tc,
      Can_write_in (WCurrent x) (translate_tc mems clkvars tc) ->
      Is_defined_in_tc x tc \/ Is_update_next_in_tc x tc.
  Proof.
    intros * Cw.
    destruct tc as [|? []|?? []]; simpl in *.
    - destruct r.
      1,2:eapply Can_write_in_Control in Cw.
      + inv Cw. left. constructor.
      + eapply Can_write_in_translate_cexp in Cw as (?&Cw).
        inv Cw. left. constructor.
    - eapply Can_write_in_Control in Cw. inv Cw.
    - eapply Can_write_in_Control in Cw. inv Cw. inv H1.
    - eapply Can_write_in_Control, Can_write_in_translate_cexp in Cw as (?&Cw).
      inv Cw. left. constructor.
    - eapply Can_write_in_Control in Cw. inv Cw.
      right. constructor.
    - eapply Can_write_in_Control in Cw. inv Cw.
      left. now constructor.
  Qed.

  Lemma Fusible_Control:
    forall mems ck s,
      (forall x, Is_free_in_clock x ck -> Can_write_in (WCurrent x) s \/ Can_write_in (WReset x) s -> False) ->
      Fusible s ->
      Fusible (Control mems ck s).
  Proof.
    induction ck as [|ck IH i b]; [now auto with *|].
    intros * Hxni Hfce; simpl.
    cases; auto using Fusible; apply IH.
    - intros j Hfree Hcw.
      apply Hxni with (x := j); [inversion_clear Hfree; eauto with stcfree|].
      destruct Hcw as [Hcw|Hcw]; [left|right]; inv Hcw.
      1,2:simpl_Exists; destruct x; simpl in *; try take (Can_write_in _ _) and now inv it.
      1,2:apply skip_branches_with_In_det in Hin; subst; auto.
    - constructor.
      + apply Forall_forall; intros [|] Hin; simpl; auto using Fusible.
        apply skip_branches_with_In_det in Hin; subst; auto.
      + intros * Hfree; apply Forall_forall; intros [|] Hin; simpl; try now inversion 1.
        apply skip_branches_with_In_det in Hin; subst.
        inv Hfree. eauto with stcfree.
      + intros * Hfree; apply Forall_forall; intros [|] Hin; simpl; try now inversion 1.
    - intros j Hfree Hcw.
      apply Hxni with (x := j); [inversion_clear Hfree; eauto with stcfree|].
      destruct Hcw as [Hcw|Hcw]; [left|right]; inv Hcw.
      1,2:simpl_Exists; destruct x; simpl in *; try take (Can_write_in _ _) and now inv it.
      1,2:apply skip_branches_with_In_det in Hin; subst; auto.
    - constructor.
      + apply Forall_forall; intros [|] Hin; simpl; auto using Fusible.
        apply skip_branches_with_In_det in Hin; subst; auto.
      + intros * Hfree; apply Forall_forall; intros [|] Hin; simpl; try now inversion 1.
        apply skip_branches_with_In_det in Hin; subst.
        inv Hfree; eauto with stcfree.
      + intros * Hfree; apply Forall_forall; intros [|] Hin; simpl; try now inversion 1.
  Qed.

  Fact Fusible_fold_left_change:
    forall A f (xs: list A) acc1 acc2,
      (Fusible acc1 -> Fusible acc2) ->
      (forall x, Is_free_in_stmt (RLast x) acc2 -> Is_free_in_stmt (RLast x) acc1) ->
      Fusible (fold_left (fun i x => Comp (f x) i) xs acc1) ->
      Fusible (fold_left (fun i x => Comp (f x) i) xs acc2).
  Proof.
    induction xs; intros * Acc Last Fus; simpl in *; auto.
    eapply IHxs in Fus; eauto.
    + intros * F. inv F. econstructor; eauto.
      intros * Cw L. eapply H3; eauto.
    + intros * F. inv F; eauto using Is_free_in_stmt.
  Qed.

  Fact Fusible_fold_left_shift:
    forall A f (xs : list A) iacc,
      Forall' (fun stmts stmt => forall x, Is_free_in_stmt (RLast x) stmt -> ~Exists (Can_write_in (WCurrent x)) stmts) (iacc::map f xs) ->
      Fusible (fold_left (fun i x => Comp (f x) i) xs Skip) ->
      Fusible iacc ->
      Fusible (fold_left (fun i x => Comp (f x) i) xs iacc).
  Proof.
    induction xs as [|x xs IH]; intros * Sch Fus1 Fus2; [now auto with *|].
    repeat take (Forall' _ (_ :: _)) and inv it.
    simpl in *. apply IH; auto.
    - constructor; auto. intros * ??.
      take (Is_free_in_stmt _ (Comp _ _)) and inv it.
      + take (forall x, _ -> ~Exists _ _) and eapply it; eauto.
      + take (forall x, _ -> ~Exists _ (_::_)) and eapply it; eauto.
    - eapply Fusible_fold_left_change in Fus1; eauto.
      + intros. constructor.
      + intros * L. inv L.
    - constructor; auto.
      + clear - Fus1. induction xs; simpl in *.
        * now inv Fus1.
        * eapply IHxs. eapply Fusible_fold_left_change in Fus1; eauto.
          -- intros F. now inv F.
          -- intros * F. inv F; eauto using Is_free_in_stmt.
      + intros * Cw Free.
        eapply H1; eauto.
  Qed.

  Lemma Fusible_translate_cexp:
    forall mems assign e,
      (forall e, Fusible (assign e)) ->
      (forall x, Is_free_in_cexp (FunctionalEnvironment.Var x) e ->
            forall oe, ~Can_write_in (WCurrent x) (assign oe) /\ ~Can_write_in (WReset x) (assign oe)) ->
      (forall x, Is_free_in_cexp (FunctionalEnvironment.Last x) e -> forall oe, ~Can_write_in (WReset x) (assign oe)) ->
      Fusible (translate_cexp mems assign e).
  Proof.
    induction e using cexp_ind2'; intros * Fus Free FreeL; eauto.
    - destruct x.
      simpl; constructor.
      + simpl_Forall. eapply H; eauto.
        * intros * F. eapply Free. constructor. solve_Exists.
        * intros * F. eapply FreeL. constructor. solve_Exists.
      + intros * Hfree'. simpl_Forall. intros [Cw|Cw].
        1,2:eapply Can_write_in_translate_cexp in Cw as (?&Cw).
        1,2:eapply Free in Cw; eauto; cases; inv Hfree'; constructor.
      + intros * Hfree'. simpl_Forall. intros Cw.
        eapply Can_write_in_translate_cexp in Cw as (?&Cw).
        eapply Free in Cw; eauto; cases; inv Hfree'; constructor.
    - simpl; constructor.
      + simpl_Forall. destruct x; simpl in *.
        * eapply H; eauto.
          -- intros * F. eapply Free. apply FreeEcase_branches. solve_Exists.
          -- intros * F. eapply FreeL. apply FreeEcase_branches. solve_Exists.
        * eapply IHe; eauto.
          -- intros * F. eapply Free; eauto using Is_free_in_cexp.
          -- intros * F. eapply FreeL; eauto using Is_free_in_cexp.
      + intros * Hfree'. simpl_Forall. intros Cw.
        eapply Is_free_current_translate_exp in Hfree'.
        destruct Cw as [Cw|Cw], x0; simpl in *.
        all:eapply Can_write_in_translate_cexp in Cw as (?&Cw).
        all:eapply Free in Cw; eauto using Is_free_in_cexp.
      + intros * Hfree'. simpl_Forall. intros Cw.
        eapply Is_free_last_translate_exp in Hfree'.
        destruct x0; simpl in *.
        all:eapply Can_write_in_translate_cexp in Cw as (?&Cw).
        all:eapply FreeL in Cw; eauto using Is_free_in_cexp.
  Qed.

  Lemma translate_tcs_Fusible {prefs} :
    forall (P: @Stc.Syn.program prefs) Γ nexts mems clkvars inputs tcs,
      wc_env (idfst Γ) ->
      NoDupMembers Γ ->
      Forall (wc_trconstr P Γ) tcs ->
      NoDup (defined tcs) ->
      Is_well_sch inputs nexts tcs ->
      (forall x, PS.In x mems -> ~ Is_variable_in x tcs /\ ~ In x inputs) ->
      (forall x, In x nexts -> PS.In x mems) ->
      (forall x ck, In (x, (ck, true)) Γ -> PS.In x mems) ->
      (* (forall x ck, Is_reset_state_in x ck tcs \/ (* Is_update_last_in x tcs \/  *)Is_update_next_in x tcs -> PS.In x mems) -> *)
      (forall x, In x inputs \/ In x nexts -> ~ Is_defined_in x tcs) ->
      Fusible (translate_tcs mems clkvars tcs).
  Proof.
    intros * Hwk Hnd Hwks Vars Hwsch Hnvi Mems1 Mems2 (* Mems3 *) Ndef.
    induction tcs as [|tc tcs IH]; [now constructor|].
    assert (NoDup (defined tcs))
      by (simpl in Vars; rewrite Permutation.Permutation_app_comm in Vars;
          apply NoDup_app_weaken in Vars; auto).
    inversion_clear Hwks as [|?? Hwktc];
      inversion Hwsch as [|?? (HH&HL&HN&HR&_) Hwsch']; subst; clear Hwsch.
    unfold translate_tcs.
    simpl; apply Fusible_fold_left_shift.
    - constructor.
      + intros * Free Cw. inv Free; [|take (Is_free_in_stmt _ _) and inv it].
        eapply Is_free_last_translate_tc in H3.
        simpl_Exists. eapply Can_write_in_translate_tc in Cw as [Def|Next];
          [eapply Is_defined_Is_variable_Is_last_in_tc in Def as [Var|Upd]|].
        * edestruct Hnvi as (Hnv&_); [|eapply Hnv; right; solve_Exists].
          eapply Is_free_last_wc_trconstr in H3 as (?&Last); [|simpl_Forall; eauto].
          edestruct Hnvi as (?&?); eauto.
        * eapply HL; eauto. unfold Is_update_last_in. solve_Exists.
        * eapply Is_free_last_wc_trconstr in H3 as (?&Last); [|simpl_Forall; eauto].
          simpl_Forall. inv Next. inv H0.
          eapply NoDupMembers_det in Last; eauto. congruence.
      + eapply Forall'_map, Forall'_impl_In; [|eauto].
        intros * In Incl (HH'&HL'&HN'&HR'&_) * Free Cw.
        eapply Is_free_last_translate_tc in Free.
        simpl_Exists. eapply Can_write_in_translate_tc in Cw as [Def|Next];
          [eapply Is_defined_Is_variable_Is_last_in_tc in Def as [Var|Upd]|].
        * apply Incl in Hin.
          edestruct Hnvi as (Hnv&_); [|eapply Hnv; right; solve_Exists].
          eapply Is_free_last_wc_trconstr in Free as (?&Last); [|clear Hin; simpl_Forall; eauto].
          edestruct Hnvi as (?&?); eauto.
        * eapply HL'; eauto. unfold Is_update_last_in. solve_Exists.
        * eapply Is_free_last_wc_trconstr in Free as (?&Last); [|clear Hin; simpl_Forall; eauto].
          clear In. eapply Incl in Hin. simpl_Forall. inv Next. inv H0.
          eapply NoDupMembers_det in Last; eauto. congruence.
    - apply IH; auto.
      + intros * Hin; apply Hnvi in Hin as (Hin&?).
        split; auto. intro; apply Hin; right; auto.
      (* + intros * [Upd|Upd]; eapply Mems3 with (ck:=ck); [left|right]; right; eauto. *)
      + intros * Hin; apply Ndef in Hin.
        intro; apply Hin; right; auto.
    - clear IH.
      repeat constructor.
      destruct tc as [ck y e|ckr [y c0|s f]|ck ? [y e|y e|s xs f es]]; simpl.
      + assert (~PS.In y mems) as Hnxm.
        { intros Hin. apply Hnvi in Hin as (Hin&_). apply Hin. repeat constructor. }
        assert (forall i, Is_free_in_arhs (FunctionalEnvironment.Var i) ck e -> y <> i) as Hfni.
        { intros i Hfree ?; subst.
          assert (Hfree': Is_free_in_tc (FunctionalEnvironment.Var i) (TcDef ck i e)) by auto with stcfree.
          eapply HH in Hfree' as [Hdef|[Hinput|Hmems]].
          - simpl in *. eapply NoDup_cons'; eauto.
            apply Is_defined_in_defined; auto.
          - eapply Ndef; eauto. left. constructor.
          - eapply Hnxm; eauto.
        }
        destruct e; apply Fusible_Control.
        * intros * Hfree [Cw|Cw]; inv Cw.
          eapply Hfni; eauto using Is_free_in_arhs.
        * constructor.
        * intros * Free [Cw|Cw]; apply Can_write_in_translate_cexp in Cw as (?&Cw); inv Cw.
          eapply Hfni; eauto. now apply FreeArhs2.
        * apply Fusible_translate_cexp.
          -- intros. constructor.
          -- intros. split; intros Cw; inv Cw.
             eapply Hfni; eauto with stcfree.
          -- intros * _ * Cw. inv Cw.
      + apply Fusible_Control; auto using Fusible.
        intros x' Hfree [Cw|Cw]; inv Cw.
        edestruct HR as (?&?&?&?); eauto. constructor.
        eapply H2; left; eauto with stcfree.
      + apply Fusible_Control; auto using Fusible.
        intros * _ [Cw|Cw]; inv Cw. inv H3.
      + assert (forall i, Is_free_in_acexp (FunctionalEnvironment.Var i) ck e -> y <> i) as Hfni.
        { intros i Hfree ?; subst.
          assert (Hfree': Is_free_in_tc (FunctionalEnvironment.Var i) (TcUpdate ck l (UpdLast i e))) by auto with stcfree.
          eapply HH in Hfree' as [Hdef|Hinput].
          - simpl in *. eapply NoDup_cons'; eauto.
            apply Is_defined_in_defined; auto.
          - eapply Ndef; eauto. left. constructor.
        }
        apply Fusible_Control; auto using Fusible.
        * intros * Free [Cw|Cw]; apply Can_write_in_translate_cexp in Cw as (?&Cw); inv Cw.
          eapply Hfni; eauto using Is_free_in_acexp.
        * apply Fusible_translate_cexp.
          -- intros. constructor.
          -- intros. split; intros Cw; inv Cw.
             eapply Hfni; eauto using Is_free_in_acexp.
          -- intros * _ * Cw; inv Cw.
      + apply Fusible_Control; auto using Fusible.
        intros ?? [Cw|Cw]; inv Cw.
        eapply wc_TcUpdateNext_not_Is_free_in_clock; eauto.
      + apply Fusible_Control; auto using Fusible.
        intros ?? [Cw|Cw]; inv Cw.
        now eapply wc_TcUpdateInst_not_Is_free_in_clock; eauto.
      + intros * _ Free. inv Free.
  Qed.

  Lemma reset_mems_Fusible:
    forall mems,
      Fusible (reset_mems mems).
  Proof.
    intro; unfold reset_mems.
    assert (Fusible Skip) as Hf by auto using Fusible.
    revert Hf; generalize Skip.
    induction mems as [|(x, (c, ck))]; intros s Hf; simpl; auto using Fusible.
    eapply IHmems. repeat constructor; auto.
    intros * Cw Free. inv Free.
    cases; inv H1.
  Qed.
  Local Hint Resolve reset_mems_Fusible : obcinv.

  Lemma reset_insts_Fusible:
    forall blocks,
      Fusible (reset_insts blocks).
  Proof.
    intro; unfold reset_insts.
    assert (Fusible Skip) as Hf by constructor.
    revert Hf; generalize Skip.
    induction blocks as [|(x, f)]; intros s Hf; simpl; auto using Fusible.
    eapply IHblocks. repeat constructor; auto.
    intros * Cw Free. inv Free. inv H1.
  Qed.
  Local Hint Resolve reset_insts_Fusible : obcinv.

  Theorem ProgramFusible_translate:
    forall P,
      wc_program P ->
      Well_scheduled P ->
      ProgramFusible (translate P).
  Proof.
    intros []; induction systems0 as [|s]; intros * WC Wsch;
      inversion_clear WC as [|?? (?&?&?& WCb)];
      inversion_clear Wsch as [|??? Wsch'];
      simpl; constructor; auto; try now apply IHsystems0.
    unfold ClassFusible; simpl.
    repeat constructor; simpl; auto with obcinv.
    assert (NoDup (defined (s_tcs s))) by apply s_nodup_defined.
    eapply translate_tcs_Fusible; eauto with obcinv.
    - clear - H1. simpl_app.
      erewrite ? map_map, map_ext with (l:=s_in _), map_ext with (l:=s_vars _), map_ext with (l:=s_out _),
              map_ext with (l:=s_lasts _), map_ext with (l:=s_nexts _); eauto.
      all:intros; destruct_conjs; auto.
    - rewrite fst_NoDupMembers. simpl_app.
      erewrite ? map_map, map_ext with (l:=s_in _), map_ext with (l:=s_vars _), map_ext with (l:=s_out _),
              map_ext with (l:=s_lasts _), map_ext with (l:=s_nexts _); eauto.
      apply s_nodup.
      all:intros; destruct_conjs; auto.
    - intros * In. apply ps_from_list_In in In. split; intros In2.
      + apply Is_variable_in_variables in In2. rewrite <-s_vars_out_in_tcs in In2.
        pose proof (s_nodup s) as Nd. apply NoDup_app_r in Nd. rewrite app_assoc in Nd.
        eapply NoDup_app_In; eauto. now rewrite <-map_app.
      + eapply NoDup_app_In; eauto using s_nodup.
        rewrite <-map_app. auto using in_or_app.
    - intros * L. apply ps_from_list_In. rewrite map_app. auto using in_or_app.
    - intros * In. apply ps_from_list_In. rewrite map_app, in_app_iff. left.
      rewrite ? in_app_iff in In. destruct In as [In|[In|In]]; solve_In.
    - intros * [In|In].
      + apply s_ins_not_def, fst_InMembers; auto.
      + rewrite Is_defined_in_defined, s_defined, <-s_lasts_in_tcs. intros ?.
        pose proof (s_nodup_variables_lasts_nexts s) as ND. rewrite map_app, app_assoc in ND.
        eapply NoDup_app_In in ND; eauto.
    - intros * Cw _. clear - Cw.
      remember (s_lasts _ ++ s_nexts _) as xs. clear Heqxs.
      unfold reset_mems in *.
      assert (Can_write_in (WCurrent x0) Skip -> False) as Acc by (intros Cw'; inv Cw').
      revert Acc Cw; generalize Skip.
      induction xs as [|(x, f)]; intros * Acc Cw; simpl in *; eauto.
      eapply IHxs in Cw; eauto.
      intros Cw1. inv Cw1; auto. cases; inv H1.
  Qed.

  (** Translating gives [No_Overwrites] Obc. *)

  Lemma Can_write_in_var_Control:
    forall mems ck s x,
      Can_write_in_var x (Control mems ck s) -> Can_write_in_var x s.
  Proof.
    induction ck; simpl; auto.
    destruct p, t as [|].
    - inversion 1.
    - intros * Cw; apply IHck in Cw; inv Cw.
      take (Exists _ _) and apply Exists_exists in it as ([|] & Hin & Cw);
        simpl in *; try now inv Cw.
      apply skip_branches_with_In_det in Hin; subst; auto.
  Qed.

  Corollary Can_write_in_var_Control':
    forall mems ck s x enums Γ,
      wt_clock enums Γ ck ->
      Can_write_in_var x (Control mems ck s) <-> Can_write_in_var x s.
  Proof.
    intros * WT; split; eauto using Can_write_in_var_Control.
    revert s; induction ck; simpl; auto; inv WT.
    intros * Cw; apply IHck; auto.
    constructor.
    apply Exists_exists.
    take (_ < _) and eapply skip_branches_with_In in it; eauto.
  Qed.

  Lemma No_Overwrites_Control:
    forall mems ck s enums Γ,
      wt_clock enums Γ ck ->
      No_Overwrites (Control mems ck s) <-> No_Overwrites s.
  Proof.
    induction ck; simpl; try reflexivity; inversion_clear 1.
    setoid_rewrite IHck; eauto; split; simpl in *.
    - inversion_clear 1; auto.
      take (_ < _) and eapply skip_branches_with_In in it; eauto.
      eapply Forall_forall in it; eauto; auto.
    - constructor.
      apply Forall_forall; intros [|] Hin; simpl; auto using No_Overwrites.
      apply skip_branches_with_In_det in Hin; subst; auto.
  Qed.

  Lemma Can_write_in_var_translate_cexp:
    forall mems e x assign,
      Can_write_in_var x (translate_cexp mems assign e) ->
      exists oe, Can_write_in_var x (assign oe).
  Proof.
    induction e using cexp_ind2; simpl;
      try setoid_rewrite Can_write_in_var_Switch;
      try setoid_rewrite Exists_exists.
    - intros * (os & Hin & Cw).
      simpl_In. simpl_Forall. eauto.
    - intros * (os & Hin & Cw).
      simpl_In. simpl_Forall. destruct x0; simpl in *; eauto.
    - intros; eauto.
  Qed.

  Lemma No_Overwrites_translate_cexp:
    forall mems assign e,
      (forall oe, No_Overwrites (assign oe)) ->
      No_Overwrites (translate_cexp mems assign e).
  Proof.
    induction e using cexp_ind2; intros * NO; simpl; auto.
    1,2:constructor; simpl_Forall; eauto.
    destruct x; simpl in *; auto.
  Qed.

  Lemma Can_write_in_var_translate_tc_Is_variable_in_tc:
    forall mems clkvars tc x,
      Can_write_in_var x (translate_tc mems clkvars tc) -> Is_variable_in_tc x tc.
  Proof.
    destruct tc as [|?[]|?? []]; simpl; intros * Cw;
      try (take rhs and destruct it);
      try destruct c0;
      apply Can_write_in_var_Control in Cw as Cw;
      try apply Can_write_in_var_translate_cexp in Cw as (?&Cw); inv Cw;
        auto using Is_variable_in_tc.
    contradiction.
  Qed.

  Lemma Can_write_in_var_translate_tcs_Is_variable_in:
    forall mems clkvars tcs x,
      Can_write_in_var x (translate_tcs mems clkvars tcs) -> Is_variable_in x tcs.
  Proof.
    unfold translate_tcs.
    intros mems clkvars tcs x.
    match goal with |- ?P -> ?Q => cut (P -> (Q \/ Can_write_in_var x Skip)) end;
      [intros HH Cw; apply HH in Cw as [|Cw]; auto; inv Cw|].
    generalize Skip.
    induction tcs as [|tc tcs IH]; simpl; intro s; auto.
    intros Cw.
    apply IH in Cw as [|Cw].
    - now left; right.
    - apply Can_write_in_var_Comp in Cw as [Cw|]; auto.
      apply Can_write_in_var_translate_tc_Is_variable_in_tc in Cw.
      now left; left.
  Qed.

  (* Here, we use [Is_well_sch] because it simplifies the inductive proof
     (many of the required lemmas already exist), but in fact, the weaker
     property that no two trconstrs define the same variable is sufficient. *)

  Lemma translate_tcs_No_Overwrites {prefs} :
    forall clkvars mems inputs nexts tcs (P: @Stc.Syn.program prefs) Γ,
      NoDup (variables tcs) ->
      Forall (wt_trconstr P Γ) tcs ->
      Is_well_sch inputs nexts tcs ->
      No_Overwrites (translate_tcs mems clkvars tcs).
  Proof.
    unfold translate_tcs.
    intros *.
    pose proof NoOSkip as Hs; revert Hs.
    assert (forall x, Is_variable_in x tcs -> ~Can_write_in_var x Skip) as Hdcw
        by inversion 2; revert Hdcw.
    assert (forall x, Can_write_in_var x Skip -> ~Is_variable_in x tcs) as Hcwd
        by inversion 1; revert Hcwd.
    generalize Skip.
    induction tcs as [|tc tcs IH]; auto.
    intros * Hcwd Hdcw Hno Nodup Wt Hwsch; inv Wt.
    inversion_clear Hwsch as [|?? (Hfree&Hnext&_) Hwsch'].
    assert (forall x, Is_variable_in_tc x tc -> ~ Is_variable_in x tcs) as Defs
        by (intro; rewrite Is_variable_in_variables, Is_variable_in_tc_variables_tc;
            simpl in Nodup; intros; eapply NoDup_app_In in Nodup; eauto).
    simpl. apply IH; auto.
    - setoid_rewrite Can_write_in_var_Comp.
      intros ? [Hvar|Hcw]; auto.
      + apply Can_write_in_var_translate_tc_Is_variable_in_tc in Hvar; auto.
      + apply Hcwd, not_Is_variable_in_cons in Hcw as (? & ?); auto.
    - setoid_rewrite cannot_write_in_var_Comp.
      intros ? Hdef. split; intro Hcw.
      + apply Can_write_in_var_translate_tc_Is_variable_in_tc in Hcw.
        eapply Defs; eauto.
      + apply Hdcw in Hcw; auto. now constructor 2.
    - constructor; auto with obcinv.
      + intros ? Hdef.
        apply Can_write_in_var_translate_tc_Is_variable_in_tc in Hdef.
        apply Hdcw; left; auto.
      + intros ? Hcw Hcw2.
        apply Can_write_in_var_translate_tc_Is_variable_in_tc in Hcw2.
        apply Hcwd, not_Is_variable_in_cons in Hcw as (? & ?); auto.
      + destruct tc; simpl;
          try destruct v0; inv H1;
          try (take (wt_rhs _ _ _ _) and inv it);
          try (take (wt_const _ _ _) and inv it);
          try setoid_rewrite No_Overwrites_Control;
          eauto using No_Overwrites_translate_cexp with obcinv.
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
    constructor; auto with obcinv.
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
    assert (forall x, InMembers x resets -> ~ Can_write_in_var x Skip) as CWIS by inversion 2.
    revert NOS CWIS; generalize Skip.
    induction resets as [|(x, (c0, ck))]; simpl; auto; inv Nodup.
    intros; apply IHresets; auto.
    - constructor; auto with obcinv.
      + inversion 2; subst; eapply CWIS; eauto.
      + inversion_clear 1; auto.
    - inversion_clear 2 as [| | | | |??? CWI];
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
    - apply No_Overwrites_reset_mems, s_nodup_lasts_nexts.
    - apply No_Overwrites_reset_inst.
  Qed.

  Lemma translate_system_No_Overwrites {prefs} :
    forall s m (P: @Stc.Syn.program prefs),
      Is_well_sch (map fst (s_in s)) (map fst (s_nexts s)) (s_tcs s) ->
      Forall
        (wt_trconstr P
           (map (fun '(x, (ty, _)) => (x, (ty, false))) (s_in s ++ s_vars s ++ s_out s)
              ++ map (fun '(x, (_, ty, _)) => (x, (ty, true))) (s_lasts s)
              ++ map (fun '(x, (_, ty, _)) => (x, (ty, false))) (s_nexts s))) (s_tcs s) ->
      In m (translate_system s).(c_methods) ->
      No_Overwrites m.(m_body).
  Proof.
    intros ????? Hin.
    destruct Hin as [|[|]]; simpl in *; subst; simpl;
      try contradiction.
    - eapply translate_tcs_No_Overwrites; eauto.
      apply s_nodup_variables.
    - apply translate_reset_No_Overwrites.
  Qed.

  Corollary translate_No_Overwrites:
    forall P,
      Well_scheduled P ->
      Stc.Typ.wt_program P ->
      Forall_methods (fun m => No_Overwrites m.(m_body)) (translate P).
  Proof.
    intros * Wsch WTp; apply Forall_forall; intros * HinP; apply Forall_forall; intros.
    unfold translate in HinP; apply in_map_iff in HinP as (?&?&?); subst; eauto.
    eapply Forall_forall in Wsch; eauto.
    eapply Forall'_In in WTp as (?&?&?& [] &?); eauto.
    eapply translate_system_No_Overwrites; eauto.
  Qed.

  (** ** The node doesn't write its inputs *)

  Lemma Can_write_in_translate_tc_Is_variable_in_tc:
    forall mems clkvars tc x,
      Can_write_in_var x (translate_tc mems clkvars tc) ->
      Is_variable_in_tc x tc \/ (exists ck, Is_reset_state_in_tc x ck tc) \/ Is_update_last_in_tc x tc.
  Proof.
    destruct tc as [|?[]|??[]]; simpl; intros * Cw;
      try (take rhs and destruct it);
      try destruct c0;
      apply Can_write_in_var_Control in Cw;
      try apply Can_write_in_var_translate_cexp in Cw as (?&Cw); inv Cw;
      subst; try inversion_clear HH; eauto using Is_variable_in_tc, Is_reset_state_in_tc, Is_update_last_in_tc.
    contradiction.
  Qed.

  Lemma Can_write_in_translate_tcs_Is_variable_in:
    forall mems clkvars tcs x,
      Can_write_in_var x (translate_tcs mems clkvars tcs) ->
      Is_variable_in x tcs \/ (exists ck, Is_reset_state_in x ck tcs) \/ Is_update_last_in x tcs.
  Proof.
    unfold translate_tcs.
    intros mems clkvars tcs x.
    match goal with |- ?P -> ?Q => cut (P -> (Q \/ Can_write_in_var x Skip)) end.
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
      Forall (fun x => ~Can_write_in_var x m.(m_body)) (map fst m.(m_in)).
  Proof.
    intros * Hin.
    destruct Hin as [|[|]]; simpl in *; subst; simpl;
      auto; try contradiction.
    apply Forall_forall; intros x Hin.
    apply fst_InMembers, InMembers_idfst in Hin. intro contra.
    apply Can_write_in_translate_tcs_Is_variable_in in contra as [H|[(?&H)|H]].
    - eapply s_ins_not_var in H; eauto.
    - eapply s_ins_not_reset_state in H; eauto.
    - eapply s_ins_not_last in H; eauto.
  Qed.

  Corollary translate_cannot_write_inputs:
    forall P,
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in_var x (m_body m)) (map fst (m_in m)))
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
       (OpAux : OPERATORS_AUX   Ids Op)
       (ComTyp: COMMONTYPING    Ids Op OpAux)
       (Cks   : CLOCKS          Ids Op OpAux)
       (Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (CE    : COREEXPR    Ids Op OpAux ComTyp Cks Str)
       (Stc   : STC         Ids Op OpAux ComTyp Cks Str CE)
       (Obc   : OBC         Ids Op OpAux ComTyp)
       (Trans : TRANSLATION Ids Op OpAux        Cks CE.Syn Stc.Syn Obc.Syn)
  <: STC2OBCINVARIANTS Ids Op OpAux ComTyp Cks Str CE Stc Obc Trans.
  Include STC2OBCINVARIANTS Ids Op OpAux ComTyp Cks Str CE Stc Obc Trans.
End Stc2ObcInvariantsFun.
