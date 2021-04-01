From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr Transcription.TrOrdered.

From Velus Require Import Lustre.LTyping.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import Lustre.LCausality.
From Velus Require Import Lustre.LSemantics Lustre.LClockSemantics.
From Velus Require Import Lustre.Normalization.Normalization.
From Velus Require Import Lustre.Normalization.Correctness.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLCoindSemantics.

From Velus Require Import CoindStreams IndexedStreams.

From Coq Require Import String.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Permutation.
From Coq Require Import Omega.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

Open Scope list.

From compcert Require Import common.Errors.
Open Scope error_monad_scope.

From Coq Require Import Classes.EquivDec.

(** * Semantics Preservation Proof for Transcription *)

Module Type CORRECTNESS
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX        Op)
       (L           : LSYNTAX          Ids Op)
       (Import CE   : CESYNTAX             Op)
       (NL          : NLSYNTAX         Ids Op              CE)
       (Import TR   : TR               Ids Op OpAux L      CE NL)
       (LT          : LTYPING          Ids Op       L)
       (LC          : LCLOCKING        Ids Op       L)
       (LCA         : LCAUSALITY       Ids Op       L)
       (Ord         : NLORDERED        Ids Op              CE NL)
       (Lord        : LORDERED         Ids Op       L)
       (Import Str  : COINDSTREAMS         Op OpAux)
       (IStr        : INDEXEDSTREAMS       Op OpAux)
       (LS          : LSEMANTICS       Ids Op OpAux L Lord       Str)
       (LCS         : LCLOCKSEMANTICS  Ids Op OpAux L LC LCA Lord Str IStr LS)
       (LN          : NORMALIZATION    Ids Op OpAux L LCA)
       (NLSC        : NLCOINDSEMANTICS Ids Op OpAux        CE NL Str Ord).

  Lemma sem_const_step :
    forall G H b e e' v s,
      to_constant e = OK e' ->
      LS.sem_exp G H b e [v ⋅ s] ->
      LS.sem_exp G (history_tl H) (Streams.tl b) e [s].
  Proof.
    einduction e using L.exp_ind2; intros * Htr Hsem; inv Htr.
    - inv Hsem. symmetry in H5.
      destruct v;
        [ apply const_inv1 in H5; destruct H5 as [ b' [ Hs Hb ] ]
        | apply const_inv2 in H5; destruct H5 as (b' & Hs & Hb & Hc) ];
        rewrite Hs; rewrite Hb; simpl; econstructor; reflexivity.
    - destruct es; inv H2.
      destruct es; inv H3.
      inv H0. inv H5. inv Hsem. inv H12. inv H10. inv H9. inv H6. inv H0.
      rewrite app_nil_r in H3. inv H3.
      destruct x0. destruct s0.
      econstructor. econstructor; eauto.
      eapply sem_var_step; eauto. econstructor; eauto.
      now inv H5.
  Qed.

  Lemma sem_lexp_step :
    forall G H b e e' v s,
      to_lexp e = OK e' ->
      LS.sem_exp G H b e [v ⋅ s] ->
      LS.sem_exp G (history_tl H) (Streams.tl b) e [s].
  Proof.
    einduction e using L.exp_ind2; intros * Htr Hsem; inv Htr.
    - inv Hsem. symmetry in H5.
      destruct v;
        [ apply const_inv1 in H5; destruct H5 as [ b' [ Hs Hb ] ]
        | apply const_inv2 in H5; destruct H5 as (b' & Hs & Hb & Hc) ];
      rewrite Hs; rewrite Hb; simpl; econstructor; reflexivity.
    - inv Hsem. inv H5.  destruct xs'.
      econstructor. econstructor.
      eapply env_maps_tl; eauto. inv H3; simpl in *. assumption.
    - inv Hsem. destruct a. monadInv H1. destruct s0.
      econstructor; eauto. inv H10; auto.
    - inv Hsem. destruct a. monadInv H1. destruct s1, s2.
      econstructor; eauto. inv H13; auto.
    - destruct es; inv H2.
      destruct es; inv H3.
      inv H0.
      destruct a. destruct l; inv H2.
      destruct l; try now inv H1. monadInv H1.
      clear H5.
      inv Hsem. inv H11. inv H5. destruct s0, x1.
      inv H9. inv H7. simpl in H0. rewrite app_nil_r in H0. subst.
      econstructor.
      + econstructor; eauto.
      + eapply sem_var_step. eassumption.
      + econstructor; eauto. inv H3; eauto.
  Qed.

  Lemma sem_cexp_step :
    forall G H b e e' v s,
      to_cexp e = OK e' ->
      LS.sem_exp G H b e [v ⋅ s] ->
      LS.sem_exp G (history_tl H) (Streams.tl b) e [s].
  Proof.
    einduction e using L.exp_ind2; intros * Htr Hsem;
      (now inv Htr) || (unfold to_cexp in Htr;
                       try (monadInv Htr; eapply sem_lexp_step; eauto));
      cases; monadInv Htr; fold to_cexp in *;

        inv Hsem; inv H11; inv H6; inv H12; inv H7; inv H13; inv H10;
          rewrite app_nil_r in H3, H2; subst;
            inv H0; inv H1; clear H10 H7; destruct x2, y1.
    - inv H8;
        (econstructor; eauto;
         [ eapply sem_var_step; eauto | econstructor; eauto; econstructor ]).
    - inv H8;
        (econstructor; eauto; eapply sem_lexp_step in EQ; eauto;
         econstructor; eauto; constructor).
  Qed.

  Lemma ty_lexp :
    forall G env e e',
      LT.wt_exp G env e ->
      to_lexp e = OK e' ->
      L.typeof e = [CE.typeof e'].
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr; inv Htr.
    - now simpl.
    - destruct a. inv H0. now simpl.
    - destruct a. simpl. monadInv H0. now simpl.
    - destruct a. monadInv H0. now simpl.
    - cases. inv H. simpl. inv Hwt. inv H8. inv H6. monadInv H1.
      unfold L.typesof. unfold flat_map. simpl. rewrite app_nil_r.
      now apply H3.
  Qed.

  Lemma sem_exp_lexp :
    forall G G' env H b e e' s,
      LT.wt_exp G' env e ->
      to_lexp e = OK e' ->
      LS.sem_exp G H b e [s] ->
      NLSC.sem_exp H b e' s.
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr Hsem; inv Htr.
    - inv Hsem. now econstructor.
    - destruct a. inv Hsem. inv H1. econstructor; eauto.
    - destruct a. inv Hsem. monadInv H1. inv Hwt. econstructor; eauto.
      eapply ty_lexp in EQ; eauto. rewrite H9 in EQ. now inv EQ.
    - destruct a. inv Hsem. monadInv H1. inv Hwt. econstructor; eauto.
      eapply ty_lexp in EQ; eauto. eapply ty_lexp in EQ1; eauto.
      rewrite H11 in EQ. inv EQ. rewrite H12 in EQ1. now inv EQ1.
    - cases. monadInv H2. inv Hsem. inv H0. clear H4. inv Hwt.
      inv H9. inv H5. inv H11. inv H6. rewrite app_nil_r in H0. inv H0. inv H14.
      econstructor; eauto.
  Qed.

  Lemma sem_lexp_single :
    forall e e' G H b ss,
      to_lexp e = OK e' ->
      LS.sem_exp G H b e ss ->
      exists s, ss = [s].
  Proof.
    induction e using L.exp_ind2; intros * Htr Hsem; inv Htr;
      try (inv Hsem; eexists; now eauto).
    cases_eqn H2. subst. monadInv H2. inv Hsem. inv H9. inv H5. inv H. inv H5.
    eapply H4 in EQ; [|eauto]. inv EQ. simpl in H11. inv H11. inv H6.
    eauto.
  Qed.

  Lemma sem_exps_lexps :
    forall G H b tenv es les ss,
      mmap to_lexp es = OK les ->
      Forall (LT.wt_exp G tenv) es ->
      Forall2 (LS.sem_exp G H b) es ss ->
      Forall2 (NLSC.sem_exp H b) les (concat ss).
  Proof.
    intros * Hmmap Hwt Hsem. revert dependent les.
    induction Hsem; intros. inv Hmmap. simpl. auto.
    apply mmap_cons in Hmmap.
    destruct Hmmap as [ x' [le' [Hle [Htolexp  Hmmap]]]]. inv Hwt.
    apply IHHsem in Hmmap; eauto.
    assert (Htolexp' := Htolexp).
    eapply sem_lexp_single in Htolexp'; eauto. inv Htolexp'.
    eapply sem_exp_lexp in Htolexp; eauto. now constructor.
  Qed.

  Lemma sem_exp_cexp :
    forall G G' env H b e e' s,
      LT.wt_exp G' env e ->
      to_cexp e = OK e' ->
      LS.sem_exp G H b e [s] ->
      NLSC.sem_cexp H b e' s.
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr Hsem;
      (now inv Htr) || (unfold to_cexp in Htr;
                       try (monadInv Htr; econstructor;
                            eapply sem_exp_lexp; eauto));
      cases; monadInv Htr; fold to_cexp in *;
                 inv Hsem; inv H11; inv H6; inv H12; inv H7; inv H13; inv H10;
                   rewrite app_nil_r in H3, H2; subst;
                     inv H0; inv H1; clear H10 H7; destruct x2, y1.
    - inv Hwt; inv H11; inv H12. inv H8;
        (econstructor; eauto;
         econstructor; eauto; eapply merge_id; eauto).
    - inv Hwt. inv H12. inv H13.
      inv H8; econstructor; eauto;
        eapply sem_exp_lexp in EQ; eauto;
          econstructor; eauto.
  Qed.

  Lemma sem_lexp_step2: forall H b e v s,
      NLSC.sem_exp H b e (v ⋅ s) ->
      NLSC.sem_exp (history_tl H) (Streams.tl b) e s.
  Proof.
    induction e; intros * Hsem; inv Hsem.
    - econstructor; eauto. unfold_St b. inv H4. simpl in *. eauto.
    - econstructor; eauto using sem_var_step_nl.
    - inv H9; econstructor; eauto using sem_var_step_nl.
    - inv H8; econstructor; eauto using sem_var_step_nl.
    - inv H10; econstructor; eauto using sem_var_step_nl.
  Qed.

  Lemma sem_cexp_step2: forall H b e v s,
      NLSC.sem_cexp H b e (v ⋅ s) ->
      NLSC.sem_cexp (history_tl H) (Streams.tl b) e s.
  Proof.
    induction e; intros * Hsem; inv Hsem.
    - inv H10; econstructor; eauto using sem_var_step_nl.
    - inv H10; econstructor; eauto using sem_lexp_step2.
    - econstructor; eauto using sem_lexp_step2.
  Qed.

  Lemma fby_const:
    forall b c xs ys rs,
      LS.fby xs ys rs ->
      xs ≡ const b c ->
      b  ≡ abstract_clock rs ->
      rs ≡ NLSC.fby (sem_const c) ys.
  Proof.
    cofix Cofix; intros * Hfby Hconst Hac.
    unfold_Stv ys; inv Hfby; rewrite unfold_Stream in Hac;
      simpl in Hac; rewrite unfold_Stream; simpl; symmetry in Hconst.
    - apply const_inv1 in Hconst.
      destruct Hconst as (?& Hc & Hb). rewrite Hb in Hac.
      inv Hac; simpl in *. econstructor; simpl; eauto.
    - apply const_inv2 in Hconst.
      destruct Hconst as (?& Hc & Hb & Hx). rewrite Hb in Hac.
      inv Hac; simpl in *. econstructor; simpl; eauto.
      clear H Cofix. revert H0 H3 Hb Hc. revert rs0 x0 ys xs0 v c b.
      cofix Cofix; intros * Hac Hfby1 Hb Hconst.
      unfold_Stv ys; inv Hfby1; rewrite unfold_Stream in Hac;
        simpl in Hac; rewrite unfold_Stream; simpl; symmetry in Hconst.
      + apply const_inv1 in Hconst.
        destruct Hconst as (?& Hc & Hbb). rewrite Hbb in Hac.
        inv Hac; simpl in *. econstructor; simpl; eauto.
        eapply Cofix; eauto. reflexivity.
      + apply const_inv2 in Hconst.
        destruct Hconst as (?& Hc & Hbb & Hx). rewrite Hbb in Hac.
        inv Hac; simpl in *. econstructor; simpl; eauto.
  Qed.

  Lemma sem_const_exp:
    forall G H b e c c' xs,
      to_constant e = OK c ->
      LS.sem_exp G H b e [present c' ⋅ xs] ->
      c' = sem_const c.
  Proof.
    induction e using L.exp_ind2; intros * Htoc Hsem;
      inv Htoc; inv Hsem.
    - symmetry in H5. apply const_inv2 in H5. inv H5. tauto.
    - cases. inv H0. inv H5.
      inv H10. inv H6. inv H12. inv H7. rewrite app_nil_r in H0.
      subst. inv H6.
      eapply H4; eauto.
  Qed.

  Lemma fby_const_when :
    forall G H bk x i ck e b c s cs css xs ys,
      sem_var H x xs ->
      sem_clock H bk (Con ck i b) (abstract_clock xs) ->
      LS.fby css ys xs ->
      to_constant e = OK c ->
      LS.sem_exp G H bk e [cs] ->
      when b cs s css ->
      xs ≡ NLSC.fby (sem_const c) ys.
  Proof.
    cofix Cofix; intros * Hsemv Hsc Hfby Htoc Hse Hwhen.
    unfold_Stv xs; inv Hfby; rewrite unfold_Stream; simpl;
      rewrite unfold_Stream in Hsc; simpl in Hsc.
    - econstructor; simpl; eauto. destruct cs.
      eapply sem_var_step in Hsemv; eauto.
      assert (Htoc' := Htoc).
      eapply sem_const_step in Htoc; eauto.
      eapply sc_step in Hsc.
      inv Hwhen; eapply Cofix; eauto.
    - econstructor; simpl; eauto. inv Hwhen. f_equal.
      eapply sem_const_exp; eauto. clear Cofix.
      eapply sc_step in Hsc.
      eapply sem_var_step in Hsemv.
      assert (Htoc' := Htoc).
      inv Hwhen. eapply sem_const_step in Htoc'; eauto. clear Hse.
      revert dependent H. revert H3 H5 H6. revert bk xs xs0 xs1 xs0 cs0 ys0 y.
      cofix Cofix; intros.
      unfold_Stv xs; inv H3; rewrite unfold_Stream; simpl;
        rewrite unfold_Stream in Hsc; simpl in Hsc;
          eapply sc_step in Hsc;
          eapply sem_var_step in Hsemv;
          econstructor; simpl; eauto;
            inv H5; eapply Cofix; eauto using sem_const_step.
  Qed.

  Lemma var_fby_const :
    forall G H b c a env cenv ck ckx x e0 e1 cs xs ys,
      LS.sem_exp G H b e0 [cs] ->
      sem_var H x xs ->
      LS.fby cs ys xs ->
      find_clock env x = OK ck ->
      LC.wc_exp G cenv (L.Efby [e0] [e1] a) ->
      [ckx] = map L.clock_of_nclock a ->
      In (x, ckx) cenv ->
      envs_eq env cenv ->
      to_constant e0 = OK c ->
      sem_clock H b ck (abstract_clock xs) ->
      sem_var H x (NLSC.fby (sem_const c) ys).
  Proof.
    destruct ck; intros * Hse Hxs Hfby Hfind Hwc Hckx Hin Henv Htoc Hsc.
    - (* ck = Base. Show that e0 is not EWhen *)
      inv Hsc. destruct e0; inv Htoc.
      + inv Hse. eapply fby_const in Hfby; eauto.
        now rewrite <- Hfby.
      + cases. inv Hwc. inv H5. inv H4. rewrite <- Hckx in H7.
        inv H7. inv H11. destruct tys; inv H4.
        unfold L.clock_of_nclock, stripname in Hin. simpl in Hin.
        eapply envs_eq_find with (x := x) in Henv; eauto.
        rewrite Henv in Hfind. discriminate.
    - destruct e0; inv Htoc.
      + inv Hse. eapply fby_const in Hfby; eauto.
        now rewrite <- Hfby.
        apply LCS.ac_fby1 in Hfby. symmetry in H5. apply ac_const in H5.
        now rewrite H5, Hfby.
      + cases. eapply envs_eq_find with (x := x) in Henv; eauto.
        rewrite Henv in Hfind. inv Hfind. destruct a; inv Hckx.
        destruct a0; inv H3.
        inv Hwc. inv H5. inv H4. simpl in *.
        rewrite app_nil_r in H7. destruct tys; inv H7.
        destruct tys; inv H16. rewrite <- H2 in H5.
        unfold L.clock_of_nclock, stripname in H5. simpl in H5. inv H5.
        (* now (i,b0) = (i0,b1) *)
        inv Hse. inv H18. inv H7. simpl in H20. rewrite app_nil_r in H20.
        inv H20. inv H11.
        assert (Hxs' := Hxs).
        eapply fby_const_when in Hxs; eauto.
        now rewrite <- Hxs.
  Qed.

  Lemma sem_exp_caexp :
    forall G H b env e e' s ck,
      LT.wt_exp G env e ->
      to_cexp e = OK e' ->
      LS.sem_exp G H b e [s] ->
      sem_clock H b ck (abstract_clock s) ->
      NLSC.sem_caexp H b ck e' s.
  Proof.
    cofix Cofix. intros * Hwt Hto Hsem Hsc.
    pose proof (sem_exp_cexp _ _ _ _ _ _ _ _ Hwt Hto Hsem).
    unfold_Stv s; rewrite unfold_Stream in Hsc; simpl in Hsc;
      econstructor; eauto; eapply Cofix;
        eauto using sc_step, sem_cexp_step.
  Qed.

  Lemma sem_lexp_laexp :
    forall H b e s ck,
      NLSC.sem_exp H b e s ->
      sem_clock H b ck (abstract_clock s) ->
      NLSC.sem_aexp H b ck e s.
  Proof.
    cofix Cofix. intros * Hsem Hsc.
    unfold_Stv s; rewrite unfold_Stream in Hsc; simpl in Hsc;
      econstructor; eauto; eapply Cofix;
        eauto using sc_step, sem_lexp_step2.
  Qed.

  Module NCor := CorrectnessFun Ids Op OpAux Str IStr L LCA LT LC Lord LS LCS LN.

  Lemma sc_cexp : forall G env H b e vs,
      LC.wc_global G ->
      LCS.sc_nodes G ->
      NoDupMembers env ->
      LCS.sc_var_inv' env H b ->
      LN.Unnesting.normalized_cexp e ->
      LC.wc_exp G env e ->
      LS.sem_exp G H b e vs ->
      Forall2 (sem_clock H b) (L.clockof e) (map abstract_clock vs).
  Proof.
    intros * HwcG Hsc Hnd Hinv Hnormed Hwc Hsem.
    eapply LCS.sc_exp; eauto.
    eapply NCor.normalized_cexp_sem_sem_anon; eauto.
  Qed.

  Corollary sc_lexps : forall G env H b es vs,
      LC.wc_global G ->
      LCS.sc_nodes G ->
      NoDupMembers env ->
      LCS.sc_var_inv' env H b ->
      Forall LN.Unnesting.normalized_lexp es ->
      Forall (LC.wc_exp G env) es ->
      Forall2 (LS.sem_exp G H b) es vs ->
      Forall2 (sem_clock H b) (L.clocksof es) (map abstract_clock (concat vs)).
  Proof.
    induction es; intros * HwcG Hsc Hnd Hinv Hnormed Hwc Hsem;
      inv Hnormed; inv Hwc; inv Hsem; simpl; auto.
    rewrite map_app. eapply Forall2_app; eauto.
    eapply sc_cexp; eauto.
  Qed.

  Hint Resolve  envs_eq_find'.

  Lemma sem_toeq :
    forall cenv out G H P env envo eq eq' b,
      LN.NormFby.normalized_equation G out eq ->
      LT.wt_equation G (idty cenv) eq ->
      LC.wc_equation G (idck cenv) eq ->
      LC.wc_global G ->
      LCS.sc_nodes G ->
      NoDupMembers cenv ->
      envs_eq env (idck cenv) ->
      (forall f xs ys,
          LS.sem_node G f xs ys ->
          LCS.sem_clock_inputs G f xs ->
          NLSC.sem_node P f xs ys) ->
      LCS.sc_var_inv' (idck cenv) H b ->
      to_equation env envo eq = OK eq' ->
      LS.sem_equation G H b eq ->
      NLSC.sem_equation P H b eq'.
  Proof.
    intros ??????? [xs [|e []]] eq' b Hnormed Hwt Hwc Hwcg Hscg
           Hnodup Henvs Hsemnode Hvar Htoeq Hsem; try now (inv Htoeq; cases).
    rewrite <- NoDupMembers_idck in Hnodup.
    destruct Hwt as (Hwt1&Hwt2). destruct Hwc as (Hwc1&Hwc2&Hwc3).
    destruct e.
    1-4,7-9:(inv Hnormed; inv Hsem; simpl in *; simpl_Foralls;
             simpl in *; try rewrite app_nil_r in *; subst).
    - monadInv Htoeq.
      econstructor; eauto.
      eapply sem_exp_caexp; eauto.
      eapply sc_cexp in H7; eauto. simpl in *; simpl_Foralls.
      erewrite envs_eq_find in EQ; eauto; inv EQ; eauto.
    - monadInv Htoeq.
      econstructor; eauto.
      eapply sem_exp_caexp; eauto.
      eapply sc_cexp in H7; eauto. simpl in *; simpl_Foralls.
      erewrite envs_eq_find in EQ; eauto; inv EQ; eauto.
    - monadInv Htoeq.
      econstructor; eauto.
      eapply sem_exp_caexp; eauto.
      eapply sc_cexp in H7; eauto. simpl in *; simpl_Foralls.
      erewrite envs_eq_find in EQ; eauto; inv EQ; eauto.
    - monadInv Htoeq.
      econstructor; eauto.
      eapply sem_exp_caexp; eauto.
      eapply sc_cexp in H7; eauto. simpl in *; simpl_Foralls.
      erewrite envs_eq_find in EQ; eauto; inv EQ; eauto.
    - monadInv Htoeq.
      econstructor; eauto.
      eapply sem_exp_caexp; eauto.
      eapply sc_cexp in H7; eauto. simpl in *; simpl_Foralls.
      erewrite envs_eq_find in EQ; eauto; inv EQ; eauto.
      rewrite <- H13 in H0; inv H0; auto.
    - monadInv Htoeq.
      econstructor; eauto.
      eapply sem_exp_caexp; eauto.
      eapply sc_cexp in H7; eauto. simpl in *; simpl_Foralls.
      erewrite envs_eq_find in EQ; eauto; inv EQ; eauto.
      rewrite <- H13 in H0; inv H0; auto.
    - monadInv Htoeq.
      econstructor; eauto.
      eapply sem_exp_caexp; eauto.
      eapply sc_cexp in H7; eauto. simpl in *; simpl_Foralls.
      erewrite envs_eq_find in EQ; eauto; inv EQ; eauto.
      rewrite <- H13 in H0; inv H0; auto.
    - (* EFby *)
      inversion Htoeq as [Heq']. cases; monadInv Heq'. rename x1 into ck.
      assert (Hsem' := Hsem).
      inversion_clear Hsem as [ ????? Hseme Hsemv].
      inversion Hseme as [| ???? Hsef Hse]. inv Hse. simpl in Hsemv.
      rewrite app_nil_r in Hsemv.
      inversion Hsemv as [|???? Hsvar Hf2]. inv Hf2.
      assert (Hsc := Hwc1). (* eapply LCS.sc_equation in Hsc; simpl; eauto. *)
      simpl_Foralls.
      inversion H4 as [| | | | ? ? ? ? Hwte1 | | | | | |]. inv Hwte1.
      inversion Hsef as [| | | |???????? Hse0 Hse1 Hwfby | | | | | |].
      inversion_clear H2 as [| | | | | ???? Hwc0 ? Hck0 | | | | | |]; subst. apply Forall_singl in Hwc0.
      inversion Hse0 as [|????? Hf2]. inv Hf2.
      inversion Hse1 as [|????? Hf2]. inv Hf2.
      inversion Hwfby as [|?????? Hlsf Hf Hcat]. inv Hf. rewrite app_nil_r in *.
      subst. eapply sem_exp_lexp in EQ2; eauto.
      assert (sem_clock H b ck (abstract_clock y5)) as Hck.
      { inv Hnormed. 2:inv H18; inv H14.
        eapply sc_cexp in H11; eauto.
        apply LN.Unnesting.normalized_lexp_numstreams in H28. rewrite <- L.length_clockof_numstreams in H28.
        singleton_length.
        apply Forall2_singl in Hck0; subst.
        erewrite envs_eq_find in EQ0; eauto. inv EQ0; eauto. inv H5; auto.
        apply Forall2_singl in H11; auto.
      }
      econstructor; eauto. instantiate (1 := y5).
      + eapply sem_lexp_laexp; eauto.
      + (* we show how to erase Whens in constants using var_fby_const *)
        eapply var_fby_const in Hlsf; eauto.
        rewrite <- LCS.ac_fby2; eauto.
    - (* EArrow *) inv Hnormed. inv H2. inv H0.
    - (* Eapp *)
      assert (Forall LN.Unnesting.normalized_lexp l) as Hnormed'.
      { clear - Hnormed. inv Hnormed; eauto. inv H1; inv H. }
      simpl in Htoeq. cases; monadInv Htoeq.
      + (* reset *)
        inversion Hsem; subst. simpl_Foralls. simpl in *. rewrite app_nil_r in *.
        take (LS.sem_exp _ _ _ _ _) and inv it.
        take (LT.wt_exp _ _ _) and inv it.
        econstructor; eauto using sem_exps_lexps.
        2:{ inv H12; auto. }
        2:{ intros k. specialize (H14 k).
            eapply Hsemnode; eauto. take (LS.sem_node _ _ _ _) and inv it.
            unfold LCS.sem_clock_inputs. esplit; esplit; split; eauto. split; eauto.
            (* now we use sc_inside *)
            take (LC.wc_exp _ _ _) and inv it.
            match goal with
            | H1: L.find_node _ G = Some _, H2: L.find_node _ G = Some _ |- _
              => rewrite H2 in H1; inv H1
            end.
            take (L.find_node _ _ = _) and eapply LC.wc_find_node in it
              as (?&?&?); eauto.
            eapply LCS.sc_inside_mask' with (es := l); eauto.
            clear - H10 Hnormed'.
            induction H10; inv Hnormed'; constructor; eauto.
            eapply NCor.normalized_lexp_sem_sem_anon; eauto. }

        take (LC.wc_exp _ _ _) and inversion_clear it
          as [| | | | | | | | | | |?????? bck sub Wce ? WIi WIo Wcr ?].
        eapply sc_lexps in H10 as Hsc; eauto.
        take (L.find_node _ _ = Some n0) and
             pose proof (LC.wc_find_node _ _ n0 Hwcg it) as (?& (Wcin &?)).
        assert (find_base_clock (L.clocksof l) = bck) as ->.
        {
          apply find_base_clock_bck.
          + rewrite L.clocksof_nclocksof. eapply LC.WellInstantiated_bck; eauto.
            unfold idck. rewrite map_length. exact (L.n_ingt0 n0).
          + apply LC.WellInstantiated_parent in WIi.
            rewrite L.clocksof_nclocksof, Forall_map.
            eapply Forall_impl; eauto. now simpl.
        }
        eapply LCS.sc_parent with (ck := bck) in Hsc; eauto.
        { rewrite L.clocksof_nclocksof. eapply LC.WellInstantiated_bck; eauto.
          unfold idck. rewrite map_length. exact (L.n_ingt0 n0). }
        { apply LC.WellInstantiated_parent in WIi.
          rewrite L.clocksof_nclocksof, Forall_map.
          eapply Forall_impl; eauto. now simpl. }
      + (* not reset *)
        inversion Hsem; subst. simpl_Foralls. simpl in *. rewrite app_nil_r in *.
        take (LS.sem_exp _ _ _ _ _) and inv it.
        take (LT.wt_exp _ _ _) and inv it.
        econstructor; eauto using sem_exps_lexps.
        2:{ eapply Hsemnode; eauto. take (LS.sem_node _ _ _ _) and inv it.
            unfold LCS.sem_clock_inputs. esplit; esplit; split; eauto. split; eauto.
            (* now we use sc_inside *)
            take (LC.wc_exp _ _ _) and inv it.
            match goal with
            | H1: L.find_node _ G = Some _, H2: L.find_node _ G = Some _ |- _
              => rewrite H2 in H1; inv H1
            end.
            take (L.find_node _ _ = _) and eapply LC.wc_find_node in it
              as (?&?&?); eauto.
            eapply LCS.sc_inside' with (es := l); eauto.
            clear - H10 Hnormed'.
            induction H10; inv Hnormed'; constructor; eauto.
            eapply NCor.normalized_lexp_sem_sem_anon; eauto. }

        take (LC.wc_exp _ _ _) and inversion_clear it
          as [| | | | | | | | | | ???? bck sub Wce ? WIi WIo |].
        eapply sc_lexps in H10 as Hsc; eauto.
        take (L.find_node _ _ = Some n0) and
             pose proof (LC.wc_find_node _ _ n0 Hwcg it) as (?& (Wcin &?)).
        assert (find_base_clock (L.clocksof l) = bck) as ->.
        {
          apply find_base_clock_bck.
          + rewrite L.clocksof_nclocksof. eapply LC.WellInstantiated_bck; eauto.
            unfold idck. rewrite map_length. exact (L.n_ingt0 n0).
          + apply LC.WellInstantiated_parent in WIi.
            rewrite L.clocksof_nclocksof, Forall_map.
            eapply Forall_impl; eauto. now simpl.
        }
        eapply LCS.sc_parent with (ck := bck) in Hsc; eauto.
        { rewrite L.clocksof_nclocksof. eapply LC.WellInstantiated_bck; eauto.
          unfold idck. rewrite map_length. exact (L.n_ingt0 n0). }
        { apply LC.WellInstantiated_parent in WIi.
          rewrite L.clocksof_nclocksof, Forall_map.
          eapply Forall_impl; eauto. now simpl. }
  Qed.

  Lemma sem_toeqs' :
    forall cenv out G H P env envo eqs eqs' b,
      Forall (LN.NormFby.normalized_equation G out) eqs ->
      Forall (LT.wt_equation G (idty cenv)) eqs ->
      Forall (LC.wc_equation G (idck cenv)) eqs ->
      LC.wc_global G ->
      LCS.sc_nodes G ->
      NoDupMembers cenv ->
      envs_eq env (idck cenv) ->
      (forall f xs ys,
          LS.sem_node G f xs ys ->
          LCS.sem_clock_inputs G f xs ->
          NLSC.sem_node P f xs ys) ->
      LCS.sc_var_inv' (idck cenv) H b ->
      mmap (to_equation env envo) eqs = OK eqs' ->
      Forall (LS.sem_equation G H b) eqs ->
      Forall (NLSC.sem_equation P H b) eqs'.
  Proof.
    induction eqs; intros * Hnormed Hwt Hwc HwcG HscG Hndup Henvs Hsemnode Hinv Heqs Hsem;
      inv Hnormed; inv Hwt; inv Hwc; inv Hsem; simpl in *; monadInv Heqs; auto.
    - constructor; eauto.
      eapply sem_toeq; eauto.
  Qed.

  Lemma sem_toeqs :
    forall G n H P env envo eqs' ins,
      LN.NormFby.normalized_node G n ->
      Forall (LT.wt_equation G (idty (L.n_in n ++ L.n_vars n ++ L.n_out n))) (L.n_eqs n) ->
      Forall (LC.wc_equation G (idck (L.n_in n ++ L.n_vars n ++ L.n_out n))) (L.n_eqs n) ->
      LCA.node_causal n ->
      Lord.Ordered_nodes G ->
      LT.wt_global G ->
      LC.wc_global G ->
      LCS.sc_nodes G ->
      envs_eq env (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)) ->
      (forall f xs ys,
          LS.sem_node G f xs ys ->
          LCS.sem_clock_inputs G f xs ->
          NLSC.sem_node P f xs ys) ->
      LC.wc_node G n ->
      Forall2 (sem_var H) (L.idents (L.n_in n)) ins ->
      LCS.sem_clock_inputs (n :: G) (L.n_name n) ins ->
      mmap (to_equation env envo) (L.n_eqs n) = OK eqs' ->
      Forall (LS.sem_equation G H (clocks_of ins)) (L.n_eqs n) ->
      Forall (NLSC.sem_equation P H (clocks_of ins)) eqs'.
  Proof.
    intros * Hnormed Hwt Hwc Hcaus Hord Hwcg Hwtg Hscn Henvs Hnode Hwcn Hins Hscin Hmmap Hsem.

    assert (LCS.sc_var_inv' (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)) H (clocks_of ins)) as Hinv.
    { eapply LCS.sc_node_sc_var_inv'; eauto.
      + destruct Hscin as (?&?&?&?&?).
        simpl in H0. rewrite ident_eqb_refl in H0. inv H0.
        eapply LCS.sem_clocks_det'; eauto. destruct Hwcn as (?&_); auto.
      + eapply Forall_impl_In; [|eauto]. intros.
        eapply NCor.normalized_equation_sem_sem_anon; eauto. 1,2:eapply Forall_forall; eauto.
    }

    eapply sem_toeqs' in Hmmap; eauto.
    eapply fst_NoDupMembers, L.node_NoDup.
  Qed.

  Lemma inputs_clocked_vars :
    forall n G H f ins,
      LCS.sem_clock_inputs (n :: G) f ins ->
      L.n_name n = f ->
      wc_env (idck (L.n_in n)) ->
      Forall2 (sem_var H) (L.idents (L.n_in n)) ins ->
      NLSC.sem_clocked_vars H (clocks_of ins) (idck (L.n_in n)).
  Proof.
    intros * Hv Hnf Wcin Hins.
    eapply LCS.inputs_clocked_vars in Hv; eauto.
    unfold NLSC.sem_clocked_vars, NLSC.sem_clocked_var.
    unfold idck, L.idents in *.
    rewrite Forall2_map_1 in Hins. rewrite Forall2_map_1, Forall2_map_2 in Hv. rewrite Forall_map.
    eapply Forall2_Forall2 in Hv; [|eapply Hins].
    eapply Forall2_ignore2 in Hv. eapply Forall_impl; [|eauto].
    intros (?&?&?) (?&?&?&?); simpl in *.
    split; intros; eauto.
    exists (abstract_clock x); split; auto.
    eapply sem_var_det in H1; eauto. rewrite <- H1. apply ac_aligned.
  Qed.

  Module Import TrOrdered := TrOrderedFun Ids Op OpAux L Lord CE NL Ord TR.

  Theorem sem_l_nl :
    forall G P Hprefs f ins outs,
      LN.NormFby.normalized_global G ->
      Lord.Ordered_nodes G ->
      Forall LCA.node_causal G ->
      LT.wt_global G ->
      LC.wc_global G ->
      to_global G Hprefs = OK P ->
      LS.sem_node G f ins outs ->
      LCS.sem_clock_inputs G f ins ->
      NLSC.sem_node P f ins outs.
  Proof.
    induction G as [|node]. now inversion 7.
    intros * Hnormed Hord Hcaus Hwt Hwc Htr Hsem Hscin.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [? ? ? ? ? ? Hfind Hins Houts Heqs Hbk].
    pose proof (Lord.find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    inv Hnormed. inv Hwt. inv Hwc. inv Hcaus.
    assert (LCS.sc_nodes G) as Hsc.
    { inv Hord. eapply LCS.l_sem_node_clock; eauto. }
    simpl in Hfind. destruct (ident_eqb (L.n_name node) f) eqn:Hnf.
    - assert (Hord':=Hord).
      inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn].
      inv Hfind.
      eapply LS.Forall_sem_equation_global_tl in Heqs; eauto.
      assert (Htr':=Htr). monadInv Htr'.
      assert (forall f ins outs,
                 LS.sem_node G f ins outs ->
                 LCS.sem_clock_inputs G f ins ->
                 NLSC.sem_node x0 f ins outs) as IHG'
          by eauto.
      apply ident_eqb_eq in Hnf. rewrite <- Hnf.
      take (LT.wt_node _ _) and inversion it as (Hwt1 & Hwt2 & Hwt3 & Hwt4).
      take (LC.wc_node _ _) and inversion it as (Hwc1 & Hwc2 & Hwc3 & Hwc4).
      econstructor; simpl.
      + erewrite <- to_node_name, ident_eqb_refl; eauto.
      + erewrite <- to_node_in; eauto.
      + erewrite <- to_node_out; eauto.
      + erewrite <- to_node_in; eauto.
        eapply inputs_clocked_vars; eauto.
      + apply NLSC.sem_equation_cons2; auto.
        * eapply ord_l_nl; eauto.
        * assert (Hton := EQ). tonodeInv EQ; simpl in *.
          eapply sem_toeqs; eauto.
          apply envs_eq_node.
        * assert (Htrn' := EQ).
          apply to_node_name in EQ. rewrite <- EQ.
          eapply ninin_l_nl; eauto.
    - apply ident_eqb_neq in Hnf.
      eapply LS.sem_node_cons in Hsem; auto.
      eapply LCS.sem_clock_inputs_cons in Hscin; auto.
      assert (Htr' := Htr).
      monadInv Htr.
      rewrite cons_is_app in Hord.
      apply Lord.Ordered_nodes_append in Hord.
      eapply NLSC.sem_node_cons2; eauto.
      + eapply ord_l_nl; eauto.
      + apply to_node_name in EQ. rewrite <- EQ.
        eapply TR.to_global_names; eauto.
  Qed.

End CORRECTNESS.

Module CorrectnessFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX        Op)
       (L     : LSYNTAX          Ids Op)
       (CE    : CESYNTAX             Op)
       (NL    : NLSYNTAX         Ids Op              CE)
       (TR    : TR               Ids Op OpAux L      CE NL)
       (LT    : LTYPING          Ids Op       L)
       (LC    : LCLOCKING        Ids Op       L)
       (LCA   : LCAUSALITY       Ids Op       L)
       (Ord   : NLORDERED        Ids Op              CE NL)
       (Lord  : LORDERED         Ids Op       L)
       (Str   : COINDSTREAMS         Op OpAux)
       (IStr  : INDEXEDSTREAMS       Op OpAux)
       (LS    : LSEMANTICS       Ids Op OpAux L Lord       Str)
       (LCS   : LCLOCKSEMANTICS  Ids Op OpAux L LC LCA Lord Str IStr LS)
       (LN          : NORMALIZATION    Ids Op OpAux L LCA)
       (NLSC  : NLCOINDSEMANTICS Ids Op OpAux        CE NL Str Ord)
<: CORRECTNESS Ids Op OpAux L CE NL TR LT LC LCA Ord Lord Str IStr LS LCS LN NLSC.
  Include CORRECTNESS Ids Op OpAux L CE NL TR LT LC LCA Ord Lord Str IStr LS LCS LN NLSC.
End CorrectnessFun.
