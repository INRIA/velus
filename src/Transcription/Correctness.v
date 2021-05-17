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
       (LN          : NORMALIZATION    Ids Op OpAux L    LCA)
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

  Lemma fby1_reset1_fby : forall bs c v v' xs ys r vs,
      aligned ys bs ->
      xs ≡ const bs c ->
      LiftO (v = sem_const c) (fun v' => v = v') v' ->
      LS.fby1 v' xs ys r vs ->
      vs ≡ NLSC.reset1 (sem_const c) (sfby v ys) r false.
  Proof.
    intros * Haligned Hconst Hv' Hfby.
    eapply ntheq_eqst. intros n. revert n bs v v' xs ys r vs Haligned Hconst Hv' Hfby.
    induction n;
      (intros * Haligned Hconst Hv' Hfby;
       inv Haligned; inv Hfby;
       simpl in Hconst; inv Hconst;
       repeat rewrite Str_nth_0_hd; repeat rewrite Str_nth_S_tl; simpl in * ); auto.
    - inv H0; auto.
    - inv H0; eauto.
    - eapply IHn; eauto. simpl; auto.
    - eapply IHn; eauto; simpl; auto.
    - eapply IHn; eauto; simpl; auto.
    - etransitivity. eapply IHn in H3; eauto. simpl; auto.
      apply eqst_ntheq. symmetry. apply NLSC.reset1_fby.
    - destruct v'; eapply IHn; eauto.
  Qed.

  Corollary fby_reset_fby:
    forall b c xs ys r zs,
      b  ≡ abstract_clock zs ->
      LS.fby xs ys r zs ->
      xs ≡ const b c ->
      zs ≡ NLSC.reset (sem_const c) (sfby (sem_const c) ys) r.
  Proof.
    intros. eapply fby1_reset1_fby; eauto. 2:simpl; auto.
    eapply LS.ac_fby12 in H0. rewrite H, <- H0.
    apply ac_aligned.
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

  Fact sem_clock_ac : forall H bs bs' ck x b xs vs ys,
      sem_var H x vs ->
      sem_clock H bs (Con ck x b) bs' ->
      when b xs vs ys ->
      bs' ≡ abstract_clock ys.
  Proof.
    intros * Hvar Hck Hwhen.
    rewrite LCS.CIStr.sem_clock_equiv in *.
    apply LCS.CIStr.CIStr.sem_var_impl in Hvar.
    rewrite when_spec in Hwhen.
    apply ntheq_eqst.
    intros n. specialize (Hvar n). specialize (Hck n). specialize (Hwhen n).
    repeat rewrite LCS.CIStr.CIStr.tr_Stream_nth in Hck. rewrite LCS.CIStr.CIStr.tr_Stream_nth in Hvar.
    rewrite ac_nth.
    destruct Hwhen as [(Hx&Hv&Hy)|[(?&?&Hx&Hv&?&Hy)|(?&?&Hx&Hv&?&Hy)]]; rewrite Hv, Hy in *.
    - inv Hck; auto. exfalso.
      eapply IStr.sem_var_instant_det in Hvar; eauto; congruence.
    - inv Hck; auto. exfalso.
      eapply IStr.sem_var_instant_det in Hvar; [|eauto]. inv Hvar.
      rewrite H0 in H7; inv H7.
      apply Bool.no_fixpoint_negb in H2; auto.
    - inv Hck; auto. 1,2:exfalso.
      1,2:eapply IStr.sem_var_instant_det in Hvar; [|eauto]; try congruence.
      inv Hvar. rewrite H0 in H7; inv H7.
      apply Bool.no_fixpoint_negb in H2; auto.
  Qed.

  Fact sem_clock_inv : forall H bs ck x b xs vs ys,
      sem_var H x vs ->
      sem_clock H bs (Con ck x b) (abstract_clock ys) ->
      when b xs vs ys ->
      sem_clock H bs ck (abstract_clock xs).
  Proof.
    intros * Hvar Hck Hwhen.
    rewrite LCS.CIStr.sem_clock_equiv in *.
    apply LCS.CIStr.CIStr.sem_var_impl in Hvar.
    rewrite when_spec in Hwhen.
    intros n. specialize (Hvar n). specialize (Hck n). specialize (Hwhen n).
    rewrite LCS.CIStr.CIStr.tr_Stream_ac in *.
    repeat rewrite LCS.CIStr.CIStr.tr_Stream_nth in *. rewrite LCS.CIStr.CIStr.tr_Stream_nth in Hvar.
    destruct Hwhen as [(Hx&Hv&Hy)|[(?&?&Hx&Hv&?&Hy)|(?&?&Hx&Hv&?&Hy)]];
      rewrite Hx, Hv, Hy in *; inv Hck; auto.
    1,2:eapply IStr.sem_var_instant_det in Hvar; eauto; congruence.
  Qed.

  Fact sem_clock_const : forall H ck x s b bs bs' bs'' c xs ys,
    sem_var H x s ->
    sem_clock H bs ck bs' ->
    sem_clock H bs (Con ck x b) bs'' ->
    when b xs s ys ->
    xs ≡ const bs' c ->
    ys ≡ const bs'' c.
  Proof.
    intros * Hvar Hck1 Hck2 Hwhen Hcs.
    apply LCS.CIStr.CIStr.sem_var_impl in Hvar.
    rewrite LCS.CIStr.sem_clock_equiv in *.
    rewrite when_spec in Hwhen.
    apply ntheq_eqst. intros n.
    specialize (Hvar n). specialize (Hck1 n). specialize (Hck2 n). specialize (Hwhen n).
    apply eqst_ntheq with (n:=n) in Hcs.
    repeat rewrite LCS.CIStr.CIStr.tr_Stream_nth in Hck1, Hck2. rewrite LCS.CIStr.CIStr.tr_Stream_nth in Hvar.
    rewrite const_nth' in *.
    destruct Hwhen as [(Hx&Hv&Hy)|[(?&?&Hx&Hv&?&Hy)|(?&?&Hx&Hv&?&Hy)]];
      rewrite Hx, Hv, Hy in *; auto; inv Hck2; auto. 1,2,4,5:exfalso.
    1-5:eapply IStr.sem_var_instant_det in Hvar; [|eauto]; inv Hvar.
    1-2:rewrite H0 in H7; inv H7; apply Bool.no_fixpoint_negb in H2; auto.
    - destruct (bs' # n); congruence.
  Qed.

  Lemma to_constant_sem : forall G cenv H b e ck b' c cs,
      L.clockof e = [ck] ->
      LC.wc_exp G cenv e ->
      to_constant e = OK c ->
      LS.sem_exp G H b e [cs] ->
      sem_clock H b ck b' ->
      cs ≡ const b' c.
  Proof.
    induction e using L.exp_ind2;
      intros * Hck Hwc Hconst Hsem Hsck; simpl in *; inv Hconst.
    - (* constant *) inv Hck.
      inv Hsem. inv Hsck.
      rewrite <- H1. assumption.
    - (* when *)
      do 2 (destruct es; try congruence).
      apply Forall_singl in H0.
      inv Hwc; simpl in *; rewrite app_nil_r in *.
      apply Forall_singl in H6.
      do 2 (destruct tys; simpl in *; try congruence). inv Hck.
      symmetry in H9. singleton_length.
      apply Forall_singl in H8; inv H8.
      inv Hsem. inv H12; inv H8. simpl in H14; rewrite app_nil_r in H14. inv H14; inv H9.
      assert (b' ≡ abstract_clock cs) as Hac.
      { eapply sem_clock_ac in Hsck; eauto. }
      rewrite Hac in *. eapply sem_clock_inv in H8 as Hck'; eauto. 2:eapply Hsck.
      assert (Hx0:=Hck'). eapply H0 in Hx0; eauto.
      eapply sem_clock_const; eauto. eapply Hsck.
  Qed.

  Lemma var_fby_const :
    forall G H b c a env cenv ck x e0 e1 r cs xs ys rs,
      LS.sem_exp G H b e0 [cs] ->
      sem_var H x xs ->
      LS.fby cs ys rs xs ->
      In (x, ck) cenv ->
      envs_eq env cenv ->
      LC.wc_exp G cenv (L.Efby [e0] [e1] r a) ->
      [ck] = map L.clock_of_nclock a ->
      to_constant e0 = OK c ->
      sem_clock H b ck (abstract_clock xs) ->
      sem_var H x (NLSC.reset (sem_const c) (sfby (sem_const c) ys) rs).
  Proof.
    intros * Hse Hxs Hfby Hin Henv Hwc Hck Htoc Hsc.
    eapply fby_reset_fby in Hfby; eauto. 2:reflexivity.
    rewrite <- Hfby; eauto.
    inv Hwc.
    eapply Forall_singl in H4.
    simpl in H7; rewrite app_nil_r, <- Hck in H7. apply Forall2_eq in H7.
    eapply to_constant_sem in Htoc; eauto.
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
    assert (Hsem':=Hsem). eapply sem_exp_cexp in Hsem'; [|eauto|eauto].
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

  Hint Resolve  envs_eq_find'.

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
      inversion Htoeq as [Heq'].
      destruct (vars_of l1) eqn:Vars. eapply vars_of_spec in Vars.
      1,2:cases; monadInv Heq'. rename x1 into ck.
      assert (Hsem' := Hsem).
      inversion_clear Hsem as [ ????? Hseme Hsemv].
      inversion Hseme as [| ???? Hsef Hse]. inv Hse. simpl in Hsemv.
      rewrite app_nil_r in Hsemv.
      inversion Hsemv as [|???? Hsvar Hf2]. inv Hf2.
      assert (Hsc := Hwc1). (* eapply LCS.sc_equation in Hsc; simpl; eauto. *)
      simpl_Foralls.
      inversion H4 as [| | | | ? ? ? ? ? Hwte1 | | | | |]. inv Hwte1.
      inversion Hsef as [| | | | ??????????? Hse0 Hse1 Hser ? Hwfby | | | | |]; subst.
      inversion_clear H2 as [| | | | | ????? Hwc0 ?? Hck0 | | | | |]; subst. apply Forall_singl in Hwc0.
      inversion Hse0 as [|????? Hf2]. inv Hf2.
      inversion Hse1 as [|????? Hf2]. inv Hf2.
      inversion Hwfby as [|?????? Hlsf Hf Hcat]. inv Hf. rewrite app_nil_r in *.
      subst. eapply sem_exp_lexp in EQ2; eauto.
      assert (y = ck); subst.
      { erewrite envs_eq_find in EQ0; eauto. inv EQ0; eauto. }
      assert (sem_clock H b ck (abstract_clock y5)) as Hck.
      { inv Hnormed. 2:inv H28; inv H26.
        eapply sc_cexp in Hwc0; eauto.
        apply LN.Unnesting.normalized_lexp_numstreams in H34. rewrite <- L.length_clockof_numstreams in H34.
        singleton_length.
        apply Forall2_singl in Hck0; subst.
        inv H5; auto.
        apply Forall2_singl in Hwc0; auto.
      }
      econstructor; try reflexivity; eauto.
      + eapply sem_lexp_laexp; eauto.
      + rewrite Forall2_map_1. clear - Vars Hser.
        eapply Forall2_swap_args in Vars.
        eapply Forall2_trans_ex in Hser; eauto.
        eapply Forall2_impl_In; [|eauto].
        intros (?&?) ? _ _ (?&?&(?&?&?)&?); subst.
        inv H2; auto.
      + unfold NLSC.sem_clocked_vars.
        eapply Forall2_ignore1 in Vars.
        eapply Forall_impl; [|eauto].
        intros (?&?) (?&?&?&?&?); subst. eapply Forall_forall in H19; eauto.
        eapply Forall_forall in Hvar. 2:inv H19; eauto.
        destruct Hvar as (?&Var&Ck).
        constructor.
        * intros * Var'. eapply sem_var_det in Var; eauto.
          simpl. repeat esplit; eauto.
          rewrite Var. apply ac_aligned.
        * intros * Ck'; eauto.
      + (* we show how to erase Whens in constants using var_fby_const *)
        eapply var_fby_const in Hlsf; eauto.
        rewrite <- LS.ac_fby2; eauto.
    - (* EArrow *) inv Hnormed. inv H2. inv H0.
    - (* Eapp *)
      assert (Forall LN.Unnesting.normalized_lexp l) as Hnormed'.
      { clear - Hnormed. inv Hnormed; eauto. inv H1; inv H. }
      simpl in Htoeq.
      destruct (vars_of l0) eqn:Vars. eapply vars_of_spec in Vars.
      1,2:cases; monadInv Htoeq.
      inversion Hsem; subst. simpl_Foralls. simpl in *. rewrite app_nil_r in *.
      take (LS.sem_exp _ _ _ _ _) and inv it.
      take (LT.wt_exp _ _ _) and inv it.
      econstructor; eauto using sem_exps_lexps.
      2:{ rewrite Forall2_map_1. clear - Vars H12.
        eapply Forall2_swap_args in Vars.
        eapply Forall2_trans_ex in H12; eauto.
        eapply Forall2_impl_In; [|eauto].
        intros (?&?) ? _ _ (?&?&(?&?&?)&?); subst.
        inv H2; auto. }
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
        as [| | | | | | | | | |????? bck sub Wce ?? WIi WIo Wcr].
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
       (LN          : NORMALIZATION    Ids Op OpAux L    LCA)
       (NLSC  : NLCOINDSEMANTICS Ids Op OpAux        CE NL Str Ord)
<: CORRECTNESS Ids Op OpAux L CE NL TR LT LC LCA Ord Lord Str IStr LS LCS LN NLSC.
  Include CORRECTNESS Ids Op OpAux L CE NL TR LT LC LCA Ord Lord Str IStr LS LCS LN NLSC.
End CorrectnessFun.
