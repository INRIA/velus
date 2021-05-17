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
       (Import OpAux: OPERATORS_AUX    Ids Op)
       (Import Cks  : CLOCKS           Ids Op OpAux)
       (L           : LSYNTAX          Ids Op OpAux Cks)
       (Import CE   : CESYNTAX         Ids Op OpAux Cks)
       (NL          : NLSYNTAX         Ids Op OpAux Cks        CE)
       (Import TR   : TR               Ids Op OpAux Cks L      CE NL)
       (LT          : LTYPING          Ids Op OpAux Cks L)
       (LC          : LCLOCKING        Ids Op OpAux Cks L)
       (LCA         : LCAUSALITY       Ids Op OpAux Cks L)
       (Ord         : NLORDERED        Ids Op OpAux Cks        CE NL)
       (Lord        : LORDERED         Ids Op OpAux Cks L)
       (Import Str  : COINDSTREAMS     Ids Op OpAux Cks)
       (IStr        : INDEXEDSTREAMS   Ids Op OpAux Cks)
       (LS          : LSEMANTICS       Ids Op OpAux Cks L Lord       Str)
       (LCS         : LCLOCKSEMANTICS  Ids Op OpAux Cks L LC LCA Lord Str IStr LS)
       (LN          : NORMALIZATION    Ids Op OpAux Cks L    LCA)
       (NLSC        : NLCOINDSEMANTICS Ids Op OpAux Cks        CE NL Str Ord).

  Lemma sem_lexp_step {prefs} :
    forall (G: @L.global prefs) H b e e' v s,
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
    - inv Hsem. constructor.
      inv H4; simpl in *; auto.
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

  Lemma sem_cexp_step {prefs} :
    forall (G: @L.global prefs) H b e e' v s,
      to_cexp e = OK e' ->
      LS.sem_exp G H b e [v ⋅ s] ->
      LS.sem_exp G (history_tl H) (Streams.tl b) e [s].
  Proof.
    einduction e using L.exp_ind2; intros * Htr Hsem;
      (now inv Htr) || (unfold to_cexp in Htr;
                       try (monadInv Htr; eapply sem_lexp_step; simpl; eauto)).
    1,2:destruct a as ([|? [|]]&?&?); monadInv Htr; fold to_cexp in *.
    - inv Hsem; inv H10; inv H6.
      destruct s0.
      eapply LS.Smerge with (vs0:=map (map (map (fun x => Streams.tl x))) vs); eauto.
      + eapply sem_var_step; eauto.
      + clear - EQ H0 H1 H3 H9. rewrite Forall2_map_2.
        revert dependent vs. revert dependent x0. revert dependent hd1.
        induction es; intros; inv H9; inv H0; inv H1; inv H3;
          monadInv EQ;
          constructor; eauto.
        clear EQ IHes H7 H8 H9 H11.
        cases. inv H6; inv H7. inv H5; inv H8. simpl in *; rewrite app_nil_r in *.
        destruct y1 as [|? [|]]; simpl in *; inv H4; inv H2. destruct y0.
        eapply H3 in EQ0; eauto.
      + inv H5; repeat econstructor; eauto.
        1,3:(rewrite map_map, Forall2_map_1, Forall2_map_2;
             rewrite Forall2_map_1 in H3;
             eapply Forall2_impl_In; [|eauto]; intros; simpl in *;
             rewrite <-concat_map; destruct (concat a); simpl in *; now inv H5).
        1,2:(rewrite 2 map_map, Forall_map;
             rewrite map_map, Forall_map in H1;
             eapply Forall_impl; [|eauto]; intros; simpl in *;
             rewrite <-concat_map; destruct (concat a); simpl in *; try rewrite H2; auto).
    - inv Hsem; inv H10; inv H6.
      destruct s0.
      eapply LS.Scase with (vs0:=map (map (map (fun x => Streams.tl x))) vs); eauto.
      + eapply sem_lexp_step; eauto.
      + clear - EQ1 H0 H1 H3 H9. rewrite Forall2_map_2.
        revert dependent vs. revert dependent x0. revert dependent hd1.
        induction es; intros; inv H9; inv H0; inv H1; inv H3;
          monadInv EQ1;
          constructor; eauto.
        clear EQ1 IHes H7 H8 H9 H11.
        cases. inv H6; inv H7. inv H5; inv H8. simpl in *; rewrite app_nil_r in *.
        destruct y1 as [|? [|]]; simpl in *; inv H4; inv H2. destruct y0.
        eapply H3 in EQ; eauto.
      + inv H5; repeat econstructor; eauto.
        1,3:(rewrite map_map, Forall2_map_1, Forall2_map_2;
             rewrite Forall2_map_1 in H3;
             eapply Forall2_impl_In; [|eauto]; intros; simpl in *;
             rewrite <-concat_map; destruct (concat a); simpl in *; now inv H5).
        1,2:(rewrite 2 map_map, Forall_map;
             rewrite map_map, Forall_map in H1;
             eapply Forall_impl; [|eauto]; intros; simpl in *;
             rewrite <-concat_map; destruct (concat a); simpl in *; try rewrite H2; auto).
  Qed.

  Lemma ty_lexp {prefs} :
    forall (G: @L.global prefs) env e e',
      LT.wt_exp G env e ->
      to_lexp e = OK e' ->
      L.typeof e = [CE.typeof e'].
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr; inv Htr.
    - now simpl.
    - now simpl.
    - destruct a. inv H0. now simpl.
    - destruct a. simpl. monadInv H0. now simpl.
    - destruct a. monadInv H0. now simpl.
    - cases. inv H. simpl. inv Hwt. inv H10. inv H5. monadInv H1.
      unfold L.typesof. unfold flat_map. simpl. rewrite app_nil_r in H11.
      eapply H3 in H2; eauto. congruence.
  Qed.

  Lemma sem_exp_lexp {prefs} :
    forall (G : @L.global prefs) env H b e e' s,
      LT.wt_exp G env e ->
      to_lexp e = OK e' ->
      LS.sem_exp G H b e [s] ->
      NLSC.sem_exp H b e' s.
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr Hsem; inv Htr.
    - inv Hsem. now econstructor.
    - inv Hsem. now constructor.
    - destruct a. inv Hsem. inv H1. econstructor; eauto.
    - destruct a. inv Hsem. monadInv H1. inv Hwt. econstructor; eauto.
      eapply ty_lexp in EQ; eauto. rewrite H9 in EQ. now inv EQ.
    - destruct a. inv Hsem. monadInv H1. inv Hwt. econstructor; eauto.
      eapply ty_lexp in EQ; eauto. eapply ty_lexp in EQ1; eauto.
      rewrite H11 in EQ. inv EQ. rewrite H12 in EQ1. now inv EQ1.
    - cases. monadInv H2. inv Hsem. inv H0. clear H4. inv Hwt.
      inv H9. inv H5. inv H12. inv H5. simpl in H11; rewrite app_nil_r in H11. inv H11. inv H12.
      econstructor; eauto.
  Qed.

  Lemma sem_lexp_single {prefs} :
    forall e e' G H b ss,
      to_lexp e = OK e' ->
      LS.sem_exp (G: @L.global prefs) H b e ss ->
      exists s, ss = [s].
  Proof.
    induction e using L.exp_ind2; intros * Htr Hsem; inv Htr;
      try (inv Hsem; eexists; now eauto).
    cases_eqn H2. subst. monadInv H2. inv Hsem. inv H9. inv H5. inv H. inv H5.
    eapply H4 in EQ; [|eauto]. inv EQ. simpl in H11. inv H11. inv H6.
    eauto.
  Qed.

  Lemma sem_exps_lexps {prefs} :
    forall (G: @L.global prefs) H b tenv es les ss,
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

  Lemma sem_exp_cexp {prefs} :
    forall (G: @L.global prefs) env H b e e' s,
      LT.wt_exp G env e ->
      to_cexp e = OK e' ->
      LS.sem_exp G H b e [s] ->
      NLSC.sem_cexp H b e' s.
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr Hsem;
      (now inv Htr) || (unfold to_cexp in Htr;
                       try (monadInv Htr; econstructor;
                            eapply sem_exp_lexp; eauto));
      destruct a as (?&?&?); destruct l as [|? [|]]; try monadInv Htr;
        fold to_cexp in *.
    - inv Hsem; inv H10; inv H6.
      rewrite Forall2_map_1 in H3. rewrite map_map, Forall_map in H1.
      inv Hwt.
      econstructor; eauto.
      clear - H0 H1 H3 H9 H15 EQ.
      revert vs hd1 x0 H1 H3 H9 EQ.
      induction es; intros; inv H15; inv H0; simpl in *; monadInv EQ;
        inv H9; inv H3; inv H1; constructor; eauto.
      clear EQ IHes H6 H8 H10 H11 H12.
      cases_eqn EQ0. inv H4; inv H8.
      simpl in *; rewrite app_nil_r in *.
      destruct y1 as [|? [|]]; simpl in *; inv H9; inv H3.
      inv H5. inv H7. auto.
    - inv Hsem; inv H10; inv H6.
      rewrite Forall2_map_1 in H3. rewrite map_map, Forall_map in H1.
      inv Hwt.
      econstructor; eauto.
      + eapply sem_exp_lexp in EQ; eauto.
      + clear - H0 H1 H3 H9 H15 EQ1.
        revert vs hd1 x0 H1 H3 H9 EQ1.
        induction es; intros; inv H15; inv H0; simpl in *; monadInv EQ1;
          inv H9; inv H3; inv H1; constructor; eauto.
        clear EQ1 IHes H6 H8 H10 H11 H12.
        cases_eqn EQ0. inv H4; inv H8.
        simpl in *; rewrite app_nil_r in *.
        destruct y1 as [|? [|]]; simpl in *; inv H9; inv H3.
        inv H5. inv H7. auto.
  Qed.

  Lemma sem_lexp_step2: forall H b e v s,
      NLSC.sem_exp H b e (v ⋅ s) ->
      NLSC.sem_exp (history_tl H) (Streams.tl b) e s.
  Proof.
    induction e; intros * Hsem; inv Hsem.
    - econstructor; eauto. unfold_St b. inv H4. simpl in *. eauto.
    - econstructor; eauto. unfold_St b. inv H6. simpl in *. eauto.
    - econstructor; eauto using sem_var_step_nl.
    - inv H9; econstructor; eauto using sem_var_step_nl.
    - inv H8; econstructor; eauto using sem_var_step_nl.
    - inv H10; econstructor; eauto using sem_var_step_nl.
  Qed.

  Lemma fby1_reset1_fby : forall bs c v v' xs ys r vs,
      aligned ys bs ->
      xs ≡ (match c with Const c => const bs c | Enum t => enum bs t end) ->
      LiftO (v = sem_const c) (fun v' => v = v') v' ->
      LS.fby1 v' xs ys r vs ->
      vs ≡ NLSC.reset1 (sem_const c) (sfby v ys) r false.
  Proof.
    intros * Haligned Hconst Hv' Hfby.
    eapply ntheq_eqst. intros n. revert n bs v v' xs ys r vs Haligned Hconst Hv' Hfby.
    induction n;
      (intros * Haligned Hconst Hv' Hfby;
       inv Haligned; inv Hfby;
       simpl in Hconst;
       repeat rewrite Str_nth_0_hd; repeat rewrite Str_nth_S_tl; simpl in * ); auto.
    - destruct c; simpl in *; inv Hconst; auto.
    - destruct c; simpl in *; inv Hconst; auto.
    - subst; auto.
    - eapply IHn; eauto; simpl; auto.
      destruct c; simpl in *; inv Hconst; auto.
    - eapply IHn; eauto; simpl; auto.
      destruct c; simpl in *; inv Hconst; auto.
    - eapply IHn; eauto; simpl; auto.
      destruct c; simpl in *; inv Hconst; auto.
    - etransitivity. eapply IHn in H3; eauto; simpl; auto.
      destruct c; simpl in *; inv Hconst; auto.
      apply eqst_ntheq. symmetry. apply NLSC.reset1_fby.
    - destruct v'; eapply IHn; eauto.
      1,2:destruct c; simpl in *; inv Hconst; auto.
  Qed.

  Corollary fby_reset_fby:
    forall b c xs ys r zs,
      b ≡ abstract_clock zs ->
      LS.fby xs ys r zs ->
      xs ≡ (match c with Const c => const b c | Enum t => enum b t end) ->
      zs ≡ NLSC.reset (sem_const c) (sfby (sem_const c) ys) r.
  Proof.
    intros. eapply fby1_reset1_fby; eauto. 2:simpl; auto.
    eapply LS.ac_fby12 in H0. rewrite H, <- H0.
    apply ac_aligned.
  Qed.

  Lemma sem_const_exp {prefs} :
    forall (G: @L.global prefs) H b e c c' xs,
      to_constant e = OK c ->
      LS.sem_exp G H b e [present c' ⋅ xs] ->
      c' = sem_const c.
  Proof.
    induction e using L.exp_ind2; intros * Htoc Hsem;
      inv Htoc; inv Hsem.
    - symmetry in H5. apply const_inv2 in H5. inv H5. tauto.
    - symmetry in H4. inv H4; simpl in *.
      destruct (Streams.hd b); try congruence.
    - cases. inv H0. inv H5.
      inv H10. inv H6. inv H12. inv H7. rewrite app_nil_r in H0.
      subst. inv H6.
      eapply H4; eauto.
  Qed.

  Fact sem_clock_ac : forall H bs bs' ck x ty k xs vs ys,
      sem_var H x vs ->
      sem_clock H bs (Con ck x (ty, k)) bs' ->
      when k xs vs ys ->
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
    destruct Hwhen as [(Hx&Hv&Hy)|[(?&?&Hx&Hv&?&Hy)|(?&Hx&Hv&Hy)]]; rewrite Hv, Hy in *.
    - inv Hck; auto. exfalso.
      eapply IStr.sem_var_instant_det in Hvar; eauto; congruence.
    - inv Hck; auto. exfalso.
      eapply IStr.sem_var_instant_det in Hvar; [|eauto]. inv Hvar.
      congruence.
    - inv Hck; auto. 1,2:exfalso.
      1,2:eapply IStr.sem_var_instant_det in Hvar; [|eauto]; congruence.
  Qed.

  Fact sem_clock_inv : forall H bs ck x ty k xs vs ys,
      sem_var H x vs ->
      sem_clock H bs (Con ck x (ty, k)) (abstract_clock ys) ->
      when k xs vs ys ->
      sem_clock H bs ck (abstract_clock xs).
  Proof.
    intros * Hvar Hck Hwhen.
    rewrite LCS.CIStr.sem_clock_equiv in *.
    apply LCS.CIStr.CIStr.sem_var_impl in Hvar.
    rewrite when_spec in Hwhen.
    intros n. specialize (Hvar n). specialize (Hck n). specialize (Hwhen n).
    rewrite LCS.CIStr.CIStr.tr_Stream_ac in *.
    repeat rewrite LCS.CIStr.CIStr.tr_Stream_nth in *. rewrite LCS.CIStr.CIStr.tr_Stream_nth in Hvar.
    destruct Hwhen as [(Hx&Hv&Hy)|[(?&?&Hx&Hv&?&Hy)|(?&Hx&Hv&Hy)]];
      rewrite Hx, Hv, Hy in *; inv Hck; auto.
    1,2:eapply IStr.sem_var_instant_det in Hvar; eauto; congruence.
  Qed.

  Fact sem_clock_const : forall H ck x s ty k bs bs' bs'' c xs ys,
    sem_var H x s ->
    sem_clock H bs ck bs' ->
    sem_clock H bs (Con ck x (ty, k)) bs'' ->
    when k xs s ys ->
    xs ≡ (match c with Const c => const bs' c | Enum k => enum bs' k end) ->
    ys ≡ (match c with Const c => const bs'' c | Enum k => enum bs'' k end).
  Proof.
    intros * Hvar Hck1 Hck2 Hwhen Hcs.
    apply LCS.CIStr.CIStr.sem_var_impl in Hvar.
    rewrite LCS.CIStr.sem_clock_equiv in *.
    rewrite when_spec in Hwhen.
    apply ntheq_eqst. intros n.
    specialize (Hvar n). specialize (Hck1 n). specialize (Hck2 n). specialize (Hwhen n).
    apply eqst_ntheq with (n:=n) in Hcs.
    repeat rewrite LCS.CIStr.CIStr.tr_Stream_nth in Hck1, Hck2. rewrite LCS.CIStr.CIStr.tr_Stream_nth in Hvar.
    destruct c; try rewrite const_nth' in *; try rewrite enum_nth' in *.
    1,2:destruct Hwhen as [(Hx&Hv&Hy)|[(?&?&Hx&Hv&?&Hy)|(?&Hx&Hv&Hy)]];
      rewrite Hx, Hv, Hy in *; auto; inv Hck2; auto. 1,2,4,5,6,7,9,10:exfalso.
    1-10:eapply IStr.sem_var_instant_det in Hvar; [|eauto]; inv Hvar.
    1-4:congruence.
    1,2:destruct (bs' # n); congruence.
  Qed.

  Lemma to_constant_sem {prefs} :
    forall (G: @L.global prefs) cenv H b e ck b' c cs,
      L.clockof e = [ck] ->
      LC.wc_exp G cenv e ->
      to_constant e = OK c ->
      LS.sem_exp G H b e [cs] ->
      sem_clock H b ck b' ->
      cs ≡ (match c with Const c => const b' c | Enum k => enum b' k end).
  Proof.
    induction e using L.exp_ind2;
      intros * Hck Hwc Hconst Hsem Hsck; simpl in *; inv Hconst.
    - (* constant *) inv Hck.
      inv Hsem. inv Hsck.
      rewrite <- H1. assumption.
    - (* enum *) inv Hck.
      inv Hsem. inv Hsck.
      rewrite <- H1. assumption.
    - (* when *)
      do 2 (destruct es; try congruence).
      apply Forall_singl in H0.
      inv Hwc; simpl in *; rewrite app_nil_r in *.
      apply Forall_singl in H7.
      do 2 (destruct tys; simpl in *; try congruence). inv Hck.
      symmetry in H9. singleton_length.
      apply Forall_singl in H8; inv H8.
      inv Hsem. inv H12; inv H8. simpl in H14; rewrite app_nil_r in H14. inv H14; inv H9.
      assert (b' ≡ abstract_clock cs) as Hac.
      { eapply sem_clock_ac in Hsck; eauto. }
      rewrite Hac in *. eapply sem_clock_inv in H8 as Hck'; eauto. 2:eapply Hsck.
      assert (Hx0:=Hck'). eapply H0 in Hx0; eauto.
      eapply sem_clock_const; eauto. rewrite Hac. eapply Hsck.
  Qed.

  Lemma var_fby_const {prefs} :
    forall (G: @L.global prefs) H b c a env cenv ck x e0 e1 r cs xs ys rs,
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

  Lemma sem_exp_caexp {prefs} :
    forall (G: @L.global prefs) H b env e e' s ck,
      LT.wt_exp G env e ->
      to_cexp e = OK e' ->
      LS.sem_exp G H b e [s] ->
      sem_clock H b ck (abstract_clock s) ->
      NLSC.sem_caexp H b ck e' s.
  Proof.
    cofix Cofix. intros * Hwt Hto Hsem Hsc.
    assert (Hsem':=Hsem). eapply sem_exp_cexp in Hsem'; [|eauto|eauto].
    unfold_Stv s; rewrite unfold_Stream in Hsc; simpl in Hsc;
      econstructor; eauto; eapply Cofix; eauto using sc_step, sem_cexp_step.
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

  Module NCor := CorrectnessFun Ids Op OpAux Cks Str IStr L LCA LT LC Lord LS LCS LN.

  Lemma sc_cexp {prefs} :
    forall (G: @L.global prefs) env H b e vs,
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

  Corollary sc_lexps {prefs} :
    forall (G: @L.global prefs) env H b es vs,
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

  Lemma sem_toeq {prefs} :
    forall cenv out (G: @L.global prefs) H P env envo eq eq' b,
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
    1-5,8-10:(inv Hnormed; inv Hsem; simpl in *; simpl_Foralls;
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
      inversion H4 as [| | | | | ? ? ? ? ? Hwte1 | | | | |]. inv Hwte1.
      inversion Hsef as [| | | | | ??????????? Hse0 Hse1 Hser ? Hwfby | | | | |]; subst.
      inversion_clear H2 as [| | | | | | ????? Hwc0 ?? Hck0 | | | | |]; subst. apply Forall_singl in Hwc0.
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
        as [| | | | | | | | | | |????? bck sub Wce ?? WIi WIo Wcr].
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

  Lemma sem_toeqs' {prefs} :
    forall cenv out (G: @L.global prefs) H P env envo eqs eqs' b,
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

  Lemma sem_toeqs {prefs} :
    forall enms (n : @L.node prefs) nds H P env envo eqs' ins,
      LN.NormFby.normalized_node (L.Global enms nds) n ->
      Forall (LT.wt_equation (L.Global enms nds) (idty (L.n_in n ++ L.n_vars n ++ L.n_out n))) (L.n_eqs n) ->
      Forall (LC.wc_equation (L.Global enms nds) (idck (L.n_in n ++ L.n_vars n ++ L.n_out n))) (L.n_eqs n) ->
      LCA.node_causal n ->
      Lord.Ordered_nodes (L.Global enms nds) ->
      LT.wt_global (L.Global enms nds) ->
      LC.wc_global (L.Global enms nds) ->
      LCS.sc_nodes (L.Global enms nds) ->
      envs_eq env (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)) ->
      (forall f xs ys,
          LS.sem_node (L.Global enms nds) f xs ys ->
          LCS.sem_clock_inputs (L.Global enms nds) f xs ->
          NLSC.sem_node P f xs ys) ->
      LC.wc_node (L.Global enms nds) n ->
      Forall2 (sem_var H) (L.idents (L.n_in n)) ins ->
      LCS.sem_clock_inputs (L.Global enms (n::nds)) (L.n_name n) ins ->
      mmap (to_equation env envo) (L.n_eqs n) = OK eqs' ->
      Forall (LS.sem_equation (L.Global enms nds) H (clocks_of ins)) (L.n_eqs n) ->
      Forall (NLSC.sem_equation P H (clocks_of ins)) eqs'.
  Proof.
    intros * Hnormed Hwt Hwc Hcaus Hord Hwcg Hwtg Hscn Henvs Hnode Hwcn Hins Hscin Hmmap Hsem.

    assert (LCS.sc_var_inv' (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)) H (clocks_of ins)) as Hinv.
    { eapply LCS.sc_node_sc_var_inv'; eauto.
      + destruct Hscin as (?&?&?&?&?).
        simpl in H0. rewrite L.find_node_now in H0; eauto; inv H0.
        eapply LCS.sem_clocks_det'; eauto. destruct Hwcn as (?&_); auto.
      + eapply Forall_impl_In; [|eauto]. intros.
        eapply NCor.normalized_equation_sem_sem_anon; eauto. 1,2:eapply Forall_forall; eauto.
    }

    eapply sem_toeqs' in Hmmap; eauto.
    eapply fst_NoDupMembers, L.node_NoDup.
  Qed.

  Lemma inputs_clocked_vars {prefs} :
    forall enms (n: @L.node prefs) nds H f ins,
      LCS.sem_clock_inputs (L.Global enms (n::nds)) f ins ->
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

  Module Import TrOrdered := TrOrderedFun Ids Op OpAux Cks L Lord CE NL Ord TR.

  Theorem sem_l_nl :
    forall G P f ins outs,
      LN.NormFby.normalized_global G ->
      Lord.Ordered_nodes G ->
      Forall LCA.node_causal G.(L.nodes) ->
      LT.wt_global G ->
      LC.wc_global G ->
      to_global G = OK P ->
      LS.sem_node G f ins outs ->
      LCS.sem_clock_inputs G f ins ->
      NLSC.sem_node P f ins outs.
  Proof.
    intros (enms&nds).
    induction nds as [|nd]. now inversion 7.
    intros * Hnormed Hord Hcaus Hwt Hwc Htr Hsem Hscin.
    destruct Hwt as (Hbool&Hwt).
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [? ? ? ? ? ? Hfind Hins Houts Heqs Hbk].
    pose proof (Lord.find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    inversion_clear Hnormed as [|?? (?&?)].
    inversion_clear Hwt as [|?? (?&?)].
    inversion_clear Hwc as [|?? (?&?)]. inv Hcaus.
    assert (LCS.sc_nodes (L.Global enms nds)) as Hsc.
    { inv Hord. eapply LCS.l_sem_node_clock; eauto. }
    simpl in Hfind. destruct (ident_eq_dec (L.n_name nd) f); subst.
    - rewrite L.find_node_now in Hfind; eauto. inv Hfind.
      assert (Hord':=Hord).
      inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn].
      eapply LS.Forall_sem_equation_global_tl in Heqs; eauto.
      assert (Htr':=Htr). monadInv Htr'. monadInv EQ.
      assert (forall f ins outs,
                 LS.sem_node (L.Global enms nds) f ins outs ->
                 LCS.sem_clock_inputs (L.Global enms nds) f ins ->
                 NLSC.sem_node (NL.Global enms x4) f ins outs) as IHnds'.
      { intros. eapply IHnds; eauto. constructor; auto.
        unfold to_global; simpl. rewrite EQ; auto. }
      take (LT.wt_node _ _) and inversion it as (Hwt1 & Hwt2 & Hwt3 & Hwt4 & Hwt5).
      take (LC.wc_node _ _) and inversion it as (Hwc1 & Hwc2 & Hwc3 & Hwc4).
      econstructor; simpl.
      + erewrite NL.find_node_now; eauto. erewrite <- to_node_name; eauto.
      + erewrite <- to_node_in; eauto.
      + erewrite <- to_node_out; eauto.
      + erewrite <- to_node_in; eauto.
        eapply inputs_clocked_vars; eauto.
      + apply NLSC.sem_equation_cons2; auto.
        * eapply ord_l_nl; eauto.
        * assert (Hton := EQ0). tonodeInv EQ0; simpl in *.
          eapply sem_toeqs; eauto. constructor; auto.
          apply envs_eq_node.
        * assert (Htrn' := EQ0).
          apply to_node_name in EQ0. rewrite <- EQ0.
          eapply ninin_l_nl; eauto.
    - eapply LS.sem_node_cons in Hsem; auto.
      eapply LCS.sem_clock_inputs_cons in Hscin; auto.
      assert (Htr' := Htr).
      monadInv Htr. monadInv EQ.
      rewrite cons_is_app in Hord.
      assert (Lord.Ordered_nodes {| L.enums := enms; L.nodes := nds |}) as Hord'.
      { eapply Lord.Ordered_nodes_append in Hord; eauto.
        econstructor; simpl; eauto. 2:rewrite cons_is_app; auto.
        intros ?; simpl; auto. }
      eapply NLSC.sem_node_cons2; eauto.
      + eapply ord_l_nl with (G:=L.Global enms nds); auto.
        unfold to_global; simpl; rewrite EQ; simpl; auto.
      + eapply IHnds; eauto. constructor; auto.
        unfold to_global; simpl; rewrite EQ; simpl; auto.
      + replace x4 with (NL.Global enms x4).(NL.nodes) by auto.
        eapply TR.to_global_names with (G:=L.Global enms nds); simpl; eauto.
        erewrite <-to_node_name; eauto.
        unfold to_global; simpl; rewrite EQ; simpl; auto.
  Qed.

End CORRECTNESS.

Module CorrectnessFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (OpAux: OPERATORS_AUX    Ids Op)
       (Cks  : CLOCKS           Ids Op OpAux)
       (L    : LSYNTAX          Ids Op OpAux Cks)
       (CE   : CESYNTAX         Ids Op OpAux Cks)
       (NL   : NLSYNTAX         Ids Op OpAux Cks        CE)
       (TR   : TR               Ids Op OpAux Cks L      CE NL)
       (LT   : LTYPING          Ids Op OpAux Cks L)
       (LC   : LCLOCKING        Ids Op OpAux Cks L)
       (LCA  : LCAUSALITY       Ids Op OpAux Cks L)
       (Ord  : NLORDERED        Ids Op OpAux Cks        CE NL)
       (Lord : LORDERED         Ids Op OpAux Cks L)
       (Str  : COINDSTREAMS     Ids Op OpAux Cks)
       (IStr : INDEXEDSTREAMS   Ids Op OpAux Cks)
       (LS   : LSEMANTICS       Ids Op OpAux Cks L Lord       Str)
       (LCS  : LCLOCKSEMANTICS  Ids Op OpAux Cks L LC LCA Lord Str IStr LS)
       (LN   : NORMALIZATION    Ids Op OpAux Cks L    LCA)
       (NLSC : NLCOINDSEMANTICS Ids Op OpAux Cks        CE NL Str Ord)
<: CORRECTNESS Ids Op OpAux Cks L CE NL TR LT LC LCA Ord Lord Str IStr LS LCS LN NLSC.
  Include CORRECTNESS Ids Op OpAux Cks L CE NL TR LT LC LCA Ord Lord Str IStr LS LCS LN NLSC.
End CorrectnessFun.
