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
From Velus Require Import CoindToIndexed IndexedToCoind CoindIndexed.

From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import CoreExpr.CEInterpreter.
From Velus Require Import NLustre.NLIndexedSemantics.
From Velus Require Import NLCoindToIndexed NLIndexedToCoind.

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

(** Used in lemma count_ex_dec *)
From Coq Require Import Classical_Prop.

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
       (LS          : LSEMANTICS       Ids Op OpAux Cks L Lord       Str)
       (Import LCS  : LCLOCKSEMANTICS  Ids Op OpAux Cks L LC LCA Lord Str LS)
       (LN          : NORMALIZATION    Ids Op OpAux Cks L)
       (NLSC        : NLCOINDSEMANTICS Ids Op OpAux Cks        CE NL Str Ord).

  Lemma sem_lexp_step {PSyn prefs} :
    forall (G: @L.global PSyn prefs) H b e e' s,
      to_lexp e = OK e' ->
      LS.sem_exp G H b e s ->
      LS.sem_exp G (history_tl H) (Streams.tl b) e (map (@Streams.tl _) s).
  Proof.
    einduction e using L.exp_ind2; intros * Htr Hsem; inv Htr.
    - inv Hsem; inv H4.
      simpl in *. constructor; auto.
    - inv Hsem; simpl. inv H6.
      simpl in *. constructor; auto.
    - inv Hsem. destruct a. monadInv H1. inv H7; destruct xs'.
      econstructor. econstructor.
      eapply env_maps_tl; eauto. inv H2; simpl in *. assumption.
    - inv Hsem. destruct a. monadInv H1. destruct s0.
      eapply IHe0 in H7; eauto; simpl in *.
      econstructor; eauto. inv H10; auto.
    - inv Hsem. destruct a. monadInv H1. destruct s1, s2.
      eapply IHe0_1 in H6; eauto. eapply IHe0_2 in H9; eauto.
      econstructor; eauto. inv H13; auto.
    - cases; monadInv H2.
      apply Forall_singl in H0.
      inv Hsem. inv H9; inv H5.
      simpl in *; rewrite app_nil_r in *.
      eapply H0 in H3; eauto.
      destruct s0.
      econstructor.
      + econstructor; eauto.
      + eapply sem_var_step. eassumption.
      + simpl; rewrite app_nil_r.
        rewrite Forall2_map_1, Forall2_map_2.
        eapply Forall2_impl_In; [|eauto]; intros ?? _ _ ?.
        inv H1; eauto.
  Qed.

  Lemma sem_cexp_step {PSyn prefs} :
    forall (G: @L.global PSyn prefs) H b e e' s,
      to_cexp e = OK e' ->
      LS.sem_exp G H b e s ->
      LS.sem_exp G (history_tl H) (Streams.tl b) e (map (@Streams.tl _) s).
  Proof.
    einduction e using L.exp_ind2; intros * Htr Hsem;
      (now inv Htr) || (unfold to_cexp in Htr;
                       try (monadInv Htr; eapply sem_lexp_step; simpl; eauto)).
    - (* merge *)
      destruct a as ([|? [|]]&?&?); monadInv Htr; fold to_cexp in *.
      inv Hsem. destruct s0.
      eapply LS.Smerge with (vs0:=map (map (map (fun x => Streams.tl x))) vs); eauto.
      + eapply sem_var_step; eauto.
      + clear - EQ H0 H9. rewrite Forall2_map_2.
        revert dependent vs. revert dependent x0.
        induction es; intros; inv H9; inv H0;
          simpl in *; monadInv EQ;
          constructor; eauto.
        clear EQ IHes H6.
        cases. apply Forall_singl in H4. inv H3; inv H7. simpl.
        repeat constructor; eauto.
      + rewrite map_map.
        replace (map (fun x => concat (map (map (fun x2 => Streams.tl x2)) x)) vs)
          with (map (map (@Streams.tl _)) (map (@concat _) vs)).
        2:{ rewrite map_map. eapply map_ext; intros.
            rewrite concat_map; auto. }
        rewrite Forall2Transpose_map_1, Forall2Transpose_map_2.
        eapply Forall2Transpose_impl; eauto.
        intros ?? Hmerge. inv Hmerge; eauto.
    - (* case *)
      destruct a as ([|? [|]]&?&?); cases; monadInv Htr; fold to_cexp in *.
      inv Hsem. destruct s0.
      eapply LS.Scase with (vs0:=map (map (map (fun x => Streams.tl x))) vs)
                           (vd0:=(map (map (fun x => Streams.tl x)) vd)); eauto.
      + eapply sem_lexp_step in H7; eauto.
      + clear - EQ1 H0 H10. rewrite Forall2_map_2.
        revert dependent vs. revert dependent x0.
        induction es; intros; inv H0; inv H10;
          simpl in *; monadInv EQ1;
          constructor; eauto.
        clear EQ1 IHes H4 H6.
        cases; monadInv EQ; intros ? Heq; inv Heq.
        apply Forall_singl in H3. specialize (H2 _ eq_refl).
        inv H2; inv H6. simpl. repeat constructor; eauto.
      + clear - H12. rewrite Forall2_map_2.
        eapply Forall2_impl_In; [|eauto]; intros ?? _ _ ? ?; subst.
        rewrite Forall2_map_1, Forall2_map_2.
        eapply Forall2_impl_In; [|eauto]; intros.
        eapply map_st_EqSt; eauto.
        intros ?? Heq. rewrite Heq. reflexivity.
      + clear - H1 H13 EQ0. inv H13; inv H5.
        simpl. repeat constructor.
        apply Forall_singl in H1; eauto.
      + rewrite map_map.
        replace (map (fun x => concat (map (map (fun x2 => Streams.tl x2)) x)) vs)
          with (map (map (@Streams.tl _)) (map (@concat _) vs)).
        2:{ rewrite map_map. eapply map_ext; intros.
            rewrite concat_map; auto. }
        rewrite Forall2Transpose_map_1, Forall2Transpose_map_2.
        eapply Forall2Transpose_impl; eauto.
        intros ?? Hcase. inv Hcase; eauto.
  Qed.

  Lemma ty_lexp {PSyn prefs} :
    forall (G: @L.global PSyn prefs) env e e',
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
    - cases. inv H. simpl. inv Hwt. inv H10. inv H5. simpl in *. monadInv H1.
      unfold L.typesof. unfold flat_map. simpl. rewrite app_nil_r in H11.
      eapply H3 in H2; eauto. congruence.
  Qed.

  Lemma sem_exp_lexp {PSyn prefs} :
    forall (G : @L.global PSyn prefs) env H b e e' s,
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

  Lemma sem_lexp_single {PSyn prefs} :
    forall e e' G H b ss,
      to_lexp e = OK e' ->
      LS.sem_exp (G: @L.global PSyn prefs) H b e ss ->
      exists s, ss = [s].
  Proof.
    induction e using L.exp_ind2; intros * Htr Hsem; inv Htr;
      try (inv Hsem; eexists; now eauto).
    cases_eqn H2. subst. monadInv H2. inv Hsem. inv H9. inv H5. inv H. inv H5.
    eapply H4 in EQ; [|eauto]. inv EQ. simpl in H11. inv H11. inv H6.
    eauto.
  Qed.

  Lemma sem_exps_lexps {PSyn prefs} :
    forall (G: @L.global PSyn prefs) H b tenv es les ss,
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

  Lemma sem_exp_cexp {PSyn prefs} :
    forall (G: @L.global PSyn prefs) env H b e e' s,
      LT.wt_exp G env e ->
      to_cexp e = OK e' ->
      LS.sem_exp G H b e [s] ->
      NLSC.sem_cexp H b e' s.
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr Hsem;
      (now inv Htr) || (unfold to_cexp in Htr;
                       try (monadInv Htr; econstructor;
                            eapply sem_exp_lexp; eauto));
      cases; monadInv Htr; fold to_cexp in *.
    - (* merge *)
      inv Hsem; inv H10; inv H6.
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
    - (* case *)
      inv Hsem. apply Forall_singl in H1.
      inv H13; inv H6. inv H14; inv H9.
      rewrite Forall2_map_1 in H5. rewrite map_map, Forall_map in H2.
      inv Hwt.
      econstructor; eauto.
      + eapply sem_exp_lexp in EQ; eauto.
      + apply Forall_singl in H21. rename H21 into Hwtd.
        rename H1 into Hd. rename H4 into Hsemd.
        clear - H0 Hd Hwtd Hsemd H2 H5 H10 H12 H19 EQ0 EQ1.
        revert vs hd1 x0 H0 H2 H5 H10 H12 H19 EQ1.
        induction es; intros; inv H0; simpl in *; monadInv EQ1;
          inv H10; inv H12; inv H5; inv H2; constructor; eauto.
        clear EQ1 IHes H6 H8 H10.
        cases; monadInv EQ; simpl in *.
        * apply Forall_singl in H4; eauto.
          specialize (H3 _ eq_refl). inv H3; inv H8; simpl in *; rewrite app_nil_r in *; auto.
          destruct y2 as [|? [|]]; inv H7; inv H5.
          eapply H4 in H2; eauto.
          eapply Forall_forall in H19; eauto with datatypes.
        * eapply Hd; eauto.
          specialize (H9 eq_refl). inv H9; inv H8.
          simpl in *; rewrite app_nil_r in *.
          destruct x as [|? [|]]; simpl in *; inv H7; inv H5.
          inv H6; inv H7. rewrite H2; auto.
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

  Module NCor := CorrectnessFun Ids Op OpAux Cks Str L LCA LT LC Lord LS LCS LN.

  Lemma reset_or_not_reset : forall n r,
      (forall m, m <= n -> r # m = false) \/
      (exists m, m <= n /\ r # m = true).
  Proof.
    induction n; intros *; unfold_Stv r.
    - right. exists 0; auto.
    - left. intros ? Hle. inv Hle; auto.
    - right. exists 0; auto using Nat.le_0_l.
    - destruct (IHn r) as [Hle|(m&Hle&Htrue)].
      + left. intros [|] ?; auto.
        rewrite Str_nth_S_tl; simpl; auto.
        apply Hle; lia.
      + right. exists (S m). split; auto; lia.
  Qed.

  Lemma fby1_reset1_fby:
    forall n r x0 v0 x y,
      (forall m, m <= n -> r # m = false) ->
      LS.fby1 v0 (NCor.const_val (abstract_clock (maskv 0 r x)) x0) (maskv 0 r x) (maskv 0 r y) ->
      y # n = (NLSC.reset1 x0 (sfby v0 x) r false) # n.
  Proof.
    induction n;
      intros * Hle Hfby; unfold_Stv r; unfold_Stv x; destruct y;
        repeat rewrite Str_nth_0_hd; repeat rewrite Str_nth_S_tl; simpl in *.
    - exfalso. specialize (Hle 0 (Nat.le_0_l _)).
      rewrite Str_nth_0_hd in Hle; simpl in Hle; congruence.
    - exfalso. specialize (Hle 0 (Nat.le_0_l _)).
      rewrite Str_nth_0_hd in Hle; simpl in Hle; congruence.
    - rewrite 2 maskv_Cons, ac_Cons, NCor.const_val_Cons in Hfby. inv Hfby; auto.
    - rewrite 2 maskv_Cons, ac_Cons, NCor.const_val_Cons in Hfby. inv Hfby; auto.
    - exfalso. specialize (Hle 0 (Nat.le_0_l _)).
      rewrite Str_nth_0_hd in Hle; simpl in Hle; congruence.
    - exfalso. specialize (Hle 0 (Nat.le_0_l _)).
      rewrite Str_nth_0_hd in Hle; simpl in Hle; congruence.
    - rewrite 2 maskv_Cons, ac_Cons, NCor.const_val_Cons in Hfby. inv Hfby; auto.
      eapply IHn in H3; eauto.
      intros ? Hle'. specialize (Hle (S m)). rewrite Str_nth_S_tl in Hle. eapply Hle; lia.
    - rewrite 2 maskv_Cons, ac_Cons, NCor.const_val_Cons in Hfby. inv Hfby; auto.
      eapply IHn in H1; eauto.
      intros ? Hle'. specialize (Hle (S m)). rewrite Str_nth_S_tl in Hle. eapply Hle; lia.
  Qed.

  Lemma reset1_fby_reset : forall n v0 v xs rs,
      (exists m, m <= n /\ rs # m = true) ->
      (NLSC.reset1 v0 (sfby v xs) rs false) # n = (NLSC.reset1 v0 (sfby v0 xs) rs false) # n.
  Proof.
    induction n; intros * Hle;
      unfold_Stv rs; unfold_Stv xs;
        repeat rewrite Str_nth_0_hd; repeat rewrite Str_nth_S_tl; simpl; auto.
    - exfalso.
      destruct Hle as (?&Hle&Hr). inv Hle.
      rewrite Str_nth_0_hd in Hr; simpl in Hr. congruence.
    - repeat rewrite NLSC.reset1_fby.
      reflexivity.
    - eapply IHn.
      destruct Hle as (?&Hle&Hr). destruct x.
      + rewrite Str_nth_0_hd in Hr; simpl in Hr. congruence.
      + rewrite Str_nth_S_tl in Hr; simpl in Hr.
        eexists; split; [|eauto]. lia.
  Qed.

  Corollary fby_reset_fby:
    forall r x0 x y,
      (forall k, LS.fby (NCor.const_val (abstract_clock (maskv k r x)) x0) (maskv k r x) (maskv k r y)) ->
      y ≡ NLSC.reset x0 (sfby x0 x) r.
  Proof.
    intros * Hfby.
    eapply ntheq_eqst. intros n.
    assert (forall k, (count r) # n <= k ->
                 LS.fby (NCor.const_val (abstract_clock (maskv k r x)) x0) (maskv k r x) (maskv k r y)) as Hfby'.
    { intros; auto. } clear Hfby. rename Hfby' into Hfby.

    revert x0 x y r Hfby.
    induction n;
      intros; unfold_Stv r; unfold_Stv x; destruct y;
        repeat rewrite Str_nth_0_hd; repeat rewrite Str_nth_S_tl; simpl in *.
    - specialize (Hfby 1). rewrite 2 maskv_Cons, ac_Cons, NCor.const_val_Cons in Hfby.
      rewrite Str_nth_0_hd in Hfby; simpl in Hfby; specialize (Hfby (Nat.le_refl _)).
      inv Hfby; auto.
    - specialize (Hfby 1). rewrite 2 maskv_Cons, ac_Cons, NCor.const_val_Cons in Hfby.
      rewrite Str_nth_0_hd in Hfby; simpl in Hfby; specialize (Hfby (Nat.le_refl _)).
      inv Hfby; auto.
    - specialize (Hfby 0). rewrite 2 maskv_Cons, ac_Cons, NCor.const_val_Cons in Hfby.
      rewrite Str_nth_0_hd in Hfby; simpl in Hfby; specialize (Hfby (Nat.le_refl _)).
      inv Hfby; auto.
    - specialize (Hfby 0). rewrite 2 maskv_Cons, ac_Cons, NCor.const_val_Cons in Hfby.
      rewrite Str_nth_0_hd in Hfby; simpl in Hfby; specialize (Hfby (Nat.le_refl _)).
      inv Hfby; auto.
    - rewrite NLSC.reset1_fby.
      eapply IHn; auto. intros k Hc.
      specialize (Hfby (S k)).
      rewrite Str_nth_S_tl in Hfby; simpl in Hfby. setoid_rewrite count_S_nth' in Hfby.
      specialize (Hfby (le_n_S _ _ Hc)).
      destruct k; rewrite 2 maskv_Cons, ac_Cons, NCor.const_val_Cons in Hfby; inv Hfby; eauto.
    - (* 2 possibilities :
         + there is no reset before n, in which case the sequence behaves as fby1 until n
         + there is a reset before n, in which case we can use the induction hypothesis
       *)
      destruct (reset_or_not_reset n r).
      + specialize (Hfby 1). rewrite 2 maskv_Cons, ac_Cons, NCor.const_val_Cons in Hfby.
        rewrite Str_nth_S_tl in Hfby; simpl in Hfby. setoid_rewrite count_S_nth' in Hfby.
        rewrite (proj1 (count_0 _ _)) in Hfby; auto. specialize (Hfby (Nat.le_refl _)).
        inv Hfby.
        eapply fby1_reset1_fby; eauto.
      + rewrite reset1_fby_reset; auto.
        eapply IHn; eauto. intros k Hle.
        assert (k > 0) as Hgt by (eapply count_not_0 in H; lia).
        specialize (Hfby (S k)).
        rewrite Str_nth_S_tl, 2 maskv_Cons in Hfby; simpl in Hfby. setoid_rewrite count_S_nth' in Hfby.
        specialize (Hfby (le_n_S _ _ Hle)).
        destruct k; rewrite ac_Cons, NCor.const_val_Cons in Hfby; inv Hfby; eauto.
        inv Hgt.
    - eapply IHn; auto. intros [|k] Hle.
      + specialize (Hfby 0). rewrite 2 maskv_Cons, ac_Cons, NCor.const_val_Cons in Hfby.
        rewrite Str_nth_S_tl in Hfby; simpl in Hfby. specialize (Hfby Hle).
        inv Hfby; auto.
      + specialize (Hfby (S k)).
        rewrite Str_nth_S_tl in Hfby; simpl in Hfby. specialize (Hfby Hle).
        destruct k; rewrite 2 maskv_Cons, ac_Cons, NCor.const_val_Cons in Hfby; inv Hfby; auto.
    - destruct (reset_or_not_reset n r).
      + specialize (Hfby 0). rewrite 2 maskv_Cons, ac_Cons, NCor.const_val_Cons in Hfby.
        rewrite Str_nth_S_tl in Hfby; simpl in Hfby.
        rewrite (proj1 (count_0 _ _)) in Hfby; auto. specialize (Hfby (Nat.le_refl _)).
        inv Hfby.
        eapply fby1_reset1_fby; eauto.
      + rewrite reset1_fby_reset; auto.
        eapply IHn; eauto. intros k Hle.
        assert (k > 0) as Hgt by (eapply count_not_0 in H; lia).
        specialize (Hfby k).
        rewrite Str_nth_S_tl, 2 maskv_Cons in Hfby; simpl in Hfby. specialize (Hfby Hle).
        destruct k as [|[|]]; rewrite ac_Cons, NCor.const_val_Cons in Hfby; inv Hfby; eauto.
        inv Hgt.
  Qed.

  Lemma sem_const_exp {PSyn prefs} :
    forall (G: @L.global PSyn prefs) H b e c c' xs,
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
    xs ≡ (NCor.const_val bs' c) ->
    ys ≡ (NCor.const_val bs'' c).
  Proof.
    intros * Hvar Hck1 Hck2 Hwhen Hcs.
    apply LCS.CIStr.CIStr.sem_var_impl in Hvar.
    rewrite LCS.CIStr.sem_clock_equiv in *.
    rewrite when_spec in Hwhen.
    apply ntheq_eqst. intros n.
    specialize (Hvar n). specialize (Hck1 n). specialize (Hck2 n). specialize (Hwhen n).
    apply eqst_ntheq with (n:=n) in Hcs.
    repeat rewrite LCS.CIStr.CIStr.tr_Stream_nth in Hck1, Hck2. rewrite LCS.CIStr.CIStr.tr_Stream_nth in Hvar.
    rewrite NCor.const_val_nth in *.
    destruct Hwhen as [(Hx&Hv&Hy)|[(?&?&Hx&Hv&?&Hy)|(?&Hx&Hv&Hy)]];
      rewrite Hx, Hv, Hy in *; auto; inv Hck2; auto. 1,2,4,5:exfalso.
    1-5:eapply IStr.sem_var_instant_det in Hvar; [|eauto]; inv Hvar.
    1-2:congruence.
    1:destruct (bs' # n); congruence.
  Qed.

  Lemma to_constant_sem {PSyn prefs} :
    forall (G: @L.global PSyn prefs) cenv H b e ck b' c cs,
      L.clockof e = [ck] ->
      LC.wc_exp G cenv e ->
      to_constant e = OK c ->
      LS.sem_exp G H b e [cs] ->
      sem_clock H b ck b' ->
      cs ≡ (NCor.const_val b' (sem_const c)).
  Proof.
    induction e using L.exp_ind2;
      intros * Hck Hwc Hconst Hsem Hsck; simpl in *; inv Hconst.
    - (* constant *) inv Hck.
      inv Hsem. inv Hsck. simpl.
      rewrite <-NCor.const_val_const, <-H1; auto.
    - (* enum *) inv Hck.
      inv Hsem. inv Hsck. simpl.
      rewrite <-NCor.const_val_enum, <-H1; auto.
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
      eapply sem_clock_const; eauto. eapply Hsck.
  Qed.

  Lemma sem_exp_caexp {PSyn prefs} :
    forall (G: @L.global PSyn prefs) H b env e e' s ck,
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
    - eapply sem_cexp_step in Hsem; eauto.
    - eapply sem_cexp_step in Hsem; eauto.
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

  Module CES := CESemanticsFun Ids Op OpAux Cks CE IStr.
  Module CEI := CEInterpreterFun Ids Op OpAux Cks CE IStr CES.
  Module ICStr := IndexedToCoindFun Ids Op OpAux Cks IStr Str.
  Module CIStr' := CoindToIndexedFun Ids Op OpAux Cks Str IStr.
  Module Import ConvStr := CoindIndexedFun Ids Op OpAux Cks Str IStr.
  Module NLSI := NLIndexedSemanticsFun Ids Op OpAux Cks CE NL IStr Ord CES.
  Module NICStr := NLIndexedToCoindFun Ids Op OpAux Cks CE NL IStr Str ICStr Ord CES NLSI CEI NLSC.
  Module NCIStr := NLCoindToIndexedFun Ids Op OpAux Cks CE NL IStr Str CIStr' Ord CES NLSI NLSC.

  Lemma Forall2_forall' {A B} : forall (P : nat -> A -> B -> Prop) xs ys,
    (forall k, Forall2 (P k) xs ys) <-> Forall2 (fun x y => forall k, (P k x y)) xs ys.
  Proof.
    split; intros * Hf.
    - revert ys Hf. induction xs; intros.
      + specialize (Hf 0); inv Hf; auto.
      + destruct ys.
        * specialize (Hf 0). inv Hf; auto.
        * constructor. 2:apply IHxs.
          1,2:intros k; specialize (Hf k); inv Hf; auto.
    - intros k. induction Hf; auto.
  Qed.

  Lemma Forall_Forall2 {A B} : forall (P : A -> B -> Prop) xs,
      Forall (fun x => exists y, P x y) xs ->
      exists ys, Forall2 P xs ys.
  Proof.
    intros * Hf. induction Hf; eauto.
    destruct H as (?&?). destruct IHHf as (?&?).
    eauto.
  Qed.

  Lemma sem_lexp_mask: forall r H b e v,
      (forall k, NLSC.sem_exp (mask_hist k r H) (maskb k r b) e (maskv k r v)) ->
      NLSC.sem_exp H b e v.
  Proof.
    intros * Hsem.
    rewrite <-tr_stream_eqst, <-(tr_stream_eqst v), <-tr_history_equiv.
    eapply NICStr.sem_exp_impl. intros n.
    specialize (Hsem ((count r) # n)).
    eapply NCIStr.sem_exp_impl in Hsem. specialize (Hsem n); simpl in Hsem.
    unfold CIStr'.tr_Stream in Hsem.
    rewrite maskv_nth, maskb_nth, Nat.eqb_refl in Hsem.
    rewrite <-LCS.history_mask_count; eauto.
  Qed.

  Corollary sem_lexps_mask: forall r H b es vs,
      (forall k, Forall2 (fun e v => NLSC.sem_exp (mask_hist k r H) (maskb k r b) e (maskv k r v)) es vs) ->
      Forall2 (NLSC.sem_exp H b) es vs.
  Proof.
    intros * Hf.
    eapply Forall2_forall' in Hf. eapply Forall2_impl_In; [|eauto]; intros.
    eapply sem_lexp_mask; eauto.
  Qed.

  Lemma sem_cexp_mask: forall r H b e v,
      (forall k, NLSC.sem_cexp (mask_hist k r H) (maskb k r b) e (maskv k r v)) ->
      NLSC.sem_cexp H b e v.
  Proof.
    intros * Hsem.
    rewrite <-tr_stream_eqst, <-(tr_stream_eqst v), <-tr_history_equiv.
    eapply NICStr.sem_cexp_impl. intros n.
    specialize (Hsem ((count r) # n)).
    eapply NCIStr.sem_cexp_impl in Hsem. specialize (Hsem n); simpl in Hsem.
    unfold CIStr'.tr_Stream in Hsem.
    rewrite maskv_nth, maskb_nth, Nat.eqb_refl in Hsem.
    rewrite <-LCS.history_mask_count; eauto.
  Qed.

  Lemma sem_aexp_mask: forall r H b ck e v,
      (forall k, NLSC.sem_aexp (mask_hist k r H) (maskb k r b) ck e (maskv k r v)) ->
      NLSC.sem_aexp H b ck e v.
  Proof.
    intros * Hsem.
    rewrite <-tr_stream_eqst, <-(tr_stream_eqst v), <-tr_history_equiv.
    eapply NICStr.sem_aexp_impl. intros n.
    specialize (Hsem ((count r) # n)).
    eapply NCIStr.sem_aexp_impl in Hsem. specialize (Hsem n); simpl in Hsem.
    unfold CIStr'.tr_Stream in Hsem.
    rewrite maskv_nth, maskb_nth, Nat.eqb_refl in Hsem.
    rewrite <-LCS.history_mask_count; eauto.
  Qed.

  Lemma sem_caexp_mask: forall r H b ck e v,
      (forall k, NLSC.sem_caexp (mask_hist k r H) (maskb k r b) ck e (maskv k r v)) ->
      NLSC.sem_caexp H b ck e v.
  Proof.
    intros * Hsem.
    rewrite <-tr_stream_eqst, <-(tr_stream_eqst v), <-tr_history_equiv.
    eapply NICStr.sem_caexp_impl. intros n.
    specialize (Hsem ((count r) # n)).
    eapply NCIStr.sem_caexp_impl in Hsem. specialize (Hsem n); simpl in Hsem.
    unfold CIStr'.tr_Stream in Hsem.
    rewrite maskv_nth, maskb_nth, Nat.eqb_refl in Hsem.
    rewrite <-LCS.history_mask_count; eauto.
  Qed.

  Lemma sem_toeq_normalized {PSyn prefs} :
    forall (G: @L.global PSyn prefs) P cenv x e ck e' r H b,
      LC.wc_global G ->
      LCS.sc_vars (idck cenv) H b ->
      LN.Unnesting.normalized_cexp e ->
      LT.wt_exp G (idty cenv) e ->
      LC.wc_exp G (idck cenv) e ->
      L.clockof e = [ck] ->
      to_cexp e = OK e' ->
      (forall k, LCS.sem_equation_ck G (mask_hist k r H) (maskb k r b) ([x], [e])) ->
      NLSC.sem_equation P H b (NL.EqDef x ck e').
  Proof.
    intros * HwcG Hinv Hnormed Hwt Hwc Hck Hto Hsem.
    assert (exists v, sem_var H x v) as (v&Hvar).
    { specialize (Hsem 0). inv Hsem. simpl_Foralls.
      simpl in *; rewrite app_nil_r in *; subst.
      eapply sem_var_mask_inv in H3 as (?&?&?); eauto. }
    econstructor; eauto. eapply sem_caexp_mask with (r:=r).
    intros k. specialize (Hsem k). inv Hsem. simpl_Foralls.
    simpl in *; rewrite app_nil_r in *; subst.
    eapply sem_var_mask_inv in H3 as (?&Hvar'&Heq).
    eapply sem_var_det in Hvar; eauto. rewrite Heq, Hvar in H6.
    eapply sem_exp_caexp; eauto using LCS.sem_exp_ck_sem_exp.
    eapply LCS.sc_exp in H6; eauto.
    2:eapply LCS.sc_vars_mask; eauto.
    rewrite Hck in H6. simpl in H6. inv H6; auto.
  Qed.

  Lemma sem_lexp_mask_inv: forall r k H b e v,
      NLSC.sem_exp (mask_hist k r H) (maskb k r b) e v ->
      exists v', v ≡ maskv k r v'.
  Proof.
    induction e; intros * Hsem; inv Hsem.
    - (* const *) exists (const b c).
      rewrite H4. eapply ntheq_eqst. intros n.
      rewrite maskv_nth, 2 const_nth', maskb_nth.
      destruct (_ =? _); simpl; auto.
    - (* enum *) exists (enum b e).
      rewrite H6. eapply ntheq_eqst. intros n.
      rewrite maskv_nth, 2 enum_nth', maskb_nth.
      destruct (_ =? _); simpl; auto.
    - (* var *)
      eapply sem_var_mask_inv in H6 as (?&?&?); eauto.
    - (* when *)
      eapply IHe in H6 as (?&Heq). rewrite Heq in H9.
      exists v. eapply ntheq_eqst. intros n. rewrite maskv_nth.
      eapply when_spec with (n:=n) in H9 as [(Hmask&?&Hv)|[(?&?&Hmask&?&?&Hv)|(?&Hmask&?&Hv)]].
      + rewrite Hv. destruct (_ =? _); auto.
      + rewrite Hv. destruct (_ =? _); auto.
      + rewrite Hv. rewrite maskv_nth in Hmask.
        destruct (_ =? _); auto.
    - (* unop *)
      eapply IHe in H7 as (?&Heq). rewrite Heq in H8.
      exists v. eapply ntheq_eqst. intros n. rewrite maskv_nth.
      eapply lift1_spec with (n:=n) in H8 as [(?&Hv)|(?&?&Hmask&?&Hv)].
      + rewrite Hv. destruct (_ =? _); auto.
      + rewrite Hv. rewrite maskv_nth in Hmask.
        destruct (_ =? _); auto. congruence.
    - (* binop *)
      eapply IHe1 in H8 as (?&Heq1). rewrite Heq1 in H10.
      eapply IHe2 in H9 as (?&Heq2). rewrite Heq2 in H10.
      exists v. eapply ntheq_eqst. intros n. rewrite maskv_nth.
      eapply lift2_spec with (n:=n) in H10 as [(?&?&Hv)|(?&?&?&Hm1&Hm2&?&Hv)].
      + rewrite Hv. destruct (_ =? _); auto.
      + rewrite Hv. rewrite maskv_nth in Hm1, Hm2.
        destruct (_ =? _); auto. congruence.
  Qed.

  Lemma sem_normalized_lexp_mask_inv {PSyn prefs}: forall (G: @L.global PSyn prefs) r k H b e v,
      LN.Unnesting.normalized_lexp e ->
      LS.sem_exp G (mask_hist k r H) (maskb k r b) e v ->
      exists v', EqSts v [maskv k r v'].
  Proof.
    intros * Hnormed. revert v.
    induction Hnormed; intros * Hsem; inv Hsem.
    - (* const *) exists (const b c).
      rewrite H4. constructor; auto. eapply ntheq_eqst. intros n.
      rewrite maskv_nth, 2 const_nth', maskb_nth.
      destruct (_ =? _); simpl; auto.
    - (* enum *) exists (enum b k0).
      rewrite H6. constructor; auto. eapply ntheq_eqst. intros n.
      rewrite maskv_nth, 2 enum_nth', maskb_nth.
      destruct (_ =? _); simpl; auto.
    - (* var *)
      eapply sem_var_mask_inv in H6 as (?&?&?); eauto.
      do 2 econstructor; eauto.
    - (* unop *)
      eapply IHHnormed in H6 as (?&Heq). apply Forall2_singl in Heq. rewrite Heq in H9.
      do 2 econstructor; eauto.
      eapply ntheq_eqst. intros n. rewrite maskv_nth.
      eapply lift1_spec with (n:=n) in H9 as [(?&Hv)|(?&?&Hmask&?&Hv)].
      + rewrite Hv. destruct (_ =? _); eauto.
      + rewrite Hv. rewrite maskv_nth in Hmask.
        destruct (_ =? _); auto. congruence.
    - (* binop *)
      eapply IHHnormed1 in H5 as (?&Heq1). apply Forall2_singl in Heq1. rewrite Heq1 in H12.
      eapply IHHnormed2 in H8 as (?&Heq2). apply Forall2_singl in Heq2. rewrite Heq2 in H12.
      do 2 econstructor; eauto.
      eapply ntheq_eqst. intros n. rewrite maskv_nth.
      eapply lift2_spec with (n:=n) in H12 as [(?&?&Hv)|(?&?&?&Hm1&Hm2&?&Hv)].
      + rewrite Hv. destruct (_ =? _); eauto.
      + rewrite Hv. rewrite maskv_nth in Hm1, Hm2.
        destruct (_ =? _); auto. congruence.
    - (* when *)
      inv H8; inv H4.
      eapply IHHnormed in H2 as (?&Heq). inv Heq; inv H4.
      simpl in H10. inv H10; inv H5.
      rewrite H3 in H2.
      do 2 econstructor; eauto.
      eapply ntheq_eqst. intros n. rewrite maskv_nth.
      eapply when_spec with (n:=n) in H2 as [(Hmask&?&Hv)|[(?&?&Hmask&?&?&Hv)|(?&Hmask&?&Hv)]].
      + rewrite Hv. destruct (_ =? _); eauto.
      + rewrite Hv. destruct (_ =? _); auto.
      + rewrite Hv. rewrite maskv_nth in Hmask.
        destruct (_ =? _); auto.
  Qed.

  Corollary sem_laexp_mask_inv: forall r k H b e ck v,
      NLSC.sem_aexp (mask_hist k r H) (maskb k r b) ck e v ->
      exists v', v ≡ maskv k r v'.
  Proof.
    intros * Hsem.
    inv Hsem; eapply sem_lexp_mask_inv in H1; eauto.
  Qed.

  Lemma sem_vars_unmask: forall r H xs vs,
      (forall k : nat, Forall2 (sem_var (mask_hist k r H)) xs (map (maskv k r) vs)) ->
      Forall2 (sem_var H) xs vs.
  Proof.
    setoid_rewrite Forall2_map_2.
    induction xs; intros * Hf.
    - specialize (Hf 0); inv Hf; auto.
    - assert (Hf0 := Hf 0). inv Hf0.
      constructor.
      + eapply LCS.sem_var_unmask. intros k.
        specialize (Hf k). inv Hf; eauto.
      + eapply IHxs; intros.
        specialize (Hf k). inv Hf; eauto.
  Qed.

  Lemma sem_normalized_lexp_det {PSyn prefs} : forall (G: @L.global PSyn prefs) H b e vs1 vs2,
      LN.Unnesting.normalized_lexp e ->
      LS.sem_exp G H b e vs1 ->
      LS.sem_exp G H b e vs2 ->
      EqSts vs1 vs2.
  Proof.
    intros * Hun. revert vs1 vs2.
    induction Hun; intros * Hs1 Hs2; inv Hs1; inv Hs2.
    - (* const *)
      rewrite H4, H5. reflexivity.
    - (* enum *)
      rewrite H6, H7. reflexivity.
    - (* var *)
      eapply sem_var_det in H6; eauto.
      rewrite H6. reflexivity.
    - (* unop *)
      eapply IHHun in H6; eauto. apply Forall2_singl in H6.
      rewrite H6 in H12. constructor; auto.
      rewrite H8 in H11. inv H11. clear - H9 H12.
      eapply ntheq_eqst. intros n.
      rewrite lift1_spec in *.
      specialize (H9 n) as [(?&?)|(?&?&?&?&?)]; specialize (H12 n) as [(?&?)|(?&?&?&?&?)]; congruence.
    - (* binop *)
      eapply IHHun1 in H5; eauto. apply Forall2_singl in H5.
      eapply IHHun2 in H8; eauto. apply Forall2_singl in H8.
      rewrite H5, H8 in H17. constructor; auto.
      rewrite H15 in H10. inv H10. rewrite H16 in H11. inv H11.
      clear - H12 H17.
      eapply ntheq_eqst. intros n.
      rewrite lift2_spec in *.
      specialize (H12 n) as [(?&?&?)|(?&?&?&?&?&?&?)];
        specialize (H17 n) as [(?&?&?)|(?&?&?&?&?&?&?)]; try congruence.
    - (* when *)
      eapply sem_var_det in H9; eauto.
      inv H8; inv H4. inv H11; inv H5.
      eapply IHHun in H2; eauto.
      simpl in *; rewrite app_nil_r in *. clear -H2 H9 H10 H13.
      revert vs1 vs2 H10 H13.
      induction H2; intros; inv H10; inv H13; constructor; eauto.
      2:eapply IHForall2; eauto.
      rewrite H, H9 in H4. clear - H3 H4.
      eapply ntheq_eqst. intros n.
      rewrite when_spec in *.
      specialize (H3 n) as [(?&?&?)|[(?&?&?&?&?&?)|(?&?&?&?)]];
        specialize (H4 n) as [(?&?&?)|[(?&?&?&?&?&?)|(?&?&?&?)]]; congruence.
  Qed.

  Fact disj_str_Cons : forall x y xs ys,
      disj_str [x ⋅ xs; y ⋅ ys] ≡ x || y ⋅ disj_str [xs; ys].
  Proof.
    intros.
    eapply ntheq_eqst. intros [|].
    - rewrite 2 Str_nth_0_hd; simpl.
      rewrite Bool.orb_false_r; auto.
    - rewrite 2 Str_nth_S_tl; simpl.
      reflexivity.
  Qed.

  Lemma mask_comm {A} (absent : A) : forall k1 k2 r1 r2 xs,
      mask absent k1 r1 (mask absent k2 r2 xs) ≡ mask absent k2 r2 (mask absent k1 r1 xs).
  Proof.
    intros *.
    eapply ntheq_eqst. intros n.
    repeat rewrite mask_nth.
    destruct (_ =? _), (_ =? _); auto.
  Qed.

  Lemma disj_str_maskb : forall k r rs,
      maskb k r (disj_str rs) ≡ disj_str (map (maskb k r) rs).
  Proof.
    intros *.
    eapply ntheq_eqst. intros n.
    rewrite maskb_nth, 2 disj_str_spec, existsb_map.
    destruct (_ =? _) eqn:Hcount.
    1,2:induction rs; simpl; try rewrite maskb_nth, Hcount; auto.
    rewrite IHrs; auto.
  Qed.

  Lemma disj_str_comm : forall r1 r2,
      disj_str [r1;r2] ≡ disj_str [r2;r1].
  Proof.
    intros.
    eapply ntheq_eqst. intros.
    repeat rewrite disj_str_spec; simpl.
    repeat rewrite Bool.orb_false_r.
    apply Bool.orb_comm.
  Qed.

  (** Given a stream r and an index k, either there is a point
      in which we meet the k-nth true value in r, or there is not.
      We need the excluded-middle axiom to prove this,
      as r is an infinite stream, which prevents us from checking which of the cases
      we are in constructively (we would need to iterate infinitely in the case where
      we never meet the k-nth true)
   *)
  Lemma count_ex_dec : forall r k,
      (exists n, (count r) # n = k) \/ (forall n, (count r) # n <> k).
  Proof.
    intros.
    destruct (classic (exists n, (count r) # n = k)); auto.
    right. intros n contra; eauto.
  Qed.

  Lemma count_neq_0_or_lt : forall r k,
      (forall n, (count r) # n <> k) ->
      (k = 0 /\ r # 0 = true) \/
      (forall n, (count r) # n < k).
  Proof.
    intros ? [|k'] Hcount.
    - left. split; auto.
      unfold_Stv r; auto. exfalso.
      specialize (Hcount 0); rewrite Str_nth_0_hd in Hcount; auto.
    - right. intros n. revert r k' Hcount.
      induction n; intros.
      + specialize (Hcount 0).
        unfold_Stv r; rewrite Str_nth_0_hd in *; simpl in *; lia.
      + unfold_Stv r; rewrite Str_nth_S_tl; simpl.
        * rewrite count_S_nth'. eapply lt_n_S.
          destruct k'; simpl in *.
          -- exfalso. apply (Hcount 0); auto.
          -- eapply IHn; eauto; intros.
             specialize (Hcount (S n0)).
             contradict Hcount. rewrite Str_nth_S_tl; simpl. rewrite count_S_nth'. f_equal; auto.
        * eapply IHn; eauto; intros.
          specialize (Hcount (S n0)); eauto.
  Qed.

  Lemma count_disj_count : forall k r1 r2,
      exists k1 k2, forall n, (count (disj_str [r1;r2])) # n = k <->
                    ((count (maskb k2 r2 r1)) # n = k1 /\ (count r2) # n = k2).
  Proof.
    intros.
    destruct (count_ex_dec (disj_str [r1;r2]) k) as [(n&Heq)|].
    - exists ((count (maskb ((count r2) # n) r2 r1)) # n), ((count r2) # n); intros; subst.
      destruct (le_gt_dec n n0) as [Hle|Hgt]. apply le_lt_or_eq in Hle as [Hlt|Heq]; subst; auto.
      + split; [intros|intros (Hr1&Hr2)].
        * symmetry in H.
          split; symmetry.
          -- rewrite count_eq_false in *; auto.
             intros ? Hl1 Hl2. specialize (H _ Hl1 Hl2).
             rewrite maskb_nth. destruct (_ =? _); auto.
             rewrite disj_str_spec in H; simpl in H.
             destruct (r1 # k), (r2 # k); simpl in *; try congruence.
          -- rewrite count_eq_false in *; auto.
             intros ? Hl1 Hl2. specialize (H _ Hl1 Hl2).
             rewrite disj_str_spec in H; simpl in H.
             destruct (r1 # k), (r2 # k); simpl in *; try congruence.
        * symmetry. symmetry in Hr1. symmetry in Hr2.
          rewrite count_eq_false; auto. intros ? Hl1 Hl2.
          assert ((count r2) # k = (count r2) # n) as Hr2k.
          { eapply count_between. 2:eauto. 1-3:lia. }
          rewrite count_eq_false in Hr1, Hr2; auto.
          specialize (Hr1 _ Hl1 Hl2). specialize (Hr2 _ Hl1 Hl2).
          rewrite <-Hr2k, maskb_nth, Nat.eqb_refl in Hr1.
          rewrite disj_str_spec; simpl. rewrite Hr1, Hr2; auto.
      + split; auto.
      + apply gt_not_le, Nat.nle_gt in Hgt.
        split; [intros|intros (Hr1&Hr2)].
        * split.
          -- rewrite count_eq_false in *; auto.
             intros ? Hl1 Hl2. specialize (H _ Hl1 Hl2).
             rewrite maskb_nth. destruct (_ =? _); auto.
             rewrite disj_str_spec in H; simpl in H.
             destruct (r1 # k), (r2 # k); simpl in *; try congruence.
          -- rewrite count_eq_false in *; auto.
             intros ? Hl1 Hl2. specialize (H _ Hl1 Hl2).
             rewrite disj_str_spec in H; simpl in H.
             destruct (r1 # k), (r2 # k); simpl in *; try congruence.
        * rewrite count_eq_false; auto. intros ? Hl1 Hl2.
          assert ((count r2) # k = (count r2) # n) as Hr2k.
          { rewrite <-Hr2. eapply count_between. 2:eauto. 1-3:lia. }
          rewrite count_eq_false in Hr1, Hr2; auto.
          specialize (Hr1 _ Hl1 Hl2). specialize (Hr2 _ Hl1 Hl2).
          rewrite <-Hr2k, maskb_nth, Nat.eqb_refl in Hr1.
          rewrite disj_str_spec; simpl. rewrite Hr1, Hr2; auto.
    - exists k, k. eapply count_neq_0_or_lt in H as [(?&Hr0)|Hlt]; subst.
      + intros n; split; [intros | intros (H1&H2)].
        eapply count_0_inv in H; congruence.
        eapply count_0_inv in H1. eapply count_0_inv in H2.
        rewrite Str_nth_0_hd in H1, H2, Hr0.
        unfold_Stv r1; unfold_Stv r2; simpl in *; try congruence.
      + intros n; split; [intros | intros (H1&H2)]; subst.
        * specialize (Hlt n). lia.
        * specialize (Hlt n). exfalso.
          specialize (count_disj_le2 n r1 r2) as Hle. lia.
  Qed.

  Lemma mask_disj : forall k r1 r2,
      exists k1 k2,
        forall {A} (absent: A) xs, mask absent k (disj_str [r1;r2]) xs ≡
                                   mask absent k1 (maskb k2 r2 r1) (mask absent k2 r2 xs).
  Proof.
    intros.
    specialize (count_disj_count k r1 r2) as (k1&k2&Hk).
    exists k1. exists k2. intros.
    eapply ntheq_eqst; intros. repeat rewrite mask_nth.
    destruct (_ =? _) eqn:Hcount.
    - apply Nat.eqb_eq, Hk in Hcount as (Hk1&Hk2).
      rewrite <- Nat.eqb_eq in Hk1, Hk2. rewrite Hk1, Hk2; auto.
    - rewrite Nat.eqb_neq, Hk in Hcount.
      apply Decidable.not_and in Hcount as [?|?]; eauto using Nat.eq_decidable.
      + rewrite <-Nat.eqb_neq in H. now rewrite H.
      + rewrite <-Nat.eqb_neq in H. rewrite H. destruct (_ =? k1); auto.
  Qed.

  Corollary mask_disj' : forall k r1 r2,
      exists k1 k2,
        (forall xs, maskv k (disj_str [r1;r2]) xs ≡ maskv k1 (maskb k2 r2 r1) (maskv k2 r2 xs)) /\
        (forall bs, maskb k (disj_str [r1;r2]) bs ≡ maskb k1 (maskb k2 r2 r1) (maskb k2 r2 bs)) /\
        (forall H, Env.Equiv (@EqSt _) (mask_hist k (disj_str [r1;r2]) H) (mask_hist k1 (maskb k2 r2 r1) (mask_hist k2 r2 H))).
  Proof.
    intros *.
    specialize (mask_disj k r1 r2) as (k1&k2&Heq).
    exists k1, k2. split; [|split]; eauto.
    intros H. eapply Env.Equiv_orel; intros.
    unfold mask_hist. repeat rewrite Env.Props.P.F.map_o.
    destruct (Env.find x H); simpl; constructor; eauto.
  Qed.

  Lemma sem_toeq {PSyn prefs} :
    forall cenv out (G: @L.global PSyn prefs) H P env envo xr rs r eq eq' b,
      LN.NormFby.normalized_equation G out eq ->
      LT.wt_equation G (idty cenv) eq ->
      LC.wc_equation G (idck cenv) eq ->
      LC.wc_global G ->
      envs_eq env (idck cenv) ->
      (forall f xs ys,
          LCS.sem_node_ck G f xs ys ->
          NLSC.sem_node P f xs ys) ->
      LCS.sc_vars (idck cenv) H b ->
      Forall (fun xr => In xr (idck cenv)) xr ->
      to_equation env envo xr eq = OK eq' ->
      Forall2 (sem_var H) (map fst xr) rs ->
      bools_ofs rs r ->
      (forall k, LCS.sem_equation_ck G (mask_hist k r H) (maskb k r b) eq) ->
      NLSC.sem_equation P H b eq'.
  Proof.
    intros ?????????? [xs [|e []]] eq' b Hnormed Hwt Hwc Hwcg
           Henvs Hsemnode Hvar Hxr Htoeq Hsxr Hbools Hsem; try now (inv Htoeq; cases).
    destruct Hwt as (Hwt1&Hwt2). destruct Hwc as (Hwc1&Hwc2&Hwc3).
    destruct e.
    1-5,8-10:(inv Hnormed; simpl in *; simpl_Foralls;
              simpl in *; try rewrite app_nil_r in *; subst).
    - monadInv Htoeq.
      eapply sem_toeq_normalized in Hsem; eauto.
      simpl. erewrite envs_eq_find in EQ; eauto; inv EQ; eauto.
    - monadInv Htoeq.
      eapply sem_toeq_normalized in Hsem; eauto.
      simpl. erewrite envs_eq_find in EQ; eauto; inv EQ; eauto.
    - monadInv Htoeq.
      eapply sem_toeq_normalized in Hsem; eauto.
      simpl. erewrite envs_eq_find in EQ; eauto; inv EQ; eauto.
    - monadInv Htoeq.
      eapply sem_toeq_normalized in Hsem; eauto.
      simpl. erewrite envs_eq_find in EQ; eauto; inv EQ; eauto.
    - monadInv Htoeq.
      eapply sem_toeq_normalized in Hsem; eauto.
      simpl. erewrite envs_eq_find in EQ; eauto; inv EQ; eauto.
    - monadInv Htoeq.
      eapply sem_toeq_normalized in Hsem; eauto.
      simpl. erewrite envs_eq_find in EQ; eauto; inv EQ; eauto.
    - monadInv Htoeq.
      eapply sem_toeq_normalized in Hsem; eauto.
      simpl. erewrite envs_eq_find in EQ; eauto; inv EQ; eauto.
    - monadInv Htoeq.
      eapply sem_toeq_normalized in Hsem; eauto.
      simpl. erewrite envs_eq_find in EQ; eauto; inv EQ; eauto.
    - (* EFby *)
      inversion Htoeq as [Heq'].
      cases; monadInv Heq'. rename x1 into ck.
      assert (exists y, sem_var H i y) as (y&Hv).
      { assert (Hsem':=Hsem). specialize (Hsem' 0). inv Hsem'. inv H6; inv H4.
        eapply sem_var_mask_inv in H3 as (?&?&?); eauto. }
      assert (exists v, forall k, NLSC.sem_aexp (mask_hist k r H) (maskb k r b) ck x2 (maskv k r v)
                        /\ LS.fby (NCor.const_val (abstract_clock (maskv k r v)) (sem_const x0))
                                 (maskv k r v) (maskv k r y)) as (v&Hsel).
      { eapply consolidate_mask with (P0:=fun k v => NLSC.sem_aexp (mask_hist k r H) (maskb k r b) ck x2 v
                                       /\ LS.fby (NCor.const_val (abstract_clock v) (sem_const x0))
                                                v (maskv k r y)).
        { intros ?????? (?&?); subst; split.
          - eapply NLSC.sem_aexp_morph; eauto; reflexivity.
          - rewrite <-H1; auto.
        }
        intros k. specialize (Hsem k). inv Hsem. simpl_Foralls.
        inv H2. inv H3. inv H6. simpl_Foralls.
        simpl in *. repeat rewrite app_nil_r in *. subst.
        inv H28; inv H24.
        eapply sem_exp_lexp in EQ2; eauto using LCS.sem_exp_ck_sem_exp.
        assert (y2 = ck); subst.
        { erewrite envs_eq_find in EQ0; eauto. inv EQ0; eauto. }
        assert (sem_clock (mask_hist k r H) (maskb k r b) ck (abstract_clock y1)) as Hck.
        { inv Hnormed. 2:inv H4; inv H0.
          eapply LCS.sc_exp in H10; eauto using LCS.sc_vars_mask.
          apply LN.Unnesting.normalized_lexp_numstreams in H27. rewrite <- L.length_clockof_numstreams in H27.
          singleton_length.
          apply Forall2_singl in H10; subst.
          inv H5; auto.
          apply Forall2_singl in H17; auto. rewrite H17; auto.
        }
        eapply sem_lexp_laexp in EQ2; eauto using LCS.sem_exp_ck_sem_exp.
        eapply to_constant_sem in EQ1; eauto using LCS.sem_exp_ck_sem_exp.
        2:{ eapply Forall2_eq in H14. congruence. }
        rewrite EQ1 in H23.
        assert (Hmask:=EQ2). eapply sem_laexp_mask_inv in Hmask as (?&Hmask).
        rewrite Hmask in H23, EQ2.
        eapply sem_var_mask in Hv; eauto. eapply sem_var_det in H7; eauto.
        setoid_rewrite H7. eauto.
      }
      econstructor; eauto.
      + eapply sem_aexp_mask; eauto. intros. eapply Hsel; eauto.
      + eapply Forall_forall. intros (?&?) Hin.
        eapply Forall_forall in Hxr; eauto.
        eapply Forall_forall in Hvar; eauto. simpl in Hvar. destruct Hvar as (?&Hsemv&Hsemc).
        econstructor; intros ? Hsemv'; eauto.
        eapply sem_var_det in Hsemv; eauto.
        do 2 esplit; eauto. rewrite <-Hsemv. apply ac_aligned.
      + erewrite <-fby_reset_fby; eauto.
        intros k. eapply Hsel; eauto.
    - (* EArrow *) inv Hnormed. inv H2. inv H0.
    - (* Eapp *)
      assert (Forall LN.Unnesting.normalized_lexp l) as Hnormed'.
      { clear - Hnormed. inv Hnormed; eauto. inv H1; inv H. }
      simpl in Htoeq.
      destruct (vars_of l0) eqn:Vars. eapply vars_of_spec in Vars.
      1,2:cases; monadInv Htoeq.
      assert (exists ys, Forall2 (sem_var H) xs ys) as (ys&Hv).
      { assert (Hsem':=Hsem). specialize (Hsem' 0). inv Hsem'.
        eapply LS.sem_vars_mask_inv in H6 as (?&?&?); eauto. }
      assert (exists vs, forall k, Forall2 (LCS.sem_exp_ck G (mask_hist k r H) (maskb k r b)) l (map (map (maskv k r)) vs))
             as (ess&Hse).
      { assert (exists vs, forall k, Forall2 (fun e v => LCS.sem_exp_ck G (mask_hist k r H) (maskb k r b) e [v]) l (map (maskv k r) vs))
          as (ess&Hse).
        setoid_rewrite Forall2_map_2.
        setoid_rewrite Forall2_forall'
          with (P0 := fun k e v => LCS.sem_exp_ck G (mask_hist k r H) (maskb k r b) e [maskv k r v]).
        eapply Forall_Forall2. eapply Forall_forall; intros.
        eapply consolidate_mask with (P0:=fun k v => LCS.sem_exp_ck G (mask_hist k r H) (maskb k r b) x0 [v]).
        { intros ????? Heq ?; subst.
          rewrite <-Heq; auto. }
        intros k. specialize (Hsem k). inv Hsem. simpl_Foralls.
        inv H5. simpl_Foralls.
        eapply Forall2_ignore2, Forall_forall in H10 as (?&?&?); eauto.
        eapply Forall_forall in Hnormed'; eauto.
        eapply sem_normalized_lexp_mask_inv in Hnormed' as (?&Heq); eauto using LCS.sem_exp_ck_sem_exp.
        rewrite Heq in H2; eauto.
        exists (List.map (fun x => [x]) ess).
        intros k. specialize (Hse k). rewrite 2 Forall2_map_2; simpl. rewrite Forall2_map_2 in Hse.
        auto.
      }
      assert (exists vr', Forall2 (sem_var H) (map fst l2) vr') as (vr'&Hvr).
      { clear - Vars Hsem.
        eapply Forall_Forall2; rewrite Forall_map; eapply Forall_forall; intros (?&?) Hin.
        specialize (Hsem 0). inv Hsem. simpl_Foralls.
        inv H2. eapply Forall2_trans_ex in Vars; [|eapply Forall2_swap_args, H10].
        eapply Forall2_ignore1, Forall_forall in Vars as (?&?&?&?&Hs&Hx); eauto.
        destruct Hx as (?&?&?); subst. inv Hs.
        eapply sem_var_mask_inv in H8 as (?&?&?); eauto.
      }
      assert (exists sr', Forall2 bools_of vr' sr') as (sr'&Hbools2).
      { clear - Vars Hsem Hvr.
        eapply Forall_Forall2, Forall_forall; intros v' Hin.
        setoid_rewrite <-bools_of_mask with (rs:=r).
        eapply consolidate_mask with (P:=fun k sr => bools_of (maskv k r v') sr).
        { intros ????? Heq ?; subst. now rewrite <-Heq. }
        intros k.
        rewrite Forall2_map_1 in Hvr. eapply Forall2_ignore1, Forall_forall in Hvr as ((?&?)&Hin'&Hvar); eauto.
        specialize (Hsem k). inv Hsem. simpl_Foralls.
        inv H2. inversion H12 as (?&Hbools'&_).
        eapply Forall2_trans_ex in Vars; [|eapply Forall2_swap_args, H10].
        eapply Forall2_ignore1, Forall_forall in Vars as (?&?&?&?&Hs&Hx); eauto.
        destruct Hx as (?&?&?); subst. inv Hs.
        eapply sem_var_mask with (r:=r) (k:=k) in Hvar.
        eapply sem_var_det in Hvar; eauto.
        destruct H12 as (?&Hbools&_). eapply Forall2_ignore2, Forall_forall in Hbools as (?&?&Hbools); eauto.
        rewrite Hvar in Hbools.
        assert (Hbm:=Hbools). eapply bools_of_mask_inv in Hbm as (v&Heq).
        rewrite Heq in Hbools; eauto.
      }
      inversion_clear Hbools as (?&Hbools1&Hdisj).
      econstructor. instantiate (1:=(concat ess)). 6:eauto.
      + eapply sem_lexps_mask. intros k.
        specialize (Hse k).
        eapply LCS.sem_exps_ck_sem_exps, sem_exps_lexps in Hse; eauto.
        rewrite <-concat_map, Forall2_map_2 in Hse; eauto.
        simpl_Foralls. inv H3; eauto.
      + eapply LCS.sem_clock_unmask with (r:=r). intros k.
        specialize (Hse k).
        simpl_Foralls.
        take (LC.wc_exp _ _ _) and inversion_clear it
          as [| | | | | | | | | | |????? bck sub Wce ?? WIi WIo Wcr].
        eapply LCS.sc_exps in Hse as Hsc; eauto using LCS.sc_vars_mask.
        take (L.find_node _ _ = Some n) and
             pose proof (LC.wc_find_node _ _ n Hwcg it) as (?& (Wcin &?)).
        assert (find_base_clock (L.clocksof l) = bck) as ->.
        {
          apply find_base_clock_bck.
          + rewrite L.clocksof_nclocksof. eapply LC.WellInstantiated_bck; eauto.
            unfold idck. rewrite map_length, length_idty. exact (L.n_ingt0 n).
          + apply LC.WellInstantiated_parent in WIi.
            rewrite L.clocksof_nclocksof, Forall_map.
            eapply Forall_impl; eauto. now simpl.
        }
        eapply LCS.sc_parent with (ck := bck) in Hsc; eauto.
        { rewrite <-concat_map, clocks_of_mask in Hsc; auto. }
        { rewrite L.clocksof_nclocksof. eapply LC.WellInstantiated_bck; eauto.
          unfold idck. rewrite map_length, length_idty. exact (L.n_ingt0 n). }
        { apply LC.WellInstantiated_parent in WIi.
          rewrite L.clocksof_nclocksof, Forall_map.
          eapply Forall_impl; eauto. now simpl. }
      + rewrite map_app. apply Forall2_app; eauto.
      + do 2 econstructor. apply Forall2_app; eauto.
        now rewrite disj_str_app, disj_str_comm.
      + intros k.
        specialize (mask_disj' k (disj_str sr') (disj_str x0)) as (k2&k1&(Hmask&_)).
        specialize (Hsem k1). inv Hsem. simpl_Foralls.
        inv H4. specialize (H15 k2).
        assert (bs ≡ (maskb k1 r (disj_str sr'))) as Hbs.
        { eapply bools_ofs_det; eauto.
          econstructor; split. 2:rewrite disj_str_maskb; reflexivity.
          assert (EqSts rs0 (map (maskv k1 r) vr')) as Heq.
          2:{ clear -Hbools2 Heq. unfold EqSts in *. rewrite Forall2_map_2 in Heq. rewrite Forall2_map_2.
              eapply Forall2_trans_ex in Hbools2; [|eapply Heq].
              eapply Forall2_impl_In; [|eauto]. intros ?? _ _ (?&?&Heq'&?).
              rewrite Heq'; auto. eapply bools_of_mask; eauto. }
          clear - Hvr Hbools2 H12 Vars.
          eapply Forall2_trans_ex in Vars; [|eapply Forall2_swap_args, H12].
          unfold EqSts in *.
          rewrite Forall2_map_1 in Hvr. rewrite Forall2_map_2. unfold EqSts.
          eapply Forall2_trans_ex in Hvr; [|eapply Vars]. clear - Hvr.
          eapply Forall2_impl_In; [|eauto]. intros ?? _ _ ((?&?)&_&(?&_&?&(?&?&?))&?); subst.
          inv H0. eapply sem_var_mask in H2.
          eapply sem_var_det in H2; eauto.
        }
        eapply NLSC.mod_sem_node_morph_Proper. reflexivity.
        3:(eapply Hsemnode; eauto).
        * specialize (Hse k1). clear - Hwcg Hnormed' Hmask Hse H9 Hbs Hdisj.
          assert (EqSts (concat ss) (map (maskv k1 r) (concat ess))) as Heq.
          { rewrite Forall2_swap_args in H9. eapply Forall2_trans_ex in Hse; eauto.
            unfold EqSts. rewrite Forall2_map_2. rewrite Forall2_map_2 in Hse.
            eapply Forall2_concat, Forall2_impl_In; [|eauto]. intros ?? _ _ (?&Hin&?&?).
            rewrite <-Forall2_map_2.
            eapply Forall_forall in Hnormed'; eauto.
            eapply LCS.sem_exp_ck_sem_exp, sem_normalized_lexp_det in H1; eauto using LCS.sem_exp_ck_sem_exp.
          }
          clear - Hmask Heq Hbs Hdisj. unfold EqSts in *.
          rewrite Forall2_map_2 in *. rewrite Forall2_map_1.
          eapply Forall2_impl_In; [|eauto]; intros ?? _ _ Heq'; simpl in Heq'.
          rewrite Hmask, Heq', Hbs, Hdisj. reflexivity.
        * clear - Hmask Hv H6 Hbs Hdisj. simpl in H6; rewrite app_nil_r in H6.
          assert (EqSts y (map (maskv k1 r) ys)) as Heq.
          { rewrite Forall2_swap_args in H6. eapply Forall2_trans_ex in Hv; eauto.
            unfold EqSts. rewrite Forall2_map_2.
            eapply Forall2_impl_In; [|eauto]. intros ?? _ _ (?&?&?&?).
            eapply sem_var_mask, sem_var_det in H2; eauto.
          }
          clear - Hmask Heq Hbs Hdisj. unfold EqSts in *.
          rewrite Forall2_map_2 in *. rewrite Forall2_map_1.
          eapply Forall2_impl_In; [|eauto]; intros ?? _ _ Heq'; simpl in Heq'.
          rewrite Hmask, Heq', Hbs, Hdisj. reflexivity.
  Qed.

  Lemma sem_blocktoeq {PSyn prefs} :
    forall cenv out (G: @L.global PSyn prefs) H P env envo bck xr rs r eqs' b,
      LN.NormFby.normalized_block G out bck ->
      LT.wt_block G (idty cenv) bck ->
      LC.wc_block G (idck cenv) bck ->
      LC.wc_global G ->
      envs_eq env (idck cenv) ->
      (forall f xs ys,
          LCS.sem_node_ck G f xs ys ->
          NLSC.sem_node P f xs ys) ->
      LCS.sc_vars (idck cenv) H b ->
      Forall (fun xr0 => In xr0 (idck cenv)) xr ->
      block_to_equation env envo xr bck = OK eqs' ->
      Forall2 (sem_var H) (map fst xr) rs ->
      bools_ofs rs r ->
      (forall k, LCS.sem_block_ck G (mask_hist k r H) (maskb k r b) bck) ->
      NLSC.sem_equation P H b eqs'.
  Proof.
    induction bck using L.block_ind2;
      intros * Hnormed Hwt Hwc HwcG Henvs Hsemnode Hinv Hxr Heqs Hsxr Hbools Hsem;
      inv Hnormed; inv Hwt; inv Hwc; simpl in *; cases.
    - (* eq *)
      eapply sem_toeq in Heqs; eauto.
      intros k. specialize (Hsem k). inv Hsem; eauto.
    - (* reset *)
      simpl_Foralls.
      assert (exists vr, sem_var H x vr) as (vr&Hx).
      {  assert (Hsem0 := Hsem 0). inv Hsem0. inv H11.
        eapply sem_var_mask_inv in H13 as (?&?&?); eauto. }
      assert (exists sr, bools_of vr sr) as (?&Hbool).
      { setoid_rewrite <-bools_of_mask with (rs:=r).
        eapply consolidate_mask with (P0:=fun k sr => bools_of (maskv k r vr) sr).
        { intros ????? Heq ?; subst. now rewrite <-Heq. }
        intros k.
        eapply sem_var_mask with (r:=r) (k:=k) in Hx.
        specialize (Hsem k). inv Hsem. simpl_Foralls.
        inv H11. eapply sem_var_det in Hx; eauto. rewrite Hx in H14.
        assert (Hbool:=H14). eapply bools_of_mask_inv in H14 as (?&?).
        rewrite H0 in Hbool; eauto.
      }
      inversion_clear Hbools as (?&Hbools'&Hdisj).
      eapply H4 in Heqs; simpl; eauto; clear H4. 1,2:econstructor; auto.
      + inv H9; auto.
      + econstructor.
        constructor; eauto. reflexivity.
      + intros k. rewrite disj_str_cons.
        specialize (mask_disj' k x0 (disj_str x1)) as (k1&k2&Hxs&Hbs&HH).
        rewrite Hbs, HH, <-Hdisj.
        specialize (Hsem k2). inv Hsem. simpl_Foralls.
        specialize (H14 k1). simpl_Foralls.
        inv H4. eapply sem_var_mask in Hx. eapply sem_var_det in H14; eauto.
        rewrite <-H14 in H13.
        eapply bools_of_mask_det in H13; eauto.
        now rewrite H13 in H2.
  Qed.

  Lemma sem_blockstoeqs {PSyn prefs} :
    forall cenv out (G: @L.global PSyn prefs) H P env envo bcks eqs' b,
      Forall (LN.NormFby.normalized_block G out) bcks ->
      Forall (LT.wt_block G (idty cenv)) bcks ->
      Forall (LC.wc_block G (idck cenv)) bcks ->
      LC.wc_global G ->
      envs_eq env (idck cenv) ->
      (forall f xs ys,
          LCS.sem_node_ck G f xs ys ->
          NLSC.sem_node P f xs ys) ->
      LCS.sc_vars (idck cenv) H b ->
      mmap (block_to_equation env envo []) bcks = OK eqs' ->
      Forall (LCS.sem_block_ck G H b) bcks ->
      Forall (NLSC.sem_equation P H b) eqs'.
  Proof.
    induction bcks; intros * Hnormed Hwt Hwc HwcG Henvs Hsemnode Hinv Heqs Hsem;
      inv Hnormed; inv Hwt; inv Hwc; inv Hsem; simpl in *; monadInv Heqs; auto.
    - constructor; eauto.
      eapply sem_blocktoeq; eauto. simpl; constructor.
      eapply bools_ofs_empty.
      intros [|].
      + now rewrite maskb_false_0, mask_hist_false_0.
      + rewrite maskb_false_S, mask_hist_false_S.
        eapply LCS.sem_block_absent; eauto.
  Qed.

  Lemma inputs_clocked_vars {PSyn prefs} :
    forall (n: @L.node PSyn prefs) H ins,
      LCS.sc_vars (idck (idty (L.n_in n ++ L.n_out n))) H (clocks_of ins) ->
      NLSC.sem_clocked_vars H (clocks_of ins) (idck (idty (L.n_in n))).
  Proof.
    intros * Hsc.
    unfold LCS.sc_vars in Hsc.
    eapply Forall_map, Forall_map, Forall_app in Hsc as (Hsc&_).
    eapply Forall_map, Forall_map, Forall_forall. intros (?&?&?) Hin; simpl.
    eapply Forall_forall in Hsc as (?&Hvar&Hck); eauto; simpl in *.
    constructor; intros; eauto.
    eapply sem_var_det in Hvar; eauto. rewrite <-Hvar in Hck.
    do 2 esplit; eauto. apply ac_aligned.
  Qed.

  Module Import TrOrdered := TrOrderedFun Ids Op OpAux Cks L Lord CE NL Ord TR.

  Theorem sem_l_nl :
    forall G P f ins outs,
      LN.NormFby.normalized_global G ->
      Lord.Ordered_nodes G ->
      LT.wt_global G ->
      LC.wc_global G ->
      to_global G = OK P ->
      LCS.sem_node_ck G f ins outs ->
      NLSC.sem_node P f ins outs.
  Proof.
    intros (enms&nds).
    induction nds as [|nd]. now inversion 6.
    intros * Hnormed Hord Hwt Hwc Htr Hsem.
    destruct Hwt as (Hbool&Hwt).
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [? ? ? ? ? ? Hfind Hins Houts Hblocks Hbk (Hdom&Hsc)].
    pose proof (Lord.find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    inversion_clear Hnormed as [|?? ([??? Hblk Hblks]&?)].
    inversion_clear Hwt as [|?? (?&?)].
    inversion_clear Hwc as [|?? (?&?)].
    simpl in Hfind. destruct (ident_eq_dec (L.n_name nd) f); subst.
    - rewrite L.find_node_now in Hfind; eauto. inv Hfind.
      assert (Hord':=Hord).
      inversion_clear Hord as [|? ? Hord'' Hnnblocks Hnn].
      eapply LCS.sem_block_ck_cons in Hblocks; eauto.
      assert (Htr':=Htr). monadInv Htr'; simpl in *; monadInv EQ.
      assert (forall f ins outs,
                 LCS.sem_node_ck (L.Global enms nds) f ins outs ->
                 NLSC.sem_node (NL.Global enms x4) f ins outs) as IHnds'.
      { intros. eapply IHnds; eauto. constructor; auto.
        unfold to_global; simpl. rewrite EQ; auto. }
      take (LT.wt_node _ _) and inversion it as (Hwt1 & Hwt2 & Hwt3 & Hwt4).
      take (LC.wc_node _ _) and inversion it as (Hwc1 & Hwc2 & Hwc3).
      pose proof (L.n_nodup n) as (Hnd1&Hnd2).
      rewrite Hblk in *. inv Hnd2. inv Hblocks.
      assert (Env.refines (@EqSt _) H H') as Href.
      { rewrite map_app, map_fst_idty in Hdom.
        eapply LCS.local_hist_dom_refines; eauto; simpl in *. rewrite app_nil_r.
        intros ? [Hinm1|Hinm1] Hinm2.
        - eapply H11 in Hinm1; eauto using in_or_app.
        - eapply NoDupMembers_app_InMembers in Hnd1; eauto.
          eapply Hnd1, InMembers_incl; eauto using L.local_anons_in_block_incl.
          rewrite InMembers_idty, fst_InMembers; auto.
      }
      eapply NLSC.SNode with (H:=H'); simpl.
      + erewrite NL.find_node_now; eauto. erewrite <- to_node_name; eauto.
      + erewrite <- to_node_in, map_fst_idty; eauto.
        eapply Forall2_impl_In; [|eauto]; intros. eapply LS.sem_var_refines; eauto.
      + erewrite <- to_node_out, map_fst_idty; eauto.
        eapply Forall2_impl_In; [|eauto]; intros. eapply LS.sem_var_refines; eauto.
      + erewrite <- to_node_in; eauto.
        eapply inputs_clocked_vars; eauto.
        eapply sc_vars_refines; eauto.
      + apply NLSC.sem_equation_cons2; eauto using ord_l_nl.
        2:{ assert (Htrn' := EQ0).
            apply to_node_name in EQ0. rewrite <- EQ0.
            eapply ninin_l_nl; eauto. congruence. }
        tonodeInv EQ0; simpl in *.
        eapply sem_blockstoeqs. 5:eapply envs_eq_node. 1-9:eauto.
        * inv Hwt4. eapply Forall_impl; [|eauto]; intros.
          eapply LT.wt_block_incl; [|eauto].
          rewrite (Permutation_app_comm locs).
          repeat rewrite idty_app. now rewrite app_assoc.
        * inv Hwc3. eapply Forall_impl; [|eauto]; intros.
          eapply LC.wc_block_incl; [|eauto].
          rewrite (Permutation_app_comm locs).
          repeat rewrite idty_app. repeat rewrite idck_app. now rewrite app_assoc.
        * unfold sc_vars. rewrite (Permutation_app_comm locs), app_assoc, idty_app, idck_app.
          apply Forall_app; split; auto.
          eapply sc_vars_refines; eauto.
        * clear Htr. rewrite Hblk in Hmmap. monadInv Hmmap; eauto.
    - eapply LCS.sem_node_ck_cons in Hsem; auto.
      assert (Htr' := Htr).
      monadInv Htr. simpl in *. monadInv EQ.
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
       (LS   : LSEMANTICS       Ids Op OpAux Cks L Lord       Str)
       (LCS  : LCLOCKSEMANTICS  Ids Op OpAux Cks L LC LCA Lord Str LS)
       (LN   : NORMALIZATION    Ids Op OpAux Cks L)
       (NLSC : NLCOINDSEMANTICS Ids Op OpAux Cks        CE NL Str Ord)
<: CORRECTNESS Ids Op OpAux Cks L CE NL TR LT LC LCA Ord Lord Str LS LCS LN NLSC.
  Include CORRECTNESS Ids Op OpAux Cks L CE NL TR LT LC LCA Ord Lord Str LS LCS LN NLSC.
End CorrectnessFun.
