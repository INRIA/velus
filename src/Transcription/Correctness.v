From Velus Require Import Common.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr Transcription.TrOrdered.

From Velus Require Import Lustre.LTyping.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics Lustre.LClockedSemantics.
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
       (Import Senv : STATICENV        Ids Op OpAux Cks)
       (L           : LSYNTAX          Ids Op OpAux Cks Senv)
       (Import CE   : CESYNTAX         Ids Op OpAux Cks)
       (NL          : NLSYNTAX         Ids Op OpAux Cks        CE)
       (Import TR   : TR               Ids Op OpAux Cks Senv L      CE NL)
       (LT          : LTYPING          Ids Op OpAux Cks Senv L)
       (LC          : LCLOCKING        Ids Op OpAux Cks Senv L)
       (Ord         : NLORDERED        Ids Op OpAux Cks        CE NL)
       (Lord        : LORDERED         Ids Op OpAux Cks Senv L)
       (Import Str  : COINDSTREAMS     Ids Op OpAux Cks)
       (LS          : LSEMANTICS       Ids Op OpAux Cks Senv L Lord       Str)
       (Import LCS  : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv L LC Lord Str LS)
       (LN          : NORMALIZATION    Ids Op OpAux Cks Senv L)
       (NLSC        : NLCOINDSEMANTICS Ids Op OpAux Cks        CE NL Str Ord).

  Lemma sem_lexp_step {PSyn prefs} :
    forall (G: @L.global PSyn prefs) H b e e' s,
      to_lexp e = OK e' ->
      LCS.sem_exp_ck G H b e s ->
      LCS.sem_exp_ck G (history_tl H) (Streams.tl b) e (map (@Streams.tl _) s).
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
      LCS.sem_exp_ck G H b e s ->
      LCS.sem_exp_ck G (history_tl H) (Streams.tl b) e (map (@Streams.tl _) s).
  Proof.
    einduction e using L.exp_ind2; intros * Htr Hsem;
      (now inv Htr) || (unfold to_cexp in Htr;
                       try (monadInv Htr; eapply sem_lexp_step; simpl; eauto)).
    - (* merge *)
      destruct a as ([|? [|]]&?); monadInv Htr; fold to_cexp in *.
      inv Hsem. destruct s0.
      eapply LCS.Smerge with (vs:=map (map (fun '(i, vs) => (i, Streams.tl vs))) vs); eauto.
      + eapply sem_var_step; eauto.
      + clear - EQ H0 H9. eapply LS.Forall2Brs_map_2.
        eapply LS.Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse.
        eapply Exists_exists in Hin as (?&Hin1&Hin2).
        eapply mmap_inversion, Coqlib.list_forall2_in_left in EQ as ((?&?)&?&Htr); eauto.
        cases. monadInv Htr. simpl in *. destruct Hin2 as [|[]]; subst.
        eapply Forall_forall in H0; eauto; simpl in *. inv H0; eauto.
      + rewrite Forall2_map_1, Forall2_map_2.
        eapply Forall2_impl_In; [|eauto]; intros ?? _ _ Hmerge.
        inv Hmerge; eauto.
    - (* case *)
      destruct a as ([|? [|]]&?); cases; monadInv Htr; fold to_cexp in *.
      + inv Hsem. destruct s0.
        eapply LCS.ScaseDefault with (vs:=map (map (fun '(i, vs) => (i, Streams.tl vs))) vs)
                                    (vd:=(map (map (fun x => Streams.tl x)) vd)).
        * eapply sem_lexp_step in H7; eauto.
        * simpl. inv H10; inv H6.
          constructor; auto. inv H5; auto.
        * eapply LS.Forall2Brs_map_2.
          eapply LS.Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse.
          eapply Exists_exists in Hin as (?&Hin1&Hin2).
          eapply mmap_inversion, Coqlib.list_forall2_in_left in EQ1 as ((?&?)&?&Htr); eauto.
          cases. monadInv Htr. simpl in *. destruct Hin2 as [|[]]; subst.
          eapply Forall_forall in H0; eauto; simpl in *. inv H0; eauto.
        * simpl in *. inv H13; inv H6. simpl.
          apply Forall_singl in H1. eauto.
        * rewrite Forall3_map_1, <-concat_map, 2 Forall3_map_2, Forall3_map_3.
          rewrite Forall3_map_2 in H14.
          eapply Forall3_impl_In; [|eauto]; intros ??? _ _ _ Hcase.
          inv Hcase; auto.
      + inv Hsem. destruct s0.
        eapply LCS.ScaseTotal with (vs:=map (map (fun '(i, vs) => (i, Streams.tl vs))) vs).
        * eapply sem_lexp_step in H10; eauto.
        * eapply LS.Forall2Brs_map_2.
          eapply LS.Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse.
          eapply Exists_exists in Hin as (?&Hin1&Hin2).
          eapply mmap_inversion, Coqlib.list_forall2_in_left in EQ1 as ((?&?)&?&Htr); eauto.
          cases. monadInv Htr. simpl in *. destruct Hin2 as [|[]]; subst.
          eapply Forall_forall in H0; eauto; simpl in *. inv H0; eauto.
        * rewrite Forall3_map_1, Forall3_map_2, Forall3_map_3.
          rewrite Forall3_map_2 in H12.
          eapply Forall3_impl_In; [|eauto]; intros ??? _ _ _ Hcase.
          inv Hcase; auto.
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
      LCS.sem_exp_ck G H b e [s] ->
      NLSC.sem_exp (LS.var_history H) b e' s.
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr Hsem; inv Htr.
    - inv Hsem. now econstructor.
    - inv Hsem. now constructor.
    - destruct a. inv Hsem. inv H1. econstructor.
      now apply LS.sem_var_history.
    - destruct a. inv Hsem. monadInv H1. inv Hwt. econstructor; eauto.
      eapply ty_lexp in EQ; eauto. rewrite H9 in EQ. now inv EQ.
    - destruct a. inv Hsem. monadInv H1. inv Hwt. econstructor; eauto.
      eapply ty_lexp in EQ; eauto. eapply ty_lexp in EQ1; eauto.
      rewrite H11 in EQ. inv EQ. rewrite H12 in EQ1. now inv EQ1.
    - cases. monadInv H2. inv Hsem. inv H0. clear H4. inv Hwt.
      simpl_Forall; try rewrite app_nil_r in *; subst.
      econstructor; eauto. now apply LS.sem_var_history.
  Qed.

  Lemma sem_lexp_single {PSyn prefs} :
    forall e e' G H b ss,
      to_lexp e = OK e' ->
      LCS.sem_exp_ck (G: @L.global PSyn prefs) H b e ss ->
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
      Forall2 (LCS.sem_exp_ck G H b) es ss ->
      Forall2 (NLSC.sem_exp (LS.var_history H) b) les (concat ss).
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

  Lemma sem_exp_controls {PSyn prefs} (G: @L.global PSyn prefs) env0 : forall H b es es' vs,
    Forall (fun es =>
              Forall (fun e => forall e' s,
                          LT.wt_exp G env0 e ->
                          to_cexp e = OK e' ->
                          LCS.sem_exp_ck G H b e [s] ->
                          NLSC.sem_cexp (LS.var_history H) b e' s)
                     (snd es)) es ->
    Forall (fun es => Forall (LT.wt_exp G env0) (snd es)) es ->
    LS.Forall2Brs (LCS.sem_exp_ck G H b) es [vs] ->
    mmap
      (fun pat =>
         match pat with
         | (i, []) => Error (msg "control expression not normalized")
         | (i, [e]) => do ce <- to_cexp e; OK (i, ce)
         | (i, e :: _ :: _) => Error (msg "control expression not normalized")
         end) es = OK es' ->
    Forall2 (NLSC.sem_cexp (LS.var_history H) b) (map snd es') (map snd vs).
  Proof.
    induction es; intros * Hf Hwt Hsem Hmmap;
      inv Hf; inv Hwt; inv Hsem; simpl in *; monadInv Hmmap.
    - apply Forall_singl in H0; subst; simpl; auto.
    - cases. monadInv EQ. inv H6; inv H11; simpl in *; rewrite app_nil_r in *.
      inv H9; inv H12.
      eapply IHes in H3. 2,3,4:eauto.
      apply Forall_singl in H2. apply Forall_singl in H4.
      constructor; eauto.
  Qed.

  Lemma merge_Permutation : forall c vs vs' s,
      Permutation vs vs' ->
      merge c vs s ->
      merge c vs' s.
  Proof.
    intros * Hperm Hmerge.
    rewrite merge_spec in *. intros n.
    specialize (Hmerge n) as [(Hc&Hf&Hs)|(?&?&Hc&Hpres&Habs&Hs)].
    - left. repeat split; auto.
      now rewrite <-Hperm.
    - right. repeat esplit; eauto.
      1,2:now rewrite <-Hperm.
  Qed.

  Lemma case_Permutation : forall c vs vs' vd s,
      Permutation vs vs' ->
      case c vs vd s ->
      case c vs' vd s.
  Proof.
    intros * Hperm Hcase.
    rewrite case_spec in *. intros n.
    specialize (Hcase n) as [(Hc&Hf&Hd&Hs)|[(?&?&Hc&Habs&Hpres&Hd&Hs)|(?&?&Hc&Habs&Hneq&Hd&Hs)]].
    - left. repeat split; auto.
      now rewrite <-Hperm.
    - right; left. repeat esplit; eauto.
      1,2:now rewrite <-Hperm.
    - right; right. repeat esplit; eauto.
      1,2:now rewrite <-Hperm.
  Qed.

  Lemma case_complete : forall tx tn c vs vs' vd s,
      wt_streams [c] [Tenum tx tn] ->
      map fst vs' = seq 0 (length tn) ->
      (forall i v, In (i, v) vs' <-> In (i, v) vs \/ (i < length vs' /\ ~InMembers i vs /\ v = vd)) ->
      case c vs (Some vd) s ->
      case c vs' None s.
  Proof.
    intros * Hwt Hfst Heq Hcase.
    assert (length vs' = length tn) as Hlen.
    { erewrite <-map_length, Hfst, seq_length; auto. }
    rewrite case_spec in *. intros n.
    specialize (Hcase n) as [(Hc&Hf&Hd&Hs)|[(?&?&Hc&Habs&Hpres&Hd&Hs)|(?&?&Hc&Habs&Hneq&Hd&Hs)]]; simpl in *.
    - left. repeat split; auto.
      eapply Forall_forall; intros (?&?) Hin.
      eapply Heq in Hin as [Hin|(?&Hnin&?)]; subst; simpl in *; auto.
      eapply Forall_forall in Hf; eauto. auto.
    - right; left. repeat esplit; eauto.
      + eapply Forall_forall; intros (?&?) Hin.
        eapply Heq in Hin as [Hin|(?&Hnin&?)]; subst; simpl in *; auto.
        eapply Forall_forall in Habs; eauto. auto.
      + eapply Exists_exists in Hpres as ((?&?)&Hin&?&Hpres); subst.
        eapply Exists_exists. do 2 esplit; eauto. eapply Heq; eauto.
        simpl; auto.
    - right; left. repeat esplit; eauto.
      + eapply Forall_forall; intros (?&?) Hin.
        eapply Heq in Hin as [Hin|(?&Hnin&?)]; subst; simpl in *; auto.
        * eapply Forall_forall in Habs; eauto. auto.
        * congruence.
      + eapply Forall2_singl, SForall_forall in Hwt. rewrite Hc in Hwt; inv Hwt; simpl in *.
        assert (Hnth:=H1). rewrite <-Hlen in Hnth. eapply nth_In with (d:=(0, Streams.const absent)) in Hnth.
        rewrite combine_fst_snd in Hnth at 1. rewrite Hfst, combine_nth, seq_nth in Hnth; auto; simpl in *.
        2:rewrite seq_length, map_length; auto.
        apply Exists_exists. do 2 esplit; eauto; simpl. split; auto.
        eapply Heq in Hnth as [Hin|(?&Hnin&?)]; subst; auto.
        eapply Forall_forall in Hneq; eauto; simpl in *. congruence.
  Qed.

  Lemma Forall2_Permutation_1_fst {A B C} : forall (P : (A * B) -> (A * C) -> Prop) l1 l1' l2,
      Permutation l1 l1' ->
      Forall2 P l1 l2 ->
      map fst l1 = map fst l2 ->
      exists l2', Permutation l2 l2' /\ Forall2 P l1' l2' /\ map fst l1' = map fst l2'.
  Proof.
    intros P l1 l1' l2 Hperm Hf Heq. revert l2 Hf Heq.
    induction Hperm; intros l2 Hf Heq; simpl in *.
    - inv Hf. exists []; auto.
    - inv Hf; simpl in *. inv Heq.
      apply IHHperm in H3 as (l2'&Hperm'&Hf'&Heq'); auto.
      exists (y::l2'). repeat split; simpl; auto.
    - inv Hf. inv H3. simpl in *. inv Heq.
      exists (y1::y0::l'0). repeat split; simpl; auto.
      repeat constructor.
    - eapply IHHperm1 in Hf; eauto. destruct Hf as (l2'&Hperm'&Hf'&Heq').
      eapply IHHperm2 in Hf'; eauto. destruct Hf' as (l2''&Hperm''&Hf''&Heq'').
      exists l2''. split; auto. etransitivity; eauto.
  Qed.

  (** Simpler than an existential : build the list explicitely *)
  Fixpoint complete_sem (s : list enumtag) (brs : list (enumtag * Stream svalue)) (d : Stream svalue) : list (enumtag * Stream svalue) :=
    match s with
    | [] => brs
    | k::s =>
      match brs with
      | [] => (k, d)::(complete_sem s brs d)
      | (tag, e)::tl => if (tag =? k) then (tag, e)::(complete_sem s tl d)
                      else (k, d)::(complete_sem s brs d)
      end
    end.

  Lemma complete_sem_fst : forall n es d,
      NoDupMembers es ->
      Sorted.StronglySorted le (map fst es) ->
      incl (map fst es) (seq 0 n) ->
      map fst (complete_sem (seq 0 n) es d) = (seq 0 n).
  Proof.
    intros n. generalize 0 as start.
    induction n; intros * Hnd Hsort Hincl; simpl in *.
    - apply incl_nil, map_eq_nil in Hincl; subst; auto.
    - destruct es as [|(?&?)]; inv Hnd; inv Hsort; simpl in *; auto.
      + f_equal; eapply IHn; simpl; eauto using incl_nil', Sorted.StronglySorted with datatypes.
      + destruct (n0 =? start) eqn:Hn; simpl.
        * eapply Nat.eqb_eq in Hn; subst.
          f_equal; auto.
          eapply IHn; eauto.
          apply incl_cons' in Hincl as (?&Hincl).
          intros ? Hin. assert (Hin':=Hin). apply Hincl in Hin'; inv Hin'; auto.
          exfalso. now apply H1, fst_InMembers.
        * eapply Nat.eqb_neq in Hn.
          f_equal; auto.
          eapply IHn; simpl. 1,2:constructor; simpl in *; eauto.
          apply incl_cons' in Hincl as (?&Hincl).
          apply incl_cons.
          -- inv H; auto. congruence.
          -- intros ? Hin. assert (Hin':=Hin). apply Hincl in Hin'; inv Hin'; auto.
             exfalso.
             eapply Forall_forall in H4; eauto.
             inv H; try congruence.
             eapply in_seq in H0 as (Hle1&Hle2). lia.
  Qed.

  Corollary complete_sem_length : forall n ys d,
      NoDupMembers ys ->
      Sorted.StronglySorted le (map fst ys) ->
      incl (map fst ys) (seq 0 n) ->
      length (complete_sem (seq 0 n) ys d) = n.
  Proof.
    intros * Hnd Hs Hincl.
    erewrite <-map_length, complete_sem_fst, seq_length; eauto.
  Qed.

  Lemma complete_branches_sem H b : forall n es d ys vd,
      map fst ys = map fst es ->
      Forall2 (fun e y => NLSC.sem_cexp H b (snd e) (snd y)) es ys ->
      NLSC.sem_cexp H b d vd ->
      Forall2 (fun oe => NLSC.sem_cexp H b (or_default d oe)) (map snd (complete_branches (seq 0 n) es)) (map snd (complete_sem (seq 0 n) ys vd)).
  Proof.
    intros n. generalize 0 as start.
    induction n; intros * Hfst Hses Hsd; simpl in *.
    - rewrite 2 Forall2_map_1, Forall2_map_2.
      eapply Forall2_impl_In; [|eauto]; intros (?&?) ? _ _ ?; simpl; auto.
    - inv Hses; simpl.
      + constructor; auto.
      + destruct x, y; simpl in *; inv Hfst.
        destruct (e =? start); simpl; constructor; eauto.
        eapply IHn; eauto. simpl; f_equal; auto.
  Qed.

  Lemma complete_sem_In : forall n ys d i v,
      NoDupMembers ys ->
      Sorted.StronglySorted le (map fst ys) ->
      incl (map fst ys) (seq 0 n) ->
      In (i, v) (complete_sem (seq 0 n) ys d) <-> In (i, v) ys \/ (In i (seq 0 n) /\ ~InMembers i ys /\ v = d).
  Proof.
    intros n. generalize 0 as start.
    induction n; intros * Hnd Hsorted Hincl;
      (split; [intros Hin|intros [Hin|(Hlt&Hnin&Heq)]]); simpl in *; subst; auto.
    - lia.
    - destruct ys as [|(?&?)]; simpl in *.
      + destruct Hin as [Heq|Hin]. inv Heq; auto.
        eapply IHn in Hin; eauto; simpl in *; auto using incl_nil'. intuition.
      + destruct (n0 =? start) eqn:Heq; simpl; inv Hin; eauto.
        * apply Nat.eqb_eq in Heq; subst.
          inv Hnd; inv Hsorted. eapply IHn in H as [?|(?&?&?)]; subst; eauto.
          -- right. repeat split; auto. apply and_not_or; split; auto.
             intro contra; subst. eapply in_seq in H. lia.
          -- eapply incl_cons' in Hincl as (?&Hincl).
             intros ? Hin. assert (Hin':=Hin). eapply Hincl in Hin'; inv Hin'; auto.
             exfalso. apply H2, fst_InMembers; auto.
        * apply Nat.eqb_neq in Heq.
          apply incl_cons' in Hincl as (Hincl1&Hincl2). inv Hincl1; try congruence.
          inv H. right. repeat split; auto. apply and_not_or; split; auto.
          intro contra. apply fst_InMembers in contra.
          inv Hsorted. eapply Forall_forall in H3; eauto.
          eapply in_seq in H0. lia.
        * apply Nat.eqb_neq in Heq.
          apply incl_cons' in Hincl as (Hincl1&Hincl2). inv Hincl1; try congruence.
          eapply IHn in H as [?|(?&?&?)]; eauto; simpl; auto.
          intros ? [|Hin]; subst; auto.
          assert (Hin':=Hin). eapply Hincl2 in Hin'; inv Hin'; auto.
          exfalso. inv Hnd; inv Hsorted.
          eapply Forall_forall in H7; eauto. eapply in_seq in H0. lia.
    - destruct ys as [|(?&?)]; [inv Hin|]; simpl in *.
      destruct (n0 =? start) eqn:Heq; simpl; inv Hin; eauto.
      + apply Nat.eqb_eq in Heq; subst. inv Hnd; inv Hsorted.
        right. eapply IHn; eauto.
        eapply incl_cons' in Hincl as (?&Hincl).
        intros ? Hin. assert (Hin':=Hin). eapply Hincl in Hin'; inv Hin'; auto.
        exfalso. apply H2, fst_InMembers; auto.
      + apply Nat.eqb_neq in Heq.
        inv H; auto. right. eapply IHn; eauto; simpl; auto.
        apply incl_cons' in Hincl as (Hincl1&Hincl2). inv Hincl1; try congruence.
        intros ? [|Hin]; subst; auto.
        assert (Hin':=Hin). eapply Hincl2 in Hin'; inv Hin'; auto.
        exfalso. inv Hnd; inv Hsorted.
        eapply Forall_forall in H5; eauto. eapply in_seq in H. lia.
      + apply Nat.eqb_neq in Heq.
        right. eapply IHn; eauto; simpl; auto.
        apply incl_cons' in Hincl as (Hincl1&Hincl2). inv Hincl1; try congruence.
        intros ? [|Hin]; subst; auto.
        assert (Hin':=Hin). eapply Hincl2 in Hin'; inv Hin'; auto.
        exfalso. inv Hnd; inv Hsorted.
        eapply Forall_forall in H6; eauto. eapply in_seq in H0. lia.
    - destruct ys as [|(?&?)]; simpl in *.
      + destruct Hlt as [|Hseq]; subst; auto.
        right. eapply IHn; eauto using incl_nil'.
      + apply not_or_and in Hnin as (Hn1&Hn2).
        destruct (n0 =? start) eqn:Heq; simpl in *.
        * apply Nat.eqb_eq in Heq; subst.
          destruct Hlt as [|Hseq]; subst; try congruence.
          right. inv Hnd. inv Hsorted. eapply IHn; eauto.
          apply incl_cons' in Hincl as (?&Hincl).
          intros ? Hin. assert (Hin':=Hin). eapply Hincl in Hin'; inv Hin'; auto.
          exfalso. apply H1, fst_InMembers; auto.
        * apply Nat.eqb_neq in Heq.
          destruct Hlt as [|Hseq]; subst; auto.
          right. eapply IHn; eauto; simpl.
          -- apply incl_cons' in Hincl as (Hincl1&Hincl2). inv Hincl1; try congruence.
             intros ? [|Hin]; subst; auto.
             assert (Hin':=Hin). eapply Hincl2 in Hin'; inv Hin'; auto.
             exfalso. inv Hnd; inv Hsorted.
             eapply Forall_forall in H5; eauto. eapply in_seq in H. lia.
          -- right. repeat split; auto using and_not_or.
  Qed.

  Lemma sem_exp_cexp {PSyn prefs} :
    forall (G: @L.global PSyn prefs) env H b e e' s,
      LT.wt_exp G env e ->
      to_cexp e = OK e' ->
      LCS.sem_exp_ck G H b e [s] ->
      NLSC.sem_cexp (LS.var_history H) b e' s.
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr Hsem;
      (now inv Htr) || (unfold to_cexp in Htr;
                       try (monadInv Htr; econstructor;
                            eapply sem_exp_lexp; eauto));
      cases_eqn Eq; monadInv Htr; fold to_cexp in *.
    - (* merge *)
      inv Hsem; inv H10; inv H5.
      inv Hwt.
      eapply sem_exp_controls in H0; eauto. eapply to_controls_fst in EQ.
      eapply LS.Forall2Brs_fst, Forall_singl in H9.
      rewrite Forall2_map_1, Forall2_map_2 in H0.
      eapply Forall2_Permutation_1_fst in H0 as (s'&Hperm&Hf&Heq).
      2:eapply BranchesSort.Permuted_sort.
      2:congruence.
      econstructor; eauto.
      + eapply LS.sem_var_history; eauto.
      + eapply Forall2_map_1, Forall2_map_2; eauto.
      + replace (seq 0 (Datatypes.length (map snd s'))) with (map fst s').
        2:{ eapply Forall2_length in Hf. rewrite <-Heq, map_length, <-Hf.
            eapply Permutation_seq_eq.
            erewrite <-BranchesSort.Permuted_sort, <-map_length, 2 EQ, H11, seq_length. reflexivity.
            eapply Sorted.Sorted_StronglySorted, Sorted_map, Sorted_impl, BranchesSort.Sorted_sort.
            1,2:intros ?? Heqb. lia. apply Nat.leb_le in Heqb; auto.
        }
        erewrite <-combine_fst_snd.
        eapply merge_Permutation; [|eauto]; eauto.
    - (* case (default) *)
      inv Hsem. inv H13; inv H6. simpl in *; rewrite app_nil_r in *.
      rewrite Forall3_map_2 in H14. inv H14; inv H9.
      inv Hwt. apply Forall_singl in H20. simpl in *; rewrite app_nil_r in *.
      eapply sem_exp_lexp in H7; eauto.
      eapply sem_exp_controls in H0; eauto. eapply to_controls_fst in EQ1.
      eapply LS.Forall2Brs_fst, Forall_singl in H12.
      rewrite Forall2_map_1, Forall2_map_2 in H0.
      eapply Forall2_Permutation_1_fst in H0 as (s'&Hperm&Hf&Heq).
      2:eapply BranchesSort.Permuted_sort.
      2:congruence.
      apply Forall_singl in H1. eapply H1 in H4; eauto.
      rewrite Eq5 in H10. rewrite Eq5 in H13; inv H13.
      assert (NoDupMembers s') as Hnd'.
      { rewrite fst_NoDupMembers, <-Hperm, H12, <-fst_NoDupMembers; auto. }
      assert (Sorted.StronglySorted le (map fst s')) as Hsorted'.
      { rewrite <-Heq.
        eapply Sorted.Sorted_StronglySorted, Sorted_map, Sorted_impl, BranchesSort.Sorted_sort.
        - intros ?????; lia.
        - intros ?? Hle. eapply Nat.leb_le in Hle; auto.
      }
      assert (incl (map fst s') (seq 0 (length tn))) as Hincl'.
      { rewrite <-Hperm, H12; auto. }
      econstructor; eauto.
      + eapply complete_branches_sem; eauto.
      + eapply case_complete, case_Permutation; eauto.
        (* * rewrite combine_length, seq_length, Nat.min_id, map_length, complete_sem_length; eauto. *)
        * rewrite combine_map_fst', map_length, complete_sem_length; auto.
          rewrite seq_length; eauto.
        * intros ??. rewrite map_length, complete_sem_length; eauto.
          erewrite <-complete_sem_fst, <-combine_fst_snd at 1; eauto.
          rewrite complete_sem_In; eauto.
          rewrite combine_length, map_length, complete_sem_length, seq_length, Nat.min_id; eauto. rewrite in_seq.
          split; intros [|(Hlt&?&?)]; subst; auto. 1,2:right; repeat split; auto. 1,2:lia.
    - (* case (total) *)
      inv Hsem; simpl in *. inv H12; inv H8.
      inv Hwt.
      eapply sem_exp_lexp in H10; eauto.
      eapply sem_exp_controls in H0; eauto. eapply to_controls_fst in EQ1.
      eapply LS.Forall2Brs_fst, Forall_singl in H11.
      rewrite Forall2_map_1, Forall2_map_2 in H0.
      eapply Forall2_Permutation_1_fst in H0 as (s'&Hperm&Hf&Heq).
      2:eapply BranchesSort.Permuted_sort.
      2:congruence.
      econstructor; eauto.
      + eapply Forall2_map_1, Forall2_map_2; eauto.
        eapply Forall2_impl_In; [|eauto]; intros (?&?) (?&?) _ _ ?; simpl; eauto.
      + replace (seq 0 (Datatypes.length (map snd s'))) with (map fst s').
        2:{ eapply Forall2_length in Hf. rewrite <-Heq, map_length, <-Hf.
            eapply Permutation_seq_eq.
            erewrite <-BranchesSort.Permuted_sort, <-map_length, 2 EQ1, H12, seq_length. reflexivity.
            eapply Sorted.Sorted_StronglySorted, Sorted_map, Sorted_impl, BranchesSort.Sorted_sort.
            1,2:intros ?? Heqb. lia. apply Nat.leb_le in Heqb; auto.
        }
        erewrite <-combine_fst_snd.
        eapply case_Permutation; [|eauto]; eauto.
  Qed.

  Lemma sem_lexp_step2: forall H b e v s,
      NLSC.sem_exp H b e (v ⋅ s) ->
      NLSC.sem_exp (history_tl H) (Streams.tl b) e s.
  Proof.
    induction e; intros * Hsem; inv Hsem.
    - econstructor; eauto. unfold_St b. inv H4. simpl in *. eauto.
    - econstructor; eauto. unfold_St b. inv H6. simpl in *. eauto.
    - econstructor. eapply sem_var_step_nl; eauto.
    - inv H9; econstructor; eauto. all:eapply sem_var_step_nl; eauto.
    - inv H8; econstructor; eauto. all:eapply sem_var_step_nl; eauto.
    - inv H10; econstructor; eauto. all:eapply sem_var_step_nl; eauto.
  Qed.

  Module NCor := CorrectnessFun Ids Op OpAux Cks Str Senv L LT LC Lord LS LCS LN.

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
      LS.fby1 v0 (NCor.const_val (abstract_clock (mask' absent 0 0 r x)) x0) (mask' absent 0 0 r x) (mask' absent 0 0 r y) ->
      y # n = (NLSC.reset1 x0 (sfby v0 x) r false) # n.
  Proof.
    induction n;
      intros * Hle Hfby; unfold_Stv r; unfold_Stv x; destruct y;
        repeat rewrite Str_nth_0_hd; repeat rewrite Str_nth_S_tl; simpl in *.
    - exfalso. specialize (Hle 0 (Nat.le_0_l _)).
      rewrite Str_nth_0_hd in Hle; simpl in Hle; congruence.
    - exfalso. specialize (Hle 0 (Nat.le_0_l _)).
      rewrite Str_nth_0_hd in Hle; simpl in Hle; congruence.
    - rewrite 2 mask'_Cons, ac_Cons, NCor.const_val_Cons, Nat.eqb_refl in Hfby.
      inv Hfby; auto.
    - rewrite 2 mask'_Cons, ac_Cons, NCor.const_val_Cons, Nat.eqb_refl in Hfby.
      inv Hfby; auto.
    - exfalso. specialize (Hle 0 (Nat.le_0_l _)).
      rewrite Str_nth_0_hd in Hle; simpl in Hle; congruence.
    - exfalso. specialize (Hle 0 (Nat.le_0_l _)).
      rewrite Str_nth_0_hd in Hle; simpl in Hle; congruence.
    - rewrite 2 mask'_Cons, ac_Cons, NCor.const_val_Cons in Hfby.
      inv Hfby; auto.
      eapply IHn in H3; eauto.
      intros ? Hle'. specialize (Hle (S m)). rewrite Str_nth_S_tl in Hle. eapply Hle; lia.
    - rewrite 2 mask'_Cons, ac_Cons, NCor.const_val_Cons in Hfby.
      inv Hfby; auto.
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
                 LS.fby (NCor.const_val (abstract_clock (mask' absent k 0 r x)) x0) (mask' absent k 0 r x) (mask' absent k 0 r y)) as Hfby'.
    { intros. apply Hfby. } clear Hfby. rename Hfby' into Hfby.

    revert x0 x y r Hfby.
    induction n;
      intros; unfold_Stv r; unfold_Stv x; destruct y;
        repeat rewrite Str_nth_0_hd; repeat rewrite Str_nth_S_tl; simpl in *.
    - specialize (Hfby 1). rewrite 2 mask'_Cons, ac_Cons, NCor.const_val_Cons, Nat.eqb_refl in Hfby.
      rewrite Str_nth_0_hd in Hfby; simpl in Hfby; specialize (Hfby (Nat.le_refl _)).
      inv Hfby; auto.
    - specialize (Hfby 1). rewrite 2 mask'_Cons, ac_Cons, NCor.const_val_Cons, Nat.eqb_refl in Hfby.
      rewrite Str_nth_0_hd in Hfby; simpl in Hfby; specialize (Hfby (Nat.le_refl _)).
      inv Hfby; auto.
    - specialize (Hfby 0). rewrite 2 mask'_Cons, ac_Cons, NCor.const_val_Cons, Nat.eqb_refl in Hfby.
      rewrite Str_nth_0_hd in Hfby; simpl in Hfby; specialize (Hfby (Nat.le_refl _)).
      inv Hfby; auto.
    - specialize (Hfby 0). rewrite 2 mask'_Cons, ac_Cons, NCor.const_val_Cons, Nat.eqb_refl in Hfby.
      rewrite Str_nth_0_hd in Hfby; simpl in Hfby; specialize (Hfby (Nat.le_refl _)).
      inv Hfby; auto.
    - rewrite NLSC.reset1_fby.
      eapply IHn; auto. intros k Hc.
      specialize (Hfby (S k)).
      rewrite Str_nth_S_tl in Hfby; simpl in Hfby. setoid_rewrite count_S_nth' in Hfby.
      specialize (Hfby (le_n_S _ _ Hc)).
      destruct k; rewrite 2 mask'_Cons, ac_Cons, NCor.const_val_Cons, 2 mask'_S in Hfby; inv Hfby; eauto.
    - (* 2 possibilities : *)
    (*      + there is no reset before n, in which case the sequence behaves as fby1 until n *)
    (*      + there is a reset before n, in which case we can use the induction hypothesis *)
    (*    *)
      destruct (reset_or_not_reset n r).
      + specialize (Hfby 1). rewrite 2 mask'_Cons, ac_Cons, NCor.const_val_Cons, Nat.eqb_refl, 2 mask'_S in Hfby.
        rewrite Str_nth_S_tl in Hfby; simpl in Hfby. setoid_rewrite count_S_nth' in Hfby.
        rewrite (proj1 (count_0 _ _)) in Hfby; auto. specialize (Hfby (Nat.le_refl _)).
        inv Hfby.
        eapply fby1_reset1_fby; eauto.
      + rewrite reset1_fby_reset; auto.
        eapply IHn; eauto. intros k Hle.
        assert (k > 0) as Hgt by (eapply count_not_0 in H; lia).
        specialize (Hfby (S k)).
        rewrite Str_nth_S_tl, 2 mask'_Cons, 2 mask'_S in Hfby; simpl in Hfby. setoid_rewrite count_S_nth' in Hfby.
        specialize (Hfby (le_n_S _ _ Hle)).
        destruct k; rewrite ac_Cons, NCor.const_val_Cons in Hfby; inv Hfby; eauto.
        inv Hgt.
    - eapply IHn; auto. intros [|k] Hle.
      + specialize (Hfby 0). rewrite 2 mask'_Cons, ac_Cons, NCor.const_val_Cons in Hfby.
        rewrite Str_nth_S_tl in Hfby; simpl in Hfby. specialize (Hfby Hle).
        inv Hfby; auto.
      + specialize (Hfby (S k)).
        rewrite Str_nth_S_tl in Hfby; simpl in Hfby. specialize (Hfby Hle).
        destruct k; rewrite 2 mask'_Cons, ac_Cons, NCor.const_val_Cons in Hfby; inv Hfby; auto.
    - destruct (reset_or_not_reset n r).
      + specialize (Hfby 0). rewrite 2 mask'_Cons, ac_Cons, NCor.const_val_Cons in Hfby.
        rewrite Str_nth_S_tl in Hfby; simpl in Hfby.
        rewrite (proj1 (count_0 _ _)) in Hfby; auto. specialize (Hfby (Nat.le_refl _)).
        inv Hfby.
        eapply fby1_reset1_fby; eauto.
      + rewrite reset1_fby_reset; auto.
        eapply IHn; eauto. intros k Hle.
        assert (k > 0) as Hgt by (eapply count_not_0 in H; lia).
        specialize (Hfby k).
        rewrite Str_nth_S_tl, 2 mask'_Cons in Hfby; simpl in Hfby. specialize (Hfby Hle).
        destruct k as [|[|]]; rewrite ac_Cons, NCor.const_val_Cons in Hfby; inv Hfby; eauto.
        inv Hgt.
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
    destruct Hwhen as [(Hx&Hv&Hy)|[(?&?&Hx&Hv&?&Hy)|(?&Hx&Hv&Hy)]]; rewrite Hv in *; setoid_rewrite Hy.
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
    repeat rewrite LCS.CIStr.CIStr.tr_Stream_nth in *.
    destruct Hwhen as [(Hx&Hv&Hy)|[(?&?&Hx&Hv&?&Hy)|(?&Hx&Hv&Hy)]];
      rewrite Hv in *; setoid_rewrite Hx; inv Hck; auto;
      try setoid_rewrite Hy in H5; try congruence.
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
      LCS.sem_exp_ck G H b e [cs] ->
      sem_clock (LS.var_history H) b ck b' ->
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
      inv Hsem. simpl_Forall. rewrite app_nil_r in *; subst.
      assert (b' ≡ abstract_clock cs) as Hac.
      { eapply sem_clock_ac in Hsck; eauto. now apply LS.sem_var_history. }
      rewrite Hac in *. eapply sem_clock_inv in H8 as Hck'; eauto.
      assert (Hx0:=Hck'). eapply H0 in Hx0; eauto.
      eapply sem_clock_const; eauto. 1,2:now apply LS.sem_var_history.
  Qed.

  Module CES := CESemanticsFun Ids Op OpAux Cks CE IStr.
  Module CEI := CEInterpreterFun Ids Op OpAux Cks CE IStr CES.
  Module ICStr := IndexedToCoindFun Ids Op OpAux Cks IStr Str.
  Module CIStr' := CoindToIndexedFun Ids Op OpAux Cks Str IStr.
  Module Import ConvStr := CoindIndexedFun Ids Op OpAux Cks Str IStr.
  Module NLSI := NLIndexedSemanticsFun Ids Op OpAux Cks CE NL IStr Ord CES.
  Module NICStr := NLIndexedToCoindFun Ids Op OpAux Cks CE NL IStr Str ICStr Ord CES NLSI CEI NLSC.
  Module NCIStr := NLCoindToIndexedFun Ids Op OpAux Cks CE NL IStr Str CIStr' Ord CES NLSI NLSC.

  Lemma sem_rhs_arhs : forall H b ck e s,
      NLSC.sem_rhs H b e s ->
      sem_clock H b ck (abstract_clock s) ->
      NLSC.sem_arhs H b ck e s.
  Proof.
    intros * Hsem Hsck.
    apply NICStr.NLCIStr.sem_rhs_impl in Hsem.
    apply CIStr.CIStr.sem_clock_impl in Hsck.
    rewrite <-CIStr.tr_history_equiv, <-CIStr.tr_stream_eqst with (x:=b), <-CIStr.tr_stream_eqst with (x:=s).
    apply NICStr.sem_arhs_impl.
    intros ?. specialize (Hsem n). specialize (Hsck n).
    unfold CES.sem_arhs_instant.
    repeat rewrite NICStr.CIStr.tr_Stream_nth, ?ac_nth in *.
    destruct (s # n) eqn:Heq; econstructor; auto.
    1,2:setoid_rewrite Heq in Hsck; auto.
  Qed.

  Corollary sem_exp_arhs {PSyn prefs} :
    forall (G: @L.global PSyn prefs) H b env e e' s ck,
      LT.wt_exp G env e ->
      to_cexp e = OK e' ->
      LCS.sem_exp_ck G H b e [s] ->
      sem_clock (LS.var_history H) b ck (abstract_clock s) ->
      NLSC.sem_arhs (LS.var_history H) b ck (Ecexp e') s.
  Proof.
    intros * Hwt Hto Hsem Hsck.
    apply sem_rhs_arhs; auto.
    eapply sem_exp_cexp in Hsem; [|eauto|eauto].
    econstructor; eauto.
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

  Lemma sem_arhs_mask: forall r H b ck e v,
      (forall k, NLSC.sem_arhs (mask_hist k r H) (maskb k r b) ck e (maskv k r v)) ->
      NLSC.sem_arhs H b ck e v.
  Proof.
    intros * Hsem.
    rewrite <-tr_stream_eqst, <-(tr_stream_eqst v), <-tr_history_equiv.
    eapply NICStr.sem_arhs_impl. intros n.
    specialize (Hsem ((count r) # n)).
    eapply NCIStr.sem_arhs_impl in Hsem. specialize (Hsem n); simpl in Hsem.
    unfold CIStr'.tr_Stream in Hsem.
    rewrite maskv_nth, maskb_nth, Nat.eqb_refl in Hsem.
    rewrite <-LCS.history_mask_count; eauto.
  Qed.

  Lemma sem_toeq_normalized {PSyn prefs} :
    forall (G: @L.global PSyn prefs) P cenv x e ck e' r H b,
      LC.wc_global G ->
      LCS.sc_vars cenv H b ->
      LN.Unnesting.normalized_cexp e ->
      LT.wt_exp G cenv e ->
      LC.wc_exp G cenv e ->
      L.clockof e = [ck] ->
      to_cexp e = OK e' ->
      (forall k, LCS.sem_equation_ck G (mask_hist k r H) (maskb k r b) ([x], [e])) ->
      NLSC.sem_equation P (LS.var_history H) b (NL.EqDef x ck (Ecexp e')).
  Proof.
    intros * HwcG Hinv Hnormed Hwt Hwc Hck Hto Hsem.
    assert (exists v, sem_var H (Var x) v) as (v&Hvar).
    { specialize (Hsem 0). inv Hsem. simpl_Foralls.
      simpl in *; rewrite app_nil_r in *; subst.
      eapply sem_var_mask_inv in H3 as (?&Hv&?); eauto. }
    econstructor; eauto. 2:eapply LS.sem_var_history; eauto.
    eapply sem_arhs_mask with (r:=r).
    intros k. specialize (Hsem k). inv Hsem. simpl_Foralls.
    simpl in *; rewrite app_nil_r in *; subst.
    eapply sem_var_mask_inv in H3 as (?&Hvar'&Heq).
    eapply sem_var_det in Hvar; eauto. rewrite Heq, Hvar in H6.
    rewrite <-LS.var_history_mask.
    eapply sem_exp_arhs; eauto.
    eapply sc_exp in H6; eauto.
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
      LCS.sem_exp_ck G (mask_hist k r H) (maskb k r b) e v ->
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

  Lemma sem_normalized_lexp_det {PSyn prefs} : forall (G: @L.global PSyn prefs) H b e vs1 vs2,
      LN.Unnesting.normalized_lexp e ->
      LCS.sem_exp_ck G H b e vs1 ->
      LCS.sem_exp_ck G H b e vs2 ->
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
      simpl_Forall. rewrite app_nil_r in *.
      eapply IHHun in H2; eauto.
      clear -H2 H9 H10 H14.
      revert vs1 vs2 H10 H14.
      induction H2; intros; inv H10; inv H14; constructor; eauto.
      2:eapply IHForall2; eauto.
      rewrite <-H, H9 in H4. clear - H3 H4.
      eapply ntheq_eqst. intros n.
      rewrite when_spec in *.
      specialize (H3 n) as [(?&?&?)|[(?&?&?&?&?&?)|(?&?&?&?)]];
        specialize (H4 n) as [(?&?&?)|[(?&?&?&?&?&?)|(?&?&?&?)]]; congruence.
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
        * rewrite count_S_nth', <-Nat.succ_lt_mono.
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
      destruct (Compare_dec.le_gt_dec n n0) as [Hle|Hgt]. apply Nat.lt_eq_cases in Hle as [Hlt|Heq]; subst; auto.
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
      + apply Nat.lt_nge, Nat.nle_gt in Hgt.
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
        forall A (absent: A) xs, mask absent k (disj_str [r1;r2]) xs ≡
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

  Corollary mask_disj' {K} : forall k r1 r2,
      exists k1 k2,
        (forall xs, maskv k (disj_str [r1;r2]) xs ≡ maskv k1 (maskb k2 r2 r1) (maskv k2 r2 xs)) /\
        (forall bs, maskb k (disj_str [r1;r2]) bs ≡ maskb k1 (maskb k2 r2 r1) (maskb k2 r2 bs)) /\
        (forall (H: @history K), FEnv.Equiv (@EqSt _) (mask_hist k (disj_str [r1;r2]) H) (mask_hist k1 (maskb k2 r2 r1) (mask_hist k2 r2 H))).
  Proof.
    intros *.
    specialize (mask_disj k r1 r2) as (k1&k2&Heq).
    exists k1, k2. split; [|split]; eauto.
    intros H ?. simpl_fenv.
    destruct (H x); simpl; constructor; eauto.
  Qed.

  Lemma sem_toeq {PSyn prefs} :
    forall cenv out (G: @L.global PSyn prefs) H P env envo xr rs r eq eq' b,
      LN.NormFby.normalized_equation G out eq ->
      LT.wt_equation G cenv eq ->
      LC.wc_equation G cenv eq ->
      LC.wc_global G ->
      envs_eq env (idck cenv) ->
      (forall f xs ys,
          LCS.sem_node_ck G f xs ys ->
          NLSC.sem_node P f xs ys) ->
      LCS.sc_vars cenv H b ->
      Forall (fun xr => In xr (idck cenv)) xr ->
      to_equation env envo xr eq = OK eq' ->
      Forall2 (sem_var H) (map (fun '(x, _) => Var x) xr) rs ->
      bools_ofs rs r ->
      (forall k, LCS.sem_equation_ck G (mask_hist k r H) (maskb k r b) eq) ->
      NLSC.sem_equation P (LS.var_history H) b eq'.
  Proof.
    intros ?????????? [xs [|e []]] eq' b Hnormed Hwt Hwc Hwcg
           Henvs Hsemnode Hvar Hxr Htoeq Hsxr Hbools Hsem; try now (inv Htoeq; cases).
    destruct Hwt as (Hwt1&Hwt2).
    destruct e.
    1-6,10-12:(inv Hwc; inv Hnormed; simpl in *; simpl_Foralls;
              simpl in *; try rewrite app_nil_r in *; subst).
    1-9:(monadInv Htoeq;
         eapply sem_toeq_normalized in Hsem; eauto;
         simpl; erewrite envs_eq_find in EQ; eauto; inv EQ; eauto;
         inv H7; solve_In; congruence).
    - (* extcall *)
      simpl_Forall. inv Hwc; simpl_Forall.
      monadInv Htoeq.
      assert (exists v, sem_var H (Var x) v) as (v&Hvar').
      { specialize (Hsem 0). inv Hsem. simpl_Forall.
        simpl in *; rewrite app_nil_r in *; subst.
        eapply sem_var_mask_inv in H5 as (?&?&?); eauto. }
      econstructor; eauto. 2:eapply LS.sem_var_history; eauto.
      eapply sem_arhs_mask with (r:=r). intros k. specialize (Hsem k). inv Hsem. simpl_Foralls.
      simpl in *; rewrite app_nil_r in *; subst.
      eapply sem_var_mask_inv in H5 as (?&Hvar2&Heq).
      eapply sem_var_det in Hvar'; eauto. rewrite Heq, Hvar' in H10.
      eapply sc_exp in H10 as Hsemck; eauto using LCS.sc_vars_mask.
      simpl in *. simpl_Forall.
      eapply sem_rhs_arhs; eauto.
      take (LT.wt_exp _ _ _) and inv it.
      take (sem_exp_ck _ _ _ _ _) and inv it.
      econstructor; eauto.
      + eapply mmap_inversion in EQ. clear - EQ H8 H15.
        revert tyins0 H15. induction EQ; simpl in *; intros * Htys; inv H8. inv Htys; auto.
        eapply ty_lexp in H; [|eauto]. rewrite H in *.
        inv Htys. constructor; eauto.
      + eapply sem_exps_lexps in H18; eauto.

    - (* EFby *)
      inv Hwc; simpl_Foralls. rename H2 into Hwt. rename H4 into Hwc. rename H3 into Hf2.
      inversion Htoeq as [Heq'].
      cases; monadInv Heq'. rename x1 into ck.
      assert (exists y, sem_var H (Var i) y) as (y&Hv).
      { assert (Hsem':=Hsem). specialize (Hsem' 0). inv Hsem'. inv H6; inv H4.
        eapply sem_var_mask_inv in H3 as (?&?&?); eauto. }
      assert (exists v, forall k, NLSC.sem_aexp (LS.var_history (mask_hist k r H)) (maskb k r b) ck x2 (maskv k r v)
                        /\ LS.fby (NCor.const_val (abstract_clock (maskv k r v)) (sem_const x0))
                                 (maskv k r v) (maskv k r y)) as (v&Hsel).
      { eapply consolidate_mask with (P:=fun k v => NLSC.sem_aexp (LS.var_history (mask_hist k r H)) (maskb k r b) ck x2 v
                                       /\ LS.fby (NCor.const_val (abstract_clock v) (sem_const x0))
                                                v (maskv k r y)).
        { intros ?????? (?&?); subst; split.
          - eapply NLSC.sem_aexp_morph; eauto; reflexivity.
          - rewrite <-H1; auto.
        }
        intros k. specialize (Hsem k). inv Hsem. inv Hwc. inv Hwt. simpl_Foralls.
        take (sem_exp_ck _ _ _ _ _) and inv it; simpl_Foralls.
        simpl in *; repeat rewrite app_nil_r in *. subst.
        inv H24; inv H21.
        eapply sem_exp_lexp in EQ2; eauto.
        assert (y2 = ck); subst.
        { erewrite envs_eq_find in EQ0; eauto. inv EQ0; eauto.
          inv H16; solve_In; congruence. }
        assert (sem_clock (LS.var_history (mask_hist k r H)) (maskb k r b) ck (abstract_clock y1)) as Hck.
        { inv Hnormed. 2:{ inv H3; inv H0. }
          eapply sc_exp in H6; eauto using LCS.sc_vars_mask.
          simpl in *. simpl_Foralls. congruence.
        }
        eapply sem_lexp_laexp in EQ2; eauto.
        eapply to_constant_sem in EQ1; eauto.
        2:{ eapply Forall2_eq in H7. congruence. }
        rewrite EQ1 in *.
        assert (Hmask:=EQ2). eapply sem_laexp_mask_inv in Hmask as (?&Hmask).
        rewrite Hmask in *.
        eapply sem_var_mask in Hv; eauto. eapply sem_var_det in H14; eauto.
        setoid_rewrite H14. eauto.
      }
      econstructor; eauto.
      + eapply sem_aexp_mask; eauto. intros. eapply Hsel; eauto.
      + simpl_Forall. eapply LS.sem_var_history; eauto.
      + eapply Forall_forall. intros (?&?) Hin. simpl_Forall. simpl_In.
        eapply Forall2_ignore2 in Hsxr; simpl_Forall.
        take (sem_var _ _ _) and (eapply LS.sem_var_history in it as Var').
        eapply Hvar in it as Hck; [|eauto with senv].
        econstructor; intros ? Hsemv'; eauto.
        eapply sem_var_det in Var'; eauto.
        do 2 esplit; eauto. rewrite <-Var'. apply ac_aligned.
      + erewrite <-fby_reset_fby; eauto. eapply LS.sem_var_history; eauto.
        intros k. eapply Hsel; eauto.
    - (* EArrow *) inv Hnormed. inv H2. inv H0.
    - (* Eapp *)
      assert (Forall LN.Unnesting.normalized_lexp l) as Hnormed'.
      { clear - Hnormed. inv Hnormed; eauto. inv H1; inv H. }
      simpl in Htoeq.
      destruct (vars_of l0) eqn:Vars. eapply vars_of_spec in Vars.
      1,2:cases; monadInv Htoeq.
      assert (exists ys, Forall2 (sem_var H) (map Var xs) ys) as (ys&Hv).
      { assert (Hsem':=Hsem). specialize (Hsem' 0). inv Hsem'.
        edestruct (@LS.sem_vars_mask_inv var_last) as (?&?&?); [|eauto]. rewrite Forall2_map_1; eauto. }
      assert (exists vs, forall k, Forall2 (LCS.sem_exp_ck G (mask_hist k r H) (maskb k r b)) l (map (map (maskv k r)) vs))
             as (ess&Hse).
      { assert (exists vs, forall k, Forall2 (fun e v => LCS.sem_exp_ck G (mask_hist k r H) (maskb k r b) e [v]) l (map (maskv k r) vs))
          as (ess&Hse).
        setoid_rewrite Forall2_map_2.
        setoid_rewrite Forall2_forall'
          with (P := fun k e v => LCS.sem_exp_ck G (mask_hist k r H) (maskb k r b) e [maskv k r v]).
        eapply Forall_Forall2. eapply Forall_forall; intros.
        eapply consolidate_mask with (P:=fun k v => LCS.sem_exp_ck G (mask_hist k r H) (maskb k r b) x0 [v]).
        { intros ????? Heq ?; subst.
          rewrite <-Heq; auto. }
        intros k. specialize (Hsem k). inv Hsem. simpl_Foralls.
        inv H4.
        eapply Forall2_ignore2 in H11. simpl_Forall.
        eapply sem_normalized_lexp_mask_inv in Hnormed' as (?&Heq); eauto.
        rewrite Heq in H2; eauto.
        exists (List.map (fun x => [x]) ess).
        intros k. specialize (Hse k). simpl_Forall; auto.
      }
      assert (exists vr', Forall2 (sem_var H) (map (fun '(x, _) => Var x) l2) vr') as (vr'&Hvr).
      { clear - Vars Hsem.
        eapply Forall_Forall2; rewrite Forall_map; eapply Forall_forall; intros (?&?) Hin.
        specialize (Hsem 0). inv Hsem. simpl_Foralls.
        inv H2. eapply Forall2_trans_ex in Vars; [|eapply Forall2_swap_args, H11].
        eapply Forall2_ignore1, Forall_forall in Vars as (?&?&?&?&Hs&Hx); eauto.
        destruct Hx as (?&?); subst. inv Hs.
        eapply sem_var_mask_inv in H7 as (?&?&?); eauto.
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
        eapply Forall2_trans_ex in Vars; [|eapply Forall2_swap_args, H11].
        eapply Forall2_ignore1, Forall_forall in Vars as (?&?&?&?&Hs&Hx); eauto.
        destruct Hx as (?&?); subst. inv Hs.
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
        eapply sem_exps_lexps in Hse; eauto.
        rewrite <-concat_map, Forall2_map_2 in Hse; eauto.
        simpl_Foralls. inv H2; eauto.
      + eapply LCS.sem_clock_unmask with (r:=r). intros k.
        specialize (Hse k).
        eapply sc_exps in Hse; eauto using LCS.sc_vars_mask.
        2:{ inv Hwc; auto. simpl_Foralls. inv H4; auto. }
        assert (exists n bck sub, L.find_node i G = Some n /\
                             Forall2 (LC.WellInstantiated bck sub) (map (fun '(x, (_, ck, _)) => (x, ck)) (L.n_in n)) (L.nclocksof l)) as (n&bck&?&Hfind&WIi).
        { inv Hwc; eauto. simpl_Foralls. inv H4; eauto. }
        take (L.find_node _ _ = Some n) and
             pose proof (LC.wc_find_node _ _ n Hwcg it) as (?& Wc).
        inversion_clear Wc as [?? Wcin _ _ _].
        assert (find_base_clock (L.clocksof l) = bck) as ->.
        {
          apply find_base_clock_bck.
          + rewrite L.clocksof_nclocksof. eapply LC.WellInstantiated_bck; eauto.
            rewrite map_length. exact (L.n_ingt0 n).
          + apply LC.WellInstantiated_parent in WIi.
            rewrite L.clocksof_nclocksof, Forall_map.
            eapply Forall_impl; eauto. now simpl.
        }
        eapply LCS.sc_parent with (ck := bck) in Hse; eauto.
        { rewrite <-concat_map, clocks_of_mask in Hse; auto. }
        { rewrite L.clocksof_nclocksof. eapply LC.WellInstantiated_bck; eauto.
          rewrite map_length. exact (L.n_ingt0 n). }
        { apply LC.WellInstantiated_parent in WIi.
          rewrite L.clocksof_nclocksof, Forall_map.
          eapply Forall_impl; eauto. now simpl. }
      + rewrite map_app. apply Forall2_app with (l1':=rs) (l2':=vr'); eauto.
        1,2:simpl_Forall; apply LS.sem_var_history; auto.
      + do 2 econstructor. apply Forall2_app; eauto.
        now rewrite disj_str_app, disj_str_comm.
      + intros k.
        specialize (@mask_disj' ident k (disj_str sr') (disj_str x0)) as (k2&k1&(Hmask&_)).
        specialize (Hsem k1). inv Hsem. simpl_Foralls.
        inv H3. specialize (H14 k2).
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
          eapply Forall2_impl_In; [|eauto]. intros ?? _ _ ((?&?)&_&(?&_&?&(?&?))&?); subst.
          inv H0. eapply sem_var_mask in H2.
          eapply sem_var_det in H2; eauto.
        }
        eapply NLSC.mod_sem_node_morph_Proper. reflexivity.
        3:(eapply Hsemnode; eauto).
        * specialize (Hse k1). clear - Hwcg Hnormed' Hmask Hse H10 Hbs Hdisj.
          assert (EqSts (concat ss) (map (maskv k1 r) (concat ess))) as Heq.
          { rewrite Forall2_swap_args in H10. eapply Forall2_trans_ex in Hse; eauto.
            unfold EqSts. rewrite Forall2_map_2. rewrite Forall2_map_2 in Hse.
            eapply Forall2_concat, Forall2_impl_In; [|eauto]. intros ?? _ _ (?&Hin&?&?).
            rewrite <-Forall2_map_2.
            eapply Forall_forall in Hnormed'; eauto.
            eapply sem_normalized_lexp_det in H1; eauto.
          }
          clear - Hmask Heq Hbs Hdisj. unfold EqSts in *.
          rewrite Forall2_map_2 in *. rewrite Forall2_map_1.
          eapply Forall2_impl_In; [|eauto]; intros ?? _ _ Heq'; simpl in Heq'.
          rewrite Hmask, Heq', Hbs, Hdisj. reflexivity.
        * clear - Hmask Hv H6 Hbs Hdisj. simpl in H6; rewrite app_nil_r in H6.
          assert (EqSts y (map (maskv k1 r) ys)) as Heq.
          { simpl_Forall. rewrite Forall2_swap_args in H6. eapply Forall2_trans_ex in Hv; eauto.
            unfold EqSts. simpl_Forall.
            eapply sem_var_mask, sem_var_det in H4; eauto.
          }
          clear - Hmask Heq Hbs Hdisj. unfold EqSts in *.
          rewrite Forall2_map_2 in *. rewrite Forall2_map_1.
          eapply Forall2_impl_In; [|eauto]; intros ?? _ _ Heq'; simpl in Heq'.
          rewrite Hmask, Heq', Hbs, Hdisj. reflexivity.
      + simpl_Forall. now apply LS.sem_var_history.
  Qed.

  Lemma sem_blocktoeq {PSyn prefs} :
    forall cenv out (G: @L.global PSyn prefs) H P env envo bck xr rs r eqs' b,
      LN.NormFby.normalized_block G out bck ->
      LT.wt_block G cenv bck ->
      LC.wc_block G cenv bck ->
      LC.wc_global G ->
      envs_eq env (idck cenv) ->
      (forall f xs ys,
          LCS.sem_node_ck G f xs ys ->
          NLSC.sem_node P f xs ys) ->
      LCS.sc_vars cenv H b ->
      Forall (fun xr0 => In xr0 (idck cenv)) xr ->
      block_to_equation env envo xr bck = OK eqs' ->
      Forall2 (sem_var H) (map (fun '(x, _) => Var x) xr) rs ->
      bools_ofs rs r ->
      (forall k, LCS.sem_block_ck G (mask_hist k r H) (maskb k r b) bck) ->
      NLSC.sem_equation P (LS.var_history H) b eqs'.
  Proof.
    induction bck using L.block_ind2;
      intros * Hnormed Hwt Hwc HwcG Henvs Hsemnode Hinv Hxr Heqs Hsxr Hbools Hsem;
      inv Hnormed; inv Hwt; inv Hwc; simpl in *; cases.
    - (* eq *)
      eapply sem_toeq in Heqs; eauto.
      intros k. specialize (Hsem k). inv Hsem; eauto.
    - (* reset *)
      simpl_Foralls.
      assert (exists vr, sem_var H (Var x) vr) as (vr&Hx).
      { assert (Hsem0 := Hsem 0). inv Hsem0. inv H11.
        eapply sem_var_mask_inv in H13 as (?&?&?); eauto. }
      assert (exists sr, bools_of vr sr) as (?&Hbool).
      { setoid_rewrite <-bools_of_mask with (rs:=r).
        eapply consolidate_mask with (P:=fun k sr => bools_of (maskv k r vr) sr).
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
      + inv H9. inv H1. solve_In.
      + econstructor.
        constructor; eauto. reflexivity.
      + intros k.
        specialize (@mask_disj' var_last k x0 (disj_str x1)) as (k1&k2&Hxs&Hbs&HH).
        eapply sem_block_ck_morph; simpl. 3:auto.
        2:rewrite disj_str_cons; symmetry; eauto.
        rewrite disj_str_cons; symmetry; apply HH.
        specialize (Hsem k2). inv Hsem. simpl_Foralls.
        specialize (H14 k1). simpl_Foralls.
        inv H4. eapply sem_var_mask in Hx. eapply sem_var_det in H14; eauto.
        rewrite <-H14 in H13.
        eapply bools_of_mask_det in H13; eauto.
        eapply sem_block_ck_morph. 3,4:eauto.
        1,2:rewrite H13, Hdisj; reflexivity.
  Qed.

  Lemma sem_blockstoeqs {PSyn prefs} :
    forall cenv out (G: @L.global PSyn prefs) H P env envo bcks eqs' b,
      Forall (LN.NormFby.normalized_block G out) bcks ->
      Forall (LT.wt_block G cenv) bcks ->
      Forall (LC.wc_block G cenv) bcks ->
      LC.wc_global G ->
      envs_eq env (idck cenv) ->
      (forall f xs ys,
          LCS.sem_node_ck G f xs ys ->
          NLSC.sem_node P f xs ys) ->
      LCS.sc_vars cenv H b ->
      mmap (block_to_equation env envo []) bcks = OK eqs' ->
      Forall (LCS.sem_block_ck G H b) bcks ->
      Forall (NLSC.sem_equation P (LS.var_history H) b) eqs'.
  Proof.
    induction bcks; intros * Hnormed Hwt Hwc HwcG Henvs Hsemnode Hinv Heqs Hsem;
      inv Hnormed; inv Hwt; inv Hwc; inv Hsem; simpl in *; monadInv Heqs; auto.
    - constructor; eauto.
      eapply sem_blocktoeq; eauto. simpl; constructor.
      eapply bools_ofs_empty.
      intros [|].
      + eapply sem_block_ck_morph; eauto.
        rewrite mask_hist_false_0; reflexivity.
        rewrite maskb_false_0; reflexivity.
      + eapply sem_block_ck_morph. 3:eauto. 3:eapply LCS.sem_block_absent; eauto.
        rewrite mask_hist_false_S; reflexivity.
        rewrite maskb_false_S; reflexivity.
  Qed.

  Lemma inputs_clocked_vars {PSyn prefs} :
    forall (n: @L.node PSyn prefs) H ins,
      Forall2 (fun x => sem_var H (Var x)) (L.idents (L.n_in n)) ins ->
      LCS.sc_vars (senv_of_ins (L.n_in n) ++ senv_of_decls (L.n_out n)) H (clocks_of ins) ->
      NLSC.sem_clocked_vars (LS.var_history H) (clocks_of ins) (Common.idck (Common.idty (L.n_in n))).
  Proof.
    intros * Hvs (Hsc&_).
    unfold NLSC.sem_clocked_vars. simpl_Forall. simpl_In.
    apply Forall2_ignore2 in Hvs. unfold L.idents in *. simpl_Forall.
    econstructor; solve_In; eauto with datatypes.
    2:intros; setoid_rewrite LS.sem_var_history; eauto.
    intros * Hvar.
    eapply LS.sem_var_history, Hsc in Hvar; [|econstructor; solve_In; eauto with datatypes; auto].
    2:apply in_app_iff, or_introl; solve_In.
    do 2 esplit; eauto. apply ac_aligned.
  Qed.

  Module Import TrOrdered := TrOrderedFun Ids Op OpAux Cks Senv L Lord CE NL Ord TR.

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
    intros [].
    induction nodes as [|nd]. now inversion 6.
    intros * Hnormed Hord Hwt Hwc Htr Hsem.
    destruct Hwt as (Hbool&Hwt).
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [? ? ? ? ? Hfind Hins Houts ? Slast Sblk (Hdom&Hsc)].
    pose proof (Lord.find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    inv Hnormed. destruct H2. inversion_clear H0 as [??? Hblk Hlocs Hblks].
    pose proof (L.n_syn n) as Hsyn. inversion_clear Hsyn as [?? Hsyn1 Hsyn2 _].
    inversion_clear Hwt as [|?? (?&?)].
    inversion_clear Hwc as [|?? (?&?)].
    simpl in Hfind. destruct (ident_eq_dec (L.n_name nd) f); subst.
    - rewrite L.find_node_now in Hfind; eauto. inv Hfind.
      assert (Hord':=Hord).
      inversion_clear Hord as [|? ? Hord'' Hnnblocks Hnn].
      eapply LCS.sem_node_ck_cons1' in Sblk as (Sblk'&_); eauto.
      assert (Htr':=Htr). monadInv Htr'; simpl in *; monadInv EQ.
      assert (forall f ins outs,
                 LCS.sem_node_ck (L.Global types externs nodes) f ins outs ->
                 NLSC.sem_node (NL.Global types externs x3) f ins outs) as IHnds'.
      { intros. eapply IHnodes; eauto. constructor; auto.
        unfold to_global; simpl. rewrite EQ; auto. }
      take (LT.wt_node _ _) and inversion_clear it as [?? Hwt1 Hwt2 Hwt3 _ Hwt4]; subst Γ.
      take (LC.wc_node _ _) and inversion_clear it as [?? Hwc1 Hwc2 _ Hwc3]; subst Γ.
      pose proof (L.n_nodup n) as (Hnd1&Hnd2).
      rewrite Hblk in *. inv Hnd2. inv H8. inv Sblk'. inv H10.
      assert (H ⊑ H + Hi') as Href.
      { eapply LS.local_hist_dom_refines. 3:eauto. 1,2:eauto.
        intros. rewrite IsVar_fst, map_app, map_fst_senv_of_ins, map_fst_senv_of_decls; eauto. }
      assert (sc_vars (senv_of_ins (L.n_in n) ++ senv_of_decls (L.n_out n)) (H + Hi') (clocks_of ins)) as Hsc'.
      { destruct Hsc as (Hsc1&_). split.
        - intros * Hck Hv.
          eapply LS.sem_clock_refines, Hsc1; eauto using LS.var_history_refines.
          inv Hck; simpl_In.
          apply sem_var_union in Hv as [Hv|Hv]; auto.
          exfalso. apply LS.sem_var_In, H8, IsVar_senv_of_decls in Hv.
          eapply H12; eauto. rewrite <-map_fst_senv_of_ins, <-map_fst_senv_of_decls, <-map_app. solve_In.
        - intros * _ Hl. exfalso.
          eapply NoLast_app; [|eauto]; split; eauto using senv_of_ins_NoLast.
          clear - Hsyn1. intros * L. inv L. simpl_In. simpl_Forall. subst; simpl in *; congruence.
      }
      eapply NLSC.SNode with (H:=LS.var_history (H + Hi')); simpl.
      + erewrite NL.find_node_now; eauto. erewrite <- to_node_name; eauto.
      + erewrite <- to_node_in, map_fst_idty; eauto.
        eapply Forall2_impl_In; [|eauto]; intros.
        eapply LS.sem_var_refines, LS.sem_var_history; eauto using LS.var_history_refines.
      + erewrite <- to_node_out, 2 map_fst_idty; eauto.
        eapply Forall2_impl_In; [|eauto]; intros.
        eapply LS.sem_var_refines, LS.sem_var_history; eauto using LS.var_history_refines.
      + erewrite <- to_node_in; eauto.
        eapply inputs_clocked_vars; eauto.
        unfold L.idents. simpl_Forall; eauto using LS.sem_var_refines.
      + apply NLSC.sem_equation_cons2; eauto using ord_l_nl.
        2:{ assert (Htrn' := EQ0).
            apply to_node_name in EQ0. rewrite <- EQ0.
            eapply ninin_l_nl; eauto. contradict Hnini. right; auto. }
        tonodeInv EQ0; simpl in *.
        eapply sem_blockstoeqs with (cenv:=senv_of_ins (L.n_in n) ++ senv_of_decls (L.n_out n) ++ _). 1-9:eauto.
        5:{ clear Htr. rewrite Hblk in Hmmap. monadInv Hmmap; eauto. }
        * inv Hwt4. inv H10. subst Γ'. simpl_app. eauto.
        * inv Hwc3. inv H10. subst Γ'. simpl_app. eauto.
        * apply envs_eq_node in Hblk. clear - Hblk.
          intros ??. specialize (Hblk x ck). rewrite <-Hblk.
          rewrite (Permutation_app_comm (Common.idty (Common.idty locs))).
          simpl_app. repeat rewrite in_app_iff.
          clear - n. split; (intros [|[|]]; [left|right;left|right;right]; solve_In).
        * rewrite app_assoc. apply sc_vars_app; eauto.
          intros *. rewrite fst_InMembers, map_app, map_fst_senv_of_ins, map_fst_senv_of_decls.
          intros Hin1 Hin2. eapply H12; eauto. clear - Hin2. solve_In.
    - eapply LCS.sem_node_ck_cons1 in Hsem; auto.
      assert (Htr' := Htr).
      monadInv Htr. simpl in *. monadInv EQ.
      rewrite cons_is_app in Hord.
      assert (Lord.Ordered_nodes {| L.types := types; L.externs := externs; L.nodes := nodes |}) as Hord'.
      { eapply Lord.Ordered_nodes_append in Hord; eauto.
        econstructor; simpl; eauto. 2:rewrite cons_is_app; auto.
        intros ?; simpl; auto. }
      eapply NLSC.sem_node_cons2; eauto.
      + eapply ord_l_nl with (G:=L.Global types externs nodes); auto.
        unfold to_global; simpl; rewrite EQ; simpl; auto.
      + eapply IHnodes; eauto. constructor; auto.
        unfold to_global; simpl; rewrite EQ; simpl; auto.
      + replace x3 with (NL.Global types externs x3).(NL.nodes) by auto.
        eapply TR.to_global_names with (G:=L.Global types externs nodes); simpl; eauto.
        erewrite <-to_node_name; eauto.
        unfold to_global; simpl; rewrite EQ; simpl; auto.
  Qed.

End CORRECTNESS.

Module CorrectnessFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (OpAux: OPERATORS_AUX    Ids Op)
       (Cks  : CLOCKS           Ids Op OpAux)
       (Senv : STATICENV        Ids Op OpAux Cks)
       (L    : LSYNTAX          Ids Op OpAux Cks Senv)
       (CE   : CESYNTAX         Ids Op OpAux Cks)
       (NL   : NLSYNTAX         Ids Op OpAux Cks        CE)
       (TR   : TR               Ids Op OpAux Cks Senv L      CE NL)
       (LT   : LTYPING          Ids Op OpAux Cks Senv L)
       (LC   : LCLOCKING        Ids Op OpAux Cks Senv L)
       (Ord  : NLORDERED        Ids Op OpAux Cks        CE NL)
       (Lord : LORDERED         Ids Op OpAux Cks Senv L)
       (Str  : COINDSTREAMS     Ids Op OpAux Cks)
       (LS   : LSEMANTICS       Ids Op OpAux Cks Senv L Lord       Str)
       (LCS  : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv L LC Lord Str LS)
       (LN   : NORMALIZATION    Ids Op OpAux Cks Senv L)
       (NLSC : NLCOINDSEMANTICS Ids Op OpAux Cks        CE NL Str Ord)
<: CORRECTNESS Ids Op OpAux Cks Senv L CE NL TR LT LC Ord Lord Str LS LCS LN NLSC.
  Include CORRECTNESS Ids Op OpAux Cks Senv L CE NL TR LT LC Ord Lord Str LS LCS LN NLSC.
End CorrectnessFun.
