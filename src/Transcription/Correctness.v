From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.

From Velus Require Import Lustre.LTyping.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import Lustre.LCausality.
From Velus Require Import Lustre.LSemantics Lustre.LClockSemantics.
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
       (LCS         : LCLOCKSEMANTICS  Ids Op OpAux L LT LC LCA Lord Str IStr LS)
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

  Hint Resolve  envs_eq_find'.

  Lemma sem_toeq :
    forall cenv G H P env envo eq eq' b,
      LT.wt_equation G (idty cenv) eq ->
      LC.wc_equation G (idck cenv) eq ->
      LC.wc_global G ->
      LCS.sc_nodes G ->
      NoDupMembers (cenv ++ L.anon_in_eq eq) ->
      wc_env (idck cenv) ->
      envs_eq env (idck cenv) ->
      (forall f xs ys,
          LS.sem_node G f xs ys ->
          LCS.sem_clock_inputs G f xs ->
          NLSC.sem_node P f xs ys) ->
      LCS.sc_var_inv (fun x => Exists (fun e => LCA.Is_free_left x e) (snd eq)) (idck cenv) H b ->
      to_equation env envo eq = OK eq' ->
      LS.sem_equation G H b eq ->
      NLSC.sem_equation P H b eq'.
  Proof.
    intros ?????? [xs [|e []]] eq' b Hwt Hwc Hwcg Hscg
           Hnodup Henv Henvs Hsemnode Hvar Htoeq Hsem; try now (inv Htoeq; cases).
    destruct e.
    - unfold to_equation in Htoeq. cases. monadInv Htoeq.
      inversion Hsem; subst. simpl_Foralls.
      eapply LCS.sc_equation in Hwc; simpl; eauto.
      econstructor; eauto.
      inv Hwt. simpl_Foralls. eapply sem_exp_caexp; eauto.
      simpl in *. rewrite app_nil_r in *. now subst.
    - unfold to_equation in Htoeq. cases. monadInv Htoeq.
      inversion Hsem. subst. simpl_Foralls.
      eapply LCS.sc_equation in Hwc; simpl; eauto.
      econstructor; eauto.
      inv Hwt. simpl_Foralls. eapply sem_exp_caexp; eauto.
      simpl in *. rewrite app_nil_r in *. now subst.
    - unfold to_equation in Htoeq. cases. monadInv Htoeq.
      inversion Hsem. subst. simpl_Foralls.
      eapply LCS.sc_equation in Hwc; simpl; eauto.
      econstructor; eauto.
      inv Hwt. simpl_Foralls. eapply sem_exp_caexp; eauto.
      simpl in *. rewrite app_nil_r in *. now subst.
    - unfold to_equation in Htoeq. cases. monadInv Htoeq.
      inversion Hsem. subst. simpl_Foralls.
      eapply LCS.sc_equation in Hwc; simpl; eauto.
      econstructor; eauto.
      inv Hwt. simpl_Foralls. eapply sem_exp_caexp; eauto.
      simpl in *. rewrite app_nil_r in *. now subst.
    - (* EFby *)
      inversion Htoeq as [Heq']. cases; monadInv Heq'. rename x1 into ck.
      assert (Hsem' := Hsem).
      inversion_clear Hsem as [ ????? Hseme Hsemv].
      inversion Hseme as [| ???? Hsef Hse]. inv Hse. simpl in Hsemv.
      rewrite app_nil_r in Hsemv.
      inversion Hsemv as [|???? Hsvar Hf2]. inv Hf2.
      assert (Hsc := Hwc). eapply LCS.sc_equation in Hsc; simpl; eauto.
      inversion_clear Hwc as [Hwce ?]. inv Hwce.
      inversion_clear Hwt as [Hwte ?]. inversion Hwte as [|?? Hwt].
      inversion Hwt as [| | | | ? ? ? ? Hwte1 | | | | | |]. inv Hwte1.
      inversion Hsef as [| | | |???????? Hse0 Hse1 Hwfby | | | | | |].
      inversion Hse1 as [|????? Hf2]. inv Hf2.
      inversion Hwfby as [|?????? Hlsf Hf Hcat]. inv Hf. rewrite app_nil_r in *.
      subst. eapply sem_exp_lexp in EQ2; eauto.
      econstructor; eauto. instantiate (1 := y1).
      apply LCS.ac_fby2 in Hlsf. rewrite <- Hlsf in Hsc.
      eapply sem_lexp_laexp; eauto.
      (* we show how to erase Whens in constants using var_fby_const *)
      inversion Hse0 as [| ????? Hf2]. inv Hf2.
      inversion Hcat as [Hx1]. rewrite app_nil_r in Hx1. subst.
      destruct H0 as (HliftO & HFin).
      inversion HFin as [|?????  Hf2 Huseless Hnil].
      inv Hf2. rewrite app_nil_r in Hnil.
      eapply var_fby_const; eauto.
    - unfold to_equation in Htoeq. cases. monadInv Htoeq.
      inversion Hsem. subst. simpl_Foralls.
      eapply LCS.sc_equation in Hwc; simpl; eauto.
      econstructor; eauto.
      inv Hwt. simpl_Foralls. eapply sem_exp_caexp; eauto.
      simpl in *. rewrite app_nil_r in *. now subst.
    - unfold to_equation in Htoeq. cases. monadInv Htoeq.
      inversion Hsem. subst. simpl_Foralls.
      eapply LCS.sc_equation in Hwc; simpl; eauto.
      econstructor; eauto.
      inv Hwt. simpl_Foralls. eapply sem_exp_caexp; eauto.
      simpl in *. rewrite app_nil_r in *. now subst.
    - unfold to_equation in Htoeq. cases. monadInv Htoeq.
      inversion Hsem. subst. simpl_Foralls.
      eapply LCS.sc_equation in Hwc; simpl; eauto.
      econstructor; eauto.
      inv Hwt. simpl_Foralls. eapply sem_exp_caexp; eauto.
      simpl in *. rewrite app_nil_r in *. now subst.
    - unfold to_equation in Htoeq. cases. monadInv Htoeq.
      inversion Hsem. subst. simpl_Foralls.
      eapply LCS.sc_equation in Hwc; simpl; eauto.
      econstructor; eauto.
      inv Hwt. simpl_Foralls. eapply sem_exp_caexp; eauto.
      simpl in *. rewrite app_nil_r in *. now subst.
    - (* Eapp *)
      simpl in Htoeq.
      cases; monadInv Htoeq.
      + (* reset *)
        unfold L.anon_in_eq, L.anon_ins in Hnodup; simpl in Hnodup; rewrite app_nil_r in Hnodup.
        inversion Hsem. subst. inv Hwt. simpl_Foralls. simpl in *. rewrite app_nil_r in *.
        take (LS.sem_exp _ _ _ _ _) and inv it.
        take (LT.wt_exp _ _ _) and inv it.
        econstructor; eauto using sem_exps_lexps.
        2:{ inv H12; auto. }
        2:{ intros k. specialize (H14 k).
            eapply Hsemnode; eauto. take (LS.sem_node _ _ _ _) and inv it.
            unfold LCS.sem_clock_inputs. esplit; esplit; split; eauto. split; eauto.
            (* now we use sc_inside *)
            destruct Hwc as (Hwc & ?& Hinxs). simpl_Foralls.
            take (LC.wc_exp _ _ _) and inv it.
            match goal with
            | H1: L.find_node _ G = Some _, H2: L.find_node _ G = Some _ |- _
              => rewrite H2 in H1; inv H1
            end.
            take (L.find_node _ _ = _) and eapply LC.wc_find_node in it
              as (?&?&?); eauto.
            eapply LCS.sc_inside_mask with (es := l); eauto.
            eapply Forall2_impl_In; eauto. intros.
            eapply LCS.sc_exp; eauto; try (now eapply Forall_forall; eauto).
            { eapply L.NoDupMembers_fresh_in'; eauto. }
            eapply LCS.sc_var_inv_weaken; eauto. intros. simpl. constructor.
            constructor. right. eapply Exists_exists; eauto.
        }

        destruct Hwc as (Hwc & ?& Hinxs). simpl_Foralls.
        take (LC.wc_exp _ _ _) and inversion_clear it
          as [| | | | | | | | | | |?????? bck sub Wce ? WIi WIo Wcr ?].
        take (Forall2 (LS.sem_exp _ _ _) _ _) and eapply LCS.sc_union_envs
          in it as (?&?&?&?& Hsc); eauto.
        2:{
          eapply Forall2_impl_In; eauto. intros ???? Hse.
          eapply LCS.sc_exp in Hse; eauto; try (now eapply Forall_forall; eauto).
          { eapply L.NoDupMembers_fresh_in'; eauto. }
          eapply LCS.sc_var_inv_weaken; eauto. simpl. intros. constructor.
          constructor. right. apply Exists_exists; eauto.
        }
        simpl in *.
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
        eapply LCS.sc_parent with (ck := bck) in Hsc.
        2:{ rewrite L.clocksof_nclocksof. eapply LC.WellInstantiated_bck; eauto.
            unfold idck. rewrite map_length. exact (L.n_ingt0 n0). }
        2:{ apply LC.WellInstantiated_parent in WIi.
            rewrite L.clocksof_nclocksof, Forall_map.
            eapply Forall_impl; eauto. now simpl. }
        assert (forall x, Is_free_in_clock x bck -> InMembers x cenv). {
          intros ? Hfr.
          destruct l0 as [| a].
          { inv WIo. take ([] = _) and symmetry in it.
            apply map_eq_nil, length_zero_iff_nil in it.
            pose (L.n_outgt0 n0). omega. }
          simpl in WIo. inv WIo. take (LC.WellInstantiated _ _ _ _) and inv it.
          eapply instck_free_bck in Hfr; eauto.
          inv Hinxs. unfold L.clock_of_nclock, stripname in *.
          eapply LCS.wc_env_free_in_clock with (vars := idck cenv) in Hfr as (?&?); eauto.
          eapply In_InMembers, InMembers_idck in H20; eauto.
        }
        eapply LCS.sc_switch_adds in Hsc; eauto.
        2:{ intros ? Hfr Hino. apply LCS.filter_anons_spec in Hino as [Hino]; eauto.
            rewrite InMembers_idck in H18; eauto. }
        eapply LCS.sc_switch_adds in Hsc; eauto.
        { intros ? Hfr Hino. eapply Ino_Forall in Hino; eauto. simpl in Hino.
          apply Exists_exists in Hino as (?&?& Hf).
          apply H17 in Hfr.
          eapply NoDupMembers_app_InMembers in Hnodup; eauto.
          eapply Hnodup, L.InMembers_fresh_in; eauto.
        }
      + (* not reset *)
        unfold L.anon_in_eq, L.anon_ins in Hnodup; simpl in Hnodup; rewrite app_nil_r in Hnodup.
        inversion Hsem. subst. inv Hwt. simpl_Foralls. simpl in *. rewrite app_nil_r in *.
        take (LS.sem_exp _ _ _ _ _) and inv it.
        (* 2: cases; monadInv Htoeq. *)
        take (LT.wt_exp _ _ _) and inv it.
        econstructor; eauto using sem_exps_lexps.
        2:{ eapply Hsemnode; eauto. take (LS.sem_node _ _ _ _) and inv it.
            unfold LCS.sem_clock_inputs. esplit; esplit; split; eauto. split; eauto.
            (* now we use sc_inside *)
            destruct Hwc as (Hwc & ?& Hinxs). simpl_Foralls.
            take (LC.wc_exp _ _ _) and inv it.
            match goal with
            | H1: L.find_node _ G = Some _, H2: L.find_node _ G = Some _ |- _
              => rewrite H2 in H1; inv H1
            end.
            take (L.find_node _ _ = _) and eapply LC.wc_find_node in it
              as (?&?&?); eauto.
            eapply LCS.sc_inside with (es := l); eauto.
            eapply Forall2_impl_In; eauto. intros.
            eapply LCS.sc_exp; eauto; try (now eapply Forall_forall; eauto).
            { eapply L.NoDupMembers_fresh_in'; eauto. }
            eapply LCS.sc_var_inv_weaken; eauto. intros. simpl. constructor.
            constructor. eapply Exists_exists; eauto.
        }

        destruct Hwc as (Hwc & ?& Hinxs). simpl_Foralls.
        take (LC.wc_exp _ _ _) and inversion_clear it
          as [| | | | | | | | | |???? bck sub Wce ? WIi WIo|].
        take (Forall2 (LS.sem_exp _ _ _) _ _) and eapply LCS.sc_union_envs
          in it as (?&?&?&?& Hsc); eauto.
        2:{
          eapply Forall2_impl_In; eauto. intros ???? Hse.
          eapply LCS.sc_exp in Hse; eauto; try (now eapply Forall_forall; eauto).
          { eapply L.NoDupMembers_fresh_in'; eauto. }
          eapply LCS.sc_var_inv_weaken; eauto. simpl. intros. constructor.
          constructor. apply Exists_exists; eauto.
        }
        simpl in *.
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
        eapply LCS.sc_parent with (ck := bck) in Hsc.
        2:{ rewrite L.clocksof_nclocksof. eapply LC.WellInstantiated_bck; eauto.
            unfold idck. rewrite map_length. exact (L.n_ingt0 n0). }
        2:{ apply LC.WellInstantiated_parent in WIi.
            rewrite L.clocksof_nclocksof, Forall_map.
            eapply Forall_impl; eauto. now simpl. }
        assert (forall x, Is_free_in_clock x bck -> InMembers x cenv). {
          intros ? Hfr.
          destruct l0 as [| a].
          { inv WIo. take ([] = _) and symmetry in it.
            apply map_eq_nil, length_zero_iff_nil in it.
            pose (L.n_outgt0 n0). omega. }
          simpl in WIo. inv WIo. take (LC.WellInstantiated _ _ _ _) and inv it.
          eapply instck_free_bck in Hfr; eauto.
          inv Hinxs. unfold L.clock_of_nclock, stripname in *.
          eapply LCS.wc_env_free_in_clock with (vars := idck cenv) in Hfr as (?&?); eauto.
          eapply In_InMembers, InMembers_idck in H15; eauto.
        }
        eapply LCS.sc_switch_adds in Hsc; eauto.
        2:{ intros ? Hfr Hino. apply LCS.filter_anons_spec in Hino as [Hino]; eauto.
            rewrite InMembers_idck in H13; eauto. }
        eapply LCS.sc_switch_adds in Hsc; eauto.
        { intros ? Hfr Hino. eapply Ino_Forall in Hino; eauto. simpl in Hino.
          apply Exists_exists in Hino as (?&?& Hf).
          apply H12 in Hfr.
          eapply NoDupMembers_app_InMembers in Hnodup; eauto.
          eapply Hnodup, L.InMembers_fresh_in; eauto.
        }
  Qed.

  Lemma sem_toeqs :
    forall G n H P env envo eqs' ins,
      Forall (LT.wt_equation G (idty (L.n_in n ++ L.n_vars n ++ L.n_out n))) (L.n_eqs n) ->
      Forall (LC.wc_equation G (idck (L.n_in n ++ L.n_vars n ++ L.n_out n))) (L.n_eqs n) ->
      LCA.node_causal n ->
      Lord.Ordered_nodes G ->
      LT.wt_global G ->
      LC.wc_global G ->
      LCS.sc_nodes G ->
      wc_env (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)) ->
      envs_eq env (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)) ->
      (forall f xs ys,
          LS.sem_node G f xs ys ->
          LCS.sem_clock_inputs G f xs ->
          NLSC.sem_node P f xs ys) ->
      LC.wc_node G n ->
      Forall2 (sem_var H) (LS.idents (L.n_in n)) ins ->
      LCS.sem_clock_inputs (n :: G) (L.n_name n) ins ->
      mmap (to_equation env envo) (L.n_eqs n) = OK eqs' ->
      Forall (LS.sem_equation G H (clocks_of ins)) (L.n_eqs n) ->
      Forall (NLSC.sem_equation P H (clocks_of ins)) eqs'.
  Proof.
    intros * Hwt Hwc Hcaus Hord Hwcg Hwtg Hscn (* Henv *) Hcenv Henvs Hnode Hwcn
                 Hins Hscin Hmmap Hsem.

    destruct Hscin as (H0 & n0 & Hfind & Hins' & Hscin).
    simpl in Hfind. rewrite ident_eqb_refl in Hfind. inv Hfind.
    destruct Hwcn as (Wcin &?&?& Hwceqs).
    eapply LCS.causal_variables in Hsem as Hvar; eauto.

    assert (Forall (fun e => NoDupMembers (L.n_in n0 ++ L.n_vars n0 ++ L.n_out n0 ++ L.anon_in_eq e)) (L.n_eqs n0)) as Hndup'.
    { rewrite Forall_forall. intros e Hin.
      assert (Hndup:=(L.n_nodup n0)).
      unfold L.anon_in_eqs in Hndup.
      repeat rewrite app_assoc. eapply L.NoDupMembers_anon_in_eq'; eauto.
      repeat rewrite <- app_assoc; eauto. }

    assert (Hvar2 := Hvar). rewrite L.n_defd in Hvar2.
    revert dependent eqs'.
    induction Hsem; intros. now inv Hmmap. apply mmap_cons in Hmmap.
    destruct Hmmap as (eq' & leq' & Heqs' & Htoeq & Hmmap). subst.
    inv Hwt. inv Hwc.
    simpl in Hvar. apply Forall_app in Hvar as [Hvar Hvar'].
    constructor. 2: take (Forall _ (_::_)) and inv it; eapply IHHsem; eauto.
    eapply sem_toeq in Htoeq; eauto.
    { inv Hndup'. repeat rewrite <- app_assoc; auto. }
    intros y Hfr ck ys Hin Hy.

    inv Hwceqs. eapply LCS.free_left_env in Hfr; eauto.
    unfold idck in Hfr.
    rewrite map_app, InMembers_app in Hfr.
    destruct Hfr as [Hini| Hinov].
    - (* input *)
      pose proof (L.n_nodup n0) as Hdup.
      apply InMembers_In in Hini as (?&?).
      unfold idck in Hin. rewrite map_app, in_app in Hin.
      destruct Hin as [Hin|Hin]. 2:{
        exfalso.
        eapply NoDupMembers_app_InMembers with (x1 := y) in Hdup.
        2: apply InMembers_idck; eapply In_InMembers; eauto.
        apply In_InMembers,InMembers_idck in Hin.
        apply Hdup. rewrite app_assoc, InMembers_app; auto.
      }
      pose proof (sem_var_env_eq _ _ _ _ Hins Hins') as Horel.

      rewrite LCS.idck_idents, Forall2_map_1 in Hins.
      rewrite Forall2_map_2 in Hscin.
      pose proof (Forall2_Forall2 _ _ _ _ Hins Hscin) as Hf2.
      pose proof (Forall2_in_left _ _ _ _ Hf2 Hin) as (?&?& Hv&?).
      simpl in *.
      eapply sem_var_det in Hy; eauto. rewrite <- Hy.
      eapply LCS.sc_switch_env; eauto.
      intros * Hfr.
      eapply Forall_forall in Horel; eauto.
      unfold LS.idents.
      eapply LCS.wc_env_free_in_clock with (ck := ck) in Wcin as (?&?); eauto.
      rewrite <- fst_InMembers, <- InMembers_idck. eauto using In_InMembers.
    - (* defined variable *)
      rewrite fst_InMembers, map_map in Hinov. simpl in Hinov.
      pose proof Hinov as Hsc; eapply Forall_forall in Hsc; eauto.
      simpl in Hsc; auto.
  Qed.

  Lemma inin_l_nl :
    forall f n n',
      to_node n = OK n' ->
      Ord.Is_node_in f (NL.n_eqs n') ->
      Lord.Is_node_in f (L.n_eqs n).
  Proof.
    intros * Htr Hord.
    destruct n'. simpl in Hord.
    tonodeInv Htr.
    clear - Hord Hmmap. revert dependent n_eqs.
    induction (L.n_eqs n); intros. inv Hmmap. inv Hord.
    apply mmap_cons in Hmmap.
    destruct Hmmap as (eq' & l' & Hneqs & Hteq & Hmmap); subst.
    inversion_clear Hord as [ ? ? Hord' |].
    - econstructor.
      destruct eq' as [| i ck x le |]; inv Hord'.
      destruct a as [ xs [|]]. inv Hteq. cases.
      destruct l0; [ idtac | inv Hteq; cases ].
      destruct e; inv Hteq; cases; monadInv H0;
        econstructor; apply Lord.INEapp2.
    - apply Exists_cons_tl. eapply IHl; eauto.
  Qed.

  Lemma ninin_l_nl :
    forall f n n',
      to_node n = OK n' ->
      ~ Lord.Is_node_in f (L.n_eqs n) ->
      ~ Ord.Is_node_in f (NL.n_eqs n').
  Proof.
    intros. intro. destruct H0. eapply inin_l_nl; eauto.
  Qed.

  Lemma ord_l_nl :
    forall G P,
      to_global G = OK P ->
      Lord.Ordered_nodes G ->
      Ord.Ordered_nodes P.
  Proof.
    intros * Htr Hord.
    revert dependent P.
    induction Hord; intros. inv Htr. constructor.
    apply mmap_cons in Htr.
    destruct Htr as (n' & P' & HP & Hton & Hmmap). subst.
    constructor; auto.
    - intros f Hin.
      assert (Lord.Is_node_in f (L.n_eqs nd)) as Hfin.
      eapply inin_l_nl; eauto.
      apply H in Hfin. destruct Hfin as [ Hf Hnds ].
      split.
      apply to_node_name in Hton. now rewrite <- Hton.
      clear - Hnds Hmmap. revert dependent P'.
      induction nds; intros; inv Hnds;
        apply mmap_cons in Hmmap;
        destruct Hmmap as (n'' & P'' & HP & Hton' & Hmmap); subst.
      constructor. now apply to_node_name.
      apply Exists_cons_tl. apply IHnds; auto.
    - apply to_node_name in Hton. rewrite <- Hton.
      monadInv Hmmap. clear - H0 H1.
      induction H1; eauto. inv H0.
      constructor. apply to_node_name in H. now rewrite <- H.
      now apply IHlist_forall2.
  Qed.

  Lemma inputs_clocked_vars :
    forall n G H f ins,
      LCS.sem_clock_inputs (n :: G) f ins ->
      L.n_name n = f ->
      wc_env (idck (L.n_in n)) ->
      Forall2 (sem_var H) (LS.idents (L.n_in n)) ins ->
      NLSC.sem_clocked_vars H (clocks_of ins) (idck (L.n_in n)).
  Proof.
    intros * (H'&n'& Hfind & Hv & Hscin) Hnf Wcin Hins.
    simpl in Hfind. rewrite <- Hnf, ident_eqb_refl in Hfind. inv Hfind.
    pose proof (sem_var_env_eq _ _ _ _ Hins Hv) as Horel.
    unfold NLSC.sem_clocked_vars, NLSC.sem_clocked_var.
    rewrite LCS.idck_idents in *. rewrite Forall2_map_1 in Hv, Hins.
    apply Forall_forall. intros (?&ck) Hin. split; intros ? Hvar.
    - rewrite Forall2_map_2 in Hscin.
      pose proof (Forall2_Forall2 _ _ _ _ Hins Hscin) as Hf2.
      pose proof (Forall2_in_left _ _ _ _ Hf2 Hin) as (s&?& Hv'&?).
      exists (abstract_clock s). split.
      eapply LCS.sc_switch_env; eauto. intros * Hfr.
      eapply Forall_forall in Horel; eauto.
      eapply LCS.wc_env_free_in_clock in Wcin as (?& Hmem); eauto.
      rewrite <- fst_InMembers. now apply In_InMembers in Hmem.
      simpl in *.
      eapply sem_var_det in Hvar; eauto. rewrite <- Hvar.
      apply ac_aligned.
    - pose proof (Forall2_in_left _ _ _ _ Hins Hin) as (?&?&?); eauto.
  Qed.

  Theorem sem_l_nl :
    forall G P f ins outs,
      Lord.Ordered_nodes G ->
      Forall LCA.node_causal G ->
      LT.wt_global G ->
      LC.wc_global G ->
      to_global G = OK P ->
      LS.sem_node G f ins outs ->
      LCS.sem_clock_inputs G f ins ->
      NLSC.sem_node P f ins outs.
  Proof.
    induction G as [|node]. now inversion 6.
    intros * Hord Hcaus Hwt Hwc Htr Hsem Hscin.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [? ? ? ? ? ? Hfind Hins Houts Heqs Hbk].
    pose proof (Lord.find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    inv Hwt. inv Hwc. inv Hcaus.
    simpl in Hfind. destruct (ident_eqb (L.n_name node) f) eqn:Hnf.
    - assert (Hord':=Hord).
      inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn].
      injection Hfind; intro HR; rewrite HR in *; clear HR; simpl in *.
      eapply LS.Forall_sem_equation_global_tl in Heqs; eauto.
      assert (Htr' := Htr). apply mmap_cons in Htr'.
      destruct Htr' as (n' & P' & Hp & Htrn & Hmmap). subst.
      assert (forall f ins outs,
                 LS.sem_node G f ins outs ->
                 LCS.sem_clock_inputs G f ins ->
                 NLSC.sem_node P' f ins outs) as IHG'
          by auto.
      apply ident_eqb_eq in Hnf. rewrite <- Hnf.
      take (LT.wt_node _ _) and inversion it as (Hwt1 & Hwt2 & Hwt3 & Hwt4).
      take (LC.wc_node _ _) and inversion it as (Hwc1 & Hwc2 & Hwc3 & Hwc4).
      econstructor; simpl.
      + tonodeInv Htrn. rewrite ident_eqb_refl; eauto.
      + tonodeInv Htrn. simpl.
        eapply Forall2_impl_In in Hins; eauto.
      + tonodeInv Htrn. simpl. eapply Forall2_impl_In in Houts; eauto.
      + erewrite <- to_node_in; eauto.
        eapply inputs_clocked_vars; eauto.
      + apply NLSC.sem_equation_cons2; auto.
        * eapply ord_l_nl; eauto.
        * assert (Hton := Htrn). tonodeInv Htrn. simpl in *.
          eapply sem_toeqs; eauto using LCS.l_sem_node_clock.
          eapply wc_env_Proper; try eassumption. unfold idck. rewrite 4 map_app.
          now apply Permutation_app_head, Permutation_app_comm.
          apply envs_eq_node.
        * assert (Htrn' := Htrn).
          apply to_node_name in Htrn. rewrite <- Htrn.
          eapply ninin_l_nl; eauto.
    - apply ident_eqb_neq in Hnf.
      eapply LS.sem_node_cons in Hsem; auto.
      eapply LCS.sem_clock_inputs_cons in Hscin; auto.
      assert (Htr' := Htr).
      apply mmap_cons in Htr.
      destruct Htr as (n' & P' & Hp & Htn & Hmmap). subst.
      rewrite cons_is_app in Hord.
      apply Lord.Ordered_nodes_append in Hord.
      eapply NLSC.sem_node_cons2; eauto.
      + eapply ord_l_nl; eauto.
      + apply to_node_name in Htn. rewrite <- Htn.
        monadInv Hmmap. clear - H0 H7.
        induction H0; eauto. inv H7.
        constructor. apply to_node_name in H. now rewrite <- H.
        now apply IHlist_forall2.
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
       (LCS   : LCLOCKSEMANTICS  Ids Op OpAux L LT LC LCA Lord Str IStr LS)
       (NLSC  : NLCOINDSEMANTICS Ids Op OpAux        CE NL Str Ord)
<: CORRECTNESS Ids Op OpAux L CE NL TR LT LC LCA Ord Lord Str IStr LS LCS NLSC.
  Include CORRECTNESS Ids Op OpAux L CE NL TR LT LC LCA Ord Lord Str IStr LS LCS NLSC.
End CorrectnessFun.
