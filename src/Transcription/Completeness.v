From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.

From compcert Require Import common.Errors.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.

From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LTyping.
From Velus Require Import Lustre.Normalization.Normalization.
From Velus Require Import Lustre.Normalization.NTyping.

From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.

From Coq Require Import Program.Equality.

Module Type COMPLETENESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Import LSyn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import LT : LTYPING Ids Op OpAux Cks Senv LSyn)
       (Import Norm : NORMALIZATION Ids Op OpAux Cks Senv LSyn)
       (Import CE : CESYNTAX Ids Op OpAux Cks)
       (NL : NLSYNTAX Ids Op OpAux Cks CE)
       (Import TR : TR Ids Op OpAux Cks Senv LSyn CE NL).

  Fact to_constant_complete : forall c,
    normalized_constant c ->
    exists e', to_constant c = OK e'.
  Proof with eauto.
    intros c Hnorm. induction Hnorm.
    - eexists; simpl...
    - eexists; simpl...
    - destruct IHHnorm as [e' He'].
      eexists; simpl...
  Qed.

  Fact to_lexp_complete : forall e,
    normalized_lexp e ->
    exists e', to_lexp e = OK e'.
  Proof with eauto.
    intros e Hnorm.
    induction e using exp_ind2; inv Hnorm.
    - (* const *) eexists; simpl...
    - (* enum *) eexists; simpl...
    - (* var *) eexists; simpl...
    - (* unop *)
      apply IHe in H0 as [e' He'].
      eexists; simpl.
      rewrite He'; simpl...
    - (* binop *)
      apply IHe1 in H1 as [e1' He1].
      apply IHe2 in H4 as [e2' He2].
      eexists; simpl.
      rewrite He1. rewrite He2. simpl...
    - (* when *)
      inv H. apply H3 in H1 as [e' He'].
      eexists; simpl.
      rewrite He'. simpl...
  Qed.

  Corollary mmap_to_lexp_complete : forall es,
      Forall normalized_lexp es ->
      exists es', Errors.mmap to_lexp es = OK es'.
  Proof with eauto.
    intros es Hf.
    induction Hf.
    - eexists; simpl...
    - apply to_lexp_complete in H as [e' He'].
      destruct IHHf as [es' Hes'].
      eexists; simpl.
      rewrite He'; rewrite Hes'. simpl...
  Qed.

  Fact to_cexp_complete {PSyn prefs} (G: @global PSyn prefs) vars : forall e,
      wt_exp G vars e ->
      normalized_cexp e ->
      exists e', to_cexp e = OK e'.
  Proof with eauto.
    intros e Hwt Hnorm.
    induction e using exp_ind2; inv Hnorm;
      try solve [eapply to_lexp_complete in H as [e' He'];
                 exists (Eexp e'); unfold to_cexp; rewrite He'; simpl; eauto];
      try (solve [take (normalized_lexp _) and inv it]).
    - (* when *)
      eapply to_lexp_complete in H0 as [e' He'].
      exists (Eexp e'). unfold to_cexp. rewrite He'; simpl...
    - (* merge *)
      inv Hwt. clear - H H1 H9.
      induction es; inv H; inv H1; inv H9; simpl; eauto.
      destruct a, H2 as (?&?&Hnormed); simpl in *; subst; auto.
      destruct IHes as (?&EQ); auto. monadInv EQ.
      erewrite EQ0; clear EQ0.
      apply Forall_singl in H1. apply Forall_singl in H3.
      eapply H3 in Hnormed as (?&Htoc); auto.
      erewrite Htoc; simpl; eauto.
    - (* case *)
      eapply to_lexp_complete in H4 as (?&Htol).
      simpl; erewrite Htol; simpl.
      assert (exists es', Errors.mmap
                       (fun pat =>
                          match pat with
                          | (i, nil) => Error (msg "control expression not normalized")
                          | (i, e0 :: nil) => do ce <- to_cexp e0; OK (i, ce)
                          | (i, e0 :: _ :: _) => Error (msg "control expression not normalized")
                          end) es = OK es') as (?&Htoces).
      { assert (Forall (fun es => Forall (wt_exp G vars) (snd es)) es) as Hwt' by (inv Hwt; auto).
        clear - H Hwt' H6.
        induction es; inv H; inv Hwt'; inv H6; simpl; eauto.
        destruct a, H5 as (?&?&Hnormed); simpl in *; subst; auto.
        destruct IHes as (?&EQ); auto.
        erewrite EQ; clear EQ.
        apply Forall_singl in H1. apply Forall_singl in H2.
        eapply H2 in Hnormed as (?&Htoc); auto.
        erewrite Htoc; simpl; eauto. }
      rewrite Htoces; simpl.
      inv Hwt; simpl in *; eauto.
      specialize (H7 _ eq_refl) as (?&Heq&?); inv Heq.
      apply Forall_singl in H16.
      apply Forall_singl in H0 as (?&Htod); auto.
      rewrite Htod, H9. destruct tn; simpl; eauto.
  Qed.

  Fact to_equation_complete {PSyn prefs} (G: @global PSyn prefs) vars : forall out env envo xr xs es,
      wt_equation G vars (xs, es) ->
      normalized_equation G out (xs, es) ->
      Forall (fun x => exists cl, find_clock env x = OK cl) xs ->
      (forall x e, envo x = Error e -> PS.In x out) ->
      exists eq', to_equation env envo xr (xs, es) = OK eq'.
  Proof with eauto.
    intros * Hwt Hnorm Hfind Henvo.
    inv Hnorm. inv Hwt.
    - apply mmap_to_lexp_complete in H1 as [es' Hes'].
      apply vars_of_Some in H5 as (?&Vars).
      eexists; simpl. rewrite Hes', Vars; simpl...
    - apply to_constant_complete in H3 as [e0' He0'].
      apply to_lexp_complete in H4 as [e' He'].
      inv Hfind. destruct H2 as [? Hck].
      eexists; simpl.
      rewrite He0', He', Hck; simpl...
      specialize (Henvo x).
      destruct (envo x); simpl...
      exfalso...
    - inv Hwt. simpl_Forall. inv H4.
      eapply mmap_to_lexp_complete in H1 as (?&Hes).
      esplit. rewrite Hes; simpl; eauto.
    - inv Hwt. inv H.
      eapply to_cexp_complete in H1 as (?&He'); eauto.
      inv Hfind. destruct H2 as [cl Hcl].
      eexists; simpl.
      destruct e; try (rewrite Hcl; rewrite He'; simpl; eauto).
      all:inv He'.
  Qed.

  Fact block_to_equation_complete {PSyn prefs} (G: @global PSyn prefs) vars : forall out env envo blk xs xr,
      wt_block G vars blk ->
      normalized_block G out blk ->
      VarsDefinedComp blk xs ->
      Forall (fun x => exists cl, find_clock env x = OK cl) xs ->
      (forall x e, envo x = Error e -> PS.In x out) ->
      exists eq', block_to_equation env envo xr blk = OK eq'.
  Proof with eauto.
    intros * Hwt Hnorm Hvars Hfind Henvo. revert xr xs Hvars Hfind.
    induction Hnorm; intros * Hvars Hfind; inv Hwt; inv Hvars; simpl.
    - destruct eq. eapply to_equation_complete in H; eauto.
    - destruct ann0 as (?&?).
      simpl_Forall.
      simpl in Hfind; rewrite app_nil_r in Hfind.
      eapply IHHnorm; eauto.
  Qed.

  Corollary mmap_block_to_equation_complete {prefs} : forall (G: @global nolocal prefs) (n: @node nolocal prefs) env envo locs blks,
      n_block n = Blocal (Scope locs blks) ->
      Forall (fun '(_, (_, _, _, o)) => o = None) locs ->
      wt_node G n ->
      Forall (normalized_block G (ps_from_list (map fst (n_out n)))) blks ->
      Forall (fun x => exists cl, find_clock env x = OK cl) (map fst (n_out n)) ->
      (forall x e, envo x = Error e -> PS.In x (ps_from_list (map fst (n_out n)))) ->
      exists eqs', Errors.mmap (block_to_equation (Env.adds' (idty (idty locs)) env) envo nil) blks = OK eqs'.
  Proof.
    intros * Hblk Hlocs Hwtn Hnormed Hfind Henvo.
    pose proof (n_syn n) as Syn. inversion_clear Syn as [?? _ _ (?&Hvars&Hperm)].
    rewrite Hblk in Hvars. inv Hvars; inv H0; inv_VarsDefined.
    assert (Forall (fun x => exists cl, find_clock (Env.adds' (idty (idty locs)) env) x = OK cl) (concat x0)) as Hfind'.
    { rewrite Hperm0.
      apply Forall_app; split; simpl_Forall; subst.
      - rewrite Hperm in H; simpl_In; simpl_Forall.
        unfold find_clock in *; simpl in *.
        cases_eqn Hfind; subst; eauto.
        eapply Env.find_adds'_nIn in Hfind1 as (?&?). congruence.
      - apply In_InMembers in H.
        unfold find_clock. cases_eqn Hfind; eauto.
        eapply Env.find_adds'_nIn in Hfind0 as (Hinm&_).
        rewrite 2 InMembers_idty in Hinm. congruence.
    }
    inversion_clear Hwtn as [?? _ _ _ _ Hwt]. rewrite Hblk in Hwt. inv Hwt; inv H1. subst Γ Γ'.
    clear Hblk Hperm0.
    induction Hvars; intros; simpl in *; eauto. simpl_Forall.
    apply Forall_app in Hfind' as (?&?). simpl in *.
    eapply block_to_equation_complete in H4 as (?&Heqs1); eauto.
    eapply IHHvars in H8 as (?&Heqs2); eauto.
    erewrite Heqs1, Heqs2; simpl; eauto.
  Qed.

  Open Scope string_scope.

  Lemma to_node_complete : forall (G: @global nolocal norm2_prefs) n,
      wt_node G n ->
      normalized_node G n ->
      exists n', to_node n = OK n'.
  Proof.
    intros * Hwtn Hnorm. inversion_clear Hnorm as [??? Hblk ? Hnormed].
    unfold to_node.
    edestruct (mmap_block_to_equation_complete G n)
              with (env:=Env.adds' (idty (n_in n)) (Env.from_list (idty (idty (n_out n)))))
                   (envo := fun x => if Env.mem x (Env.from_list (idty (idty (n_out n))))
                                  then Error (msg "output variable defined as a fby")
                                  else OK tt)
      as [? ?]; eauto.
    3:{ unfold mmap_block_to_equation. destruct n; simpl in *.
        dependent destruction n_block0; inv Hblk.
        cases_eqn Hmap; eauto. congruence. }
    - simpl_Forall. simpl_In.
      exists c; simpl. eapply envs_eq_find. eapply env_eq_env_adds', env_eq_env_from_list.
      1,2:rewrite fst_NoDupMembers. rewrite map_app. 1,2:repeat rewrite map_fst_idty.
      + eapply n_nodup.
      + eapply NoDup_app_r, n_nodup.
      + rewrite idck_app. apply in_app_iff, or_intror. solve_In.
    - intros x e Hmem; simpl in Hmem.
      rewrite <-2 map_fst_idty, ps_from_list_In.
      rewrite <- fst_InMembers. rewrite <- Env.In_from_list.
      apply Env.mem_2.
      cases_eqn Hmem.
  Qed.

  Lemma to_global_complete : forall G,
      wt_global G ->
      normalized_global G ->
      exists G', to_global G = OK G'.
  Proof.
    intros [] (_&Hwt). revert Hwt.
    induction nodes0; intros * Hwt Hnormed;
      inversion_clear Hnormed as [|?? (Hnormed'&_)];
      inversion_clear Hwt as [|?? (?&?)]; simpl in *.
    - exists (NL.Global types0 externs0 []). reflexivity.
    - unfold to_global; simpl.
      eapply to_node_complete in Hnormed' as (hd'&Hton); auto.
      erewrite Hton; clear Hton; simpl.
      eapply IHnodes0 in H as (tl'&HtoG); auto.
      monadInv HtoG; simpl in *.
      erewrite EQ; simpl; eauto.
  Qed.

  Module NTyping := NTypingFun Ids Op OpAux Cks Senv LSyn LT Norm.

  Theorem normalize_global_complete : forall G,
      wt_global G ->
      exists G'', to_global (normalize_global G) = OK G''.
  Proof.
    intros * Hwt.
    eapply to_global_complete; eauto using NTyping.normalize_global_wt.
    eapply normalize_global_normalized_global; eauto with ltyping.
  Qed.
End COMPLETENESS.

Module CompletenessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (LSyn : LSYNTAX Ids Op OpAux Cks Senv)
       (LT : LTYPING Ids Op OpAux Cks Senv LSyn)
       (Norm : NORMALIZATION Ids Op OpAux Cks Senv LSyn)
       (CE : CESYNTAX Ids Op OpAux Cks)
       (NL : NLSYNTAX Ids Op OpAux Cks CE)
       (TR : TR Ids Op OpAux Cks Senv LSyn CE NL)
       <: COMPLETENESS Ids Op OpAux Cks Senv LSyn LT Norm CE NL TR.
  Include COMPLETENESS Ids Op OpAux Cks Senv LSyn LT Norm CE NL TR.
End CompletenessFun.
