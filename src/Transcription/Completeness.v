From Coq Require Import String.
From Coq Require Import List.

From compcert Require Import common.Errors.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.

From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.Normalization.Normalization.

From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.

Require Import Program.Equality.

Module Type COMPLETENESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import LSyn : LSYNTAX Ids Op OpAux Cks)
       (Import Norm : NORMALIZATION Ids Op OpAux Cks LSyn)
       (Import CE : CESYNTAX Ids Op OpAux Cks)
       (NL : NLSYNTAX Ids Op OpAux Cks CE)
       (Import TR : TR Ids Op OpAux Cks LSyn CE NL).

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

  Fact to_cexp_complete : forall e,
      normalized_cexp e ->
      exists e', to_cexp e = OK e'.
  Proof with eauto.
    intros e Hnorm.
    induction e using exp_ind2; inv Hnorm;
      try solve [eapply to_lexp_complete in H as [e' He'];
                 exists (Eexp e'); unfold to_cexp; rewrite He'; simpl; eauto];
      try (solve [take (normalized_lexp _) and inv it]).
    - (* when *)
      eapply to_lexp_complete in H0 as [e' He'].
      exists (Eexp e'). unfold to_cexp. rewrite He'; simpl...
    - (* merge *)
      eapply Forall_Forall in H; eauto. clear - H.
      induction H as [|?? ((?&?&Hnormed)&H1)]; subst; simpl; eauto.
      destruct IHForall as (?&EQ); monadInv EQ.
      erewrite EQ0; clear EQ0.
      inv H1. eapply H3 in Hnormed as (?&Htoc).
      erewrite Htoc; simpl; eauto.
    - (* case *)
      eapply to_lexp_complete in H4 as (?&Htol).
      simpl; destruct cl; erewrite Htol; simpl.
      apply Forall_singl in H0. eapply H0 in H7 as (?&Htoc).
      rewrite Htoc; simpl.
      eapply Forall_Forall in H; eauto. clear - H.
      induction H as [|?? (Hnormed&H1)]; subst; simpl; eauto.
      destruct IHForall as (?&EQ); monadInv EQ.
      erewrite EQ0; clear EQ0.
      destruct x1; simpl in *; eauto.
      specialize (Hnormed _ eq_refl) as (?&?&Hnormed); subst; eauto.
      inv H1. eapply H3 in Hnormed as (?&Htoc).
      erewrite Htoc; simpl; eauto.
  Qed.

  Fact to_equation_complete {PSyn prefs} : forall (G: @global PSyn prefs) out env envo xr xs es,
      normalized_equation G out (xs, es) ->
      Forall (fun x => exists cl, find_clock env x = OK cl) xs ->
      (forall x e, envo x = Error e -> PS.In x out) ->
      exists eq', to_equation env envo xr (xs, es) = OK eq'.
  Proof with eauto.
    intros * Hnorm Hfind Henvo.
    inv Hnorm.
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
    - specialize (to_cexp_complete _ H1) as [e' He'].
      inv Hfind. destruct H2 as [cl Hcl].
      eexists; simpl.
      destruct e; try (rewrite Hcl; rewrite He'; simpl; eauto).
      inv He'.
      inv He'.
  Qed.

  Fact block_to_equation_complete {PSyn prefs} : forall (G: @global PSyn prefs) out env envo d xs xr,
      normalized_block G out d ->
      VarsDefined d xs ->
      Forall (fun x => exists cl, find_clock env x = OK cl) xs ->
      (forall x e, envo x = Error e -> PS.In x out) ->
      exists eq', block_to_equation env envo xr d = OK eq'.
  Proof with eauto.
    intros * Hnorm Hvars Hfind Henvo. revert xr xs Hvars Hfind.
    induction Hnorm; intros * Hvars Hfind; inv Hvars; simpl.
    - destruct eq. eapply to_equation_complete in H; eauto.
    - destruct ann0 as (?&?&?).
      inv H2; inv H4.
      simpl in Hfind; rewrite app_nil_r in Hfind.
      eapply IHHnorm; eauto.
  Qed.

  Corollary mmap_block_to_equation_complete {PSyn prefs} : forall (G: @global PSyn prefs) (n: @node PSyn prefs) env envo locs blks,
      n_block n = Blocal locs blks ->
      Forall (normalized_block G (ps_from_list (map fst (n_out n)))) blks ->
      Forall (fun x => exists cl, find_clock env x = OK cl) (map fst (n_out n)) ->
      (forall x e, envo x = Error e -> PS.In x (ps_from_list (map fst (n_out n)))) ->
      exists eqs', Errors.mmap (block_to_equation (Env.adds' (idty locs) env) envo nil) blks = OK eqs'.
  Proof.
    intros * Hblk Hnormed Hfind Henvo.
    pose proof (n_defd n) as (?&Hvars&Hperm). rewrite Hblk in Hvars. inv Hvars.
    assert (Forall (fun x => exists cl, find_clock (Env.adds' (idty locs) env) x = OK cl) (concat xs)) as Hfind'.
    { rewrite <-H3, Hperm.
      apply Forall_app; split; solve_forall.
      - eapply In_InMembers in H.
        unfold find_clock. cases_eqn Hfind; eauto.
        eapply Env.find_adds'_nIn in Hfind0 as (Hinm&_).
        rewrite InMembers_idty in Hinm. simpl in *. congruence.
      - destruct H0 as (?&Hfind). unfold find_clock in *; simpl in *.
        cases_eqn Hfind; subst; eauto.
        eapply Env.find_adds'_nIn in Hfind2 as (?&?). congruence.
    }
    clear Hblk Hperm H3.
    induction H1; intros; simpl in *; eauto.
    inv Hnormed. apply Forall_app in Hfind' as (?&?). simpl in *.
    eapply block_to_equation_complete in H3 as (?&Heqs1); eauto.
    eapply IHForall2 in H4 as (?&Heqs2); eauto.
    erewrite Heqs1, Heqs2; simpl; eauto.
  Qed.

  Open Scope string_scope.

  Lemma to_node_complete : forall (G: @global nolocal_top_block norm2_prefs) n,
      normalized_node G n ->
      exists n', to_node n = OK n'.
  Proof.
    intros * Hnorm. inversion_clear Hnorm as [??? Hblk Hnormed].
    unfold to_node.
    edestruct (mmap_block_to_equation_complete G n)
              with (env:=Env.adds' (idty (n_in n)) (Env.from_list (idty (n_out n))))
                   (envo := fun x => if Env.mem x (Env.from_list (idty (n_out n)))
                                  then Error (msg "output variable defined as a fby")
                                  else OK tt)
      as [? H]; eauto.
    3:{ unfold mmap_block_to_equation. destruct n; simpl in *.
        dependent destruction n_block0; inv Hblk.
        cases_eqn Hmap; eauto. congruence. }
    - rewrite Forall_forall. intros x Hin.
      eapply in_map_iff in Hin as ((?&((?&ck)&?))&(?&Hin)); subst.
      eapply in_app_weak, in_app_comm in Hin.
      exists ck; simpl. eapply envs_eq_find.
      2:erewrite In_idck_exists; eexists; erewrite In_idty_exists; eauto.
      pose proof (n_nodup n) as (Hnd&_). apply NoDupMembers_app_l in Hnd. rewrite idty_app in Hnd.
      rewrite idty_app. eapply env_eq_env_adds', env_eq_env_from_list; auto.
      apply NoDupMembers_app_r in Hnd; auto.
    - intros x e Hmem; simpl in Hmem.
      rewrite <-map_fst_idty, ps_from_list_In.
      rewrite <- fst_InMembers. rewrite <- Env.In_from_list.
      apply Env.mem_2.
      cases_eqn Hmem.
  Qed.

  Lemma to_global_complete : forall G,
      normalized_global G ->
      exists G', to_global G = OK G'.
  Proof.
    intros (?&nds).
    induction nds; intros * Hnormed; inversion_clear Hnormed as [|?? (Hnormed'&_)].
    - exists (NL.Global enums0 nil). reflexivity.
    - unfold to_global; simpl.
      eapply to_node_complete in Hnormed' as (hd'&Hton). erewrite Hton; clear Hton; simpl.
      eapply IHnds in H as (tl'&HtoG).
      monadInv HtoG; simpl in *.
      erewrite EQ; simpl; eauto.
  Qed.

  Theorem normalize_global_complete : forall G,
      wl_global G ->
      exists G'', to_global (normalize_global G) = OK G''.
  Proof.
    intros * Hwl.
    eapply to_global_complete.
    eapply normalize_global_normalized_global; eauto.
  Qed.
End COMPLETENESS.

Module CompletenessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (LSyn : LSYNTAX Ids Op OpAux Cks)
       (Norm : NORMALIZATION Ids Op OpAux Cks LSyn)
       (CE : CESYNTAX Ids Op OpAux Cks)
       (NL : NLSYNTAX Ids Op OpAux Cks CE)
       (TR : TR Ids Op OpAux Cks LSyn CE NL)
       <: COMPLETENESS Ids Op OpAux Cks LSyn Norm CE NL TR.
  Include COMPLETENESS Ids Op OpAux Cks LSyn Norm CE NL TR.
End CompletenessFun.
