From Coq Require Import List.

From compcert Require Import common.Errors.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.

From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LCausality.
From Velus Require Import Lustre.Normalization.Normalization.

From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.

Module Type COMPLETENESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import LSyn : LSYNTAX Ids Op)
       (Import LCau : LCAUSALITY Ids Op LSyn)
       (Import Norm : NORMALIZATION Ids Op OpAux LSyn LCau)
       (Import CE : CESYNTAX Op)
       (NL : NLSYNTAX Ids Op CE)
       (Import TR : TR Ids Op OpAux LSyn CE NL).

  Fact to_constant_complete : forall c,
    normalized_constant c ->
    exists e', to_constant c = OK e'.
  Proof with eauto.
    intros c Hnorm. induction Hnorm.
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
      exists es', mmap to_lexp es = OK es'.
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
      try (eapply to_lexp_complete in H as [e' He'];
           exists (Eexp e'); unfold to_cexp; rewrite He'; simpl; eauto);
      try (solve [inv H1]); try (solve [inv H2]).
    - (* when *)
      eapply to_lexp_complete in H0 as [e' He'].
      exists (Eexp e'). unfold to_cexp. rewrite He'; simpl...
    - (* merge *)
      inv H. inv H0.
      apply H4 in H3 as [et' Het'].
      apply H2 in H6 as [ef' Hef'].
      eexists. simpl.
      rewrite Het'. rewrite Hef'. simpl...
    - (* ite *)
      inv H. inv H0.
      apply to_lexp_complete in H4 as [e' He'].
      apply H3 in H6 as [et' Het'].
      apply H2 in H7 as [ef' Hef'].
      eexists; simpl.
      rewrite He'. rewrite Het'. rewrite Hef'. simpl...
  Qed.

  Fact to_equation_complete : forall G xs es out env envo,
      normalized_equation G out (xs, es) ->
      Forall (fun x => exists cl, find_clock env x = OK cl) xs ->
      (forall x e, envo x = Error e -> PS.In x out) ->
      exists eq', to_equation env envo (xs, es) = OK eq'.
  Proof with eauto.
    intros * Hnorm Hfind Henvo.
    inv Hnorm.
    - apply mmap_to_lexp_complete in H1 as [es' Hes'].
      apply vars_of_Some in H5 as (?&Vars).
      eexists; simpl. rewrite Hes', Vars; simpl...
    - apply to_constant_complete in H2 as [e0' He0'].
      apply to_lexp_complete in H4 as [e' He'].
      inv Hfind. destruct H2 as [? Hck].
      eapply vars_of_Some in H5 as (?&Vars).
      eexists; simpl.
      rewrite He0', He', Hck, Vars; simpl...
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

  Corollary mmap_to_equation_complete : forall G eqs out env envo,
      Forall (normalized_equation G out) eqs ->
      Forall (fun x => exists cl, find_clock env x = OK cl) (vars_defined eqs) ->
      (forall x e, envo x = Error e -> PS.In x out) ->
      exists eqs', mmap (to_equation env envo) eqs = OK eqs'.
  Proof.
    induction eqs; intros * Hnorm Hfind Henvo; simpl.
    - eexists; eauto.
    - inv Hnorm. destruct a.
      simpl in Hfind. rewrite Forall_app in Hfind. destruct Hfind as [Hfind1 Hfind2].
      specialize (to_equation_complete _ _ _ _ _ _ H1 Hfind1 Henvo) as [eq' Heq'].
      eapply IHeqs in H2; eauto. destruct H2 as [eqs' Heqs'].
      rewrite Heqs'; rewrite Heq'; eexists; simpl; eauto.
  Qed.

  Corollary mmap_to_equation_complete' : forall G n out env envo,
      Forall (normalized_equation G out) (n_eqs n) ->
      Forall (fun x => exists cl, find_clock env x = OK cl) (vars_defined (n_eqs n)) ->
      (forall x e, envo x = Error e -> PS.In x out) ->
      exists eqs', mmap_to_equation env envo n = OK eqs'.
  Proof.
    intros * Hnorm Hfind Henvo.
    eapply mmap_to_equation_complete in Hnorm; eauto.
    destruct Hnorm as [eqs' Heqs'].
    exists (exist (fun neqs : list NL.equation => _) eqs' Heqs').
    unfold mmap_to_equation. rewrite Heqs'. reflexivity.
  Qed.

  Lemma to_node_complete : forall G n Hpref,
      normalized_node G n ->
      exists n', to_node n Hpref = OK n'.
  Proof.
    intros * Hnorm.
    unfold to_node.
    edestruct mmap_to_equation_complete' as [[? ?] H].
    4: (rewrite H; eauto).
    - unfold normalized_node in Hnorm. eassumption.
    - specialize (n_defd n) as Hperm.
      rewrite Forall_forall. intros x Hin.
      eapply Permutation.Permutation_in in Hperm; eauto. clear Hin.
      rewrite in_map_iff in Hperm; destruct Hperm as [[? [? ?]] [? Hin]]; simpl in H; subst.
      erewrite envs_eq_find with (ck:=c); simpl; eauto.
      + apply envs_eq_node.
      + rewrite In_idck_exists.
        exists t. repeat rewrite in_app_iff in *.
        destruct Hin; auto.
    - intros x e Hmem; simpl in Hmem.
      rewrite ps_from_list_In.
      rewrite <- fst_InMembers. rewrite <- Env.In_from_list.
      apply Env.mem_2.
      destruct (Env.mem x (Env.from_list (n_out n))); congruence.
  Qed.

  Lemma to_global_complete : forall G Hprefs,
      normalized_global G ->
      exists G', to_global G Hprefs = OK G'.
  Proof.
    induction G; intros * Hnormed; inv Hnormed.
    - exists nil. reflexivity.
    - unfold to_global; simpl.
      eapply to_node_complete in H1 as (hd'&Hton). erewrite Hton; clear Hton; simpl.
      eapply IHG in H2 as (tl'&HtoG). erewrite HtoG; clear HtoG; simpl.
      eauto.
  Qed.

  Theorem normalize_global_complete : forall G G' Hwl Hprefs Hprefs',
      normalize_global G Hwl Hprefs = OK G' ->
      exists G'', to_global G' Hprefs' = OK G''.
  Proof.
    intros * Hnorm.
    eapply to_global_complete.
    eapply normalize_global_normalized_global; eauto.
  Qed.
End COMPLETENESS.

Module CompletenessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (LSyn : LSYNTAX Ids Op)
       (LCau : LCAUSALITY Ids Op LSyn)
       (Norm : NORMALIZATION Ids Op OpAux LSyn LCau)
       (CE : CESYNTAX Op)
       (NL : NLSYNTAX Ids Op CE)
       (TR : TR Ids Op OpAux LSyn CE NL)
       <: COMPLETENESS Ids Op OpAux LSyn LCau Norm CE NL TR.
  Include COMPLETENESS Ids Op OpAux LSyn LCau Norm CE NL TR.
End CompletenessFun.
