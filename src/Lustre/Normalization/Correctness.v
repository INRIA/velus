From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Omega.

From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LSemantics.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.
From Velus Require Import Lustre.Normalization.NTyping.

(** * Correctness of the Normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type CORRECTNESS
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str : COINDSTREAMS Op OpAux)
       (Import Syn : LSYNTAX Ids Op)
       (Import Typ : LTYPING Ids Op Syn)
       (Lord : LORDERED Ids Op Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Syn Lord Str)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn Typ).

  Import Fresh Tactics.
  Module Typ := NTypingFun Ids Op OpAux Syn Typ Norm.
  Import Typ.

  Fact sem_exp_numstreams : forall G vars H b e v,
      wt_exp G vars e ->
      sem_exp G H b e v ->
      length v = numstreams e.
  Proof with eauto.
    induction e using exp_ind2; intros v Hsem Hwt; inv Hwt; inv Hsem; simpl; auto.
    - (* fby *)
      repeat rewrite_Forall_forall.
      rewrite <- H11.
      replace (length a) with (length (List.map fst a)) by (rewrite map_length; reflexivity).
      rewrite <- H9. unfold typesof; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite_Forall_forall; solve_length.
      erewrite map_nth'; solve_length. rewrite length_typeof_numstreams.
      eapply H0...
      + apply nth_In; congruence.
      + apply H5. apply nth_In; congruence.
    - (* when *)
      repeat rewrite_Forall_forall.
      rewrite <- H1. unfold typesof; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite_Forall_forall; solve_length.
      erewrite map_nth'. rewrite length_typeof_numstreams.
      eapply H0...
      + apply nth_In; congruence.
      + apply H5. apply nth_In; congruence.
      + congruence.
    - (* merge *)
      repeat rewrite_Forall_forall.
      rewrite <- H11. unfold typesof; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite_Forall_forall; solve_length.
      erewrite map_nth'. rewrite length_typeof_numstreams.
      eapply H0...
      + apply nth_In; congruence.
      + apply H6. apply nth_In; congruence.
      + congruence.
    - (* ite *)
      repeat rewrite_Forall_forall.
      rewrite <- H12. unfold typesof; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite_Forall_forall; solve_length.
      erewrite map_nth'. rewrite length_typeof_numstreams.
      eapply H0...
      + apply nth_In; congruence.
      + apply H7. apply nth_In; congruence.
      + congruence.
    - (* app *)
      destruct H11.
      rewrite H3 in H6; clear H3; inv H6.
      repeat rewrite_Forall_forall.
      unfold idents in H11.
      solve_length.
    - (* app (reset) *)
      specialize (H13 0). inv H13.
      rewrite H3 in H7; clear H3; inv H7.
      repeat rewrite_Forall_forall.
      unfold idents in H5.
      solve_length.
      Unshelve. 1,2,3,4:exact (hd_default []).
  Qed.

  Corollary normalize_exp_sem_length : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (fun e => forall v H b,
                  sem_exp G H b e v ->
                  length v = 1) es'.
  Proof.
    intros G vars e is_control es' eqs' st st' Hwt Hnorm.
    specialize (normalize_exp_numstreams _ _ _ _ _ _ Hnorm) as Hnumstreams.
    specialize (Typ.normalize_exp_wt_exp _ _ _ _ _ _ _ _ Hwt Hnorm) as Hwt'.
    repeat rewrite_Forall_forall.
    specialize (Hnumstreams _ H). specialize (Hwt' _ H).
    rewrite <- Hnumstreams.
    eapply sem_exp_numstreams; eauto.
  Qed.

  (** ** Conservation of sem_exp *)

  Fact map_bind2_sem : forall G vars b is_control es H vs es' eqs' st st',
      Forall (wt_exp G vars) es ->
      Forall2 (sem_exp G H b) es vs ->
      Forall2 (fun e v => forall H es' eqs' st st',
                   sem_exp G H b e v ->
                   normalize_exp is_control e st = (es', eqs', st') ->
                   (exists H',
                       Env.refines eq H H' /\
                       Forall2 (fun e v => sem_exp G H' b e [v]) es' v /\
                       Forall (sem_equation G H' b) eqs')) es vs ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          Forall2 (fun es vs => Forall2 (fun e v => sem_exp G H' b e [v]) es vs) es' vs /\
          Forall (sem_equation G H' b) (concat eqs')).
  Proof with eauto.
    induction es; intros H vs es' eqs' st st' Hwt Hsem Hf Hmap;
      inv Hwt; inv Hsem; inv Hf; simpl in Hmap; repeat inv_bind.
    - exists H; simpl. repeat split; auto.
    - specialize (H7 _ _ _ _ _ H4 H0). destruct H7 as [H' [Href1 [Hsem1 Hsem1']]].
      assert (Forall2 (sem_exp G H' b) es l') as Hsem'.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
      specialize (IHes _ _ _ _ _ _ H3 Hsem' H9 H1). clear H9.
      destruct IHes as [H'' [Href2 [Hsem2 Hsem2']]].
      exists H''. repeat split; simpl.
      + etransitivity...
      + constructor; eauto. subst.
        specialize (normalize_exp_length _ _ _ _ _ _ _ _ H2 H0) as Hlength1.
        specialize (sem_exp_numstreams _ _ _ _ _ _ H2 H4) as Hlength2.
        specialize (normalize_exp_sem_length _ _ _ _ _ _ _ _ H2 H0) as Hnormlength.
        repeat rewrite_Forall_forall.
        eapply sem_exp_refines; eauto.
      + apply Forall_app. split...
        solve_forall. eapply sem_equation_refines...
  Qed.

  Hint Constructors sem_exp.
  Fact normalize_exp_sem : forall G vars b e H v is_control es' eqs' st st',
      wt_exp G vars e ->
      sem_exp G H b e v ->
      normalize_exp is_control e st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          Forall2 (fun e v => sem_exp G H' b e [v]) es' v /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction e using exp_ind2; intros Hi v is_control es' eqs' st st' Hwt Hsem Hnorm;
      inv Hwt; inv Hsem; simpl in Hnorm; repeat inv_bind.
    - (* const *)
      exists Hi. repeat split...
    - (* var *)
      exists Hi. repeat split...
    - (* unop *)
      specialize (Typ.normalize_exp_typeof _ _ _ _ _ _ _ _ H2 H) as Htypeof.
      specialize (IHe _ _ _ _ _ _ _ H2 H9 H). destruct IHe as [Hi' [Href [Hsem Hsem']]].
      assert (numstreams e = 1) by (rewrite <- length_typeof_numstreams; rewrite H3; reflexivity).
      eapply normalize_exp_length in H... rewrite H0 in H.
      repeat singleton_length. inv Hsem. clear H10.
      exists Hi'.
      repeat split...
      repeat econstructor... congruence.
    - (* binop *)
      specialize (Typ.normalize_exp_typeof _ _ _ _ _ _ _ _ H3 H) as Htypeof1.
      specialize (Typ.normalize_exp_typeof _ _ _ _ _ _ _ _ H4 H0) as Htypeof2.
      assert (numstreams e1 = 1) by (rewrite <- length_typeof_numstreams; rewrite H15; reflexivity).
      assert (numstreams e2 = 1) by (rewrite <- length_typeof_numstreams; rewrite H16; reflexivity).
      specialize (IHe1 _ _ _ _ _ _ _ H3 H10 H). destruct IHe1 as [Hi' [Href1 [Hsem1 Hsem1']]].
      eapply sem_exp_refines in H13; [| eauto].
      specialize (IHe2 _ _ _ _ _ _ _ H4 H13 H0). destruct IHe2 as [Hi'' [Href2 [Hsem2 Hsem2']]].
      eapply normalize_exp_length in H... rewrite H1 in H.
      eapply normalize_exp_length in H0... rewrite H2 in H0.
      repeat singleton_length; subst.
      inv Hsem1. inv Hsem2. clear H14 H19.
      rewrite H5 in H15; inv H15. rewrite H6 in H16; inv H16.
      exists Hi''.
      repeat split...
      repeat econstructor...
      + apply Href1 in H. destruct H as [? [? H]]; subst.
        apply Href2 in H. destruct H as [? [? H]]; subst...
      + repeat econstructor...
        * eapply sem_exp_refines...
        * congruence.
        * congruence.
      + rewrite Forall_app. split...
        solve_forall. eapply sem_equation_refines...
    - (* fby *)
      admit.
    - (* when *)
      specialize (map_bind2_normalize_exp_length _ _ _ _ _ _ _ _ H4 H0) as Hlength.
      erewrite <- (map_length _ (annots es)) in Hlength. erewrite <- typesof_annots in Hlength.
      eapply map_bind2_sem in H0...
      + destruct H0 as [H' [Href [Hsem1 Hsem2]]].
        apply Forall2_concat in Hsem1.
        exists H'. repeat split; simpl...
        repeat rewrite_Forall_forall; simpl; solve_length.
        repeat Typ.simpl_nth. Unshelve. 2: exact (hd_default [], Op.bool_type).
        destruct (nth n _) eqn:Hnth. Typ.simpl_nth.
        econstructor.
        * repeat constructor.
          eapply H1...
        * eapply sem_var_refines; eauto.
        * simpl. repeat constructor.
          eapply H3...
      + repeat rewrite_Forall_forall.
        eapply nth_In in H8...
  Admitted.

  (** ** Conservation of sem_equation *)

  Fact normalize_equation_sem : forall G vars H b to_cut equ eqs' st st',
      wt_equation G vars equ ->
      sem_equation G H b equ ->
      normalize_equation to_cut equ st = (eqs', st') ->
      (exists H', Env.refines eq H H' /\
             Forall (sem_equation G H' b) eqs').
  Proof.
  Admitted.

  Corollary normalize_equations_sem : forall G vars b to_cut eqs H eqs' st st',
      Forall (wt_equation G vars) eqs ->
      Forall (sem_equation G H b) eqs ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      (exists H', Env.refines eq H H' /\
             Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction eqs; intros H eqs' st st' Hwt Hsem Hnorm;
      inv Hwt; inv Hsem; simpl in Hnorm; repeat inv_bind.
    - exists H...
    - eapply normalize_equation_sem in H0... destruct H0 as [H' [Href1 Hsem1]].
      assert (Forall (sem_equation G H' b) eqs) by (solve_forall; eapply sem_equation_refines; eauto).
      specialize (IHeqs _ _ _ _ H3 H0 H1). destruct IHeqs as [H'' [Href2 Hsem2]].
      exists H''. split.
      + etransitivity...
      + eapply Forall_app. split...
        solve_forall. eapply sem_equation_refines...
  Qed.

  Lemma normalize_node_sem : forall f n G Hwt ins outs to_cut f' n',
      find_node f G = Some n ->
      sem_node G f ins outs ->
      normalize_node to_cut n (ex_intro _ G Hwt) = n' ->
      find_node f' G = Some n' ->
      sem_node G f' ins outs.
  Proof with eauto.
    intros f n G Hwt ins outs to_cut n' f' Hfind Hsem Hnorm Hfind'; simpl in *.
    inv Hsem. rewrite Hfind in H0. inv H0.
    destruct Hwt as [? [? [? Hwt]]].
    remember (normalize_equations (PS.union to_cut (ps_from_list (List.map fst (n_out n0))))
                                  (n_eqs n0) (init_st (first_unused_ident n0))) as res.
    destruct res as [eqs' st']. symmetry in Heqres.
    specialize (normalize_equations_sem _ _ _ _ _ _ _ _ _ Hwt H3 Heqres) as [H' [Href Hsem']].
    eapply Snode with (H:=H'); eauto; unfold normalize_node; simpl.
    - repeat rewrite_Forall_forall.
      eapply H4 in H5... eapply sem_var_refines...
    - repeat rewrite_Forall_forall.
      eapply H2 in H5... eapply sem_var_refines...
    - rewrite Heqres...
  Qed.

End CORRECTNESS.

Module CorrectnessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str : COINDSTREAMS Op OpAux)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn)
       (Lord : LORDERED Ids Op Syn)
       (Sem : LSEMANTICS Ids Op OpAux Syn Lord Str)
       (Norm : NORMALIZATION Ids Op OpAux Syn Typ)
       <: CORRECTNESS Ids Op OpAux Str Syn Typ Lord Sem Norm.
  Include CORRECTNESS Ids Op OpAux Str Syn Typ Lord Sem Norm.
  Module Typing := NTypingFun Ids Op OpAux Syn Typ Norm.
End CorrectnessFun.
