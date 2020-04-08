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
      rewrite Forall2_map_2.
      rewrite_Forall_forall; solve_length.
      rewrite length_typeof_numstreams. eapply H0...
      + apply nth_In; congruence.
      + apply H5. apply nth_In; congruence.
    - (* when *)
      repeat rewrite_Forall_forall.
      rewrite <- H1. unfold typesof; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite Forall2_map_2.
      rewrite_Forall_forall; solve_length.
      rewrite length_typeof_numstreams. eapply H0...
      + apply nth_In; congruence.
      + apply H5. apply nth_In; congruence.
    - (* merge *)
      repeat rewrite_Forall_forall.
      rewrite <- H11. unfold typesof; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite Forall2_map_2.
      rewrite_Forall_forall; solve_length.
      rewrite length_typeof_numstreams. eapply H0...
      + apply nth_In; congruence.
      + apply H6. apply nth_In; congruence.
    - (* ite *)
      repeat rewrite_Forall_forall.
      rewrite <- H12. unfold typesof; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite Forall2_map_2.
      rewrite_Forall_forall; solve_length.
      rewrite length_typeof_numstreams.
      eapply H0...
      + apply nth_In; congruence.
      + apply H7. apply nth_In; congruence.
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
  Qed.

  Corollary sem_exps_numstreams : forall G vars H b es vs,
      Forall (wt_exp G vars) es ->
      Forall2 (sem_exp G H b) es vs ->
      length (concat vs) = length (annots es).
  Proof.
    intros G vars H b es vs Hwt Hsem.
    assert (Forall2 (fun v e => length v = numstreams e) vs es) as Hf.
    { repeat rewrite_Forall_forall.
      eapply sem_exp_numstreams.
      + eapply Hwt. eapply nth_In. solve_length.
      + eapply H1; eauto. solve_length. }
    clear Hwt Hsem.
    induction Hf; simpl.
    - reflexivity.
    - repeat rewrite app_length.
      f_equal; auto.
      rewrite length_annot_numstreams. assumption.
  Qed.

  Fact normalize_exp_sem_length : forall G vars e is_control es' eqs' st st',
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

  Definition before_st {B} (l : list ident) (st : fresh_st B) :=
    Forall (fun id => Pos.lt id (smallest_ident st)) l.

  Fact before_st_follows {B} : forall l (st st' : fresh_st B),
      fresh_st_follows st st' ->
      before_st l st ->
      before_st l st'.
  Proof.
    intros l st st' Hfollows Hbef.
    apply st_follows_smallest in Hfollows.
    unfold before_st in *.
    solve_forall.
    eapply Pos.lt_le_trans; eauto.
  Qed.
  Hint Resolve before_st_follows.

  Definition valid_after {B} (l : list ident) (st : fresh_st B) :=
    fresh_st_valid st /\ before_st l st.

  (** ** Conservation of sem_exp *)

  Fact idents_for_anns_NoDupMembers : forall anns ids st st',
      fresh_st_valid st ->
      idents_for_anns anns st = (ids, st') ->
      NoDupMembers ids.
  Proof.
    intros anns ids st st' Hvalid Hids.
    eapply idents_for_anns_st_valid in Hvalid; eauto.
    apply idents_for_anns_vars_perm in Hids.
    apply st_valid_NoDupMembers in Hvalid.
    unfold st_ids in *.
    rewrite fst_NoDupMembers in Hvalid; rewrite fst_NoDupMembers.
    rewrite <- Hids in Hvalid.
    apply NoDup_app_weaken in Hvalid; auto.
  Qed.

  Fact idents_for_anns_nIn : forall anns ids st st',
      fresh_st_valid st ->
      idents_for_anns anns st = (ids, st') ->
      Forall (fun id => ~List.In id (st_ids st)) (List.map fst ids).
  Proof.
    intros anns ids st st' Hvalid Hids.
    eapply idents_for_anns_st_valid in Hvalid; eauto.
    apply st_valid_NoDupMembers in Hvalid.
    apply idents_for_anns_vars_perm in Hids.
    unfold st_ids in *.
    rewrite fst_NoDupMembers in Hvalid.
    rewrite <- Hids in Hvalid.
    rewrite Forall_forall. intros x Hin.
    eapply NoDup_app_In; eauto.
  Qed.

  Fact map_bind2_sem : forall G vars b is_control es H vs es' eqs' st st',
      Forall (wt_exp G vars) es ->
      Forall2 (sem_exp G H b) es vs ->
      valid_after (List.map fst vars) st ->
      Env.dom H ((List.map fst vars)++(st_ids st)) ->
      Forall2 (fun e v => forall H es' eqs' st st',
                   sem_exp G H b e v ->
                   valid_after (List.map fst vars) st ->
                   Env.dom H ((List.map fst vars)++(st_ids st)) ->
                   normalize_exp is_control e st = (es', eqs', st') ->
                   (exists H',
                       Env.refines eq H H' /\
                       Env.dom H' ((List.map fst vars)++(st_ids st')) /\
                       Forall2 (fun e v => sem_exp G H' b e [v]) es' v /\
                       Forall (sem_equation G H' b) eqs')) es vs ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          Env.dom H' ((List.map fst vars)++(st_ids st')) /\
          Forall2 (fun es vs => Forall2 (fun e v => sem_exp G H' b e [v]) es vs) es' vs /\
          Forall (sem_equation G H' b) (concat eqs')).
  Proof with eauto.
    induction es; intros H vs es' eqs' st st' Hwt Hsem Hbef Hdom Hf Hmap;
      inv Hwt; inv Hsem; inv Hf; simpl in Hmap; repeat inv_bind.
    - exists H; simpl. repeat split; auto.
    - specialize (H7 _ _ _ _ _ H4 Hbef Hdom H0). destruct H7 as [H' [Href1 [Hdom1 [Hsem1 Hsem1']]]].
      assert (Forall2 (sem_exp G H' b) es l') as Hsem'.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
      assert (valid_after (List.map fst vars) x1) as Hbef1 by (destruct Hbef; constructor; eauto).
      specialize (IHes _ _ _ _ _ _ H3 Hsem' Hbef1 Hdom1 H9 H1). clear H9.
      destruct IHes as [H'' [Href2 [Hdom2 [Hsem2 Hsem2']]]].
      exists H''. repeat split; simpl...
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

  Import Permutation.
  Hint Constructors sem_exp.
  Fact normalize_exp_sem : forall G vars b e H vs is_control es' eqs' st st',
      wt_exp G vars e ->
      sem_exp G H b e vs ->
      valid_after (List.map fst vars) st ->
      Env.dom H ((List.map fst vars)++(st_ids st)) ->
      normalize_exp is_control e st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          Env.dom H' ((List.map fst vars)++(st_ids st')) /\
          Forall2 (fun e v => sem_exp G H' b e [v]) es' vs /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction e using exp_ind2; intros Hi vs is_control es' eqs' st st' Hwt Hsem Hbef Hdom Hnorm;
      inv Hwt; inv Hsem; simpl in Hnorm; repeat inv_bind.
    - (* const *)
      exists Hi. repeat split...
    - (* var *)
      exists Hi. repeat split...
    - (* unop *)
      specialize (Typ.normalize_exp_typeof _ _ _ _ _ _ _ _ H2 H) as Htypeof.
      specialize (IHe _ _ _ _ _ _ _ H2 H9 Hbef Hdom H). destruct IHe as [Hi' [Href [Hdom' [Hsem Hsem']]]].
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
      specialize (IHe1 _ _ _ _ _ _ _ H3 H10 Hbef Hdom H). destruct IHe1 as [Hi' [Href1 [Hdom1 [Hsem1 Hsem1']]]].
      eapply sem_exp_refines in H13; [| eauto].
      assert (valid_after (List.map fst vars) x1) as Hbef1 by (destruct Hbef; constructor; eauto).
      specialize (IHe2 _ _ _ _ _ _ _ H4 H13 Hbef1 Hdom1 H0). destruct IHe2 as [Hi'' [Href2 [Hdom2 [Hsem2 Hsem2']]]].
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
      eapply map_bind2_sem in H0... 2: (repeat rewrite_Forall_forall; eapply nth_In in H8; eauto).
      destruct H0 as [H' [Href [Hdom1 [Hsem1 Hsem2]]]].
      apply Forall2_concat in Hsem1.
      exists H'. repeat split; simpl...
      rewrite Forall2_map_1.
      eapply Forall2_trans_ex in H13; [| eauto].
      apply Forall2_combine_lr with (zs:=(typesof es)) in H13; auto.
      eapply Forall2_impl_In; [| eauto].
      intros; simpl in H2. destruct a. destruct H2 as [y [Hin [Hsem Hsem']]].
      econstructor...
      + eapply sem_var_refines...
      + simpl. repeat constructor...
    - (* merge *)
      specialize (sem_exps_numstreams _ _ _ _ _ _ H5 H15) as Hlength3.
      assert (fresh_st_follows st x2) as Hfollows1.
      { eapply map_bind2_st_follows in H1; eauto. solve_forall. }
      assert (valid_after (List.map fst vars) x2) as Hbef1.
      { destruct Hbef. constructor; eauto.
        eapply map_bind2_st_valid; eauto. solve_forall. }
      eapply map_bind2_sem in H1... 2:(repeat rewrite_Forall_forall; eapply nth_In in H17; eauto). clear H.
      destruct H1 as [H' [Href1 [Hdom1 [Hsem1 Hsem1']]]]. apply Forall2_concat in Hsem1.
      assert (Forall2 (sem_exp G H' b) efs fs) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
      assert (fresh_st_follows x2 x5) as Hfollows2.
      { eapply map_bind2_st_follows in H2; eauto. solve_forall. }
      assert (valid_after (List.map fst vars) x5) as Hbef2.
      { destruct Hbef1. constructor; eauto.
        eapply map_bind2_st_valid; eauto. solve_forall. }
      eapply map_bind2_sem in H2... 2:(repeat rewrite_Forall_forall; eapply nth_In in H19; eauto). clear H0.
      destruct H2 as [H'' [Href2 [Hdom2 [Hsem2 Hsem2']]]]. apply Forall2_concat in Hsem2.
      destruct is_control; repeat inv_bind.
      + (* control *)
        exists H''. repeat split; simpl...
        * etransitivity...
        * rewrite Forall2_map_1.
          repeat rewrite typesof_annots in H9.
          assert (length (annots efs) = length (annots ets)) as Hlena by (erewrite <- map_length; erewrite H9; solve_length).
          repeat rewrite_Forall_forall; solve_length.
          destruct (nth n (combine _ _) _) as [[? ?] ?] eqn:Hnth.
          destruct a as [[de de0] dt]. repeat simpl_nth.
          econstructor.
          -- apply sem_var_refines with (H:=Hi)... etransitivity...
          -- repeat econstructor.
             eapply sem_exp_refines...
          -- repeat econstructor...
          -- repeat econstructor...
        * rewrite Forall_app. split; auto.
          solve_forall. eapply sem_equation_refines...
          Unshelve. exact default_ann. 1,2:exact b0.
      + (* exp *)
        specialize (idents_for_anns_length _ _ _ _ H) as Hlength.
        remember (Env.adds (List.map fst x0) vs H'') as H'''.
        assert (Env.refines eq H'' H''') as Href3.
        { assert (Forall (fun id => ~List.In id (List.map fst vars)) (List.map fst x0)) as Hnvar.
          { assert (valid_after (List.map fst vars) st') by (destruct Hbef2; constructor; eauto).
            apply idents_for_anns_incl in H.
            solve_forall.
            eapply incl_map in H. apply H in H1. clear H.
            intro contra.
            destruct H0 as [_ H0]. unfold before_st in H0.
            rewrite Forall_forall in H0. apply H0 in contra.
            unfold idty in H1. rewrite map_map in H1. simpl in H1.
            apply smallest_ident_In in H1.
            apply (Pos.lt_irrefl x1). eapply Pos.lt_le_trans...
          }
          rewrite HeqH'''. apply Env.refines_adds.
          apply idents_for_anns_nIn in H; auto.
          rewrite Forall_forall in *. intros x1 Hin contra.
          erewrite Env.dom_use in contra; [|eauto].
          apply in_app_or in contra; destruct contra.
          + eapply Hnvar...
          + eapply H...
          + destruct Hbef2... }
        exists H'''. repeat split...
        * repeat (etransitivity; eauto).
        * apply idents_for_anns_vars_perm in H. (* Env.dom_Permutation *)
          rewrite HeqH'''.
          apply Env.dom_adds with (ids:=List.map fst x0) (vs0:=vs) in Hdom2.
          2:(repeat rewrite_Forall_forall; solve_length).
          eapply Env.dom_Permutation; [|eauto].
          symmetry. rewrite Permutation_app_comm. rewrite <- app_assoc. apply Permutation_app_head.
          rewrite Permutation_app_comm. assumption.
        * rewrite Forall2_map_1.
          repeat rewrite_Forall_forall; solve_length.
          destruct (nth _ x0 _) eqn:Hnth.
          repeat constructor. econstructor; [| reflexivity].
          destruct a. rewrite split_nth in Hnth; inv Hnth.
          rewrite split_map_fst.
          apply Env.adds_MapsTo; solve_length.
          rewrite <- fst_NoDupMembers.
          destruct Hbef2.
          apply idents_for_anns_NoDupMembers in H...
        * repeat rewrite Forall_app. repeat split.
          -- rewrite map_map; simpl.
             eapply Forall2_combine'.
             rewrite Forall2_map_1. rewrite Forall2_map_2.
             repeat rewrite_Forall_forall; solve_length.
             destruct (nth _ x0 _) eqn:Hnth1.
             destruct (nth _ (combine _ _) _) as [[? ?] ?] eqn:Hnth2; subst.
             destruct b0 as [[? ?] ?]. repeat simpl_nth.
             econstructor.
             ++ repeat constructor.
                eapply Smerge with (ts:=[[nth n (concat ts) s]]) (fs:=[[nth n (concat fs) s]]); simpl.
                ** eapply sem_var_refines; [| eauto].
                   etransitivity... etransitivity...
                ** rewrite_Forall_forall.
                   simpl in H21. destruct n0; simpl; try omega.
                   specialize (H8 e1 s _ _ _ H19 eq_refl eq_refl).
                   eapply sem_exp_refines; [| eauto]. etransitivity...
                ** rewrite_Forall_forall.
                   simpl in H21. destruct n0; simpl; try omega.
                   specialize (H8 e1 s _ _ _ H19 eq_refl eq_refl).
                   eapply sem_exp_refines; [| eauto]. etransitivity...
                ** repeat econstructor. eauto.
             ++ simpl. repeat constructor.
                econstructor.
                destruct a. rewrite split_nth in Hnth1; inv Hnth1.
                rewrite split_map_fst.
                apply Env.adds_MapsTo; solve_length. 2:reflexivity.
                rewrite <- fst_NoDupMembers.
                destruct Hbef2.
                apply idents_for_anns_NoDupMembers in H...
          -- solve_forall. repeat (eapply sem_equation_refines; eauto).
          -- solve_forall. eapply sem_equation_refines...
             Unshelve. exact default_ann. exact s.
    - (* ite *)
      specialize (sem_exp_numstreams _ _ _ _ _ _ H5 H14) as Hlength1. simpl in Hlength1.
      specialize (normalize_exp_length _ _ _ _ _ _ _ _ H5 H1) as Hlength1'. rewrite <- Hlength1 in Hlength1'. clear Hlength1.
      specialize (sem_exps_numstreams _ _ _ _ _ _ H6 H16) as Hlength3.
      assert (fresh_st_follows st x1) as Hfollows1 by eauto.
      assert (valid_after (List.map fst vars) x1) as Hbef1.
      { destruct Hbef. constructor; eauto. }
      eapply IHe in H1... clear IHe. destruct H1 as [H' [Href1 [Hdom1 [Hsem1 Hsem1']]]].
      assert (fresh_st_follows x1 x4) as Hfollows2.
      { eapply map_bind2_st_follows in H2; eauto. solve_forall. }
      assert (valid_after (List.map fst vars) x4) as Hbef2.
      { destruct Hbef1. constructor; eauto.
        eapply map_bind2_st_valid; eauto. solve_forall. }
      assert (Forall2 (sem_exp G H' b) ets ts) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
      eapply map_bind2_sem in H2... 2:(repeat rewrite_Forall_forall; eapply nth_In in H22; eauto). clear H.
      destruct H2 as [H'' [Href2 [Hdom2 [Hsem2 Hsem2']]]]. apply Forall2_concat in Hsem2.
      assert (fresh_st_follows x4 x7) as Hfollows3.
      { eapply map_bind2_st_follows in H3; eauto. solve_forall. }
      assert (valid_after (List.map fst vars) x7) as Hbef3.
      { destruct Hbef2. constructor; eauto.
        eapply map_bind2_st_valid; eauto. solve_forall. }
      assert (Forall2 (sem_exp G H'' b) efs fs) as Hsem'' by (repeat rewrite_Forall_forall; repeat (eapply sem_exp_refines; eauto)).
      eapply map_bind2_sem in H3... 2:(repeat rewrite_Forall_forall; eapply nth_In in H24; eauto). clear H0.
      destruct H3 as [H''' [Href3 [Hdom3 [Hsem3 Hsem3']]]]. apply Forall2_concat in Hsem3.
      destruct is_control; repeat inv_bind.
      + (* control *)
        exists H'''. repeat split; simpl...
        * repeat (etransitivity; eauto).
        * rewrite Forall2_map_1.
          repeat rewrite typesof_annots in H10.
          assert (length (annots efs) = length (annots ets)) as Hlena by (erewrite <- map_length; erewrite H10; solve_length).
          repeat rewrite_Forall_forall; solve_length.
          destruct (nth n (combine _ _) _) as [[? ?] ?] eqn:Hnth.
          destruct a as [[de de0] dt]. repeat simpl_nth.
          econstructor.
          -- repeat singleton_length; subst.
             specialize (H15 de b0 0 _ _ Nat.lt_0_1 eq_refl eq_refl).
             eapply sem_exp_refines with (H:=H')... etransitivity...
          -- repeat econstructor.
             eapply sem_exp_refines...
          -- repeat econstructor...
          -- repeat econstructor...
        * repeat rewrite Forall_app. repeat split; auto.
          -- solve_forall. eapply sem_equation_refines with (H:=H')... etransitivity...
          -- solve_forall. eapply sem_equation_refines with (H:=H'')...
          Unshelve. exact default_ann. 1,2:exact b0.
      + (* exp *)
        specialize (idents_for_anns_length _ _ _ _ H) as Hlength.
        remember (Env.adds (List.map fst x2) vs H''') as H''''.
        assert (Env.refines eq H''' H'''') as Href4.
        { assert (Forall (fun id => ~List.In id (List.map fst vars)) (List.map fst x2)) as Hnvar.
          { assert (valid_after (List.map fst vars) st') by (destruct Hbef3; constructor; eauto).
            apply idents_for_anns_incl in H.
            solve_forall.
            eapply incl_map in H. apply H in H1. clear H.
            intro contra.
            destruct H0 as [_ H0]. unfold before_st in H0.
            rewrite Forall_forall in H0. apply H0 in contra.
            unfold idty in H1. rewrite map_map in H1. simpl in H1.
            apply smallest_ident_In in H1.
            apply (Pos.lt_irrefl x3). eapply Pos.lt_le_trans...
          }
          rewrite HeqH''''. apply Env.refines_adds.
          apply idents_for_anns_nIn in H; auto.
          rewrite Forall_forall in *. intros x3 Hin contra.
          erewrite Env.dom_use in contra; [|eauto].
          apply in_app_or in contra; destruct contra.
          + eapply Hnvar...
          + eapply H...
          + destruct Hbef3... }
        exists H''''. repeat split...
        * repeat (etransitivity; eauto).
        * apply idents_for_anns_vars_perm in H. (* Env.dom_Permutation *)
          rewrite HeqH''''.
          apply Env.dom_adds with (ids:=List.map fst x2) (vs0:=vs) in Hdom3.
          2:(repeat rewrite_Forall_forall; solve_length).
          eapply Env.dom_Permutation; [|eauto].
          symmetry. rewrite Permutation_app_comm. rewrite <- app_assoc. apply Permutation_app_head.
          rewrite Permutation_app_comm. assumption.
        * rewrite Forall2_map_1.
          repeat rewrite_Forall_forall; solve_length.
          destruct (nth _ x2 _) eqn:Hnth.
          repeat constructor. econstructor; [| reflexivity].
          destruct a. rewrite split_nth in Hnth; inv Hnth.
          rewrite split_map_fst.
          apply Env.adds_MapsTo; solve_length.
          rewrite <- fst_NoDupMembers.
          destruct Hbef3.
          apply idents_for_anns_NoDupMembers in H...
        * repeat rewrite Forall_app. repeat split.
          -- rewrite map_map; simpl.
             eapply Forall2_combine'.
             rewrite Forall2_map_1. rewrite Forall2_map_2.
             repeat rewrite_Forall_forall; solve_length.
             destruct (nth _ x2 _) eqn:Hnth1.
             destruct (nth _ (combine _ _) _) as [[? ?] ?] eqn:Hnth2; subst.
             destruct b0 as [[? ?] ?]. repeat simpl_nth.
             econstructor.
             ++ repeat constructor.
                eapply Site with (ts:=[[nth n (concat ts) s]]) (fs:=[[nth n (concat fs) s]]); simpl.
                ** simpl in H15. repeat singleton_length; subst.
                   eapply sem_exp_refines; [| eauto].
                   etransitivity... etransitivity...
                ** rewrite_Forall_forall.
                   simpl in H25. destruct n0; simpl; try omega.
                   specialize (H9 e2 s _ _ _ H24 eq_refl eq_refl).
                   eapply sem_exp_refines; [| eauto]. etransitivity...
                ** rewrite_Forall_forall.
                   simpl in H25. destruct n0; simpl; try omega.
                   specialize (H9 e2 s _ _ _ H24 eq_refl eq_refl).
                   eapply sem_exp_refines; [| eauto]. etransitivity...
                ** repeat econstructor. eauto.
             ++ simpl. repeat constructor.
                econstructor.
                destruct a. rewrite split_nth in Hnth1; inv Hnth1.
                rewrite split_map_fst.
                apply Env.adds_MapsTo; solve_length. 2:reflexivity.
                rewrite <- fst_NoDupMembers.
                destruct Hbef3.
                apply idents_for_anns_NoDupMembers in H...
          -- solve_forall. repeat (eapply sem_equation_refines; eauto).
          -- solve_forall. eapply sem_equation_refines with (H:=H'')... etransitivity...
             Unshelve. exact default_ann. exact (hd_default []). 1,2:exact s.
  Admitted.

  (** ** Conservation of sem_equation *)

  Fact normalize_equation_sem : forall G vars H b to_cut equ eqs' st st',
      wt_equation G vars equ ->
      before_st (List.map fst vars) st ->
      Env.dom H ((List.map fst vars)++(st_ids st)) ->
      sem_equation G H b equ ->
      normalize_equation to_cut equ st = (eqs', st') ->
      (exists H', Env.refines eq H H' /\
             Env.dom H' ((List.map fst vars)++(st_ids st')) /\
             Forall (sem_equation G H' b) eqs').
  Proof.
  Admitted.

  Corollary normalize_equations_sem : forall G vars b to_cut eqs H eqs' st st',
      Forall (wt_equation G vars) eqs ->
      Forall (sem_equation G H b) eqs ->
      before_st (List.map fst vars) st ->
      Env.dom H ((List.map fst vars)++(st_ids st)) ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      (exists H', Env.refines eq H H' /\
             Env.dom H' ((List.map fst vars)++(st_ids st')) /\
             Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction eqs; intros H eqs' st st' Hwt Hsem Hbef Hdome Hnorm;
      inv Hwt; inv Hsem; simpl in Hnorm; repeat inv_bind.
    - exists H...
    - assert (fresh_st_follows st x0)...
      eapply normalize_equation_sem in H0... destruct H0 as [H' [Href1 [Hdom1 Hsem1]]].
      assert (Forall (sem_equation G H' b) eqs) by (solve_forall; eapply sem_equation_refines; eauto).
      eapply before_st_follows in Hbef...
      specialize (IHeqs _ _ _ _ H3 H0 Hbef Hdom1 H1). destruct IHeqs as [H'' [Href2 [Hdom2 Hsem2]]].
      exists H''. repeat split...
      + etransitivity...
      + eapply Forall_app. split...
        solve_forall. eapply sem_equation_refines...
  Qed.

  Lemma normalize_node_sem : forall f n G ins outs to_cut f' n',
      find_node f (proj1_sig G) = Some n ->
      sem_node (proj1_sig G) f ins outs ->
      normalize_node to_cut n G = n' ->
      find_node f' (proj1_sig G) = Some n' ->
      sem_node (proj1_sig G) f' ins outs.
  Proof with eauto.
    intros f n [G Hwt] ins outs to_cut n' f' Hfind Hsem Hnorm Hfind'; simpl in *.
    inv Hsem. rewrite Hfind in H0. inv H0.
    destruct Hwt as [? [? [? Hwt]]].
    remember (normalize_equations (PS.union to_cut (ps_from_list (List.map fst (n_out n0))))
                                  (n_eqs n0) (init_st (first_unused_ident n0))) as res.
    destruct res as [eqs' st']. symmetry in Heqres.
    (* Idée : se débarasser des flots inutiles dans l'historie issu de sem_node.
       autrement dit, réduire dom H à vars, et prouver que ça suffit à donner une sémantique à la node d'origine n;
       puis utiliser cela pour prouver que la sémantique de n est conservée par la normalisation *)
    (* eapply normalize_equations_sem in Heqres. *)
    (* specialize (normalize_equations_sem _ _ _ _ _ _ _ _ _ Hwt H3 Heqres) as [H' [Href Hsem']]. *)
    (* eapply Snode with (H:=H'); eauto; unfold normalize_node; simpl. *)
    (* - repeat rewrite_Forall_forall. *)
    (*   eapply H4 in H5... eapply sem_var_refines... *)
    (* - repeat rewrite_Forall_forall. *)
    (*   eapply H2 in H5... eapply sem_var_refines... *)
    (* - rewrite Heqres... *)
  Admitted.

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
