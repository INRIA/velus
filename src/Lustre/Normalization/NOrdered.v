From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

(** * Conservation of order through normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type NORDERED
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Ord : LORDERED Ids Op Syn)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn).

  Import Fresh Tactics.

  (** ** Conservation of Is_node_in *)

  Fact map_bind2_Is_node_in : forall f (k : exp -> FreshAnn (list exp * list equation)) es es' eqs' st st',
      Forall wl_exp es ->
      map_bind2 k es st = (es', eqs', st') ->
      Forall (fun e => forall es' eqs' st st',
                  k e st = (es', eqs', st') ->
                  (List.Exists (Is_node_in_exp f) es' \/ Is_node_in f eqs') ->
                  Is_node_in_exp f e) es ->
      (List.Exists (Is_node_in_exp f) (concat es') \/ Is_node_in f (concat eqs')) ->
      List.Exists (Is_node_in_exp f) es.
  Proof with eauto.
    intros f k es es' eqs' st st' Hwl Hmap Hf Hisin.
    eapply map_bind2_values in Hmap.
    repeat rewrite_Forall_forall.
    destruct Hisin.
    - eapply Exists_concat_nth' in H2. destruct H2 as [n [Hlen Hex]].
      rewrite <- H in Hlen.
      specialize (H1 (hd_default []) [] [] _ _ _ _ Hlen eq_refl eq_refl eq_refl).
      destruct H1 as [st'' [st''' Hk]].
      eapply nth_In in Hlen.
      apply Hf in Hk; eauto. clear Hf.
      rewrite Exists_exists. exists (nth n es (hd_default [])).
      split; auto.
    - eapply Exists_concat_nth' in H2. destruct H2 as [n [Hlen Hex]].
      rewrite <- H0 in Hlen.
      specialize (H1 (hd_default []) [] [] _ _ _ _ Hlen eq_refl eq_refl eq_refl).
      destruct H1 as [st'' [st''' Hk]].
      eapply nth_In in Hlen.
      apply Hf in Hk; eauto. clear Hf.
      rewrite Exists_exists. exists (nth n es (hd_default [])).
      split; auto.
  Qed.

  Fact add_whens_Is_node_in : forall f ty cl e,
      Is_node_in_exp f (add_whens e ty cl) ->
      Is_node_in_exp f e.
  Proof with eauto.
    induction cl; intros e Hisin; simpl in Hisin...
    inv Hisin. inv H1; [| inv H0]...
  Qed.

  Hint Constructors Is_node_in_exp.

  Fact fby_iteexp_Is_node_in : forall f e0 e ann e' eqs' st st',
      fby_iteexp e0 e ann st = (e', eqs', st') ->
      (Is_node_in_exp f e' \/ Is_node_in f eqs') ->
      (Is_node_in_exp f e0 \/ Is_node_in_exp f e).
  Proof with eauto.
    intros f e0 e [ty cl] e' eqs' st st' Hfby Hisin.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind.
    - destruct Hisin; inv H.
      destruct H2; (inv H; [| inv H1])...
    - destruct Hisin.
      + inv H1. destruct H4; inv H1.
        * inv H2... inv H3.
        * inv H2; inv H3.
      + inv H1.
        * inv H3; inv H2.
          destruct H4; (inv H1; [| inv H3])...
          apply add_whens_Is_node_in in H3. inv H3.
        * unfold init_var_for_clock in H.
          destruct (find _ _).
          -- destruct p; inv H. inv H3.
          -- destruct (fresh_ident _ _). inv H.
             inv H3; inv H1; inv H2.
             destruct H3; (inv H; [| inv H2]); eapply add_whens_Is_node_in in H2; inv H2.
  Qed.

  Fact normalize_fby_Is_node_in : forall f e0s es anns es' eqs' st st',
      length e0s = length anns ->
      length es = length anns ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      (List.Exists (Is_node_in_exp f) es' \/ Is_node_in f eqs') ->
      (List.Exists (Is_node_in_exp f) e0s \/ List.Exists (Is_node_in_exp f) es).
  Proof with eauto.
    intros f e0s es anns; revert e0s es.
    induction anns; intros e0s es es' eqs' st st' Hlen1 Hlen2 Hnorm Hex;
      destruct e0s; destruct es; simpl in *; try congruence;
        unfold normalize_fby in Hnorm; simpl in *; repeat inv_bind.
    - destruct Hex; inv H.
    - inv Hlen1; inv Hlen2.
      assert (normalize_fby e0s es anns x2 = (x3, concat x4, st')) as Hnorm.
      { unfold normalize_fby. repeat inv_bind.
        exists x3. exists x4. exists st'. split... inv_bind... }
      specialize (IHanns _ _ _ _ _ _ H2 H3 Hnorm); clear Hnorm.
      destruct Hex.
      + inv H1.
        * eapply fby_iteexp_Is_node_in in H...
          destruct H...
        * specialize (IHanns (or_introl H5)) as [?|?]...
      + simpl in H1. rewrite Is_node_in_app in H1. destruct H1.
        * eapply fby_iteexp_Is_node_in in H...
          destruct H...
        * specialize (IHanns (or_intror H1)) as [?|?]...
  Qed.
  Local Hint Resolve normalize_fby_Is_node_in.

  Fact normalize_reset_Is_node_in : forall f e e' eqs' st st',
      normalize_reset e st = (e', eqs', st') ->
      (Is_node_in_exp f e' \/ Is_node_in f eqs') ->
      Is_node_in_exp f e.
  Proof.
    intros f e e' eqs' st st' Hnorm Hisin.
    specialize (normalize_reset_spec e) as [[v [ann [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind.
    - destruct Hisin; inv H.
    - destruct (List.hd _ _) as [? [? ?]].
      repeat inv_bind.
      destruct Hisin; inv H; inv H0; inv H1; auto; inv H0.
  Qed.
  Local Hint Resolve normalize_reset_Is_node_in.

  Fact normalize_exp_Is_node_in : forall f e is_control es' eqs' st st',
      wl_exp e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      (List.Exists (Is_node_in_exp f) es' \/ Is_node_in f eqs') ->
      Is_node_in_exp f e.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwl Hnorm Hisin;
      inv Hwl; simpl in Hnorm; repeat inv_bind.
    - (* const *) exfalso.
      destruct Hisin as [H|H]; inv H; inv H1.
    - (* var *) exfalso.
      destruct Hisin as [H|H]; inv H; inv H1.
    - (* unop *)
      specialize (normalize_exp_length _ _ _ _ _ _ H1 H) as Hlen.
      rewrite H3 in Hlen. singleton_length. clear H3.
      constructor. eapply IHe...
      destruct Hisin...
      left. constructor.
      inv H0; inv H3...
    - (* binop *)
      specialize (normalize_exp_length _ _ _ _ _ _ H3 H) as Hlen1.
      rewrite H5 in Hlen1. singleton_length. clear H5.
      specialize (normalize_exp_length _ _ _ _ _ _ H4 H0) as Hlen2.
      rewrite H6 in Hlen2. singleton_length. clear H6.
      constructor.
      destruct Hisin.
      + inv H1; inv H5.
        destruct H6...
      + rewrite Is_node_in_app in H1. destruct H1...
    - (* fby *)
      specialize (map_bind2_normalize_exp_length _ _ _ _ _ _ H4 H1) as Hlen1.
      specialize (map_bind2_normalize_exp_length _ _ _ _ _ _ H5 H2) as Hlen2.
      constructor.
      repeat rewrite Is_node_in_app in Hisin. destruct Hisin as [Hisin|[Hisin|[Hisin|[Hisin|Hisin]]]].
      + exfalso.
        rewrite CommonList.Exists_map in Hisin.
        rewrite Exists_exists in Hisin. destruct Hisin as [[id ann] [Hin Hisin]].
        inv Hisin.
      + rewrite Is_node_in_Exists in Hisin.
        rewrite CommonList.Exists_map in Hisin.
        eapply normalize_fby_Is_node_in in H3; solve_length.
        * destruct H3.
          -- eapply map_bind2_Is_node_in in H1... (repeat rewrite_Forall_forall; eauto).
          -- eapply map_bind2_Is_node_in in H2... (repeat rewrite_Forall_forall; eauto).
        * left. rewrite Exists_exists in *. destruct Hisin as [[[id ann] e] [Hin Hisin]].
          repeat simpl_In. inv Hisin; [| inv H11].
          exists e...
      + left.
        eapply map_bind2_Is_node_in in H1... (repeat rewrite_Forall_forall; eauto).
      + right.
        eapply map_bind2_Is_node_in in H2... (repeat rewrite_Forall_forall; eauto).
      + eapply normalize_fby_Is_node_in in H3; solve_length...
        destruct H3.
        * eapply map_bind2_Is_node_in in H1... (repeat rewrite_Forall_forall; eauto).
        * eapply map_bind2_Is_node_in in H2... (repeat rewrite_Forall_forall; eauto).
    - (* when *)
      specialize (map_bind2_normalize_exp_length _ _ _ _ _ _ H2 H0) as Hlength.
      constructor.
      eapply map_bind2_Is_node_in in H0... (repeat rewrite_Forall_forall; eauto).
      destruct Hisin...
      left.
      rewrite CommonList.Exists_map in H1.
      rewrite Exists_combine_l with (ys:=tys); solve_length.
      rewrite Exists_exists in *. destruct H1 as [[e ty] [HIn Hex]].
      exists (e, ty); split...
      inv Hex. inv H4... inv H3.
    - (* merge *)
      specialize (map_bind2_normalize_exp_length _ _ _ _ _ _ H5 H1) as Hlen1.
      specialize (map_bind2_normalize_exp_length _ _ _ _ _ _ H6 H2) as Hlen2.
      constructor. destruct is_control; repeat inv_bind.
      + destruct Hisin.
        * rewrite CommonList.Exists_map in H3.
          rewrite Exists_exists in H3. destruct H3 as [[[e0 e] ty] [HIn Hnode]].
          repeat simpl_In.
          inv Hnode. destruct H11; (inv H9; [| inv H11]).
          -- left. eapply map_bind2_Is_node_in in H1... (repeat rewrite_Forall_forall; eauto).
             left. eapply Exists_exists. eexists...
          -- right. eapply map_bind2_Is_node_in in H2... (repeat rewrite_Forall_forall; eauto).
             left. eapply Exists_exists. eexists...
        * rewrite Is_node_in_app in H3. destruct H3.
          -- left. eapply map_bind2_Is_node_in in H1... (repeat rewrite_Forall_forall; eauto).
          -- right. eapply map_bind2_Is_node_in in H2... (repeat rewrite_Forall_forall; eauto).
      + destruct Hisin.
        * exfalso.
          rewrite CommonList.Exists_map in H4.
          rewrite Exists_exists in H4. destruct H4 as [[id ann] [Hin Hex]]. inv Hex.
        * repeat rewrite Is_node_in_app in H4. destruct H4 as [H4|[H4|H4]].
          -- rewrite Is_node_in_Exists in H4.
             rewrite map_map in H4. rewrite combine_map_fst in H4. rewrite combine_map_snd in H4.
             rewrite map_map in H4; simpl in H4.
             rewrite CommonList.Exists_map in H4.
             rewrite Exists_exists in H4. destruct H4 as [[[id ann] [[e0 e] ty]] [Hin Hex]]; simpl in Hex.
             repeat simpl_In.
             inv Hex; inv H12. destruct H14.
             ++ left.
                inv H11; [| inv H13].
                eapply map_bind2_Is_node_in in H1... (repeat rewrite_Forall_forall; eauto).
                left. eapply Exists_exists. eexists...
             ++ right.
                inv H11; [| inv H13].
                eapply map_bind2_Is_node_in in H2... (repeat rewrite_Forall_forall; eauto).
                left. eapply Exists_exists. eexists...
          -- left. eapply map_bind2_Is_node_in in H1... (repeat rewrite_Forall_forall; eauto).
          -- right. eapply map_bind2_Is_node_in in H2... (repeat rewrite_Forall_forall; eauto).
    - (* ite *)
      specialize (normalize_exp_length _ _ _ _ _ _ H5 H1) as Hlen.
      rewrite H8 in Hlen. singleton_length. clear H8.
      specialize (map_bind2_normalize_exp_length _ _ _ _ _ _ H6 H2) as Hlen1.
      specialize (map_bind2_normalize_exp_length _ _ _ _ _ _ H7 H3) as Hlen2.
      constructor. destruct is_control; repeat inv_bind.
      + destruct Hisin.
        * rewrite CommonList.Exists_map in H4.
          rewrite Exists_exists in H4. destruct H4 as [[[et ef] ty] [HIn Hnode]].
          repeat simpl_In.
          inv Hnode. destruct H13 as [H13|[H13|H13]]...
          -- right. left.
             inv H13; [| inv H12].
             eapply map_bind2_Is_node_in in H2... (repeat rewrite_Forall_forall; eauto).
             left. eapply Exists_exists. eexists...
          -- right. right.
             inv H13; [| inv H12].
             eapply map_bind2_Is_node_in in H3... (repeat rewrite_Forall_forall; eauto).
             left. eapply Exists_exists. eexists...
        * repeat rewrite Is_node_in_app in H4. destruct H4 as [H4|[H4|H4]]...
          -- right. left. eapply map_bind2_Is_node_in in H2... (repeat rewrite_Forall_forall; eauto).
          -- right. right. eapply map_bind2_Is_node_in in H3... (repeat rewrite_Forall_forall; eauto).
      + destruct Hisin.
        * exfalso.
          rewrite CommonList.Exists_map in H8.
          rewrite Exists_exists in H8. destruct H8 as [[id ann] [Hin Hex]]. inv Hex.
        * repeat rewrite Is_node_in_app in H8. destruct H8 as [H8|[H8|[H8|H8]]]...
          -- rewrite Is_node_in_Exists in H8.
             rewrite map_map in H8. rewrite combine_map_fst in H8. rewrite combine_map_snd in H8.
             rewrite map_map in H8; simpl in H8.
             rewrite CommonList.Exists_map in H8.
             rewrite Exists_exists in H8. destruct H8 as [[[id ann] [[et ef] ty]] [Hin Hex]]; simpl in Hex.
             repeat simpl_In.
             inv Hex; inv H14. destruct H16 as [H16|[H16|H16]]...
             ++ right. left.
                inv H16; [| inv H14].
                eapply map_bind2_Is_node_in in H2... (repeat rewrite_Forall_forall; eauto).
                left. eapply Exists_exists. eexists...
             ++ right. right.
                inv H16; [| inv H14].
                eapply map_bind2_Is_node_in in H3... (repeat rewrite_Forall_forall; eauto).
                left. eapply Exists_exists. eexists...
          -- right. left. eapply map_bind2_Is_node_in in H2... (repeat rewrite_Forall_forall; eauto).
          -- right. eapply map_bind2_Is_node_in in H3... (repeat rewrite_Forall_forall; eauto).
    - (* app *)
      destruct Hisin.
      + exfalso.
        rewrite CommonList.Exists_map in H4.
        rewrite Exists_exists in H4. destruct H4 as [[id ann] [Hin Hex]]. inv Hex.
      + inv H4.
        * inv H6; inv H5...
          eapply map_bind2_Is_node_in in H1... (repeat rewrite_Forall_forall; eauto).
        * eapply map_bind2_Is_node_in in H1... (repeat rewrite_Forall_forall; eauto).
    - (* app (reset) *)
      specialize (normalize_exp_length _ _ _ _ _ _ H4 H1) as Hlen.
      rewrite H7 in Hlen. singleton_length. clear H7.
      destruct Hisin.
      + exfalso.
        rewrite CommonList.Exists_map in H7.
        rewrite Exists_exists in H7. destruct H7 as [[id ann] [Hin Hex]]. inv Hex.
      + inv H7; [| repeat rewrite Exists_app' in H9; destruct H9 as [[H9|H9]|H9]]...
        * inv H9; [| inv H8].
          inv H8...
          inv H10.
          --eapply normalize_reset_Is_node_in in H5...
            eapply H in H1...
          -- eapply map_bind2_Is_node_in in H2... (repeat rewrite_Forall_forall; eauto).
        * eapply normalize_reset_Is_node_in in H5...
          eapply H in H1...
        * eapply map_bind2_Is_node_in in H2... (repeat rewrite_Forall_forall; eauto).
  Qed.
  Local Hint Resolve normalize_exp_Is_node_in.

  Corollary normalize_exps_Is_node_in : forall f es es' eqs' st st',
      Forall wl_exp es ->
      normalize_exps es st = (es', eqs', st') ->
      (List.Exists (Is_node_in_exp f) es' \/ Is_node_in f eqs') ->
      List.Exists (Is_node_in_exp f) es.
  Proof.
    intros f es es' eqs' st st' Hwl Hnorm Hex.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_Is_node_in in H; eauto.
    solve_forall.
  Qed.
  Local Hint Resolve normalize_exps_Is_node_in.

  Fact normalize_rhs_Is_node_in : forall f e keep_fby es' eqs' st st',
      wl_exp e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      (List.Exists (Is_node_in_exp f) es' \/ Is_node_in f eqs') ->
      Is_node_in_exp f e.
  Proof with eauto.
    intros f e keep_fby es' eqs' st st' Hwl Hnorm Hisin.
    destruct e; unfold normalize_rhs in Hnorm;
      try (eapply normalize_exp_Is_node_in in Hnorm; eauto);
      [destruct keep_fby|destruct o].
    - (* fby (keep) *)
      inv Hwl. repeat inv_bind.
      specialize (normalize_exps_length _ _ _ _ _ H2 H) as Hlen1.
      specialize (normalize_exps_length _ _ _ _ _ H3 H0) as Hlen2.
      repeat rewrite Is_node_in_app in Hisin.
      destruct Hisin as [Hisin|[Hisin|[Hisin|Hisin]]]...
      + eapply normalize_fby_Is_node_in in H1; solve_length...
        destruct H1...
      + eapply normalize_fby_Is_node_in in H1; solve_length...
        destruct H1...
    - (* fby (dont keep) *)
      eapply normalize_exp_Is_node_in in Hnorm...
    - (* app (reset) *)
      inv Hwl. repeat inv_bind.
      specialize (normalize_exp_length _ _ _ _ _ _ H2 H) as Hlen.
      rewrite H5 in Hlen. singleton_length. clear H5.
      destruct Hisin.
      + inv H3; inv H6...
        inv H7...
        eapply normalize_reset_Is_node_in in H1...
        eapply normalize_exp_Is_node_in in H...
      + repeat rewrite Is_node_in_app in H3. destruct H3 as [[H3|H3]|H3]...
        eapply normalize_reset_Is_node_in in H1...
        eapply normalize_exp_Is_node_in in H...
    - (* app *)
      inv Hwl. repeat inv_bind.
      destruct Hisin...
      inv H1; inv H3...
  Qed.
  Local Hint Resolve normalize_rhs_Is_node_in.

  Corollary normalize_rhss_Is_node_in : forall f es keep_fby es' eqs' st st',
      Forall wl_exp es ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      (List.Exists (Is_node_in_exp f) es' \/ Is_node_in f eqs') ->
      List.Exists (Is_node_in_exp f) es.
  Proof.
    intros f es keep_fby es' eqs' st st' Hwl Hnorm Hisin.
    unfold normalize_rhss in Hnorm. repeat inv_bind.
    eapply map_bind2_Is_node_in in H; eauto.
    solve_forall.
  Qed.
  Local Hint Resolve normalize_rhss_Is_node_in.

  Fact normalize_equation_Is_node_in : forall f eq to_cut eqs' st st',
      wl_equation eq ->
      normalize_equation to_cut eq st = (eqs', st') ->
      Is_node_in f eqs' ->
      Is_node_in_eq f eq.
  Proof with eauto.
    intros f [xs es] to_cut eqs' st st' Hwl Hnorm Hisin.
    inv Hwl.
    unfold normalize_equation in Hnorm; repeat inv_bind.
    rewrite Is_node_in_app in Hisin. destruct Hisin.
    + rewrite Is_node_in_Exists in H2.
      rewrite CommonList.Exists_map in H2.
      rewrite Exists_exists in H2. destruct H2 as [[e xs'] [Hin Hisin]].
      repeat simpl_In. inv Hisin; [| inv H3].
      eapply combine_for_numstreams_In in Hin.
      eapply normalize_rhss_Is_node_in in H1...
      left. eapply List.Exists_exists. eexists...
    + eapply normalize_rhss_Is_node_in in H1...
  Qed.
  Local Hint Resolve normalize_equation_Is_node_in.

  Corollary normalize_equations_Is_node_in : forall f eqs to_cut eqs' st st',
      Forall wl_equation eqs ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      Is_node_in f eqs' ->
      Is_node_in f eqs.
  Proof.
    induction eqs; intros to_cut eqs' st st' Hwl Hnorm Hisin;
      simpl in Hnorm; repeat inv_bind.
    - inv Hisin.
    - inv Hwl.
      rewrite Is_node_in_app in Hisin; destruct Hisin.
      + left. eauto.
      + right. rewrite <- Is_node_in_Exists. eauto.
  Qed.

  Fact normalize_node_Is_node_in : forall f n to_cut Hwl,
      Is_node_in f (n_eqs (normalize_node to_cut n Hwl)) ->
      Is_node_in f (n_eqs n).
  Proof.
    intros f n to_cut Hwl Hisin; simpl in Hisin.
    remember (normalize_equations _ _ _) as res; destruct res as [eqs' st'].
    symmetry in Heqres.
    eapply normalize_equations_Is_node_in in Heqres; eauto.
  Qed.

  Fact normalize_global_names : forall G Hwl,
      List.map n_name (normalize_global G Hwl) = List.map n_name G.
  Proof.
    induction G; intros Hwl; simpl; eauto.
    f_equal; eauto.
  Qed.

  Fact normalize_node_ordered : forall G n Hwl to_cut,
      Ordered_nodes (n::G) ->
      Ordered_nodes (normalize_node to_cut n Hwl::G).
  Proof.
    intros G n Hwl to_cut Hordered.
    inv Hordered.
    constructor; eauto.
    intros f Hisin.
    eapply normalize_node_Is_node_in in Hisin; auto.
  Qed.

  Lemma normalize_global_ordered : forall G Hwl,
      Ordered_nodes G ->
      Ordered_nodes (normalize_global G Hwl).
  Proof with eauto.
    intros G Hwl Hord.
    induction Hord; simpl; constructor...
    - intros f Hisin; simpl.
      eapply normalize_node_Is_node_in in Hisin.
      eapply H in Hisin. destruct Hisin as [Hname Hnexists].
      split; auto.
      rewrite <- CommonList.Exists_map in *.
      rewrite normalize_global_names...
    - simpl.
      rewrite <- (Forall_map (fun n => ~(n_name nd = n))) in *.
      rewrite normalize_global_names...
  Qed.

End NORDERED.

Module NOrderedFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Lord : LORDERED Ids Op Syn)
       (Norm : NORMALIZATION Ids Op OpAux Syn)
       <: NORDERED Ids Op OpAux Syn Lord Norm.
  Include NORDERED Ids Op OpAux Syn Lord Norm.
End NOrderedFun.
