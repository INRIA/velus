From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Lustre.LSyntax Lustre.LCausality Lustre.LOrdered.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

(** * Preservation of order through normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type NORDERED
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Cau : LCAUSALITY Ids Op Syn)
       (Import Ord : LORDERED Ids Op Syn)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn Cau).

  Import Fresh Tactics.

  (** ** Preservation of order through the first pass *)

  Fact map_bind2_Is_node_in : forall G f (k : exp -> Unnesting.FreshAnn (list exp * list equation)) es es' eqs' st st',
      Forall (wl_exp G) es ->
      map_bind2 k es st = (es', eqs', st') ->
      Forall (fun e => forall es' eqs' st st',
                  k e st = (es', eqs', st') ->
                  (List.Exists (Is_node_in_exp f) es' \/ Is_node_in f eqs') ->
                  Is_node_in_exp f e) es ->
      (List.Exists (Is_node_in_exp f) (concat es') \/ Is_node_in f (concat eqs')) ->
      List.Exists (Is_node_in_exp f) es.
  Proof with eauto.
    intros G f k es es' eqs' st st' Hwl Hmap Hf Hisin.
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

  Hint Constructors Is_node_in_exp.

  Fact unnest_reset_Is_node_in : forall k f e e' eqs' st st',
      LiftO True (fun e => forall es' eqs' st st',
                   k e st = (es', eqs', st') ->
                   Exists (Is_node_in_exp f) es' \/ Is_node_in f eqs' ->
                   Is_node_in_exp f e) e ->
      unnest_reset k e st = (e', eqs', st') ->
      LiftO True (Is_node_in_exp f) e' \/ Is_node_in f eqs' ->
      LiftO True (Is_node_in_exp f) e.
  Proof.
    intros * Hkisin Hnorm Hisin.
    unnest_reset_spec; simpl in *; eauto.
    - eapply Hkisin in Hk0; eauto.
      destruct Hisin as [Hisin|Hisin]; auto. inv Hisin.
    - eapply Hkisin in Hk0; eauto.
      destruct Hisin as [Hisin|Hisin]; inv Hisin; auto.
      apply Exists_singl in H0.
      destruct l; simpl in H0; auto. inv H0.
  Qed.
  Local Hint Resolve unnest_reset_Is_node_in.

  Fact unnest_exp_Is_node_in : forall G f e is_control es' eqs' st st',
      wl_exp G e ->
      unnest_exp is_control e st = (es', eqs', st') ->
      (List.Exists (Is_node_in_exp f) es' \/ Is_node_in f eqs') ->
      Is_node_in_exp f e.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwl Hnorm Hisin;
      inv Hwl; simpl in Hnorm. 1-10:repeat inv_bind.
    - (* const *) exfalso.
      destruct Hisin as [H|H]; inv H; inv H1.
    - (* var *) exfalso.
      destruct Hisin as [H|H]; inv H; inv H1.
    - (* unop *)
      assert (length x = numstreams e) as Hlen by (eapply unnest_exp_length; eauto).
      rewrite H4 in Hlen. singleton_length. clear H4.
      constructor. eapply IHe...
      destruct Hisin...
      left. constructor.
      inv H0; inv H3...
    - (* binop *)
      assert (length x = numstreams e1) as Hlen1 by (eapply unnest_exp_length; eauto).
      rewrite H6 in Hlen1. singleton_length. clear H6.
      assert (length x2 = numstreams e2) as Hlen2 by (eapply unnest_exp_length; eauto).
      rewrite H7 in Hlen2. singleton_length. clear H7.
      constructor.
      destruct Hisin.
      + inv H1; inv H3.
        destruct H6...
      + rewrite Is_node_in_app in H1. destruct H1...
    - (* fby *)
      assert (length (concat x2) = length (annots e0s)) as Hlen1 by (eapply map_bind2_unnest_exp_length; eauto).
      assert (length (concat x6) = length (annots es)) as Hlen2 by (eapply map_bind2_unnest_exp_length; eauto).
      constructor.
      repeat rewrite Is_node_in_app in Hisin. destruct Hisin as [Hisin|[Hisin|[Hisin|Hisin]]].
      + exfalso.
        rewrite CommonList.Exists_map in Hisin.
        rewrite Exists_exists in Hisin. destruct Hisin as [[id ann] [Hin Hisin]].
        inv Hisin.
      + rewrite Is_node_in_Exists in Hisin.
        rewrite CommonList.Exists_map in Hisin.
        unfold unnest_fby in Hisin.
        apply Exists_exists in Hisin as [[[? ?] ?] [Hin ?]]; repeat simpl_In.
        apply Exists_singl in H5. inv H5. destruct H15 as [Hin|Hin]; eapply Exists_singl in Hin.
        * eapply map_bind2_Is_node_in in H1... solve_forall.
          left. eapply Exists_exists. exists e...
        * eapply map_bind2_Is_node_in in H2... solve_forall.
          left. eapply Exists_exists. exists e0...
      + left.
        eapply map_bind2_Is_node_in in H1... solve_forall.
      + right.
        eapply map_bind2_Is_node_in in H2... solve_forall.
    - (* arrow *)
      assert (length (concat x2) = length (annots e0s)) as Hlen1 by (eapply map_bind2_unnest_exp_length; eauto).
      assert (length (concat x6) = length (annots es)) as Hlen2 by (eapply map_bind2_unnest_exp_length; eauto).
      constructor.
      repeat rewrite Is_node_in_app in Hisin. destruct Hisin as [Hisin|[Hisin|[Hisin|Hisin]]].
      + exfalso.
        rewrite CommonList.Exists_map in Hisin.
        rewrite Exists_exists in Hisin. destruct Hisin as [[id ann] [Hin Hisin]].
        inv Hisin.
      + rewrite Is_node_in_Exists in Hisin.
        unfold unnest_arrow in Hisin.
        apply Exists_exists in Hisin as [[? ?] [Hin ?]]; repeat simpl_In.
        apply Exists_singl in H5. inv H5. destruct H15 as [Hin|Hin]; eapply Exists_singl in Hin.
        * eapply map_bind2_Is_node_in in H1... solve_forall.
          left. eapply Exists_exists. exists e...
        * eapply map_bind2_Is_node_in in H2... solve_forall.
          left. eapply Exists_exists. exists e0...
      + left.
        eapply map_bind2_Is_node_in in H1... solve_forall.
      + right.
        eapply map_bind2_Is_node_in in H2... solve_forall.
    - (* when *)
      assert (length (concat x1) = length (annots es)) by (eapply map_bind2_unnest_exp_length; eauto).
      constructor.
      eapply map_bind2_Is_node_in in H0... (repeat rewrite_Forall_forall; eauto).
      destruct Hisin...
      left. unfold unnest_when in H2.
      rewrite CommonList.Exists_map in H2.
      rewrite Exists_combine_l with (ys:=tys); solve_length.
      rewrite Exists_exists in *. destruct H2 as [[e ty] [HIn Hex]].
      exists (e, ty); split...
      inv Hex. inv H5... inv H4.
    - (* merge *)
      assert (length (concat x3) = length (annots ets)) as Hlen1 by (eapply map_bind2_unnest_exp_length; eauto).
      assert (length (concat x6) = length (annots efs)) as Hlen2 by (eapply map_bind2_unnest_exp_length; eauto).
      constructor. destruct is_control; repeat inv_bind.
      + destruct Hisin.
        * unfold unnest_merge in H3. rewrite CommonList.Exists_map in H3.
          rewrite Exists_exists in H3. destruct H3 as [[[e0 e] ty] [HIn Hnode]].
          repeat simpl_In.
          inv Hnode. destruct H11; (inv H5; [| inv H11]).
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
          -- unfold unnest_merge in H4. rewrite Is_node_in_Exists in H4.
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
      assert (length x = numstreams e) as Hlen by (eapply unnest_exp_length; eauto).
      rewrite H9 in Hlen. singleton_length. clear H9.
      assert (length (concat x5) = length (annots ets)) as Hlen1 by (eapply map_bind2_unnest_exp_length; eauto).
      assert (length (concat x8) = length (annots efs)) as Hlen2 by (eapply map_bind2_unnest_exp_length; eauto).
      constructor. destruct is_control; repeat inv_bind.
      + destruct Hisin.
        * unfold unnest_ite in H4. rewrite CommonList.Exists_map in H4.
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
          rewrite CommonList.Exists_map in H7.
          rewrite Exists_exists in H7. destruct H7 as [[id ann] [Hin Hex]]. inv Hex.
        * repeat rewrite Is_node_in_app in H7. destruct H7 as [H7|[H7|[H7|H7]]]...
          -- unfold unnest_ite in H7. rewrite Is_node_in_Exists in H7.
             rewrite map_map, combine_map_fst, combine_map_snd, map_map in H7; simpl in H7.
             rewrite CommonList.Exists_map, Exists_exists in H7.
             destruct H7 as [[[id ann] [[et ef] ty]] [Hin Hex]]; simpl in Hex.
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
        rewrite CommonList.Exists_map, Exists_exists in H3.
        destruct H3 as [[id ann] [Hin Hex]]. inv Hex.
      + inv H3.
        * inv H5; inv H4...
          eapply map_bind2_Is_node_in in H1... (repeat rewrite_Forall_forall; eauto).
        * eapply map_bind2_Is_node_in in H1... (repeat rewrite_Forall_forall; eauto).
          rewrite app_nil_r in H5...
    - (* app (reset) *)
      do 5 inv_bind.
      assert (LiftO True (Is_node_in_exp f) x2 \/ Is_node_in f x3 ->
              Is_node_in_exp f (Eapp f0 es (Some r) a)) as Hisin2.
      { intros.
        eapply (unnest_reset_Is_node_in _ _ (Some r)) in H2; simpl; eauto.
      } clear H2.
      repeat inv_bind.
      destruct Hisin as [Hisin|Hisin].
      + exfalso.
        rewrite CommonList.Exists_map, Exists_exists in Hisin.
        destruct Hisin as [[id ann] [Hin Hex]]. inv Hex.
      + inv Hisin; [| repeat rewrite Exists_app' in H4; destruct H4 as [H4|H4]]...
        * inv H4; [| inv H7].
          inv H7; simpl in *...
          inv H12; eauto.
          eapply map_bind2_Is_node_in in H1... (repeat rewrite_Forall_forall; eauto).
        * eapply map_bind2_Is_node_in in H1... (repeat rewrite_Forall_forall; eauto).
  Qed.
  Local Hint Resolve unnest_exp_Is_node_in.

  Corollary unnest_exps_Is_node_in : forall G f es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_exps es st = (es', eqs', st') ->
      (List.Exists (Is_node_in_exp f) es' \/ Is_node_in f eqs') ->
      List.Exists (Is_node_in_exp f) es.
  Proof.
    intros G f es es' eqs' st st' Hwl Hnorm Hex.
    unfold unnest_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_Is_node_in in H; eauto.
    solve_forall.
  Qed.
  Local Hint Resolve unnest_exps_Is_node_in.

  Fact unnest_rhs_Is_node_in : forall G f e es' eqs' st st',
      wl_exp G e ->
      unnest_rhs e st = (es', eqs', st') ->
      (List.Exists (Is_node_in_exp f) es' \/ Is_node_in f eqs') ->
      Is_node_in_exp f e.
  Proof with eauto.
    intros * Hwl Hnorm Hisin.
    destruct e; unfold unnest_rhs in Hnorm;
      try (eapply unnest_exp_Is_node_in in Hnorm; eauto);
      [| |destruct o].
    - (* fby *)
      inv Hwl. repeat inv_bind.
      assert (length x = length (annots l)) as Hlen1 by (eapply unnest_exps_length; eauto).
      assert (length x2 = length (annots l0)) as Hlen2 by (eapply unnest_exps_length; eauto).
      repeat rewrite Is_node_in_app in Hisin.
      constructor.
      destruct Hisin as [Hisin|[Hisin|Hisin]]...
      unfold unnest_fby in Hisin.
      rewrite Exists_map in Hisin. apply Exists_exists in Hisin as [[[? ?] ?] [Hin ?]]; repeat simpl_In.
      inv H1. destruct H10 as [Hisin|Hisin].
      + apply Exists_singl in Hisin.
        eapply unnest_exps_Is_node_in in H...
        left. rewrite Exists_exists. exists e; auto.
      + apply Exists_singl in Hisin.
        eapply unnest_exps_Is_node_in in H0...
        left. rewrite Exists_exists. exists e0; auto.
    - (* arrow *)
      inv Hwl. repeat inv_bind.
      assert (length x = length (annots l)) as Hlen1 by (eapply unnest_exps_length; eauto).
      assert (length x2 = length (annots l0)) as Hlen2 by (eapply unnest_exps_length; eauto).
      repeat rewrite Is_node_in_app in Hisin.
      constructor.
      destruct Hisin as [Hisin|[Hisin|Hisin]]...
      unfold unnest_arrow in Hisin.
      rewrite Exists_map in Hisin. apply Exists_exists in Hisin as [[[? ?] ?] [Hin ?]]; repeat simpl_In.
      inv H1. destruct H10 as [Hisin|Hisin].
      + apply Exists_singl in Hisin.
        eapply unnest_exps_Is_node_in in H...
        left. rewrite Exists_exists. exists e; auto.
      + apply Exists_singl in Hisin.
        eapply unnest_exps_Is_node_in in H0...
        left. rewrite Exists_exists. exists e0; auto.
    - (* app (reset) *)
      inv Hwl. do 4 inv_bind.
      assert (LiftO True (Is_node_in_exp f) x2 \/ Is_node_in f x3 ->
              Is_node_in_exp f (Eapp i l (Some e) l0)) as Hisin2.
      { intros.
        eapply (unnest_reset_Is_node_in _ _ (Some e)) in H0; simpl; eauto.
      } clear H0.
      destruct Hisin as [Hisin|Hisin].
      + apply Exists_singl in Hisin.
        inv Hisin... inv H2...
      + unfold Is_node_in in Hisin. rewrite Exists_app' in Hisin; destruct Hisin as [Hisin|Hisin]...
    - (* app *)
      inv Hwl. repeat inv_bind.
      destruct Hisin...
      inv H0; inv H3...
      rewrite app_nil_r in H0...
  Qed.
  Local Hint Resolve unnest_rhs_Is_node_in.

  Corollary unnest_rhss_Is_node_in : forall G f es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_rhss es st = (es', eqs', st') ->
      (List.Exists (Is_node_in_exp f) es' \/ Is_node_in f eqs') ->
      List.Exists (Is_node_in_exp f) es.
  Proof.
    intros * Hwl Hnorm Hisin.
    unfold unnest_rhss in Hnorm. repeat inv_bind.
    eapply map_bind2_Is_node_in in H; eauto.
    solve_forall.
  Qed.
  Local Hint Resolve unnest_rhss_Is_node_in.

  Fact unnest_equation_Is_node_in : forall G f eq eqs' st st',
      wl_equation G eq ->
      unnest_equation eq st = (eqs', st') ->
      Is_node_in f eqs' ->
      Is_node_in_eq f eq.
  Proof with eauto.
    intros G f [xs es] eqs' st st' Hwl Hnorm Hisin.
    inv Hwl.
    unfold unnest_equation in Hnorm; repeat inv_bind.
    rewrite Is_node_in_app in Hisin. destruct Hisin.
    + rewrite Is_node_in_Exists in H2.
      rewrite CommonList.Exists_map in H2.
      rewrite Exists_exists in H2. destruct H2 as [[e xs'] [Hin Hisin]].
      repeat simpl_In. inv Hisin; [| inv H3].
      eapply combine_for_numstreams_In in Hin.
      eapply unnest_rhss_Is_node_in in H1...
      left. eapply List.Exists_exists. eexists...
    + eapply unnest_rhss_Is_node_in in H1...
  Qed.
  Local Hint Resolve unnest_equation_Is_node_in.

  Corollary unnest_equations_Is_node_in : forall G f eqs eqs' st st',
      Forall (wl_equation G) eqs ->
      unnest_equations eqs st = (eqs', st') ->
      Is_node_in f eqs' ->
      Is_node_in f eqs.
  Proof.
    induction eqs; intros * Hwl Hnorm Hisin;
      unfold unnest_equations in Hnorm; simpl in *; repeat inv_bind; simpl in *.
    - inv Hisin.
    - inv Hwl.
      rewrite Is_node_in_app in Hisin; destruct Hisin.
      + left. eauto.
      + right. rewrite <- Is_node_in_Exists.
        eapply IHeqs; eauto.
        unfold unnest_equations.
        inv_bind. repeat eexists; eauto. inv_bind; eauto.
  Qed.

  Fact unnest_node_Is_node_in : forall f n Hwl Hpref,
      Is_node_in f (n_eqs (unnest_node n Hwl Hpref)) ->
      Is_node_in f (n_eqs n).
  Proof.
    intros * Hisin; simpl in Hisin.
    remember (unnest_equations _ _) as res; destruct res as [eqs' st'].
    symmetry in Heqres.
    destruct Hwl. unfold wl_node in w.
    eapply unnest_equations_Is_node_in in Heqres; eauto.
  Qed.

  Fact unnest_global_names : forall G Hwl Hprefs,
      List.map n_name (unnest_global G Hwl Hprefs) = List.map n_name G.
  Proof.
    induction G; intros *; simpl; eauto.
    f_equal; eauto.
  Qed.

  Fact unnest_node_ordered : forall G n Hwl Hpref,
      Ordered_nodes (n::G) ->
      Ordered_nodes (unnest_node n Hwl Hpref::G).
  Proof.
    intros * Hordered.
    inv Hordered.
    constructor; eauto.
    intros f Hisin.
    eapply unnest_node_Is_node_in in Hisin; auto.
  Qed.

  Lemma unnest_global_ordered : forall G Hwl Hprefs,
      Ordered_nodes G ->
      Ordered_nodes (unnest_global G Hwl Hprefs).
  Proof with eauto.
    intros G * Hord.
    induction Hord; simpl; constructor...
    - intros f Hisin; simpl.
      eapply unnest_node_Is_node_in in Hisin.
      eapply H in Hisin. destruct Hisin as [Hname Hnexists].
      split; auto.
      rewrite <- CommonList.Exists_map in *.
      rewrite unnest_global_names...
    - simpl.
      rewrite <- (Forall_map (fun n => ~(n_name nd = n))) in *.
      rewrite unnest_global_names...
  Qed.

  (** ** Preservation of order through the second pass *)

  Fact add_whens_Is_node_in : forall f ty cl e,
      Is_node_in_exp f (add_whens e ty cl) ->
      Is_node_in_exp f e.
  Proof with eauto.
    induction cl; intros e Hisin; simpl in Hisin...
    inv Hisin. inv H1; [| inv H0]...
  Qed.

  Fact init_var_for_clock_nIs_node_in : forall f ck x eqs' st st',
    init_var_for_clock ck st = (x, eqs', st') ->
    ~Exists (Is_node_in_eq f) eqs'.
  Proof.
    intros * Hinit contra.
    unfold init_var_for_clock in Hinit. destruct (find _ _).
    - destruct p; inv Hinit. inv contra.
    - destruct (fresh_ident _ _). inv Hinit.
      inv contra; inv H0; inv H1.
      destruct H2; (inv H; [| inv H1]); eapply add_whens_Is_node_in in H1; inv H1.
  Qed.

  Fact fby_iteexp_Is_node_in : forall f e0 e ann e' eqs' st st',
      fby_iteexp e0 e ann st = (e', eqs', st') ->
      (Is_node_in_exp f e' \/ Is_node_in f eqs') ->
      (Is_node_in_exp f e0 \/ Is_node_in_exp f e).
  Proof with eauto.
    intros f e0 e [ty [ck ann]] e' eqs' st st' Hfby Hisin.
    unfold fby_iteexp in Hfby; repeat inv_bind.
    destruct Hisin.
    + inv H1. destruct H4; inv H1.
      * inv H2... inv H3.
      * inv H2; inv H3.
    + inv H1.
      * inv H3; inv H2.
        destruct H4; (inv H1; [| inv H3])...
        apply add_whens_Is_node_in in H3. inv H3.
      * exfalso.
        eapply init_var_for_clock_nIs_node_in in H; eauto.
  Qed.

  Lemma fby_equation_Is_node_in : forall f to_cut eq eqs' st st',
      fby_equation to_cut eq st = (eqs', st') ->
      Is_node_in f eqs' ->
      Is_node_in f [eq].
  Proof.
    intros * Hfby Hisin.
    inv_fby_equation Hfby to_cut eq; destruct x2 as (ty&ck&name).
    - (* fby (constant) *)
      destruct PS.mem; repeat inv_bind; auto.
      inv Hisin; auto.
      + inv H1; [|inv H2]. inv H2.
      + apply Exists_singl in H1; auto.
        constructor. constructor. inv H1; auto.
    - (* fby *)
      constructor; constructor; constructor.
      eapply fby_iteexp_Is_node_in with (f:=f) (ann:=(ty, (ck, name))) in H as [H|H].
      + left. constructor; auto.
      + right. constructor; auto.
      + inv Hisin.
        * inv H1; auto. inv H2.
        * right; auto.
    - (* arrow *)
      repeat inv_bind.
      constructor; constructor; constructor.
      inv Hisin.
      + apply Exists_singl in H1. inv H1. destruct H3 as [Hisin|[Hisin|Hisin]]; auto.
        inv Hisin.
      + exfalso.
        eapply init_var_for_clock_nIs_node_in in H; eauto.
  Qed.

  Lemma fby_equations_Is_node_in : forall f to_cut eqs eqs' st st',
      fby_equations to_cut eqs st = (eqs', st') ->
      Is_node_in f eqs' ->
      Is_node_in f eqs.
  Proof.
    induction eqs; intros * Hnorm Hisin;
      unfold fby_equations in Hnorm; simpl in *; repeat inv_bind; simpl in *.
    - inv Hisin.
    - rewrite Is_node_in_app in Hisin; destruct Hisin.
      + left. eapply fby_equation_Is_node_in in H; eauto.
        apply Exists_singl in H; auto.
      + right. rewrite <- Is_node_in_Exists.
        eapply IHeqs; eauto.
        unfold fby_equations.
        inv_bind. repeat eexists; eauto. inv_bind; eauto.
  Qed.

  Fact normfby_node_Is_node_in : forall f to_cut n Hwl Hpref,
      Is_node_in f (n_eqs (normfby_node to_cut n Hwl Hpref)) ->
      Is_node_in f (n_eqs n).
  Proof.
    intros * Hisin; simpl in Hisin.
    remember (fby_equations _ _ _) as res; destruct res as [eqs' st'].
    symmetry in Heqres.
    eapply fby_equations_Is_node_in in Heqres; eauto.
  Qed.

  Fact normfby_global_names : forall G Hwl Hprefs,
      List.map n_name (normfby_global G Hwl Hprefs) = List.map n_name G.
  Proof.
    induction G; intros *; simpl; eauto.
    f_equal; eauto.
  Qed.

  Fact normfby_node_ordered : forall G n to_cut Hunt Hpref,
      Ordered_nodes (n::G) ->
      Ordered_nodes (normfby_node to_cut n Hunt Hpref::G).
  Proof.
    intros * Hordered.
    inv Hordered.
    constructor; eauto.
    intros f Hisin.
    eapply normfby_node_Is_node_in in Hisin; auto.
  Qed.

  Lemma normfby_global_ordered : forall G Hwl Hprefs,
      Ordered_nodes G ->
      Ordered_nodes (normfby_global G Hwl Hprefs).
  Proof with eauto.
    intros * Hord.
    induction Hord; simpl; constructor...
    - intros f Hisin; simpl.
      eapply normfby_node_Is_node_in in Hisin.
      eapply H in Hisin. destruct Hisin as [Hname Hnexists].
      split; auto.
      rewrite <- CommonList.Exists_map in *.
      rewrite normfby_global_names...
    - simpl.
      rewrite <- (Forall_map (fun n => ~(n_name nd = n))) in *.
      rewrite normfby_global_names...
  Qed.

  (** ** Conclusion *)

  Lemma normalize_global_ordered : forall G G' Hwl Hprefs,
      Ordered_nodes G ->
      normalize_global G Hwl Hprefs = Errors.OK G' ->
      Ordered_nodes G'.
  Proof.
    intros * Hord Hnorm.
    unfold normalize_global in Hnorm. destruct (Cau.check_causality _); inv Hnorm.
    eapply normfby_global_ordered, unnest_global_ordered, Hord.
  Qed.

End NORDERED.

Module NOrderedFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Cau : LCAUSALITY Ids Op Syn)
       (Lord : LORDERED Ids Op Syn)
       (Norm : NORMALIZATION Ids Op OpAux Syn Cau)
       <: NORDERED Ids Op OpAux Syn Cau Lord Norm.
  Include NORDERED Ids Op OpAux Syn Cau Lord Norm.
End NOrderedFun.
