From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Permutation.
From Coq Require Import Decidable.
From Coq Require Import Omega.
From Coq Require Import Setoid Morphisms.

From compcert Require Import common.Errors.

From Velus Require Import Common Clocks.
From Velus Require Import Operators Environment.
From Velus Require Import AcyGraph.
From Velus Require Import Lustre.LSyntax Lustre.LClocking Lustre.LCausality.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

(** * Conservation of causality through normalization *)

Module Type NCAUSALITY
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (Import Cau : LCAUSALITY Ids Op OpAux Cks Syn)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (Import Norm : NORMALIZATION Ids Op OpAux Cks Syn Cau).

  Import Fresh Tactics.

  (** Some auxiliary stuff *)

  Fact in_vars_defined_concat : forall x eqs eqs',
      In eqs eqs' ->
      In x (vars_defined eqs) ->
      In x (vars_defined (concat eqs')).
  Proof.
    intros * Hin1 Hin2.
    unfold vars_defined in *. rewrite flat_map_concat_map in *.
    apply in_concat in Hin2 as [xs [Hin2 Hin3]].
    apply in_map_iff in Hin3 as [[xs' es] [? Hin3]]; simpl in *; subst.
    eapply incl_concat_map with (x0:=(xs, es)); simpl; auto.
    eapply in_concat'; eauto.
  Qed.

  Fact vars_defined_combine : forall xs es,
      length xs = length es ->
      vars_defined (combine xs es) = concat xs.
  Proof.
    intros * Hlen.
    unfold vars_defined. rewrite flat_map_concat_map, combine_map_fst'; auto.
  Qed.

  (** ** Causality of the second phase of normalization *)

  Hint Constructors Is_free_in_clock.

  Fact add_whens_const_Is_free_left : forall ck ty c,
      forall x, Is_free_left x 0 (add_whens (Econst c) ty ck) ->
           Is_free_in_clock x ck.
  Proof.
    induction ck as [|? ? ? (?&?)]; intros * Hfree; inv Hfree; simpl in *.
    destruct H1 as [[_ ?]|?]; subst; auto.
    - inv H; eauto.
      rewrite add_whens_numstreams in H3; auto. inv H3.
  Qed.

  Fact add_whens_enum_Is_free_left : forall ck ty k,
      forall x, Is_free_left x 0 (add_whens (Eenum k ty) ty ck) ->
           Is_free_in_clock x ck.
  Proof.
    induction ck as [|? ? ? (?&?)]; intros * Hfree; inv Hfree; simpl in *.
    destruct H1 as [[_ ?]|?]; subst; auto.
    - inv H; eauto.
      rewrite add_whens_numstreams in H3; auto. inv H3.
  Qed.

  Definition st_clocks (st : fresh_st (Op.type * clock)) :=
    idck (st_anns st).

  Fact st_clocks_st_ids : forall st,
      map fst (st_clocks st) = st_ids st.
  Proof.
    intros *.
    unfold st_clocks, st_ids, idty, idck.
    repeat rewrite map_map. apply map_ext.
    intros (?&?&?); auto.
  Qed.

  (** A variable is used to calculate a clock, either directly or indirectly *)
  Definition used_in_clock {a v} (g: AcyGraph v a) x ck :=
    Is_free_in_clock x ck \/ (exists x', is_trans_arc g x x' /\ Is_free_in_clock x' ck).

  (** A variable is used to calculate a reset, either directly or indirectly *)
  Definition used_in_reset {v a} (g : AcyGraph v a) x y :=
    PS.Exists (fun y' => x = y' \/ is_trans_arc g x y') y.

  Lemma used_in_clock_trans :
    forall {v a} (g : AcyGraph v a) x y ck,
      is_trans_arc g x y ->
      used_in_clock g y ck ->
      used_in_clock g x ck.
  Proof.
    intros * Ha [?|(?&?&?)].
    - right. exists y; auto.
    - right. exists x0; split; auto.
      etransitivity; eauto.
  Qed.

  Lemma used_in_reset_trans :
    forall {v a} (g : AcyGraph v a) x y xr,
      is_trans_arc g x y ->
      used_in_reset g y xr ->
      used_in_reset g x xr.
  Proof.
    intros * Ha (x&In&[?|?]); subst; exists x; split; eauto.
    right.
    etransitivity; eauto.
  Qed.

  Lemma used_in_clock_reset_add_arc' :
    forall {v a} (g : AcyGraph v a) x' y' (g' : AcyGraph v (add_arc x' y' a)) x ck xr,
      used_in_clock g x ck \/ used_in_reset g x xr ->
      used_in_clock g' x ck \/ used_in_reset g' x xr.
  Proof.
    intros * [[?|(?&?&?)]|?].
    - left; left; auto.
    - left; right.
      exists x0. split; auto.
      apply add_arc_spec2; auto.
    - right.
      destruct H as (z&?&[?|?]); subst; exists z; split; eauto.
      right. apply add_arc_spec2; auto.
  Qed.

  Local Ltac destruct_conj_disj :=
    match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : _ \/ _ |- _ => destruct H
    end; subst.

  Lemma used_in_clock_reset_add_arc :
    forall {v a} (g : AcyGraph v a) x' y' (g' : AcyGraph v (add_arc x' y' a)) x y ck xr,
      y <> y' ->
      (forall x, is_trans_arc g x y -> used_in_clock g x ck \/ used_in_reset g x xr) ->
      is_trans_arc g' x y ->
      used_in_clock g' x ck \/ used_in_reset g' x xr.
  Proof.
    intros * Hneq Hack Ha.
    apply add_arc_spec2 in Ha.
    repeat destruct_conj_disj.
    - apply Hack in H.
      eapply used_in_clock_reset_add_arc'; eauto.
    - congruence.
    - apply Hack in H0.
      eapply used_in_clock_reset_add_arc' in H0 as [?|?]; eauto.
      + left. eapply used_in_clock_trans; eauto.
        apply add_arc_spec2; auto.
      + right. eapply used_in_reset_trans; eauto.
        apply add_arc_spec2; auto.
    - congruence.
    - eapply Hack in H0.
      eapply used_in_clock_reset_add_arc' in H0 as [?|?]; eauto.
      + left. eapply used_in_clock_trans; eauto.
        unfold is_arc. apply add_arc_spec2; auto 8.
      + right. eapply used_in_reset_trans; eauto.
        apply add_arc_spec2; auto 8.
  Qed.

  Lemma used_in_clock_add_after :
    forall {v a} (g : AcyGraph v a) preds x' (g' : AcyGraph v (add_after preds x' a)) x ck,
      used_in_clock g x ck ->
      used_in_clock g' x ck.
  Proof.
    intros * [?|(?&?&?)].
    - left; auto.
    - right.
      exists x0. split; auto.
      apply add_after_spec2; auto.
  Qed.

  Lemma used_in_reset_add_after :
    forall {v a} (g : AcyGraph v a) preds x' (g' : AcyGraph v (add_after preds x' a)) x y,
      used_in_reset g x y ->
      used_in_reset g' x y.
  Proof.
    intros * (x'&?&[?|?]); subst; exists x'; split; eauto.
    right. apply add_after_spec2; auto.
  Qed.

  Lemma used_in_clock_reset_add_between' :
    forall {v a} (g : AcyGraph v a) preds x' y' (g' : AcyGraph v (add_between preds x' y' a)) x ck xr,
      ~PS.In y' preds ->
      ~ PS.Exists (fun p => has_trans_arc a y' p) preds ->
      used_in_clock g x ck \/ used_in_reset g x xr ->
      used_in_clock g' x ck \/ used_in_reset g' x xr.
  Proof.
    intros * Hnin1 Hnin2 [[?|(?&?&?)]|?].
    - left; left; auto.
    - left; right.
      exists x0. split; auto.
      eapply add_between_spec2; eauto.
    - right. destruct H as (z&?&[?|?]); subst; exists z; split; eauto.
      right. eapply add_between_spec2; eauto.
  Qed.

  Lemma used_in_clock_reset_add_between :
    forall {v a} (g : AcyGraph v a) preds x' y' (g' : AcyGraph (PS.add x' v) (add_between preds x' y' a)) x y ck xr,
      ~PS.In y' preds ->
      ~PS.Exists (fun p => has_trans_arc a y' p) preds ->
      y <> y' ->
      y <> x' ->
      ~PS.In x' v ->
      (forall x, is_trans_arc g x y -> used_in_clock g x ck \/ used_in_reset g x xr) ->
      is_trans_arc g' x y ->
      used_in_clock g' x ck \/ used_in_reset g' x xr.
  Proof.
    intros * Hnin1 Hnin2 Hneq1 Hneq2 Hnin3 Hack Ha.
    unfold is_trans_arc in Ha. rewrite add_between_spec2 in Ha; eauto.
    repeat destruct_conj_disj; try congruence.
    3,4,6,7:(apply Hack, used_in_clock_reset_add_between' with (g'0:=g') in H0 as [?|?]; eauto).
    1-11:try solve [left; eapply used_in_clock_trans; eauto;
                    unfold is_trans_arc; rewrite add_between_spec2; eauto 10].
    1-7:try solve [right; eapply used_in_reset_trans; eauto;
                   unfold is_trans_arc; rewrite add_between_spec2; eauto 10].
    - eapply Hack in H. eapply used_in_clock_reset_add_between' with (g'0:=g') in H; eauto.
    - (* x' cant be a vertex ! *)
      exfalso.
      eapply is_trans_arc_is_vertex with (g0:=g) in H0 as (?&?); eauto.
    - (* x' cant be a vertex ! *)
      exfalso.
      eapply is_trans_arc_is_vertex with (g0:=g) in H0 as (?&?); eauto.
  Qed.

  (** *** Causality invariant *)

  Definition causal_inv vars eqs st :=
    NoDupMembers vars /\
    st_valid_after st norm2 (PSP.of_list (map fst vars)) /\
    exists v a (g : AcyGraph v a),
      graph_of_eqs (vars ++ st_clocks st) eqs g.

  Instance causal_inv_Proper:
    Proper (@Permutation (ident * clock) ==> @Permutation equation ==> @eq (fresh_st (Op.type * clock)) ==> @Basics.impl)
           causal_inv.
  Proof.
    intros ? ? Hp1 ? ? Hp2 ? st Heq (Hnd&Hvalid&v&a&g&?); subst.
    repeat split.
    - rewrite <- Hp1. assumption.
    - rewrite <- ps_from_list_ps_of_list in *. rewrite <- Hp1. assumption.
    - exists v. exists a. exists g.
      now rewrite <- Hp1, <- Hp2.
  Qed.

  Fact graph_of_eqs_ck_causal_inv : forall {v a} vars eqs (g : AcyGraph v a),
      NoDupMembers vars ->
      ~PS.In norm2 norm1_prefs ->
      Forall (AtomOrGensym norm1_prefs) (map fst vars) ->
      graph_of_eqs vars eqs g ->
      causal_inv vars eqs init_st.
  Proof.
    intros * Hndup Hg.
    repeat (split; auto).
    - eapply init_st_valid; eauto.
      intros ? Hin. rewrite ps_of_list_In in Hin.
      eapply Forall_forall in H; eauto.
    - exists v, a, g.
      unfold st_clocks; rewrite init_st_anns, app_nil_r; auto.
  Qed.

  Fact vars_defined_In : forall x xs es eqs,
      In (xs, es) eqs ->
      In x xs ->
      In x (vars_defined eqs).
  Proof.
    intros * Hin Hin'.
    unfold vars_defined. rewrite in_flat_map.
    exists (xs, es); auto.
  Qed.

  Fact causal_inv_add_init : forall vars eqs x ck xr e st st',
      causal_inv vars eqs st ->
      wc_clock (vars++st_clocks st) ck ->
      (forall x, Is_free_left x 0 e -> Is_free_in_clock x ck \/ PS.In x xr) ->
      PS.For_all (fun xr => exists ckr, In (xr, ckr) vars) xr ->
      fresh_ident norm2 (OpAux.bool_velus_type, ck) st = (x, st') ->
      causal_inv vars (([x], [e])::eqs) st'.
  Proof.
    intros * (Hnd&Hvalid&v&a&g&(Hv&Ha)) Hwc Hfree Hxr Hfresh.
    repeat constructor; auto. eapply fresh_ident_st_valid in Hfresh; eauto.

    assert (~PS.In x v) as Hnv.
    { intro contra. rewrite Hv in contra.
      eapply Facts.fresh_ident_nIn'' in Hfresh; eauto.
      rewrite ps_of_list_In, map_app, st_clocks_st_ids in contra; auto. }

    (* First add the variable *)
    assert (AcyGraph (PS.add x v)
                     (add_after (PS.union (collect_free_clock ck) xr) x a)) as g'.
    { apply add_after_AcyGraph'; auto.
      - intro contra. rewrite PS.union_spec, collect_free_clock_spec in contra.
        destruct contra as [contra|contra].
        + eapply wc_clock_is_free_in, fst_InMembers in Hwc; eauto.
          eapply Facts.fresh_ident_nIn'' in Hfresh; eauto.
          rewrite map_app, st_clocks_st_ids in Hwc; auto.
        + apply Hnv. rewrite Hv, map_app.
          eapply Hxr in contra as (?&?).
          eapply ps_of_list_In, in_app_iff, or_introl, fst_InMembers, In_InMembers; eauto.
      - intros ? Hin. rewrite PS.union_spec, collect_free_clock_spec in Hin.
        destruct Hin as [Hin|Hin].
        + eapply wc_clock_is_free_in, fst_InMembers in Hwc; eauto.
          rewrite Hv, ps_of_list_In; auto.
        + rewrite Hv, map_app.
          eapply Hxr in Hin as (?&?).
          eapply ps_of_list_In, in_app_iff, or_introl, fst_InMembers, In_InMembers; eauto.
    }
    eexists. eexists. exists g'. split.

    - (* vertices *)
      unfold vertices; simpl. rewrite Hv.
      repeat rewrite <- ps_from_list_ps_of_list.
      rewrite add_ps_from_list_cons, map_app, map_app, Permutation_middle.
      apply fresh_ident_anns in Hfresh.
      unfold st_clocks. rewrite Hfresh. reflexivity.

    - (* arcs (add the equation) *)
      intros * Hdep.
      unfold is_arc. rewrite add_after_spec.
      destruct Hdep as [Hdep|Hdep]; eauto.
      + inversion_clear Hdep as [?? Hk|?? Hex]. 2:(left; eapply Ha; left; eauto).
        destruct Hk as (?&Hnth&Hfree'); simpl in *.
        rewrite nth_error_length_nth in Hnth.
        specialize (Hnth xH) as (Hl&Hnth).
        rewrite Nat.lt_1_r in Hl; subst.
        inv Hfree'; [|inv H3].
        right; split; auto.
        rewrite PS.union_spec, collect_free_clock_spec.
        eapply Hfree in H3 as [?|?]; eauto.
      + destruct Hdep as (?&Hin&Hfree').
        unfold st_clocks in Hin.
        erewrite fresh_ident_anns in Hin; eauto; simpl in *.
        rewrite <- Permutation_middle in Hin. inv Hin. 2:(left; apply Ha; right; eauto).
        inv H. right; split; auto.
        rewrite PS.union_spec, collect_free_clock_spec; auto.
  Qed.

  Fact init_var_for_clock_causal_inv :
    forall vars eqs ck xr x eqs' st st',
      wc_clock vars ck ->
      Forall (fun '(xr, (ckr, _)) => In (xr, ckr) vars) xr ->
      causal_inv vars eqs st ->
      init_var_for_clock ck xr st = (x, eqs', st') ->
      causal_inv vars (eqs++eqs') st'.
  Proof.
    intros * Hwc Hwcr Hinv Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
    rewrite Permutation_app_comm; simpl.
    eapply causal_inv_add_init; simpl. 1,5:eauto.
    eapply wc_clock_incl; eauto; eapply incl_appl; reflexivity.
    - intros ? Hfree; simpl.
      inv Hfree.
      destruct H1 as [H1|(?&?)].
      left; inv H1; [|inv H4]; eapply add_whens_enum_Is_free_left; eauto.
      right. eapply ps_of_list_In.
      rewrite Exists_map in H0. eapply Exists_exists in H0 as ((?&?)&In&?). inv H0.
      eapply in_map with (f:=fst) in In; eauto.
    - intros ? In. apply ps_of_list_In in In. simpl_In. destruct x1 as (?&?&?).
      eapply Forall_forall in Hwcr; eauto; simpl in *; eauto.
  Qed.

  Lemma causal_inv_insert_eq {prefs} :
    forall (G: @global prefs) vars st st' x x' ty ck e e1 e2 eqs,
      wl_exp G e2 ->
      In (x, ck) (vars++st_clocks st) ->
      numstreams e = 1 ->
      fresh_ident norm2 (ty, ck) st = (x', st') ->
      causal_inv vars (([x], [e]) :: eqs) st ->
      (forall y, Is_free_left y 0 e1 -> (y = x' \/ Is_free_left y 0 e \/ Is_free_in_clock y ck)) ->
      (forall y, Is_free_left y 0 e2 -> Is_free_left y 0 e \/ Is_free_in_clock y ck) ->
      causal_inv vars (([x], [e1]) :: ([x'], [e2]) :: eqs) st'.
  Proof.
    intros * Hwl Hck Hnum Hfresh (?&?&v&a&g&(Hv&Ha)) Hf1 Hf2.
    repeat split; eauto.

    (* if y is in e2, then its in e, so x depends on it *)
    assert (forall y, Is_free_left y 0 e2 \/ Is_free_in_clock y ck -> is_arc g y x) as Hax.
    { intros y [Hfree|Hfree].
      - eapply Hf2 in Hfree as [Hfree|Hfree].
        + apply Ha. left. left.
          exists 0. repeat split; auto. left; auto.
          rewrite Hnum; auto.
        + apply Ha. right. eauto.
      - apply Ha. right. exists ck; split; auto.
    }

    (* We can build a new graph where x depends on x' *)
    remember (PS.union (nth 0 (collect_free_left e2) PS.empty) (collect_free_clock ck)) as preds.
    assert (AcyGraph (PS.add x' v) (add_between preds x' x a)) as g'.
    { eapply add_between_AcyGraph with (g0:=g); subst; eauto.
      - intros ? Hin.
        erewrite PS.union_spec, collect_free_left_spec, collect_free_clock_spec in Hin; eauto.
        apply Hax, is_arc_is_vertex in Hin as (?&?); auto.
      - unfold is_vertex. rewrite Hv.
        rewrite ps_of_list_In.
        rewrite in_map_iff. exists (x, ck); auto.
      - intros ? Hin.
        erewrite PS.union_spec, collect_free_left_spec, collect_free_clock_spec in Hin; eauto.
      - intro contra. apply Hv, ps_of_list_In in contra.
        eapply Facts.fresh_ident_nIn'' in Hfresh; eauto.
        apply Hfresh. rewrite <- st_clocks_st_ids, <- map_app; auto.
    }

    assert (~ PS.In x preds) as Hnin1.
    { intro contra; subst.
      erewrite PS.union_spec, collect_free_left_spec, collect_free_clock_spec in contra; eauto.
      eapply Hax, has_arc_irrefl in contra; eauto.
    }
    assert (~ PS.Exists (fun p : PS.elt => has_trans_arc a x p) preds) as Hnin2.
    { intros (?&Hin&Ha''); subst.
      erewrite PS.union_spec, collect_free_left_spec, collect_free_clock_spec in Hin; eauto.
      eapply Hax in Hin. eapply is_trans_arc_Asymmetric with (g0:=g) in Ha''; eauto.
      eapply Ha''. left; eauto.
    }
    assert (~ PS.Exists (fun p : PS.elt => has_arc a x p) preds) as Hnin3.
    { intros (x0&Hin&Ha''); subst.
      eapply Hnin2. exists x0. split; auto.
    }

    eexists. eexists. exists g'. split.

    - (* vertices *)
      unfold vertices; simpl. rewrite Hv.
      repeat rewrite <- ps_from_list_ps_of_list.
      rewrite add_ps_from_list_cons, map_app, map_app, Permutation_middle.
      apply fresh_ident_anns in Hfresh.
      unfold st_clocks. rewrite Hfresh. reflexivity.

    - (* arcs (add the equation) *)
      intros * Hdep.
      unfold is_arc. rewrite add_between_spec; eauto.
      destruct Hdep as [Hdep|Hdep]; [inv Hdep;[|inv H2]|].
      + destruct H2 as (?&Hnth&?); simpl in *.
        rewrite nth_error_length_nth in Hnth.
        specialize (Hnth xH) as (Hlen&Hnth).
        apply Nat.lt_1_r in Hlen; subst. inv H1; [|inv H6].
        apply Hf1 in H6 as [?|[?|?]]; subst; simpl; auto 10.
        * left. apply Ha. left. left.
          exists 0. repeat split; auto. left; auto.
          rewrite Hnum; auto.
        * left. apply Ha. right; eauto.
      + destruct H3 as (?&Hnth&?); simpl in *.
        rewrite nth_error_length_nth in Hnth.
        specialize (Hnth xH) as (Hlen&Hnth).
        apply Nat.lt_1_r in Hlen; subst. inv H1; [|inv H6].
        right; left. split; auto.
        erewrite PS.union_spec, collect_free_left_spec; eauto.
      + left. apply Ha. left. right; auto.
      + destruct Hdep as (ck'&Hin&Hfree).
        unfold st_clocks in Hin. erewrite fresh_ident_anns in Hin; eauto; simpl in Hin.
        rewrite <- Permutation_middle in Hin. inv Hin.
        2:(left; apply Ha; right; eauto).
        inv H1. right. left. split; auto.
        rewrite PS.union_spec, collect_free_clock_spec; auto.
  Qed.

  Fact fby_equation_causal {prefs} : forall (G: @global prefs) vars to_cut eq eqs eqs' st st',
      Forall (unnested_equation G) (eq::eqs) ->
      wc_env vars ->
      wc_equation G vars eq ->
      causal_inv vars (eq::eqs) st ->
      fby_equation to_cut eq st = (eqs', st') ->
      causal_inv vars (eqs++eqs') st'.
  Proof.
    intros * Hunt Hwenv Hwc Hinv Hfby.
    inv_fby_equation Hfby to_cut eq; try destruct x3 as (ty&ck&name).
    - destruct PS.mem; repeat inv_bind.
      1,2:rewrite Permutation_app_comm; simpl; auto.
      eapply causal_inv_insert_eq; eauto. 3:simpl; auto.
      + destruct Hwc as (Hwc&_&_); apply Forall_singl in Hwc; eauto.
      + destruct Hwc as (_&_&Hwc). apply Forall2_singl in Hwc; auto.
        apply in_or_app; left; auto.
      + intros ? Hfree. inv Hfree. left; auto.
    - repeat inv_bind.
      unfold init_var_for_clock in *. destruct (fresh_ident _ _) eqn:Hfresh; repeat inv_bind.
      simpl in *.
      rewrite <- Permutation_middle, <-(Permutation_middle eqs), <-(Permutation_middle eqs), app_nil_r; simpl.
      assert (In (x, ck) (vars)) as Hin.
      { destruct Hwc as (_&_&Hwc). apply Forall2_singl in Hwc; auto. }
      eapply causal_inv_insert_eq
        with (e1:=Ecase (Evar x3 (OpAux.bool_velus_type, (ck, Some x3))) [None; Some [x0]]
                       [Efby [add_whens (init_type ty) ty ck] [x1] [] [(ty, (ck, name))]]
                       ([ty], (ck, name)))
             (G0:=G)in Hinv.
      eapply causal_inv_insert_eq with (G0:=G); eauto. 1-11:simpl; eauto.
      2,6:apply in_or_app; auto.
      1,4:repeat constructor; simpl; auto.
      1,5,6:apply add_whens_wl; auto.
      1,2,4:destruct ck as [|?? (?&?)], ty; simpl; auto.
      4,5:destruct ck as [|?? (?&?)]; simpl; auto.
      3,4:rewrite Forall_map; eapply Forall_forall; intros (?&?) ?; auto.
      + destruct Hwc as (Hwc&_). apply Forall_singl in Hwc. inv Hwc. inv H5; eauto.
      + inv Hunt. inv H2. 2:(inv H1; inv H).
        rewrite app_nil_r, length_annot_numstreams. apply normalized_lexp_numstreams; auto.
      + intros ? Hfree; simpl.
        inv Hfree.
        destruct H2 as [(?&Hfree)|[Hfree|Hfree]].
        * right; left. inv Hfree. constructor; auto.
        * right; left. constructor. right; left; auto.
        * inv Hfree; inv H4; auto.
      + intros ? Hfree. inv Hfree. destruct H2 as [Hfree|(_&Hfree)]; inv Hfree. 2:inv H4.
        destruct ty; simpl in *; eauto using add_whens_const_Is_free_left, add_whens_enum_Is_free_left.
      + intros ? Hfree; simpl.
        inv Hfree. destruct H2 as [(?&Hfree)|[Hfree|Hfree]].
        * inv Hfree; auto.
        * inv Hfree. destruct H1 as (?&?&?); try congruence.
          apply Exists_singl in H1 as (?&Heq&?); inv Heq. inv H; [|inv H5].
          right; left; auto.
        * inv Hfree; inv H4; auto.
          destruct H2 as [Hfree|(?&Hfree)]; inv Hfree.
          2:inv H5.
          destruct ty; simpl in *; eauto using add_whens_const_Is_free_left, add_whens_enum_Is_free_left.
      + intros ? Hfree; simpl.
        inv Hfree.
        destruct H2 as [Hfree|(?&Hfree)].
        * inv Hfree; [|inv H4]. eapply add_whens_enum_Is_free_left in H4; eauto.
        * rewrite Exists_map in Hfree. eapply Exists_exists in Hfree as ((?&?)&In&Hfree). inv Hfree.
          left. constructor. right. split; auto.
          eapply Forall2_ignore1, Forall_forall in Hr as (?&?&Hex); eauto. destruct Hex as (?&?); subst.
          eapply Exists_exists; eauto.
    - repeat inv_bind.
      unfold init_var_for_clock in H.
      destruct (fresh_ident _ _) eqn:Hident. repeat inv_bind.
      simpl in *. rewrite <- Permutation_middle, <- (Permutation_middle eqs). rewrite app_nil_r.
      eapply causal_inv_insert_eq with (G0:=G); eauto. 3:auto.
      + repeat constructor; simpl; eauto.
        1-2:eapply add_whens_wl; eauto.
        2-3:destruct ck as [|?? (?&?)]; simpl; auto.
        1,2:rewrite Forall_map; eapply Forall_forall; intros (?&?) ?; auto.
      + destruct Hwc as (_&_&Hwc). apply Forall2_singl in Hwc; auto.
        apply in_or_app; left; auto.
      + intros ? Hf. inv Hf.
        destruct H1 as [(_&Hf)|Hf]; [|inv Hf]; auto 10.
        * inv Hf; auto.
        * inversion_clear H as [?? (?&Heq&?)|?? [?? (?&Heq&Hex)|?? [|]]]; try inv Heq.
          inversion_clear Hex as [???? Hfree|???? [|]].
          right. constructor; auto.
      + intros ? Hfree; simpl.
        inv Hfree.
        destruct H1 as [H1|(?&?)].
        * inv H1; [|inv H4]. eapply add_whens_enum_Is_free_left in H4; eauto.
        * rewrite Exists_map in H0. eapply Exists_exists in H0 as ((?&?)&In&?). inv H0.
          left. constructor. do 2 right. split; auto.
          eapply Forall2_ignore1, Forall_forall in Hr as (?&?&Hex); eauto. destruct Hex as (?&?); subst.
          eapply Exists_exists; eauto.
    - rewrite Permutation_app_comm; auto.
  Qed.

  Fact fby_equations_causal' {prefs} :
    forall (G: @global prefs) vars to_cut eqs ceqs eqs' st st',
      wc_env vars ->
      Forall (unnested_equation G) (ceqs++eqs) ->
      Forall (wc_equation G vars) eqs ->
      causal_inv vars (ceqs++eqs) st ->
      fby_equations to_cut eqs st = (eqs', st') ->
      causal_inv vars (ceqs++eqs') st'.
  Proof.
    induction eqs; intros * Henv Hunt Hwc Hinv Hfby;
      unfold fby_equations in Hfby; simpl in *; repeat inv_bind; simpl; auto.
    inv Hwc.
    rewrite <- Permutation_middle in Hinv.
    eapply fby_equation_causal in H as Hcaus'. 3,4,5:eauto.
    2:rewrite Permutation_middle; eauto.
    rewrite <- app_assoc, (Permutation_app_comm eqs), app_assoc in Hcaus'.
    eapply IHeqs in Hcaus'; auto.
    - rewrite app_assoc; eauto.
    - apply Forall_app in Hunt as [Hunt1 Hunt2]. inv Hunt2.
      repeat rewrite Forall_app. repeat split; auto.
      eapply fby_equation_unnested_eq; eauto.
    - unfold fby_equations; repeat inv_bind; repeat eexists; eauto; inv_bind; auto.
  Qed.

  Corollary fby_equations_causal {prefs} :
    forall (G: @global prefs) vars to_cut eqs eqs' st st',
      wc_env vars ->
      Forall (unnested_equation G) eqs ->
      Forall (wc_equation G vars) eqs ->
      causal_inv vars eqs st ->
      fby_equations to_cut eqs st = (eqs', st') ->
      causal_inv vars eqs' st'.
  Proof.
    intros * Hwenv Hunt Hwl Hcaus Hfby.
    eapply fby_equations_causal' with (ceqs:=[]) in Hfby; simpl; eauto.
  Qed.

  Fact Permutation_map_fst {B} : forall (xs : list (ident * B)) ys,
      Permutation (map fst xs) ys ->
      exists zs, Permutation xs zs /\ ys = map fst zs.
  Proof.
    induction xs; intros * Hperm.
    - apply Permutation_nil in Hperm; subst.
      exists []; auto.
    - destruct a as [id b].
      specialize (in_split id ys) as (ys1&ys2&?); subst.
      { rewrite <- Hperm. left; auto. }
      apply Permutation_cons_app_inv in Hperm.
      apply IHxs in Hperm as (?&?&?).
      symmetry in H0. apply map_app' in H0 as (xs1&xs2&?&?&?); subst.
      exists (xs1 ++ (id, b) :: xs2); simpl; split.
      + rewrite <- Permutation_middle. apply perm_skip; auto.
      + rewrite map_app; simpl. reflexivity.
  Qed.

  Lemma normfby_node_causal : forall G n,
      unnested_node G n ->
      wc_global G ->
      wc_node G n ->
      node_causal n ->
      node_causal (normfby_node n).
  Proof.
    intros * Hun HwcG Hwc Hcaus.
    destruct Hcaus as (v&a&g&Hg).
    unfold node_causal, graph_of_node in *. simpl.
    destruct (fby_equations _ _ _) as (eqs'&st') eqn:Hres.
    eapply fby_equations_causal in Hres. 2-5:eauto.
    3:destruct Hwc as (_&_&_&?); eauto.
    - destruct Hres as (?&?&?&?&g''&(Ha&Hv)).
      eexists. eexists. exists g''.
      repeat rewrite idck_app. repeat rewrite <- app_assoc.
      rewrite (Permutation_app_comm (idck (st_anns st')) (idck (n_out n))).
      repeat rewrite <- idck_app. split.
      + rewrite Ha. unfold st_clocks.
        rewrite <- idck_app. repeat rewrite <- app_assoc. reflexivity.
      + intros * Hdep. apply Hv.
        repeat rewrite idck_app in Hdep. repeat rewrite idck_app.
        unfold st_clocks. repeat rewrite <- app_assoc. assumption.
    - destruct Hwc as (_&_&?&_).
      rewrite (Permutation_app_comm (n_vars _)); eauto.
    - eapply graph_of_eqs_ck_causal_inv; eauto.
      + rewrite NoDupMembers_idck, fst_NoDupMembers.
        apply node_NoDup.
      + eapply norm2_not_in_norm1_prefs.
      + pose proof (n_good n) as (Good&_).
        eapply Forall_incl; eauto.
        rewrite map_fst_idck.
        apply incl_map, incl_appr', incl_appr', incl_appl, incl_refl.
  Qed.

  Lemma normfby_global_causal : forall G,
      unnested_global G ->
      wc_global G ->
      Forall node_causal (nodes G) ->
      Forall node_causal (nodes (normfby_global G)).
  Proof.
    unfold unnested_global, wc_global, CommonTyping.wt_program, CommonProgram.units.
    intros (?&nds). induction nds; intros * Hun Hwc Hcaus; simpl; auto.
    inversion_clear Hun as [|?? (?&?)]. inversion_clear Hwc as [|?? (?&?)]. inv Hcaus.
    constructor; eauto.
    eapply normfby_node_causal; simpl; eauto.
  Qed.

End NCAUSALITY.

Module NCausalityFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (Cau : LCAUSALITY Ids Op OpAux Cks Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (Norm : NORMALIZATION Ids Op OpAux Cks Syn Cau)
       <: NCAUSALITY Ids Op OpAux Cks Syn Cau Clo Norm.
  Include NCAUSALITY Ids Op OpAux Cks Syn Cau Clo Norm.
End NCausalityFun.
