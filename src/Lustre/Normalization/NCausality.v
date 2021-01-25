From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Permutation.
From Coq Require Import Decidable.
From Coq Require Import Omega.
From Coq Require Import Setoid Morphisms.

From compcert Require Import common.Errors.

From Velus Require Import Common Ident Clocks.
From Velus Require Import Operators Environment.
From Velus Require Import AcyGraph.
From Velus Require Import Lustre.LSyntax Lustre.LClocking Lustre.LCausality.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

(** * Conservation of causality through normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type NCAUSALITY
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Cau : LCAUSALITY Ids Op Syn)
       (Import Clo : LCLOCKING Ids Op Syn)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn Cau).

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

  (** If an expression is wc with regards to an environment, all it's
      left-free vars appear in the environment *)
  Fact wc_exp_Is_free_left : forall G env e x k,
      wc_exp G env e ->
      Is_free_left x k e ->
      InMembers x env.
  Proof.
    Local Hint Resolve In_InMembers.
    Local Ltac solve_forall_exists H1 H2 H3 :=
      try eapply Is_free_left_list_Exists in H3; try destruct H3 as (?&H3);
      eapply Forall_Forall in H1; [|eapply H2];
      eapply Forall_Exists in H1; [|eapply H3];
      eapply Exists_exists in H1 as (?&?&(?&?)&?); eauto.
    induction e using exp_ind2; intros * Hwc Hfree;
      inv Hwc; inv Hfree; eauto.
    - (* binop *) destruct H1; eauto.
    - (* fby *) solve_forall_exists H H4 H3.
    - (* arrow *)
      destruct H3 as [Hex|Hex]. solve_forall_exists H H4 Hex. solve_forall_exists H0 H5 Hex.
    - (* when *)
      destruct H2 as [[? Hex]|Hex]; subst; eauto.
      solve_forall_exists H H4 Hex.
    - (* merge *)
      destruct H3 as [[? Hex]|[Hex|Hex]]; subst; eauto.
      solve_forall_exists H H5 Hex. solve_forall_exists H0 H6 Hex.
    - (* ite *)
      destruct H3 as [[? Hex]|[Hex|Hex]]; eauto.
      solve_forall_exists H H6 Hex. solve_forall_exists H0 H7 Hex.
    - (* app *) solve_forall_exists H0 H5 H10.
    - (* app (reset) *)
      destruct H13 as [Hex|Hex]; eauto. solve_forall_exists H0 H5 Hex.
  Qed.

  (* Lemma Is_free_in_clock_dec : forall x ck, *)
  (*     {Is_free_in_clock x ck} + {~Is_free_in_clock x ck}. *)
  (* Proof. *)
  (*   induction ck. *)
  (*   - right. intro contra; inv contra. *)
  (*   - destruct IHck; auto. *)
  (*     destruct (ident_eqb x i) eqn:Heqb. *)
  (*     * rewrite ident_eqb_eq in Heqb; subst; auto. *)
  (*     * rewrite ident_eqb_neq in Heqb. *)
  (*       right. intro contra. inv contra; auto. *)
  (* Qed. *)

  (* Fact Is_causal_ck_Is_free_in_clock : forall eqs xs x ck, *)
  (*     Is_causal_ck eqs ((x, ck)::xs) -> *)
  (*     (forall y, Is_free_in_clock y ck -> InMembers y xs). *)
  (* Proof. *)
  (*   intros * Hcaus y Hfree. *)
  (*   inv Hcaus. *)
  (*   specialize (H1 y). apply H1. *)
  (*   right; auto. *)
  (* Qed. *)

  (* Corollary Is_causal_ck_Is_free_in_clock' : forall eqs xs, *)
  (*     Is_causal_ck eqs xs -> *)
  (*     Forall (fun '(_, ck) => forall y, Is_free_in_clock y ck -> InMembers y xs) xs. *)
  (* Proof. *)
  (*   induction xs; intros * Hcaus; auto. *)
  (*   destruct a as (x&ck). constructor. *)
  (*   - intros. eapply Is_causal_ck_Is_free_in_clock in Hcaus; eauto. *)
  (*     right; auto. *)
  (*   - inv Hcaus. eapply IHxs in H2. *)
  (*     eapply Forall_impl; [|eauto]. intros (?&?) ???. *)
  (*     right; auto. *)
  (* Qed. *)

  (* Fact Is_causal_ck_nIs_free_in_clock : forall eqs xs x ck, *)
  (*     NoDupMembers ((x, ck)::xs) -> *)
  (*     Is_causal_ck eqs ((x, ck)::xs) -> *)
  (*     Forall (fun '(x', ck') => ~Is_free_in_clock x ck') xs. *)
  (* Proof. *)
  (*   intros * Hnd Hcaus. *)
  (*   inv Hcaus. eapply Is_causal_ck_Is_free_in_clock' in H2. *)
  (*   eapply Forall_impl; [|eauto]. intros (?&?) ? contra. *)
  (*   eapply H in contra. inv Hnd; auto. *)
  (* Qed. *)

  (** ** Causality of the second phase of normalization *)

  (** *** Recover info about the init equations in the state *)

  Definition st_inits (st : fresh_st (Op.type * clock * bool)) :=
    idck (idty (filter (fun '(_, (ty, _, b)) => b && (ty ==b Op.bool_type)) (st_anns st))).

  Fact st_follows_inits_incl : forall st st',
      st_follows st st' ->
      incl (st_inits st) (st_inits st').
  Proof.
    intros * Hfollows.
    eapply st_follows_incl in Hfollows.
    unfold st_inits, idck, idty.
    apply incl_map, incl_map, incl_filter; auto.
  Qed.

  Fact st_inits_find_Some : forall st x (ck : nclock) p,
      find (fun '(_, (ty, ck', isinit)) => isinit && (ck' ==b fst ck) && (ty ==b Op.bool_type)) (st_anns st) = Some (x, p) ->
      In (x, (fst ck)) (st_inits st).
  Proof.
    intros * Hfind.
    apply find_some in Hfind as [Hin Hf].
    destruct p as [[ty ck'] isinit].
    repeat rewrite Bool.andb_true_iff in Hf. destruct Hf as [[Hty Hck] ?]; auto.
    unfold st_inits.
    rewrite In_idck_exists. exists ty.
    rewrite In_idty_exists. exists isinit.
    rewrite filter_In; split; auto.
    - rewrite clock_eqb_eq in Hck; subst. assumption.
    - rewrite Hty, H; auto.
  Qed.

  Fact st_inits_find_None : forall st (ck : nclock),
      find (fun '(_, (ty, ck', isinit)) => isinit && (ck' ==b fst ck) && (ty ==b Op.bool_type)) (st_anns st) = None ->
      ~In (fst ck) (map snd (st_inits st)).
  Proof.
    intros * Hfind.
    intro contra. unfold st_inits in contra. repeat simpl_In.
    apply filter_In in H0 as [Hin Heq].
    eapply find_none in Hfind; eauto. simpl in *.
    apply Bool.andb_true_iff in Heq as [Hb Hty]; subst; simpl in Hfind.
    rewrite Hty, equiv_decb_refl in Hfind; simpl in Hfind. congruence.
  Qed.

  Fact fresh_ident_false_st_inits : forall (st st' : fresh_st (Op.type * clock * bool)) a id,
      fresh_ident (a, false) st = (id, st') ->
      st_inits st' = st_inits st.
  Proof.
    intros * Hfresh.
    unfold st_inits. destruct a as [ty ck].
    apply fresh_ident_anns in Hfresh. rewrite Hfresh.
    simpl; auto.
  Qed.

  Fact fresh_ident_true_st_inits : forall st st' ck id,
      fresh_ident ((Op.bool_type, ck), true) st = (id, st') ->
      st_inits st' = (id, ck)::st_inits st.
  Proof.
    intros * Hfresh.
    unfold st_inits.
    apply fresh_ident_anns in Hfresh. rewrite Hfresh.
    simpl. rewrite equiv_decb_refl; auto.
  Qed.

  Fact init_var_for_clock_In_st_inits : forall ck x eqs' st st',
      init_var_for_clock ck st = (x, eqs', st') ->
      In (x, ck) (st_inits st').
  Proof.
    intros * Hinit.
    eapply init_var_for_clock_In in Hinit.
    unfold st_inits.
    simpl_In. exists Op.bool_type. simpl_In. exists true.
    rewrite filter_In. split; auto.
    rewrite equiv_decb_refl; auto.
  Qed.

  Hint Constructors Is_free_in_clock.

  Fact add_whens_Is_free_left : forall ck ty c,
      forall x, Is_free_left x 0 (add_whens (Econst c) ty ck) ->
           Is_free_in_clock x ck.
  Proof.
    induction ck; intros * Hfree; inv Hfree; simpl in *.
    destruct H1 as [[_ ?]|?]; subst; auto.
    - inv H; eauto.
      rewrite add_whens_numstreams in H3; auto. inv H3.
  Qed.

  (* (** *** Small properties on the clocking of generated equations *) *)

  (* Fact init_var_for_clock_clocksof : forall ck id eqs' st st', *)
  (*     init_var_for_clock ck st = (id, eqs', st') -> *)
  (*     Forall (fun eq => clocksof (snd eq) = [ck]) eqs'. *)
  (* Proof. *)
  (*   intros * Hinit. *)
  (*   unfold init_var_for_clock in Hinit. *)
  (*   destruct (find _ _); repeat inv_bind. *)
  (*   - destruct p; inv Hinit; auto. *)
  (*   - destruct (fresh_ident _ _); inv Hinit; auto. *)
  (* Qed. *)

  (* Fact fby_iteexp_clocksof : forall e0 e ty ck name e' eqs' st st', *)
  (*     fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') -> *)
  (*     Forall (fun eq => clocksof (snd eq) = [ck]) eqs'. *)
  (* Proof. *)
  (*   intros * Hfby; simpl in *. *)
  (*   repeat inv_bind; constructor; auto. *)
  (*   eapply init_var_for_clock_clocksof; eauto. *)
  (* Qed. *)

  Definition st_clocks (st : fresh_st (Op.type * clock * bool)) :=
    idck (idty (st_anns st)).

  Fact st_clocks_st_ids : forall st,
      map fst (st_clocks st) = st_ids st.
  Proof.
    intros *.
    unfold st_clocks, st_ids, idty, idck.
    repeat rewrite map_map. apply map_ext.
    intros (?&(?&?)&?); auto.
  Qed.

  Fact st_inits_incl_st_clocks : forall st,
      incl (st_inits st) (st_clocks st).
  Proof.
    intros st ? Hin.
    unfold st_inits, st_clocks in *.
    repeat simpl_In. exists x. simpl_In. exists x0.
    eapply in_filter; eauto.
  Qed.

  Corollary st_inits_incl_st_ids : forall st,
      incl (map fst (st_inits st)) (st_ids st).
  Proof.
    intros st.
    rewrite <- st_clocks_st_ids. eapply incl_map.
    apply st_inits_incl_st_clocks.
  Qed.

  (** A variable is used to calculate a clock, either directly or indirectly *)
  Definition used_in_clock {a v} (g: AcyGraph v a) x ck :=
    Is_free_in_clock x ck \/ (exists x', is_trans_arc g x x' /\ Is_free_in_clock x' ck).

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

  Lemma used_in_clock_add_arc' :
    forall {v a} (g : AcyGraph v a) x' y' (g' : AcyGraph v (add_arc x' y' a)) x ck,
      used_in_clock g x ck ->
      used_in_clock g' x ck.
  Proof.
    intros * [?|(?&?&?)].
    - left; auto.
    - right.
      exists x0. split; auto.
      apply add_arc_spec2; auto.
  Qed.

  Local Ltac destruct_conj_disj :=
    match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : _ \/ _ |- _ => destruct H
    end; subst.

  Lemma used_in_clock_add_arc :
    forall {v a} (g : AcyGraph v a) x' y' (g' : AcyGraph v (add_arc x' y' a)) x y ck,
      y <> y' ->
      (forall x, is_trans_arc g x y -> used_in_clock g x ck) ->
      is_trans_arc g' x y ->
      used_in_clock g' x ck.
  Proof.
    intros * Hneq Hack Ha.
    apply add_arc_spec2 in Ha.
    repeat destruct_conj_disj.
    - apply Hack in H.
      eapply used_in_clock_add_arc'; eauto.
    - congruence.
    - apply Hack in H0.
      eapply used_in_clock_add_arc' in H0; eauto.
      eapply used_in_clock_trans; eauto.
      apply add_arc_spec2; auto.
    - congruence.
    - eapply Hack in H0.
      eapply used_in_clock_add_arc' in H0; eauto.
      eapply used_in_clock_trans; eauto.
      unfold is_arc. apply add_arc_spec2; auto 8.
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

  Lemma used_in_clock_add_between' :
    forall {v a} (g : AcyGraph v a) preds x' y' (g' : AcyGraph v (add_between preds x' y' a)) x ck,
      ~PS.In y' preds ->
      ~ PS.Exists (fun p => has_trans_arc a y' p) preds ->
      used_in_clock g x ck ->
      used_in_clock g' x ck.
  Proof.
    intros * Hnin1 Hnin2 [?|(?&?&?)].
    - left; auto.
    - right.
      exists x0. split; auto.
      eapply add_between_spec2; eauto.
  Qed.

  Lemma used_in_clock_add_between :
    forall {v a} (g : AcyGraph v a) preds x' y' (g' : AcyGraph (PS.add x' v) (add_between preds x' y' a)) x y ck,
      ~PS.In y' preds ->
      ~PS.Exists (fun p => has_trans_arc a y' p) preds ->
      y <> y' ->
      y <> x' ->
      ~PS.In x' v ->
      (forall x, is_trans_arc g x y -> used_in_clock g x ck) ->
      is_trans_arc g' x y ->
      used_in_clock g' x ck.
  Proof.
    intros * Hnin1 Hnin2 Hneq1 Hneq2 Hnin3 Hack Ha.
    unfold is_trans_arc in Ha. rewrite add_between_spec2 in Ha; eauto.
    repeat destruct_conj_disj; try congruence.
    3,4,6,7:(apply Hack, used_in_clock_add_between' with (g'0:=g') in H0; [| | |eauto]; eauto;
             eapply used_in_clock_trans; eauto;
             unfold is_trans_arc; rewrite add_between_spec2; eauto 10).
    - eapply Hack in H. eapply used_in_clock_add_between' with (g'0:=g') in H; eauto.
    - (* x' cant be a vertex ! *)
      exfalso.
      eapply is_trans_arc_is_vertex with (g0:=g) in H0 as (?&?); eauto.
    - (* x' cant be a vertex ! *)
      exfalso.
      eapply is_trans_arc_is_vertex with (g0:=g) in H0 as (?&?); eauto.
  Qed.

  (** *** Causality invariant
      We add an invariant to our causality hypothesis:
      Variables marked as init variables only depend on the variables of their clocks
      This is necessary so that we can add arcs using them later on
   *)

  Definition causal_inv vars eqs (st : fresh_st (Op.type * clock * bool)) :=
    NoDupMembers vars /\
    st_valid_after st (PSP.of_list (map fst vars)) /\
    exists v a (g : AcyGraph v a),
      graph_of_eqs (vars ++ st_clocks st) eqs g /\
      Forall (fun '(y, ck) => forall x, is_trans_arc g x y -> used_in_clock g x ck) (st_inits st).

  Instance causal_inv_Proper:
    Proper (@Permutation (ident * clock) ==> @Permutation equation ==> @eq (fresh_st (Op.type * clock * bool)) ==> @Basics.impl)
           causal_inv.
  Proof.
    intros ? ? Hp1 ? ? Hp2 ? st Heq (Hnd&Hvalid&v&a&g&?&?); subst.
    repeat split.
    - rewrite <- Hp1. assumption.
    - rewrite <- ps_from_list_ps_of_list in *. rewrite <- Hp1. assumption.
    - exists v. exists a. exists g. split; auto.
      rewrite <- Hp1, <- Hp2. assumption.
  Qed.

  Fact graph_of_eqs_ck_causal_inv : forall {v a} vars eqs id0 (g : AcyGraph v a),
      NoDupMembers vars ->
      Forall (fun id => (id < id0)%positive) (map fst vars) ->
      graph_of_eqs vars eqs g ->
      causal_inv vars eqs (init_st id0).
  Proof.
    intros * Hndup Hlt Hg.
    repeat (split; auto).
    - apply init_st_valid.
      rewrite <- ps_from_list_ps_of_list, PS_For_all_Forall'; auto.
    - exists v, a, g. split; auto.
      + unfold st_clocks; rewrite init_st_anns, app_nil_r; auto.
      + unfold st_inits; rewrite init_st_anns; simpl; auto.
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

  Fact causal_inv_add_init : forall vars eqs x ck e st st',
      causal_inv vars eqs st ->
      wc_clock (vars++st_clocks st) ck ->
      (forall x, Is_free_left x 0 e -> Is_free_in_clock x ck) ->
      ~In ck (map snd (st_inits st)) ->
      fresh_ident (Op.bool_type, ck, true) st = (x, st') ->
      causal_inv vars (([x], [e])::eqs) st'.
  Proof.
    intros * (Hnd&Hvalid&v&a&g&(Hv&Ha)&Hinits) Hwc Hfree Hnin Hfresh.
    repeat constructor; auto. eapply fresh_ident_st_valid in Hfresh; eauto.

    assert (~PS.In x v) as Hnv.
    { intro contra. rewrite Hv in contra.
      eapply Facts.fresh_ident_nIn'' in Hfresh; eauto.
      rewrite ps_of_list_In, map_app, st_clocks_st_ids in contra; auto. }

    (* First add the variable *)
    assert (AcyGraph (PS.add x v) (add_after (collect_free_clock ck) x a)) as g'.
    { apply add_after_AcyGraph'; auto.
      + intro contra. rewrite collect_free_clock_spec in contra.
        eapply wc_clock_is_free_in, fst_InMembers in Hwc; eauto.
        eapply Facts.fresh_ident_nIn'' in Hfresh; eauto.
        rewrite map_app, st_clocks_st_ids in Hwc; auto.
      + intros ? Hin. rewrite collect_free_clock_spec in Hin.
        eapply wc_clock_is_free_in, fst_InMembers in Hwc; eauto.
        rewrite Hv, ps_of_list_In; auto.
    }
    eexists. eexists. exists g'. split; [split|].

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
        destruct Hk as (?&Hl&Hnth&Hfree'); simpl in *.
        rewrite Nat.lt_1_r in Hl; subst.
        inv Hfree'; [|inv H3].
        right; split; auto.
        rewrite collect_free_clock_spec. auto.
      + destruct Hdep as (?&Hin&Hfree').
        unfold st_clocks in Hin.
        erewrite fresh_ident_anns in Hin; eauto; simpl in *.
        rewrite <- Permutation_middle in Hin. inv Hin. 2:(left; apply Ha; right; eauto).
        inv H. right; split; auto.
        rewrite collect_free_clock_spec. auto.

    - (* st_inits *)
      erewrite fresh_ident_true_st_inits; eauto.
      constructor; auto.
      + intros y Ha'.
        eapply add_after_has_trans_arc3 in Ha' as [Hin|(?&Hin&Ha')]; eauto; [left|right].
        1,2:rewrite collect_free_clock_spec in Hin; auto.
        eexists; split; eauto.
        apply add_after_spec2; auto.
      + eapply Forall_impl_In; [|eauto].
        intros (?&?) Hin Ha' ? Ha''.
        apply add_after_spec2 in Ha'' as [?|[(_&?)|[(_&Ha'')|[(_&?)|(_&Ha'')]]]]; subst.
        2-5:exfalso.
        3,5:eapply is_trans_arc_is_vertex with (g0:=g) in Ha'' as (?&?); eauto.
        2,3:(eapply Facts.fresh_ident_nIn; eauto;
             apply st_inits_incl_st_ids; eapply in_map with (f:=fst) in Hin; eauto).
        eapply Ha' in H as [?|(?&?&?)]; [left|right]; auto.
        eexists; split; eauto. unfold is_arc. apply add_after_spec2; auto.
  Qed.

  Fact init_var_for_clock_causal_inv :
    forall vars eqs ck x eqs' st st',
      wc_clock vars ck ->
      causal_inv vars eqs st ->
      init_var_for_clock ck st = (x, eqs', st') ->
      causal_inv vars (eqs++eqs') st'.
  Proof.
    intros * Hwc Hinv Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (find _ _) eqn:Hfind.
    - destruct p; inv Hinit; rewrite app_nil_r; auto.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
      rewrite Permutation_app_comm; simpl.
      eapply causal_inv_add_init. 1,5:eauto.
      + eapply wc_clock_incl; eauto. eapply incl_appl; reflexivity.
      + intros ? Hfree. inv Hfree.
        inv H1. 2:inv H4.
        eapply add_whens_Is_free_left; eauto.
      + eapply st_inits_find_None with (ck:=(ck, None)) in Hfind; eauto.
  Qed.

  Lemma causal_inv_replace_eq : forall vars st x xinit ck e e' eqs,
      In (x, ck) (vars ++ st_clocks st) ->
      ~InMembers x (st_inits st) ->
      In (xinit, ck) (st_inits st) ->
      numstreams e = 1 ->
      causal_inv vars (([x], [e]) :: eqs) st ->
      (forall y, Is_free_left y 0 e' -> (Is_free_left y 0 e \/ y = xinit)) ->
      causal_inv vars (([x], [e']) :: eqs) st.
  Proof.
    intros * Hck Hnck Hinit Hnum (?&?&v&a&g&(Hv&Ha)&?) Hfree.
    repeat split; auto.

    (* We can build a new graph where x depends on xinit *)
    assert (AcyGraph v (add_arc xinit x a)) as g'.
    { econstructor; eauto.
      - intro contra; subst.
        eapply Hnck, In_InMembers; eauto.
      - rewrite Hv, ps_of_list_In, in_map_iff.
        exists (xinit, ck); split; auto.
        apply in_app_iff; right.
        apply st_inits_incl_st_clocks; auto.
      - rewrite Hv, ps_of_list_In, in_map_iff.
        exists (x, ck); auto.
      - intro contra.
        eapply Forall_forall in H1; eauto.
        eapply H1 in contra as [?|(x'&?&?)].
        + eapply is_trans_arc_Irreflexive with (g0:=g); eauto.
          left. eapply Ha.
          right. eauto.
        + eapply is_trans_arc_Asymmetric; eauto.
          left. eapply Ha. right; eauto.
    }
    eexists; eexists. exists g'. split; [split|]; auto.

    (* All the arcs are here *)
    - intros ? ? [Hdep|Hdep]; [inv Hdep|].
      1-3:unfold is_arc; rewrite add_arc_spec. 2,3:left.
      + destruct H3 as (?&Hlen&Hnth&Hfree'); simpl in *.
        apply Nat.lt_1_r in Hlen; subst.
        inv Hfree'; [|inv H6].
        apply Hfree in H6 as [Hfree'|?]; subst; clear Hfree.
        * left. apply Ha. left. left.
          exists 0. repeat split; auto.
          left; auto. rewrite Hnum; auto.
        * eapply Forall_forall in H1; eauto.
      + apply Ha. left; right; auto.
      + apply Ha. right; auto.

    (* And it preserves the invariant *)
    - eapply Forall_impl_In; [|eauto].
      intros (?&?) Hin Ha' ? Ha''.
      eapply used_in_clock_add_arc; eauto.
      intros ?; subst.
      eapply Hnck, In_InMembers; eauto.
  Qed.

  Fact depends_on_vars_defined : forall eqs x y,
      depends_on eqs x y ->
      In x (vars_defined eqs).
  Proof.
    intros * Hdep.
    unfold depends_on in Hdep.
    apply Exists_exists in Hdep as ((?&?)&?&?&Hl&Hnth&_).
    eapply vars_defined_In; eauto.
    rewrite <- Hnth. apply nth_In; auto.
  Qed.

  Lemma causal_inv_insert_eq :
    forall G vars st st' x x' ty ck e e1 e2 eqs,
      wl_exp G e2 ->
      In (x, ck) vars ->
      ~InMembers x (st_inits st) ->
      numstreams e = 1 ->
      fresh_ident (ty, ck, false) st = (x', st') ->
      causal_inv vars (([x], [e]) :: eqs) st ->
      (forall y, Is_free_left y 0 e1 -> (y = x' \/ Is_free_left y 0 e)) ->
      (forall y, Is_free_left y 0 e2 -> Is_free_left y 0 e) ->
      causal_inv vars (([x], [e1]) :: ([x'], [e2]) :: eqs) st'.
  Proof.
    intros * Hwl Hck Hnck Hnum Hfresh (?&?&v&a&g&(Hv&Ha)&Hinits) Hf1 Hf2.
    repeat split; eauto.

    (* if y is in e2, then its in e, so x depends on it *)
    assert (forall y, Is_free_left y 0 e2 \/ Is_free_in_clock y ck -> is_arc g y x) as Hax.
    { intros y [Hfree|Hfree].
      - eapply Hf2 in Hfree.
        apply Ha. left. left.
        exists 0. repeat split; auto. left; auto.
        rewrite Hnum; auto.
      - apply Ha. right. exists ck; split; auto.
        apply in_or_app; auto.
    }

    (* We can build a new graph where x depends on x' *)
    remember (PS.union (nth 0 (collect_free_left e2) PS.empty) (collect_free_clock ck)) as preds.
    assert (AcyGraph (PS.add x' v) (add_between preds x' x a)) as g'.
    { eapply add_between_AcyGraph with (g0:=g); subst; eauto.
      - intros ? Hin.
        erewrite PS.union_spec, collect_free_left_spec, collect_free_clock_spec in Hin; eauto.
        apply Hax, is_arc_is_vertex in Hin as (?&?); auto.
      - unfold is_vertex. rewrite Hv.
        rewrite ps_of_list_In, map_app. apply in_or_app; left.
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

    eexists. eexists. exists g'. split; [split|]; auto.

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
      + destruct H2 as (?&?&?&?); simpl in *.
        apply Nat.lt_1_r in H1; subst. inv H3; [|inv H6].
        apply Hf1 in H6 as [?|?]; subst; auto 10.
        left. apply Ha. left. left.
        exists 0. repeat split; auto. left; auto.
        rewrite Hnum; auto.
      + destruct H3 as (?&?&?&?); simpl in *.
        apply Nat.lt_1_r in H1; subst. inv H3; [|inv H6].
        right; left. split; auto.
        rewrite PS.union_spec, collect_free_left_spec; eauto.
      + left. apply Ha. left. right; auto.
      + destruct Hdep as (ck'&Hin&Hfree).
        unfold st_clocks in Hin. erewrite fresh_ident_anns in Hin; eauto; simpl in Hin.
        rewrite <- Permutation_middle in Hin. inv Hin.
        2:(left; apply Ha; right; eauto).
        inv H1. right. left. split; auto.
        rewrite PS.union_spec, collect_free_clock_spec; auto.

    - (* the new arcs preserve the invariant *)
      erewrite fresh_ident_false_st_inits; eauto.
      eapply Forall_impl_In; [|eauto].
      intros (?&?) Hin Ha' ? Ha''.
      eapply used_in_clock_add_between; eauto.
      1-3:intro contra; subst.
      + eapply Hnck, In_InMembers; eauto.
      + eapply Facts.fresh_ident_nIn in Hfresh; eauto.
        apply Hfresh, st_inits_incl_st_ids.
        rewrite in_map_iff. exists (x', c); auto.
      + unfold is_vertex in contra. rewrite Hv in contra.
        eapply Facts.fresh_ident_nIn'' in Hfresh; eauto.
        rewrite ps_of_list_In, map_app, st_clocks_st_ids in contra; auto.
  Qed.

  Lemma causal_inv_insert_eq_with_xinit :
    forall G vars st st' x x' xinit ty ck e e1 e2 eqs,
      wl_exp G e2 ->
      In (x, ck) vars ->
      ~InMembers x (st_inits st) ->
      In (xinit, ck) (st_inits st) ->
      numstreams e = 1 ->
      fresh_ident (ty, ck, false) st = (x', st') ->
      causal_inv vars (([x], [e]) :: eqs) st ->
      (forall y, Is_free_left y 0 e1 -> (y = x' \/ Is_free_left y 0 e \/ y = xinit)) ->
      (forall y, Is_free_left y 0 e2 -> Is_free_in_clock y ck) ->
      causal_inv vars (([x], [e1]) :: ([x'], [e2]) :: eqs) st'.
  Proof.
    intros * Hwl Hck Hnck Hinit Hnum Hfresh (?&?&v&a&g&(Hv&Ha)&Hinits) Hf1 Hf2.
    repeat split; eauto.

    (* if y is in e2, then its in e, so x depends on it *)
    assert (forall y, Is_free_left y 0 e2 \/ Is_free_in_clock y ck -> is_arc g y x) as Hax.
    { intros y [Hfree|Hfree]; [apply Hf2 in Hfree|].
      1,2:apply Ha; right; exists ck; split; [apply in_or_app|]; auto.
    }

    (* We can build a new graph where x depends on x' *)
    remember (PS.union (nth 0 (collect_free_left e2) PS.empty) (collect_free_clock ck)) as preds.
    assert (AcyGraph (PS.add x' v) (add_between preds x' x a)) as g'.
    { eapply add_between_AcyGraph with (g0:=g); subst; eauto.
      - intros ? Hin.
        erewrite PS.union_spec, collect_free_left_spec, collect_free_clock_spec in Hin; eauto.
        apply Hax, is_arc_is_vertex in Hin as (?&?); auto.
      - unfold is_vertex. rewrite Hv.
        rewrite ps_of_list_In, map_app. apply in_or_app; left.
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

    (* Also x must depend on xinit *)
    assert (AcyGraph (PS.add x' v) (add_arc xinit x (add_between preds x' x a))) as g''.
    { eapply AGadda; eauto.
      - intro contra; subst.
        eapply Hnck, In_InMembers; eauto.
      - apply PSF.add_2.
        rewrite Hv, ps_of_list_In, in_map_iff.
        exists (xinit, ck); split; auto.
        apply in_app_iff; right.
        apply st_inits_incl_st_clocks; auto.
      - apply PSF.add_2.
        rewrite Hv, ps_of_list_In, in_map_iff.
        exists (x, ck); split; [|apply in_or_app]; auto.
      - intro contra.
        assert (has_trans_arc a x xinit) as contra'.
        { rewrite add_between_spec2 in contra; eauto.
          repeat destruct_conj_disj; auto.
          1-8:exfalso; auto.
          1,2:apply In_InMembers in Hinit; auto.
        } clear contra.
        eapply Forall_forall in Hinits; eauto.
        eapply Hinits in contra' as [?|(?&?&?)].
        + eapply has_arc_irrefl; eauto.
          eapply add_between_spec; eauto. left. eapply Ha.
          right. exists ck. split; eauto. apply in_or_app; auto.
        + eapply is_trans_arc_Asymmetric; eauto.
          left. eapply Ha. right. exists ck; split; eauto. apply in_or_app; auto.
    }
    eexists; eexists. exists g''. split; [split|]; auto.

    - (* vertices *)
      unfold vertices; simpl. rewrite Hv.
      repeat rewrite <- ps_from_list_ps_of_list.
      rewrite add_ps_from_list_cons, map_app, map_app, Permutation_middle.
      apply fresh_ident_anns in Hfresh.
      unfold st_clocks. rewrite Hfresh. reflexivity.

    - (* arcs (add the equation) *)
      intros * Hdep.
      unfold is_arc. rewrite add_arc_spec. repeat rewrite add_between_spec; eauto.
      destruct Hdep as [Hdep|Hdep]; [inv Hdep;[|inv H2]|].
      + destruct H2 as (?&?&?&?); simpl in *.
        apply Nat.lt_1_r in H1; subst. inv H3; [|inv H6].
        apply Hf1 in H6 as [?|[?|?]]; subst; auto 10.
        left. left. apply Ha. left. left.
        exists 0. repeat split; auto. left; auto.
        rewrite Hnum; auto.
      + destruct H3 as (?&?&?&?); simpl in *.
        apply Nat.lt_1_r in H1; subst. inv H3; [|inv H6].
        left. right; left. split; auto.
        rewrite PS.union_spec, collect_free_left_spec; eauto.
      + left. left. apply Ha. left. right; auto.
      + destruct Hdep as (ck'&Hin&Hfree).
        unfold st_clocks in Hin. erewrite fresh_ident_anns in Hin; eauto; simpl in Hin.
        rewrite <- Permutation_middle in Hin. inv Hin.
        2:(left; left; apply Ha; right; eauto).
        inv H1. left. right. left. split; auto.
        rewrite PS.union_spec, collect_free_clock_spec; auto.

    - (* the new arcs preserve the invariant *)
      erewrite fresh_ident_false_st_inits; eauto.
      eapply Forall_impl_In; [|eauto].
      intros (?&?) Hin Ha' ? Ha''.
      eapply used_in_clock_add_arc with (g0:=g'); eauto.
      1:intros contra; subst; eapply Hnck, In_InMembers; eauto.
      clear Ha''. intros ? Ha''.
      eapply used_in_clock_add_between; eauto.
      1-3:intro contra; subst.
      + eapply Hnck, In_InMembers; eauto.
      + eapply Facts.fresh_ident_nIn in Hfresh; eauto.
        apply Hfresh, st_inits_incl_st_ids.
        rewrite in_map_iff. exists (x', c); auto.
      + unfold is_vertex in contra. rewrite Hv in contra.
        eapply Facts.fresh_ident_nIn'' in Hfresh; eauto.
        rewrite ps_of_list_In, map_app, st_clocks_st_ids in contra; auto.
  Qed.

  Fact fby_equation_causal : forall G vars to_cut eq eqs eqs' st st',
      Forall unnested_equation (eq::eqs) ->
      wc_env vars ->
      wc_equation G vars eq ->
      causal_inv vars (eq::eqs) st ->
      fby_equation to_cut eq st = (eqs', st') ->
      causal_inv vars (eqs++eqs') st'.
  Proof.
    intros * Hunt Hwenv Hwc Hinv Hfby.
    inv_fby_equation Hfby to_cut eq; try destruct x2 as (ty&ck&name).
    - destruct PS.mem; repeat inv_bind.
      1,2:rewrite Permutation_app_comm; simpl; auto.
      eapply causal_inv_insert_eq; eauto. 4:simpl; auto.
      + destruct Hwc as (Hwc&_&_); apply Forall_singl in Hwc; eauto.
      + destruct Hwc as (_&_&Hwc). apply Forall2_singl in Hwc; auto.
      + destruct Hinv as (Hndup&Hvalid&_).
        destruct Hwc as (_&_&Hin). apply Forall2_singl in Hin.
        apply Facts.st_valid_after_NoDupMembers in Hvalid; auto.
        intro contra. apply InMembers_In in contra as (?&contra). apply st_inits_incl_st_clocks in contra.
        rewrite <- st_clocks_st_ids, <- map_app in Hvalid.
        apply In_InMembers in Hin. apply In_InMembers in contra.
        rewrite <- fst_NoDupMembers in Hvalid. eapply NoDupMembers_app_InMembers in Hvalid; eauto.
      + intros ? Hfree. inv Hfree. left; auto.
    - repeat inv_bind.
      assert (Hinit:=H). eapply init_var_for_clock_causal_inv in H; eauto.
      2:{ destruct Hwc as (_&_&Hwc). apply Forall2_singl in Hwc.
          eapply wc_env_var; eauto. }
      simpl in *. rewrite <- Permutation_middle, <- (Permutation_middle eqs).
      assert (In (x, ck) vars) as Hin.
      { destruct Hwc as (_&_&Hwc). apply Forall2_singl in Hwc; auto. }
      eapply causal_inv_insert_eq_with_xinit; eauto. 4:auto.
      + destruct Hwc as (Hwc&_). apply Forall_singl in Hwc.
        apply wc_exp_wl_exp in Hwc.
        inv Hwc.
        repeat (constructor; eauto); simpl.
        * apply add_whens_wl; auto.
        * rewrite app_nil_r, length_annot_numstreams, add_whens_numstreams; simpl; auto.
      + destruct H as (Hndup&Hvalid&_).
        destruct Hwc as (_&_&Hin'). apply Forall2_singl in Hin'.
        apply Facts.st_valid_after_NoDupMembers in Hvalid; auto.
        intro contra. apply InMembers_In in contra as (?&contra). apply st_inits_incl_st_clocks in contra.
        rewrite <- st_clocks_st_ids, <- map_app in Hvalid.
        apply In_InMembers in Hin'. apply In_InMembers in contra.
        rewrite <- fst_NoDupMembers in Hvalid. eapply NoDupMembers_app_InMembers in Hvalid; eauto.
      + eapply init_var_for_clock_In_st_inits in Hinit; eauto.
      + intros ? Hf. inv Hf.
        destruct H3 as [(_&Hf)|[Hf|Hf]]; auto 10.
        * inv Hf. right. right. split; auto.
        * inv Hf; inv H5; auto.
      + intros ? Hf. inv Hf.
        inv H3. 2:inv H6.
        apply add_whens_Is_free_left in H6; auto.
    - repeat inv_bind.
      assert (Hinit:=H). eapply init_var_for_clock_causal_inv in H; eauto.
      2:{ destruct Hwc as (_&_&Hwc). apply Forall2_singl in Hwc.
          eapply wc_env_var; eauto. }
      simpl in *. rewrite <- Permutation_middle.
      assert (In (x, ck) vars) as Hin.
      { destruct Hwc as (_&_&Hwc). apply Forall2_singl in Hwc; auto. }
      eapply causal_inv_replace_eq; eauto. 4:auto.
      + apply in_or_app; eauto.
      + intro contra. eapply fst_InMembers in contra. apply st_inits_incl_st_ids in contra.
        apply in_map with (f:=fst) in Hin.
        destruct H as (Hnd&Hvalid&_); eauto.
        eapply init_var_for_clock_In_st_inits in Hinit; eauto.
        apply Facts.st_valid_after_NoDupMembers in Hvalid; eauto.
        eapply NoDup_app_In in Hvalid; eauto.
      + apply init_var_for_clock_In_st_inits in Hinit; eauto.
      + intros y Hfree.
        inv Hfree. destruct H2 as [(_&?)|[Hfree|Hfree]].
        2,3:left; constructor; auto.
        inv H0; auto.
    - rewrite Permutation_app_comm; auto.
  Qed.

  Fact fby_equations_causal' :
    forall G vars to_cut eqs ceqs eqs' st st',
      wc_env vars ->
      Forall unnested_equation (ceqs++eqs) ->
      Forall (wc_equation G vars) eqs ->
      causal_inv vars (ceqs++eqs) st ->
      fby_equations to_cut eqs st = (eqs', st') ->
      causal_inv vars (ceqs++eqs') st'.
  Proof.
    induction eqs; intros * Henv Hunt Hwc Hinv Hfby;
      unfold fby_equations in Hfby; simpl in *; repeat inv_bind; simpl; auto.
    inv Hwc.
    rewrite <- Permutation_middle in Hinv.
    eapply fby_equation_causal in H as Hcaus'. 2,3,4,5:eauto.
    2:rewrite Permutation_middle; eauto.
    rewrite <- app_assoc, (Permutation_app_comm eqs), app_assoc in Hcaus'.
    eapply IHeqs in Hcaus'; eauto.
    - rewrite <- app_assoc in Hcaus'; eauto.
    - apply Forall_app in Hunt as [Hunt1 Hunt2]. inv Hunt2.
      repeat rewrite Forall_app. repeat split; auto.
      eapply fby_equation_unnested_eq; eauto.
    - unfold fby_equations; repeat inv_bind; repeat eexists; eauto; inv_bind; auto.
  Qed.

  Corollary fby_equations_causal :
    forall G vars to_cut eqs eqs' st st',
      wc_env vars ->
      Forall unnested_equation eqs ->
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

  Lemma normfby_node_causal : forall G n to_cut Hunt,
      wc_global G ->
      wc_node G n ->
      node_causal n ->
      node_causal (normfby_node to_cut n Hunt).
  Proof.
    intros * HwcG Hwc Hcaus.
    destruct Hcaus as (v&a&g&Hg).
    unfold node_causal, graph_of_node in *. simpl.
    remember (fby_equations _ _ _) as res. symmetry in Heqres. destruct res as [eqs' st'].
    eapply fby_equations_causal in Heqres; eauto; simpl in *.
    3:destruct Hwc as (_&_&_&?); eauto.
    - destruct Heqres as (?&?&?&?&g''&(Ha&Hv)&_).
      eexists. eexists. exists g''.
      repeat rewrite idck_app. repeat rewrite <- app_assoc.
      rewrite (Permutation_app_comm (idck (idty (st_anns st'))) (idck (n_out n))).
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
      + eapply Forall_incl. eapply first_unused_ident_gt; eauto.
        rewrite map_fst_idck.
        apply incl_tl, incl_tl, incl_map, incl_appr', incl_appr', incl_appl, incl_refl.
  Qed.

  Lemma normfby_global_causal : forall G Hunt,
      wc_global G ->
      Forall node_causal G ->
      Forall node_causal (normfby_global G Hunt).
  Proof.
    induction G; intros * Hwc Hcaus; auto.
    inv Hwc. inv Hcaus.
    constructor; eauto.
    eapply normfby_node_causal; eauto.
  Qed.

End NCAUSALITY.

Module NCausalityFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Cau : LCAUSALITY Ids Op Syn)
       (Clo : LCLOCKING Ids Op Syn)
       (Norm : NORMALIZATION Ids Op OpAux Syn Cau)
       <: NCAUSALITY Ids Op OpAux Syn Cau Clo Norm.
  Include NCAUSALITY Ids Op OpAux Syn Cau Clo Norm.
End NCausalityFun.
