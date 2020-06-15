From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

Require Import Omega.

From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LSemantics Lustre.LClockSemantics.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.FullNorm.
From Velus Require Import Lustre.Normalization.NTyping Lustre.Normalization.NClocking Lustre.Normalization.NOrdered.

(** * Correctness of the Normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type CORRECTNESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Str : COINDSTREAMS Op OpAux)
       (Import Syn : LSYNTAX Ids Op)
       (Import Typ : LTYPING Ids Op Syn)
       (Import Cl : LCLOCKING Ids Op Syn)
       (Import Ord : LORDERED Ids Op Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Syn Ord Str)
       (Import Norm : FULLNORM Ids Op OpAux Syn).

  Import Fresh Tactics.
  Module Import ClockSem := LClockSemanticsFun Ids Op OpAux Syn Typ Cl Ord Str Sem.
  Module Import Typ := NTypingFun Ids Op OpAux Syn Typ Norm.
  Module Clo := NClockingFun Ids Op OpAux Syn Cl Norm.
  Module Ord := NOrderedFun Ids Op OpAux Syn Ord Norm.
  Import List.

  CoFixpoint default_stream : Stream OpAux.value :=
    absent ⋅ default_stream.

  Fact sem_exp_numstreams : forall G H b e v,
      wl_exp G e ->
      sem_exp G H b e v ->
      length v = numstreams e.
  Proof with eauto.
    induction e using exp_ind2; intros v Hsem Hwl; inv Hwl; inv Hsem; simpl; auto.
    - (* fby *)
      repeat rewrite_Forall_forall.
      rewrite <- H9. rewrite <- H10.
      unfold annots; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite Forall2_map_2.
      rewrite_Forall_forall; solve_length.
      rewrite length_annot_numstreams. eapply H0; [| |eauto].
      + apply nth_In; congruence.
      + apply H5. apply nth_In; congruence.
    - (* when *)
      repeat rewrite_Forall_forall.
      rewrite <- H1. rewrite <- H7.
      unfold annots; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite Forall2_map_2.
      rewrite_Forall_forall; solve_length.
      rewrite length_annot_numstreams. eapply H0; [| |eauto].
      + apply nth_In; congruence.
      + apply H4. apply nth_In; congruence.
    - (* merge *)
      repeat rewrite_Forall_forall.
      rewrite <- H10. rewrite <- H11.
      unfold annots; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite Forall2_map_2.
      rewrite_Forall_forall; solve_length.
      rewrite length_annot_numstreams. eapply H0; [| |eauto].
      + apply nth_In; congruence.
      + apply H7. apply nth_In; congruence.
    - (* ite *)
      repeat rewrite_Forall_forall.
      rewrite <- H11. rewrite <- H15.
      unfold annots; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite Forall2_map_2.
      rewrite_Forall_forall; solve_length.
      rewrite length_annot_numstreams. eapply H0; [| |eauto].
      + apply nth_In; congruence.
      + apply H7. apply nth_In; congruence.
    - (* app *)
      inv H11.
      repeat rewrite_Forall_forall.
      unfold idents in H6.
      solve_length.
    - (* app (reset) *)
      specialize (H13 0). inv H13.
      repeat rewrite_Forall_forall.
      unfold idents in H5.
      solve_length.
  Qed.

  Corollary sem_exps_numstreams : forall G H b es vs,
      Forall (wl_exp G) es ->
      Forall2 (sem_exp G H b) es vs ->
      length (concat vs) = length (annots es).
  Proof.
    intros G H b es vs Hwt Hsem.
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

  (** Some additional stuff *)

  Import Permutation.

  Fact fresh_ident_refines {B V} : forall vars H H' a id (v : V) (st st' : fresh_st B),
      st_valid_after st (PSP.of_list vars) ->
      Env.dom H (vars++st_ids st) ->
      fresh_ident a st = (id, st') ->
      H' = Env.add id v H ->
      Env.refines eq H H'.
  Proof with eauto.
    intros vars H H' a id v st st' Hvalid Hdom Hfresh Heq.
    rewrite Heq.
    assert (st_valid_after st' (PSP.of_list vars)) as Hvalid' by eauto.
    eapply Env.refines_add...
    intro contra. erewrite Env.dom_use in contra; [| eauto].
    apply in_app_or in contra. destruct contra.
    + eapply Facts.fresh_ident_In in Hfresh.
      assert (In id (st_ids st')).
      { unfold st_ids, idty. repeat simpl_In; simpl in *.
        exists (id, a); auto. }
      apply st_valid_NoDup in Hvalid'.
      eapply NoDup_app_In in Hvalid'; [|eauto].
      apply Hvalid'; clear Hvalid'.
      rewrite ps_of_list_ps_to_list...
    + eapply Facts.fresh_ident_nIn in Hfresh...
  Qed.

  Fact idents_for_anns_NoDupMembers : forall anns ids st st' aft,
      st_valid_after st aft ->
      idents_for_anns anns st = (ids, st') ->
      NoDupMembers ids.
  Proof.
    intros anns ids st st' aft Hvalid Hids.
    eapply idents_for_anns_st_valid_after in Hvalid; eauto.
    apply idents_for_anns_vars_perm in Hids.
    apply st_valid_NoDup, NoDup_app_l in Hvalid.
    rewrite fst_NoDupMembers in *.
    rewrite <- Hids in Hvalid.
    apply NoDup_app_l in Hvalid; auto.
  Qed.

  Fact idents_for_anns_nIn : forall anns ids st st' aft,
      st_valid_after st aft ->
      idents_for_anns anns st = (ids, st') ->
      Forall (fun id => ~In id (st_ids st)) (map fst ids).
  Proof.
    intros anns ids st st' aft Hvalid Hids.
    eapply idents_for_anns_st_valid_after in Hvalid; eauto.
    apply st_valid_NoDup, NoDup_app_l in Hvalid.
    apply idents_for_anns_vars_perm in Hids.
    unfold st_ids in *.
    rewrite <- Hids in Hvalid.
    rewrite Forall_forall. intros x Hin.
    eapply NoDup_app_In; eauto.
  Qed.

  Fact idents_for_anns_dom {V} : forall vars H H' anns ids (vs : list V) st st',
      length vs = length ids ->
      st_valid_after st (PSP.of_list vars) ->
      Env.dom H (vars++st_ids st) ->
      idents_for_anns anns st = (ids, st') ->
      H' = Env.adds (map fst ids) vs H ->
      Env.dom H' (vars++st_ids st').
  Proof with eauto.
    intros vars H H' anns ids vs st st' Hlen Hvalid Hdom Hids Heq.
    apply idents_for_anns_vars_perm in Hids.
    rewrite Heq.
    apply Env.dom_adds with (ids0:=map fst ids) (vs0:=vs) in Hdom.
    2:(repeat rewrite_Forall_forall; solve_length).
    eapply Env.dom_Permutation; [|eauto].
    symmetry. rewrite Permutation_app_comm. rewrite <- app_assoc. apply Permutation_app_head.
    rewrite Permutation_app_comm. assumption.
  Qed.

  Fact idents_for_anns_refines {V} : forall vars H H' anns ids (vs : list V) st st',
      length vs = length ids ->
      st_valid_after st (PSP.of_list vars) ->
      Env.dom H (vars++st_ids st) ->
      idents_for_anns anns st = (ids, st') ->
      H' = Env.adds (map fst ids) vs H ->
      Env.refines eq H H'.
  Proof with eauto.
    intros vars H H' anns ids vs st st' Hlen Hvalid Hdom Hids Heq.
    assert (Forall (fun id => ~In id vars) (List.map fst ids)) as Hnvar.
    { assert (st_valid_after st' (PSP.of_list vars)) by eauto.
      apply idents_for_anns_incl_ids in Hids.
      solve_forall.
      apply Hids in H1. clear Hids.
      intro contra.
      apply st_valid_NoDup in H0.
      eapply NoDup_app_In in H0; [|eauto].
      apply H0. rewrite ps_of_list_ps_to_list... }
    rewrite Heq. apply Env.refines_adds.
    eapply idents_for_anns_nIn in Hids...
    rewrite Forall_forall in *. intros x1 Hin contra.
    erewrite Env.dom_use in contra...
    apply in_app_or in contra; destruct contra.
    + eapply Hnvar...
    + eapply Hids...
  Qed.

  Fact idents_for_anns'_NoDupMembers : forall anns ids st st' aft reusable,
      NoDup (map fst (Syn.anon_streams anns) ++ PS.elements reusable) ->
      st_valid_reuse st aft (ps_adds (map fst (Syn.anon_streams anns)) reusable) ->
      idents_for_anns' anns st = (ids, st') ->
      NoDupMembers ids.
  Proof.
    intros anns ids st st' aft reusable Hndup Hvalid Hids.
    eapply idents_for_anns'_st_valid in Hvalid; eauto.
    apply idents_for_anns'_vars_perm in Hids.
    apply st_valid_reuse_st_valid, st_valid_NoDup, NoDup_app_l in Hvalid.
    rewrite fst_NoDupMembers in *.
    rewrite <- Hids in Hvalid.
    apply NoDup_app_l in Hvalid; auto.
  Qed.

  Fact idents_for_anns'_nIn : forall anns ids st st' aft reusable,
      NoDup (map fst (Syn.anon_streams anns) ++ PS.elements reusable) ->
      st_valid_reuse st aft (ps_adds (map fst (Syn.anon_streams anns)) reusable) ->
      idents_for_anns' anns st = (ids, st') ->
      Forall (fun id => ~In id (st_ids st)) (map fst ids).
  Proof.
    intros anns ids st st' aft reusable Hndup Hvalid Hids.
    eapply idents_for_anns'_st_valid in Hvalid; eauto.
    apply st_valid_reuse_st_valid, st_valid_NoDup, NoDup_app_l in Hvalid.
    apply idents_for_anns'_vars_perm in Hids.
    unfold st_ids in *.
    rewrite <- Hids in Hvalid.
    rewrite Forall_forall. intros x Hin.
    eapply NoDup_app_In; eauto.
  Qed.

  Fact idents_for_anns'_dom {V} : forall vars H H' anns ids (vs : list V) st st',
      length vs = length ids ->
      st_valid_after st (PSP.of_list vars) ->
      Env.dom H (vars++st_ids st) ->
      idents_for_anns' anns st = (ids, st') ->
      H' = Env.adds (map fst ids) vs H ->
      Env.dom H' (vars++st_ids st').
  Proof with eauto.
    intros vars H H' anns ids vs st st' Hlen Hvalid Hdom Hids Heq.
    apply idents_for_anns'_vars_perm in Hids.
    rewrite Heq.
    apply Env.dom_adds with (ids0:=map fst ids) (vs0:=vs) in Hdom.
    2:(repeat rewrite_Forall_forall; solve_length).
    eapply Env.dom_Permutation; [|eauto].
    symmetry. rewrite Permutation_app_comm. rewrite <- app_assoc. apply Permutation_app_head.
    rewrite Permutation_app_comm. assumption.
  Qed.

  Fact idents_for_anns'_refines {V} : forall vars H H' anns ids (vs : list V) st st' reusable,
      length vs = length ids ->
      NoDup (map fst (Syn.anon_streams anns) ++ PS.elements reusable) ->
      st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (Syn.anon_streams anns)) reusable) ->
      Env.dom H (vars++st_ids st) ->
      idents_for_anns' anns st = (ids, st') ->
      H' = Env.adds (map fst ids) vs H ->
      Env.refines eq H H'.
  Proof with eauto.
    intros vars H H' anns ids vs st st' reusable Hndup Hlen Hvalid Hdom Hids Heq.
    assert (Forall (fun id => ~In id vars) (List.map fst ids)) as Hnvar.
    { assert (st_valid_reuse st' (PSP.of_list vars) reusable) by eauto.
      apply idents_for_anns'_incl_ids in Hids.
      solve_forall.
      apply Hids in H1. clear Hids.
      intro contra.
      apply st_valid_reuse_st_valid, st_valid_NoDup in H0.
      eapply NoDup_app_In in H0; [|eauto].
      apply H0. rewrite ps_of_list_ps_to_list... }
    rewrite Heq. apply Env.refines_adds.
    eapply idents_for_anns'_nIn in Hids...
    rewrite Forall_forall in *. intros x1 Hin contra.
    erewrite Env.dom_use in contra...
    apply in_app_or in contra; destruct contra.
    + eapply Hnvar...
    + eapply Hids...
  Qed.

  (** ** Relation between state and history *)

  (** We want to specify the semantics of the init equations created during the normalization
      with idents stored in the env *)

  (* Pas possible de prouver que c'est la semantique de Swhen false sans le lemme d'alignement...
     Ou alors il faut calculer les horloges differement *)

  CoFixpoint const_val (b : Stream bool) (v : Op.val) : Stream value :=
    (if Streams.hd b then present v else absent) ⋅ (const_val (Streams.tl b) v).

  Fact const_val_Cons : forall b bs v,
      const_val (b ⋅ bs) v =
      (if b then present v else absent) ⋅ (const_val bs v).
  Proof.
    intros b bs v.
    rewrite unfold_Stream at 1; reflexivity.
  Qed.

  Fact const_val_const : forall b c,
      Str.const b c ≡ const_val b (Op.sem_const c).
  Proof.
    cofix const_val_const.
    intros [b0 b] c; simpl.
    constructor; simpl; auto.
  Qed.

  CoFixpoint shift (v : Op.val) (str : Stream OpAux.value) :=
    match str with
    | (present v') ⋅ str' => (present v) ⋅ (shift v' str')
    | absent ⋅ str' => absent ⋅ (shift v str')
    end.

  Fact shift_Cons : forall v y ys,
      shift v (y ⋅ ys) =
      match y with
      | present v' => (present v) ⋅ (shift v' ys)
      | absent => absent ⋅ (shift v ys)
      end.
  Proof.
    intros v y ys.
    rewrite unfold_Stream at 1; simpl.
    destruct y; reflexivity.
  Qed.

  Add Parametric Morphism : shift
      with signature eq ==> @EqSt value ==> @EqSt value
    as shift_EqSt.
  Proof.
    cofix CoFix.
    intros v [x xs] [y ys] Heq.
    inv Heq; simpl in *; subst.
    constructor; simpl.
    + destruct y; auto.
    + destruct y; auto.
  Qed.

  Lemma shift_const : forall bs v,
      shift v (const_val bs v) ≡ (const_val bs v).
  Proof.
    cofix CoFix.
    intros [b bs] v.
    rewrite const_val_Cons.
    destruct b; rewrite shift_Cons; constructor; simpl; auto.
  Qed.

  Lemma ite_false : forall bs xs ys,
      synchronized xs bs ->
      synchronized ys bs ->
      ite (const_val bs false_val) xs ys ys.
  Proof.
    cofix CoFix.
    intros [b bs] xs ys Hsync1 Hsync2.
    rewrite const_val_Cons.
    inv Hsync1; inv Hsync2; constructor; auto.
  Qed.

  Lemma fby1_shift : forall bs v y ys,
      synchronized ys bs ->
      fby1 y (const_val bs v) ys (shift y ys).
  Proof with eauto.
    cofix fby1_shift.
    intros [b bs] v y ys Hsync.
    specialize (fby1_shift bs).
    inv Hsync;
      rewrite const_val_Cons; rewrite unfold_Stream; simpl.
    - constructor...
    - constructor...
  Qed.

  Lemma fby1_shift' : forall y y0s ys zs,
      fby1 y y0s ys zs ->
      zs ≡ (shift y ys).
  Proof.
    cofix CoFix.
    intros y y0s ys zs Hfby1.
    inv Hfby1; constructor; simpl; eauto.
  Qed.

  CoFixpoint prefix_with_val b (v : Op.val) (ys : Stream OpAux.value) :=
    match (Streams.hd b) with
    | true => shift v ys
    | false => absent ⋅ (prefix_with_val (Streams.tl b) v (Streams.tl ys))
    end.

  Fact prefix_with_val_Cons : forall b bs v ys,
      prefix_with_val (b ⋅ bs) v ys =
      match b with
      | true => shift v ys
      | false => absent ⋅ (prefix_with_val bs v (Streams.tl ys))
      end.
  Proof.
    intros b bs v ys.
    rewrite unfold_Stream at 1; simpl.
    destruct b; auto.
    destruct (shift v ys); auto.
  Qed.

  Instance prefix_with_val_Proper:
    Proper (@EqSt bool ==> eq ==> @EqSt value ==> @EqSt value)
           prefix_with_val.
  Proof.
    intros bs bs' Heq1 v v' ? vs vs' Heq2; subst.
    revert bs bs' Heq1 vs vs' Heq2.
    cofix CoFix.
    intros [b bs] [b' bs'] Heq1 [x xs] [y ys] Heq2.
    inv Heq1; inv Heq2; simpl in *; subst.
    repeat rewrite prefix_with_val_Cons.
    destruct b'.
    - rewrite H2. reflexivity.
    - constructor; simpl; auto.
  Qed.

  Lemma prefix_with_val_fby : forall b v y,
      synchronized y b ->
      fby (const_val b v) y (prefix_with_val b v y).
  Proof with eauto.
    cofix prefix_with_val_fby.
    intros [b0 b] v y Hsync.
    rewrite const_val_Cons.
    rewrite unfold_Stream; simpl.
    destruct b0; simpl; inv Hsync.
    - econstructor. eapply fby1_shift...
    - econstructor; simpl...
  Qed.

  Definition init_stream H b cl :=
    let b := interp_clock H b cl in
    prefix_with_val b true_val (Str.const b false_const).

  Lemma fby_ite : forall bs v y0s ys zs,
      synchronized y0s bs ->
      synchronized ys bs ->
      synchronized zs bs ->
      fby y0s ys zs ->
      ite (prefix_with_val bs true_val (const_val bs false_val)) y0s (prefix_with_val bs v ys) zs.
  Proof with eauto.
    cofix fby_init_stream_ite.
    intros [b bs] v y0s ys zs Hsync1 Hsync2 Hsync3 Hfby1.
    specialize (prefix_with_val_fby _ v _ Hsync2) as Hfby2.
    specialize (fby_init_stream_ite bs v).
    destruct b; inv Hsync1; inv Hsync2; inv Hsync3.
    - repeat rewrite prefix_with_val_Cons in *. repeat rewrite const_val_Cons in *.
      inv Hfby1.
      repeat rewrite shift_Cons. constructor.
      rewrite shift_const.
      rewrite <- fby1_shift'...
      apply ite_false...
    - repeat rewrite prefix_with_val_Cons in *. constructor; simpl in *.
      rewrite const_val_Cons in Hfby2.
      inv Hfby1. inv Hfby2.
      eapply fby_init_stream_ite...
  Qed.

  Corollary fby_init_stream_ite : forall H bs cl v y0s ys zs,
      let b' := interp_clock H bs cl in
      synchronized y0s b' ->
      synchronized ys b' ->
      synchronized zs b' ->
      fby y0s ys zs ->
      ite (init_stream H bs cl) y0s (prefix_with_val b' v ys) zs.
  Proof.
    intros H b cl v y0 ys zs; simpl. intros Hsync1 Hsync2 Hsync3 Hfby1.
    eapply fby_ite in Hfby1; eauto.
    unfold init_stream.
    rewrite const_val_const. rewrite sem_false_const. eassumption.
  Qed.

  Definition init_eqs_valids l b H (st : fresh_st (Op.type * clock * bool)) :=
    Forall (fun '(id, (_, cl, is_init)) =>
                  is_init = true ->
                  (only_depends_on (l++st_ids st) cl /\ sem_var H id (init_stream H b cl))) (st_anns st).

  Definition hist_st (l : list ident) b H st :=
    Env.dom H (l++st_ids st) /\
    init_eqs_valids l b H st.

  Fact fresh_ident_dom {B V} : forall vars H H' a id (v : V) (st st' : fresh_st B),
      Env.dom H (vars++st_ids st) ->
      fresh_ident a st = (id, st') ->
      H' = Env.add id v H ->
      Env.dom H' (vars++st_ids st').
  Proof.
    intros vars H H' a id v st st' Hdom Hfresh Heq.
    apply Facts.fresh_ident_vars_perm in Hfresh.
    rewrite Heq.
    apply Env.dom_add_cons with (x:=id) (v0:=v) in Hdom.
    eapply Env.dom_Permutation; [| eauto].
    symmetry. rewrite Permutation_middle.
    apply Permutation_app_head. assumption.
  Qed.

  Fact fresh_ident_hist_st : forall vars b a id v H st st',
      st_valid_after st (PSP.of_list vars) ->
      fresh_ident (a, false) st = (id, st') ->
      hist_st vars b H st ->
      hist_st vars b (Env.add id v H) st'.
  Proof with auto.
    intros vars b a id v H st st' Hvalid Hfresh [H1 H2].
    constructor.
    - eapply fresh_ident_dom; eauto.
    - unfold init_eqs_valids in *.
      assert (~In id (st_ids st)) as Hnin by (eapply Facts.fresh_ident_nIn in Hfresh; eauto).
      assert (st_valid_after st' (PSP.of_list vars)) as Hvalid2 by eauto.
      eapply fresh_ident_anns in Hfresh.
      rewrite Hfresh.
      constructor...
      + destruct a. intros. congruence.
      + repeat rewrite_Forall_forall.
        destruct x as [id' [[ty' cl'] is_init]].
        specialize (H2 _ H0). simpl in H2.
        intro His. apply H2 in His as [Hdep His]. clear H2.
        split; [|eapply sem_var_refines].
        * eapply only_depends_on_incl; [|eauto].
          unfold st_ids. rewrite Hfresh; simpl.
          apply incl_appr', incl_tl, incl_refl.
        * apply Env.refines_add...
          intro contra.
          erewrite Env.dom_use in contra; [| eauto].
          eapply in_app_or in contra.
          destruct contra; [|congruence].
          assert (In id (st_ids st')).
          { unfold st_ids, idty. rewrite Hfresh. simpl... }
          apply st_valid_NoDup, NoDup_app_In with (x:=id) in Hvalid2...
          apply Hvalid2. rewrite ps_of_list_ps_to_list...
        * assert (~In id (vars++st_ids st)) as Hnin'.
          { intro contra. apply in_app_or in contra as [contra|contra]; [|auto].
            assert (In id (st_ids st')).
            { unfold st_ids. rewrite Hfresh; simpl; auto. }
            eapply st_valid_NoDup, NoDup_app_In in Hvalid2; [|eauto].
            rewrite ps_of_list_ps_to_list in Hvalid2; auto. }
          unfold init_stream in *.
          rewrite interp_clock_add...
  Qed.
  Hint Resolve fresh_ident_hist_st.

  Fact idents_for_anns_hist_st : forall vars b anns ids vs H st st',
      length vs = length ids ->
      st_valid_after st (PSP.of_list vars) ->
      idents_for_anns anns st = (ids, st') ->
      hist_st vars b H st ->
      hist_st vars b (Env.adds (List.map fst ids) vs H) st'.
  Proof with eauto.
    intros vars b anns ids vs H st st' Hlen Hvalid Hids Hist.
    constructor.
    - destruct Hist.
      eapply idents_for_anns_dom in Hids...
    - revert ids vs H st st' Hlen Hvalid Hids Hist.
      induction anns; intros; repeat inv_bind; simpl.
      + unfold Env.adds; simpl. destruct Hist. assumption.
      + destruct a as [? [? ?]]. repeat inv_bind.
        destruct vs; simpl in Hlen; try congruence.
        unfold Env.adds; simpl.
        assert (st_valid_after x0 (PSP.of_list vars)) by eauto.
        eapply fresh_ident_hist_st in H0...
        eapply IHanns in H1...
  Qed.
  Hint Resolve idents_for_anns_hist_st.

  Fact reuse_ident_dom {B V} : forall vars H H' a id (v : V) (st st' : fresh_st B),
      Env.dom H (vars++st_ids st) ->
      reuse_ident id a st = (tt, st') ->
      H' = Env.add id v H ->
      Env.dom H' (vars++st_ids st').
  Proof.
    intros vars H H' a id v st st' Hdom Hfresh Heq.
    apply Facts.reuse_ident_vars_perm in Hfresh.
    rewrite Heq.
    apply Env.dom_add_cons with (x:=id) (v0:=v) in Hdom.
    eapply Env.dom_Permutation; [| eauto].
    symmetry. rewrite Permutation_middle.
    apply Permutation_app_head. assumption.
  Qed.

  Fact reuse_ident_hist_st : forall vars b a id v H st st' reusable,
      ~PS.In id reusable ->
      st_valid_reuse st (PSP.of_list vars) (PS.add id reusable) ->
      reuse_ident id (a, false) st = (tt, st') ->
      hist_st vars b H st ->
      hist_st vars b (Env.add id v H) st'.
  Proof with auto.
    intros vars b a id v H st st' reusable Hin Hvalid Hfresh [H1 H2].
    constructor.
    - eapply reuse_ident_dom; eauto.
    - unfold init_eqs_valids in *.
      assert (st_valid_reuse st' (PSP.of_list vars) reusable) as Hvalid2 by eauto.
      eapply reuse_ident_anns in Hfresh.
      rewrite Hfresh.
      constructor...
      + destruct a. intros. congruence.
      + repeat rewrite_Forall_forall.
        destruct x as [id0 [[ty cl] is_init]].
        specialize (H2 _ H0). simpl in H2.
        intro His. apply H2 in His as [Hdep His]; clear H2.
        split; [|eapply sem_var_refines].
        * eapply only_depends_on_incl; [|eauto].
          unfold st_ids. rewrite Hfresh; simpl.
          apply incl_appr', incl_tl, incl_refl.
        * apply Env.refines_add...
          intro contra.
          erewrite Env.dom_use in contra; [| eauto].
          assert (In id (st_ids st')) as HIn.
          { unfold st_ids, idty. rewrite Hfresh. simpl... }
          eapply in_app_or in contra.
          destruct contra.
          -- eapply st_valid_reuse_st_valid, st_valid_NoDup, NoDup_app_In in Hvalid2; [|eauto].
             apply Hvalid2. rewrite ps_of_list_ps_to_list...
          -- eapply st_valid_reuse_nIn in Hvalid.
             rewrite PS_For_all_add in Hvalid. destruct Hvalid...
        * assert (~In id (vars++st_ids st)) as Hnin'.
          { intro contra. apply in_app_or in contra as [contra|contra].
            + assert (In id (st_ids st')).
              { unfold st_ids. rewrite Hfresh; simpl; auto. }
              eapply st_valid_reuse_st_valid, st_valid_NoDup, NoDup_app_In in Hvalid2; [|eauto].
              rewrite ps_of_list_ps_to_list in Hvalid2; auto.
            + apply st_valid_reuse_nIn, PS_For_all_add in Hvalid as [? _]... }
          unfold init_stream in *.
          rewrite interp_clock_add...
  Qed.
  Hint Resolve reuse_ident_hist_st.

  Fact idents_for_anns'_hist_st : forall vars b anns ids vs H st st' reusable,
      length vs = length ids ->
      NoDup (map fst (Syn.anon_streams anns) ++ PS.elements reusable) ->
      st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (Syn.anon_streams anns)) reusable) ->
      idents_for_anns' anns st = (ids, st') ->
      hist_st vars b H st ->
      hist_st vars b (Env.adds (List.map fst ids) vs H) st'.
  Proof with eauto.
    intros vars b anns ids vs H st st' reusable Hlen Hndup Hvalid Hids Hist.
    constructor.
    - destruct Hist.
      eapply idents_for_anns'_dom in Hids...
    - revert ids vs H st st' Hlen Hvalid Hids Hist.
      induction anns; intros; repeat inv_bind; simpl.
      + unfold Env.adds; simpl. destruct Hist. assumption.
      + destruct a as [? [? [o|]]]; repeat inv_bind;
          destruct vs; simpl in Hlen; try congruence;
            unfold Env.adds; simpl in *.
        * rewrite <- ps_add_adds_eq in Hvalid. destruct x.
          assert (~ PS.In o (ps_adds (map fst (Syn.anon_streams anns)) reusable)) as Hnin.
          { apply NoDup_cons' in Hndup; destruct Hndup as [Hnin Hndup].
            intro contra; apply Hnin.
            rewrite <- In_PS_elements, Permutation_PS_elements_ps_adds' in contra... }
          assert (st_valid_reuse x0 (PSP.of_list vars) (ps_adds (map fst (Syn.anon_streams anns)) reusable)).
          { eapply reuse_ident_st_valid_reuse in H0... }
          eapply reuse_ident_hist_st in H0...
          eapply IHanns in H1...
          rewrite cons_is_app in Hndup; ndup_r Hndup.
        * assert (st_valid_reuse x0 (PSP.of_list vars) (ps_adds (map fst (Syn.anon_streams anns)) reusable)) by eauto.
          eapply fresh_ident_hist_st in H0...
          eapply IHanns in H1...
  Qed.
  Hint Resolve idents_for_anns'_hist_st.

  (** ** Conservation of sem_exp *)

  Fact map_bind2_sem : forall G vars b is_control es H vs es' eqs' st st' reusable,
      NoDup (map fst (fresh_ins es)++PS.elements reusable) ->
      Forall (wt_exp G vars) es ->
      Forall2 (sem_exp G H b) es vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_ins es)) reusable) ->
      hist_st (map fst vars) b H st ->
      Forall2 (fun e v => forall H es' eqs' st st' reusable,
                   NoDup (map fst (fresh_in e)++PS.elements reusable) ->
                   sem_exp G H b e v ->
                   st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_in e)) reusable) ->
                   hist_st (map fst vars) b H st ->
                   normalize_exp is_control e st = (es', eqs', st') ->
                   (exists H',
                       Env.refines eq H H' /\
                       st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
                       hist_st (map fst vars) b H' st' /\
                       Forall2 (fun e v => sem_exp G H' b e [v]) es' v /\
                       Forall (sem_equation G H' b) eqs')) es vs ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (map fst vars) b H' st' /\
          Forall2 (fun es vs => Forall2 (fun e v => sem_exp G H' b e [v]) es vs) es' vs /\
          Forall (sem_equation G H' b) (concat eqs')).
  Proof with eauto.
    induction es; intros H vs es' eqs' st st' reusable Hndup Hwt Hsem Hvalid Histst Hf Hmap;
      inv Hwt; inv Hsem; inv Hf; repeat inv_bind.
    - exists H; simpl. repeat (split; eauto).
    - unfold fresh_ins in *; simpl in *; rewrite map_app, ps_adds_app in Hvalid.
      assert (NoDup (map fst (fresh_ins es)++PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (fresh_in a) ++ PS.elements (ps_adds (map fst (fresh_ins es)) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
      specialize (H7 _ _ _ _ _ _ Hndup1 H4 Hvalid Histst H0). destruct H7 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      assert (Forall2 (sem_exp G H' b) es l') as Hsem'.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
      specialize (IHes _ _ _ _ _ _ _ Hndup2 H3 Hsem' Hvalid1 Histst1 H9 H1). clear H3 H9 H1.
      destruct IHes as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]].
      exists H''. repeat (split; eauto).
      + etransitivity...
      + constructor; eauto. subst.
        assert (length x = numstreams a) as Hlength1 by (eapply normalize_exp_length; eauto).
        assert (length y = numstreams a) as Hlength2 by (eapply sem_exp_numstreams; eauto).
        specialize (normalize_exp_sem_length _ _ _ _ _ _ _ _ H2 H0) as Hnormlength.
        repeat rewrite_Forall_forall.
        eapply sem_exp_refines; eauto.
      + apply Forall_app. split...
        solve_forall. eapply sem_equation_refines...
  Qed.

  Fact normalize_reset_sem : forall G vars b e H v e' eqs' st st' reusable,
      sem_exp G H b e [v] ->
      st_valid_reuse st (PSP.of_list vars) reusable ->
      hist_st vars b H st ->
      Env.dom H (vars++st_ids st) ->
      normalize_reset e st = (e', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list vars) reusable /\
          hist_st vars b H' st' /\
          sem_exp G H' b e' [v] /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros G vars b e H v e' eqs' st st' reusable Hsem Hvalid Histst Hdom Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind.
    - exists H. repeat (split; auto).
    - destruct (List.hd _ _) as [? [? ?]] eqn:Heqann; repeat inv_bind.
      assert (st_follows st st') as Hfollows by eauto.
      assert (st_valid_after st (PSP.of_list vars)) as Hvalid' by eauto.
      remember (Env.add x v H) as H'.
      assert (hist_st vars b H' st') by (subst; eauto).
      assert (Env.refines eq H H') as Href by (eapply fresh_ident_refines with (st0:=st); eauto).
      exists H'. repeat (split; eauto).
      + constructor.
        econstructor; [| reflexivity].
        rewrite HeqH'. apply Env.add_1. reflexivity.
      + repeat constructor.
        apply Seq with (ss:=[[v]]).
        * repeat constructor.
          eapply sem_exp_refines...
        * simpl. repeat constructor.
          econstructor; [| reflexivity].
          rewrite HeqH'. apply Env.add_1. reflexivity.
  Qed.

  Fact wt_clock_only_depends_on : forall vars ck,
      wt_clock vars ck ->
      only_depends_on (map fst vars) ck.
  Proof.
    intros * Hwc.
    induction Hwc; intros id Hisin; inv Hisin.
    - simpl_In. exists (x, bool_type); auto.
    - apply IHHwc; auto.
  Qed.

  Fact fby_iteexp_sem : forall G vars b H e0 e ty cl y0 y z e' eqs' st st' reusable,
      wt_nclock vars cl ->
      sem_exp G H b e0 [y0] ->
      sem_exp G H b e [y] ->
      fby y0 y z ->
      st_valid_reuse st (PSP.of_list (map fst vars)) reusable ->
      hist_st (map fst vars) b H st ->
      fby_iteexp e0 e (ty, cl) st = (e', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (map fst vars) b H' st' /\
          sem_exp G H' b e' [z] /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros * Hwt Hsem0 Hsem Hfby Hvalid Histst Hiteexp.
    unfold fby_iteexp in Hiteexp. inv Hwt; rename H0 into Hwt.
    destruct (Norm.is_constant e0); repeat inv_bind.
    - exists H. repeat (split; eauto).
      econstructor.
      + constructor; eauto.
      + constructor; eauto.
      + repeat constructor. assumption.
    - unfold init_var_for_clock in H0.
      destruct (find _ _) eqn:Hfind.
      + destruct p; inv H0.
        remember (interp_clock H b ck) as b'.
        remember (prefix_with_val b' (Op.sem_const (Op.init_type ty)) y) as y'.
        remember (Env.add x2 y' H) as H'.
        assert (Env.refines eq H H') by (destruct Histst; eapply fresh_ident_refines in H1; eauto).
        exists H'. repeat (split; eauto).
        * destruct Histst. eapply fresh_ident_dom in H1...
        * eapply fresh_ident_hist_st in H1...
          rewrite <- HeqH' in H1.
          destruct H1...
        * (* We can get data about x back from our hist_st hypothesis *)
          assert (sem_var H x (init_stream H b ck)).
          { destruct Histst as [_ Hvalids]. unfold init_eqs_valids in Hvalids.
            rewrite Forall_forall in Hvalids.
            eapply find_some in Hfind. destruct p as [[ty' cl'] isinit].
            repeat rewrite Bool.andb_true_iff in Hfind. destruct Hfind as [Hin [[Hisinit Hcl] Hty]].
            rewrite OpAux.type_eqb_eq in Hty.
            rewrite Clocks.clock_eqb_eq in Hcl. subst.
            eapply Hvalids in Hin. apply Hin... }
          econstructor...
          -- constructor. eapply sem_var_refines...
          -- repeat econstructor...
             eapply sem_exp_refines...
          -- repeat constructor...
             rewrite HeqH'.
             econstructor; [| reflexivity].
             apply Env.add_1. reflexivity.
          -- simpl. repeat constructor.
             rewrite Heqy'.
             specialize (fby_init_stream_ite H b ck (sem_const (init_type ty)) y0 y z) as Hinit.
             simpl in Hinit. rewrite Heqb'. apply Hinit...
             1,2,3:admit.
        * repeat constructor.
          eapply Seq with (ss:=[[y']]); simpl.
          -- repeat constructor.
             eapply Sfby with (s0ss:=[[const b' (init_type ty)]]).
             2:(repeat constructor; eapply sem_exp_refines; eauto).
             ++ repeat constructor.
                admit. (* alignment ? *)
             ++ repeat constructor.
                rewrite Heqy'.
                rewrite const_val_const.
                eapply prefix_with_val_fby.
                admit. (* alignment ? *)
          -- repeat constructor.
             rewrite HeqH'.
             econstructor; [| reflexivity].
             apply Env.add_1. reflexivity.
      + clear Hfind.
        destruct (fresh_ident _ _) eqn:Hident. repeat inv_bind.
        assert (st_valid_reuse x1 (PSP.of_list (map fst vars)) reusable) as Hvalid1 by eauto.
        remember (Env.add x (init_stream H b ck) H) as H'.
        assert (Env.refines eq H H') as Href1 by (destruct Histst; eapply fresh_ident_refines in Hident; eauto).
        assert (hist_st (map fst vars) b H' x1) as Histst1.
        { destruct Histst.
          constructor.
          + eapply fresh_ident_dom in Hident...
          + assert (only_depends_on (map fst vars) ck) as Hdep by (apply wt_clock_only_depends_on in Hwt; auto).
            assert (~In x (st_ids st)) as Hnin1 by (eapply Facts.fresh_ident_nIn in Hident; eauto).
            assert (~In x (map fst vars)) as Hnin2.
            { apply Facts.fresh_ident_In in Hident.
              eapply st_valid_reuse_st_valid, st_valid_NoDup, NoDup_app_In with (x0:=x) in Hvalid1.
              rewrite ps_of_list_ps_to_list in Hvalid1...
              unfold st_ids. repeat simpl_In. exists (x, (bool_type, ck, true))... }
            assert (~Env.In x H) as Hnin3.
            { eapply Env.dom_use in H0; rewrite H0.
              intro contra. apply in_app_or in contra as [?|?]; auto. }
            unfold init_eqs_valids in *.
            erewrite fresh_ident_anns...
            constructor; [intros _; split|].
            * eapply only_depends_on_incl; [|eauto].
              apply incl_appl, incl_refl.
            * rewrite HeqH'. econstructor. eapply Env.add_1; reflexivity.
              unfold init_stream.
              rewrite interp_clock_add... reflexivity.
            * eapply Forall_impl_In; [|eauto].
              intros [? [[? ?] ?]] Hin H3 Heq; subst.
              specialize (H3 eq_refl) as [Hdep' Hsem']; split.
              -- eapply only_depends_on_incl; [|eauto].
                 unfold st_ids.
                 apply incl_appr', incl_map, st_follows_incl. repeat solve_st_follows.
              -- eapply sem_var_refines. eapply Env.refines_add; auto.
                 unfold init_stream. rewrite interp_clock_add; auto.
                 intro contra. apply Hdep', in_app_or in contra as [?|?]; auto.
        }
        assert (st_valid_reuse st' (PSP.of_list (map fst vars)) reusable) as Hvalid2 by eauto.
        remember (interp_clock H b ck) as b'.
        remember (prefix_with_val b' (Op.sem_const (Op.init_type ty)) y) as y'.
        remember (Env.add x2 y' H') as H''.
        assert (Env.refines eq H' H'') as Href2 by (destruct Histst1; eapply fresh_ident_refines in H1; eauto).
        assert (hist_st (map fst vars) b H'' st') as Histst2 by (rewrite HeqH''; eauto).
        assert (~Env.E.eq x2 x) as Hneq.
        { intro contra. eapply Facts.fresh_ident_In in Hident.
          assert (In x (st_ids x1)).
          { unfold st_ids, idty. rewrite in_map_iff. exists (x, (Op.bool_type, ck, true)); eauto. }
          eapply Facts.fresh_ident_nIn in H1. 2:eauto.
          rewrite contra in H1. congruence. }
        exists H''. repeat (split; eauto)...
        * etransitivity...
        * eapply Site with (s:=(init_stream H b ck)) (ts:=[[y0]]) (fs:=[[y']]).
          -- constructor. econstructor; [| reflexivity].
             rewrite HeqH''. rewrite HeqH'.
             eapply Env.add_2... eapply Env.add_1. reflexivity.
          -- repeat constructor.
             eapply sem_exp_refines; [| eauto]. etransitivity...
          -- repeat constructor. econstructor; [| reflexivity].
             rewrite HeqH''. eapply Env.add_1. reflexivity.
          -- simpl. repeat constructor.
             subst. eapply fby_init_stream_ite...
             1,2,3:admit.
        * repeat constructor.
          -- apply Seq with (ss:=[[y']]); simpl.
             ++ repeat constructor. admit.
             ++ repeat constructor. econstructor; [| reflexivity].
                rewrite HeqH''. apply Env.add_1; reflexivity.
          -- apply Seq with (ss:=[[init_stream H b ck]]); simpl.
             ++ repeat constructor. admit.
             ++ repeat constructor. econstructor; [| reflexivity].
                rewrite HeqH''. rewrite HeqH'.
                eapply Env.add_2... eapply Env.add_1. reflexivity.
  Admitted.

  Fact normalize_fby_sem : forall G vars b anns H e0s es s0s ss vs es' eqs' st st' reusable,
      Forall (wt_nclock vars) (map snd anns) ->
      length e0s = length anns ->
      length es = length anns ->
      Forall2 (fun e v => sem_exp G H b e [v]) e0s s0s ->
      Forall2 (fun e v => sem_exp G H b e [v]) es ss ->
      Forall3 fby s0s ss vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) reusable ->
      hist_st (map fst vars) b H st ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (map fst vars) b H' st' /\
          Forall2 (fun e v => sem_exp G H' b e [v]) es' vs /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction anns; intros * Hwt Hlen1 Hlen2 Hsem1 Hsem2 Hfby Hvalid Histst Hnorm;
      unfold normalize_fby in Hnorm; repeat inv_bind.
    - destruct e0s; simpl in *; try congruence.
      destruct es; simpl in *; try congruence.
      repeat inv_bind. inv Hsem1. inv Hsem2. inv Hfby.
      exists H. repeat (split; eauto); simpl...
    - destruct e0s; simpl in *; try congruence.
      destruct es; simpl in *; try congruence.
      repeat inv_bind.
      inv Hwt. inv Hlen1. inv Hlen2. inv Hsem1. inv Hsem2. inv Hfby.
      destruct a as [ty ck].
      eapply fby_iteexp_sem in H0... destruct H0 as [H' [Hvalid1 [Href1 [Hdom1 [Hsem1 Hsem1']]]]].
      assert (Forall2 (fun (e1 : exp) (v : Stream OpAux.value) => sem_exp G H' b e1 [v]) e0s l').
      { repeat rewrite_Forall_forall; solve_length. eapply sem_exp_refines... } clear H8.
      assert (Forall2 (fun (e1 : exp) (v : Stream OpAux.value) => sem_exp G H' b e1 [v]) es l'0).
      { repeat rewrite_Forall_forall; solve_length. eapply sem_exp_refines... } clear H10.
      assert (normalize_fby e0s es anns x2 = (x3, (concat x4), st')) as Hnorm.
      { unfold normalize_fby. repeat inv_bind.
        repeat eexists; try inv_bind; eauto. }
      eapply IHanns in Hnorm... clear IHanns.
      destruct Hnorm as [H'' [Hvalid2 [Href2 [Hdom2 [Hsem2 Hsem2']]]]].
      eexists H''. repeat (split; eauto).
      + etransitivity...
      + constructor...
        eapply sem_exp_refines...
      + simpl. eapply Forall_app; split...
        solve_forall. eapply sem_equation_refines...
  Qed.

  Fact In_fresh_in_NoDup : forall e es vars,
      In e es ->
      NoDup (map fst (fresh_ins es) ++ vars) ->
      NoDup (map fst (fresh_in e) ++ vars).
  Proof.
    induction es; intros vars Hin Hndup; inv Hin;
      unfold fresh_ins in Hndup; simpl in Hndup; rewrite map_app, <- app_assoc in Hndup.
    - ndup_l Hndup.
    - ndup_r Hndup.
  Qed.
  Hint Resolve In_fresh_in_NoDup.

  Hint Constructors sem_exp.
  Fact normalize_exp_sem : forall G vars b e H vs is_control es' eqs' st st' reusable,
      NoDup (map fst (fresh_in e) ++ PS.elements reusable) ->
      wt_exp G vars e ->
      sem_exp G H b e vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_in e)) reusable) ->
      hist_st (map fst vars) b H st ->
      normalize_exp is_control e st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (map fst vars) b H' st' /\
          Forall2 (fun e v => sem_exp G H' b e [v]) es' vs /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction e using exp_ind2; intros Hi vs is_control es' eqs' st st' reusable Hndup Hwt Hsem Hvalid Histst Hnorm;
      inv Hwt; inv Hsem; repeat inv_bind.
    - (* const *)
      exists Hi. repeat (split; eauto).
    - (* var *)
      exists Hi. repeat (split; eauto).
    - (* unop *)
      specialize (Typ.normalize_exp_typeof _ _ _ _ _ _ _ _ H2 H) as Htypeof.
      specialize (IHe _ _ _ _ _ _ _ _ Hndup H2 H9 Hvalid Histst H). destruct IHe as [Hi' [Hvalid1 [Href1 [Hdom1 [Hsem1 Hsem1']]]]].
      assert (numstreams e = 1) by (rewrite <- length_typeof_numstreams; rewrite H3; reflexivity).
      eapply normalize_exp_length in H... rewrite H0 in H.
      repeat singleton_length. inv Hsem1. clear H10.
      exists Hi'.
      repeat (split; eauto).
      repeat econstructor... congruence.
    - (* binop *)
      simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      specialize (Typ.normalize_exp_typeof _ _ _ _ _ _ _ _ H3 H) as Htypeof1.
      specialize (Typ.normalize_exp_typeof _ _ _ _ _ _ _ _ H4 H0) as Htypeof2.
      assert (numstreams e1 = 1) by (rewrite <- length_typeof_numstreams; rewrite H15; reflexivity).
      assert (numstreams e2 = 1) by (rewrite <- length_typeof_numstreams; rewrite H16; reflexivity).
      assert (NoDup (map fst (fresh_in e1) ++ PS.elements (ps_adds (map fst (fresh_in e2)) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'. ndup_simpl... ndup_r Hndup. }
      specialize (IHe1 _ _ _ _ _ _ _ _ Hndup1 H3 H10 Hvalid Histst H).
      destruct IHe1 as [Hi' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      eapply sem_exp_refines in H13; [| eauto].
      assert (NoDup (map fst (fresh_in e2) ++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      specialize (IHe2 _ _ _ _ _ _ _ _ Hndup2 H4 H13 Hvalid1 Histst1 H0).
      destruct IHe2 as [Hi'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]].
      eapply normalize_exp_length in H... rewrite H1 in H.
      eapply normalize_exp_length in H0... rewrite H2 in H0.
      repeat singleton_length; subst.
      inv Hsem1. inv Hsem2. clear H14 H19.
      rewrite H5 in H15; inv H15. rewrite H6 in H16; inv H16.
      exists Hi''.
      repeat (split; eauto).
      + etransitivity...
      + repeat econstructor...
        * eapply sem_exp_refines...
        * congruence.
        * congruence.
      + apply Forall_app. split; solve_forall...
        eapply sem_equation_refines...
    - (* fby *)
      simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      assert (length (concat x2) = length (annots e0s)) as Hlength1 by (eapply map_bind2_normalize_exp_length; eauto).
      assert (length (concat x9) = length (annots es)) as Hlength2 by (eapply map_bind2_normalize_exp_length; eauto).
      assert (NoDup (map fst (fresh_ins es) ++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (fresh_ins e0s) ++ PS.elements (ps_adds (map fst (concat (map fresh_in es))) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
      eapply map_bind2_sem in H1... 2:repeat rewrite_Forall_forall; eapply nth_In in H17... clear H.
      destruct H1 as [H' [Href1 [Histst1 [Hdom1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.
      assert (Forall2 (sem_exp G H' b) es sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
      eapply map_bind2_sem in H2... 2:repeat rewrite_Forall_forall; eapply nth_In in H19... clear H0.
      destruct H2 as [H'' [Hvalid2 [Href2 [Hdom2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
      assert (Forall2 (fun (e : exp) (v : Stream OpAux.value) => sem_exp G H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
      specialize (idents_for_anns_length _ _ _ _ H9) as Hlength.
      assert (length vs = length a) as Hlength'.
      { repeat rewrite_Forall_forall. repeat simpl_length.
        rewrite <- H13. erewrite <- map_length. rewrite H7. solve_length. }
      eapply normalize_fby_sem in H3; solve_length...
      2,3: (erewrite <- map_length; try rewrite H6; try rewrite H7; solve_length).
      destruct H3 as [H''' [Href3 [Hvalid3 [Hdom3 [Hsem3 Hsem3']]]]].
      remember (Env.adds (List.map fst x8) vs H''') as H''''.
      assert (Env.refines eq H''' H'''') as Href4.
      { destruct Hdom3. eapply idents_for_anns_refines... solve_length. }
      assert (hist_st (map fst vars) b H'''' st') as Histst4.
      { rewrite HeqH''''. eapply idents_for_anns_hist_st in H9... solve_length. }
      exists H''''. repeat (split; eauto)...
      * repeat (etransitivity; eauto).
      * rewrite Forall2_map_1.
        repeat rewrite_Forall_forall; solve_length.
        destruct (nth _ x8 _) eqn:Hnth.
        repeat constructor. econstructor; [| reflexivity].
        destruct a0. rewrite split_nth in Hnth; inv Hnth.
        rewrite split_map_fst.
        apply Env.adds_MapsTo; solve_length.
        rewrite <- fst_NoDupMembers.
        eapply idents_for_anns_NoDupMembers in H9...
      * repeat rewrite Forall_app. repeat split.
        -- rewrite Forall_map.
           eapply Forall2_combine'.
           repeat rewrite_Forall_forall; solve_length.
           destruct (nth _ x8 _) eqn:Hnth1.
           econstructor.
           ++ repeat constructor.
              specialize (H0 b0 default_stream _ _ _ H22 eq_refl eq_refl).
              eapply sem_exp_refines...
           ++ simpl. repeat constructor.
              econstructor.
              destruct a0. rewrite split_nth in Hnth1; inv Hnth1.
              rewrite split_map_fst.
              apply Env.adds_MapsTo; solve_length. 2:reflexivity.
              rewrite <- fst_NoDupMembers.
              eapply idents_for_anns_NoDupMembers in H9...
        -- solve_forall. repeat (eapply sem_equation_refines; eauto).
        -- solve_forall. repeat (eapply sem_equation_refines; eauto).
        -- solve_forall. eapply sem_equation_refines...
    - (* when *)
      assert (length (concat x1) = length (annots es)) as Hlength by (eapply map_bind2_normalize_exp_length; eauto).
      erewrite <- (map_length _ (annots es)) in Hlength. erewrite <- typesof_annots in Hlength.
      eapply map_bind2_sem in H0... 2:repeat rewrite_Forall_forall; eapply nth_In in H8... clear H.
      destruct H0 as [H' [Hvalid1 [Href1 [Hdom1 [Hsem1 Hsem1']]]]].
      apply Forall2_concat in Hsem1.
      exists H'. repeat (split; simpl; eauto).
      rewrite Forall2_map_1.
      eapply Forall2_trans_ex in H13; [| eauto].
      apply Forall2_combine_lr with (zs:=(typesof es)) in H13; auto.
      eapply Forall2_impl_In; [| eauto].
      intros; simpl in H1. destruct a. destruct H1 as [y [Hin [Hsem Hsem']]].
      econstructor...
      + eapply sem_var_refines...
      + simpl. repeat constructor...
    - (* merge *)
      simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      assert (length (concat ts) = length (annots ets)) as Hlength1 by (eapply sem_exps_numstreams; eauto).
      assert (NoDup (map fst (fresh_ins efs) ++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (fresh_ins ets) ++ PS.elements (ps_adds (map fst (concat (map fresh_in efs))) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
      eapply map_bind2_sem in H1... 2:repeat rewrite_Forall_forall; eapply nth_In in H17... clear H.
      destruct H1 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.
      assert (Forall2 (sem_exp G H' b) efs fs) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
      eapply map_bind2_sem in H2... 2:(repeat rewrite_Forall_forall; eapply nth_In in H19; eauto). clear H0.
      destruct H2 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
      destruct is_control; repeat inv_bind.
      + (* control *)
        exists H''. repeat (split; simpl; eauto).
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
        { destruct Histst2. eapply idents_for_anns_refines...
          repeat rewrite_Forall_forall; solve_length. }
        assert (hist_st (map fst vars) b H''' st') as Histst3.
        { rewrite HeqH'''. eapply idents_for_anns_hist_st in H...
          repeat rewrite_Forall_forall. solve_length. }
        exists H'''. repeat (split; eauto).
        * repeat (etransitivity; eauto).
        * rewrite Forall2_map_1.
          repeat rewrite_Forall_forall; solve_length.
          destruct (nth _ x0 _) eqn:Hnth.
          repeat constructor. econstructor; [| reflexivity].
          destruct a. rewrite split_nth in Hnth; inv Hnth.
          rewrite split_map_fst.
          apply Env.adds_MapsTo; solve_length.
          rewrite <- fst_NoDupMembers.
          eapply idents_for_anns_NoDupMembers in H...
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
                eapply idents_for_anns_NoDupMembers in H...
          -- solve_forall. repeat (eapply sem_equation_refines; eauto).
          -- solve_forall. eapply sem_equation_refines...
             Unshelve. exact default_ann. exact s.
    - (* ite *)
      simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
      assert (length [s] = numstreams e) as Hlength1 by (eapply sem_exp_numstreams; eauto). simpl in Hlength1.
      assert (length x = numstreams e) as Hlength1' by (eapply normalize_exp_length; eauto).
      rewrite <- Hlength1 in Hlength1'. clear Hlength1.
      assert (length (concat ts) = length (annots ets)) as Hlength3 by (eapply sem_exps_numstreams; eauto).
      assert (NoDup (map fst (fresh_ins efs) ++ PS.elements reusable)) as Hndup3 by repeat ndup_r Hndup.
      assert (NoDup (map fst (fresh_ins ets) ++ PS.elements (ps_adds (map fst (fresh_ins efs)) reusable))) as Hndup2.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }
      assert (NoDup
                (map fst (fresh_in e) ++
                     PS.elements (ps_adds (map fst (fresh_ins ets)) (ps_adds (map fst (fresh_ins efs)) reusable)))) as Hndup1.
      { repeat rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }
      eapply IHe in H1... clear IHe. destruct H1 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      assert (Forall2 (sem_exp G H' b) ets ts) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
      eapply map_bind2_sem in H2... 2:repeat rewrite_Forall_forall; eapply nth_In in H22... clear H.
      destruct H2 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
      assert (Forall2 (sem_exp G H'' b) efs fs) as Hsem'' by (repeat rewrite_Forall_forall; repeat (eapply sem_exp_refines; eauto)).
      eapply map_bind2_sem in H3... 2:repeat rewrite_Forall_forall; eapply nth_In in H24... clear H0.
      destruct H3 as [H''' [Href3 [Hvalid3 [Histst3 [Hsem3 Hsem3']]]]]. apply Forall2_concat in Hsem3.
      destruct is_control; repeat inv_bind.
      + (* control *)
        exists H'''. repeat (split; simpl; eauto).
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
        { destruct Histst3. eapply idents_for_anns_refines...
          repeat rewrite_Forall_forall; solve_length. }
        assert (hist_st (map fst vars) b H'''' st').
        { rewrite HeqH''''. eapply idents_for_anns_hist_st in H...
          repeat rewrite_Forall_forall. solve_length. }
        exists H''''. repeat (split; eauto)...
        * repeat (etransitivity; eauto).
        * rewrite Forall2_map_1.
          repeat rewrite_Forall_forall; solve_length.
          destruct (nth _ x2 _) eqn:Hnth.
          repeat constructor. econstructor; [| reflexivity].
          destruct a. rewrite split_nth in Hnth; inv Hnth.
          rewrite split_map_fst.
          apply Env.adds_MapsTo; solve_length.
          rewrite <- fst_NoDupMembers.
          eapply idents_for_anns_NoDupMembers in H...
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
                ** repeat constructor.
                   specialize (H12 e2 s _ _ _ H25 eq_refl eq_refl).
                   eapply sem_exp_refines; [| eauto]. etransitivity...
                ** repeat constructor.
                   specialize (H12 e2 s _ _ _ H25 eq_refl eq_refl).
                   eapply sem_exp_refines; [| eauto]. etransitivity...
                ** repeat econstructor. eauto.
             ++ simpl. repeat constructor.
                econstructor.
                destruct a. rewrite split_nth in Hnth1; inv Hnth1.
                rewrite split_map_fst.
                apply Env.adds_MapsTo; solve_length. 2:reflexivity.
                rewrite <- fst_NoDupMembers.
                eapply idents_for_anns_NoDupMembers in H...
          -- solve_forall. repeat (eapply sem_equation_refines; eauto).
          -- solve_forall. eapply sem_equation_refines with (H:=H'')... etransitivity...
          -- solve_forall. eapply sem_equation_refines...
             Unshelve. exact default_ann. exact (hd_default []). 1,2:exact s.
    - (* app *)
      simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
      specialize (idents_for_anns'_length _ _ _ _ H2) as Hlength1.
      assert (length (n_out n) = length vs) as Hlength2.
      { destruct H14. repeat rewrite_Forall_forall.
        rewrite H4 in H6. inv H6. unfold idents in *. solve_length. }
      assert (NoDup (map fst (Syn.anon_streams a)++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (fresh_ins es) ++ PS.elements (ps_adds (map fst (Syn.anon_streams a)) reusable))).
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
      eapply map_bind2_sem in H1... 2:repeat rewrite_Forall_forall; eapply nth_In in H13... clear H0.
      destruct H1 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      remember (Env.adds (map fst x1) vs H') as H''.
      assert (Env.refines eq H' H'') as Href2.
      { destruct Histst1.
        eapply idents_for_anns'_refines... repeat rewrite_Forall_forall; solve_length. }
      assert (hist_st (map fst vars) b H'' st').
      { rewrite HeqH''. eapply idents_for_anns'_hist_st in H2...
        repeat rewrite_Forall_forall. solve_length. }
      exists H''. repeat (split; eauto).
      + etransitivity...
      + rewrite Forall2_map_1.
        repeat rewrite_Forall_forall; solve_length.
        destruct (nth n0 x1 a0) eqn:Hnth. setoid_rewrite Hnth.
        repeat constructor. econstructor; [|reflexivity].
        destruct a0. rewrite split_nth in Hnth; inv Hnth.
        rewrite split_map_fst.
        apply Env.adds_MapsTo; solve_length.
        rewrite <- fst_NoDupMembers.
        eapply idents_for_anns'_NoDupMembers in H2...
      + constructor.
        * apply Seq with (ss:=[vs]).
          -- repeat constructor.
             apply Sapp with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))).
             ++ apply Forall2_concat.
                repeat rewrite_Forall_forall; solve_length;
                  specialize (H4 a0 (List.map (fun _ => default_stream) b0) _ _ _ H15 eq_refl eq_refl);
                  repeat rewrite_Forall_forall; simpl_length.
                ** rewrite <- map_nth.
                   rewrite <- (map_nth (length (A:=_)) (List.map _ ss)). f_equal; solve_length.
                   repeat rewrite map_map.
                   apply map_ext_in. intros; solve_length.
                ** specialize (H17 a1 default_stream _ _ _ H16 eq_refl eq_refl).
                   repeat simpl_nth; [| eassumption].
                   eapply sem_exp_refines...
             ++ rewrite concat_map_singl2. assumption.
          -- simpl. rewrite app_nil_r.
             repeat rewrite_Forall_forall; solve_length.
             repeat constructor. econstructor; [| reflexivity].
             apply Env.adds_MapsTo; solve_length.
             rewrite <- fst_NoDupMembers.
             eapply idents_for_anns'_NoDupMembers in H2...
        * rewrite app_nil_r; solve_forall.
          eapply sem_equation_refines...
    - (* app (reset) *)
      simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
      specialize (idents_for_anns'_length _ _ _ _ H3) as Hlength1.
      assert (length (n_out n) = length vs) as Hlength3.
      { clear H H0 H1 H4. specialize (H19 0); inv H19; subst.
        repeat rewrite_Forall_forall.
        rewrite H0 in H6; inv H6. unfold idents in *. solve_length. }
      assert (NoDup (map fst (Syn.anon_streams a) ++ PS.elements reusable)) as Hndup3 by repeat ndup_r Hndup.
      assert (NoDup (map fst (fresh_in r) ++ PS.elements (ps_adds (map fst (Syn.anon_streams a)) reusable))) as Hndup2.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }
      assert (NoDup (map fst (fresh_ins es) ++
                         PS.elements (ps_adds (map fst (fresh_in r)) (ps_adds (map fst (Syn.anon_streams a)) reusable)))) as Hndup1.
      { repeat rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }
      eapply map_bind2_sem in H1... 2:repeat rewrite_Forall_forall; eapply nth_In in H16... clear H0.
      destruct H1 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      assert (length x6 = 1) as Hlength2.
      { eapply normalize_exp_length in H2... rewrite <- length_typeof_numstreams in H2.
        rewrite H2, H11. reflexivity. }
      singleton_length.
      assert (sem_exp G H' b r [rs]) as Hsem' by (eapply sem_exp_refines; eauto). clear H17.
      eapply H in H2... clear H.
      destruct H2 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. inv Hsem2; inv H13.
      eapply normalize_reset_sem in H4... 2:(destruct Histst2; eauto).
      destruct H4 as [H''' [Href3 [Hvalid3 [Histst3 [Hsem3 Hsem3']]]]].
      remember (Env.adds (List.map fst x5) vs H''') as H''''.
      assert (Env.refines eq H''' H'''') as Href4.
      { destruct Histst3. eapply idents_for_anns'_refines...
        repeat rewrite_Forall_forall; solve_length. }
      assert (st_valid_reuse st' (PSP.of_list (map fst vars)) reusable) as Hvalid4 by eauto.
      assert (hist_st (map fst vars) b H'''' st').
      { rewrite HeqH''''. eapply idents_for_anns'_hist_st in H3...
        repeat rewrite_Forall_forall; solve_length. }
      exists H''''. repeat (split; auto).
      + repeat (etransitivity; eauto).
      + rewrite Forall2_map_1.
        repeat rewrite_Forall_forall; solve_length.
        destruct (nth n0 x5 a0) eqn:Hnth; setoid_rewrite Hnth.
        repeat constructor. econstructor; [|reflexivity].
        destruct a0. rewrite split_nth in Hnth; inv Hnth.
        rewrite split_map_fst.
        apply Env.adds_MapsTo; solve_length.
        rewrite <- fst_NoDupMembers.
        eapply idents_for_anns'_NoDupMembers in H3...
      + constructor.
        * apply Seq with (ss:=[vs]).
          -- repeat constructor.
             apply Sreset with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))) (rs:=rs) (bs:=bs)...
             ++ apply Forall2_concat.
                repeat rewrite_Forall_forall; solve_length;
                  specialize (H1 a0 (List.map (fun _ => default_stream) b0) _ _ _ H15 eq_refl eq_refl);
                  repeat rewrite_Forall_forall; simpl_length.
                ** rewrite <- map_nth.
                   rewrite <- (map_nth (length (A:=_)) (List.map _ ss)). f_equal; solve_length.
                   repeat rewrite map_map.
                   apply map_ext_in. intros; solve_length.
                ** specialize (H17 a1 default_stream _ _ _ H16 eq_refl eq_refl).
                   repeat simpl_nth; [| eassumption].
                   eapply sem_exp_refines; [| eauto].
                   repeat (etransitivity; eauto).
             ++ eapply sem_exp_refines; [| eauto]. etransitivity...
             ++ rewrite concat_map_singl2. assumption.
          -- simpl. rewrite app_nil_r.
             repeat rewrite_Forall_forall; solve_length.
             repeat constructor. econstructor; [| reflexivity].
             apply Env.adds_MapsTo; solve_length.
             rewrite <- fst_NoDupMembers.
             eapply idents_for_anns'_NoDupMembers in H3...
        * repeat rewrite Forall_app.
          repeat split; solve_forall; solve_length.
          1,2,3: (eapply sem_equation_refines; [| eauto]; repeat (etransitivity; eauto)).
  Qed.

  Corollary normalize_exps_sem : forall G vars b es H vs es' eqs' st st' reusable,
      NoDup (map fst (fresh_ins es) ++ PS.elements reusable) ->
      Forall (wt_exp G vars) es ->
      Forall2 (sem_exp G H b) es vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_ins es)) reusable) ->
      hist_st (map fst vars) b H st ->
      map_bind2 (normalize_exp false) es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (map fst vars) b H' st' /\
          Forall2
            (fun (es : list exp) (vs : list (Stream OpAux.value)) =>
             Forall2 (fun e v => sem_exp G H' b e [v]) es vs) es' vs /\
          Forall (sem_equation G H' b) (concat eqs')).
  Proof.
    intros G vars b es H vs es' eqs' st st' reusable Hndup Hwt Hsem Hvalid Hdom Hnorm.
    eapply map_bind2_sem in Hnorm; eauto.
    repeat rewrite_Forall_forall.
    specialize (nth_In _ a H2) as Hin.
    eapply normalize_exp_sem with (e:=(nth n es a)); eauto.
  Qed.

  Fact normalize_rhs_sem : forall G vars b keep_fby e H vs es' eqs' st st' reusable,
      NoDup (map fst (anon_in e) ++ PS.elements reusable) ->
      wt_exp G vars e ->
      sem_exp G H b e vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in e)) reusable) ->
      hist_st (map fst vars) b H st ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (map fst vars) b H' st' /\
          (Forall2 (fun e v => sem_exp G H' b e [v]) es' vs \/
           exists e', (es' = [e'] /\ sem_exp G H' b e' vs)) /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros * Hndup Hwt Hsem Hvalid Hhistst Hnorm.
    destruct e; try eapply normalize_exp_sem in Hnorm; eauto.
    1,2,3,4,6,7,8: (destruct Hnorm as [H' [Href1 [Hvalid1 [Hhistst1 [Hsem1 Hsem2]]]]];
                    exists H'; repeat (split; eauto)).
      1,2:(unfold normalize_rhs in Hnorm). destruct keep_fby. 1,2,3:(inv Hwt; inv Hsem).
    - (* fby (keep) *)
      simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
      repeat inv_bind.
      assert (length x = length (annots l)) as Hlength1 by (eapply normalize_exps_length; eauto).
      assert (length x2 = length (annots l0)) as Hlength2 by (eapply normalize_exps_length; eauto).
      unfold normalize_exps in *. repeat inv_bind.
      assert (NoDup (map fst (fresh_ins l0) ++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (fresh_ins l) ++ PS.elements (ps_adds (map fst (fresh_ins l0)) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
      eapply normalize_exps_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.
      assert (Forall2 (sem_exp G H' b) l0 sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
      eapply normalize_exps_sem in H1...
      destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
      assert (Forall2 (fun (e : exp) (v : Stream OpAux.value) => sem_exp G H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
      eapply normalize_fby_sem in H2; solve_length...
      2,3: (erewrite <- map_length; try rewrite H5; try rewrite H6; solve_length).
      destruct H2 as [H''' [Href3 [Hvalid3 [Histst3 [Hsem3 Hsem3']]]]].
      exists H'''. repeat (split; auto).
      + repeat (etransitivity; eauto).
      + repeat rewrite Forall_app. repeat split...
        * solve_forall. eapply sem_equation_refines; [| eauto]. etransitivity...
        * solve_forall. eapply sem_equation_refines...
    - (* fby (don't keep) *)
      eapply normalize_exp_sem in Hnorm...
      destruct Hnorm as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem2]]]]].
      exists H'. repeat (split; eauto).
    - (* app *)
      repeat inv_bind. unfold normalize_exps in H0; repeat inv_bind.
      eapply normalize_exps_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      exists H'. repeat (split; auto).
      right. eexists; split...
      apply Sapp with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))).
      * apply Forall2_concat.
        repeat rewrite_Forall_forall; solve_length;
          specialize (H1 a (List.map (fun _ => default_stream) b0) _ _ _ H11 eq_refl eq_refl);
          repeat rewrite_Forall_forall; simpl_length.
        -- rewrite <- map_nth.
           rewrite <- (map_nth (length (A:=_)) (List.map _ ss)). f_equal; solve_length.
           repeat rewrite map_map.
           apply map_ext_in. intros; solve_length.
        -- specialize (H14 a0 default_stream _ _ _ H12 eq_refl eq_refl).
           repeat simpl_nth; [| eassumption].
           eauto.
      * rewrite concat_map_singl2. assumption.
      * rewrite app_nil_r...
    - (* app (reset) *)
      simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
      repeat inv_bind. unfold normalize_exps in H0; repeat inv_bind.
      assert (NoDup (map fst (fresh_in r) ++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (fresh_ins l) ++ PS.elements (ps_adds (map fst (fresh_in r)) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
      eapply normalize_exps_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      assert (length x4 = 1) as Hlength2.
      { eapply normalize_exp_length in H1... rewrite <- length_typeof_numstreams in H1.
        rewrite H1, H10. reflexivity. }
      singleton_length.
      assert (sem_exp G H' b r [rs]) as Hsem' by (eapply sem_exp_refines; eauto). clear H16.
      eapply normalize_exp_sem in H1...
      destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. inv Hsem2; clear H13.
      eapply normalize_reset_sem in H2... 2:(destruct Histst2; auto).
      destruct H2 as [H''' [Href3 [Hvalid3 [Histst3 [Hsem3 Hsem3']]]]].
      exists H'''. repeat (split; auto).
      + repeat (etransitivity; eauto).
      + right. eexists; split...
        apply Sreset with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))) (rs:=rs) (bs:=bs); eauto.
        * apply Forall2_concat.
          repeat rewrite_Forall_forall; solve_length;
            specialize (H1 a (List.map (fun _ => default_stream) b0) _ _ _ H14 eq_refl eq_refl);
            repeat rewrite_Forall_forall; simpl_length.
          -- rewrite <- map_nth.
             rewrite <- (map_nth (length (A:=_)) (List.map _ ss)). f_equal; solve_length.
             repeat rewrite map_map.
             apply map_ext_in. intros; solve_length.
          -- specialize (H16 a0 default_stream _ _ _ H15 eq_refl eq_refl).
             repeat simpl_nth; [| eassumption].
             eapply sem_exp_refines; [| eauto]. etransitivity...
        * rewrite concat_map_singl2. assumption.
      + repeat rewrite Forall_app.
        repeat split; solve_forall; (eapply sem_equation_refines; [| eauto]); eauto.
        etransitivity...
  Qed.

  Corollary map_bind2_normalize_rhs_sem : forall G vars b keep_fby es H vs es' eqs' st st' reusable,
      NoDup (map fst (anon_ins es) ++ PS.elements reusable) ->
      Forall (wt_exp G vars) es ->
      Forall2 (sem_exp G H b) es vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_ins es)) reusable) ->
      hist_st (map fst vars) b H st ->
      map_bind2 (normalize_rhs keep_fby) es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (map fst vars) b H' st' /\
          Forall2 (fun es' vs =>
                     Forall2 (fun e v => sem_exp G H' b e [v]) es' vs \/
                     exists e', (es' = [e'] /\ sem_exp G H' b e' vs)) es' vs /\
          Forall (sem_equation G H' b) (concat eqs')).
  Proof with eauto.
    induction es; intros H vs es' eqs' st st' reusable Hndup Hwt Hsem Hvalid Histst Hmap;
      repeat inv_bind.
    - exists H; simpl. inv Hsem. repeat (split; auto).
    - inv Hwt. inv Hsem.
      unfold anon_ins in *. simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      assert (NoDup (map fst (anon_ins es) ++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (anon_in a) ++ PS.elements (ps_adds (map fst (anon_ins es)) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
      eapply normalize_rhs_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      assert (Forall2 (sem_exp G H' b) es l') as Hsem'.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
      eapply IHes in H1... clear IHes.
      destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]].
      exists H''. repeat (split; auto); simpl.
      + etransitivity...
      + constructor...
        destruct Hsem1.
        * left. repeat rewrite_Forall_forall. eapply sem_exp_refines...
        * right. destruct H0 as [e' [? H0]]; subst.
          exists e'. split... eapply sem_exp_refines...
      + apply Forall_app. split...
        solve_forall. eapply sem_equation_refines...
  Qed.

  Corollary normalize_rhss_sem : forall G vars b keep_fby es H vs es' eqs' st st' reusable,
      NoDup (map fst (anon_ins es) ++ PS.elements reusable) ->
      Forall (wt_exp G vars) es ->
      Forall2 (sem_exp G H b) es vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_ins es)) reusable) ->
      hist_st (map fst vars) b H st ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (map fst vars) b H' st' /\
          Forall (fun '(e, v) => sem_exp G H' b e v)
                 (combine_for_numstreams es' (concat vs)) /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros G vars b keep_fby es H vs es' eqs' st st' reusable Hndup Hwt Hsem Hvalid Histst Hnorm.
    assert (Forall (wt_exp G (vars++Typ.st_tys st')) es') as Hwt'.
    { eapply Typ.normalize_rhss_wt_exp in Hnorm... }
    unfold normalize_rhss in *.
    repeat inv_bind.
    eapply map_bind2_normalize_rhs_sem in H0...
    destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
    exists H'. repeat (split; auto).
    clear Hsem. induction Hsem1; simpl...
    simpl. destruct H0.
    - induction H0; simpl in *...
      inv Hwt'.
      assert (numstreams x = 1) as Hnumstreams.
      { eapply sem_exp_numstreams in H0... }
      constructor.
      + rewrite Hnumstreams; simpl...
      + rewrite Hnumstreams; simpl...
    - destruct H0 as [? [? H0]]; subst; simpl in *.
      inv Hwt'.
      assert (numstreams x1 = length y) as Hnumstreams.
      { eapply sem_exp_numstreams in H0... }
      constructor.
      + rewrite firstn_app, Hnumstreams, firstn_all, Nat.sub_diag, firstn_O, app_nil_r...
      + rewrite skipn_app...
  Qed.

  (** ** Conservation of sem_equation *)

  Fact combine_for_numstreams_length {V} : forall es (vs : list V),
      length (combine_for_numstreams es vs) = length es.
  Proof.
    induction es; intros vs; simpl; auto.
  Qed.

  Fact combine_for_numstreams_fst_split {V} : forall es (vs : list V),
      fst (split (combine_for_numstreams es vs)) = es.
  Proof.
    induction es; intros vs; simpl.
    - reflexivity.
    - destruct (split _) eqn:Hsplit; simpl.
      assert (fst (l, l0) = es).
      { rewrite <- Hsplit; auto. }
      simpl in H. f_equal; auto.
  Qed.

  Fact combine_for_numstreams_numstreams {V} : forall es (vs : list V),
      length vs = length (annots es) ->
      Forall (fun '(e, v) => numstreams e = length v) (combine_for_numstreams es vs).
  Proof with eauto.
    induction es; intros vs Hlen; simpl in *...
    rewrite app_length in Hlen.
    rewrite length_annot_numstreams in Hlen.
    constructor...
    - rewrite firstn_length.
      symmetry. apply Nat.min_l.
      omega.
    - apply IHes.
      rewrite skipn_length.
      omega.
  Qed.

  Fact combine_for_numstreams_nth_2 {V1 V2} : forall es (v1s : list V1) (v2s : list V2) n n0 e v1 v2 d1 d2 de1 de2,
      length v1s = length (annots es) ->
      length v2s = length (annots es) ->
      n < length es ->
      n0 < length v1 ->
      nth n (combine_for_numstreams es v1s) de1 = (e, v1) ->
      nth n (combine_for_numstreams es v2s) de2 = (e, v2) ->
      exists n',
        (n' < length v1s /\
         nth n' v1s d1 = nth n0 v1 d1 /\
         nth n' v2s d2 = nth n0 v2 d2).
  Proof with eauto.
    induction es; intros v1s v2s n n0 e v1 v2 d1 d2 de1 de2 Hlen1 Hlen2 Hn Hn0 Hnth1 Hnth2;
      simpl in *; try omega.
    rewrite app_length in *. rewrite length_annot_numstreams in *.
    destruct n.
    - inv Hnth1; inv Hnth2.
      rewrite firstn_length in Hn0; rewrite Nat.min_glb_lt_iff in Hn0; destruct Hn0.
      exists n0. repeat split...
      + rewrite nth_firstn_1...
      + rewrite nth_firstn_1...
    - apply lt_S_n in Hn.
      eapply IHes in Hn. 4,5,6:eauto.
      + destruct Hn as [n' [Hlen' [Hnth1' Hnth2']]].
        exists (n'+(numstreams a)).
        repeat split.
        * rewrite skipn_length in Hlen'. omega.
        * rewrite nth_skipn in Hnth1'...
        * rewrite nth_skipn in Hnth2'...
      + rewrite skipn_length. omega.
      + rewrite skipn_length. omega.
  Qed.

  Fact normalize_equation_sem : forall G vars H b to_cut equ eqs' st st' reusable,
      NoDup (map fst (anon_in_eq equ) ++ PS.elements reusable) ->
      wt_equation G vars equ ->
      sem_equation G H b equ ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in_eq equ)) reusable) ->
      hist_st (map fst vars) b H st ->
      normalize_equation to_cut equ st = (eqs', st') ->
      (exists H', Env.refines eq H H' /\
             st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
             hist_st (map fst vars) b H' st' /\
             Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros G vars H b to_cut equ eqs' st st' reusable Hndup Hwt Hsem Hvalid Histst Hnorm.
    unfold normalize_equation in Hnorm.
    destruct equ as [xs es]. inv Hwt. inv Hsem.
    repeat inv_bind.
    assert (typesof x = typesof es) as Hannots by (eapply Typ.normalize_rhss_typesof; eauto).
    eapply normalize_rhss_sem in H2...
    destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
    exists H'. repeat (split; eauto).
    apply Forall_app. split...
    clear Hsem1'.
    repeat rewrite_Forall_forall.
    destruct x1. repeat simpl_In. inv H7.
    assert (HIn := H8).
    eapply In_nth with (d:=(hd_default [], [])) in H8. destruct H8 as [n [Hn Hnth]].
    rewrite combine_for_numstreams_length in Hn. rewrite <- (combine_for_numstreams_length _ (concat ss)) in Hn.
    assert (HIn' := Hn).
    apply nth_In with (d:=(hd_default [], [])) in HIn'.
    specialize (Hsem1 _ HIn').
    destruct (nth _ _ _) eqn:Hnth' in Hsem1. rewrite Hnth' in HIn'.
    assert (e = e0) as Hee0.
    { rewrite split_nth in Hnth; inv Hnth.
      rewrite split_nth in Hnth'; inv Hnth'.
      repeat rewrite combine_for_numstreams_fst_split. reflexivity. } subst.
    apply Seq with (ss:=[l0]).
    + repeat constructor...
    + simpl. rewrite app_nil_r.
      repeat rewrite_Forall_forall.
      * rewrite <- Hannots in H1. rewrite typesof_annots in H1. rewrite map_length in H1.
        replace (length l) with (numstreams e0). replace (length l0) with (numstreams e0). reflexivity.
        { rewrite H2 in H1. apply combine_for_numstreams_numstreams in H1.
          rewrite Forall_forall in H1. apply H1 in HIn'... }
        { apply combine_for_numstreams_numstreams in H1.
          rewrite Forall_forall in H1. apply H1 in HIn... }
      * eapply sem_var_refines...
        specialize (combine_for_numstreams_nth_2 x xs (concat ss) n n0 e0 l l0
                                                 a b0 (hd_default [], []) (hd_default [], [])) as Hcomb.
        apply Hcomb in H7. clear Hcomb.
        2,3:(rewrite <- Hannots in H1; rewrite typesof_annots in H1; rewrite map_length in H1).
        2:eapply H1. 2:(rewrite H2 in H1; eapply H1).
        3,4:auto.
        2:(rewrite combine_for_numstreams_length in Hn; auto).
        destruct H7 as [n' [Hlen' [Hnth1' Hnth2']]].
        eapply H3...
  Qed.

  Corollary normalize_equations_sem : forall G vars b to_cut eqs H eqs' st st' reusable,
      NoDup (map fst (anon_in_eqs eqs) ++ PS.elements reusable) ->
      Forall (wt_equation G vars) eqs ->
      Forall (sem_equation G H b) eqs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in_eqs eqs)) reusable) ->
      hist_st (map fst vars) b H st ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      (exists H', Env.refines eq H H' /\
             Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction eqs; intros H eqs' st st' reusable Hndup Hwt Hsem Hvalid Hdome Hnorm;
      inv Hwt; inv Hsem; repeat inv_bind.
    - exists H...
    - unfold anon_in_eqs in *; simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      assert (NoDup (map fst (anon_in_eqs eqs) ++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (anon_in_eq a) ++ PS.elements (ps_adds (map fst (anon_in_eqs eqs)) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
      eapply normalize_equation_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 Hsem1]]]].
      assert (Forall (sem_equation G H' b) eqs) by (solve_forall; eapply sem_equation_refines; eauto).
      eapply IHeqs in H1...
      destruct H1 as [H'' [Href Hsem2]].
      exists H''. repeat split...
      + etransitivity...
      + eapply Forall_app. split...
        solve_forall. eapply sem_equation_refines...
  Qed.

  (** ** Preservation of the semantics while restricting an environment *)

  Fact sem_var_restrict {B} : forall (vars : list (ident * B)) H id ty v,
      In (id, ty) vars ->
      sem_var H id v ->
      sem_var (Env.restrict H (List.map fst vars)) id v.
  Proof.
    intros vars H id ty v HIn Hsem.
    inv Hsem.
    econstructor; eauto.
    apply Env.find_1 in H1. apply Env.find_2.
    apply Env.restrict_find; auto.
    simpl_In. exists (id, ty); auto.
  Qed.

  Fact sem_exp_restrict : forall G vars H b e vs,
      wt_exp G vars e ->
      sem_exp G H b e vs ->
      sem_exp G (Env.restrict H (List.map fst vars)) b e vs.
  Proof with eauto.
    induction e using exp_ind2; intros vs Hwt Hsem; inv Hwt; inv Hsem.
    - (* const *)
      constructor...
    - (* var *)
      constructor. eapply sem_var_restrict...
    - (* unop *)
      econstructor...
    - (* binop *)
      econstructor...
    - (* fby *)
      econstructor...
      + repeat rewrite_Forall_forall. eapply H0...
      + repeat rewrite_Forall_forall. eapply H1...
    - (* when *)
      econstructor...
      + repeat rewrite_Forall_forall. eapply H0...
      + eapply sem_var_restrict...
    - (* merge *)
      econstructor...
      + eapply sem_var_restrict...
      + repeat rewrite_Forall_forall. eapply H0...
      + repeat rewrite_Forall_forall. eapply H1...
    - (* ite *)
      econstructor...
      + repeat rewrite_Forall_forall. eapply H0...
      + repeat rewrite_Forall_forall. eapply H1...
    - (* app *)
      econstructor...
      repeat rewrite_Forall_forall. eapply H1...
    - (* app (reset) *)
      econstructor...
      repeat rewrite_Forall_forall. eapply H1...
  Qed.

  Fact sem_equation_restrict : forall G vars H b eq,
      wt_equation G vars eq ->
      sem_equation G H b eq ->
      sem_equation G (Env.restrict H (List.map fst vars)) b eq.
  Proof with eauto.
    intros G vars H b [xs es] Hwt Hsem.
    inv Hwt. inv Hsem.
    econstructor.
    + repeat rewrite_Forall_forall; eauto.
      eapply sem_exp_restrict...
    + repeat rewrite_Forall_forall.
      eapply sem_var_restrict...
      Unshelve. eapply Op.bool_type.
  Qed.

  (** ** Preservation of sem_node *)

  Fact init_st_hist_st : forall b H n,
      Env.dom H (List.map fst (n_in n++n_vars n++n_out n)) ->
      hist_st (map fst (n_in n++n_vars n++n_out n)) b H
              (init_st (first_unused_ident (self::out::(map fst (n_in n++n_vars n++n_out n++anon_in_eqs (n_eqs n)))))).
  Proof.
    intros b H n Hdom.
    constructor.
    - unfold st_ids.
      rewrite init_st_anns; simpl.
      rewrite app_nil_r. assumption.
    - unfold init_eqs_valids.
      rewrite init_st_anns. constructor.
  Qed.

  Fact sem_var_In : forall H vs ss,
      Forall2 (sem_var H) vs ss ->
      Forall (fun v => Env.In v H) vs.
  Proof.
    intros. repeat rewrite_Forall_forall.
    apply In_nth with (d:=xH) in H2. destruct H2 as [n [Hn H2]].
    eapply H1 in Hn. 2,3:reflexivity.
    setoid_rewrite H2 in Hn.
    inv Hn. apply Env.find_1 in H4.
    apply Env.find_In in H4. auto.
    Unshelve. exact default_stream.
  Qed.

  Fact sem_equation_In : forall G H b eqs,
      Forall (sem_equation G H b) eqs ->
      Forall (fun v => Env.In v H) (vars_defined eqs).
  Proof.
    induction eqs; intros Hsem; inv Hsem; simpl.
    - constructor.
    - destruct a; simpl.
      inv H2.
      apply Forall_app. split; auto.
      apply sem_var_In in H8; auto.
  Qed.

  Fact normalize_node_sem_equation : forall G H n Hwl ins to_cut,
      Env.dom H (List.map fst (n_in n ++ n_vars n ++ n_out n)) ->
      Forall (wt_equation G (idty (n_in n ++ n_vars n ++ n_out n))) (n_eqs n) ->
      Forall (sem_equation G H (Str.clocks_of ins)) (n_eqs n) ->
      exists H', Env.refines eq H H' /\
            Forall (sem_equation G H' (Str.clocks_of ins)) (n_eqs (normalize_node to_cut n Hwl)).
  Proof with eauto.
    intros G H n Hwl ins to_cut Hdom Hwt Hsem.
    remember (@init_st ((Op.type * clock) * bool)
                (first_unused_ident (self::out::(map fst (n_in n++n_vars n++n_out n++anon_in_eqs (n_eqs n)))))) as init.
    specialize (n_nodup n) as Hndup; rewrite fst_NoDupMembers in Hndup; repeat rewrite map_app in Hndup.
    eapply normalize_equations_sem with (st:=init)...
    4: simpl; rewrite <- surjective_pairing; subst; reflexivity.
    - rewrite PSP.elements_empty, app_nil_r.
      repeat ndup_r Hndup...
    - rewrite Heqinit.
      apply init_st_valid_reuse.
      + unfold idty; rewrite map_map, ps_adds_of_list; repeat rewrite map_app.
        repeat rewrite ps_of_list_ps_to_list_Perm.
        * repeat rewrite <- app_assoc...
        * repeat ndup_r Hndup.
        * repeat rewrite app_assoc in Hndup. apply NoDup_app_l in Hndup.
          repeat rewrite <- app_assoc in Hndup...
      + rewrite <- ps_adds_of_list, PS_For_all_ps_adds; split. 2:apply PS_For_all_empty.
        eapply Forall_incl. eapply first_unused_ident_gt; reflexivity.
        unfold idty; rewrite map_map.
        apply incl_tl, incl_tl, incl_map, incl_appr', incl_appr', incl_appl, incl_refl.
      + rewrite PS_For_all_ps_adds; split. 2:apply PS_For_all_empty.
        eapply Forall_incl. eapply first_unused_ident_gt; reflexivity.
        apply incl_tl, incl_tl, incl_map, incl_appr, incl_appr, incl_appr, incl_refl.
    - rewrite Heqinit.
      unfold idty; rewrite map_map.
      eapply init_st_hist_st...
  Qed.

  Lemma normalize_node_eq : forall G G' f n Hwl ins outs to_cut,
      Ordered_nodes (n::G) ->
      Ordered_nodes ((normalize_node to_cut n Hwl)::G') ->
      global_sem_refines G G' ->
      wt_node G n ->
      sem_node (n::G) f ins outs ->
      sem_node ((normalize_node to_cut n Hwl)::G') f ins outs.
  Proof with eauto.
    intros G G' f n Hwl ins outs to_cut Hord1 Hord2 Href Hwt Hsem.
    inv Hsem; simpl in H0. destruct (ident_eqb (n_name n) f) eqn:Hident.
    - inv H0.
      (* New env H' (restrict H) and its properties *)
      remember (Env.restrict H (List.map fst (n_in n0++n_vars n0++n_out n0))) as H'.
      assert (Env.refines eq H' H) as Href'.
      { rewrite HeqH'. eapply Env.restrict_refines... }
      assert (Forall2 (sem_var H') (idents (n_in n0)) ins) as Hin.
      { repeat rewrite_Forall_forall.
        eapply sem_var_restrict; [|eauto].
        unfold idents in *. erewrite map_nth'; [| solve_length].
        rewrite <- surjective_pairing.
        apply in_or_app. left. apply nth_In. solve_length.
        Unshelve. exact (xH, (Op.bool_type, Cbase)). } clear H1.
      assert (Forall2 (sem_var H') (idents (n_out n0)) outs) as Hout.
      { repeat rewrite_Forall_forall.
        eapply sem_var_restrict; [|eauto].
        unfold idents in *. erewrite map_nth'; [| solve_length].
        rewrite <- surjective_pairing.
        repeat (apply in_or_app; right). apply nth_In. solve_length.
        Unshelve. exact (xH, (Op.bool_type, Cbase)). } clear H2.
      assert (Env.dom H' (List.map fst (n_in n0 ++ n_vars n0 ++ n_out n0))) as Hdom.
      { rewrite HeqH'. apply Env.dom_lb_restrict_dom.
        apply Env.dom_lb_intro. intros x HIn.
        repeat rewrite map_app in HIn. repeat rewrite in_app_iff in HIn. destruct HIn as [HIn|[HIn|HIn]].
        + eapply Env.In_refines...
          apply sem_var_In in Hin. rewrite Forall_forall in Hin...
        + specialize (n_defd n0) as Hdef; symmetry in Hdef.
          assert (In x (vars_defined (n_eqs n0))) as HIn'.
          { eapply Permutation_in in Hdef;[eauto|].
            rewrite map_app. apply in_or_app... }
          apply sem_equation_In in H3. rewrite Forall_forall in H3...
        + eapply Env.In_refines...
          apply sem_var_In in Hout. rewrite Forall_forall in Hout...
      }
      (* Reasoning on the semantics of equations *)
      assert (Forall (sem_equation G H (Str.clocks_of ins)) (n_eqs n0)).
      { eapply Forall_sem_equation_global_tl...
        eapply find_node_not_Is_node_in in Hord1...
        simpl. rewrite ident_eqb_refl... } clear H3.
      destruct Hwt as [_ [_ [_ Hwt]]].
      assert (Forall (sem_equation G H' (Str.clocks_of ins)) (n_eqs n0)).
      { rewrite HeqH'.
        clear Hin Hout.
        repeat rewrite_Forall_forall.
        specialize (H0 _ H1). specialize (Hwt _ H1).
        eapply sem_equation_restrict in H0...
        unfold idty in H0. rewrite map_map in H0. simpl in H0... } clear H0.
      eapply normalize_node_sem_equation in H1...
      destruct H1 as [H'' [Href'' Heqs']].
      eapply Snode with (H:=H''); simpl. 5:reflexivity.
      + rewrite Hident; reflexivity.
      + simpl. repeat rewrite_Forall_forall. eapply sem_var_refines...
      + simpl. repeat rewrite_Forall_forall. eapply sem_var_refines...
      + clear Hin Hout Hdom.
        assert (Forall (sem_equation G' H'' (Str.clocks_of ins)) (n_eqs (normalize_node to_cut n0 Hwl))).
        { eapply Forall_impl; [| eauto]. intros a Hsem. eapply sem_eq_sem_equation... } clear Heqs'.
        apply Forall_sem_equation_global_tl'...
        eapply find_node_not_Is_node_in in Hord2...
        simpl. rewrite ident_eqb_refl...
    - specialize (Href f ins outs).
      eapply sem_node_cons'...
      + apply Href. econstructor...
        eapply Forall_impl_In; [| eauto]. intros eq Hin Hsem.
        eapply sem_equation_global_tl...
        eapply find_node_later_not_Is_node_in in Hord1...
        intro Hisin. apply Hord1. rewrite Is_node_in_Exists. rewrite Exists_exists.
        eexists...
      + simpl. apply ident_eqb_neq in Hident...
  Qed.

  Lemma normalize_global_eq : forall G Hwl,
      wt_global G ->
      Ordered_nodes G ->
      global_sem_refines G (normalize_global G Hwl).
  Proof with eauto.
    induction G; intros Hwl Hwt Hordered; simpl; inv Hwt.
    - apply global_sem_eq_nil.
    - apply global_sem_eq_cons with (f:=n_name a)...
      + eapply Ord.normalize_global_ordered in Hordered.
        simpl in Hordered...
      + inv Hordered...
      + intros f ins outs.
        eapply normalize_node_eq...
        * eapply Ord.normalize_global_ordered in Hordered.
          simpl in Hordered...
        * inv Hordered...
  Qed.

End CORRECTNESS.

Module CorrectnessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str : COINDSTREAMS Op OpAux)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn)
       (Clo : LCLOCKING Ids Op Syn)
       (Lord : LORDERED Ids Op Syn)
       (Sem : LSEMANTICS Ids Op OpAux Syn Lord Str)
       (Norm : FULLNORM Ids Op OpAux Syn)
       <: CORRECTNESS Ids Op OpAux Str Syn Typ Clo Lord Sem Norm.
  Include CORRECTNESS Ids Op OpAux Str Syn Typ Clo Lord Sem Norm.
  Module Typing := NTypingFun Ids Op OpAux Syn Typ Norm.
  Module Clocking := NClockingFun Ids Op OpAux Syn Clo Norm.
  Module Ordered := NOrderedFun Ids Op OpAux Syn Lord Norm.
End CorrectnessFun.
