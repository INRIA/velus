From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

Require Import Omega.

From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LSemantics Lustre.LClockSemantics.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.
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
       (Cl : LCLOCKING Ids Op Syn)
       (Import Ord : LORDERED Ids Op Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Syn Ord Str)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn).

  Import Fresh Tactics.
  Module Import ClockSem := LClockSemanticsFun Ids Op OpAux Syn Cl Ord Str Sem.
  Module Import Typ := NTypingFun Ids Op OpAux Syn Typ Norm.
  Module Clo := NClockingFun Ids Op OpAux Syn Cl Norm.
  Module Ord := NOrderedFun Ids Op OpAux Syn Ord Norm.

  CoFixpoint default_stream : Stream OpAux.value :=
    Cons absent default_stream.

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
      rewrite length_annot_numstreams. eapply H0...
      + apply nth_In; congruence.
      + apply H5. apply nth_In; congruence.
    - (* when *)
      repeat rewrite_Forall_forall.
      rewrite <- H1. rewrite <- H7.
      unfold annots; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite Forall2_map_2.
      rewrite_Forall_forall; solve_length.
      rewrite length_annot_numstreams. eapply H0...
      + apply nth_In; congruence.
      + apply H4. apply nth_In; congruence.
    - (* merge *)
      repeat rewrite_Forall_forall.
      rewrite <- H10. rewrite <- H11.
      unfold annots; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite Forall2_map_2.
      rewrite_Forall_forall; solve_length.
      rewrite length_annot_numstreams. eapply H0...
      + apply nth_In; congruence.
      + apply H7. apply nth_In; congruence.
    - (* ite *)
      repeat rewrite_Forall_forall.
      rewrite <- H11. rewrite <- H15.
      unfold annots; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite Forall2_map_2.
      rewrite_Forall_forall; solve_length.
      rewrite length_annot_numstreams.
      eapply H0...
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

  (** ** Conservation of valid_after *)

  Definition valid_after {A B} (l : list (ident * A)) (st : fresh_st B) :=
    fresh_st_valid st /\ before_st (List.map fst l) st.

  Fact fresh_ident_valid_after {A B} : forall (l : list (ident * A)) (a : B) id st st',
      fresh_ident a st = (id, st') ->
      valid_after l st ->
      valid_after l st'.
  Proof.
    intros l a id st st' Hfresh [Hvalid Hbef].
    repeat constructor; eauto.
  Qed.
  Hint Resolve fresh_ident_valid_after.

  Fact idents_for_anns_valid_after {A} : forall (l : list (ident * A)) anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      valid_after l st ->
      valid_after l st'.
  Proof.
    induction anns; intros ids st st' Hids Hvalid;
      simpl in Hids.
    - repeat inv_bind; eauto.
    - destruct a as [ty [cl _]]. repeat inv_bind. eauto.
  Qed.
  Hint Resolve idents_for_anns_valid_after.

  Fact normalize_reset_valid_after {A} : forall (l : list (ident * A)) e e' eqs' st st',
      normalize_reset e st = (e', eqs', st') ->
      valid_after l st ->
      valid_after l st'.
  Proof.
    intros l e e' eqs' st st' Hnorm Hvalid.
    destruct (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind; auto.
    destruct (List.hd _ _); simpl in *.
    destruct p. repeat inv_bind. eauto.
  Qed.
  Hint Resolve normalize_reset_valid_after.

  (** Some additional stuff *)

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

  Import Permutation.

  Fact fresh_ident_dom {A B V} : forall (vars : list (ident * A)) H H' a id (v : V) (st st' : fresh_st B),
      valid_after vars st ->
      Env.dom H ((List.map fst vars)++(st_ids st)) ->
      fresh_ident a st = (id, st') ->
      H' = Env.add id v H ->
      Env.dom H' ((List.map fst vars)++(st_ids st')).
  Proof.
    intros vars H H' a id v st st' Hvalid Hdom Hfresh Heq.
    apply Facts.fresh_ident_vars_perm in Hfresh.
    rewrite Heq.
    apply Env.dom_add_cons with (x:=id) (v0:=v) in Hdom.
    eapply Env.dom_Permutation; [| eauto].
    symmetry. rewrite Permutation_middle.
    apply Permutation_app_head. assumption.
  Qed.

  Fact fresh_ident_refines {A B V} : forall (vars : list (ident * A)) H H' a id (v : V) (st st' : fresh_st B),
      valid_after vars st ->
      Env.dom H ((List.map fst vars)++(st_ids st)) ->
      fresh_ident a st = (id, st') ->
      H' = Env.add id v H ->
      Env.refines eq H H'.
  Proof with eauto.
    intros vars H H' a id v st st' Hvalid Hdom Hfresh Heq.
    rewrite Heq.
    assert (before_st (List.map fst vars) st') as Hbef1 by (destruct Hvalid as [_ ?]; eauto).
    eapply Env.refines_add...
    intro contra. erewrite Env.dom_use in contra; [| eauto].
    apply in_app_or in contra. destruct contra.
    + eapply Facts.fresh_ident_In in Hfresh.
      assert (In id (st_ids st')).
      { unfold st_ids, idty. repeat simpl_In; simpl in *.
        exists (i, a); auto. }
      apply smallest_ident_In in H1.
      unfold before_st in Hbef1.
      repeat rewrite_Forall_forall.
      apply Hbef1 in H0.
      apply (Pos.lt_irrefl id). eapply Pos.lt_le_trans...
    + eapply Facts.fresh_ident_nIn in Hfresh. 2:(destruct Hvalid; eauto).
      congruence.
  Qed.

  Fact idents_for_anns_dom {B V} : forall (vars : list (ident * B)) H H' anns ids (vs : list V) st st',
      length vs = length ids ->
      valid_after vars st ->
      Env.dom H ((List.map fst vars)++(st_ids st)) ->
      idents_for_anns anns st = (ids, st') ->
      H' = Env.adds (List.map fst ids) vs H ->
      Env.dom H' ((List.map fst vars)++(st_ids st')).
  Proof with eauto.
    intros vars H H' anns ids vs st st' Hlen Hvalid Hdom Hids Heq.
    apply idents_for_anns_vars_perm in Hids.
    rewrite Heq.
    apply Env.dom_adds with (ids0:=List.map fst ids) (vs0:=vs) in Hdom.
    2:(repeat rewrite_Forall_forall; solve_length).
    eapply Env.dom_Permutation; [|eauto].
    symmetry. rewrite Permutation_app_comm. rewrite <- app_assoc. apply Permutation_app_head.
    rewrite Permutation_app_comm. assumption.
  Qed.

  Fact idents_for_anns_refines {B V} : forall (vars : list (ident * B)) H H' anns ids (vs : list V) st st',
      length vs = length ids ->
      valid_after vars st ->
      Env.dom H ((List.map fst vars)++(st_ids st)) ->
      idents_for_anns anns st = (ids, st') ->
      H' = Env.adds (List.map fst ids) vs H ->
      Env.refines eq H H'.
  Proof with eauto.
    intros vars H H' anns ids vs st st' Hlen Hvalid Hdom Hids Heq.
    assert (Forall (fun id => ~List.In id (List.map fst vars)) (List.map fst ids)) as Hnvar.
    { assert (valid_after vars st') by eauto.
      apply idents_for_anns_incl_ids in Hids.
      solve_forall.
      apply Hids in H1. clear Hids.
      intro contra.
      destruct H0 as [_ H0]. unfold before_st in H0.
      rewrite Forall_forall in H0. apply H0 in contra.
      unfold idty in H1.
      apply smallest_ident_In in H1.
      apply (Pos.lt_irrefl x). eapply Pos.lt_le_trans...
    }
    rewrite Heq. apply Env.refines_adds.
    apply idents_for_anns_nIn in Hids; auto.
    rewrite Forall_forall in *. intros x1 Hin contra.
    erewrite Env.dom_use in contra; [|eauto].
    apply in_app_or in contra; destruct contra.
    + eapply Hnvar...
    + eapply Hids...
    + destruct Hvalid...
  Qed.

  (** ** Relation between state and history *)

  (** We want to specify the semantics of the init equations created during the normalization
      with idents stored in the env *)

  (* Pas possible de prouver que c'est la semantique de Swhen false sans le lemme d'alignement...
     Ou alors il faut calculer les horloges differement *)

  CoFixpoint const_val (b : Stream bool) (v : Op.val) : Stream value :=
    Cons (if hd b then present v else absent) (const_val (tl b) v).

  Fact const_val_Cons : forall b bs v,
      const_val (Cons b bs) v =
      Cons (if b then present v else absent) (const_val bs v).
  Proof.
    intros b bs v.
    rewrite Stream_decompose_thm at 1; reflexivity.
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
    | Cons (present v') str' => Cons (present v) (shift v' str')
    | Cons absent str' => Cons absent (shift v str')
    end.

  Fact shift_Cons : forall v y ys,
      shift v (Cons y ys) =
      match y with
      | present v' => Cons (present v) (shift v' ys)
      | absent => Cons absent (shift v ys)
      end.
  Proof.
    intros v y ys.
    rewrite Stream_decompose_thm at 1; simpl.
    destruct y; reflexivity.
  Qed.

  Add Parametric Morphism : shift
      with signature eq ==> @EqSt value ==> @EqSt value
    as shift_EqSt.
  Proof.
    cofix CoFix.
    intros v [x xs] [y ys] Heq.
    inv Heq; simpl in *; subst.
    repeat rewrite shift_Cons.
    destruct y; simpl; constructor; simpl; auto.
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
      rewrite const_val_Cons; rewrite Stream_decompose_thm; simpl.
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
    match (hd b) with
    | true => shift v ys
    | false => Cons absent (prefix_with_val (tl b) v (tl ys))
    end.

  Fact prefix_with_val_Cons : forall b bs v ys,
      prefix_with_val (Cons b bs) v ys =
      match b with
      | true => shift v ys
      | false => Cons absent (prefix_with_val bs v (tl ys))
      end.
  Proof.
    intros b bs v ys.
    rewrite Stream_decompose_thm at 1; simpl.
    destruct b; auto.
    destruct (shift v ys); auto.
  Qed.

  Add Parametric Morphism : prefix_with_val
    with signature eq ==> eq ==> @EqSt value ==> @EqSt value
      as prefix_with_val_EqSt.
  Proof.
    cofix CoFix.
    intros [b bs] v [x xs] [y ys] Heq.
    inv Heq; simpl in *.
    repeat rewrite prefix_with_val_Cons.
    destruct b.
    - destruct x; rewrite <- H; simpl.
      + constructor; simpl; auto.
        rewrite H0. reflexivity.
      + constructor; simpl; auto.
        rewrite H0. reflexivity.
    - constructor; simpl; auto.
  Qed.

  Lemma prefix_with_val_fby : forall b v y,
      synchronized y b ->
      fby (const_val b v) y (prefix_with_val b v y).
  Proof with eauto.
    cofix prefix_with_val_fby.
    intros [b0 b] v y Hsync.
    rewrite const_val_Cons.
    rewrite Stream_decompose_thm; simpl.
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

  Definition init_eqs_valids H b (st : fresh_st (Op.type * clock * bool)) :=
    Forall (fun '(id, (_, cl, is_init)) =>
                  is_init = true ->
                  ((* wt_clock (idty (idty (st_anns st))) cl /\  *)sem_var H id (init_stream H b cl))) (st_anns st).
  (* Typing hypothesis ? *)

  Definition hist_st {A} (l : list (ident * A)) b H st :=
    Env.dom H ((List.map fst l)++(st_ids st)) /\
    init_eqs_valids H b st.

  Fact fresh_ident_hist_st {A} : forall (vars : list (ident * A)) b a id v H st st',
      valid_after vars st ->
      fresh_ident (a, false) st = (id, st') ->
      hist_st vars b H st ->
      hist_st vars b (Env.add id v H) st'.
  Proof.
    intros vars b a id v H st st' Hvalid Hfresh [H1 H2].
    constructor.
    - eapply fresh_ident_dom; eauto.
    - unfold init_eqs_valids in *.
      assert (~In id (st_ids st)) by (destruct Hvalid; eapply Facts.fresh_ident_nIn in Hfresh; eauto).
      assert (valid_after vars st') as Hvalid2 by eauto.
      eapply fresh_ident_anns in Hfresh.
      rewrite Hfresh.
      constructor; eauto.
      + destruct a. intros. congruence.
      + repeat rewrite_Forall_forall.
        destruct x as [id0 [[ty cl] is_init]].
        specialize (H2 _ H3). simpl in H2.
        intro His. apply H2 in His. clear H2.
        eapply sem_var_refines; [| eauto].
        apply Env.refines_add. eauto.
        intro contra.
        erewrite Env.dom_use in contra; [| eauto].
        eapply in_app_or in contra.
        destruct contra.
        * assert (In id (st_ids st')).
          { unfold st_ids, idty. rewrite Hfresh. simpl. auto. }
          eapply smallest_ident_In in H4.
          destruct Hvalid2 as [_ Hvalid2].
          unfold before_st in Hvalid2. rewrite Forall_forall in Hvalid2.
          apply Hvalid2 in H2.
          apply (Pos.lt_irrefl id).
          eapply Pos.lt_le_trans; eauto.
        * congruence.
        * admit. (* We have to proove that the variables in cl are in H
                    (cl is well-typed in the env corresponding to H) *)
  Admitted.
  Hint Resolve fresh_ident_hist_st.

  Fact idents_for_anns_hist_st {A} : forall (vars : list (ident * A)) b anns ids vs H st st',
      length vs = length ids ->
      valid_after vars st ->
      idents_for_anns anns st = (ids, st') ->
      hist_st vars b H st ->
      hist_st vars b (Env.adds (List.map fst ids) vs H) st'.
  Proof with eauto.
    intros vars b anns ids vs H st st' Hlen Hvalid Hids Hist.
    constructor.
    - destruct Hist.
      eapply idents_for_anns_dom in Hids...
    - revert ids vs H st st' Hlen Hvalid Hids Hist.
      induction anns; intros; simpl in Hids; repeat inv_bind; simpl.
      + unfold Env.adds; simpl. destruct Hist. assumption.
      + destruct a as [? [? ?]]. repeat inv_bind.
        destruct vs; simpl in Hlen; try congruence.
        unfold Env.adds; simpl.
        assert (valid_after vars st') by eauto.
        assert (valid_after vars x0) by eauto.
        eapply fresh_ident_hist_st in H0...
        eapply IHanns in H1...
  Qed.
  Hint Resolve idents_for_anns_hist_st.

  (** ** Conservation of sem_exp *)

  Fact map_bind2_sem : forall G vars b is_control es H vs es' eqs' st st',
      Forall (wt_exp G vars) es ->
      Forall2 (sem_exp G H b) es vs ->
      valid_after vars st ->
      hist_st vars b H st ->
      Forall2 (fun e v => forall H es' eqs' st st',
                   sem_exp G H b e v ->
                   valid_after vars st ->
                   hist_st vars b H st ->
                   normalize_exp is_control e st = (es', eqs', st') ->
                   (exists H',
                       Env.refines eq H H' /\
                       valid_after vars st' /\
                       hist_st vars b H' st' /\
                       Forall2 (fun e v => sem_exp G H' b e [v]) es' v /\
                       Forall (sem_equation G H' b) eqs')) es vs ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          valid_after vars st' /\
          hist_st vars b H' st' /\
          Forall2 (fun es vs => Forall2 (fun e v => sem_exp G H' b e [v]) es vs) es' vs /\
          Forall (sem_equation G H' b) (concat eqs')).
  Proof with eauto.
    induction es; intros H vs es' eqs' st st' Hwt Hsem Hvalid Histst Hf Hmap;
      inv Hwt; inv Hsem; inv Hf; simpl in Hmap; repeat inv_bind.
    - exists H; simpl. repeat (split; eauto).
    - specialize (H7 _ _ _ _ _ H4 Hvalid Histst H0). destruct H7 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      assert (Forall2 (sem_exp G H' b) es l') as Hsem'.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
      specialize (IHes _ _ _ _ _ _ H3 Hsem' Hvalid1 Histst1 H9 H1). clear H9.
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

  Fact normalize_reset_sem {B} : forall G (vars : list (ident * B)) b e H v e' eqs' st st',
      sem_exp G H b e [v] ->
      valid_after vars st ->
      hist_st vars b H st ->
      Env.dom H ((List.map fst vars)++(st_ids st)) ->
      normalize_reset e st = (e', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          valid_after vars st' /\
          hist_st vars b H' st' /\
          sem_exp G H' b e' [v] /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros G vars b e H v e' eqs' st st' Hsem Hvalid Histst Hdom Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind.
    - exists H. repeat (split; auto).
    - destruct (List.hd _ _) as [? [? ?]] eqn:Heqann; simpl in *; repeat inv_bind.
      assert (fresh_st_follows st st') as Hfollows by eauto.
      assert (valid_after vars st') as Hvalid1 by eauto.
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

  Fact fby_iteexp_sem {B} : forall G (vars : list (ident * B)) b H e0 e a y0 y z e' eqs' st st',
      sem_exp G H b e0 [y0] ->
      sem_exp G H b e [y] ->
      fby y0 y z ->
      valid_after vars st ->
      hist_st vars b H st ->
      fby_iteexp e0 e a st = (e', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          valid_after vars st' /\
          hist_st vars b H' st' /\
          sem_exp G H' b e' [z] /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros G vars b H e0 e [ty cl] y0 y z e' eqs' st st' Hsem0 Hsem Hfby Hvalid Histst Hiteexp.
    unfold fby_iteexp in Hiteexp.
    destruct (is_constant e0); repeat inv_bind.
    - exists H. repeat (split; eauto).
      econstructor.
      + constructor; eauto.
      + constructor; eauto.
      + repeat constructor. assumption.
    - unfold init_var_for_clock in H0.
      destruct (find _ _) eqn:Hfind.
      + destruct p; inv H0.
        remember (interp_clock H b (fst cl)) as b'.
        remember (prefix_with_val b' (Op.sem_const (Op.init_type ty)) y) as y'.
        remember (Env.add x2 y' H) as H'.
        assert (Env.refines eq H H') by (destruct Histst; eapply fresh_ident_refines in H1; eauto).
        exists H'. repeat (split; eauto).
        * destruct Histst. eapply fresh_ident_dom in H1...
        * eapply fresh_ident_hist_st in H1...
          rewrite <- HeqH' in H1.
          destruct H1...
        * (* We can get data about x back from our hist_st hypothesis *)
          assert (sem_var H x (init_stream H b (fst cl))).
          { destruct Histst as [_ Hvalids]. unfold init_eqs_valids in Hvalids.
            rewrite Forall_forall in Hvalids.
            eapply find_some in Hfind. destruct p as [[ty' cl'] isinit].
            repeat rewrite Bool.andb_true_iff in Hfind. destruct Hfind as [Hin [[Hisinit Hcl] Hty]].
            rewrite OpAux.type_eqb_eq in Hty.
            rewrite Clocks.clock_eqb_eq in Hcl. subst.
            eapply Hvalids in Hin. apply Hin...
          }
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
             specialize (fby_init_stream_ite H b (fst cl) (sem_const (init_type ty)) y0 y z) as Hinit.
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
        assert (valid_after vars x1) as Hvalid1 by eauto.
        remember (Env.add x (init_stream H b (fst cl)) H) as H'.
        assert (Env.refines eq H H') as Href1 by (destruct Histst; eapply fresh_ident_refines in Hident; eauto).
        assert (hist_st vars b H' x1) as Histst1.
        { destruct Histst.
          constructor.
          + eapply fresh_ident_dom in Hident...
          + unfold init_eqs_valids in *.
            erewrite fresh_ident_anns...
            constructor...
            * intros _.
              rewrite HeqH'. econstructor. eapply Env.add_1; reflexivity.
              admit. (* init_stream only uses whats in cl, which is not changed in H' *)
            * solve_forall. destruct a as [? [[? ?] ?]].
              intuition. admit. (* init_stream only uses whats in cl, which is not changed in H' *)
        }
        assert (valid_after vars st') as Hvalid2 by eauto.
        remember (interp_clock H b (fst cl)) as b'.
        remember (prefix_with_val b' (Op.sem_const (Op.init_type ty)) y) as y'.
        remember (Env.add x2 y' H') as H''.
        assert (Env.refines eq H' H'') as Href2 by (destruct Histst1; eapply fresh_ident_refines in H1; eauto).
        assert (hist_st vars b H'' st') as Histst2 by (rewrite HeqH''; eauto).
        assert (~Env.E.eq x2 x) as Hneq.
        { intro contra. eapply Facts.fresh_ident_In in Hident.
          assert (In x (st_ids x1)).
          { unfold st_ids, idty. rewrite in_map_iff. exists (x, (Op.bool_type, (fst cl), true)); eauto. }
          eapply Facts.fresh_ident_nIn in H1. 2:(destruct Hvalid1; eauto).
          rewrite contra in H1. congruence. }
        exists H''. repeat (split; eauto)...
        * etransitivity...
        * eapply Site with (s:=(init_stream H b (fst cl))) (ts:=[[y0]]) (fs:=[[y']]).
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
          -- apply Seq with (ss:=[[init_stream H b (fst cl)]]); simpl.
             ++ repeat constructor. admit.
             ++ repeat constructor. econstructor; [| reflexivity].
                rewrite HeqH''. rewrite HeqH'.
                eapply Env.add_2... eapply Env.add_1. reflexivity.
  Admitted.

  Fact normalize_fby_sem {B} : forall G (vars : list (ident * B)) b anns H e0s es s0s ss vs es' eqs' st st',
      length e0s = length anns ->
      length es = length anns ->
      Forall2 (fun e v => sem_exp G H b e [v]) e0s s0s ->
      Forall2 (fun e v => sem_exp G H b e [v]) es ss ->
      Forall3 fby s0s ss vs ->
      valid_after vars st ->
      hist_st vars b H st ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          valid_after vars st' /\
          hist_st vars b H' st' /\
          Forall2 (fun e v => sem_exp G H' b e [v]) es' vs /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction anns; intros H e0s es s0s ss vs es' eqs' st st' Hlen1 Hlen2 Hsem1 Hsem2 Hfby Hvalid Histst Hnorm;
      unfold normalize_fby in Hnorm; repeat inv_bind.
    - destruct e0s; simpl in *; try congruence.
      destruct es; simpl in *; try congruence.
      repeat inv_bind. inv Hsem1. inv Hsem2. inv Hfby.
      exists H. repeat (split; eauto); simpl...
    - destruct e0s; simpl in *; try congruence.
      destruct es; simpl in *; try congruence.
      repeat inv_bind.
      inv Hlen1. inv Hlen2. inv Hsem1. inv Hsem2. inv Hfby.
      destruct a as [ty cl].
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

  Hint Constructors sem_exp.
  Fact normalize_exp_sem : forall G vars b e H vs is_control es' eqs' st st',
      wt_exp G vars e ->
      sem_exp G H b e vs ->
      valid_after vars st ->
      hist_st vars b H st ->
      normalize_exp is_control e st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          valid_after vars st' /\
          hist_st vars b H' st' /\
          Forall2 (fun e v => sem_exp G H' b e [v]) es' vs /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction e using exp_ind2; intros Hi vs is_control es' eqs' st st' Hwt Hsem Hvalid Histst Hnorm;
      inv Hwt; inv Hsem; simpl in Hnorm; repeat inv_bind.
    - (* const *)
      exists Hi. repeat (split; eauto).
    - (* var *)
      exists Hi. repeat (split; eauto).
    - (* unop *)
      specialize (Typ.normalize_exp_typeof _ _ _ _ _ _ _ _ H2 H) as Htypeof.
      specialize (IHe _ _ _ _ _ _ _ H2 H9 Hvalid Histst H). destruct IHe as [Hi' [Hvalid1 [Href1 [Hdom1 [Hsem1 Hsem1']]]]].
      assert (numstreams e = 1) by (rewrite <- length_typeof_numstreams; rewrite H3; reflexivity).
      eapply normalize_exp_length in H... rewrite H0 in H.
      repeat singleton_length. inv Hsem1. clear H10.
      exists Hi'.
      repeat (split; eauto).
      repeat econstructor... congruence.
    - (* binop *)
      specialize (Typ.normalize_exp_typeof _ _ _ _ _ _ _ _ H3 H) as Htypeof1.
      specialize (Typ.normalize_exp_typeof _ _ _ _ _ _ _ _ H4 H0) as Htypeof2.
      assert (numstreams e1 = 1) by (rewrite <- length_typeof_numstreams; rewrite H15; reflexivity).
      assert (numstreams e2 = 1) by (rewrite <- length_typeof_numstreams; rewrite H16; reflexivity).
      specialize (IHe1 _ _ _ _ _ _ _ H3 H10 Hvalid Histst H). destruct IHe1 as [Hi' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      eapply sem_exp_refines in H13; [| eauto].
      specialize (IHe2 _ _ _ _ _ _ _ H4 H13 Hvalid1 Histst1 H0). destruct IHe2 as [Hi'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]].
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
      assert (length (concat x2) = length (annots e0s)) as Hlength1 by (eapply map_bind2_normalize_exp_length; eauto).
      assert (length (concat x9) = length (annots es)) as Hlength2 by (eapply map_bind2_normalize_exp_length; eauto).
      eapply map_bind2_sem in H1... 2:(repeat rewrite_Forall_forall; eapply nth_In in H17; eauto). clear H.
      destruct H1 as [H' [Href1 [Histst1 [Hdom1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.
      assert (Forall2 (sem_exp G H' b) es sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
      eapply map_bind2_sem in H2... 2:(repeat rewrite_Forall_forall; eapply nth_In in H19; eauto). clear H0.
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
      assert (hist_st vars b H'''' st') as Histst4.
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
        destruct Hvalid3.
        apply idents_for_anns_NoDupMembers in H9...
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
              destruct Hvalid3.
              apply idents_for_anns_NoDupMembers in H9...
        -- solve_forall. repeat (eapply sem_equation_refines; eauto).
        -- solve_forall. repeat (eapply sem_equation_refines; eauto).
        -- solve_forall. eapply sem_equation_refines...
    - (* when *)
      assert (length (concat x1) = length (annots es)) as Hlength by (eapply map_bind2_normalize_exp_length; eauto).
      erewrite <- (map_length _ (annots es)) in Hlength. erewrite <- typesof_annots in Hlength.
      eapply map_bind2_sem in H0... 2: (repeat rewrite_Forall_forall; eapply nth_In in H8; eauto).
      destruct H0 as [H' [Hvalid1 [Href1 [Hdom1 [Hsem1 Hsem1']]]]].
      apply Forall2_concat in Hsem1.
      exists H'. repeat (split; simpl; eauto).
      rewrite Forall2_map_1.
      eapply Forall2_trans_ex in H13; [| eauto].
      apply Forall2_combine_lr with (zs:=(typesof es)) in H13; auto.
      eapply Forall2_impl_In; [| eauto].
      intros; simpl in H2. destruct a. destruct H2 as [y [Hin [Hsem Hsem']]].
      econstructor...
      + eapply sem_var_refines...
      + simpl. repeat constructor...
    - (* merge *)
      assert (length (concat ts) = length (annots ets)) as Hlength1 by (eapply sem_exps_numstreams; eauto).
      eapply map_bind2_sem in H1... 2:(repeat rewrite_Forall_forall; eapply nth_In in H17; eauto). clear H.
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
        assert (hist_st vars b H''' st') as Histst3.
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
          destruct Hvalid2.
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
                destruct Hvalid2.
                apply idents_for_anns_NoDupMembers in H...
          -- solve_forall. repeat (eapply sem_equation_refines; eauto).
          -- solve_forall. eapply sem_equation_refines...
             Unshelve. exact default_ann. exact s.
    - (* ite *)
      assert (length [s] = numstreams e) as Hlength1 by (eapply sem_exp_numstreams; eauto). simpl in Hlength1.
      assert (length x = numstreams e) as Hlength1' by (eapply normalize_exp_length; eauto).
      rewrite <- Hlength1 in Hlength1'. clear Hlength1.
      assert (length (concat ts) = length (annots ets)) as Hlength3 by (eapply sem_exps_numstreams; eauto).
      eapply IHe in H1... clear IHe. destruct H1 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      assert (Forall2 (sem_exp G H' b) ets ts) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
      eapply map_bind2_sem in H2... 2:(repeat rewrite_Forall_forall; eapply nth_In in H22; eauto). clear H.
      destruct H2 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
      assert (Forall2 (sem_exp G H'' b) efs fs) as Hsem'' by (repeat rewrite_Forall_forall; repeat (eapply sem_exp_refines; eauto)).
      eapply map_bind2_sem in H3... 2:(repeat rewrite_Forall_forall; eapply nth_In in H24; eauto). clear H0.
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
        assert (hist_st vars b H'''' st').
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
          destruct Hvalid3.
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
                destruct Hvalid3.
                apply idents_for_anns_NoDupMembers in H...
          -- solve_forall. repeat (eapply sem_equation_refines; eauto).
          -- solve_forall. eapply sem_equation_refines with (H:=H'')... etransitivity...
          -- solve_forall. eapply sem_equation_refines...
             Unshelve. exact default_ann. exact (hd_default []). 1,2:exact s.
    - (* app *)
      specialize (idents_for_anns_length _ _ _ _ H2) as Hlength1.
      assert (length (n_out n) = length vs) as Hlength2.
      { destruct H14. repeat rewrite_Forall_forall.
        rewrite H4 in H6. inv H6. unfold idents in *. solve_length. }
      eapply map_bind2_sem in H1... 2:(repeat rewrite_Forall_forall; eapply nth_In in H12; eauto). clear H0.
      destruct H1 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      remember (Env.adds (List.map fst x3) vs H') as H''.
      assert (Env.refines eq H' H'') as Href2.
      { destruct Histst1.
        eapply idents_for_anns_refines... repeat rewrite_Forall_forall; solve_length. }
      assert (hist_st vars b H'' st').
      { rewrite HeqH''. eapply idents_for_anns_hist_st in H2...
        repeat rewrite_Forall_forall. solve_length. }
      exists H''. repeat (split; eauto).
      + etransitivity...
      + rewrite Forall2_map_1.
        repeat rewrite_Forall_forall; solve_length.
        destruct (nth _ x3 _) eqn:Hnth.
        repeat constructor. econstructor; [|reflexivity].
        destruct a1. rewrite split_nth in Hnth; inv Hnth.
        rewrite split_map_fst.
        apply Env.adds_MapsTo; solve_length.
        rewrite <- fst_NoDupMembers.
        destruct Hvalid1.
        apply idents_for_anns_NoDupMembers in H2...
      + constructor.
        * apply Seq with (ss:=[vs]).
          -- repeat constructor.
             apply Sapp with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))).
             ++ apply Forall2_concat.
                repeat rewrite_Forall_forall; solve_length;
                  specialize (H3 a0 (List.map (fun _ => default_stream) b0) _ _ _ H13 eq_refl eq_refl);
                  repeat rewrite_Forall_forall; simpl_length.
                ** rewrite <- map_nth.
                   rewrite <- (map_nth (length (A:=_)) (List.map _ ss)). f_equal; solve_length.
                   repeat rewrite map_map.
                   apply map_ext_in. intros; solve_length.
                ** specialize (H16 a1 default_stream _ _ _ H15 eq_refl eq_refl).
                   repeat simpl_nth; [| eassumption].
                   eapply sem_exp_refines...
             ++ rewrite concat_map_singl2. assumption.
          -- simpl. rewrite app_nil_r.
             repeat rewrite_Forall_forall; solve_length.
             repeat constructor. econstructor; [| reflexivity].
             apply Env.adds_MapsTo; solve_length.
             rewrite <- fst_NoDupMembers.
             destruct Hvalid1.
             apply idents_for_anns_NoDupMembers in H2...
        * solve_forall.
          eapply sem_equation_refines...
    - (* app (reset) *)
      specialize (idents_for_anns_length _ _ _ _ H3) as Hlength1.
      assert (length (n_out n) = length vs) as Hlength3.
      { clear H H0 H1 H4. specialize (H19 0); inv H19; subst.
        repeat rewrite_Forall_forall.
        rewrite H0 in H6; inv H6. unfold idents in *. solve_length. }
      assert (length x2 = 1) as Hlength2.
      { eapply normalize_exp_length in H1... rewrite <- length_typeof_numstreams in H1.
        rewrite H1. rewrite H11. reflexivity. }
      repeat singleton_length; subst.
      eapply H in H1... clear H.
      destruct H1 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. inv Hsem1; inv H16.
      eapply normalize_reset_sem in H4... 2:(destruct Histst1; eauto).
      destruct H4 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]].
      assert (Forall2 (sem_exp G H'' b) es ss) as Hsem'.
      { repeat rewrite_Forall_forall.
        eapply sem_exp_refines; [| eauto]. etransitivity... } clear H15.
      eapply map_bind2_sem in H2... 2:(repeat rewrite_Forall_forall; eapply nth_In in H14; eauto). clear H0.
      destruct H2 as [H''' [Href3 [Hvalid3 [Histst3 [Hsem3 Hsem3']]]]].
      remember (Env.adds (List.map fst x5) vs H''') as H''''.
      assert (Env.refines eq H''' H'''') as Href4.
      { destruct Histst3. eapply idents_for_anns_refines...
        repeat rewrite_Forall_forall; solve_length. }
      assert (valid_after vars st') as Hvalid4 by eauto.
      assert (hist_st vars b H'''' st').
      { rewrite HeqH''''. eapply idents_for_anns_hist_st in H3...
        repeat rewrite_Forall_forall; solve_length. }
      exists H''''. repeat (split; auto).
      + repeat (etransitivity; eauto).
      + rewrite Forall2_map_1.
        repeat rewrite_Forall_forall; solve_length.
        destruct (nth _ x5 _) eqn:Hnth.
        repeat constructor. econstructor; [|reflexivity].
        destruct a1. rewrite split_nth in Hnth; inv Hnth.
        rewrite split_map_fst.
        apply Env.adds_MapsTo; solve_length.
        rewrite <- fst_NoDupMembers.
        destruct Hvalid3.
        apply idents_for_anns_NoDupMembers in H3...
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
                ** specialize (H20 a1 default_stream _ _ _ H16 eq_refl eq_refl).
                   repeat simpl_nth; [| eassumption].
                   eapply sem_exp_refines...
             ++ eapply sem_exp_refines; [| eauto]. etransitivity...
             ++ rewrite concat_map_singl2. assumption.
          -- simpl. rewrite app_nil_r.
             repeat rewrite_Forall_forall; solve_length.
             repeat constructor. econstructor; [| reflexivity].
             apply Env.adds_MapsTo; solve_length.
             rewrite <- fst_NoDupMembers.
             destruct Hvalid3.
             apply idents_for_anns_NoDupMembers in H3...
        * repeat rewrite Forall_app.
          repeat split; solve_forall; solve_length.
          1,2,3: (eapply sem_equation_refines; [| eauto]; repeat (etransitivity; eauto)).
  Qed.

  Corollary normalize_exps_sem : forall G vars b es H vs es' eqs' st st',
      Forall (wt_exp G vars) es ->
      Forall2 (sem_exp G H b) es vs ->
      valid_after vars st ->
      hist_st vars b H st ->
      map_bind2 (normalize_exp false) es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          valid_after vars st' /\
          hist_st vars b H' st' /\
          Forall2
            (fun (es : list exp) (vs : list (Stream OpAux.value)) =>
             Forall2 (fun e v => sem_exp G H' b e [v]) es vs) es' vs /\
          Forall (sem_equation G H' b) (concat eqs')).
  Proof.
    intros G vars b es H vs es' eqs' st st' Hwt Hsem Hvalid Hdom Hnorm.
    eapply map_bind2_sem in Hnorm; eauto.
    repeat rewrite_Forall_forall.
    specialize (nth_In _ a H2) as Hin.
    eapply normalize_exp_sem with (e:=(nth n es a)); eauto.
  Qed.

  Fact normalize_rhs_sem : forall G vars b keep_fby e H vs es' eqs' st st',
      wt_exp G vars e ->
      sem_exp G H b e vs ->
      valid_after vars st ->
      hist_st vars b H st ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          valid_after vars st' /\
          hist_st vars b H' st' /\
          (Forall2 (fun e v => sem_exp G H' b e [v]) es' vs \/
           exists e', (es' = [e'] /\ sem_exp G H' b e' vs)) /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros G vars b keep_fby e H vs es' eqs' st st' Hwt Hsem Hvalid Hhistst Hnorm.
    destruct e; try eapply normalize_exp_sem in Hnorm; eauto.
    1,2,3,4,6,7,8: (destruct Hnorm as [H' [Href1 [Hvalid1 [Hhistst1 [Hsem1 Hsem2]]]]];
                    exists H'; repeat (split; eauto)).
      1,2:(unfold normalize_rhs in Hnorm). destruct keep_fby. 1,2,3:(inv Hwt; inv Hsem).
    - (* fby (keep) *)
      repeat inv_bind.
      assert (length x = length (annots l)) as Hlength1 by (eapply normalize_exps_length; eauto).
      assert (length x2 = length (annots l0)) as Hlength2 by (eapply normalize_exps_length; eauto).
      unfold normalize_exps in *. repeat inv_bind.
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
    - (* app (reset) *)
      repeat inv_bind. unfold normalize_exps in H1; repeat inv_bind.
      assert (length x4 = 1) as Hlength2.
      { eapply normalize_exp_length in H0... rewrite <- length_typeof_numstreams in H0.
        rewrite H0. rewrite H10. reflexivity. }
      repeat singleton_length; subst.
      eapply normalize_exp_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. inv Hsem1; clear H15.
      eapply normalize_reset_sem in H2... 2:(destruct Histst1; auto).
      destruct H2 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]].
      assert (Forall2 (sem_exp G H'' b) l ss) as Hsem'.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines; [| eauto]. etransitivity... }
      eapply normalize_exps_sem in H1...
      destruct H1 as [H''' [Href3 [Hvalid3 [Histst3 [Hsem3 Hsem3']]]]].
      exists H'''. repeat (split; auto).
      + repeat (etransitivity; eauto).
      + right. eexists; split...
        apply Sreset with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))) (rs:=rs) (bs:=bs); eauto.
        * apply Forall2_concat.
          repeat rewrite_Forall_forall; solve_length;
            specialize (H1 a (List.map (fun _ => default_stream) b0) _ _ _ H19 eq_refl eq_refl);
            repeat rewrite_Forall_forall; simpl_length.
          -- rewrite <- map_nth.
             rewrite <- (map_nth (length (A:=_)) (List.map _ ss)). f_equal; solve_length.
             repeat rewrite map_map.
             apply map_ext_in. intros; solve_length.
          -- specialize (H21 a0 default_stream _ _ _ H20 eq_refl eq_refl).
             repeat simpl_nth; [| eassumption].
             eauto.
        * eapply sem_exp_refines...
        * rewrite concat_map_singl2. assumption.
      + repeat rewrite Forall_app.
        repeat split; solve_forall; (eapply sem_equation_refines; [| eauto]); eauto.
        etransitivity...
  Qed.

  Corollary map_bind2_normalize_rhs_sem : forall G vars b keep_fby es H vs es' eqs' st st',
      Forall (wt_exp G vars) es ->
      Forall2 (sem_exp G H b) es vs ->
      valid_after vars st ->
      hist_st vars b H st ->
      map_bind2 (normalize_rhs keep_fby) es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          valid_after vars st' /\
          hist_st vars b H' st' /\
          Forall2 (fun es' vs =>
                     Forall2 (fun e v => sem_exp G H' b e [v]) es' vs \/
                     exists e', (es' = [e'] /\ sem_exp G H' b e' vs)) es' vs /\
          Forall (sem_equation G H' b) (concat eqs')).
  Proof with eauto.
    induction es; intros H vs es' eqs' st st' Hwt Hsem Hvalid Histst Hmap;
      simpl in *; repeat inv_bind.
    - exists H; simpl. inv Hsem. repeat (split; auto).
    - inv Hwt. inv Hsem.
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

  Corollary normalize_rhss_sem : forall G vars b keep_fby es H vs es' eqs' st st',
      Forall (wt_exp G vars) es ->
      Forall2 (sem_exp G H b) es vs ->
      valid_after vars st ->
      hist_st vars b H st ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          valid_after vars st' /\
          hist_st vars b H' st' /\
          Forall (fun '(e, v) => sem_exp G H' b e v)
                 (combine_for_numstreams es' (concat vs)) /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros G vars b keep_fby es H vs es' eqs' st st' Hwt Hsem Hvalid Histst Hnorm.
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
      + rewrite firstn_app...
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

  Fact normalize_equation_sem : forall G vars H b to_cut equ eqs' st st',
      wt_equation G vars equ ->
      sem_equation G H b equ ->
      valid_after vars st ->
      hist_st vars b H st ->
      normalize_equation to_cut equ st = (eqs', st') ->
      (exists H', Env.refines eq H H' /\
             valid_after vars st' /\
             hist_st vars b H' st' /\
             Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros G vars H b to_cut equ eqs' st st' Hwt Hsem Hvalid Histst Hnorm.
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

  Corollary normalize_equations_sem : forall G vars b to_cut eqs H eqs' st st',
      Forall (wt_equation G vars) eqs ->
      Forall (sem_equation G H b) eqs ->
      valid_after vars st ->
      hist_st vars b H st ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      (exists H', Env.refines eq H H' /\
             Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction eqs; intros H eqs' st st' Hwt Hsem Hvalid Hdome Hnorm;
      inv Hwt; inv Hsem; simpl in Hnorm; repeat inv_bind.
    - exists H...
    - eapply normalize_equation_sem in H0...
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

  Fact init_st_valid_after {B} : forall n,
      valid_after (idty (n_in n++n_vars n++n_out n)) (@init_st B (first_unused_ident n)).
  Proof.
    intros n.
    constructor.
    - eapply init_st_valid.
    - unfold before_st.
      rewrite init_st_smallest.
      specialize (first_unused_ident_gt n _ eq_refl) as H.
      unfold used_idents in H.
      repeat rewrite_Forall_forall.
      apply H. apply in_or_app. right.
      unfold idty in H0; rewrite map_map in H0; simpl in H0.
      assumption.
  Qed.

  Fact init_st_hist_st : forall b H n,
      Env.dom H (List.map fst (n_in n++n_vars n++n_out n)) ->
      hist_st (idty (n_in n++n_vars n++n_out n)) b H (init_st (first_unused_ident n)).
  Proof.
    intros b H n Hdom.
    constructor.
    - unfold st_ids.
      rewrite init_st_anns; simpl. rewrite app_nil_r.
      unfold idty; rewrite map_map; simpl.
      assumption.
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
  Proof.
    intros G H n Hwl ins to_cut Hdom Hwt Hsem.
    eapply normalize_equations_sem with (st:=init_st (first_unused_ident n)) in Hsem.
    - destruct Hsem as [H' [Href Hsem]].
      exists H'; simpl; eauto.
    - eassumption.
    - apply init_st_valid_after.
    - apply init_st_hist_st; eauto.
    - rewrite <- surjective_pairing. reflexivity.
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
        eapply sem_var_restrict...
        unfold idents in *. erewrite map_nth'; [| solve_length].
        rewrite <- surjective_pairing.
        apply in_or_app. left. apply nth_In. solve_length.
        Unshelve. exact (xH, (Op.bool_type, Cbase)). } clear H1.
      assert (Forall2 (sem_var H') (idents (n_out n0)) outs) as Hout.
      { repeat rewrite_Forall_forall.
        eapply sem_var_restrict...
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
          { eapply Permutation_in in Hdef...
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
       (Norm : NORMALIZATION Ids Op OpAux Syn)
       <: CORRECTNESS Ids Op OpAux Str Syn Typ Clo Lord Sem Norm.
  Include CORRECTNESS Ids Op OpAux Str Syn Typ Clo Lord Sem Norm.
  Module Typing := NTypingFun Ids Op OpAux Syn Typ Norm.
  Module Clocking := NClockingFun Ids Op OpAux Syn Clo Norm.
  Module Ordered := NOrderedFun Ids Op OpAux Syn Lord Norm.
End CorrectnessFun.
