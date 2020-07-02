From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

Require Import Omega.

From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LCausality Lustre.LSemantics Lustre.LClockSemantics.
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
       (Import Ty : LTYPING Ids Op Syn)
       (Import Cl : LCLOCKING Ids Op Syn)
       (LCA        : LCAUSALITY Ids Op Syn)
       (Import Ord : LORDERED Ids Op Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Syn Ord Str)
       (Import LClockSem : LCLOCKSEMANTICS Ids Op OpAux Syn Ty Cl LCA Ord Str Sem)
       (Import Norm : FULLNORM Ids Op OpAux Syn).

  Import Fresh Tactics.
  Module Import Typ := NTypingFun Ids Op OpAux Syn Ty Norm.
  Module Import Clo := NClockingFun Ids Op OpAux Syn Cl Norm.
  Module Ord := NOrderedFun Ids Op OpAux Syn Ord Norm.
  Import List.

  CoFixpoint default_stream : Stream OpAux.value :=
    absent ⋅ default_stream.

  Fact normalize_exp_sem_length : forall G vars e is_control es' eqs' st st',
      wt_exp G (vars++Typ.st_tys st) e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (fun e => forall v H b,
                  sem_exp G H b e v ->
                  length v = 1) es'.
  Proof.
    intros G vars e is_control es' eqs' st st' Hwt Hnorm.
    specialize (normalize_exp_numstreams _ _ _ _ _ _ Hnorm) as Hnumstreams.
    specialize (normalize_exp_wt_exp _ _ _ _ _ _ _ _ Hwt Hnorm) as Hwt'.
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
      solve_forall; simpl.
      assert (In i (map fst ids)) by (simpl_In; exists (i, a); eauto).
      apply Hids in H2.
      intro contra.
      eapply st_valid_NoDup, NoDup_app_In in H0; [|eauto].
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

  Fact idents_for_anns'_nIn' : forall anns ids st st' aft reusable,
      NoDup (map fst (Syn.anon_streams anns) ++ PS.elements reusable) ->
      st_valid_reuse st aft (ps_adds (map fst (Syn.anon_streams anns)) reusable) ->
      idents_for_anns' anns st = (ids, st') ->
      Forall (fun id => ~In id (PSP.to_list aft++st_ids st)) (map fst ids).
  Proof.
    intros anns ids st st' aft reusable Hndup Hvalid Hids.
    eapply idents_for_anns'_st_valid in Hvalid; eauto.
    apply st_valid_reuse_st_valid, st_valid_NoDup in Hvalid.
    apply idents_for_anns'_vars_perm in Hids.
    unfold st_ids in *.
    rewrite <- Hids, Permutation_app_comm, Permutation_swap in Hvalid.
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

  Fact reuse_ident_refines {B V} : forall vars H H' a id (v : V) (st st' : fresh_st B) reusable,
      ~PS.In id reusable ->
      st_valid_reuse st (PSP.of_list vars) (PS.add id reusable) ->
      Env.dom H (vars++st_ids st) ->
      reuse_ident id a st = (tt, st') ->
      H' = Env.add id v H ->
      Env.refines eq H H'.
  Proof with eauto.
    intros * Hnin Hvalid Hdom Hreuse Heq.
    rewrite Heq.
    assert (st_valid_reuse st' (PSP.of_list vars) reusable) as Hvalid' by eauto.
    eapply Env.refines_add...
    intro contra. erewrite Env.dom_use in contra; [| eauto].
    apply in_app_or in contra. destruct contra.
    + eapply Facts.reuse_ident_In in Hreuse.
      assert (In id (st_ids st')).
      { unfold st_ids, idty. repeat simpl_In; simpl in *.
        exists (id, a); auto. }
      apply st_valid_reuse_st_valid, st_valid_NoDup in Hvalid'.
      eapply NoDup_app_In in Hvalid'; [|eauto].
      apply Hvalid'; clear Hvalid'.
      rewrite ps_of_list_ps_to_list...
    + eapply Facts.st_valid_reuse_nIn, PS_For_all_add in Hvalid as [? _]...
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
      solve_forall; simpl.
      assert (In i (map fst ids)) by (simpl_In; exists (i, (t, (c, o))); eauto).
      apply Hids in H2.
      intro contra.
      eapply st_valid_reuse_st_valid, st_valid_NoDup, NoDup_app_In in H0; [|eauto].
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

  Definition init_stream bs :=
    prefix_with_val bs true_val (Str.const bs false_const).

  Instance init_stream_Proper:
    Proper (@EqSt bool ==> @EqSt value) init_stream.
  Proof.
    intros bs bs' Heq.
    unfold init_stream. rewrite Heq. reflexivity.
  Qed.

  Lemma fby_ite : forall bs v y0s ys zs,
      (synchronized y0s bs \/ synchronized ys bs \/ synchronized zs bs) ->
      fby y0s ys zs ->
      ite (prefix_with_val bs true_val (const_val bs false_val)) y0s (prefix_with_val bs v ys) zs.
  Proof with eauto.
    cofix fby_init_stream_ite.
    intros [b bs] v y0s ys zs Hsync Hfby1.
    apply fby_synchronized in Hsync as [Hsync1 [Hsync2 Hsync3]]; [|auto].
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

  Corollary fby_init_stream_ite : forall bs v y0s ys zs,
      (synchronized y0s bs \/ synchronized ys bs \/ synchronized zs bs) ->
      fby y0s ys zs ->
      ite (init_stream bs) y0s (prefix_with_val bs v ys) zs.
  Proof.
    intros * Hsync Hfby1.
    eapply fby_ite in Hfby1; eauto.
    unfold init_stream.
    rewrite const_val_const. rewrite sem_false_const. eassumption.
  Qed.

  Lemma ac_shift : forall c vs,
      abstract_clock (shift c vs) ≡ abstract_clock vs.
  Proof.
    cofix CoFix. intros c [v vs].
    rewrite shift_Cons.
    destruct v; constructor; simpl; auto.
  Qed.

  Lemma ac_prefix_with_val : forall bs vs c,
      abstract_clock vs ≡ bs ->
      abstract_clock (prefix_with_val bs c vs) ≡ bs.
  Proof.
    cofix CoFix.
    intros [b bs] [v vs] c Hsync.
    rewrite prefix_with_val_Cons.
    destruct b; simpl.
    - rewrite ac_shift; auto.
    - constructor; simpl; auto.
      apply CoFix. inv Hsync; destruct v; simpl in *; auto.
  Qed.

  Lemma init_stream_ac : forall bs,
      abstract_clock (init_stream bs) ≡ bs.
  Proof.
    intros bs.
    unfold init_stream.
    apply ac_prefix_with_val.
    symmetry. eapply ac_const. reflexivity.
  Qed.

  Definition init_eqs_valids bs H (st : fresh_st (Op.type * clock * bool)) :=
    Forall (fun '(id, (_, ck, is_init)) =>
              is_init = true ->
              (exists bs', sem_clock H bs ck bs' /\
                      sem_var H id (init_stream bs'))) (st_anns st).

  Definition hist_st (vars : list (ident * clock)) b H st :=
    Env.dom H (map fst vars++st_ids st) /\
    init_eqs_valids b H st /\
    sc_var_inv' (vars++st_clocks st) H b.

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

  Fact fresh_ident_init_eqs : forall vars b ty ck id v H st st',
      st_valid_after st (PSP.of_list vars) ->
      Env.dom H (vars ++ st_ids st) ->
      fresh_ident ((ty, ck), false) st = (id, st') ->
      init_eqs_valids b H st ->
      init_eqs_valids b (Env.add id v H) st'.
  Proof with auto.
    intros * Hvalid Hdom Hfresh Hinits.
    assert (~In id (st_ids st)) as Hnin by (eapply Facts.fresh_ident_nIn in Hfresh; eauto).
    assert (st_valid_after st' (PSP.of_list vars)) as Hvalid2 by eauto.
    assert (Hfresh':=Hfresh). apply fresh_ident_anns in Hfresh'.
    assert (Env.refines eq H (Env.add id v H)) as Href.
    { eapply fresh_ident_refines in Hfresh; eauto. }
    unfold init_eqs_valids in *.
    eapply fresh_ident_anns in Hfresh.
    rewrite Hfresh.
    constructor...
    - intros. congruence.
    - solve_forall.
      intros Htrue. specialize (H1 Htrue) as [bs' [Hvar Hclock]].
      exists bs'. split; [eapply sem_clock_refines|eapply sem_var_refines]; eauto.
  Qed.

  Fact fresh_ident_hist_st : forall vars b ty ck id v H st st',
      st_valid_after st (PSP.of_list (map fst vars)) ->
      sem_clock H b ck (abstract_clock v) ->
      fresh_ident ((ty, ck), false) st = (id, st') ->
      hist_st vars b H st ->
      hist_st vars b (Env.add id v H) st'.
  Proof with auto.
    intros * Hvalid Hsem Hfresh [H1 [H2 H3]].
    assert (~In id (st_ids st)) as Hnin by (eapply Facts.fresh_ident_nIn in Hfresh; eauto).
    assert (st_valid_after st' (PSP.of_list (map fst vars))) as Hvalid2 by eauto.
    assert (Hfresh':=Hfresh). apply fresh_ident_anns in Hfresh'.
    assert (Env.refines eq H (Env.add id v H)) as Href.
    { eapply fresh_ident_refines in Hfresh; eauto. }
    repeat split.
    - eapply fresh_ident_dom; eauto.
    - eapply fresh_ident_init_eqs in Hfresh; eassumption.
    - unfold st_clocks, sc_var_inv' in *.
      rewrite Hfresh'; simpl.
      rewrite <- Permutation_middle. constructor.
      + exists v; split.
        * econstructor. eapply Env.add_1. 1,2:reflexivity.
        * eapply sem_clock_refines; eauto.
      + eapply sc_var_inv'_refines with (H:=H); eauto.
  Qed.

  Fact idents_for_anns_hist_st : forall vars b anns ids vs H st st',
      length vs = length ids ->
      st_valid_after st (PSP.of_list (map fst vars)) ->
      Forall2 (fun '(ty, (ck, _)) vs => sem_clock H b ck (abstract_clock vs)) anns vs ->
      idents_for_anns anns st = (ids, st') ->
      hist_st vars b H st ->
      hist_st vars b (Env.adds (List.map fst ids) vs H) st'.
  Proof with eauto.
    intros * Hlen Hvalid Hsem Hids Hist.
    constructor.
    - destruct Hist.
      eapply idents_for_anns_dom in Hids...
    - revert ids vs H st st' Hlen Hvalid Hsem Hids Hist.
      induction anns; intros; repeat inv_bind; simpl.
      + unfold Env.adds; simpl. destruct Hist. assumption.
      + destruct a as [? [? ?]]. repeat inv_bind.
        destruct vs; simpl in Hlen; try congruence.
        assert (Env.refines eq H (Env.add x s H)) as Href.
        { destruct Hist. eapply fresh_ident_refines in H0; eauto. }
        inv Hsem.
        unfold Env.adds; simpl.
        assert (st_valid_after x0 (PSP.of_list (map fst vars))) by eauto.
        eapply fresh_ident_hist_st in H0...
        eapply IHanns in H1...
        eapply Forall2_impl_In; eauto.
        intros [? [? ?]] ? ? ? ?. eapply sem_clock_refines; eauto.
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

  Fact reuse_ident_init_eqs : forall vars b a id v H st st' reusable,
      ~PS.In id reusable ->
      st_valid_reuse st (PSP.of_list vars) (PS.add id reusable) ->
      Env.dom H (vars ++ st_ids st) ->
      reuse_ident id (a, false) st = (tt, st') ->
      init_eqs_valids b H st ->
      init_eqs_valids b (Env.add id v H) st'.
  Proof with auto.
    intros * Hin Hvalid Hdom Hfresh Hinit.
    assert (Env.refines eq H (Env.add id v H)) as Href.
    { eapply reuse_ident_refines; eauto. }
    unfold init_eqs_valids in *.
    assert (st_valid_reuse st' (PSP.of_list vars) reusable) as Hvalid2 by eauto.
    eapply reuse_ident_anns in Hfresh.
    rewrite Hfresh.
    constructor...
    - destruct a. intros. congruence.
    - solve_forall. intro Htrue.
      specialize (H1 Htrue) as [bs' [Hdep His]].
      exists bs'. split; [eapply sem_clock_refines|eapply sem_var_refines]; eauto.
  Qed.

  Fact idents_for_anns'_hist_st : forall vars b anns ids vs H st st' reusable,
      length vs = length ids ->
      NoDup (map fst (Syn.anon_streams anns) ++ PS.elements reusable) ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (Syn.anon_streams anns)) reusable) ->
      Forall2 (fun '(_, (ck, _)) v => sem_clock (Env.adds (List.map fst ids) vs H) b ck (abstract_clock v)) anns vs ->
      idents_for_anns' anns st = (ids, st') ->
      hist_st vars b H st ->
      hist_st vars b (Env.adds (List.map fst ids) vs H) st'.
  Proof with eauto.
    intros * Hlen Hndup Hvalid Hclocks Hids Hist.
    repeat constructor.
    - destruct Hist as [? _].
      eapply idents_for_anns'_dom in Hids...
    - destruct Hist as [Hdom [Hinits _]].
      clear Hclocks. revert ids vs H st st' Hlen Hvalid Hids Hdom Hinits.
      induction anns; intros; repeat inv_bind; simpl.
      + unfold Env.adds; auto.
      + destruct a as [? [? [o|]]]; repeat inv_bind;
          destruct vs; simpl in Hlen; try congruence;
            unfold Env.adds; simpl in *.
        * rewrite <- ps_add_adds_eq in Hvalid. destruct x.
          assert (~ PS.In o (ps_adds (map fst (Syn.anon_streams anns)) reusable)) as Hnin.
          { apply NoDup_cons' in Hndup; destruct Hndup as [Hnin Hndup].
            intro contra; apply Hnin.
            rewrite <- In_PS_elements, Permutation_PS_elements_ps_adds' in contra... }
          assert (st_valid_reuse x0 (PSP.of_list (map fst vars)) (ps_adds (map fst (Syn.anon_streams anns)) reusable)).
          { eapply reuse_ident_st_valid_reuse in H0... }
          assert (H0':=H0). eapply reuse_ident_init_eqs in H0...
          eapply IHanns in H1... 2:eapply reuse_ident_dom in H0'...
          rewrite cons_is_app in Hndup; ndup_r Hndup.
        * assert (st_valid_reuse x0 (PSP.of_list (map fst vars)) (ps_adds (map fst (Syn.anon_streams anns)) reusable)) by eauto.
          assert (H0':=H0). eapply fresh_ident_init_eqs with (v:=s) in H0...
          eapply IHanns...
          eapply fresh_ident_dom in H0'...
    - destruct Hist as [Hdom [_ Hinv]].
      assert (Env.refines eq H (Env.adds (map fst ids) vs H)) as Href.
      { eapply idents_for_anns'_refines in Hids... }
      assert (NoDup (map fst ids)) as Hndup'.
      { eapply idents_for_anns'_NoDupMembers in Hids... rewrite <- fst_NoDupMembers... }
      unfold st_clocks, sc_var_inv' in *.
      assert (Hids':=Hids). eapply idents_for_anns'_st_anns in Hids'. rewrite Hids', idck_app, Permutation_swap.
      apply Forall_app; split.
      + assert (Forall
                  (fun x =>
                     exists v : Stream value,
                       In v vs /\
                       (sem_var (Env.adds (map fst ids) vs H) (fst x) v /\
                        sem_clock (Env.adds (map fst ids) vs H) b (snd x) (abstract_clock v)))
                  (idck (map (fun '(id, (ty, (cl, _))) => (id, (ty, cl))) ids))).
        2:{ solve_forall. destruct H1 as [? [? [? ?]]]. exists x; auto. }
        eapply Forall2_ignore2.
        eapply idents_for_anns'_values in Hids; rewrite <- Hids in Hclocks.
        unfold idck. simpl_forall. clear Hinv.
        repeat rewrite_Forall_forall.
        * destruct nth eqn:Hnth; destruct_conjs; simpl in *.
          econstructor; [|reflexivity].
          rewrite split_nth in Hnth; inv Hnth. rewrite split_map_fst.
          eapply Env.adds_MapsTo... 1,2:rewrite map_length; congruence.
        * destruct nth eqn:Hnth; destruct_conjs; simpl in *.
          specialize (H1 (p0, (t0, (c0, o0))) b0 _ _ _ H2 Hnth eq_refl); auto.
      + solve_forall. destruct H1 as [ss [Hvar Hclock]].
        exists ss. split; [eapply sem_var_refines|eapply sem_clock_refines]...
  Qed.

  (** ** Conservation of sem_exp *)

  Definition st_vars (st : fresh_st (type * clock * bool)) : list (ident * (type * clock)) :=
    idty (st_anns st).

  Fact st_ids_st_vars : forall st,
      st_ids st = map fst (st_vars st).
  Proof.
    intros. unfold st_ids, st_vars, idty.
    rewrite map_map; simpl.
    apply map_ext. intros [? [[? ?] ?]]; auto.
  Qed.

  Fact st_tys_st_vars : forall st,
      st_tys st = idty (st_vars st).
  Proof.
    intros. unfold st_tys, st_vars, idty.
    repeat rewrite map_map.
    apply map_ext. intros [? [[? ?] ?]]; auto.
  Qed.

  Fact st_clocks_st_vars : forall st,
      st_clocks st = idck (st_vars st).
  Proof.
    intros. unfold st_clocks, idck, st_vars, idty.
    repeat rewrite map_map.
    apply map_ext. intros [? [[? ?] ?]]; auto.
  Qed.

  Fact sc_normalized_lexp :  forall G H bs env e s ck,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers env ->
      wc_env (idck env) ->
      sc_var_inv' (idck env) H bs ->
      normalized_lexp e ->
      clockof e = [ck] ->
      wt_exp G (idty env) e ->
      wc_exp G (idck env) e ->
      sem_exp G H bs e [s] ->
      sem_clock H bs ck (abstract_clock s).
  Proof.
    intros * ? ? ? ? ? Hnormed Hck ? ? Hsem.
    eapply sc_exp' in Hsem; simpl in *; eauto.
    2: { eapply normalized_lexp_no_fresh in Hnormed.
         rewrite Hnormed, app_nil_r; auto. }
    rewrite Hck in Hsem.
    inv Hnormed; inv Hsem; auto.
  Qed.

  Fact st_valid_reuse_NoDupMembers : forall st vars reusable,
      NoDupMembers vars ->
      st_valid_reuse st (PSP.of_list (map fst vars)) reusable ->
      NoDupMembers (vars++st_vars st).
  Proof.
    intros * Hndup Hvalid.
    eapply st_valid_reuse_st_valid, st_valid_NoDup in Hvalid.
    rewrite ps_of_list_ps_to_list_Perm in Hvalid. 2:rewrite <- fst_NoDupMembers; auto.
    rewrite Permutation_app_comm, st_ids_st_vars, <- map_app, <- fst_NoDupMembers in Hvalid; auto.
  Qed.

  Fact st_valid_reuse_NoDupMembers' : forall st vars reu reusable,
      NoDupMembers vars ->
      NoDup (map fst reu ++ PS.elements reusable) ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst reu) reusable) ->
      NoDupMembers (vars++st_vars st++reu).
  Proof with eauto.
    intros * Hndup1 Hndup2 Hvalid.
    eapply st_valid_reuse_NoDup in Hvalid.
    rewrite ps_of_list_ps_to_list_Perm in Hvalid. 2:rewrite <- fst_NoDupMembers; auto.
    rewrite Permutation_PS_elements_ps_adds' in Hvalid...
    rewrite Permutation_swap, fst_NoDupMembers, map_app, map_app. repeat rewrite app_assoc in *.
    apply NoDup_app_l in Hvalid. rewrite st_ids_st_vars in Hvalid; auto.
  Qed.

  Fact normalize_reset_sem : forall G (vars : list (ident * (type * clock))) b e H v e' eqs' st st' reusable,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      wc_env (idck vars++st_clocks st) ->
      normalized_lexp e ->
      wt_exp G (idty vars++st_tys st) e ->
      wc_exp G (idck vars++st_clocks st) e ->
      sem_exp G H b e [v] ->
      st_valid_reuse st (PSP.of_list (map fst vars)) reusable ->
      hist_st (idck vars) b H st ->
      normalize_reset e st = (e', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (idck vars) b H' st' /\
          sem_exp G H' b e' [v] /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros * HwcG Hsc Hndup Hwenv Hnormed Hwt Hwc Hsem Hvalid Histst Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind.
    - exists H. repeat (split; auto).
    - destruct (List.hd _ _) as [? [? ?]] eqn:Heqann; repeat inv_bind.
      assert (st_follows st st') as Hfollows by eauto.
      assert (st_valid_after st (PSP.of_list (map fst vars))) as Hvalid' by eauto.
      remember (Env.add x v H) as H'.
      assert (hist_st (idck vars) b H' st').
      { subst. eapply fresh_ident_hist_st in H0; eauto. rewrite map_fst_idck; eauto.
        eapply sc_normalized_lexp with (env:=vars++_) in Hsem; eauto.
        5:rewrite idty_app; eauto. 2,5:rewrite idck_app; eauto.
        - eapply st_valid_reuse_NoDupMembers...
        - destruct Histst as [_ [_ ?]]. rewrite idck_app...
        - apply normalized_lexp_numstreams in Hnormed.
          rewrite <- length_annot_numstreams in Hnormed. singleton_length.
          rewrite clockof_annot, Hsingl...
        }
      assert (Env.refines eq H H') as Href.
      { eapply fresh_ident_refines with (st0:=st)...
        destruct Histst; rewrite map_fst_idck in H2... }
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

  (* Fact wt_clock_only_depends_on : forall vars ck, *)
  (*     wt_clock vars ck -> *)
  (*     only_depends_on (map fst vars) ck. *)
  (* Proof. *)
  (*   intros * Hwc. *)
  (*   induction Hwc; intros id Hisin; inv Hisin. *)
  (*   - simpl_In. exists (x, bool_type); auto. *)
  (*   - apply IHHwc; auto. *)
  (* Qed. *)

  Fact sem_clock_when : forall H bs bs' bs'' cs ck id ckb c,
      sem_clock H bs ck bs' ->
      sem_clock H bs (Con ck id ckb) bs'' ->
      sem_var H id cs ->
      when ckb (const bs' c) cs (const bs'' c).
  Proof.
    intros * Hcl1 Hcl2 Hvar.
    rewrite when_spec. intros n.
    apply sem_clock_sem_clock_instant with (n:=n) in Hcl1.
    apply sem_clock_sem_clock_instant with (n:=n) in Hcl2.
    rewrite sem_var_sem_var_instant in Hvar. specialize (Hvar n).
    inv Hcl2; (eapply sem_var_instant_det in Hvar; eauto;
               eapply sem_clock_instant_det in Hcl1; eauto).
    - right. right.
      exists (sem_const c). exists c0. repeat split; auto using const_true.
    - left.
      repeat split; auto using const_false.
    - right. left.
      exists (sem_const c). exists c0. repeat split; auto using const_true, const_false.
      destruct k; auto.
  Qed.

  Lemma add_whens_sem_exp : forall G H b ck ty b' c,
      sem_clock H b ck b' ->
      sem_exp G H b (add_whens (Econst c) ty ck) [const b' c].
  Proof.
    induction ck; intros * Hsem; assert (Hsem':=Hsem); inv Hsem'; simpl.
    constructor. rewrite H1; reflexivity.
    1,2,3: (eapply Swhen; eauto; simpl;
            repeat constructor;
            eapply sem_clock_when; eauto).
  Qed.

  Fact init_var_for_clock_sem : forall G vars bs H ck bs' x eqs' st st' reusable,
      sem_clock H bs ck bs' ->
      st_valid_reuse st (PSP.of_list (map fst vars)) reusable ->
      hist_st vars bs H st ->
      init_var_for_clock ck st = (x, eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st vars bs H' st' /\
          sem_var H' x (init_stream bs') /\
          Forall (sem_equation G H' bs) eqs').
  Proof with eauto.
    intros * Hsemc Hvalid Histst Hinit.
    unfold init_var_for_clock in Hinit.
    destruct find eqn:Hfind.
    - (* We already introduced such an equation previously.
         We will use the hist_st invariant to get some information back about it *)
      destruct p; inv Hinit.
      exists H. repeat (split; eauto).
      destruct Histst as [_ Hvalids]. unfold init_eqs_valids in Hvalids.
      rewrite Forall_forall in Hvalids.
      eapply find_some in Hfind. destruct p as [[ty' ck'] isinit].
      repeat rewrite Bool.andb_true_iff in Hfind. destruct Hfind as [Hin [[Hisinit Hcl] Hty]].
      rewrite OpAux.type_eqb_eq in Hty.
      rewrite Clocks.clock_eqb_eq in Hcl. subst.
      apply Hvalids in Hin. specialize (Hin eq_refl) as [bs'' [Hsemc' Hsemcv]].
      eapply sem_clock_det in Hsemc; eauto. rewrite <- Hsemc; auto.
    - (* We need to introduce a new init equation to the history and state,
         and prove its properties *)
      clear Hfind.
      destruct (fresh_ident _ _) eqn:Hident. repeat inv_bind.
      assert (st_valid_reuse st' (PSP.of_list (map fst vars)) reusable) as Hvalid1 by eauto.
      remember (Env.add x (init_stream bs') H) as H'.
      assert (Env.refines eq H H') as Href1 by (destruct Histst; eapply fresh_ident_refines in Hident; eauto).
      assert (hist_st vars bs H' st') as Histst1.
      { destruct Histst as [H1 [H2 H3]].
        repeat split.
        - eapply fresh_ident_dom in Hident...
        - unfold init_eqs_valids in *.
          erewrite fresh_ident_anns...
          constructor; [intros _|].
          + exists bs'. split; [eapply sem_clock_refines|]; eauto.
            rewrite HeqH'. econstructor. eapply Env.add_1.
            1,2:reflexivity.
          + eapply Forall_impl_In; [|eauto].
            intros [? [[? ?] ?]] Hin Hex Heq; subst.
            specialize (Hex eq_refl) as [bs'' [Hdep' Hsem']].
            exists bs''. split; [eapply sem_clock_refines|eapply sem_var_refines]; eauto.
        - unfold st_clocks, sc_var_inv' in *.
          erewrite fresh_ident_anns; simpl; eauto.
          rewrite <- Permutation_middle; constructor; simpl.
          + exists (init_stream bs'). split.
            * rewrite HeqH'. econstructor.
              eapply Env.add_1. 1,2:reflexivity.
            * rewrite init_stream_ac.
              eapply sem_clock_refines; eauto.
          + eapply Forall_impl; eauto. intros [? ?] [ss [? ?]].
            exists ss. split; [eapply sem_var_refines|eapply sem_clock_refines]; eauto.
      }
      assert (st_valid_reuse st' (PSP.of_list (map fst vars)) reusable) as Hvalid2 by eauto.
      exists H'. repeat (split; eauto).
      + rewrite HeqH'. econstructor. 2:reflexivity.
        apply Env.add_1. reflexivity.
      + repeat constructor.
        apply Seq with (ss:=[[(init_stream bs')]]); simpl; repeat constructor.
        * eapply Sfby with (s0ss:=[[(const bs' true_const)]]) (sss:=[[(const bs' false_const)]]); repeat constructor.
          -- apply add_whens_sem_exp. eauto using sem_clock_refines.
          -- apply add_whens_sem_exp. eauto using sem_clock_refines.
          -- unfold init_stream.
             repeat rewrite const_val_const; subst.
             rewrite <- sem_true_const. apply prefix_with_val_fby.
             rewrite <- const_val_const. apply const_synchronized.
        * econstructor. 2:reflexivity.
          rewrite HeqH'. apply Env.add_1. reflexivity.
  Qed.

  Fact fby_iteexp_sem : forall G vars bs H e0 e ty nck y0 y z e' eqs' st st' reusable,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      wc_env (idck vars++st_clocks st) ->
      normalized_lexp e0 ->
      clockof e0 = [fst nck] ->
      wt_exp G (idty vars++st_tys st) e0 ->
      wc_exp G (idck vars++st_clocks st) e0 ->
      sem_exp G H bs e0 [y0] ->
      sem_exp G H bs e [y] ->
      fby y0 y z ->
      st_valid_reuse st (PSP.of_list (map fst vars)) reusable ->
      hist_st (idck vars) bs H st ->
      fby_iteexp e0 e (ty, nck) st = (e', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (idck vars) bs H' st' /\
          sem_exp G H' bs e' [z] /\
          Forall (sem_equation G H' bs) eqs').
  Proof with eauto.
    intros * HwcG Hsc Hndup Hwenv Hnormed Hck Hwt Hwc Hsem0 Hsem Hfby Hvalid Histst Hiteexp.
    destruct nck as [ck ?]; simpl in *.
    unfold fby_iteexp in Hiteexp.
    destruct (Norm.is_constant e0); repeat inv_bind.
    - (* e0 is a constant, no equation is introduced *)
      exists H. repeat (split; eauto).
      repeat (econstructor; eauto).
    - (* e0 is not a constant, we have to introduce an ite equation and (maybe) an init equation *)
      eapply sc_normalized_lexp with (env:=vars++st_vars st) in Hnormed...
      3,6:rewrite idck_app... 4:rewrite idty_app...
      2:eapply st_valid_reuse_NoDupMembers...
      2:{ destruct Histst as [_ [_ ?]]. rewrite idck_app, <- st_clocks_st_vars; auto. }
      eapply init_var_for_clock_sem with (G:=G) in H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]...
      2: rewrite map_fst_idck...
      remember (abstract_clock y0) as bs'.
      remember (prefix_with_val bs' (Op.sem_const (Op.init_type ty)) y) as y'.
      remember (Env.add x2 y' H') as H''.
      assert (Env.refines eq H' H'') by (destruct Histst1; eapply fresh_ident_refines in H1; eauto).
      assert (hist_st (idck vars) bs H'' st') as Histst2.
      { eapply fresh_ident_hist_st in H1; eauto.
        rewrite HeqH''...
        rewrite Heqy', ac_prefix_with_val.
        1: eapply sem_clock_refines; eauto.
        rewrite Heqbs', ac_fby2; eauto.
        symmetry. eapply ac_fby1; eauto. }
      exists H''. repeat (split; eauto); try constructor.
      + etransitivity; eauto.
      + rewrite map_fst_idck in Hvalid1...
      + eapply Site with (s:=(init_stream bs')) (ts:=[[y0]]) (fs:=[[y']]); repeat constructor.
        * eapply sem_var_refines...
        * eapply sem_exp_refines; [| eauto]. etransitivity...
        * econstructor.
          rewrite HeqH''. eapply Env.add_1. 1,2:reflexivity.
        * subst. eapply fby_init_stream_ite...
          left. apply ac_synchronized.
      + apply Seq with (ss:=[[y']]); repeat constructor.
        * eapply Sfby with (s0ss:=[[const bs' (init_type ty)]]) (sss:=[[y]]); repeat constructor.
          -- eapply add_whens_sem_exp...
             eapply sem_clock_refines; [|eauto]. etransitivity...
          -- eapply sem_exp_refines; [| eauto]. etransitivity...
          -- rewrite Heqy'.
             rewrite const_val_const.
             eapply prefix_with_val_fby.
             eapply fby_synchronized in Hfby as [_ [? _]]; eauto.
             left. rewrite Heqbs'. apply ac_synchronized.
        * econstructor.
          rewrite HeqH''. apply Env.add_1. 1,2:reflexivity.
      + solve_forall. eapply sem_equation_refines...
  Qed.

  Fact st_follows_vars_incl : forall st st',
      st_follows st st' ->
      incl (st_vars st) (st_vars st').
  Proof.
    intros.
    unfold st_vars. apply incl_map, st_follows_incl, H.
  Qed.

  Ltac solve_incl :=
    repeat unfold idty; repeat unfold idck;
    match goal with
    | H : wt_nclock ?l1 ?ck |- wt_nclock ?l2 ?ck =>
      eapply wt_nclock_incl; [| eauto]
    | H : wc_clock ?l1 ?ck |- wc_clock ?l2 ?ck =>
      eapply wc_clock_incl; [| eauto]
    | H : wt_exp ?G ?l1 ?e |- wt_exp ?G ?l2 ?e =>
      eapply wt_exp_incl; [| eauto]
    | H : wc_exp ?G ?l1 ?e |- wc_exp ?G ?l2 ?e =>
      eapply wc_exp_incl; [| eauto]
    | H : wt_equation ?G ?l1 ?eq |- wt_equation ?G ?l2 ?eq =>
      eapply wt_equation_incl; [| eauto]
    | H : wc_equation ?G ?l1 ?eq |- wc_equation ?G ?l2 ?eq =>
      eapply wc_equation_incl; [| eauto]
    | |- incl ?l1 ?l1 => reflexivity
    | |- incl (map ?f ?l1) (map ?f ?l2) => eapply incl_map
    | |- incl ?l1 (?l1 ++ ?l2) =>
      eapply incl_appl; reflexivity
    | |- incl (?l1 ++ ?l2) (?l1 ++ ?l3) =>
      eapply incl_app
    | |- incl ?l1 (?l2 ++ ?l3) =>
      eapply incl_appr
    | |- incl ?l1 (?a::?l2) =>
      eapply incl_tl
    | |- incl (st_anns ?st1) (st_anns _) =>
      eapply st_follows_incl; repeat solve_st_follows
    | |- incl (st_vars ?st1) (st_vars _) =>
      eapply st_follows_vars_incl; repeat solve_st_follows
    | |- incl (st_tys ?st1) (st_tys _) =>
      eapply st_follows_tys_incl; repeat solve_st_follows
    | |- incl (st_clocks ?st1) (st_clocks _) =>
      eapply st_follows_clocks_incl; repeat solve_st_follows
    end; auto.

  Fact normalize_fby_sem : forall G vars b anns H e0s es s0s ss vs es' eqs' st st' reusable,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      wc_env (idck vars++st_clocks st) ->
      Forall normalized_lexp e0s ->
      Forall (wt_exp G (idty vars++st_tys st)) e0s ->
      Forall (wc_exp G (idck vars++st_clocks st)) e0s ->
      Forall (fun '(_, (ck, _)) => wc_clock (idck vars++st_clocks st) ck) anns ->
      Forall2 (fun e0 '(_, (ck, _)) => clockof e0 = [ck]) e0s anns ->
      length es = length anns ->
      Forall2 (fun e v => sem_exp G H b e [v]) e0s s0s ->
      Forall2 (fun e v => sem_exp G H b e [v]) es ss ->
      Forall3 fby s0s ss vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) reusable ->
      hist_st (idck vars) b H st ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (idck vars) b H' st' /\
          Forall2 (fun e v => sem_exp G H' b e [v]) es' vs /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction anns; intros * HwcG Hsc Hndup Hwenv Hnormed Hwt Hwc Hwck Hanns Hlen2 Hsem1 Hsem2 Hfby Hvalid Histst Hnorm;
      unfold normalize_fby in Hnorm; repeat inv_bind.
    - inv Hanns.
      destruct es; simpl in *; try congruence.
      repeat inv_bind. inv Hsem1. inv Hsem2. inv Hfby.
      exists H. repeat (split; eauto); simpl...
    - destruct a as [ty [ck name]]. inv Hanns.
      destruct es as [|e]; simpl in *; try congruence.
      repeat inv_bind.
      inv Hlen2. inv Hwt. inv Hwc. inv Hwck. inv Hsem1. inv Hsem2. inv Hnormed. inv Hfby.
      assert (st_follows st x3) as Hfollows.
      { eapply fby_iteexp_st_follows with (ann:=(ty, (ck, name))); eauto. }
      assert (wc_env (idck vars ++ st_clocks x3)) as Hwenv'. 1:eapply fby_iteexp_wc_env in H0...
      eapply fby_iteexp_sem in H0... destruct H0 as [H' [Hvalid1 [Href1 [Hdom1 [Hsem1 Hsem1']]]]].
      assert (Forall2 (fun (e1 : exp) (v : Stream OpAux.value) => sem_exp G H' b e1 [v]) l l').
      { eapply Forall2_impl_In; eauto; intros. eapply sem_exp_refines... } clear H13.
      assert (Forall2 (fun (e1 : exp) (v : Stream OpAux.value) => sem_exp G H' b e1 [v]) es l'0).
      { eapply Forall2_impl_In; eauto; intros. eapply sem_exp_refines... } clear H15.
      assert (normalize_fby l es anns x3 = (x4, (concat x5), st')) as Hnorm.
      { unfold normalize_fby. repeat inv_bind.
        repeat eexists; try inv_bind; eauto. }
      eapply IHanns in Hnorm... clear IHanns.
      2,3,4:solve_forall; repeat solve_incl.
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

  Fact normalize_when_sem : forall G H bs es tys ckid b ck s ss os,
      length es = length tys ->
      Forall2 (fun e s => sem_exp G H bs e [s]) es ss ->
      sem_var H ckid s ->
      Forall2 (fun s' => when b s' s) ss os ->
      Forall2 (fun e s => sem_exp G H bs e [s]) (normalize_when ckid b es tys ck) os.
  Proof with eauto.
    intros * Hlen Hsem Hvar Hwhen.
    unfold normalize_when. simpl_forall.
    repeat rewrite_Forall_forall. 1:congruence.
    eapply Swhen with (ss:=[[nth n ss default_stream]])...
    - repeat constructor...
      eapply H1... congruence.
  Qed.

  Fact normalize_merge_sem : forall G H bs ets efs tys ckid ck s ts fs os,
      length ets = length tys ->
      length efs = length tys ->
      Forall2 (fun e s => sem_exp G H bs e [s]) ets ts ->
      Forall2 (fun e s => sem_exp G H bs e [s]) efs fs ->
      sem_var H ckid s ->
      Forall3 (merge s) ts fs os ->
      Forall2 (fun e s => sem_exp G H bs e [s]) (normalize_merge ckid ets efs tys ck) os.
  Proof with eauto.
    intros * Hlen1 Hlen2 Hsem1 Hsem2 Hvar Hwhen.
    unfold normalize_merge. simpl_forall.
    repeat rewrite_Forall_forall. 1,2:solve_length.
    destruct nth eqn:Hnth. destruct a. rewrite combine_nth in Hnth; try congruence. inv Hnth.
    eapply Smerge with (ts:=[[nth n ts default_stream]]) (fs:=[[nth n fs default_stream]]); simpl...
    - repeat constructor...
      eapply H3... solve_length.
    - repeat constructor...
      eapply H1... solve_length.
    - repeat constructor...
      eapply H6... solve_length.
  Qed.

  Fact normalize_ite_sem : forall G H bs e ets efs tys ck s ts fs os,
      length ets = length tys ->
      length efs = length tys ->
      sem_exp G H bs e [s] ->
      Forall2 (fun e s => sem_exp G H bs e [s]) ets ts ->
      Forall2 (fun e s => sem_exp G H bs e [s]) efs fs ->
      Forall3 (ite s) ts fs os ->
      Forall2 (fun e s => sem_exp G H bs e [s]) (normalize_ite e ets efs tys ck) os.
  Proof with eauto.
    intros * Hlen1 Hlen2 Hsem1 Hsem2 Hsem3 Hwhen.
    unfold normalize_ite. simpl_forall.
    repeat rewrite_Forall_forall. 1,2:solve_length.
    destruct nth eqn:Hnth. destruct a. rewrite combine_nth in Hnth; try congruence. inv Hnth.
    eapply Site with (ts:=[[nth n ts default_stream]]) (fs:=[[nth n fs default_stream]]); simpl...
    - repeat constructor...
      eapply H3... solve_length.
    - repeat constructor...
      eapply H1... solve_length.
    - repeat constructor...
      eapply H6... solve_length.
  Qed.

  Fact sem_var_adds : forall H xs vs,
      length xs = length vs ->
      NoDup xs ->
      Forall2 (sem_var (Env.adds xs vs H)) xs vs.
  Proof.
    intros * Hlen Hndup.
    rewrite_Forall_forall.
    econstructor; [|reflexivity].
    apply Env.adds_MapsTo; auto.
  Qed.

  Fact normalize_merge_sc_exp : forall G H vars b x ets efs tys ck vs,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      wc_env (idck vars) ->
      Forall normalized_cexp (normalize_merge x ets efs tys (ck, None)) ->
      Forall (wt_exp G (idty vars)) (normalize_merge x ets efs tys (ck, None)) ->
      Forall (wc_exp G (idck vars)) (normalize_merge x ets efs tys (ck, None)) ->
      Forall2 (fun (e : exp) (v : Stream value) => sem_exp G H b e [v])
            (normalize_merge x ets efs tys (ck, None)) vs ->
      sc_var_inv' (idck vars) H b ->
      Forall (fun vs => sem_clock H b ck (abstract_clock vs)) vs.
  Proof with eauto.
    intros * HwcG Hsc Hndup Hwenv Hnormed Hwt Hwc Hsem Hinv.
    assert (Forall2 (fun e v => sem_exp G H b e v)
                    (normalize_merge x ets efs tys (ck, None)) (map (fun v => [v]) vs))
      as Hsem' by (clear - Hsem; solve_forall). clear Hsem.
    eapply sc_exps' in Hsem'...
    - unfold normalize_merge in Hsem'. simpl_forall. clear Hnormed.
      assert (Forall (fun vs => exists x, In x (combine (combine ets efs) tys) /\ sem_clock H b ck (abstract_clock vs)) vs).
      2: solve_forall; destruct H1 as [? [_ ?]]...
      eapply Forall2_ignore1, Forall2_impl_In; [|eauto]; clear Hsem'.
      intros [[et ef] ty] ? ? ? ?; simpl in *. inv H2; auto.
    - rewrite normalized_cexps_no_fresh, app_nil_r...
  Qed.

  Fact normalize_ite_sc_exp : forall G H vars b e ets efs tys ck vs,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      wc_env (idck vars) ->
      Forall normalized_cexp (normalize_ite e ets efs tys (ck, None)) ->
      Forall (wt_exp G (idty vars)) (normalize_ite e ets efs tys (ck, None)) ->
      Forall (wc_exp G (idck vars)) (normalize_ite e ets efs tys (ck, None)) ->
      Forall2 (fun (e : exp) (v : Stream value) => sem_exp G H b e [v])
            (normalize_ite e ets efs tys (ck, None)) vs ->
      sc_var_inv' (idck vars) H b ->
      Forall (fun vs => sem_clock H b ck (abstract_clock vs)) vs.
  Proof with eauto.
    intros * HwcG Hsc Hndup Hwenv Hnormed Hwt Hwc Hsem Hinv.
    assert (Forall2 (fun e v => sem_exp G H b e v)
                    (normalize_ite e ets efs tys (ck, None)) (map (fun v => [v]) vs))
      as Hsem' by (clear - Hsem; solve_forall). clear Hsem.
    eapply sc_exps' in Hsem'...
    - unfold normalize_ite in Hsem'. simpl_forall. clear Hnormed.
      assert (Forall (fun vs => exists x, In x (combine (combine ets efs) tys) /\ sem_clock H b ck (abstract_clock vs)) vs).
      2: solve_forall; destruct H1 as [? [_ ?]]...
      eapply Forall2_ignore1, Forall2_impl_In; [|eauto]; clear Hsem'.
      intros [[et ef] ty] ? ? ? ?; simpl in *. inv H2; auto.
    - rewrite normalized_cexps_no_fresh, app_nil_r...
  Qed.

  Fact normalize_fby_is_not_app : forall e0s es anns es' eqs' st st',
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall (fun e => forall id es r anns, e <> Eapp id es r anns) es'.
  Proof.
    intros * Hfby.
    unfold normalize_fby in Hfby; repeat inv_bind.
    eapply map_bind2_values in H.
    assert (Forall (fun e => exists v, In v (combine (combine e0s es) anns) /\ forall id es r anns, e <> Eapp id es r anns) es').
    2: (solve_forall; destruct H1 as [? [? ?]]; auto).
    eapply Forall2_ignore1.
    assert (Forall2 (fun _ e => exists (_:list equation), forall id es r anns, e <> Eapp id es r anns) (combine (combine e0s es) anns) es').
    2: (eapply Forall2_impl_In; eauto; intros ? ? ? ? [? ?]; eauto).
    eapply Forall3_ignore3 with (zs:=x0).
    solve_forall. destruct H2 as [? [? ?]].
    unfold fby_iteexp in H2. destruct a as [ty ck], (Norm.is_constant e); repeat inv_bind; congruence.
  Qed.

  Fact normalize_fby_sc_exp : forall G H vars b e0s es anns es' eqs' vs st st',
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      wc_env (idck vars) ->
      Forall normalized_lexp es ->
      Forall normalized_lexp e0s ->
      Forall (wt_exp G (idty vars)) es' ->
      Forall (wc_exp G (idck vars)) es' ->
      Forall2 (fun e v => sem_exp G H b e [v]) es' vs ->
      sc_var_inv' (idck vars) H b ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall2 (fun ck v => sem_clock H b ck (abstract_clock v)) (clocksof es') vs.
  Proof with eauto.
    intros * HwG Hsc Hndup Hwenv Hnormed1 Hnormed2 Hwt Hwc Hsem Hinv Hfby.
    assert (Forall2 (sem_exp G H b) es' (map (fun v => [v]) vs)) as Hsem' by (clear - Hsem; solve_forall).
    eapply sc_exps' in Hsem'...
    - unfold clocksof. rewrite <- concat_map_singl1, flat_map_concat_map.
      assert (length es' = length vs) as Hlen by (eapply Forall2_length in Hsem'; solve_length).
      apply Forall2_concat.
      assert (Hfby':=Hfby). eapply normalize_fby_numstreams in Hfby.
      eapply normalize_fby_is_not_app in Hfby'.
      solve_forall.
      rewrite <- length_clockof_numstreams in H6. singleton_length.
      destruct a; inv H2; repeat constructor...
      congruence.
    - eapply normalize_fby_no_fresh in Hfby... rewrite Hfby, app_nil_r...
  Qed.

  Fact filter_anons_anon_streams_In' : forall x vars xs,
      NoDup (map fst vars ++ map fst (Syn.anon_streams xs)) ->
      InMembers x (Syn.anon_streams xs) ->
      Ino x (filter_anons vars (map snd xs)).
  Proof.
    intros * Hndup Hin.
    induction xs; simpl in *; auto.
    destruct a as [ty [ck [name|]]]; simpl; auto.
    destruct mem_assoc_ident eqn:Hmem.
    - right. inv Hin.
      + exfalso. apply mem_assoc_ident_true in Hmem as [ck' Hin'].
        rewrite Permutation_app_comm in Hndup. eapply NoDup_app_In with (x0:=x) in Hndup. 2:left; auto.
        apply Hndup. rewrite in_map_iff. exists (x, ck'); eauto.
      + apply IHxs; auto.
        simpl in Hndup; rewrite <- Permutation_middle in Hndup; inv Hndup; auto.
    - inv Hin.
      + left; constructor.
      + right. apply IHxs; auto.
        simpl in Hndup; rewrite <- Permutation_middle in Hndup; inv Hndup; auto.
  Qed.

  Fact idents_for_anns'_filter_anons : forall vars anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      Forall2 (fun x y => forall id, x = Some id -> y = Some id) (filter_anons vars (map snd anns)) (map Some (map fst ids)).
  Proof.
    induction anns; intros * Hids; simpl in *; repeat inv_bind; simpl.
    - constructor.
    - destruct a as [ty [ck [name|]]];
        repeat inv_bind; simpl; constructor; eauto.
      + intros id. destruct mem_assoc_ident; intros; congruence.
      + intros id ?; congruence.
  Qed.

  Fact map_bind2_sem : forall G vars b is_control es H vs es' eqs' st st' reusable,
      wc_global G ->
      NoDup (map fst (fresh_ins es)++PS.elements reusable) ->
      wc_env (idck vars++st_clocks st) ->
      Forall (wt_exp G (idty vars++st_tys st)) es ->
      Forall (wc_exp G (idck vars++st_clocks st)) es ->
      Forall2 (sem_exp G H b) es vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_ins es)) reusable) ->
      hist_st (idck vars) b H st ->
      Forall2 (fun e v => forall H es' eqs' st st' reusable,
                   NoDup (map fst (fresh_in e)++PS.elements reusable) ->
                   wc_env (idck vars++st_clocks st) ->
                   wt_exp G (idty vars++st_tys st) e ->
                   wc_exp G (idck vars++st_clocks st) e ->
                   sem_exp G H b e v ->
                   st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_in e)) reusable) ->
                   hist_st (idck vars) b H st ->
                   normalize_exp is_control e st = (es', eqs', st') ->
                   (exists H',
                       Env.refines eq H H' /\
                       st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
                       hist_st (idck vars) b H' st' /\
                       Forall2 (fun e v => sem_exp G H' b e [v]) es' v /\
                       Forall (sem_equation G H' b) eqs')) es vs ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (idck vars) b H' st' /\
          Forall2 (fun es vs => Forall2 (fun e v => sem_exp G H' b e [v]) es vs) es' vs /\
          Forall (sem_equation G H' b) (concat eqs')).
  Proof with eauto.
    intros * HwcG. revert b is_control es H vs es' eqs' st st' reusable.
    induction es; intros * Hndup Hwenv Hwt Hwc Hsem Hvalid Histst Hf Hmap;
      inv Hwt; inv Hwc; inv Hsem; inv Hf; repeat inv_bind.
    - exists H; simpl. repeat (split; eauto).
    - unfold fresh_ins in *; simpl in *; rewrite map_app, ps_adds_app in Hvalid.
      assert (NoDup (map fst (fresh_ins es)++PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (fresh_in a) ++ PS.elements (ps_adds (map fst (fresh_ins es)) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
      specialize (H9 _ _ _ _ _ _ Hndup1 Hwenv H2 H4 H6 Hvalid Histst H0) as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      assert (wc_env (idck vars ++ st_clocks x1)) as Hwenv2.
      { eapply normalize_exp_wc_env in H0; eauto. }
      assert (Forall (wt_exp G (idty vars ++ st_tys x1)) es) as Hwt2.
      { solve_forall; repeat solve_incl. }
      assert (Forall (wc_exp G (idck vars ++ st_clocks x1)) es) as Hwc2.
      { solve_forall; repeat solve_incl. }
      assert (Forall2 (sem_exp G H' b) es l') as Hsem'.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
      specialize (IHes _ _ _ _ _ _ _ Hndup2 Hwenv2 Hwt2 Hwc2 Hsem' Hvalid1 Histst1 H11 H1) as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]].
      clear H11 H1.
      exists H''. repeat (split; eauto).
      + etransitivity...
      + constructor; eauto. subst.
        assert (length x = numstreams a) as Hlength1 by (eapply normalize_exp_length; eauto).
        assert (length y = numstreams a) as Hlength2 by (eapply sem_exp_numstreams; eauto).
        specialize (normalize_exp_sem_length _ _ _ _ _ _ _ _ H2 H0) as Hnormlength.
        solve_forall.
        eapply sem_exp_refines; eauto.
      + apply Forall_app. split...
        solve_forall. eapply sem_equation_refines...
  Qed.

  Hint Constructors sem_exp.
  Fact normalize_exp_sem : forall G vars b e H vs is_control es' eqs' st st' reusable,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      NoDup (map fst (fresh_in e) ++ PS.elements reusable) ->
      wc_env (idck vars++st_clocks st) ->
      wt_exp G (idty vars++st_tys st) e ->
      wc_exp G (idck vars++st_clocks st) e ->
      sem_exp G H b e vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_in e)) reusable) ->
      hist_st (idck vars) b H st ->
      normalize_exp is_control e st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (idck vars) b H' st' /\
          Forall2 (fun e v => sem_exp G H' b e [v]) es' vs /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros * HwcG Hsc Hndupvars. revert e H vs is_control es' eqs' st st' reusable.
    induction e using exp_ind2; intros * Hndup Hwenv Hwt Hwc Hsem Hvalid Histst Hnorm;
      inv Hwt; inv Hwc; inv Hsem; repeat inv_bind.
    - (* const *)
      exists H. repeat (split; eauto).
    - (* var *)
      exists H. repeat (split; eauto).
    - (* var *)
      exists H. repeat (split; eauto).
    - (* unop *)
      specialize (normalize_exp_typeof _ _ _ _ _ _ _ _ H3 H0) as Htypeof.
      specialize (IHe _ _ _ _ _ _ _ _ Hndup Hwenv H3 H2 H12 Hvalid Histst H0) as [H' [Hvalid1 [Href1 [Hdom1 [Hsem1 Hsem1']]]]].
      assert (numstreams e = 1) by (rewrite <- length_typeof_numstreams; rewrite H14; reflexivity).
      eapply normalize_exp_length in H0... rewrite H1 in H0.
      repeat singleton_length. inv Hsem1; clear H13.
      exists H'. repeat (split; eauto).
      repeat econstructor... congruence.
    - (* binop *)
      simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      specialize (normalize_exp_typeof _ _ _ _ _ _ _ _ H4 H0) as Htypeof1.
      specialize (normalize_exp_typeof _ _ _ _ _ _ _ _ H5 H1) as Htypeof2.
      assert (numstreams e1 = 1) by (rewrite <- length_typeof_numstreams; rewrite H20; reflexivity).
      assert (numstreams e2 = 1) by (rewrite <- length_typeof_numstreams; rewrite H21; reflexivity).
      assert (NoDup (map fst (fresh_in e1) ++ PS.elements (ps_adds (map fst (fresh_in e2)) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'. ndup_simpl... ndup_r Hndup. }
      specialize (IHe1 _ _ _ _ _ _ _ _ Hndup1 Hwenv H4 H10 H15 Hvalid Histst H0) as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      eapply sem_exp_refines in H18; [| eauto].
      assert (NoDup (map fst (fresh_in e2) ++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (wc_env (idck vars++st_clocks x1)) as Hwenv2.
      { eapply normalize_exp_wc_env in H0; eauto. }
      eapply wt_exp_incl with (vars':=(idty vars ++ st_tys x1)) in H5; [eauto|]; repeat solve_incl.
      eapply wc_exp_incl with (vars':=(idck vars ++ st_clocks x1)) in H12; [eauto|]; repeat solve_incl.
      specialize (IHe2 _ _ _ _ _ _ _ _ Hndup2 Hwenv2 H5 H12 H18 Hvalid1 Histst1 H1) as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]].
      eapply normalize_exp_length in H0... rewrite H2 in H0.
      eapply normalize_exp_length in H1... rewrite H3 in H1.
      repeat singleton_length; subst.
      inv Hsem1. inv Hsem2. clear H19 H24.
      exists H''. repeat (split; eauto).
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
      assert (Forall (fun e => numstreams e = 1) (concat x2)) as Hnumstreams.
      { eapply map_bind2_normalize_exp_numstreams in H2... }

      (* Normalization hypothesis *)
      assert (Forall normalized_lexp (concat x2)) as Hnormed1.
      { eapply map_bind2_normalized_lexp in H2... }
      assert (Forall normalized_lexp (concat x9)) as Hnormed2.
      { eapply map_bind2_normalized_lexp in H3... }

      (* Typing and clocking hypothesis *)
      assert (Forall (wt_exp G (idty vars ++ st_tys x4)) (concat x2)) as Hwt1.
      { eapply map_bind2_normalize_exp_wt_exp with (G:=G) (vars:=idty vars) in H2...
        solve_forall; repeat solve_incl. }
      assert (Forall (wt_exp G (idty vars ++ st_tys x7)) x5) as Hwt'.
      { eapply normalize_fby_wt_exp' with (e0s:=e0s) in H4...
        - unfold normalize_exps; repeat inv_bind.
          repeat eexists. eapply H2. inv_bind...
        - unfold normalize_exps; repeat inv_bind.
          repeat eexists. eapply H3. inv_bind... }
      assert (Forall (wc_exp G (idck vars ++ st_clocks x4)) (concat x2)) as Hwc1.
      { eapply map_bind2_normalize_exp_wc_exp with (G:=G) (vars:=idck vars) in H2...
        solve_forall; repeat solve_incl. }
      assert (Forall2 (fun e '(_, (ck, _)) => clockof e = [ck]) (concat x2) a) as Hclocksof.
      { eapply map_bind2_normalize_exp_clocksof'' in H2...
        assert (length (concat x2) = length a). { simpl_length. erewrite <- map_length, H8, map_length; auto. }
        rewrite Forall2_eq in H12. rewrite <- H12 in H2. solve_forall. }
      assert (Forall (wc_exp G (idck vars ++ st_clocks x7)) x5) as Hwc'.
      { eapply normalize_fby_wc_exp' with (e0s:=e0s) in H4...
        - unfold normalize_exps; repeat inv_bind.
          repeat eexists. eapply H2. inv_bind...
        - unfold normalize_exps; repeat inv_bind.
          repeat eexists. eapply H3. inv_bind... }

      assert (length s0ss = length e0s) as Hlen1 by (eapply Forall2_length in H18; eauto).
      assert (st_follows st x1) as Hfollows1 by repeat solve_st_follows.
      assert (wc_env (idck vars ++ st_clocks x1)) as Hwenv2.
      { eapply map_bind2_normalize_exp_wc_env in H2... }
      eapply map_bind2_sem in H2... 2:solve_forall. clear H.
      destruct H2 as [H' [Href1 [Histst1 [Hdom1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.

      assert (Forall (wt_exp G (idty vars++st_tys x1)) es) as Hwt2.
      { solve_forall; repeat solve_incl. }
      assert (Forall (wc_exp G (idck vars++st_clocks x1)) es) as Hwc2.
      { solve_forall; repeat solve_incl. }
      assert (Forall2 (sem_exp G H' b) es sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
      assert (wc_env (idck vars ++ st_clocks x4)) as Hwenv3.
      { eapply map_bind2_normalize_exp_wc_env in H3... }
      assert (length sss = length es) as Hlen2 by (eapply Forall2_length in H20; eauto).
      eapply map_bind2_sem in H3... 2:solve_forall. clear H0.
      destruct H3 as [H'' [Hvalid2 [Href2 [Hdom2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.

      assert (Forall2 (fun (e : exp) (v : Stream OpAux.value) => sem_exp G H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
      specialize (idents_for_anns_length _ _ _ _ H15) as Hlength.
      assert (length (annots es) = length a) as Hlength'.
      { erewrite <- length_typesof_annots, H7, map_length... }
      assert (length vs = length a) as Hlength''.
      { eapply Forall2_length in Hsem''; eapply Forall2_length in Hclocksof; eapply Forall3_length in H21 as [? ?].
        rewrite <- H0, <- H. setoid_rewrite <- Hsem''... }
      assert (Forall (fun '(_, (cl, _)) => wc_clock (idck vars ++ st_clocks x4) cl) a) as Hwck.
      { clear - HwcG Hwenv3 Hnumstreams Hnormed1 Hwc1 Hclocksof.
        eapply wc_exp_clocksof in Hwc1...
        rewrite normalized_lexps_no_fresh in Hwc1... simpl in Hwc1; rewrite app_nil_r in Hwc1.
        unfold clocksof in Hwc1; rewrite flat_map_concat_map in Hwc1; apply Forall_concat' in Hwc1.
        2:(solve_forall; rewrite length_clockof_numstreams; auto).
        assert (length a = length (concat x2)) by (eapply Forall2_length in Hclocksof; eauto).
        assert (Forall (fun ck => exists x, In x (concat x2) /\ wc_clock (idck vars ++ st_clocks x4) (fst (snd ck))) a).
        { apply Forall2_ignore1. solve_forall; simpl.
          rewrite H3 in H2. inv H2... } clear - H0.
        solve_forall. destruct H0 as [? [_ ?]]... }
      assert (wc_env (idck vars ++ st_clocks x7)) as Hwenv4.
      { eapply normalize_fby_wc_env in H4... }
      assert (Hfby':=H4). eapply normalize_fby_sem in H4... 2:solve_length.
      destruct H4 as [H''' [Href3 [Hvalid3 [Histst3 [Hsem3 Hsem3']]]]].
      assert (Forall2 (fun '(_, (ck, _)) v => sem_clock H''' b ck (abstract_clock v)) a vs) as Hvs.
      { (* use sc_exp', while knowing that x5 are not applications
           (annoying cause we need to know that they are well typed and well clocked) *)
        destruct Histst3 as [_ [_ Hinv]].
        eapply normalize_fby_sc_exp with (vars:=vars++st_vars x7) (e0s:=concat x2) (es:=concat x9) in Hsem3...
        6:(rewrite st_clocks_st_vars, <- idck_app in Hinv; auto).
        4:rewrite idty_app, <- st_tys_st_vars... 3,4:rewrite idck_app, <- st_clocks_st_vars...
        + rewrite Forall2_eq in H12, H13.
          eapply normalize_fby_clockof in Hfby'... 3:try congruence.
          2:(erewrite Hlength1, <- map_length, <- map_length, <- clocksof_annots, <- H12, map_length; auto).
          rewrite Hfby' in Hsem3. solve_forall.
        + apply st_valid_reuse_st_valid, st_valid_NoDup in Hvalid3.
          rewrite Permutation_app_comm, ps_of_list_ps_to_list_Perm in Hvalid3. 2:rewrite <- fst_NoDupMembers...
          rewrite st_ids_st_vars, <- map_app, <- fst_NoDupMembers in Hvalid3... } clear Hwt' Hwc'.

      remember (Env.adds (List.map fst x8) vs H''') as H''''.
      assert (length x8 = length vs) as Hlength''' by (rewrite Hlength, Hlength''; auto).
      assert (Env.refines eq H''' H'''') as Href4.
      { destruct Histst3. eapply idents_for_anns_refines...
        rewrite map_fst_idck in H; auto. }
      assert (hist_st (idck vars) b H'''' st') as Histst4.
      { rewrite HeqH''''. eapply idents_for_anns_hist_st in H15... rewrite map_fst_idck... }
      exists H''''. repeat (split; eauto).
      * repeat (etransitivity; eauto).
      * simpl_forall.
        repeat rewrite_Forall_forall.
        destruct (nth _ x8 _) eqn:Hnth.
        repeat constructor. econstructor; [| reflexivity].
        destruct a0. rewrite split_nth in Hnth; inv Hnth.
        rewrite split_map_fst.
        apply Env.adds_MapsTo. 1,2:rewrite map_length; auto.
        rewrite <- fst_NoDupMembers.
        eapply idents_for_anns_NoDupMembers in H15...
      * repeat rewrite Forall_app. repeat split.
        -- simpl_forall.
           repeat rewrite_Forall_forall. 1:congruence.
           destruct (nth _ x8 _) eqn:Hnth1.
           econstructor.
           ++ repeat constructor.
              assert (n < length x5) by congruence.
              specialize (H14 b0 default_stream _ _ _ H28 eq_refl eq_refl).
              eapply sem_exp_refines...
           ++ simpl. repeat constructor.
              econstructor.
              destruct a0. rewrite split_nth in Hnth1; inv Hnth1.
              rewrite split_map_fst.
              apply Env.adds_MapsTo. 1,2:rewrite map_length; auto. 2:reflexivity.
              rewrite <- fst_NoDupMembers.
              eapply idents_for_anns_NoDupMembers in H15...
        -- solve_forall. repeat (eapply sem_equation_refines; eauto).
        -- solve_forall. repeat (eapply sem_equation_refines; eauto).
        -- solve_forall. eapply sem_equation_refines...
    - (* when *)
      assert (length (concat x1) = length (annots es)) as Hlength by (eapply map_bind2_normalize_exp_length; eauto).
      erewrite <- (map_length _ (annots es)) in Hlength. erewrite <- typesof_annots in Hlength.
      assert (length es = length ss) by (apply Forall2_length in H16; auto).
      eapply map_bind2_sem in H1... 2:solve_forall. clear H.
      destruct H1 as [H' [Hvalid1 [Href1 [Hdom1 [Hsem1 Hsem1']]]]].
      apply Forall2_concat in Hsem1.
      exists H'. repeat (split; simpl; eauto).
      eapply normalize_when_sem...
      eapply sem_var_refines...
    - (* merge *)
      simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      assert (length (concat x3) = length (annots ets)) as Hlength1 by (eapply map_bind2_normalize_exp_length; eauto).
      assert (length (concat x6) = length (annots efs)) as Hlength2 by (eapply map_bind2_normalize_exp_length; eauto).
      assert (length (concat ts) = length (annots ets)) as Hlength1' by (eapply sem_exps_numstreams; eauto).
      assert (NoDup (map fst (fresh_ins efs) ++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (fresh_ins ets) ++ PS.elements (ps_adds (map fst (concat (map fresh_in efs))) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

      (* Normalization hypothesis *)
      assert (Forall normalized_cexp (normalize_merge x (concat x3) (concat x6) (typesof ets) (ck, None))) as Hnormed.
      { eapply normalize_merge_normalized_cexp...
        eapply map_bind2_normalized_cexp in H2... eapply map_bind2_normalized_cexp in H3... }

      (* Typing and clocking hypothesis *)
      assert (Forall (wt_exp G (idty vars ++ st_tys x5)) (normalize_merge x (concat x3) (concat x6) (typesof ets) (ck, None))) as Hwt'.
      { eapply normalize_merge_wt_exp; auto.
        + assert (incl (idty vars ++ st_tys st) (idty vars ++ st_tys x5)) by repeat solve_incl...
        + repeat solve_incl.
        + eapply map_bind2_normalize_exp_wt_exp in H2... solve_forall; repeat solve_incl.
        + eapply map_bind2_normalize_exp_wt_exp in H3... solve_forall; repeat solve_incl.
        + eapply map_bind2_normalize_exp_typesof'' in H2...
        + eapply map_bind2_normalize_exp_typesof'' in H3... congruence. }
      assert (Forall (wc_exp G (idck vars ++ st_clocks x5)) (normalize_merge x (concat x3) (concat x6) (typesof ets) (ck, None))) as Hwc'.
      { eapply normalize_merge_wc_exp; auto. 1,2:solve_length.
        + assert (incl (idck vars ++ st_clocks st) (idck vars ++ st_clocks x5)) by repeat solve_incl...
        + eapply map_bind2_normalize_exp_wc_exp in H2... solve_forall; repeat solve_incl.
        + eapply map_bind2_normalize_exp_wc_exp in H3... solve_forall; repeat solve_incl.
        + eapply map_bind2_normalize_exp_clocksof''' in H2...
        + eapply map_bind2_normalize_exp_clocksof''' in H3... }

      assert (length ets = length ts) by (apply Forall2_length in H23; auto).
      assert (st_follows st x2) as Hfollows1 by repeat solve_st_follows.
      assert (wc_env (idck vars++st_clocks x2)) as Hwenv1.
      { eapply map_bind2_normalize_exp_wc_env with (vars:=idck vars) in H2... }
      eapply map_bind2_sem in H2... 2:solve_forall. clear H.
      destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.

      assert (st_follows x2 x5) as Hfollows2 by repeat solve_st_follows.
      assert (length efs = length fs) by (apply Forall2_length in H24; auto).
      assert (Forall (wt_exp G (idty vars ++ st_tys x2)) efs) as Hwtf' by (solve_forall; repeat solve_incl). clear H7.
      assert (Forall (wc_exp G (idck vars ++ st_clocks x2)) efs) as Hwcf' by (solve_forall; repeat solve_incl). clear H13.
      assert (Forall2 (sem_exp G H' b) efs fs) as Hsemf' by (solve_forall; eapply sem_exp_refines; eauto). clear H23.
      assert (wc_env (idck vars++st_clocks x5)) as Hwenv2.
      { eapply map_bind2_normalize_exp_wc_env with (vars:=idck vars) in H3... }
      eapply map_bind2_sem in H3... 2:solve_forall.
      destruct H3 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
      assert (Forall2 (fun e v => sem_exp G H'' b e [v])
                      (normalize_merge x (concat x3) (concat x6) (typesof ets) (ck, None)) vs) as Hsem'.
      { eapply normalize_merge_sem... 1,2:solve_length.
        + solve_forall. eapply sem_exp_refines...
        + repeat (eapply sem_var_refines; eauto). }
      destruct is_control; repeat inv_bind.
      + (* control *)
        exists H''. repeat (split; simpl; eauto).
        * etransitivity...
        * rewrite Forall_app. split; auto.
          solve_forall. eapply sem_equation_refines...
      + (* exp *)
        remember (Env.adds (List.map fst x0) vs H'') as H'''.
        assert (length vs = length x0) as Hlength'.
        { eapply idents_for_anns_length in H2. repeat simpl_length.
          apply Forall3_length in H25 as [? ?]; congruence. }
        assert (Env.refines eq H'' H''') as Href3.
        { destruct Histst2 as [Hdom2 _]. eapply idents_for_anns_refines...
          rewrite map_fst_idck in Hdom2... }
        assert (hist_st (idck vars) b H''' st') as Histst3.
        { rewrite HeqH'''. eapply idents_for_anns_hist_st in H2...
          + rewrite map_fst_idck...
          + destruct Histst2 as [_ [_ Hinv2]]. rewrite st_clocks_st_vars, <- idck_app in Hinv2.
            eapply normalize_merge_sc_exp with (vars:=vars++st_vars x5) in Hsem'...
            4:rewrite idty_app, <- st_tys_st_vars... 3,4:rewrite idck_app, <- st_clocks_st_vars...
            * assert (length vs = length (typesof ets)) as Hlen'.
              { eapply Forall3_length in H25 as [? ?]; solve_length. }
              clear - Hlen' Hsem'. solve_forall.
            * apply st_valid_reuse_st_valid, st_valid_NoDup in Hvalid2.
              rewrite Permutation_app_comm, st_ids_st_vars, ps_of_list_ps_to_list_Perm, <- map_app, <- fst_NoDupMembers in Hvalid2...
              rewrite <- fst_NoDupMembers...
        }
        assert (Forall2 (sem_var H''') (map fst x0) vs) as Hvars.
        { rewrite HeqH'''. eapply sem_var_adds... 1:rewrite map_length...
          rewrite <- fst_NoDupMembers. eapply idents_for_anns_NoDupMembers in H2... }
        exists H'''. repeat (split; eauto).
        * repeat (etransitivity; eauto).
        * clear - Hvars. solve_forall.
        * repeat rewrite Forall_app; repeat split.
          -- remember (normalize_merge _ _ _ _ _) as merge.
             assert (length merge = length x0) as Hlength''.
             { eapply idents_for_anns_length in H2. clear - Heqmerge H18 H2 Hlength1 Hlength2.
               rewrite Heqmerge, normalize_merge_length; solve_length. }
             clear - Hvars Hsem' Href3 Hlength''. simpl_forall.
             assert (Forall2 (fun x1 y => exists (v:Stream value), sem_equation G H''' b (let '(id, _) := x1 in [id], [y])) x0 merge).
             { apply Forall3_ignore3 with (zs:=vs). solve_forall.
               apply Seq with (ss:=[[z]]); simpl.
               1,2:repeat constructor... eapply sem_exp_refines... }
             solve_forall. destruct H1 as [? ?]...
          -- solve_forall. repeat (eapply sem_equation_refines; eauto).
          -- solve_forall. eapply sem_equation_refines...
    - (* ite *)
      simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
      assert (length x = 1). 2:singleton_length.
      { eapply normalize_exp_length in H2... rewrite H2, <- length_typeof_numstreams, H9; auto. }
      assert (length (concat x5) = length (annots ets)) as Hlength1 by (eapply map_bind2_normalize_exp_length; eauto).
      assert (length (concat x8) = length (annots efs)) as Hlength2 by (eapply map_bind2_normalize_exp_length; eauto).
      assert (length (concat ts) = length (annots ets)) as Hlength1' by (eapply sem_exps_numstreams; eauto).
      assert (NoDup (map fst (fresh_ins efs) ++ PS.elements reusable)) as Hndup3 by repeat ndup_r Hndup.
      assert (NoDup (map fst (fresh_ins ets) ++ PS.elements (ps_adds (map fst (concat (map fresh_in efs))) reusable))) as Hndup2.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }
      assert (NoDup
                (map fst (fresh_in e) ++
                     PS.elements (ps_adds (map fst (fresh_ins ets)) (ps_adds (map fst (fresh_ins efs)) reusable)))) as Hndup1.
      { repeat rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }

      (* Normalization hypothesis *)
      assert (Forall normalized_cexp (normalize_ite e0 (concat x5) (concat x8) (typesof ets) (ck, None))) as Hnormed.
      { eapply normalize_ite_normalized_cexp...
        eapply normalize_exp_normalized_lexp in H2... inv H2...
        eapply map_bind2_normalized_cexp in H3... eapply map_bind2_normalized_cexp in H4... }

      (* Typing and clocking hypothesis *)
      assert (Forall (wt_exp G (idty vars ++ st_tys x7)) (normalize_ite e0 (concat x5) (concat x8) (typesof ets) (ck, None))) as Hwt'.
      { eapply normalize_ite_wt_exp; auto.
        + repeat solve_incl.
        + eapply normalize_exp_wt_exp in H2... inv H2. repeat solve_incl.
        + eapply normalize_exp_typeof in H2... simpl in H2; rewrite app_nil_r in H2. congruence.
        + eapply map_bind2_normalize_exp_wt_exp with (G:=G) (vars:=idty vars) in H3... 1,2:solve_forall; repeat solve_incl.
        + eapply map_bind2_normalize_exp_wt_exp in H4... 1,2:solve_forall; repeat solve_incl.
        + eapply map_bind2_normalize_exp_typesof'' in H3...
        + eapply map_bind2_normalize_exp_typesof'' in H4... congruence. }
      assert (Forall (wc_exp G (idck vars ++ st_clocks x7)) (normalize_ite e0 (concat x5) (concat x8) (typesof ets) (ck, None))) as Hwc'.
      { eapply normalize_ite_wc_exp; auto. 1,2:solve_length.
        + eapply normalize_exp_wc_exp in H2... inv H2. repeat solve_incl.
        + eapply map_bind2_normalize_exp_wc_exp with (G:=G) (vars:=idck vars) in H3... 1,2:solve_forall; repeat solve_incl.
        + eapply map_bind2_normalize_exp_wc_exp in H4... 1,2:solve_forall; repeat solve_incl.
        + eapply normalize_exp_clockof in H2... simpl in H2; rewrite app_nil_r in H2. congruence.
        + eapply map_bind2_normalize_exp_clocksof''' in H3...
        + eapply map_bind2_normalize_exp_clocksof''' in H4... }

      assert (length ets = length ts) by (apply Forall2_length in H26; auto).
      assert (st_follows st x1) as Hfollows1 by repeat solve_st_follows.
      assert (wc_env (idck vars++st_clocks x1)) as Hwenv1.
      { eapply normalize_exp_wc_env in H2... }
      eapply IHe in H2... clear IHe.
      destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. inv Hsem1; rename H25 into Hsem1; clear H30.

      assert (st_follows x1 x4) as Hfollows2 by repeat solve_st_follows.
      assert (length efs = length fs) by (apply Forall2_length in H27; auto).
      assert (Forall (wt_exp G (idty vars ++ st_tys x1)) ets) as Hwtt' by (solve_forall; repeat solve_incl). clear H7.
      assert (Forall (wc_exp G (idck vars ++ st_clocks x1)) ets) as Hwct' by (solve_forall; repeat solve_incl). clear H14.
      assert (Forall2 (sem_exp G H' b) ets ts) as Hsemt' by (solve_forall; eapply sem_exp_refines; eauto). clear H26.
      assert (wc_env (idck vars++st_clocks x4)) as Hwenv2.
      { eapply map_bind2_normalize_exp_wc_env with (vars:=idck vars) in H3... }
      eapply map_bind2_sem in H3... 2:solve_forall. clear H.
      destruct H3 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.

      assert (st_follows x4 x7) as Hfollows3 by repeat solve_st_follows.
      assert (length efs = length fs) by (apply Forall2_length in H27; auto).
      assert (Forall (wt_exp G (idty vars ++ st_tys x4)) efs) as Hwtf' by (solve_forall; repeat solve_incl). clear H8.
      assert (Forall (wc_exp G (idck vars ++ st_clocks x4)) efs) as Hwcf' by (solve_forall; repeat solve_incl). clear H15.
      assert (Forall2 (sem_exp G H'' b) efs fs) as Hsemf' by (solve_forall; repeat (eapply sem_exp_refines; eauto)). clear H27.
      assert (wc_env (idck vars++st_clocks x7)) as Hwenv3.
      { eapply map_bind2_normalize_exp_wc_env with (vars:=idck vars) in H4... }
      eapply map_bind2_sem in H4... 2:solve_forall. clear H0.
      destruct H4 as [H''' [Href3 [Hvalid3 [Histst3 [Hsem3 Hsem3']]]]]. apply Forall2_concat in Hsem3.

      assert (Forall2 (fun e v => sem_exp G H''' b e [v])
                      (normalize_ite e0 (concat x5) (concat x8) (typesof ets) (ck, None)) vs) as Hsem'.
      { eapply normalize_ite_sem... 1,2:solve_length.
        + repeat (eapply sem_exp_refines; eauto).
        + solve_forall. eapply sem_exp_refines... }
      destruct is_control; repeat inv_bind.
      + (* control *)
        exists H'''. repeat (split; simpl; eauto).
        * repeat (etransitivity; eauto).
        * repeat (rewrite Forall_app; split); auto.
          1,2:solve_forall; repeat (eapply sem_equation_refines; eauto).
      + (* exp *)
        remember (Env.adds (List.map fst x) vs H''') as H''''.
        assert (length vs = length x) as Hlength'.
        { eapply idents_for_anns_length in H0. repeat simpl_length.
          apply Forall3_length in H28 as [? ?]; congruence. }
        assert (Env.refines eq H''' H'''') as Href4.
        { destruct Histst3 as [Hdom3 _]. eapply idents_for_anns_refines...
          rewrite map_fst_idck in Hdom3... }
        assert (hist_st (idck vars) b H'''' st') as Histst4.
        { rewrite HeqH''''. eapply idents_for_anns_hist_st in H0...
          + rewrite map_fst_idck...
          + destruct Histst3 as [_ [_ Hinv3]]. rewrite st_clocks_st_vars, <- idck_app in Hinv3.
            eapply normalize_ite_sc_exp with (vars:=vars++st_vars x7) in Hsem'...
            4:rewrite idty_app, <- st_tys_st_vars... 3,4:rewrite idck_app, <- st_clocks_st_vars...
            * assert (length vs = length (typesof ets)) as Hlen'.
              { eapply Forall3_length in H28 as [? ?]; solve_length. }
              clear - Hlen' Hsem'. solve_forall.
            * apply st_valid_reuse_st_valid, st_valid_NoDup in Hvalid3.
              rewrite Permutation_app_comm, st_ids_st_vars, ps_of_list_ps_to_list_Perm, <- map_app, <- fst_NoDupMembers in Hvalid3...
              rewrite <- fst_NoDupMembers...
        }
        assert (Forall2 (sem_var H'''') (map fst x) vs) as Hvars.
        { rewrite HeqH''''. eapply sem_var_adds... 1:rewrite map_length...
          rewrite <- fst_NoDupMembers. eapply idents_for_anns_NoDupMembers in H0... }
        exists H''''. repeat (split; eauto).
        * repeat (etransitivity; eauto).
        * clear - Hvars. solve_forall.
        * repeat rewrite Forall_app; repeat split.
          2,3,4: (solve_forall; repeat (eapply sem_equation_refines; eauto)).
          remember (normalize_ite _ _ _ _ _) as ite.
          assert (length ite = length x) as Hlength''.
          { eapply idents_for_anns_length in H0. clear - Heqite H20 H0 Hlength1 Hlength2.
            rewrite Heqite, normalize_ite_length; solve_length. }
          clear - Hvars Hsem' Href4 Hlength''. simpl_forall.
          assert (Forall2 (fun x1 y => exists (v:Stream value), sem_equation G H'''' b (let '(id, _) := x1 in [id], [y])) x ite).
          { apply Forall3_ignore3 with (zs:=vs). solve_forall.
            apply Seq with (ss:=[[z]]); simpl.
            1,2:repeat constructor... eapply sem_exp_refines... }
          solve_forall. destruct H1 as [? ?]...
    - (* app *)
      simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
      assert (a = map snd x1) as Hanns; subst.
      { eapply idents_for_anns'_values in H3... }
      specialize (idents_for_anns'_length _ _ _ _ H3) as Hlength1.
      assert (length (n_out n) = length vs) as Hlength2.
      { destruct H19. apply Forall2_length in H16.
        rewrite H14 in H7; inv H7. unfold idents in *. solve_length. }
      assert (length es = length ss) as Hlength3.
      { apply Forall2_length in H18... }
      assert (NoDup (map fst (Syn.anon_streams (map snd x1))++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (fresh_ins es) ++ PS.elements (ps_adds (map fst (Syn.anon_streams (map snd x1))) reusable))).
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

      (* Normalization hypothesis *)
      assert (Forall normalized_lexp (concat x2)) as Hnormed.
      { eapply map_bind2_normalized_lexp in H2... }

      (* Typing and clocking hyp *)
      assert (wt_exp G (idty vars ++ st_tys x4) (Eapp f (concat x2) None (map snd x1))).
      { econstructor... 1-4:rewrite H11 in H7; inv H7.
        + eapply map_bind2_normalize_exp_wt_exp in H2...
        + eapply map_bind2_normalize_exp_typesof in H2... congruence.
        + congruence.
        + solve_forall; solve_incl.
          rewrite idty_app, <- app_assoc, <- app_assoc.
          apply incl_appr', incl_app; [apply incl_appl;repeat solve_incl|].
          apply incl_app; [apply incl_appl|repeat solve_incl].
          apply map_bind2_normalize_exp_fresh_incl in H2...
          unfold st_tys. apply incl_map; auto. }
      assert (wc_exp G (idck vars ++ st_clocks x4) (Eapp f (concat x2) None (map snd x1))).
      { econstructor... 1-3:rewrite H11 in H7; inv H7.
        + eapply map_bind2_normalize_exp_wc_exp in H2...
        + eapply map_bind2_normalize_exp_nclocksof in H2... rewrite H2... }

      assert (wc_env (idck vars++st_clocks x4)) as Hwenv1.
      { eapply map_bind2_normalize_exp_wc_env with (vars:=idck vars) in H2... }
      eapply map_bind2_sem in H2... 2:solve_forall... clear H0.
      destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].

      assert (sem_exp G H' b (Eapp f (concat x2) None (map snd x1)) vs) as Hsem'.
      { apply Sapp with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))).
        + apply Forall2_concat.
          do 2 solve_forall.
        + rewrite concat_map_singl2. assumption. }
      remember (Env.adds (map fst x1) vs H') as H''.
      assert (length vs = length x1) as Hlen'.
      { eapply Forall2_length in H9; solve_length. }
      assert (Env.refines eq H' H'') as Href2.
      { destruct Histst1 as [Hdom _]; rewrite map_fst_idck in Hdom.
        eapply idents_for_anns'_refines... }
      assert (NoDupMembers x1) as Hndup'. { eapply idents_for_anns'_NoDupMembers in H3... }
      assert (hist_st (idck vars) b H'' st').
      { rewrite HeqH''. eapply idents_for_anns'_hist_st in H3...
        1:rewrite map_fst_idck...
        assert (fresh_ins (concat x2) = []) as Hnfresh. { eapply normalized_lexps_no_fresh in Hnormed... }
        eapply sc_exp' with (env:=vars++st_vars x4) in Hsem'...
        4:rewrite idty_app, <- st_tys_st_vars... 3,4,5:rewrite idck_app, <- st_clocks_st_vars...
        - destruct Hsem' as [? [? [Hl [Hf Hck]]]]. simpl in Hck.
          solve_forall; simpl.
          eapply sem_clock_refines; [|eauto].
          rewrite <- Env.adds_opt'_adds. 2:rewrite <- fst_NoDupMembers... 2:rewrite map_length; auto.
          rewrite Env.adds_opt'_ignore... 2:unfold filter_anons; repeat rewrite map_length; auto.
          2:{ intros ? Hino. rewrite Ino_In in Hino.
              rewrite Forall_forall in Hf. eapply Hf in Hino; simpl in Hino.
              unfold fresh_ins in Hnfresh; rewrite Hnfresh in Hino; simpl in Hino.
              apply filter_anons_anon_streams_In'...
              apply st_valid_reuse_NoDupMembers' in Hvalid1...
              rewrite map_fst_idck, <- map_app, <- app_assoc, <- fst_NoDupMembers... }
          apply Env.adds_opt'_refines... unfold filter_anons. 1,2:repeat rewrite map_length; auto.
          + rewrite NoDupo_NoDup, <- fst_NoDupMembers...
          + eapply idents_for_anns'_nIn' in H3... destruct Histst1 as [Hdom1 _].
            eapply st_valid_reuse_NoDupMembers' in Hvalid1...
            clear - Hdom1 Hvalid1 H3.
            solve_forall; simpl in *. inv H1. erewrite Env.dom_use; [|eauto].
            intro contra; eapply H0; clear H0.
            apply in_or_app. apply in_app_or in contra as [contra|contra]; auto.
            left. rewrite map_fst_idck in contra. apply ps_of_list_ps_to_list...
          + eapply idents_for_anns'_filter_anons...
        - simpl. unfold fresh_ins in Hnfresh; rewrite Hnfresh; simpl.
          eapply st_valid_reuse_NoDupMembers' in Hvalid1... rewrite <- app_assoc...
        - destruct Histst1 as [_ [_ Hinv1]]... }
      assert (Forall2 (sem_var H'') (map fst x1) vs) as Hvars.
      { rewrite HeqH''. eapply sem_var_adds... 1:rewrite map_length... rewrite <- fst_NoDupMembers... }
      exists H''. repeat (split; eauto).
      + etransitivity...
      + clear - Hvars. solve_forall.
      + rewrite app_nil_r. constructor.
        * apply Seq with (ss:=[vs]).
          -- repeat constructor...
             eapply sem_exp_refines...
          -- simpl. rewrite app_nil_r; auto.
        * solve_forall. eapply sem_equation_refines...
    - (* app (reset) *)
      simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
      assert (a = map snd x5) as Hanns; subst.
      { eapply idents_for_anns'_values in H4... }
      specialize (idents_for_anns'_length _ _ _ _ H4) as Hlength1.
      assert (length (n_out n) = length vs) as Hlength2.
      { specialize (H26 0). inv H26. apply Forall2_length in H23.
        rewrite H20 in H7; inv H7. unfold idents in *. solve_length. }
      assert (length es = length ss) as Hlength3.
      { apply Forall2_length in H22... }
      assert (length x6 = 1). 2:singleton_length.
      { eapply normalize_exp_length in H3... rewrite H3, <- length_clockof_numstreams, H18; auto. }
      assert (NoDup (map fst (Syn.anon_streams (map snd x5))++ PS.elements reusable)) as Hndup2 by repeat ndup_r Hndup.
      assert (NoDup (map fst (fresh_in r) ++ PS.elements (ps_adds (map fst (Syn.anon_streams (map snd x5))) reusable))) as Hndup3.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }
      assert (NoDup (map fst (fresh_ins es) ++ PS.elements (ps_adds (map fst (fresh_in r)) (ps_adds (map fst (Syn.anon_streams (map snd x5))) reusable)))) as Hndup4.
      { repeat rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }

      (* Normalization hypothesis *)
      assert (normalized_lexp e) as Hnormede by (eapply normalize_exp_normalized_lexp in H3; inv H3; eauto).
      assert (Forall normalized_lexp (concat x2)) as Hnormed.
      { eapply map_bind2_normalized_lexp in H2... }
      assert (fresh_ins (concat x2) = []) as Hnfresh1 by (eapply normalized_lexps_no_fresh in Hnormed; eauto).
      assert (fresh_in x9 = []) as Hnfresh2 by (eapply normalize_reset_no_fresh in H5; eauto).

      (* Typing and clocking hyp *)
      assert (wt_exp G (idty vars ++ st_tys x4) (Eapp f (concat x2) (Some x9) (map snd x5))) as Hwtf.
      { econstructor... 1-4:rewrite H14 in H7; inv H7.
        + eapply map_bind2_normalize_exp_wt_exp in H2... solve_forall; repeat solve_incl.
        + eapply map_bind2_normalize_exp_typesof in H2... congruence.
        + congruence.
        + solve_forall; solve_incl.
          rewrite idty_app, <- app_assoc, <- app_assoc.
          apply incl_appr', incl_app; [apply incl_appl;repeat solve_incl|].
          apply incl_app; [apply incl_appl|repeat solve_incl].
          apply map_bind2_normalize_exp_fresh_incl in H2...
          unfold st_tys. apply incl_map; auto. etransitivity; eauto. repeat solve_incl.
        + eapply normalize_reset_wt_exp in H5...
          2: eapply normalize_exp_wt_exp with (G:=G) (vars:=idty vars) in H3; inv H3... 2,3:repeat solve_incl.
          eapply normalize_exp_no_fresh in H3; unfold fresh_ins in H3; simpl in H3.
          rewrite app_nil_r in H3. rewrite H3. apply incl_nil'.
        + eapply normalize_reset_typeof_bool in H5...
          eapply normalize_exp_typeof in H3...
          simpl in H3; rewrite app_nil_r in H3. congruence. }
      assert (wt_exp G (idty vars ++ st_tys x8) e) as Hwte.
      { eapply normalize_exp_wt_exp with (G:=G) (vars:=idty vars) in H3; inv H3... 1,2:repeat solve_incl. }
      assert (wc_exp G (idck vars ++ st_clocks x8) e) as Hwce.
      { eapply normalize_exp_wc_exp with (G:=G) (vars:=idck vars) in H3; inv H3... 1,2:repeat solve_incl. }
      assert (wc_exp G (idck vars ++ st_clocks x4) (Eapp f (concat x2) (Some x9) (map snd x5))) as Hwcf.
      { econstructor... 1-3:rewrite H14 in H7; inv H7.
        + eapply map_bind2_normalize_exp_wc_exp in H2... solve_forall; repeat solve_incl.
        + eapply map_bind2_normalize_exp_nclocksof in H2... rewrite H2...
        + eapply normalize_reset_wc_exp in H5...
        + eapply normalize_reset_clockof in H5...
          2:eapply normalize_exp_numstreams in H3; inv H3...
          eapply normalize_exp_clockof in H3...
          unfold clocksof in H3; simpl in H3; rewrite app_nil_r in H3. rewrite H5, H3, H18... }
      assert (wc_env (idck vars++st_clocks x1)) as Hwenv1.
      { eapply map_bind2_normalize_exp_wc_env with (vars:=idck vars) in H2... }
      assert (wc_env (idck vars++st_clocks x8)) as Hwenv2.
      { eapply normalize_exp_wc_env in H3... repeat solve_incl. }
      assert (wc_env (idck vars++st_clocks x4)) as Hwenv3.
      { eapply normalize_reset_wc_env in H5...
        eapply wc_exp_clockof in Hwce...
        eapply normalized_lexp_no_fresh in Hnormede. rewrite Hnormede, app_nil_r in Hwce... }

      assert (wt_exp G (idty vars ++ st_tys x1) r) as Hwtr' by (repeat solve_incl). clear H11.
      assert (wc_exp G (idck vars ++ st_clocks x1) r) as Hwcr' by (repeat solve_incl). clear H17.
      eapply map_bind2_sem in H2... 2:solve_forall... clear H0.
      destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].

      assert (sem_exp G H' b r [rs]) as Hsemr' by (eapply sem_exp_refines; eauto). clear H24.
      eapply H in H3... clear H.
      destruct H3 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. inv Hsem2; clear H17.

      eapply normalize_reset_sem in H5...
      destruct H5 as [H''' [Href3 [Hvalid3 [Histst3 [Hsem3 Hsem3']]]]].

      assert (sem_exp G H''' b (Eapp f (concat x2) (Some x9) (map snd x5)) vs) as Hsem'.
      { eapply Sreset with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss)))...
        + apply Forall2_concat. repeat solve_forall.
          repeat (eapply sem_exp_refines; eauto).
        + intros k. specialize (H26 k).
          rewrite concat_map_singl2. assumption. }
      remember (Env.adds (map fst x5) vs H''') as H''''.
      assert (length vs = length x5) as Hlen'.
      { eapply Forall2_length in H9; solve_length. }
      assert (Env.refines eq H''' H'''') as Href4.
      { destruct Histst3 as [Hdom _]; rewrite map_fst_idck in Hdom.
        eapply idents_for_anns'_refines... }
      assert (NoDupMembers x5) as Hndup'. { eapply idents_for_anns'_NoDupMembers in H4... }
      assert (hist_st (idck vars) b H'''' st').
      { rewrite HeqH''''. eapply idents_for_anns'_hist_st in H4...
        1:rewrite map_fst_idck...
        eapply sc_exp' with (env:=vars++st_vars x4) in Hsem'...
        4:rewrite idty_app, <- st_tys_st_vars... 3,4,5:rewrite idck_app, <- st_clocks_st_vars...
        - destruct Hsem' as [? [? [Hl [Hf Hck]]]]. simpl in Hck.
          solve_forall; simpl.
          eapply sem_clock_refines; [|eauto].
          rewrite <- Env.adds_opt'_adds. 2:rewrite <- fst_NoDupMembers... 2:rewrite map_length; auto.
          rewrite Env.adds_opt'_ignore... 2:unfold filter_anons; repeat rewrite map_length; auto.
          2:{ intros ? Hino. rewrite Ino_In in Hino.
              rewrite Forall_forall in Hf. eapply Hf in Hino; simpl in Hino.
              unfold fresh_ins in Hnfresh1; rewrite Hnfresh1 in Hino; simpl in Hino.
              apply filter_anons_anon_streams_In'...
              apply st_valid_reuse_NoDupMembers' in Hvalid3...
              rewrite map_fst_idck, <- map_app, <- app_assoc, <- fst_NoDupMembers...
              rewrite Hnfresh2 in Hino... }
          apply Env.adds_opt'_refines... unfold filter_anons. 1,2:repeat rewrite map_length; auto.
          + rewrite NoDupo_NoDup, <- fst_NoDupMembers...
          + eapply idents_for_anns'_nIn' in H4... destruct Histst3 as [Hdom1 _].
            eapply st_valid_reuse_NoDupMembers' in Hvalid3...
            clear - Hdom1 Hvalid3 H4.
            solve_forall; simpl in *. inv H1. erewrite Env.dom_use; [|eauto].
            intro contra; eapply H0; clear H0.
            apply in_or_app. apply in_app_or in contra as [contra|contra]; auto.
            left. rewrite map_fst_idck in contra. apply ps_of_list_ps_to_list...
          + eapply idents_for_anns'_filter_anons...
        - simpl. unfold fresh_ins in Hnfresh1; rewrite Hnfresh1; simpl.
          eapply st_valid_reuse_NoDupMembers' in Hvalid3... rewrite <- app_assoc, Hnfresh2...
        - destruct Histst3 as [_ [_ Hinv1]]... }
      assert (Forall2 (sem_var H'''') (map fst x5) vs) as Hvars.
      { rewrite HeqH''''. eapply sem_var_adds... 1:rewrite map_length... rewrite <- fst_NoDupMembers... }
      exists H''''. repeat (split; eauto).
      + repeat (etransitivity; eauto).
      + clear - Hvars. solve_forall.
      + constructor; [| repeat rewrite Forall_app; repeat split].
        * apply Seq with (ss:=[vs]).
          -- repeat constructor...
             eapply sem_exp_refines...
          -- simpl. rewrite app_nil_r; auto.
        * solve_forall. repeat (eapply sem_equation_refines; eauto).
        * solve_forall. repeat (eapply sem_equation_refines; eauto).
        * solve_forall. repeat (eapply sem_equation_refines; eauto).
  Qed.

  Corollary normalize_exps_sem : forall G vars b es H vs es' eqs' st st' reusable,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      NoDup (map fst (fresh_ins es) ++ PS.elements reusable) ->
      wc_env (idck vars ++ st_clocks st) ->
      Forall (wt_exp G (idty vars ++ st_tys st)) es ->
      Forall (wc_exp G (idck vars ++ st_clocks st)) es ->
      Forall2 (sem_exp G H b) es vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_ins es)) reusable) ->
      hist_st (idck vars) b H st ->
      map_bind2 (normalize_exp false) es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (idck vars) b H' st' /\
          Forall2
            (fun (es : list exp) (vs : list (Stream OpAux.value)) =>
             Forall2 (fun e v => sem_exp G H' b e [v]) es vs) es' vs /\
          Forall (sem_equation G H' b) (concat eqs')).
  Proof.
    intros * HwcG Hsc Hndup1 Hndup2 Hwenv Hwt Hwc Hsem Hvalid Hdom Hnorm.
    eapply map_bind2_sem in Hnorm; eauto.
    repeat rewrite_Forall_forall.
    specialize (nth_In _ a H2) as Hin.
    eapply normalize_exp_sem with (e:=(nth n es a)); eauto.
  Qed.

  Fact normalize_rhs_sem : forall G vars b keep_fby e H vs es' eqs' st st' reusable,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      NoDup (map fst (anon_in e) ++ PS.elements reusable) ->
      wc_env (idck vars ++ st_clocks st) ->
      wt_exp G (idty vars ++ st_tys st) e ->
      wc_exp G (idck vars ++ st_clocks st) e ->
      sem_exp G H b e vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in e)) reusable) ->
      hist_st (idck vars) b H st ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (idck vars) b H' st' /\
          (Forall2 (fun e v => sem_exp G H' b e [v]) es' vs \/
           exists e', (es' = [e'] /\ sem_exp G H' b e' vs)) /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros * HwcG Hsc Hndup1 Hndup2 Hwenv Hwt Hwc Hsem Hvalid Hhistst Hnorm.
    destruct e; try eapply normalize_exp_sem in Hnorm; eauto.
    1,2,3,4,6,7,8: (destruct Hnorm as [H' [Href1 [Hvalid1 [Hhistst1 [Hsem1 Hsem2]]]]];
                    exists H'; repeat (split; eauto)).
    1,2:(unfold normalize_rhs in Hnorm). destruct keep_fby. 1,2,3:(inv Hwt; inv Hwc; inv Hsem).
    - (* fby (keep) *)
      simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
      repeat inv_bind.
      assert (length x = length (annots l)) as Hlength1 by (eapply normalize_exps_length; eauto).
      assert (length x2 = length (annots l0)) as Hlength2 by (eapply normalize_exps_length; eauto).
      unfold normalize_exps in *. repeat inv_bind.
      assert (NoDup (map fst (fresh_ins l0) ++ PS.elements reusable)) as Hndup4 by ndup_r Hndup2.
      assert (NoDup (map fst (fresh_ins l) ++ PS.elements (ps_adds (map fst (fresh_ins l0)) reusable))) as Hndup3.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

      (* Needed hypothesis *)
      assert (Forall (fun e => numstreams e = 1) (concat x2)) as Hnumstreams by (eapply map_bind2_normalize_exp_numstreams in H0; eauto).
      assert (Forall normalized_lexp (concat x2)) as Hnormed by (eapply map_bind2_normalized_lexp in H0; eauto).
      assert (Forall (wt_exp G (idty vars ++ st_tys x4)) (concat x2)) as Hwt1.
      { eapply map_bind2_normalize_exp_wt_exp in H0... solve_forall; repeat solve_incl. }
      assert (Forall (wc_exp G (idck vars ++ st_clocks x4)) (concat x2)) as Hwc1.
      { eapply map_bind2_normalize_exp_wc_exp in H0... solve_forall; repeat solve_incl. }
      assert (Forall2 (fun e '(_, (ck, _)) => clockof e = [ck]) (concat x2) l1) as Hclocksof.
      { eapply map_bind2_normalize_exp_clocksof'' in H0...
        assert (length (concat x2) = length l1). { simpl_length. erewrite <- map_length, H6, map_length; auto. }
        rewrite Forall2_eq in H10. rewrite <- H10 in H0. solve_forall. }

      assert (Forall (wt_exp G (idty vars ++ st_tys x1)) l0) as Hwt' by (solve_forall; repeat solve_incl).
      assert (Forall (wc_exp G (idck vars ++ st_clocks x1)) l0) as Hwc' by (solve_forall; repeat solve_incl).
      assert (wc_env (idck vars ++ st_clocks x1)) as Hwenv1 by (eapply map_bind2_normalize_exp_wc_env in H0; eauto).
      eapply normalize_exps_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.
      assert (Forall2 (sem_exp G H' b) l0 sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).

      assert (wc_env (idck vars ++ st_clocks x4)) as Hwenv2 by (eapply map_bind2_normalize_exp_wc_env in H1; eauto).
      eapply normalize_exps_sem in H1...
      destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
      assert (Forall2 (fun (e : exp) (v : Stream OpAux.value) => sem_exp G H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }

      assert (Forall (fun '(_, (cl, _)) => wc_clock (idck vars ++ st_clocks x4) cl) l1) as Hwck.
      { clear - HwcG Hwenv2 Hnumstreams Hnormed Hwc1 Hclocksof.
        eapply wc_exp_clocksof in Hwc1...
        rewrite normalized_lexps_no_fresh in Hwc1... simpl in Hwc1; rewrite app_nil_r in Hwc1.
        unfold clocksof in Hwc1; rewrite flat_map_concat_map in Hwc1; apply Forall_concat' in Hwc1.
        2:(solve_forall; rewrite length_clockof_numstreams; auto).
        assert (length l1 = length (concat x2)) by (eapply Forall2_length in Hclocksof; eauto).
        assert (Forall (fun ck => exists x, In x (concat x2) /\ wc_clock (idck vars ++ st_clocks x4) (fst (snd ck))) l1).
        { apply Forall2_ignore1. solve_forall; simpl.
          rewrite H3 in H2. inv H2... } clear - H0.
        solve_forall. destruct H0 as [? [_ ?]]... }

      eapply normalize_fby_sem in H2...
      2: (simpl_length; erewrite <- map_length, <- typesof_annots, H5, map_length); auto.
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
        solve_forall. solve_forall.
      * rewrite concat_map_singl2. assumption.
      * rewrite app_nil_r...
    - (* app (reset) *)
      simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
      repeat inv_bind. unfold normalize_exps in H0; repeat inv_bind.
      assert (NoDup (map fst (fresh_in r) ++ PS.elements reusable)) as Hndup4 by ndup_r Hndup2.
      assert (NoDup (map fst (fresh_ins l) ++ PS.elements (ps_adds (map fst (fresh_in r)) reusable))) as Hndup3.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

      assert (wt_exp G (idty vars ++ st_tys x1) r) as Hwt' by repeat solve_incl.
      assert (wc_exp G (idck vars ++ st_clocks x1) r) as Hwc' by repeat solve_incl.
      assert (wc_env (idck vars ++ st_clocks x1)) as Hwenv1 by (eapply map_bind2_normalize_exp_wc_env in H0; eauto).
      eapply normalize_exps_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      assert (length x4 = 1) as Hlength2.
      { eapply normalize_exp_length in H1... rewrite <- length_typeof_numstreams in H1.
        rewrite H1, H10. reflexivity. }
      singleton_length.
      assert (sem_exp G H' b r [rs]) as Hsem' by (eapply sem_exp_refines; eauto). clear H16.

      assert (normalized_lexp e) as Hnormed by (eapply normalize_exp_normalized_lexp in H1; inv H1; eauto).
      assert (wt_exp G (idty vars ++ st_tys x6) e) as Hwt'' by (eapply normalize_exp_wt_exp in H1; inv H1; eauto).
      assert (wc_exp G (idck vars ++ st_clocks x6) e) as Hwc'' by (eapply normalize_exp_wc_exp in H1; inv H1; eauto).
      assert (wc_env (idck vars ++ st_clocks x6)) as Hwenv2 by (eapply normalize_exp_wc_env in H1; eauto).
      eapply normalize_exp_sem in H1...
      destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. inv Hsem2; clear H13.
      eapply normalize_reset_sem in H2...
      destruct H2 as [H''' [Href3 [Hvalid3 [Histst3 [Hsem3 Hsem3']]]]].
      exists H'''. repeat (split; auto).
      + repeat (etransitivity; eauto).
      + right. eexists; split...
        apply Sreset with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))) (rs:=rs) (bs:=bs); eauto.
        * apply Forall2_concat.
          solve_forall. solve_forall. repeat (eapply sem_exp_refines; eauto).
        * rewrite concat_map_singl2. assumption.
      + repeat rewrite Forall_app.
        repeat split; solve_forall; (eapply sem_equation_refines; [| eauto]); eauto.
        etransitivity...
  Qed.

  Corollary map_bind2_normalize_rhs_sem : forall G vars b keep_fby es H vs es' eqs' st st' reusable,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      NoDup (map fst (anon_ins es) ++ PS.elements reusable) ->
      wc_env (idck vars ++ st_clocks st) ->
      Forall (wt_exp G (idty vars ++ st_tys st)) es ->
      Forall (wc_exp G (idck vars ++ st_clocks st)) es ->
      Forall2 (sem_exp G H b) es vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_ins es)) reusable) ->
      hist_st (idck vars) b H st ->
      map_bind2 (normalize_rhs keep_fby) es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (idck vars) b H' st' /\
          Forall2 (fun es' vs =>
                     Forall2 (fun e v => sem_exp G H' b e [v]) es' vs \/
                     exists e', (es' = [e'] /\ sem_exp G H' b e' vs)) es' vs /\
          Forall (sem_equation G H' b) (concat eqs')).
  Proof with eauto.
    induction es; intros * HwcG Hsc Hndup1 Hndup2 Hwenv Hwt Hwc Hsem Hvalid Histst Hmap;
      repeat inv_bind.
    - exists H; simpl. inv Hsem. repeat (split; auto).
    - inv Hwt. inv Hwc. inv Hsem.
      unfold anon_ins in *. simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      assert (NoDup (map fst (anon_ins es) ++ PS.elements reusable)) as Hndup4 by ndup_r Hndup2.
      assert (NoDup (map fst (anon_in a) ++ PS.elements (ps_adds (map fst (anon_ins es)) reusable))) as Hndup3.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

      assert (Forall (wt_exp G (idty vars ++ st_tys x1)) es) as Hwt' by (solve_forall; repeat solve_incl).
      assert (Forall (wc_exp G (idck vars ++ st_clocks x1)) es) as Hwc' by (solve_forall; repeat solve_incl).
      assert (wc_env (idck vars ++ st_clocks x1)) as Hwenv' by (eapply normalize_rhs_wc_eq in H0 as [_ ?]; eauto).
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
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      NoDup (map fst (anon_ins es) ++ PS.elements reusable) ->
      wc_env (idck vars ++ st_clocks st) ->
      Forall (wt_exp G (idty vars++st_tys st)) es ->
      Forall (wc_exp G (idck vars++st_clocks st)) es ->
      Forall2 (sem_exp G H b) es vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_ins es)) reusable) ->
      hist_st (idck vars) b H st ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          hist_st (idck vars) b H' st' /\
          Forall (fun '(e, v) => sem_exp G H' b e v)
                 (combine_for_numstreams es' (concat vs)) /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros * HwcG Hsc Hndup1 Hndup2 Hwenv Hwt Hwc Hsem Hvalid Histst Hnorm.
    assert (Forall (wt_exp G (idty vars++st_tys st')) es') as Hwt'.
    { eapply normalize_rhss_wt_exp in Hnorm... }
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
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      NoDup (map fst (anon_in_eq equ) ++ PS.elements reusable) ->
      wc_env (idck vars ++ st_clocks st) ->
      wt_equation G (idty vars ++ st_tys st) equ ->
      wc_equation G (idck vars ++ st_clocks st) equ ->
      sem_equation G H b equ ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in_eq equ)) reusable) ->
      hist_st (idck vars) b H st ->
      normalize_equation to_cut equ st = (eqs', st') ->
      (exists H', Env.refines eq H H' /\
             st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
             hist_st (idck vars) b H' st' /\
             Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros * HwcG Hsc Hndup1 Hndup2 Hwenv Hwt Hwc Hsem Hvalid Histst Hnorm.
    unfold normalize_equation in Hnorm.
    destruct equ as [xs es]. inv Hwt. destruct Hwc as [Hwc _]. inv Hsem.
    repeat inv_bind.
    assert (typesof x = typesof es) as Hannots by (eapply normalize_rhss_typesof; eauto).
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
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      NoDup (map fst (anon_in_eqs eqs) ++ PS.elements reusable) ->
      wc_env (idck vars ++ st_clocks st) ->
      Forall (wt_equation G (idty vars ++ st_tys st)) eqs ->
      Forall (wc_equation G (idck vars ++ st_clocks st)) eqs ->
      Forall (sem_equation G H b) eqs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in_eqs eqs)) reusable) ->
      hist_st (idck vars) b H st ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      (exists H', Env.refines eq H H' /\
             Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction eqs; intros * HwcG Hsc Hndup1 Hndup2 Hwenv Hwt Hwc Hsem Hvalid Hdome Hnorm;
      inv Hwt; inv Hwc; inv Hsem; repeat inv_bind.
    - exists H...
    - unfold anon_in_eqs in *; simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      assert (NoDup (map fst (anon_in_eqs eqs) ++ PS.elements reusable)) as Hndup4 by ndup_r Hndup2.
      assert (NoDup (map fst (anon_in_eq a) ++ PS.elements (ps_adds (map fst (anon_in_eqs eqs)) reusable))) as Hndup3.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

      assert (Forall (wt_equation G (idty vars ++ st_tys x0)) eqs) as Hwt' by (solve_forall; repeat solve_incl).
      assert (Forall (wc_equation G (idck vars ++ st_clocks x0)) eqs) as Hwc' by (solve_forall; repeat solve_incl).
      assert (wc_env (idck vars ++ st_clocks x0)) as Hwenv' by (eapply normalize_equation_wc_eq in H0; inv H0; eauto).
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
      sc_var_inv' (idck (n_in n++n_vars n++n_out n)) H b ->
      hist_st (idck (n_in n++n_vars n++n_out n)) b H
              (init_st (first_unused_ident (self::out::(map fst (n_in n++n_vars n++n_out n++anon_in_eqs (n_eqs n)))))).
  Proof.
    intros b H n Hdom Hinv.
    repeat constructor.
    - unfold st_ids.
      rewrite init_st_anns; simpl.
      rewrite app_nil_r, map_fst_idck. assumption.
    - unfold init_eqs_valids.
      rewrite init_st_anns. constructor.
    - unfold st_clocks. rewrite init_st_anns; simpl.
      rewrite app_nil_r. assumption.
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
      wc_global G ->
      sc_nodes G ->
      wt_node G n ->
      wc_node G n ->
      sc_node' G n ->
      Env.dom H (List.map fst (n_in n ++ n_vars n ++ n_out n)) ->
      Forall2 (sem_var H) (idents (n_in n)) ins ->
      Forall (sem_equation G H (Str.clocks_of ins)) (n_eqs n) ->
      Forall2 (fun xc : ident * clock => sem_clock H (clocks_of ins) (snd xc)) (idck (n_in n)) (map abstract_clock ins) ->
      exists H', Env.refines eq H H' /\
            Forall (sem_equation G H' (Str.clocks_of ins)) (n_eqs (normalize_node to_cut n Hwl)).
  Proof with eauto.
    intros * HwcG HscG Hwt Hwc Hsc Hdom Hins Hclockinputs Hsem.
    remember (@init_st ((Op.type * clock) * bool)
                (first_unused_ident (self::out::(map fst (n_in n++n_vars n++n_out n++anon_in_eqs (n_eqs n)))))) as init.
    specialize (n_nodup n) as Hndup; rewrite fst_NoDupMembers in Hndup; repeat rewrite map_app in Hndup.
    eapply normalize_equations_sem with (eqs:=n_eqs n) (st:=init)...
    8: simpl; rewrite <- surjective_pairing; subst; reflexivity.
    - pose proof (n_nodup n) as Hndup'.
      repeat rewrite app_assoc in Hndup'. apply NoDupMembers_app_l in Hndup'.
      repeat rewrite <- app_assoc in Hndup'. exact Hndup'.
    - rewrite PSP.elements_empty, app_nil_r.
      repeat ndup_r Hndup...
    - unfold st_clocks. rewrite Heqinit, init_st_anns, app_nil_r.
      destruct Hwc as [_ [_ [Hwc _]]]; auto.
      rewrite (Permutation_app_comm (n_out n) _) in Hwc; auto.
    - unfold st_tys. rewrite Heqinit, init_st_anns, app_nil_r.
      destruct Hwt as [_ [_ [_ Hwt]]]; auto.
    - unfold st_clocks. rewrite Heqinit, init_st_anns, app_nil_r.
      destruct Hwc as [_ [_ [_ Hwc]]]; auto.
    - rewrite Heqinit.
      apply init_st_valid_reuse.
      rewrite ps_adds_of_list.
      + repeat rewrite ps_of_list_ps_to_list_Perm.
        * rewrite <- map_app, <- fst_NoDupMembers. repeat rewrite <- app_assoc. eapply (n_nodup n).
        * repeat ndup_r Hndup.
        * repeat rewrite <- map_app in Hndup. repeat rewrite app_assoc in Hndup.
          rewrite <- fst_NoDupMembers in *. apply NoDupMembers_app_l in Hndup.
          repeat rewrite <- app_assoc in Hndup...
      + rewrite <- ps_adds_of_list, PS_For_all_ps_adds; split. 2:apply PS_For_all_empty.
        eapply Forall_incl. eapply first_unused_ident_gt; reflexivity.
        apply incl_tl, incl_tl, incl_map, incl_appr', incl_appr', incl_appl, incl_refl.
      + rewrite PS_For_all_ps_adds; split. 2:apply PS_For_all_empty.
        eapply Forall_incl. eapply first_unused_ident_gt; reflexivity.
        apply incl_tl, incl_tl, incl_map, incl_appr, incl_appr, incl_appr, incl_refl.
    - rewrite Heqinit.
      eapply init_st_hist_st...
      eapply sc_node_sc_var_inv...
  Qed.

  Lemma normalize_node_eq : forall G G' f n Hwl ins outs to_cut,
      Forall2 (fun n n' => n_name n = n_name n') G G' ->
      global_iface_eq G G' ->
      global_sem_refines G G' ->
      wt_global (n::G) ->
      wc_global (n::G) ->
      wt_global G' ->
      wc_global G' ->
      Ordered_nodes (n::G) ->
      Ordered_nodes ((normalize_node to_cut n Hwl)::G') ->
      Forall LCA.node_causal (n::G) ->
      Forall LCA.node_causal G' ->
      sem_node (n::G) f ins outs ->
      sem_clock_inputs (n::G) f ins ->
      sem_node ((normalize_node to_cut n Hwl)::G') f ins outs.
  Proof with eauto.
    intros * Hnames Hiface Href HwtG HwcG HwtG' HwcG' Hord1 Hord2 Hcaus1 Hcaus2 Hsem Hinputs.
    assert (sc_nodes G) as HscG.
    { inv HwtG. inv HwcG. inv Hord1. inv Hcaus1. eapply l_sem_node_clock... }
    assert (sc_node' G n) as Hsc.
    { eapply l_sem_node_clock' in HwtG; auto. 2:left; auto.
      eapply sc_node'_global_tl... }
    assert (Forall (fun n' => exists v, In v G /\ n_name n <> n_name n') G') as Hnames'.
    { assert (length G = length G') by (eapply Forall2_length in Hnames; eauto).
      inv HwtG. eapply Forall2_ignore1. solve_forall. }
    assert (wt_global (n::G')) as HwtG''.
    { constructor...
      + inv HwtG. eapply iface_eq_wt_node...
      + solve_forall. destruct H0 as [? [_ ?]]... }
    assert (wc_global (n::G')) as HwcG''.
    { constructor...
      + inv HwcG. eapply iface_eq_wc_node...
      + solve_forall. destruct H0 as [? [_ ?]]... }
    assert (Ordered_nodes (n :: G')) as Hord'.
    { inv Hord2. constructor... clear H2.
      inv Hord1. intros ? Hisin. apply H4 in Hisin as [Hneq Hname].
      split; auto. clear - Hnames Hname.
      induction Hnames; inv Hname.
      + left; auto.
      + right; auto. }
    assert (sc_nodes G') as HscG'.
    { inv HwtG''. inv HwcG''. inv Hord2. eapply l_sem_node_clock... }
    assert (sc_node' G' n) as Hsc'.
    { eapply l_sem_node_clock' in HwtG''; auto. 3:left; auto.
      + eapply sc_node'_global_tl...
      + inv Hcaus1. constructor... }

    inv Hsem; assert (Hfind:=H0); simpl in H0. destruct (ident_eqb (n_name n) f) eqn:Hident.
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
        eapply find_node_not_Is_node_in in Hord1... }
      inversion_clear HwtG; rename H2 into Hwt.
      inversion_clear HwcG; rename H3 into Hwc.
      assert (Forall (sem_equation G H' (Str.clocks_of ins)) (n_eqs n0)) as Hsem'.
      { destruct Hwt as [_ [_ [_ Hwt]]].
        rewrite HeqH'.
        clear Hin Hout.
        repeat rewrite_Forall_forall.
        specialize (H0 _ H8). specialize (Hwt _ H8).
        eapply sem_equation_restrict in H0...
        unfold idty in H0. rewrite map_map in H0. simpl in H0... } clear H0.
      assert (Forall (sem_equation G' H' (Str.clocks_of ins)) (n_eqs n0)) as Hsem''.
      { destruct Hwt as [_ [_ [_ Hwt']]].
        destruct H5 as [Hwcclocks1 [_ [Hwcclocks Hwc']]].
        assert (sc_var_inv' (idck (n_in n0 ++ n_vars n0 ++ n_out n0)) H' (clocks_of ins)) as Hinv.
        { eapply sc_node_sc_var_inv with (G:=G)...
          rewrite ident_eqb_eq in Hident. eapply inputs_clocked_vars... }
        assert (Permutation (n_in n0 ++ n_out n0 ++ n_vars n0) (n_in n0 ++ n_vars n0 ++ n_out n0)) as Hperm.
        { apply Permutation_app_head, Permutation_app_comm. }
        solve_forall.
        eapply sem_eq_sem_equation. 7,8:eauto. 1-8:eauto.
        + assert (Hndup:=n_nodup n0). repeat rewrite app_assoc in *.
          eapply NoDupMembers_anon_in_eq'...
        + rewrite <- Hperm... }

      eapply normalize_node_sem_equation in Hsem''...
      2:inv HwtG''... 2:inv HwcG''...
      2:{ rewrite ident_eqb_eq in Hident. eapply inputs_clocked_vars...
          destruct H5 as [? _]... }
      destruct Hsem'' as [H'' [Href'' Heqs']].
      eapply Snode with (H:=H''); simpl. 5:reflexivity.
      + rewrite Hident; reflexivity.
      + simpl. repeat rewrite_Forall_forall. eapply sem_var_refines...
      + simpl. repeat rewrite_Forall_forall. eapply sem_var_refines...
      + clear Hin Hout Hdom.
        apply Forall_sem_equation_global_tl'...
        eapply find_node_not_Is_node_in in Hord2...
        simpl. rewrite ident_eqb_refl...
    - specialize (Href f ins outs).
      rewrite ident_eqb_neq in Hident.
      eapply sem_node_cons'...
      apply Href. split. 1:rewrite <- sem_clock_inputs_cons in Hinputs...
      econstructor...
      eapply Forall_impl_In; [| eauto]. intros eq Hin Hsem.
      eapply sem_equation_global_tl...
      eapply find_node_later_not_Is_node_in in Hord1...
      intro Hisin. apply Hord1. rewrite Is_node_in_Exists. rewrite Exists_exists.
      eexists...
  Qed.

  Fact normalize_global_names' : forall G Hwl,
      Forall2 (fun n n' => n_name n = n_name n') G (normalize_global G Hwl).
  Proof.
    intros.
    specialize (Ord.normalize_global_names G Hwl) as Hnames.
    rewrite <- Forall2_eq, Forall2_swap_args in Hnames.
    solve_forall.
  Qed.

  Fact iface_eq_sem_clocks_input : forall G G' f ins,
      global_iface_eq G G' ->
      sem_clock_inputs G f ins ->
      sem_clock_inputs G' f ins.
  Proof.
    intros * Hglob [H [n [Hfind [Hinputs Hsem]]]].
    specialize (Hglob f). rewrite Hfind in Hglob; inv Hglob.
    destruct H2 as (Hname&_&Hins&_).
    exists H. exists sy. repeat split; auto; congruence.
  Qed.

  Lemma normalize_global_refines : forall G Hwl,
      wt_global G ->
      wc_global G ->
      Ordered_nodes G ->
      Forall LCA.node_causal G ->
      global_sem_refines G (normalize_global G Hwl).
  Proof with eauto.
    intros G Hwl. specialize (normalize_global_eq G Hwl) as Heq.
    induction G; intros * Hwt Hwc Hordered Hcaus; simpl.
    - apply global_sem_eq_nil.
    - apply global_sem_eq_cons with (f:=n_name a)...
      + eapply Ord.normalize_global_ordered in Hordered.
        simpl in Hordered...
      + inv Hwt; inv Hwc; inv Hordered; inv Hcaus.
        eapply IHG... eapply normalize_global_eq...
      + intros ins outs Hsem. destruct Hsem as [Hinputs Hsem]. split.
        * eapply iface_eq_sem_clocks_input...
        * eapply normalize_node_eq...
          -- apply normalize_global_names'.
          -- apply normalize_global_eq.
          -- inv Hwt; inv Hwc; inv Hordered; inv Hcaus.
             eapply IHG... eapply normalize_global_eq...
          -- inv Hwt. eapply normalize_global_wt...
          -- inv Hwc. eapply normalize_global_wc...
          -- eapply Ord.normalize_global_ordered in Hordered.
             simpl in Hordered...
          -- admit. (* conservation of causality, TODO *)
  Admitted.

  Theorem normalize_global_sem : forall G Hwl f ins outs,
      wt_global G ->
      wc_global G ->
      Ordered_nodes G ->
      Forall LCA.node_causal G ->
      sem_node G f ins outs ->
      sem_clock_inputs G f ins ->
      sem_node (normalize_global G Hwl) f ins outs.
  Proof.
    intros.
    eapply normalize_global_refines with (Hwl:=Hwl) in H; eauto.
    specialize (H f ins outs) as [_ Hsem]; auto.
  Qed.

End CORRECTNESS.

Module CorrectnessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str : COINDSTREAMS Op OpAux)
       (Syn : LSYNTAX Ids Op)
       (Ty : LTYPING Ids Op Syn)
       (Clo : LCLOCKING Ids Op Syn)
       (LCA        : LCAUSALITY Ids Op Syn)
       (Lord : LORDERED Ids Op Syn)
       (Sem : LSEMANTICS Ids Op OpAux Syn Lord Str)
       (LClockSem : LCLOCKSEMANTICS Ids Op OpAux Syn Ty Clo LCA Lord Str Sem)
       (Norm : FULLNORM Ids Op OpAux Syn)
       <: CORRECTNESS Ids Op OpAux Str Syn Ty Clo LCA Lord Sem LClockSem Norm.
  Include CORRECTNESS Ids Op OpAux Str Syn Ty Clo LCA Lord Sem LClockSem Norm.
  Module Typing := NTypingFun Ids Op OpAux Syn Ty Norm.
  Module Clocking := NClockingFun Ids Op OpAux Syn Clo Norm.
  Module Ordered := NOrderedFun Ids Op OpAux Syn Lord Norm.
End CorrectnessFun.
