From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

Require Import Omega.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LCausality Lustre.LSemantics Lustre.LClockSemantics.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.
From Velus Require Import Lustre.Normalization.NTyping Lustre.Normalization.NClocking.

(** * Correctness of the Normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type CORRECTNESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (LCA        : LCAUSALITY Ids Op OpAux Cks Syn)
       (Import Ty : LTYPING Ids Op OpAux Cks Syn)
       (Import Cl : LCLOCKING Ids Op OpAux Cks Syn)
       (Import Ord : LORDERED Ids Op OpAux Cks Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Cks Syn Ord CStr)
       (Import LCS : LCLOCKSEMANTICS Ids Op OpAux Cks Syn Cl LCA Ord CStr Sem)
       (Import Norm : NORMALIZATION Ids Op OpAux Cks Syn).

  Import Fresh Tactics Unnesting.
  Module Import Typing := NTypingFun Ids Op OpAux Cks Syn Ty Norm.
  Module Import Clocking := NClockingFun Ids Op OpAux Cks Syn Cl Norm.
  Import List.

  CoFixpoint default_stream : Stream svalue :=
    absent ⋅ default_stream.

  Import Permutation.

  Hint Resolve EqStrel_Reflexive clocked_app_refines.

  (** *** Relation between state and history *)

  Definition hist_st (vars : list (ident * clock)) b H st :=
    Env.dom H (map fst vars++st_ids st) /\
    LCS.sc_var_inv (vars++st_clocks st) H b.

  (** *** Correctness of the first pass *)

  Import Unnesting.

  Fact fresh_ident_refines {B} : forall vars H a id (v: Stream svalue) (st st' : fresh_st B) reu,
      st_valid_reuse st (PSP.of_list vars) (PSP.of_list reu) ->
      Env.dom H (vars++reu++st_ids st) ->
      fresh_ident norm1 a st = (id, st') ->
      Env.refines (@EqSt _) H (Env.add id v H).
  Proof with eauto.
    intros * Hvalid Hdom Hfresh.
    assert (st_valid_reuse st' (PSP.of_list vars) (PSP.of_list reu)) as Hvalid' by eauto.
    eapply Env.refines_add...
    intro contra. erewrite Env.dom_use in contra; [| eauto].
    apply in_app_or in contra. destruct contra.
    + eapply Facts.fresh_ident_In in Hfresh.
      assert (In id (st_ids st')).
      { unfold st_ids, idty. repeat simpl_In; simpl in *.
        exists (id, a); auto. }
      apply st_valid_reuse_NoDup in Hvalid'.
      eapply NoDup_app_In in Hvalid'; [|eauto].
      apply Hvalid'; clear Hvalid'.
      apply in_or_app; left.
      rewrite ps_of_list_ps_to_list...
    + apply in_app_or in H0 as [?|?].
      * eapply Facts.fresh_ident_reuse_nIn' in Hfresh; eauto.
        eapply Hfresh, PSP.of_list_1; eauto using Env.Props.O.MO.ListIn_In.
      * eapply Facts.fresh_ident_reuse_nIn in Hfresh; eauto.
  Qed.

  Fact fresh_ident_dom {B V} : forall pref vars H a id (v : V) (st st' : fresh_st B),
      Env.dom H (vars++st_ids st) ->
      fresh_ident pref a st = (id, st') ->
      Env.dom (Env.add id v H) (vars++st_ids st').
  Proof.
    intros * Hdom Hfresh.
    apply Facts.fresh_ident_vars_perm in Hfresh.
    apply Env.dom_add_cons with (x:=id) (v0:=v) in Hdom.
    eapply Env.dom_Permutation; [| eauto].
    symmetry. rewrite Permutation_middle.
    apply Permutation_app_head. assumption.
  Qed.

  Fact fresh_ident_hist_st : forall vars b ty ck id v H st st' reu,
      st_valid_reuse st (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) ->
      sem_clock H b ck (abstract_clock v) ->
      fresh_ident norm1 (ty, ck) st = (id, st') ->
      hist_st (vars++reu) b H st ->
      hist_st (vars++reu) b (Env.add id v H) st'.
  Proof with auto.
    intros * Hvalid Hsem Hfresh [Hdom Hsc].
    assert (~In id (st_ids st)) as Hnin by (eapply Facts.fresh_ident_reuse_nIn in Hfresh; eauto).
    assert (st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu))) as Hvalid2 by eauto.
    assert (Hfresh':=Hfresh). apply fresh_ident_anns in Hfresh'.
    assert (Env.refines (@EqSt _) H (Env.add id v H)) as Href.
    { eapply fresh_ident_refines in Hfresh; eauto.
      rewrite map_app, <-app_assoc in Hdom; auto. }
    repeat split.
    - eapply fresh_ident_dom; eauto.
    - unfold st_clocks, LCS.sc_var_inv in *.
      rewrite Hfresh'; simpl.
      rewrite <- Permutation_middle. constructor.
      + exists v; split.
        * econstructor. eapply Env.add_1. 1,2:reflexivity.
        * eapply LCS.sem_clock_refines; eauto.
      + eapply LCS.sc_var_inv_refines with (H:=H); eauto.
  Qed.

  Fact idents_for_anns_NoDupMembers : forall anns ids st st' aft reu,
      st_valid_reuse st aft reu ->
      idents_for_anns anns st = (ids, st') ->
      NoDupMembers ids.
  Proof.
    intros * Hvalid Hids.
    eapply idents_for_anns_st_valid_reuse in Hvalid; eauto.
    apply idents_for_anns_vars_perm in Hids.
    apply st_valid_reuse_NoDup, NoDup_app_l in Hvalid.
    rewrite fst_NoDupMembers in *.
    rewrite <- Hids in Hvalid.
    apply NoDup_app_l in Hvalid; auto.
  Qed.

  Fact idents_for_anns_nIn : forall anns ids st st' aft reu,
      st_valid_reuse st aft (PSP.of_list reu) ->
      idents_for_anns anns st = (ids, st') ->
      Forall (fun id => ~In id (reu ++ st_ids st)) (map fst ids).
  Proof.
    intros * Hvalid Hids.
    eapply idents_for_anns_st_valid_reuse in Hvalid; eauto.
    apply st_valid_reuse_NoDup in Hvalid.
    apply idents_for_anns_vars_perm in Hids.
    unfold st_ids in *.
    rewrite <- Hids in Hvalid.
    rewrite Forall_forall. intros x Hin.
    rewrite <-app_assoc in Hvalid.
    eapply NoDup_app_In in Hvalid; eauto.
    contradict Hvalid.
    repeat rewrite in_app_iff in *. destruct Hvalid; auto.
    right. right.
    rewrite In_PS_elements, PSP.of_list_1; auto using Env.ME.MO.ListIn_In.
  Qed.

  Fact idents_for_anns_refines : forall vars H anns ids (vs : list (Stream svalue)) st st' reu,
      length vs = length ids ->
      st_valid_reuse st (PSP.of_list vars) (PSP.of_list reu) ->
      Env.dom H (vars++reu++st_ids st) ->
      idents_for_anns anns st = (ids, st') ->
      Env.refines (@EqSt _) H (Env.adds (map fst ids) vs H).
  Proof with eauto.
    intros * Hlen Hvalid Hdom Hids.
    assert (Forall (fun id => ~In id vars) (List.map fst ids)) as Hnvar.
    { assert (st_valid_reuse st' (PSP.of_list vars) (PSP.of_list reu)) by eauto.
      apply idents_for_anns_incl_ids in Hids.
      solve_forall; simpl.
      assert (In i (map fst ids)) by (simpl_In; exists (i, a); eauto).
      apply Hids in H2.
      intro contra.
      eapply st_valid_reuse_NoDup, NoDup_app_In in H0; [|eauto].
      apply H0, in_or_app. left. rewrite ps_of_list_ps_to_list... }
    apply refines_eq_EqSt, Env.refines_adds.
    eapply idents_for_anns_nIn in Hids...
    rewrite Forall_forall in *. intros x1 Hin contra.
    erewrite Env.dom_use in contra...
    rewrite in_app_iff in contra; destruct contra as [?|?].
    + eapply Hnvar...
    + eapply Hids...
  Qed.

  (* Fact idents_for_anns_dom {V} : forall vars H H' anns ids (vs : list V) st st' reu, *)
  (*     length vs = length ids -> *)
  (*     st_valid_reuse st (PSP.of_list vars) (PSP.of_list reu) -> *)
  (*     Env.dom H (vars++reu++st_ids st) -> *)
  (*     idents_for_anns anns st = (ids, st') -> *)
  (*     H' = Env.adds (map fst ids) vs H -> *)
  (*     Env.dom H' (vars++reu++st_ids st'). *)
  (* Proof with eauto. *)
  (*   intros * Hlen Hvalid Hdom Hids Heq. *)
  (*   apply idents_for_anns_vars_perm in Hids. *)
  (*   rewrite Heq. *)
  (*   apply Env.dom_adds with (ids0:=map fst ids) (vs0:=vs) in Hdom. *)
  (*   2:(repeat rewrite_Forall_forall; solve_length). *)
  (*   eapply Env.dom_Permutation; [|eauto]. *)
  (*   symmetry. rewrite Permutation_app_comm, <- app_assoc. apply Permutation_app_head. *)
  (*   rewrite Permutation_app_comm, (Permutation_app_comm reu), app_assoc. *)
  (*   rewrite Hids. apply Permutation_app_comm. *)
  (* Qed. *)

  Fact idents_for_anns_hist_st : forall vars b anns H ids vs st st' reu,
      Forall2 (fun ck v => sem_clock H b ck v) (map clock_of_nclock anns) (map abstract_clock vs) ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) ->
      idents_for_anns anns st = (ids, st') ->
      hist_st (vars++reu) b H st ->
      hist_st (vars++reu) b (Env.adds (map fst ids) vs H) st'.
  Proof.
    setoid_rewrite Forall2_map_1. setoid_rewrite Forall2_map_2.
    induction anns as [|(?&?&?)]; intros * Hcks Hvalid Hids Hhist; inv Hcks;
      repeat inv_bind; simpl; subst; auto.
    rewrite Env.adds_cons.
    eapply IHanns in H1; eauto.
    - eapply Forall2_impl_In; [|eauto]; intros; simpl in *.
      eapply sem_clock_refines; [|eauto].
      eapply fresh_ident_refines; eauto.
      destruct Hhist as (Hdom&_). now rewrite map_app, <-app_assoc in Hdom.
    - eapply fresh_ident_hist_st; eauto.
  Qed.

  Fact reuse_ident_refines : forall H id (v : Stream svalue),
      sem_var H id v ->
      Env.refines (@EqSt _) H (Env.add id v H).
  Proof with eauto.
    intros * Hvar (* Hvalid *).
    inv Hvar.
    eapply Env.refines_find_add_right in H1; eauto.
    rewrite Env.add_Equiv; eauto using EqStrel. reflexivity.
  Qed.

  Fact reuse_ident_dom {B} : forall vars H a id reu v (st st' : fresh_st B),
      Env.dom H (vars++id::reu++st_ids st) ->
      sem_var H id v ->
      reuse_ident id a st = (tt, st') ->
      Env.dom (Env.add id v H) (vars++reu++st_ids st').
  Proof.
    intros * Hdom Hvar Hreu.
    apply Facts.reuse_ident_vars_perm in Hreu.
    rewrite <-Hreu, <-Permutation_middle.
    eapply Env.dom_Equiv_Permutation_Proper; eauto. eapply EqStrel.
    eapply Env.Equiv_orel; intros.
    destruct (ident_eq_dec id x); subst.
    - rewrite Env.gss.
      inv Hvar. rewrite H1. constructor; auto.
    - rewrite Env.gso; auto.
  Defined.

  Fact reuse_ident_hist_st : forall vars b ty ck id v H st st' reu,
      sem_var H id v ->
      reuse_ident id (ty, ck) st = (tt, st') ->
      hist_st (vars++(id, ck)::reu) b H st ->
      hist_st (vars++reu) b (Env.add id v H) st'.
  Proof.
    intros * Hvar Hreu (Hdom&Hsc); simpl in *.
    unfold hist_st, st_ids, st_clocks.
    split.
    - rewrite map_app, <-app_assoc in *; simpl in *.
      eapply reuse_ident_dom; eauto.
    - assert (Hanns:=Hreu). apply reuse_ident_anns in Hanns. rewrite Hanns.
      rewrite <-app_assoc in *; simpl in *.
      unfold sc_var_inv.
      rewrite <-Permutation_middle; auto.
      eapply Forall_impl; [|eauto]; intros (?&?) (vs&?&?).
      exists vs. split; [eapply sem_var_refines|eapply sem_clock_refines]. 2,4:eauto.
      1,2:eapply reuse_ident_refines; eauto.
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
    apply st_valid_reuse_NoDup, NoDup_app_l in Hvalid.
    rewrite fst_NoDupMembers in *.
    rewrite <- Hids in Hvalid.
    apply NoDup_app_l in Hvalid; auto.
  Qed.

  Lemma app_PS_NoDup : forall (xs ys : list ident),
      NoDup (xs ++ ys) ->
      NoDup (xs ++ PSP.to_list (PSP.of_list ys)).
  Proof.
    intros.
    apply NoDup_app'_iff; repeat split; eauto using NoDup_app_l, PS_elements_NoDup.
    eapply Forall_forall; intros.
    eapply NoDup_app_In in H; eauto.
    contradict H.
    rewrite In_PS_elements, PSP.of_list_1 in H.
    apply SetoidList.InA_alt in H as (?&?&?); subst; auto.
  Qed.
  Hint Unfold PSP.to_list.
  Hint Resolve app_PS_NoDup.

  Fact idents_for_anns'_nIn : forall anns ids st st' aft reu,
      NoDup (map fst (Syn.anon_streams anns) ++ reu) ->
      st_valid_reuse st aft (ps_adds (map fst (Syn.anon_streams anns)) (PSP.of_list reu)) ->
      idents_for_anns' anns st = (ids, st') ->
      Forall (fun id => ~In id (reu ++ st_ids st)) (map fst ids).
  Proof.
    intros * Hndup Hvalid Hids.
    eapply idents_for_anns'_st_valid in Hvalid; eauto.
    apply st_valid_reuse_NoDup in Hvalid.
    apply idents_for_anns'_vars_perm in Hids.
    unfold st_ids in *.
    rewrite <- Hids, <-app_assoc in Hvalid.
    rewrite Forall_forall. intros x Hin.
    eapply NoDup_app_In in Hvalid; eauto.
    contradict Hvalid.
    repeat rewrite in_app_iff in *. destruct Hvalid as [?|?]; auto.
    do 2 right.
    rewrite In_PS_elements, PSP.of_list_1; auto using SetoidList.In_InA.
  Qed.

  Fact idents_for_anns'_refines : forall vars bs anns H ids (vs : list (Stream svalue)) st st' reu,
      clocked_app H bs anns vs ->
      NoDup (map fst (Syn.anon_streams anns) ++ reu) ->
      st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (Syn.anon_streams anns)) (PSP.of_list reu)) ->
      Env.dom H (vars ++ (map fst (Syn.anon_streams anns)) ++ reu ++ st_ids st) ->
      idents_for_anns' anns st = (ids, st') ->
      Env.refines (@EqSt _) H (Env.adds (map fst ids) vs H).
  Proof with eauto.
    induction anns as [|(?&?&[|])]; intros * Hck Hnd Hvalid Hdom Hids; inv Hck;
      repeat inv_bind; simpl. reflexivity.
    destruct x; destruct H2 as (Hv&_).
    rewrite <-ps_add_adds_eq in Hvalid.
    1,2:rewrite Env.adds_cons; (etransitivity; [|eapply IHanns with (st:=x0); eauto]).
    - eapply reuse_ident_refines; eauto.
    - eapply Forall2_impl_In; [|eauto]; intros (?&?&[|]) ? _ _ ?; simpl in *; auto.
      destruct H2; split; eauto using sem_var_refines, sem_clock_refines, reuse_ident_refines.
    - inv Hnd; eauto.
    - eapply reuse_ident_st_valid_reuse; eauto.
      inv Hnd. contradict H5.
      apply in_or_app.
      apply ps_adds_spec in H5 as [Hin|Hin]; auto.
      right.
      apply PSP.of_list_1, SetoidList.InA_alt in Hin as (?&?&?); subst; auto.
    - rewrite (app_assoc (map fst _)). eapply reuse_ident_dom; eauto.
      now rewrite <-app_assoc.
    - rewrite ps_adds_of_list_app in Hvalid.
      eapply fresh_ident_refines in H0; eauto.
      rewrite <-app_assoc; auto.
    - rewrite ps_adds_of_list_app in Hvalid.
      eapply Forall2_impl_In; [|eauto]; intros (?&?&[|]) ? _ _ ?; simpl in *; auto.
      destruct H3; split; [eapply sem_var_refines|eapply sem_clock_refines]. 2,4:eauto.
      1,2:eapply fresh_ident_refines in H0; eauto; rewrite <-app_assoc; auto.
    - eapply fresh_ident_dom in H0; eauto.
      do 2 rewrite app_assoc; eauto.
      do 2 rewrite <-app_assoc; auto.
  Qed.

  Fact idents_for_anns'_hist_st : forall vars b anns H ids vs st st' reu,
      clocked_app H b anns vs ->
      Forall2 (fun ck v => sem_clock H b ck v) (map clock_of_nclock anns) (map abstract_clock vs) ->
      NoDup (map fst (Syn.anon_streams anns) ++ map fst reu) ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (Syn.anon_streams anns)) (PSP.of_list (map fst reu))) ->
      idents_for_anns' anns st = (ids, st') ->
      hist_st (vars ++ (idck (Syn.anon_streams anns)) ++ reu) b H st ->
      hist_st (vars++reu) b (Env.adds (map fst ids) vs H) st'.
  Proof.
    setoid_rewrite Forall2_map_2.
    induction anns as [|(?&?&[|])]; intros * Hckapp Hcks Hnd Hvalid Hids Hhist; inv Hckapp; inv Hcks;
      repeat inv_bind; simpl; subst; auto.
    destruct x, H2 as (Hv&Hck). rewrite <-ps_add_adds_eq in Hvalid.
    1,2:rewrite Env.adds_cons.
    1,2:eapply IHanns in H1; eauto.
    - eapply Forall2_impl_In; [|eauto]; intros (?&?&[|]) ? _ _ ?; simpl in *; auto.
      destruct H2. split; [eapply sem_var_refines|eapply sem_clock_refines]. 2,4:eauto.
      1,2:eapply reuse_ident_refines; eauto.
    - eapply Forall2_impl_In; [|eauto]; intros ? ? _ _ ?; simpl in *; auto.
      eapply sem_clock_refines; [|eauto].
      eapply reuse_ident_refines; eauto.
    - inv Hnd; auto.
    - eapply reuse_ident_st_valid_reuse; eauto.
      inv Hnd. contradict H6.
      apply in_or_app.
      apply ps_adds_spec in H6 as [Hin|Hin]; auto.
      right.
      apply PSP.of_list_1, SetoidList.InA_alt in Hin as (?&?&?); subst; auto.
    - eapply reuse_ident_hist_st; eauto.
    - destruct Hhist as (Hdom&_). rewrite map_app, <-app_assoc in Hdom.
      eapply Forall2_impl_In; [|eauto]; intros (?&?&[|]) ? _ _ ?; simpl in *; auto.
      destruct H3. split; [eapply sem_var_refines|eapply sem_clock_refines]. 2,4:eauto.
      1,2:eapply fresh_ident_refines in H0; eauto.
      1,2:rewrite ps_adds_of_list_app in Hvalid; auto.
      1,2:rewrite map_app, map_fst_idck; auto.
    - destruct Hhist as (Hdom&_). rewrite map_app, <-app_assoc in Hdom.
      eapply Forall2_impl_In; [|eauto]; intros ? ? _ _ ?; simpl in *; auto.
      eapply sem_clock_refines; [|eauto].
      eapply fresh_ident_refines in H0; eauto.
      rewrite ps_adds_of_list_app in Hvalid; auto.
      rewrite map_app, map_fst_idck; auto.
    - eapply fresh_ident_hist_st; eauto.
      rewrite ps_adds_of_list_app in Hvalid; auto.
      rewrite map_app, map_fst_idck; auto.
  Qed.

  Ltac solve_incl :=
    repeat unfold idty; repeat unfold idck;
    match goal with
    | Hiface : global_iface_eq ?G1 ?G2, H : wt_clock (enums ?G1) _ ?ck |- wt_clock (enums ?G2) _ ?ck =>
      eapply iface_eq_wt_clock; eauto
    | H : wc_clock ?l1 ?ck |- wc_clock ?l2 ?ck =>
      eapply wc_clock_incl; [| eauto]
    | Hiface : global_iface_eq ?G1 ?G2, H : wt_nclock (enums ?G1) _ ?ck |- wt_nclock (enums ?G2) _ ?ck =>
      eapply iface_eq_wt_nclock; eauto
    | H : wt_nclock ?l1 ?ck |- wt_nclock ?l2 ?ck =>
      eapply wt_nclock_incl; [| eauto]
    | Hiface : global_iface_eq ?G1 ?G2, H : wt_exp ?G1 _ ?e |- wt_exp ?G2 _ ?e =>
      eapply iface_eq_wt_exp; eauto
    | H : wt_exp ?G ?l1 ?e |- wt_exp ?G ?l2 ?e =>
      eapply wt_exp_incl; [| eauto]
    | H : wc_exp ?G ?l1 ?e |- wc_exp ?G ?l2 ?e =>
      eapply wc_exp_incl; [| eauto]
    | H : wt_equation ?G ?l1 ?eq |- wt_equation ?G ?l2 ?eq =>
      eapply wt_equation_incl; [| eauto]
    | H : wt_block ?G ?l1 ?eq |- wt_block ?G ?l2 ?eq =>
      eapply wt_block_incl; [| eauto]
    | H : wc_equation ?G ?l1 ?eq |- wc_equation ?G ?l2 ?eq =>
      eapply wc_equation_incl; [| eauto]
    | H : wc_block ?G ?l1 ?eq |- wc_block ?G ?l2 ?eq =>
      eapply wc_block_incl; [| eauto]
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
    (* | |- incl (st_vars ?st1) (st_vars _) => *)
    (*   eapply st_follows_vars_incl; repeat solve_st_follows *)
    | |- incl (st_tys ?st1) (st_tys _) =>
      eapply st_follows_tys_incl; repeat solve_st_follows
    | |- incl (st_clocks ?st1) (st_clocks _) =>
      eapply st_follows_clocks_incl; repeat solve_st_follows
    end; auto.

  Section unnest_node_sem.
    Variable G1 : @global elab_prefs.
    Variable G2 : @global norm1_prefs.

    Hypothesis HwcG1 : wc_global G1.
    Hypothesis HwcG2 : wc_global G2.
    Hypothesis Hifaceeq : global_iface_eq G1 G2.

    Hint Resolve iface_eq_wc_exp.

    (** ** Conservation of sem_exp *)

    (** Helper lemmas *)
    Lemma ps_adds_rw_1 {A B} : forall (xs ys : list (ident * (A * B))) (zs : list (ident * B)),
        PS.Equal (ps_adds (map fst (xs ++ ys)) (PSP.of_list (map fst zs)))
                 (ps_adds (map fst xs) (PSP.of_list (map fst (idck ys ++ zs)))).
    Proof.
      intros.
      rewrite 2 map_app, map_fst_idck, ps_adds_app, <- 2 ps_from_list_ps_of_list.
      unfold ps_from_list.
      now rewrite ps_adds_app.
    Qed.

    Lemma ps_adds_rw_2 {A B} : forall (xs : list (ident * (A * B))) (zs : list (ident * B)),
        PS.Equal (PSP.of_list (map fst (idck xs ++ zs)))
                 (ps_adds (map fst xs) (PSP.of_list (map fst zs))).
    Proof.
      intros.
      rewrite map_app, map_fst_idck, <- 2 ps_from_list_ps_of_list.
      unfold ps_from_list.
      now rewrite ps_adds_app.
    Qed.

    Fact unnest_reset_sem : forall vars b e H v e' eqs' st st' reu,
        (forall e' eqs' st',
            unnest_exp G1 true e st = ([e'], eqs', st') ->
            exists H',
              Env.refines (@EqSt _) H H' /\
              st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
              hist_st (vars++reu) b H' st' /\
              sem_exp_ck G2 H' b e' [v] /\ Forall (sem_equation_ck G2 H' b) eqs')  ->
        wc_exp G1 (vars++st_clocks st) e ->
        numstreams e = 1 ->
        sem_exp_ck G1 H b e [v] ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_in e)) (PSP.of_list (map fst reu))) ->
        hist_st (vars++idck (fresh_in e)++reu) b H st ->
        unnest_reset (unnest_exp G1 true) e st = (e', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
            hist_st (vars++reu) b H' st' /\
            sem_exp_ck G2 H' b e' [v] /\
            Forall (sem_equation_ck G2 H' b) eqs').
    Proof with eauto.
      intros * Hun Hwc Hnum Hsem Hvalid Histst Hnorm.
      unnest_reset_spec; simpl in *.
      1,2:assert (length l = 1) by (eapply unnest_exp_length in Hk0; eauto; congruence).
      1,2:singleton_length.
      - specialize (Hun _ _ _ eq_refl) as (H'&Href&Hval&Histst1&Hsem1&Hsem2).
        exists H'. repeat (split; eauto).
      - specialize (Hun _ _ _ eq_refl) as (H'&Href&Hval&Histst1&Hsem1&Hsem2).
        assert (Href':=Hfresh); eapply fresh_ident_refines in Href'; eauto.
        2:(destruct Histst1 as (Hdom1&_); ndup_simpl; eauto).
        exists (Env.add x2 v H'). split;[|split;[|split;[|split]]]; eauto.
        + etransitivity; eauto.
        + eapply fresh_ident_hist_st in Hfresh; eauto.
          eapply unnest_exp_annot in Hk0; eauto.
          rewrite <-length_annot_numstreams, <-Hk0 in Hnum. simpl in Hnum; rewrite app_nil_r in Hnum.
          singleton_length.
          eapply sc_exp in Hsem; eauto.
          2:destruct Histst; eapply Forall_incl; eauto.
          rewrite clockof_annot, <-Hk0 in Hsem. inv Hsem.
          eapply sem_clock_refines; eauto.
        + repeat constructor.
          econstructor. eapply Env.add_1. 1,2:reflexivity.
        + constructor.
          eapply Seq with (ss:=[[v]]); simpl.
          1,2:repeat constructor.
          * eapply sem_exp_refines; eauto.
          * econstructor. eapply Env.add_1. 1,2:reflexivity.
          * solve_forall.
            eapply sem_equation_refines; eauto.
    Qed.

    Corollary unnest_resets_sem : forall vars b es H vs es' eqs' st st' reu,
        NoDup (map fst (fresh_ins es)++map fst reu) ->
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        Forall (fun e => numstreams e = 1) es ->
        Forall2 (fun e v => sem_exp_ck G1 H b e [v]) es vs ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_ins es)) (PSP.of_list (map fst reu))) ->
        hist_st (vars++idck (fresh_ins es)++reu) b H st ->
        Forall2 (fun e v => forall H e' eqs' st st' reu,
                     NoDup (map fst (fresh_in e)++map fst reu) ->
                     wc_exp G1 (vars++st_clocks st) e ->
                     sem_exp_ck G1 H b e [v] ->
                     st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_in e)) (PSP.of_list (map fst reu))) ->
                     hist_st (vars++idck (fresh_in e)++reu) b H st ->
                     unnest_exp G1 true e st = ([e'], eqs', st') ->
                     (exists H',
                         Env.refines (@EqSt _) H H' /\
                         st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
                         hist_st (vars++reu) b H' st' /\
                         sem_exp_ck G2 H' b e' [v] /\
                         Forall (sem_equation_ck G2 H' b) eqs')) es vs ->
        mmap2 (unnest_reset (unnest_exp G1 true)) es st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
            hist_st (vars++reu) b H' st' /\
            Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es' vs /\
            Forall (sem_equation_ck G2 H' b) (concat eqs')).
    Proof with eauto.
      induction es; intros * Hndup Hwt Hnum Hsem Hvalid Histst Hf Hmap;
        inv Hwt; inv Hnum; inv Hsem; inv Hf; repeat inv_bind.
      - exists H; simpl. repeat (split; eauto).
      - unfold fresh_ins in *; simpl in *. rewrite ps_adds_rw_1 in Hvalid.
        assert (NoDup (map fst (fresh_ins es)++map fst reu)) as Hndup2 by ndup_r Hndup.
        assert (Hr:=H0). eapply unnest_reset_sem in H0 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1'); eauto.
        3:rewrite idck_app, <-app_assoc in Histst...
        2:{ intros. eapply H9 in H7; eauto. ndup_simpl...
            rewrite idck_app, <-app_assoc in Histst... }
        rewrite ps_adds_rw_2 in Hvalid1.
        assert (Forall2 (fun e v => sem_exp_ck G1 H' b e [v]) es l') as Hsem'.
        { eapply Forall2_impl_In; [|eapply H8]; intros. eapply sem_exp_refines... }
        eapply IHes in H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]...
        2:solve_forall; repeat solve_incl.
        clear IHes H9.
        exists H''. repeat (split; eauto).
        + etransitivity...
        + constructor; eauto. subst.
          eapply sem_exp_refines; eauto.
        + apply Forall_app. split...
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
    Hint Constructors Forall3.

    Fact unnest_arrow_sem : forall H bs e0s es anns s0s ss os,
        length e0s = length anns ->
        length es = length anns ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) e0s s0s ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) es ss ->
        Forall3 (fun s0 s o => arrow s0 s o) s0s ss os ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) (unnest_arrow e0s es anns) os.
    Proof with eauto.
      intros * Hlen1 Hlen2 Hsem1 Hsem2 Hfby.
      unfold unnest_arrow.
      repeat rewrite_Forall_forall. solve_length.
      repeat simpl_length. repeat simpl_nth. Unshelve. 2:exact ((hd_default [], hd_default []), default_ann).
      destruct (nth n (combine _ _)) as [[e0 e] ?] eqn:Hnth. repeat simpl_nth.
      econstructor... 1-2:econstructor...
      Unshelve. 1-2:exact default_stream.
    Qed.

    Fact unnest_fby_sem : forall H bs e0s es anns s0s ss os,
        length e0s = length anns ->
        length es = length anns ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) e0s s0s ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) es ss ->
        Forall3 (fun s0 s o => fby s0 s o) s0s ss os ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) (unnest_fby e0s es anns) os.
    Proof with eauto.
      intros * Hlen1 Hlen2 Hsem1 Hsem2 Hfby.
      unfold unnest_fby.
      repeat rewrite_Forall_forall. 1:solve_length.
      repeat simpl_length. repeat simpl_nth. Unshelve. 2:exact ((hd_default [], hd_default []), default_ann).
      destruct (nth n (combine _ _)) as [[e0 e] ?] eqn:Hnth. repeat simpl_nth.
      econstructor... 1-2:econstructor...
      Unshelve. 1-2:exact default_stream.
    Qed.

    Fact unnest_when_sem : forall H bs es tys ckid b ck s ss os,
        length es = length tys ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) es ss ->
        sem_var H ckid s ->
        Forall2 (fun s' => when b s' s) ss os ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) (unnest_when ckid b es tys ck) os.
    Proof with eauto.
      intros * Hlen Hsem Hvar Hwhen.
      unfold unnest_when. simpl_forall.
      repeat rewrite_Forall_forall. 1:congruence.
      eapply Swhen with (ss0:=[[nth n ss default_stream]])...
      - repeat constructor...
        eapply H1... congruence.
    Qed.

    Fact unnest_merge_sem : forall H bs tys x tx es ck s vs os,
        es <> [] ->
        Forall (fun es => length es = length tys) es ->
        sem_var H x s ->
        Forall2 (Forall2 (fun e s => sem_exp_ck G2 H bs e [s])) es vs ->
        Forall2Transpose (merge s) vs os ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) (unnest_merge (x, tx) es tys ck) os.
    Proof with eauto.
      induction tys; intros * Hnnil Hlen Hvar Hsem Hmerge; simpl in *; auto.
      - assert (Forall (fun vs => length vs = 0) vs) as Hlen'.
        { clear - Hsem Hlen. eapply Forall2_ignore1 in Hsem.
          eapply Forall_impl; [|eauto]. intros ? (?&?&Hf).
          eapply Forall2_length in Hf.
          eapply Forall_forall in Hlen; eauto. congruence. }
        inv Hmerge; auto.
        exfalso. inv Hsem; try congruence. inv H0. inv Hlen'.
        destruct y; simpl in *; congruence.
      - assert (Forall (fun vs => length vs = S (length tys)) vs) as Hlen'.
        { clear - Hsem Hlen. eapply Forall2_ignore1 in Hsem.
          eapply Forall_impl; [|eauto]. intros ? (?&?&Hf).
          eapply Forall2_length in Hf.
          eapply Forall_forall in Hlen; eauto. congruence. }
        inv Hmerge; try congruence.
        + exfalso. inv Hsem; try congruence. inv H0. inv Hlen'.
          simpl in *; congruence.
        + constructor; eauto.
          * eapply Smerge with (vs0:=List.map (fun x => [[x]]) hd1); eauto.
            -- rewrite Forall2_map_1, Forall2_map_2.
               eapply Forall2_trans_ex in H0; [|eauto].
               eapply Forall2_impl_In; [|eauto]; intros ?? Hin1 Hin2 (?&Hin3&Hf&Hhd).
               inv Hf; simpl in *; inv Hhd.
               constructor; auto.
            -- econstructor; eauto.
               ++ rewrite map_map, Forall2_map_1.
                  apply Forall2_same; simpl. eapply Forall_forall; intuition.
               ++ constructor; auto.
                  rewrite map_map, map_map, Forall_map; simpl.
                  eapply Forall_forall; intuition.
          * eapply IHtys; eauto.
            -- contradict Hnnil. eauto using map_eq_nil.
            -- clear - Hlen. rewrite Forall_map.
               eapply Forall_impl; eauto; intros.
               destruct a; simpl in *; auto. inv H.
            -- clear - Hsem. rewrite Forall2_map_1, Forall2_map_2.
               eapply Forall2_impl_In; [|eauto]. intros ?? _ _ ?.
               inv H0; simpl; auto.
    Qed.

    Fact unnest_case_sem : forall H bs tys e es d ck s vs vd os,
        es <> [] ->
        Forall (LiftO True (fun es => length es = length tys)) es ->
        length d = length tys ->
        sem_exp_ck G2 H bs e [s] ->
        Forall2 (fun oes vs0 => forall es0, oes = Some es0 -> Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) es0 vs0) es vs ->
        Forall2 (fun oes vs0 => oes = None -> EqSts vs0 vd) es vs ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) d vd ->
        Forall2Transpose (case s) vs os ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) (unnest_case e es d tys ck) os.
    Proof with eauto.
      induction tys; intros * Hnnil Hlen1 Hlen2 Hcond Hsome Hnone Hsemd Hcase; simpl in *; auto.
      - assert (Forall (fun vs => length vs = 0) vs) as Hlen'.
        { clear - Hsome Hnone Hsemd Hlen1 Hlen2.
          eapply Forall2_Forall2 in Hsome; eauto. clear Hnone.
          eapply Forall2_ignore1 in Hsome.
          eapply Forall_impl; [|eauto]. intros ? (?&?&(Hn&Hs)).
          destruct x.
          - eapply Forall2_length in Hs; eauto.
            eapply Forall_forall in Hlen1; eauto; simpl in *. congruence.
          - eapply Forall2_length in Hn; eauto. eapply Forall2_length in Hsemd; eauto.
            congruence.
        }
        inv Hcase; auto.
        exfalso. inv Hsome; try congruence. inv H0. inv Hlen'.
        destruct y; simpl in *; congruence.
      - assert (Forall (fun vs => length vs = S (length tys)) vs) as Hlen'.
        { clear - Hsome Hnone Hsemd Hlen1 Hlen2.
          eapply Forall2_Forall2 in Hsome; eauto. clear Hnone.
          eapply Forall2_ignore1 in Hsome.
          eapply Forall_impl; [|eauto]. intros ? (?&?&(Hn&Hs)).
          destruct x.
          - eapply Forall2_length in Hs; eauto.
            eapply Forall_forall in Hlen1; eauto; simpl in *. congruence.
          - eapply Forall2_length in Hn; eauto. eapply Forall2_length in Hsemd; eauto.
            congruence.
        }
        destruct d; simpl in *; inv Hlen2.
        inv Hcase; try congruence.
        + exfalso. inv Hsome; try congruence. inv H0. inv Hlen'.
          simpl in *; congruence.
        + constructor; eauto.
          * inv Hsemd.
            eapply Scase with (vs0:=List.map (fun x => [[x]]) hd1); eauto.
            -- clear - H0 Hsome.
               rewrite Forall2_map_1, Forall2_map_2.
               eapply Forall2_trans_ex in H0; [|eauto].
               eapply Forall2_impl_In; [|eauto]; intros ?? Hin1 Hin2 (?&Hin3&Hf&Hhd) ? Hopt.
               eapply option_map_inv in Hopt as (?&?&Heq); subst.
               specialize (Hf _ eq_refl).
               inv Hf; simpl in *; inv Hhd.
               constructor; auto.
            -- clear - H0 Hnone.
               rewrite Forall2_map_1, Forall2_map_2.
               eapply Forall2_trans_ex in H0; [|eauto].
               eapply Forall2_impl_In; [|eauto]; intros ?? Hin1 Hin2 (?&Hin3&Hf&Hhd) Hopt.
               eapply option_map_inv_None in Hopt; subst.
               specialize (Hf eq_refl).
               inv Hf; simpl in *; inv Hhd.
               do 2 constructor; auto.
            -- econstructor; eauto.
               ++ rewrite map_map, Forall2_map_1.
                  apply Forall2_same; simpl. eapply Forall_forall; intuition.
               ++ constructor; auto.
                  rewrite map_map, map_map, Forall_map; simpl.
                  eapply Forall_forall; intuition.
          * inv Hsemd. eapply IHtys; eauto.
            -- contradict Hnnil. eauto using map_eq_nil.
            -- clear - Hlen1. rewrite Forall_map.
               eapply Forall_impl; eauto; intros.
               destruct a; simpl in *; auto.
               destruct l; simpl in *; auto. inv H.
            -- clear - Hsome. rewrite Forall2_map_1, Forall2_map_2.
               eapply Forall2_impl_In; [|eauto]. intros ?? _ _ Hf ? Hopt.
               eapply option_map_inv in Hopt as (?&?&?); subst.
               specialize (Hf _ eq_refl).
               inv Hf; simpl; auto.
            -- clear - Hnone. rewrite Forall2_map_1, Forall2_map_2.
               eapply Forall2_impl_In; [|eauto]. intros ?? _ _ Hf Hopt.
               eapply option_map_inv_None in Hopt; subst.
               specialize (Hf eq_refl).
               inv Hf; simpl; auto.
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

    Fact mmap2_sem : forall vars b is_control es H vs es' eqs' st st' reu,
        NoDup (map fst (fresh_ins es)++map fst reu) ->
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        Forall2 (sem_exp_ck G1 H b) es vs ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_ins es)) (PSP.of_list (map fst reu))) ->
        hist_st (vars++idck (fresh_ins es)++reu) b H st ->
        Forall
          (fun e => forall H vs is_control es' eqs' st st' reu,
               NoDup (map fst (fresh_in e) ++ map fst reu) ->
               wc_exp G1 (vars++st_clocks st) e ->
               sem_exp_ck G1 H b e vs ->
               st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_in e)) (PSP.of_list (map fst reu))) ->
               hist_st (vars++idck (fresh_in e)++reu) b H st ->
               unnest_exp G1 is_control e st = (es', eqs', st') ->
               exists H' : Env.t (Stream svalue),
                 Env.refines (@EqSt _) H H' /\
                 st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
                 hist_st (vars++reu) b H' st' /\
                 Forall2 (fun (e0 : exp) (v : Stream svalue) => sem_exp_ck G2 H' b e0 [v]) es' vs /\
                 Forall (sem_equation_ck G2 H' b) eqs') es ->
        mmap2 (unnest_exp G1 is_control) es st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
            hist_st (vars++reu) b H' st' /\
            Forall2 (fun es vs => Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es vs) es' vs /\
            Forall (sem_equation_ck G2 H' b) (concat eqs')).
    Proof with eauto.
      induction es; intros * Hndup Hwc Hsem Hvalid Histst Hf Hmap;
        inv Hwc; inv Hsem; inv Hf; repeat inv_bind.
      - exists H; simpl. repeat (split; eauto).
      - unfold fresh_ins in *; simpl in *; rewrite ps_adds_rw_1 in Hvalid.
        assert (NoDup (map fst (fresh_ins es)++ (map fst reu))) as Hndup2 by ndup_r Hndup.
        assert (Hun1:=H0). eapply H5 in H0 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1'); eauto.
        2:ndup_simpl...
        2:rewrite idck_app, <-app_assoc in Histst; auto.
        assert (Forall2 (sem_exp_ck G1 H' b) es l') as Hsem'.
        { eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines... }
        rewrite ps_adds_rw_2 in Hvalid1.
        eapply IHes in H1 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2'); eauto.
        2:(solve_forall; repeat solve_incl).
        clear IHes H7.
        exists H''. repeat (split; eauto).
        + etransitivity...
        + constructor; eauto. subst.
          assert (length x = numstreams a) as Hlength1 by (eapply unnest_exp_length; eauto).
          assert (length y = numstreams a) as Hlength2 by (eapply sem_exp_numstreams, sem_exp_ck_sem_exp; eauto).
          solve_forall.
          eapply sem_exp_refines; eauto.
        + apply Forall_app. split...
          solve_forall. eapply sem_equation_refines...
    Qed.

    Fact mmap2_mmap2_sem : forall vars b is_control es H vs es' eqs' st st' reu,
        NoDup (map fst (flat_map fresh_ins es)++map fst reu) ->
        Forall (Forall (wc_exp G1 (vars++st_clocks st))) es ->
        Forall2 (Forall2 (sem_exp_ck G1 H b)) es vs ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (flat_map fresh_ins es)) (PSP.of_list (map fst reu))) ->
        hist_st (vars++idck (flat_map fresh_ins es)++reu) b H st ->
        Forall
          (Forall
             (fun e => forall H vs is_control es' eqs' st st' reu,
                  NoDup (map fst (fresh_in e) ++ map fst reu) ->
                  wc_exp G1 (vars++st_clocks st) e ->
                  sem_exp_ck G1 H b e vs ->
                  st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_in e)) (PSP.of_list (map fst reu))) ->
                  hist_st (vars++idck (fresh_in e)++reu) b H st ->
                  unnest_exp G1 is_control e st = (es', eqs', st') ->
                  exists H' : Env.t (Stream svalue),
                    Env.refines (@EqSt _) H H' /\
                    st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
                    hist_st (vars++reu) b H' st' /\
                    Forall2 (fun e0 v => sem_exp_ck G2 H' b e0 [v]) es' vs /\
                    Forall (sem_equation_ck G2 H' b) eqs')) es ->
        mmap2 (fun es => bind2 (mmap2 (unnest_exp G1 is_control) es) (fun es0 eqs => ret (concat es0, concat eqs))) es st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
            hist_st (vars++reu) b H' st' /\
            Forall2 (fun es vs => Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es vs) es' (List.map (@concat _) vs) /\
            Forall (sem_equation_ck G2 H' b) (concat eqs')).
    Proof with eauto.
      induction es; intros * Hndup Hwc Hsem Hvalid Histst Hf Hmap;
        inv Hwc; inv Hsem; inv Hf; repeat inv_bind.
      - exists H; simpl. repeat (split; eauto).
      - unfold fresh_ins in *; simpl in *. rewrite ps_adds_rw_1 in Hvalid.
        assert (NoDup (map fst (flat_map fresh_ins es)++map fst reu)) as Hndup2 by ndup_r Hndup.
        eapply mmap2_sem in H5 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1'); eauto.
        2:ndup_simpl...
        2:rewrite idck_app, <-app_assoc in Histst; auto.
        assert (Forall2 (Forall2 (sem_exp_ck G1 H' b)) es l') as Hsem'.
        { do 2 (eapply Forall2_impl_In; [|eauto]; intros ?? _ _ ?). eapply sem_exp_refines... }
        rewrite ps_adds_rw_2 in Hvalid1.
        eapply IHes in H1 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2')...
        2:(solve_forall; solve_forall; repeat solve_incl).
        clear IHes H7.
        exists H''. repeat (split; eauto).
        + etransitivity...
        + constructor; eauto. subst.
          eapply Forall2_concat.
          do 2 (eapply Forall2_impl_In; [|eauto]; intros).
          eapply sem_exp_refines...
        + apply Forall_app. split...
          solve_forall. eapply sem_equation_refines...
    Qed.

    Fact mmap2_mmap2_sem' : forall vars b is_control brs H vs es' eqs' st st' reu,
        NoDup (map fst (flat_map (or_default_with [] fresh_ins) brs)++map fst reu) ->
        (forall es, In (Some es) brs -> Forall (wc_exp G1 (vars++st_clocks st)) es) ->
        Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (sem_exp_ck G1 H b) es vs) brs vs ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (flat_map (or_default_with [] fresh_ins) brs)) (PSP.of_list (map fst reu))) ->
        hist_st (vars++idck (flat_map (or_default_with [] fresh_ins) brs)++reu) b H st ->
        Forall
        (LiftO True
           (Forall
              (fun e => forall H vs is_control es' eqs' st st' reu,
               NoDup (map fst (fresh_in e) ++ map fst reu) ->
               wc_exp G1 (vars++st_clocks st) e ->
               sem_exp_ck G1 H b e vs ->
               st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_in e)) (PSP.of_list (map fst reu))) ->
               hist_st (vars++idck (fresh_in e)++reu) b H st ->
               unnest_exp G1 is_control e st = (es', eqs', st') ->
               exists H' : Env.t (Stream svalue),
                 Env.refines (@EqSt _) H H' /\
                 st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
                 hist_st (vars++reu) b H' st' /\
                 Forall2 (fun e0 v => sem_exp_ck G2 H' b e0 [v]) es' vs /\
                 Forall (sem_equation_ck G2 H' b) eqs'))) brs ->
        mmap2
          (or_default_with
             (ret (None, []))
             (fun es => bind2
                       (bind2 (mmap2 (unnest_exp G1 is_control) es) (fun es0 eqs => ret (concat es0, concat eqs)))
               (fun (es' : list exp) (eqs' : list equation) => ret (Some es', eqs')))) brs st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
            hist_st (vars++reu) b H' st' /\
            Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es vs) es'
                    (List.map (@concat _) vs) /\
            Forall (sem_equation_ck G2 H' b) (concat eqs')).
    Proof with eauto.
      induction brs; intros * Hndup Hwc Hsem Hvalid Histst Hf Hmap;
        inv Hsem; inv Hf; repeat inv_bind.
      - exists H; simpl. repeat (split; eauto).
      - unfold fresh_ins in *; simpl in *.
        assert (NoDup (map fst (flat_map (or_default_with [] fresh_ins) brs)++ (map fst reu))) as Hndup2 by ndup_r Hndup.
        destruct a; simpl in *; repeat inv_bind; simpl.
        + rewrite ps_adds_rw_1 in Hvalid.
          eapply mmap2_sem in H3 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1'); eauto.
          2:ndup_simpl...
          2:rewrite idck_app, <-app_assoc in Histst; auto.
          assert (Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (sem_exp_ck G1 H' b) es vs) brs l') as Hsem'.
          { clear - H4 Href1.
            eapply Forall2_impl_In; [|eauto]; intros; subst.
            specialize (H2 _ eq_refl). eapply Forall2_impl_In; [|eauto]; intros.
            eapply sem_exp_refines... }
          rewrite ps_adds_rw_2 in Hvalid1.
          eapply IHbrs in H1 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2')...
          2:intros ? Hin; specialize (Hwc _ (or_intror Hin)); solve_forall; repeat solve_incl.
          clear IHbrs H5.
          exists H''. repeat (split; eauto).
          * etransitivity...
          * constructor; eauto. intros ? Heq; inv Heq.
            eapply Forall2_concat.
            do 2 (eapply Forall2_impl_In; [|eauto]; intros).
            eapply sem_exp_refines...
          * apply Forall_app. split...
            solve_forall. eapply sem_equation_refines...
        + eapply IHbrs in H1 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2')...
          clear IHbrs H5.
          exists H''. repeat (split; eauto).
          constructor; auto. intros ? Heq; inv Heq.
    Qed.

    (* Lemma sc_exp :  *)

    Lemma unnest_noops_exp_sem : forall vars b cki e H v e' eqs' st st' reu,
        st_valid_reuse st (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) ->
        hist_st (vars++reu) b H st ->
        wc_exp G2 (vars++st_clocks st) e ->
        numstreams e = 1 ->
        sem_exp_ck G2 H b e [v] ->
        unnest_noops_exp cki e st = (e', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
            hist_st (vars++reu) b H' st' /\
            sem_exp_ck G2 H' b e' [v] /\
            Forall (sem_equation_ck G2 H' b) eqs').
    Proof.
      unfold unnest_noops_exp.
      intros * Hvalid Hdom Hwc Hnum Hsem Hunt.
      rewrite <-length_annot_numstreams in Hnum. singleton_length.
      destruct p as (?&?&?).
      destruct (is_noops_exp _ _); repeat inv_bind.
      - exists H; auto.
      - assert (Hfresh:=H0).
        assert (Env.refines (EqSt (A:=svalue)) H (Env.add x v H)) as Href.
        { eapply fresh_ident_refines; eauto.
          destruct Hdom as (Hdom&_); auto.
          rewrite map_app, <-app_assoc in Hdom; auto. }
        exists (Env.add x v H). split;[|split;[|split;[|split]]]; auto.
        + eapply fresh_ident_st_valid_reuse; eauto.
        + eapply fresh_ident_hist_st; eauto.
          eapply sc_exp in Hsem; eauto.
          rewrite clockof_annot, Hsingl in Hsem; inv Hsem; eauto.
          destruct Hdom. eapply Forall_incl; eauto.
        + constructor. econstructor.
          eapply Env.add_1. 1,2:reflexivity.
        + constructor; auto.
          apply Seq with (ss:=[[v]]); simpl.
          * constructor; auto. eapply sem_exp_refines; eauto.
          * constructor; auto. econstructor.
            eapply Env.add_1. 1,2:reflexivity.
    Qed.

    Lemma unnest_noops_exps_sem : forall vars b cks es H vs es' eqs' st st' reu,
        length es = length cks ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) ->
        hist_st (vars++reu) b H st ->
        Forall (wc_exp G2 (vars++st_clocks st)) es ->
        Forall (fun e => numstreams e = 1) es ->
        Forall2 (fun e v => sem_exp_ck G2 H b e [v]) es vs ->
        unnest_noops_exps cks es st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
            hist_st (vars++reu) b H' st' /\
            Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es' vs /\
            Forall (sem_equation_ck G2 H' b) eqs').
    Proof.
      unfold unnest_noops_exps.
      induction cks; intros * Hlen Hvalid Hdom Hwc Hck Hsem Hunt; repeat inv_bind; simpl; auto.
      1,2:destruct es; simpl in *; inv Hlen; repeat inv_bind.
      - inv Hsem. exists H. auto.
      - inv Hsem. inv Hwc. inv Hck.
        assert (Hnoops:=H0). eapply unnest_noops_exp_sem in H0 as (H'&?&?&?&?&?); eauto.
        assert (Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es l') as Hsem'.
        { eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines; eauto. }
        eapply IHcks with (st:=x2) in Hsem' as (H''&?&?&?&?&?); eauto.
        2:solve_forall; repeat solve_incl; eauto using unnest_noops_exp_st_follows.
        2:inv_bind; repeat eexists; eauto; inv_bind; eauto.
        exists H''. split;[|split;[|split;[|split]]]; eauto.
        + etransitivity; eauto.
        + constructor; eauto.
          eapply sem_exp_refines; eauto.
        + simpl. rewrite Forall_app; split; auto.
          solve_forall. eapply sem_equation_refines; eauto.
    Qed.

    Hypothesis HGref : global_sem_refines G1 G2.

    Hint Resolve sem_ref_sem_exp clocked_app_refines.
    Hint Constructors sem_exp_ck.

    Fact unnest_exp_sem : forall vars b e H vs is_control es' eqs' st st' reu,
        NoDup (map fst (fresh_in e) ++ map fst reu) ->
        wc_exp G1 (vars++st_clocks st) e ->
        sem_exp_ck G1 H b e vs ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_in e)) (PSP.of_list (map fst reu))) ->
        hist_st (vars++idck (fresh_in e)++reu) b H st ->
        unnest_exp G1 is_control e st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
            hist_st (vars++reu) b H' st' /\
            Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es' vs /\
            Forall (sem_equation_ck G2 H' b) eqs').
    Proof with eauto.
      induction e using exp_ind2; intros * Hndup Hwc Hsem Hvalid Histst Hnorm; repeat inv_bind. 11:inv Hwc; inv Hsem.
      - (* const *)
        inv Hsem. exists H. repeat (split; auto).
      - (* enum *)
        inv Hsem. exists H. repeat (split; auto).
      - (* var *)
        inv Hsem. exists H. repeat (split; auto).
      - (* unop *)
        inv Hsem. inv Hwc.
        assert (Htypeof:=H0). eapply unnest_exp_typeof in Htypeof...
        assert (Hnorm:=H0). eapply IHe in Hnorm as [H' [Href1 [Hvalid1 [Hhistst1 [Hsem1 Hsem1']]]]]...
        eapply unnest_exp_length in H0... rewrite <-length_clockof_numstreams, H5 in H0. singleton_length.
        inv Hsem1.
        exists H'. repeat (split; eauto).
        repeat econstructor... congruence.
      - (* binop *)
        inv Hsem; inv Hwc.
        simpl in *. rewrite ps_adds_rw_1 in Hvalid.
        assert (Htypeof1:=H0). eapply unnest_exp_typeof in Htypeof1...
        assert (Htypeof2:=H1). eapply unnest_exp_typeof in Htypeof2...
        assert (NoDup (map fst (fresh_in e1) ++ PS.elements (ps_adds (map fst (fresh_in e2)) (PSP.of_list (map fst reu))))) as Hndup1.
        { rewrite Permutation_PS_elements_ps_adds'. ndup_simpl...
          rewrite app_assoc in *...
          ndup_r Hndup. }
        assert (Hun1:=H0). eapply IHe1 in H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]... clear IHe1.
        2:ndup_simpl...
        2:rewrite idck_app, <-app_assoc in Histst; auto.
        eapply sem_exp_refines in H10; eauto.
        assert (NoDup (map fst (fresh_in e2) ++ (map fst reu))) as Hndup2 by ndup_r Hndup.
        rewrite ps_adds_rw_2 in Hvalid1.
        eapply IHe2 in H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]... clear IHe2.
        2:repeat solve_incl.
        inv Hsem1; inv H4. inv Hsem2; inv H5.
        simpl in *; rewrite app_nil_r in *.
        exists H''. repeat (split; eauto).
        + etransitivity...
        + repeat econstructor...
          * eapply sem_exp_refines...
          * congruence.
          * congruence.
        + apply Forall_app. split; solve_forall...
          eapply sem_equation_refines...
      - (* fby *)
        inversion_clear Hwc as [| | | | | |??? Hwc1 Hwc2 Hl1 Hl2 | | | | |].
        inversion_clear Hsem as [| | | | |???????? Hsem1 Hsem2 Fby| | | | |].
        simpl in *. repeat rewrite ps_adds_rw_1 in Hvalid.
        assert (length (concat x2) = length (annots e0s)) as Hlength1 by (eapply mmap2_unnest_exp_length; eauto).
        assert (length (concat x6) = length (annots es)) as Hlength2 by (eapply mmap2_unnest_exp_length; eauto).
        assert (NoDup (map fst (fresh_ins es) ++ (map fst reu))) as Hndup2 by ndup_r Hndup.
        assert (Forall (fun e => numstreams e = 1) (concat x2)) as Hnumstreams.
        { eapply mmap2_unnest_exp_numstreams in H2... }

        assert (length s0ss = length e0s) as Hlen1 by (eapply Forall2_length in Hsem1; eauto).
        assert (H2':=H2). eapply mmap2_sem in H2... clear H.
        2:ndup_simpl...
        2:rewrite idck_app, <-app_assoc in Histst; auto.
        destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1' Hsem1'']]]]]. apply Forall2_concat in Hsem1'.
        rewrite ps_adds_rw_2 in Hvalid1.

        assert (Forall2 (sem_exp_ck G1 H' b) es sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
        assert (length sss = length es) as Hlen2 by (eapply Forall2_length in Hsem2; eauto).
        assert (H3':=H3). eapply mmap2_sem in H3... clear H0.
        2:solve_forall; repeat solve_incl.
        destruct H3 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2' Hsem2'']]]]]. apply Forall2_concat in Hsem2'.

        assert (Forall2 (fun e v => sem_exp_ck G2 H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
        { eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines... }
        specialize (idents_for_anns_length _ _ _ _ H4) as Hlength.
        assert (length vs = length a) as Hlength'''.
        { eapply Forall3_length in Fby as [_ ?]. eapply Forall2_length in Hsem2'. eapply Forall2_length in Hl2.
          solve_length. }

        remember (Env.adds (List.map fst x5) vs H'') as H''''.
        assert (length x5 = length vs) as Hlength'''' by (rewrite Hlength, Hlength'''; auto).

        assert (Forall2 (sem_var H'''') (map fst x5) vs) as Hsemvars.
        { rewrite HeqH''''. eapply sem_var_adds; eauto.
          + rewrite map_length; auto.
          + eapply idents_for_anns_NoDupMembers in H4; eauto. rewrite <- fst_NoDupMembers; eauto. }

        assert (Env.refines (@EqSt _) H'' H'''') as Href4.
        { subst. eapply idents_for_anns_refines in H4...
          destruct Histst2 as (Hdom2&_). ndup_simpl... }
        clear Hlength'''.

        assert (Forall2 (fun e v => sem_exp_ck G2 H'''' b e [v]) (unnest_fby (concat x2) (concat x6) a) vs) as Hsemf.
        { eapply unnest_fby_sem; simpl...
          + eapply mmap2_unnest_exp_length in H2'... eapply Forall2_length in Hl1. solve_length.
          + eapply mmap2_unnest_exp_length in H3'... eapply Forall2_length in Hl2. solve_length.
          + clear - Hsem1' Href2 Href4. eapply Forall2_impl_In... intros; simpl in *.
            repeat (eapply sem_exp_refines; eauto).
          + clear - Hsem2' Href2 Href4. eapply Forall2_impl_In... intros; simpl in *.
            repeat (eapply sem_exp_refines; eauto). }

        exists H''''. split;[|split;[|split;[|split]]];eauto.
        * repeat (etransitivity; eauto).
        * subst. eapply idents_for_anns_hist_st in H4; eauto.
          replace (map clock_of_nclock a) with (clockof (Efby e0s es a)) by auto.
          eapply sc_exp with (env:=vars ++ st_clocks x4); eauto.
          destruct Histst2 as (_&Hsc2); eapply Forall_incl; eauto.
          eapply wc_exp_incl; [|eauto]; repeat solve_incl.
          eapply sem_ref_sem_exp; eauto. repeat (eapply sem_exp_refines; eauto).
      * clear - Hsemvars. solve_forall.
        * repeat rewrite Forall_app. repeat split.
          apply mk_equations_Forall.
          2-4:(solve_forall; repeat (eapply sem_equation_refines; eauto)).
          clear - Hsemvars Hsemf.
          remember (unnest_fby _ _ _) as fby. clear Heqfby.
          simpl_forall.
          repeat rewrite_Forall_forall. congruence.
          destruct (nth _ x5 _) eqn:Hnth1.
          econstructor.
          -- repeat constructor.
             eapply H0... congruence.
          -- repeat constructor.
             eapply H2 with (x1:=(i, a1))...
      - (* arrow *)
        inversion_clear Hwc as [| | | | | | |??? Hwc1 Hwc2 Hl1 Hl2| | | |].
        inversion_clear Hsem as [| | | | | |???????? Hsem1 Hsem2 Arrow| | | |].
        simpl in *. repeat rewrite ps_adds_rw_1 in Hvalid.
        assert (length (concat x2) = length (annots e0s)) as Hlength1 by (eapply mmap2_unnest_exp_length; eauto).
        assert (length (concat x6) = length (annots es)) as Hlength2 by (eapply mmap2_unnest_exp_length; eauto).
        assert (NoDup (map fst (fresh_ins es) ++ (map fst reu))) as Hndup2 by ndup_r Hndup.
        assert (Forall (fun e => numstreams e = 1) (concat x2)) as Hnumstreams.
        { eapply mmap2_unnest_exp_numstreams in H2... }

        assert (length s0ss = length e0s) as Hlen1 by (eapply Forall2_length in Hsem1; eauto).
        assert (H2':=H2). eapply mmap2_sem in H2... clear H.
        2:ndup_simpl...
        2:rewrite idck_app, <-app_assoc in Histst; auto.
        destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1' Hsem1'']]]]]. apply Forall2_concat in Hsem1'.
        rewrite ps_adds_rw_2 in Hvalid1.

        assert (Forall2 (sem_exp_ck G1 H' b) es sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
        assert (length sss = length es) as Hlen2 by (eapply Forall2_length in Hsem2; eauto).
        assert (H3':=H3). eapply mmap2_sem in H3... clear H0.
        2:solve_forall; repeat solve_incl.
        destruct H3 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2' Hsem2'']]]]]. apply Forall2_concat in Hsem2'.

        assert (Forall2 (fun e v => sem_exp_ck G2 H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
        { eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines... }
        specialize (idents_for_anns_length _ _ _ _ H4) as Hlength.
        assert (length vs = length a) as Hlength'''.
        { eapply Forall3_length in Arrow as [_ ?]. eapply Forall2_length in Hsem2'. eapply Forall2_length in Hl2.
          solve_length. }

        remember (Env.adds (List.map fst x5) vs H'') as H''''.
        assert (length x5 = length vs) as Hlength'''' by (rewrite Hlength, Hlength'''; auto).

        assert (Forall2 (sem_var H'''') (map fst x5) vs) as Hsemvars.
        { rewrite HeqH''''. eapply sem_var_adds; eauto.
          + rewrite map_length; auto.
          + eapply idents_for_anns_NoDupMembers in H4; eauto. rewrite <- fst_NoDupMembers; eauto. }

        assert (Env.refines (@EqSt _) H'' H'''') as Href4.
        { subst. eapply idents_for_anns_refines in H4...
          destruct Histst2 as (Hdom2&_). ndup_simpl... }
        clear Hlength'''.

        assert (Forall2 (fun e v => sem_exp_ck G2 H'''' b e [v]) (unnest_arrow (concat x2) (concat x6) a) vs) as Hsemf.
        { eapply unnest_arrow_sem; simpl...
          + eapply mmap2_unnest_exp_length in H2'... eapply Forall2_length in Hl1. solve_length.
          + eapply mmap2_unnest_exp_length in H3'... eapply Forall2_length in Hl2. solve_length.
          + clear - Hsem1' Href2 Href4. eapply Forall2_impl_In... intros; simpl in *.
            repeat (eapply sem_exp_refines; eauto).
          + clear - Hsem2' Href2 Href4. eapply Forall2_impl_In... intros; simpl in *.
            repeat (eapply sem_exp_refines; eauto). }

        exists H''''. split;[|split;[|split;[|split]]];eauto.
        * repeat (etransitivity; eauto).
        * subst. eapply idents_for_anns_hist_st in H4; eauto.
          replace (map clock_of_nclock a) with (clockof (Earrow e0s es a)) by auto.
          eapply sc_exp with (env:=vars ++ st_clocks x4); eauto.
          destruct Histst2 as (_&Hsc2); eapply Forall_incl; eauto.
          eapply wc_exp_incl; [|eauto]; repeat solve_incl.
          eapply sem_ref_sem_exp; eauto. repeat (eapply sem_exp_refines; eauto).
      * clear - Hsemvars. solve_forall.
        * repeat rewrite Forall_app. repeat split.
          apply mk_equations_Forall.
          2-4:(solve_forall; repeat (eapply sem_equation_refines; eauto)).
          clear - Hsemvars Hsemf.
          remember (unnest_arrow _ _ _) as arrow. clear Heqarrow.
          simpl_forall.
          repeat rewrite_Forall_forall. congruence.
          destruct (nth _ x5 _) eqn:Hnth1.
          econstructor.
          -- repeat constructor.
             eapply H0... congruence.
          -- repeat constructor.
             eapply H2 with (x1:=(i, a1))...
      - (* when *)
        inv Hwc. inv Hsem. repeat inv_bind.
        assert (length (concat x1) = length (annots es)) as Hlength by (eapply mmap2_unnest_exp_length; eauto).
        assert (length es = length ss) by (apply Forall2_length in H13; auto).
        eapply mmap2_sem in H1... clear H.
        destruct H1 as [H' [Hvalid1 [Href1 [Hhistst1 [Hsem1 Hsem1']]]]].
        apply Forall2_concat in Hsem1.
        exists H'. repeat (split; simpl; eauto).
        eapply unnest_when_sem... solve_length.
        eapply sem_var_refines...
      - (* merge *)
        inv Hwc. inv Hsem. repeat inv_bind.
        simpl in *.

        assert (x <> []) as Hnnil.
        { eapply mmap2_length_1 in H1.
          intro contra; subst. destruct es; simpl in *; congruence. }

        assert (Forall (fun es => length es = length tys) x) as Hlen1.
        { eapply mmap2_mmap2_unnest_exp_length, Forall2_ignore1 in H1... 2:solve_forall.
          eapply Forall_impl; [|eapply H1]; intros ? (?&Hin&Hlen).
          eapply Forall_forall in H8; eauto. solve_length. }
        assert (Hun:=H1). eapply mmap2_mmap2_sem in H1 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1')... clear H.

        assert (Forall2 (fun e v => sem_exp_ck G2 H' b e [v])
                        (unnest_merge (x0, tx) x tys (ck, None)) vs) as Hsem'.
        { eapply unnest_merge_sem...
          eapply sem_var_refines... }
        destruct is_control; repeat inv_bind.
        + (* control *)
          exists H'. repeat (split; simpl; eauto).
        + (* exp *)
          remember (Env.adds (List.map fst x3) vs H') as H''.
          assert (length vs = length x3) as Hlength'.
          { eapply idents_for_anns_length in H. repeat simpl_length.
            apply Forall2Transpose_length, Forall_map in H16.
            inv H15; try congruence. inv H8. inv H16. inv H6.
            eapply sem_exps_ck_sem_exps, sem_exps_numstreams in H1... solve_length. }
          assert (Env.refines (@EqSt _) H' H'') as Href3.
          { subst. eapply idents_for_anns_refines...
            destruct Histst1 as (Hdom1&_). ndup_simpl... }
          assert (Forall2 (sem_var H'') (map fst x3) vs) as Hvars.
          { rewrite HeqH''. eapply sem_var_adds... 1:rewrite map_length...
            rewrite <- fst_NoDupMembers. eapply idents_for_anns_NoDupMembers in H... }
          exists H''. split;[|split;[|split;[|split]]]; eauto.
          * repeat (etransitivity; eauto).
          * subst. eapply idents_for_anns_hist_st...
            rewrite map_map. change (map (fun x4 => clock_of_nclock (x4, (ck, None))) tys) with (clockof (Emerge (x0, tx) es (tys, (ck, None)))).
            eapply sc_exp with (env:=vars++st_clocks x2); eauto.
            destruct Histst1 as (_&Hsc1); eapply Forall_incl; eauto.
            eapply wc_exp_incl; [|eauto]; repeat solve_incl.
            eapply sem_ref_sem_exp; eauto. repeat (eapply sem_exp_refines; eauto).
          * clear - Hvars. solve_forall.
          * repeat rewrite Forall_app; repeat split.
            -- remember (unnest_merge _ _ _ _) as merge.
               assert (length merge = length x3) as Hlength''.
               { eapply idents_for_anns_length in H.
                 subst. rewrite unnest_merge_length. solve_length. }
               clear - Hvars Hsem' Href3 Hlength''. apply mk_equations_Forall. simpl_forall.
               rewrite Forall2_swap_args in Hsem'.
               eapply Forall2_trans_ex in Hsem'; [|eauto].
               eapply Forall2_impl_In; [|eauto]. intros (?&?) ? _ _ (?&?&?&?).
               apply Seq with (ss:=[[x]]); simpl.
               1,2:repeat constructor... eapply sem_exp_refines...
            -- solve_forall. repeat (eapply sem_equation_refines; eauto).
      - (* case *)
        inv Hwc. inv Hsem. repeat inv_bind.
        simpl in *. repeat rewrite ps_adds_rw_1 in Hvalid.
        assert (NoDup (map fst (fresh_ins d) ++ map fst reu)) as Hndup1.
        { repeat ndup_r Hndup. }
        assert (NoDup (map fst (flat_map (or_default_with [] fresh_ins) es) ++ map fst (fresh_ins d) ++ map fst reu)) as Hndup2.
        { ndup_simpl. ndup_r Hndup. }
        assert (length x = 1). 2:singleton_length.
        { eapply unnest_exp_length in H2... rewrite H2, <-length_clockof_numstreams, H7; auto. }
        assert (Hun1:=H2). eapply IHe in H2 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1')... clear IHe.
        2:ndup_simpl...
        2:rewrite idck_app, <-app_assoc in Histst; auto.
        eapply Forall2_singl in Hsem1.
        rewrite ps_adds_rw_2, ps_adds_rw_1 in Hvalid1.

        assert (x2 <> []) as Hnnil.
        { eapply mmap2_length_1 in H3.
          intro contra; subst. destruct es; simpl in *; congruence. }
        assert (Forall (LiftO True (fun es => length es = length tys)) x2) as Hlen1.
        { eapply mmap2_mmap2_unnest_exp_length', Forall2_ignore1 in H3...
          eapply Forall_impl; [|eapply H3]; intros [|] (?&Hin&Hlen); simpl; auto.
          - edestruct Hlen as (?&?&?); eauto; subst.
            erewrite H11; eauto. solve_length.
          - eapply Forall_forall. intros [|] Hin; simpl; auto.
            eapply H9 in Hin; eauto.
        }
        assert (Forall2 (fun es es' => es' = None -> es = None) es x2) as Hnone.
        { clear - H3. eapply mmap2_values, Forall3_ignore3 in H3.
          eapply Forall2_impl_In; [|eauto]; intros ?? _ _ (?&?&?&?) ?; subst.
          destruct a; auto; repeat inv_bind. }
        assert (Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (sem_exp_ck G1 H' b) es vs) es vs0) as Hsems.
        { clear - Href1 H19.
          eapply Forall2_impl_In; [|eauto]; intros; subst. specialize (H2 _ eq_refl).
          eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines... }
        assert (Hun2:=H3). eapply mmap2_mmap2_sem' in H3 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2')... clear H.
        2:ndup_simpl...
        2:intros ??; eapply Forall_impl; [|eauto]; intros; repeat solve_incl.
        2:rewrite idck_app, <-app_assoc in Histst1...
        rewrite ps_adds_rw_2 in Hvalid2.

        assert (length (concat x8) = length tys) as Hlen2.
        { eapply mmap2_unnest_exp_length in H4... rewrite H4, H14; auto using length_clocksof_annots. }
        assert (Forall2 (sem_exp_ck G1 H'' b) d vd) as Hsemd.
        { eapply Forall2_impl_In; [|eauto]; intros.
          eapply sem_exp_refines; [|eauto]. etransitivity... }
        assert (Hun3:=H4). eapply mmap2_sem in H4 as (H'''&Href3&Hvalid3&Histst3&Hsem3&Hsem3')... clear H0.
        eapply Forall2_concat in Hsem3.
        2:{ solve_forall. repeat solve_incl. destruct x; repeat inv_bind; repeat solve_st_follows. }

        assert (Forall2 (fun e v => sem_exp_ck G2 H''' b e [v])
                        (unnest_case e0 x2 (concat x8) tys (ck, None)) vs) as Hsem'.
        { eapply unnest_case_sem...
          - eapply sem_exp_refines; [|eauto]. etransitivity...
          - eapply Forall2_impl_In; [|eauto]; intros; subst.
            specialize (H2 _ eq_refl).
            eapply Forall2_impl_In; [|eauto]; intros.
            eapply sem_exp_refines...
          - clear - Hnone H21. rewrite Forall2_map_2.
            rewrite Forall2_swap_args in Hnone.
            eapply Forall2_trans_ex in H21; eauto.
            eapply Forall2_impl_In; [|eauto]; intros ?? _ _ (?&?&?&?) ?; subst.
            eapply Forall2_concat; eauto. }
        destruct is_control; repeat inv_bind.
        + (* control *)
          exists H'''. repeat (split; simpl; eauto).
          * do 2 etransitivity...
          * repeat rewrite Forall_app; repeat split...
            1,2:solve_forall; eapply sem_equation_refines; [|eauto]...
            etransitivity...
        + (* exp *)
          remember (Env.adds (List.map fst x) vs H''') as H''''.
          assert (length vs = length x) as Hlength'.
          { clear Hlen1 Hlen2. eapply idents_for_anns_length in H. repeat simpl_length.
            clear - H8 H9 H11 H12 H13 H14 H19 H21 H22 H23.
            apply Forall2Transpose_length, Forall_map in H23.
            inv H19; try congruence. inv H21. inv H23.
            destruct x.
            - specialize (H _ eq_refl). eapply sem_exps_ck_sem_exps, sem_exps_numstreams in H; eauto with datatypes.
              erewrite <-H4, H, H11; eauto with datatypes. now rewrite length_clocksof_annots.
            - eapply Forall2_concat, Forall2_length in H5; auto.
              eapply sem_exps_ck_sem_exps, sem_exps_numstreams in H22...
              rewrite <-H4, H5, <-H14. congruence. }
          assert (Env.refines (@EqSt _) H''' H'''') as Href4.
          { subst. eapply idents_for_anns_refines...
            destruct Histst3 as (Hdom3&_). ndup_simpl... }
          assert (Forall2 (sem_var H'''') (map fst x) vs) as Hvars.
          { rewrite HeqH''''. eapply sem_var_adds... 1:rewrite map_length...
            rewrite <- fst_NoDupMembers. eapply idents_for_anns_NoDupMembers in H... }
          exists H''''. split;[|split;[|split;[|split]]]; eauto.
          * repeat (etransitivity; eauto).
          * subst; eapply idents_for_anns_hist_st...
            rewrite map_map. change (map (fun ty => clock_of_nclock (ty, (ck, None))) tys) with (clockof (Ecase e es d (tys, (ck, None)))).
            eapply sc_exp with (env:=vars++st_clocks x7); eauto.
            destruct Histst3 as (_&Hsc3); eapply Forall_incl; eauto.
            eapply wc_exp_incl; [|eauto]; repeat solve_incl.
            1:{ destruct x5; repeat inv_bind; repeat solve_st_follows. }
            eapply sem_ref_sem_exp; eauto. repeat (eapply sem_exp_refines; eauto).
          * clear - Hvars. solve_forall.
          * repeat rewrite Forall_app; repeat split.
            -- remember (unnest_case _ _ _ _ _) as case.
               assert (length case = length x) as Hlength''.
               { eapply idents_for_anns_length in H.
                 subst. rewrite unnest_case_length. rewrite map_length in *; auto. }
               clear - Hvars Hsem' Href4 Hlength''. apply mk_equations_Forall. simpl_forall.
               rewrite Forall2_swap_args in Hsem'.
               eapply Forall2_trans_ex in Hsem'; [|eauto].
               eapply Forall2_impl_In; [|eauto]. intros (?&?) ? _ _ (?&?&?&?).
               apply Seq with (ss:=[[x0]]); simpl.
               1,2:repeat constructor... eapply sem_exp_refines...
            -- solve_forall. repeat (eapply sem_equation_refines; eauto).
            -- solve_forall. eapply sem_equation_refines; [|eauto]. etransitivity...
            -- solve_forall. eapply sem_equation_refines; [|eauto]. etransitivity...
      - (* app *)
        repeat rewrite ps_adds_rw_1 in Hvalid.
        assert (a = map snd x8) as Hanns; subst.
        { eapply idents_for_anns'_values in H5... }
        specialize (idents_for_anns'_length _ _ _ _ H5) as Hlength1.
        assert (length (n_out n) = length vs) as Hlength2.
        { specialize (H23 0). inv H23. apply Forall2_length in H9.
          unfold idents in *. repeat rewrite map_length in H9. congruence. }
        assert (length es = length ss) as Hlength3.
        { apply Forall2_length in H17... }
        assert (length (concat x6) = length (n_in n)) as Hlength4.
        { eapply mmap2_unnest_exp_length in H2; eauto. eapply Forall2_length in H13.
          rewrite length_idck in H13. rewrite H13. subst_length. now rewrite length_nclocksof_annots. }
        assert (NoDup (map fst (Syn.anon_streams (map snd x8))++map fst reu)) as Hndup2 by repeat ndup_r Hndup.
        assert (NoDup (map fst (fresh_ins er) ++ map fst (Syn.anon_streams (map snd x8)) ++ map fst reu)) as Hndup3.
        { ndup_simpl... ndup_r Hndup. }

        assert (Hun1:=H2). eapply mmap2_sem in H2... clear H.
        2:ndup_simpl...
        2:rewrite idck_app, <-app_assoc in Histst...
        destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].

        assert (Hun2:=H3). eapply unnest_noops_exps_sem in H3 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2')...
        5:eapply Forall2_concat; eauto.
        2:{ unfold find_node_incks. now rewrite H12, map_length. }
        2:{ eapply mmap2_unnest_exp_wc in Hun1 as (?&?); eauto. }
        2:{ eapply mmap2_unnest_exp_numstreams in Hun1; eauto. }

        rewrite ps_adds_rw_2, ps_adds_rw_1 in Hvalid2.
        assert (length rs = length er) as Hlen3 by (eapply Forall2_length in H20; eauto).
        assert (Forall2 (fun er sr => sem_exp_ck G1 H'' b er [sr]) er rs) as Hsemr' by (repeat rewrite_Forall_forall; repeat (eapply sem_exp_refines; eauto)).
        assert (Hun3:=H4). eapply unnest_resets_sem in H4...
        2:ndup_simpl...
        2:(solve_forall; repeat solve_incl).
        2:{ eapply Forall_impl; [|eapply H15]; intros ? Hck. destruct Hck as (?&Hck).
            rewrite <-length_clockof_numstreams, Hck; auto. }
        2:{ rewrite idck_app, <-app_assoc in Histst2... }
        2:{ solve_forall. eapply H18 in H15 as (H'''&?&?&?&?&?); eauto. exists H'''; split;[|split;[|split;[|split]]]; eauto.
            inv H26; eauto. }
        destruct H4 as (H'''&Href3&Hvalid3&Histst3&Hsem3&Hsem3').
        rewrite ps_adds_rw_2 in Hvalid3; eauto.

        assert (sem_exp_ck G2 H''' b (Eapp f x2 x5 (map snd x8)) vs) as Hsem'.
        { eapply Sapp with (ss0:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss)))...
          + rewrite <- concat_map, Forall2_map_2.
            solve_forall. eapply sem_exp_refines...
          + intros k. specialize (H23 k).
            rewrite concat_map_singl2. eapply HGref; eauto.
          + repeat (eapply clocked_app_refines; eauto). }
        remember (Env.adds (map fst x8) vs H''') as H''''.
        assert (length vs = length x8) as Hlen'.
        { eapply Forall2_length in H14. rewrite length_idck, map_length in H14. solve_length. }
        assert (Env.refines (@EqSt _) H''' H'''') as Href4.
        { subst. eapply idents_for_anns'_refines...
          + repeat (eapply clocked_app_refines; eauto).
          + destruct Histst3 as (Hdom3&_).
            now rewrite 2 map_app, map_fst_idck, <- 2 app_assoc in Hdom3.
        }
        assert (NoDupMembers x8) as Hndup'.
        { eapply idents_for_anns'_NoDupMembers in H5... }
        assert (Forall2 (sem_var H'''') (map fst x8) vs) as Hvars.
        { rewrite HeqH''''. eapply sem_var_adds... 1:rewrite map_length... rewrite <- fst_NoDupMembers... }
        exists H''''. split;[|split;[|split;[|split]]]...
        + repeat (etransitivity; eauto).
        + subst; eapply idents_for_anns'_hist_st in H5...
          * repeat (eapply clocked_app_refines; eauto).
          * change (map clock_of_nclock (map snd x8)) with (clockof (Eapp f es er (map snd x8))).
            eapply sc_exp with (env:=vars++st_clocks x7); eauto.
            destruct Histst3 as (_&Hsc3); eapply Forall_incl; eauto.
            eapply wc_exp_incl; [|eauto]; repeat solve_incl.
            eapply sem_ref_sem_exp; eauto. repeat (eapply sem_exp_refines; eauto).
        + clear - Hvars. solve_forall.
        + constructor; [| repeat rewrite Forall_app; repeat split].
          * apply Seq with (ss0:=[vs]).
            -- repeat constructor...
               eapply sem_exp_refines...
            -- simpl. rewrite app_nil_r; auto.
          * solve_forall. repeat (eapply sem_equation_refines; eauto).
          * solve_forall. repeat (eapply sem_equation_refines; eauto).
          * solve_forall. eapply sem_equation_refines...
            Unshelve. 1,2:exact default_stream.
    Qed.

    Corollary unnest_exps_sem : forall vars b es H vs es' eqs' st st' reu,
        NoDup (map fst (fresh_ins es) ++ map fst reu) ->
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        Forall2 (sem_exp_ck G1 H b) es vs ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (fresh_ins es)) (PSP.of_list (map fst reu))) ->
        hist_st (vars++idck (fresh_ins es)++reu) b H st ->
        mmap2 (unnest_exp G1 false) es st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
            hist_st (vars++reu) b H' st' /\
            Forall2
              (fun (es : list exp) (vs : list (Stream svalue)) =>
                 Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es vs) es' vs /\
            Forall (sem_equation_ck G2 H' b) (concat eqs')).
    Proof.
      intros * Hndup Hwt Hsem Hvalid Hhistst Hnorm.
      eapply mmap2_sem in Hnorm; eauto.
      repeat rewrite_Forall_forall.
      eapply unnest_exp_sem; eauto.
    Qed.

    Fact unnest_rhs_sem : forall vars b e H vs es' eqs' st st' reu,
        NoDup (map fst (anon_in e) ++ map fst reu) ->
        wc_exp G1 (vars++st_clocks st) e ->
        sem_exp_ck G1 H b e vs ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in e)) (PSP.of_list (map fst reu))) ->
        hist_st (vars++idck (anon_in e)++reu) b H st ->
        unnest_rhs G1 e st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
            hist_st (vars++reu) b H' st' /\
            (Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es' vs \/
             exists e', (es' = [e'] /\ sem_exp_ck G2 H' b e' vs)) /\
            Forall (sem_equation_ck G2 H' b) eqs').
    Proof with eauto.
      intros * Hndup1 Hwt Hsem Hvalid Histst Hnorm.
      destruct e; try (eapply unnest_exp_sem in Hnorm as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem2]]]]]; eauto;
                       exists H'; repeat (split; eauto)).
      1,2,3:unfold unnest_rhs in Hnorm; repeat inv_bind. 3:inv Hwt; inv Hsem.
      - (* fby *)
        inversion_clear Hwt as [| | | | | |??? Hwc1 Hwc2 Hl1 Hl2 | | | | |].
        inversion_clear Hsem as [| | | | |???????? Hsem1 Hsem2 Fby| | | | |].
        assert (length x = length (annots l)) as Hlength1 by (eapply unnest_exps_length; eauto).
        assert (length x2 = length (annots l0)) as Hlength2 by (eapply unnest_exps_length; eauto).
        unfold unnest_exps in *. repeat inv_bind.
        simpl in *. repeat rewrite ps_adds_rw_1 in Hvalid.
        assert (NoDup (map fst (fresh_ins l0) ++ map fst reu)) as Hndup3.
        { ndup_simpl... ndup_r Hndup1. }

        assert (Hun1:=H0). eapply unnest_exps_sem in H0... clear Hsem1.
        2:ndup_simpl...
        2:rewrite idck_app, <-app_assoc in Histst...
        destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.
        assert (Forall2 (sem_exp_ck G1 H' b) l0 sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
        rewrite ps_adds_rw_2 in Hvalid1.

        eapply unnest_exps_sem in H1... clear Hsem2.
        2:(solve_forall; repeat solve_incl).
        destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
        assert (Forall2 (fun e v => sem_exp_ck G2 H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
        { solve_forall. eapply sem_exp_refines... }

        exists H''. repeat (split; auto).
        + repeat (etransitivity; eauto).
        + left. eapply unnest_fby_sem...
          * eapply Forall2_length in Hl1; solve_length.
          * eapply Forall2_length in Hl2; solve_length.
        + repeat rewrite Forall_app. repeat split...
          1,2:solve_forall; (eapply sem_equation_refines; [|eauto]; etransitivity; eauto).
      - (* arrow *)
        inversion_clear Hwt as [| | | | | | |??? Hwc1 Hwc2 Hl1 Hl2| | | |].
        inversion_clear Hsem as [| | | | | |???????? Hsem1 Hsem2 Fby| | | |].
        assert (length x = length (annots l)) as Hlength1 by (eapply unnest_exps_length; eauto).
        assert (length x2 = length (annots l0)) as Hlength2 by (eapply unnest_exps_length; eauto).
        unfold unnest_exps in *. repeat inv_bind.
        simpl in *. repeat rewrite ps_adds_rw_1 in Hvalid.
        assert (NoDup (map fst (fresh_ins l0) ++ map fst reu)) as Hndup3.
        { ndup_simpl... ndup_r Hndup1. }

        assert (Hun1:=H0). eapply unnest_exps_sem in H0... clear Hsem1.
        2:ndup_simpl...
        2:rewrite idck_app, <-app_assoc in Histst...
        destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.
        assert (Forall2 (sem_exp_ck G1 H' b) l0 sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
        rewrite ps_adds_rw_2 in Hvalid1.

        eapply unnest_exps_sem in H1... clear Hsem2.
        2:(solve_forall; repeat solve_incl).
        destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
        assert (Forall2 (fun e v => sem_exp_ck G2 H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
        { solve_forall. eapply sem_exp_refines... }

        exists H''. repeat (split; auto).
        + repeat (etransitivity; eauto).
        + left. eapply unnest_arrow_sem...
          * eapply Forall2_length in Hl1; solve_length.
          * eapply Forall2_length in Hl2; solve_length.
        + repeat rewrite Forall_app. repeat split...
          1,2:solve_forall; (eapply sem_equation_refines; [|eauto]; etransitivity; eauto).
      - (* app *)
        simpl in *. repeat rewrite ps_adds_rw_1 in Hvalid.
        unfold unnest_exps in H0.
        repeat inv_bind.
        assert (NoDup (map fst (fresh_ins l0) ++ map fst reu)) as Hndup4 by ndup_r Hndup1.
        assert (length (concat x6) = length (n_in n)) as Hlength4.
        { eapply mmap2_unnest_exp_length in H0; eauto.
          eapply Forall2_length in H10. rewrite length_idck in H10. solve_length.
          now rewrite length_nclocksof_annots. }

        assert (Hun1:=H0). eapply unnest_exps_sem in H0...
        2:ndup_simpl...
        2:rewrite idck_app, <-app_assoc in Histst...
        destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].

        assert (Hun2:=H1). eapply unnest_noops_exps_sem in H1 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2')...
        5:eapply Forall2_concat...
        2:{ unfold find_node_incks. rewrite H9, map_length; auto. }
        2:{ eapply mmap2_unnest_exp_wc. 1,3:eauto. solve_forall; repeat solve_incl. }
        2:(eapply mmap2_unnest_exp_numstreams; eauto).
        rewrite ps_adds_rw_2 in Hvalid2.

        assert (length rs = length l0) as Hlen3 by (eapply Forall2_length in H17; eauto).
        assert (Forall2 (fun er sr => sem_exp_ck G1 H'' b er [sr]) l0 rs) as Hsemr'
            by (solve_forall; repeat (eapply sem_exp_refines; eauto)).
        assert (Hr:=H2). eapply unnest_resets_sem in H2...
        2:(solve_forall; repeat solve_incl).
        2:{ solve_forall. destruct H1 as (?&Hck).
            now rewrite <-length_clockof_numstreams, Hck. }
        2:{ solve_forall. eapply unnest_exp_sem in H15 as (H'''&?&?&?&Sem1&?)... inv Sem1...
            exists H'''. repeat (split; eauto). }
        destruct H2 as (H'''&Href3&Hvalid3&Hhistst3&Hsem3&Hsem3').

        exists H'''. repeat (split; auto).
        + repeat (etransitivity; eauto).
        + right. eexists; split...
          apply Sapp with (ss0:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))) (rs0:=rs) (bs0:=bs); eauto.
          * rewrite <- concat_map, Forall2_map_2; auto.
            solve_forall. repeat (eapply sem_exp_refines; eauto).
          * rewrite concat_map_singl2. intros k. eapply HGref, H20; eauto.
          * repeat (eapply clocked_app_refines; eauto).
        + repeat rewrite Forall_app.
          repeat split; solve_forall; (eapply sem_equation_refines; [|eauto]); eauto.
          etransitivity...
    Qed.

    Corollary mmap2_unnest_rhs_sem : forall vars b es H vs es' eqs' st st' reu,
        NoDup (map fst (anon_ins es) ++ map fst reu) ->
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        Forall2 (sem_exp_ck G1 H b) es vs ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_ins es)) (PSP.of_list (map fst reu))) ->
        hist_st (vars++idck (anon_ins es)++reu) b H st ->
        mmap2 (unnest_rhs G1) es st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
            hist_st (vars++reu) b H' st' /\
            Forall2 (fun es' vs =>
                       Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es' vs \/
                       exists e', (es' = [e'] /\ sem_exp_ck G2 H' b e' vs)) es' vs /\
            Forall (sem_equation_ck G2 H' b) (concat eqs')).
    Proof with eauto.
      induction es; intros * Hndup Hwt Hsem Hvalid Histst Hmap;
        repeat inv_bind.
      - exists H; simpl. inv Hsem. repeat (split; auto).
      - inv Hwt. inv Hsem.
        unfold anon_ins in *. simpl in *. rewrite ps_adds_rw_1 in Hvalid.
        assert (NoDup (map fst (anon_ins es) ++ map fst reu)) as Hndup4 by ndup_r Hndup.

        assert (st_follows st x1) as Hfollows1 by eauto.
        eapply unnest_rhs_sem in H0...
        2:ndup_simpl...
        2:rewrite idck_app, <-app_assoc in Histst...
        destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
        assert (Forall2 (sem_exp_ck G1 H' b) es l') as Hsem'.
        { eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines; eauto. }
        rewrite ps_adds_rw_2 in Hvalid1.

        eapply IHes in H1... clear IHes.
        2:(solve_forall; repeat solve_incl).
        destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]].
        exists H''. repeat (split; eauto).
        + etransitivity...
        + constructor...
          destruct Hsem1.
          * left. solve_forall. eapply sem_exp_refines...
          * right. destruct H0 as [e' [? H0]]; subst.
            exists e'. split... eapply sem_exp_refines...
        + apply Forall_app. split...
          solve_forall. eapply sem_equation_refines...
    Qed.

    Corollary unnest_rhss_sem : forall vars b es H vs es' eqs' st st' reu,
        NoDup (map fst (anon_ins es) ++ map fst reu) ->
        Forall (wc_exp G1 (vars++st_clocks st)) es ->
        Forall2 (sem_exp_ck G1 H b) es vs ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_ins es)) (PSP.of_list (map fst reu))) ->
        hist_st (vars++idck (anon_ins es)++reu) b H st ->
        unnest_rhss G1 es st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
            hist_st (vars++reu) b H' st' /\
            Forall (fun '(e, v) => sem_exp_ck G2 H' b e v)
                   (combine_for_numstreams es' (concat vs)) /\
            Forall (sem_equation_ck G2 H' b) eqs').
    Proof with eauto.
      intros * Hndup Hwt Hsem Hvalid Histst Hnorm.
      assert (Forall (wc_exp G2 (vars++st_clocks st')) es') as Hwt'.
      { eapply unnest_rhss_wc in Hnorm as [? ?]... }
      unfold unnest_rhss in *.
      repeat inv_bind.
      eapply mmap2_unnest_rhs_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      exists H'. repeat (split; eauto).
      clear Hsem. induction Hsem1; simpl...
      simpl. destruct H0.
      - induction H0; simpl in *...
        inv Hwt'.
        assert (numstreams x = 1) as Hnumstreams.
        { eapply sem_exp_ck_sem_exp, sem_exp_numstreams in H0... }
        constructor.
        + rewrite Hnumstreams; simpl...
        + rewrite Hnumstreams; simpl...
      - destruct H0 as [? [? H0]]; subst; simpl in *.
        inv Hwt'.
        assert (numstreams x1 = length y) as Hnumstreams.
        { eapply sem_exp_ck_sem_exp, sem_exp_numstreams in H0... }
        constructor.
        + rewrite firstn_app, Hnumstreams, firstn_all, Nat.sub_diag, firstn_O, app_nil_r...
        + rewrite skipn_app...
    Qed.

    Fact combine_for_numstreams_length {V} : forall es (vs : list V),
        length vs = length (annots es) ->
        length (combine_for_numstreams es vs) = length es.
    Proof.
      induction es; intros vs Hlen; simpl in *.
      - destruct vs; simpl in *; try congruence; auto.
      - f_equal. apply IHes.
        rewrite skipn_length, Hlen, app_length, length_annot_numstreams. lia.
    Qed.

    Fact combine_for_numstreams_fst_split {V} : forall es (vs : list V),
        length vs = length (annots es) ->
        fst (split (combine_for_numstreams es vs)) = es.
    Proof.
      induction es; intros vs Hlen; simpl.
      - destruct vs; simpl in *; auto. congruence.
      - destruct (split _) eqn:Hsplit; simpl.
        f_equal. simpl in Hlen.
        assert (fst (l, l0) = es); auto.
        rewrite <- Hsplit, IHes; auto.
        rewrite skipn_length, Hlen, app_length, length_annot_numstreams. lia.
    Qed.

    Fact combine_for_numstreams_numstreams {V} : forall es (vs : list V),
        length vs = length (annots es) ->
        Forall (fun '(e, v) => numstreams e = length v) (combine_for_numstreams es vs).
    Proof with eauto.
      induction es; intros vs Hlen; simpl in *...
      - destruct vs; simpl in *; auto; congruence.
      - rewrite app_length in Hlen.
        rewrite length_annot_numstreams in Hlen.
        constructor...
        + rewrite firstn_length. lia.
        + apply IHes.
          rewrite skipn_length.
          lia.
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

    Fact unnest_equation_sem : forall vars H b equ eqs' st st' reu,
        NoDup (map fst (anon_in_eq equ) ++ map fst reu) ->
        wc_equation G1 (vars++st_clocks st) equ ->
        sem_equation_ck G1 H b equ ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in_eq equ)) (PSP.of_list (map fst reu))) ->
        hist_st (vars++idck (anon_in_eq equ)++reu) b H st ->
        unnest_equation G1 equ st = (eqs', st') ->
        (exists H', Env.refines (@EqSt _) H H' /\
               st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
               hist_st (vars++reu) b H' st' /\
               Forall (sem_equation_ck G2 H' b) eqs').
    Proof with eauto.
      intros * Hndup Hwt Hsem Hvalid Histst Hnorm.
      unfold unnest_equation in Hnorm.
      destruct equ as [xs es]. inv Hwt. inv Hsem.
      repeat inv_bind.
      assert (annots x = annots es) as Hannots by (eapply unnest_rhss_annots; eauto).
      assert (Hun:=H2). eapply unnest_rhss_sem in H2 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1')...
      exists H'. repeat (split; eauto).
      apply Forall_app. split...
      clear Hsem1'.
      assert (length (concat ss) = length (annots es)) as Hlen1.
      { eapply sem_exps_ck_sem_exps, sem_exps_numstreams in H7; eauto. }
      assert (length xs = length (annots x)) as Hlen2.
      { rewrite Hannots, <-Hlen1.
        repeat rewrite_Forall_forall. simpl_length. congruence. }
      repeat rewrite_Forall_forall.
      destruct x1. repeat simpl_In. inv H6.
      assert (HIn := H7).
      eapply In_nth with (d:=(hd_default [], [])) in H7. destruct H7 as [n [Hn Hnth]].
      rewrite combine_for_numstreams_length in Hn; auto.
      rewrite <- (combine_for_numstreams_length _ (concat ss)) in Hn; try congruence.
      assert (HIn' := Hn).
      apply nth_In with (d:=(hd_default [], [])) in HIn'.
      specialize (Hsem1 _ HIn').
      destruct (nth _ _ _) eqn:Hnth' in Hsem1. rewrite Hnth' in HIn'.
      assert (e = e0) as Hee0.
      { rewrite split_nth in Hnth; inv Hnth.
        rewrite split_nth in Hnth'; inv Hnth'.
        repeat rewrite combine_for_numstreams_fst_split; try congruence. } subst.
      apply Seq with (ss0:=[l0]).
      + repeat constructor...
      + simpl. rewrite app_nil_r.
        repeat rewrite_Forall_forall.
        * replace (length l) with (numstreams e0). replace (length l0) with (numstreams e0). reflexivity.
          { eapply Forall_forall in HIn'. 2:eapply combine_for_numstreams_numstreams; try congruence.
            eauto. }
          { eapply Forall_forall in HIn. 2:eapply combine_for_numstreams_numstreams; try congruence.
            eauto. }
        * eapply sem_var_refines...
          specialize (combine_for_numstreams_nth_2 x xs (concat ss) n n0 e0 l l0
                                                   a b0 (hd_default [], []) (hd_default [], [])) as Hcomb.
          apply Hcomb in H6. clear Hcomb.
          2,3:congruence.
          2:(rewrite combine_for_numstreams_length in Hn; auto; congruence).
          2,3:auto.
          destruct H6 as (?&?&?&?).
          eapply H3...
    Qed.

    Lemma hist_st_mask : forall vars bs H st r k,
        hist_st vars bs H st ->
        hist_st vars (maskb k r bs) (mask_hist k r H) st.
    Proof.
      intros * (?&?).
      split.
      - eapply Env.dom_map; eauto.
      - eapply LCS.sc_var_inv_mask; eauto.
    Qed.

    Lemma hist_st_unmask : forall vars bs H st r,
        (forall k, hist_st vars (maskb k r bs) (mask_hist k r H) st) ->
        hist_st vars bs H st.
    Proof.
      intros * Hk.
      constructor.
      - eapply Env.dom_map. eapply (Hk 0).
      - eapply sc_var_inv_unmask. intros. eapply Hk.
    Qed.

    Fact mmap_unnest_block_sem : forall vars b blocks H blocks' st st' reu,
        Forall
         (fun d : block => forall H b blocks' st st' reu,
          NoDup (map fst (anon_in_block d) ++ map fst reu) ->
          wc_block G1 (vars ++ st_clocks st) d ->
          sem_block_ck G1 H b d ->
          st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in_block d)) (PSP.of_list (map fst reu))) ->
          hist_st (vars ++ idck (anon_in_block d) ++ reu) b H st ->
          unnest_block G1 d st = (blocks', st') ->
          exists H' : Env.t (Stream svalue),
            Env.refines (EqSt (A:=svalue)) H H' /\
            st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
            hist_st (vars ++ reu) b H' st' /\
            Forall (sem_block_ck G2 H' b) blocks') blocks ->
        NoDup (map fst (flat_map anon_in_block blocks) ++ map fst reu) ->
        Forall (wc_block G1 (vars ++ st_clocks st)) blocks ->
        Forall (sem_block_ck G1 H b) blocks ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (flat_map anon_in_block blocks)) (PSP.of_list (map fst reu))) ->
        hist_st (vars++idck (flat_map anon_in_block blocks)++reu) b H st ->
        mmap (unnest_block G1) blocks st = (blocks', st') ->
        (exists H', Env.refines (@EqSt _) H H' /\
               st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
               hist_st (vars++reu) b H' st' /\
               Forall (sem_block_ck G2 H' b) (concat blocks')).
    Proof with eauto.
      induction blocks; intros * Hf Hndup Hwc Hsem Hvalid Histst Hnorm;
        inv Hf; inv Hwc; inv Hsem; repeat inv_bind; simpl.
      - exists H...
      - simpl in *. rewrite ps_adds_rw_1 in Hvalid.
        assert (NoDup (map fst (flat_map anon_in_block blocks) ++ map fst reu)) as Hndup4 by ndup_r Hndup.

        assert (Forall (wc_block G1 (vars ++ st_clocks x0)) blocks) as Hwc'.
        { solve_forall. repeat solve_incl. }
        eapply H2 in H0 as (H'&Href1&Hvalid1&Histst1&Hsem1)...
        2:ndup_simpl...
        2:rewrite idck_app, <-app_assoc in Histst...
        assert (Forall (sem_block_ck G1 H' b) blocks) by (solve_forall; eapply sem_block_refines; eauto).
        rewrite ps_adds_rw_2 in Hvalid1.

        eapply IHblocks in H1 as (H''&Href2&Hvalid2&Histst2&Hsem2)...
        exists H''. split;[|split;[|split]]...
        + etransitivity...
        + eapply Forall_app. split...
          solve_forall. eapply sem_block_refines...
    Qed.

    Lemma unnest_block_sem : forall vars d H b blocks' st st' reu,
        NoDup (map fst (anon_in_block d) ++ map fst reu) ->
        wc_block G1 (vars++st_clocks st) d ->
        sem_block_ck G1 H b d ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in_block d)) (PSP.of_list (map fst reu))) ->
        hist_st (vars++idck (anon_in_block d)++reu) b H st ->
        unnest_block G1 d st = (blocks', st') ->
        (exists H', Env.refines (@EqSt _) H H' /\
               st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
               hist_st (vars++reu) b H' st' /\
               Forall (sem_block_ck G2 H' b) blocks').
    Proof with eauto.
      induction d using block_ind2; intros * Hndup Hwc Hsem Hvalid Histst Hnorm;
        inv Hwc; inv Hsem; repeat inv_bind.
      - (* Equation *)
        eapply unnest_equation_sem in H0 as (H'&?&?&?&?); eauto.
        exists H'. split;[|split;[|split]]; auto.
        rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
        constructor; auto.
      - (* Reset *)
        rewrite ps_adds_rw_1 in Hvalid.
        assert (forall k, exists H',
                     Env.refines (@EqSt _) (mask_hist k r H0) (mask_hist k r H') /\
                     st_valid_reuse x0 (PSP.of_list (map fst vars)) (PSP.of_list (map fst (idck (fresh_in er) ++ reu))) /\
                     hist_st (vars ++ idck (fresh_in er) ++ reu) (maskb k r b) (mask_hist k r H') x0 /\
                     Forall (sem_block_ck G2 (mask_hist k r H') (maskb k r b)) (concat x)) as Hbck.
        { intros k. specialize (H11 k).
          eapply mmap_unnest_block_sem in H1 as (H'&Href1&Hvalid1&Histst1&Hsem1); eauto.
          2:ndup_simpl...
          2:rewrite idck_app, <-app_assoc in Histst; eauto using hist_st_mask.
          destruct Histst1 as (Hdom1&Hsc1).
          assert (Env.Equiv (@EqSt _) H' (mask_hist k r H')) as Heqmask.
          { unfold st_ids in Hdom1. rewrite <-map_fst_idck, <-map_app in Hdom1.
            eapply slower_mask_hist, sc_var_inv_slower_hist; [|eauto].
            eapply Forall_incl; eauto. }
          exists H'. repeat split; auto.
          1-3:rewrite <-Heqmask; auto.
          solve_forall. rewrite <-Heqmask; auto.
        }
        eapply consolidate_mask_hist
          with (P := fun k H'k => Env.refines (@EqSt _) (mask_hist k r H0) H'k /\
                               st_valid_reuse x0 (PSP.of_list (map fst vars)) (PSP.of_list (map fst (idck (fresh_in er)++reu))) /\
                               hist_st (vars++idck (fresh_in er)++reu) (maskb k r b) H'k x0 /\
                               Forall (sem_block_ck G2 H'k (maskb k r b)) (concat x))
               in Hbck as (H'&HH').
        2:{ intros ????? Heq (?&?&(?&?)&?); subst. repeat (split; auto).
            1-3:rewrite <-Heq; auto.
            eapply Forall_impl; [|eauto]; intros.
            rewrite <-Heq; auto.
        }
        2:{ intros ????? (_&_&(Hdom1&_)&_) (_&_&(Hdom2&_)&_) Hdom.
            eapply Env.dom_intro; intros.
            eapply Env.dom_use in Hdom1. eapply Env.dom_use in Hdom2. eapply Env.dom_use in Hdom.
            rewrite Hdom2, <-Hdom1; eauto.
        }
        setoid_rewrite ps_adds_rw_2 in HH'.
        assert (Env.refines (@EqSt _) H0 H') as Href1.
        { eapply refines_unmask; intros. eapply HH'. }
        eapply unnest_reset_sem with (vars:=vars) (H:=H') in H2 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2')...
        3:(solve_forall; repeat solve_incl).
        3:now rewrite <-length_clockof_numstreams, H5.
        3:(eapply sem_exp_refines; eauto).
        3:eapply (HH' 0).
        3:{ eapply hist_st_unmask; intros. eapply HH'; eauto. }
        2:{ intros * Hun. eapply unnest_exp_sem with (H:=H') (vs:=[sr]) in Hun as (H''&Href'&Hvalid'&Histst'&Hsem'&Hsem''); eauto.
            exists H''. split;[|split;[|split;[|split]]]; eauto.
            inv Hsem'; auto.
            ndup_r Hndup. repeat solve_incl.
            eapply sem_exp_refines; eauto.
            eapply (HH' 0).
            eapply hist_st_unmask; intros. eapply HH'; eauto.
        }
        exists H''. split;[|split;[|split]]; eauto.
        + etransitivity...
        + apply Forall_app. split; rewrite Forall_map.
          * eapply Forall_forall; intros ? Hin.
            econstructor; eauto.
            intros k. constructor; auto.
            specialize (HH' k) as (_&_&_&Hsem'). eapply Forall_forall in Hsem'; eauto.
            eapply sem_block_refines; [|eauto]. eapply refines_mask; eauto.
          * eapply Forall_impl; eauto; intros.
            constructor; auto.
    Qed.

    Corollary unnest_blocks_sem : forall vars b blocks H blocks' st st' reu,
        NoDup (map fst (flat_map anon_in_block blocks) ++ map fst reu) ->
        Forall (wc_block G1 (vars ++ st_clocks st)) blocks ->
        Forall (sem_block_ck G1 H b) blocks ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (flat_map anon_in_block blocks)) (PSP.of_list (map fst reu))) ->
        hist_st (vars++idck (flat_map anon_in_block blocks)++reu) b H st ->
        unnest_blocks G1 blocks st = (blocks', st') ->
        (exists H', Env.refines (@EqSt _) H H' /\
               st_valid_reuse st' (PSP.of_list (map fst vars)) (PSP.of_list (map fst reu)) /\
               hist_st (vars++reu) b H' st' /\
               Forall (sem_block_ck G2 H' b) blocks').
    Proof with eauto.
      intros * Hndup Hwc Hsem Hvalid Histst Hnorm.
      unfold unnest_blocks in Hnorm. repeat inv_bind.
      eapply mmap_unnest_block_sem in H0; eauto.
      solve_forall.
      eapply unnest_block_sem in H9; eauto.
    Qed.

    (** *** Preservation of sem_node *)

    Fact sem_var_In : forall H vs ss,
        Forall2 (sem_var H) vs ss ->
        Forall (fun v => Env.In v H) vs.
    Proof.
      intros. repeat rewrite_Forall_forall.
      apply In_nth with (d:=xH) in H2. destruct H2 as [n [Hn H2]].
      eapply H1 with (b:=default_stream) in Hn. 2,3:reflexivity.
      setoid_rewrite H2 in Hn.
      inv Hn. apply Env.find_1 in H4.
      apply Env.find_In in H4. auto.
    Qed.

    Lemma unnest_node_sem : forall f n ins outs,
        wc_global (Global G1.(enums) (n::G1.(nodes))) ->
        Ordered_nodes (Global G1.(enums) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(enums) ((unnest_node G1 n)::G2.(nodes))) ->
        sem_node_ck (Global G1.(enums) (n::G1.(nodes))) f ins outs ->
        sem_node_ck (Global G2.(enums) ((unnest_node G1 n)::G2.(nodes))) f ins outs.
    Proof with eauto.
      intros * HwcG Hord1 Hord2 Hsem.

      inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
      - erewrite find_node_now in Hfind; eauto. inv Hfind.
        (*The semantics of equations can be given according to G only *)
        eapply sem_blocks_ck_cons in H3; eauto. rename H3 into Hbck.
        2:{ inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }

        inv HwcG. destruct H4 as (Hwc&_).
        simpl in *.
        replace {| enums := enums G1; nodes := nodes G1 |} with G1 in Hbck, Hwc by (destruct G1; auto).
        remember (unnest_node G1 n0) as n'.
        unfold unnest_node in Heqn'; inv Heqn'.
        specialize (n_nodup n0) as Hnd.
        eapply unnest_blocks_sem with (reu:=[]) (vars:=idck (n_in n0 ++ n_vars n0 ++ n_out n0))
          in Hbck as (H'&Href&_&(Hdom&Hsc)&Hsem); eauto. 6:eapply surjective_pairing.
        eapply Snode with (H0:=H'); simpl; eauto.
        + erewrite find_node_now; eauto.
        + simpl. solve_forall. eapply sem_var_refines...
        + simpl. solve_forall. eapply sem_var_refines...
        + simpl.
          apply sem_blocks_ck_cons'; simpl...
          * eapply find_node_not_Is_node_in in Hord2.
            2:erewrite find_node_now; eauto. eauto.
          * eapply Forall_impl; [|eauto]; intros.
            destruct G2; auto.
        + simpl. constructor.
          * rewrite app_nil_r, map_fst_idck in Hdom.
            erewrite unnest_blocks_no_anon_in_blocks. 2:eapply surjective_pairing.
            rewrite app_nil_r.
            repeat rewrite <-app_assoc. rewrite (Permutation_app_comm (st_anns _)).
            repeat rewrite app_assoc. now rewrite map_app, <-app_assoc.
          * rewrite app_nil_r in Hsc.
            eapply Forall_incl; [eauto|].
            repeat rewrite idck_app. repeat rewrite <-app_assoc.
            apply incl_appr', incl_appr'. now rewrite Permutation_app_comm.
        + simpl; rewrite app_nil_r.
          apply fst_NoDupMembers.
          repeat apply NoDupMembers_app_r in Hnd; auto.
        + destruct Hwc as (_&_&_&Hwc).
          unfold st_clocks. rewrite init_st_anns, app_nil_r. eauto.
        + eapply init_st_valid_reuse.
          * replace (ps_adds _ PS.empty) with (ps_from_list (map fst (flat_map anon_in_block (n_blocks n0)))); auto.
            rewrite ps_from_list_ps_of_list.
            repeat rewrite ps_of_list_ps_to_list_Perm; repeat rewrite map_app; repeat rewrite <- app_assoc in *; auto.
            1,3:rewrite map_fst_idck. rewrite <-map_app, <- 2 app_assoc. apply fst_NoDupMembers; auto.
            repeat rewrite app_assoc in Hnd. apply NoDupMembers_app_l, fst_NoDupMembers in Hnd. now rewrite app_assoc.
            repeat apply  NoDupMembers_app_r in Hnd. apply fst_NoDupMembers in Hnd; auto.
          * apply norm1_not_in_elab_prefs.
          * rewrite <- ps_from_list_ps_of_list, PS_For_all_Forall'.
            pose proof (n_good n0) as (Good&_).
            eapply Forall_incl; [eauto|].
            rewrite map_fst_idck.
            repeat rewrite map_app.
            repeat apply incl_appr'. apply incl_appl. reflexivity.
          * replace (ps_adds _ PS.empty) with (ps_from_list (map fst (flat_map anon_in_block (n_blocks n0)))); auto.
            rewrite PS_For_all_Forall'.
            pose proof (n_good n0) as (Good&_).
            eapply Forall_incl; [eauto|].
            repeat rewrite map_app.
            repeat apply incl_appr. reflexivity.
        + rewrite app_nil_r.
          destruct H5 as (Hdom&Hsc).
          constructor; auto.
          * rewrite map_app, 2 map_fst_idck, <-map_app.
            unfold st_ids. rewrite init_st_anns, app_nil_r; auto.
          * unfold st_clocks. rewrite init_st_anns, app_nil_r.
            apply Forall_app; split; auto.
            eapply sc_var_inv_anon_in_blocks; eauto.
      - erewrite find_node_other in Hfind; eauto.
        eapply sem_node_ck_cons'...
        destruct G2; apply HGref.
        econstructor...
        eapply Forall_impl_In; [| eauto]. intros eq Hin Hsem.
        destruct G1; eapply sem_block_ck_cons...
        eapply find_node_later_not_Is_node_in in Hord1...
        intro Hisin. apply Hord1. unfold Is_node_in. rewrite Exists_exists.
        eexists...
    Qed.

  End unnest_node_sem.

  Fact wc_global_Ordered_nodes {prefs} : forall (G: @global prefs),
      wc_global G ->
      Ordered_nodes G.
  Proof.
    intros G Hwt.
    apply wl_global_Ordered_nodes; auto.
  Qed.
  Hint Resolve wc_global_Ordered_nodes.

  Lemma unnest_global_refines : forall G,
      wc_global G ->
      global_sem_refines G (unnest_global G).
  Proof with eauto.
    intros (enms&nds).
    induction nds; intros * Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      eapply unnest_global_wc, wc_global_Ordered_nodes in Hwc' ;
        unfold unnest_global in Hwc'; simpl in Hwc'.
      apply global_sem_ref_cons with (f:=n_name a)...
      + inv Hwc. eapply IHnds...
      + intros ins outs Hsem; simpl in *.
        change enms with ((Global enms (unnest_nodes enms nds)).(enums)).
        eapply unnest_node_sem...
        * inv Hwc; eauto.
        * change (Global enms (unnest_nodes enms nds)) with (unnest_global (Global enms nds)).
          eapply unnest_global_wc. inv Hwc; auto.
        * apply unnest_nodes_eq.
        * inv Hwc. eapply IHnds...
  Qed.

  Theorem unnest_global_sem : forall G f ins outs,
      wc_global G ->
      sem_node_ck G f ins outs ->
      sem_node_ck (unnest_global G) f ins outs.
  Proof.
    intros.
    eapply unnest_global_refines in H; eauto.
    specialize (H f ins outs); auto.
  Qed.

  (** ** Preservation of the semantics through the second pass *)

  Module Import CIStr := CoindIndexedFun Ids Op OpAux Cks CStr IStr.

  CoFixpoint const_val (b : Stream bool) (v : value) : Stream svalue :=
    (if Streams.hd b then present v else absent) ⋅ (const_val (Streams.tl b) v).

  Fact const_val_Cons : forall b bs v,
      const_val (b ⋅ bs) v =
      (if b then present v else absent) ⋅ (const_val bs v).
  Proof.
    intros b bs v.
    rewrite unfold_Stream at 1; reflexivity.
  Qed.

  Corollary const_val_nth : forall n bs c,
      (const_val bs c) # n = if bs # n then present c else absent.
  Proof.
    induction n; intros; destruct bs; rewrite const_val_Cons.
    - repeat rewrite Str_nth_0; auto.
    - repeat rewrite Str_nth_S; auto.
  Qed.

  Fact const_val_const : forall b c,
      const b c ≡ const_val b (Vscalar (sem_cconst c)).
  Proof.
    cofix const_val_const.
    intros [b0 b] c; simpl.
    constructor; simpl; auto.
  Qed.

  Fact const_val_enum : forall b c,
      enum b c ≡ const_val b (Venum c).
  Proof.
    cofix const_val_const.
    intros [b0 b] c; simpl.
    constructor; simpl; auto.
  Qed.

  Add Parametric Morphism : const_val
      with signature @EqSt _ ==> eq ==> @EqSt _
        as const_val_morph.
  Proof.
    cofix CoFix.
    intros ?? Heq ?.
    inv Heq. constructor; simpl; eauto.
    rewrite H. reflexivity.
  Qed.

  Section normfby_node_sem.
    Variable G1 : @global norm1_prefs.
    Variable G2 : @global norm2_prefs.

    (** *** Manipulation of initialization streams *)

    (** We want to specify the semantics of the init equations created during the normalization
      with idents stored in the env *)

    Definition false_val := Venum 0.
    Definition true_val := Venum 1.

    Lemma sfby_const : forall bs v,
        sfby v (const_val bs v) ≡ (const_val bs v).
    Proof.
      cofix CoFix.
      intros [b bs] v.
      rewrite const_val_Cons.
      destruct b; rewrite sfby_Cons; constructor; simpl; auto.
    Qed.

    Lemma case_false : forall bs xs ys,
        aligned xs bs ->
        aligned ys bs ->
        case (const_val bs false_val) [xs; ys] xs.
    Proof.
      cofix CoFix.
      intros [b bs] xs ys Hsync1 Hsync2.
      rewrite const_val_Cons. unfold false_val.
      inv Hsync1; inv Hsync2; econstructor; eauto.
      + eapply CoFix; eauto.
      + repeat constructor; simpl; congruence.
      + constructor. reflexivity.
      + eapply CoFix; eauto.
    Qed.

    Lemma sfby_fby1 : forall bs v y ys,
        aligned ys bs ->
        fby1 y (const_val bs v) ys (sfby y ys).
    Proof with eauto.
      cofix sfby_fby1.
      intros [b bs] v y ys Hsync.
      specialize (sfby_fby1 bs).
      inv Hsync;
        rewrite const_val_Cons; rewrite unfold_Stream; simpl.
      - constructor...
      - constructor...
    Qed.

    Lemma sfby_fby1' : forall y y0s ys zs,
        fby1 y y0s ys zs ->
        zs ≡ (sfby y ys).
    Proof.
      cofix CoFix.
      intros y y0s ys zs Hfby1.
      inv Hfby1; constructor; simpl; eauto.
    Qed.

    Lemma sfby_fby : forall b v y,
        aligned y b ->
        fby (const_val b v) y (sfby v y).
    Proof with eauto.
      cofix sfby_fby.
      intros [b bs] v y Hsync.
      rewrite const_val_Cons.
      rewrite unfold_Stream; simpl.
      destruct b; simpl; inv Hsync.
      - econstructor. eapply sfby_fby1...
      - econstructor; simpl...
    Qed.

    Definition init_stream bs :=
      sfby true_val (enum bs 0).

    Instance init_stream_Proper:
      Proper (@EqSt bool ==> @EqSt svalue) init_stream.
    Proof.
      intros bs bs' Heq1.
      unfold init_stream. rewrite Heq1. reflexivity.
    Qed.

    Lemma fby_case : forall bs v y0s ys zs,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        fby y0s ys zs ->
        case (sfby true_val (const_val bs false_val)) [(sfby v ys);y0s] zs.
    Proof with eauto.
      cofix CoFix.
    intros [b bs] v y0s ys zs Hsync Hfby1.
    apply fby_aligned in Hsync as [Hsync1 [Hsync2 Hsync3]]; [|auto].
    destruct b; inv Hsync1; inv Hsync2; inv Hsync3.
    - repeat rewrite const_val_Cons.
      inv Hfby1.
      repeat rewrite sfby_Cons. econstructor; simpl.
      + rewrite sfby_const.
        rewrite <- sfby_fby1'...
        apply case_false...
      + repeat constructor; simpl; auto; congruence.
      + constructor. reflexivity.
    - rewrite const_val_Cons. repeat rewrite sfby_Cons.
      inv Hfby1.
      constructor; auto.
      eapply CoFix; eauto.
    Qed.

    Corollary fby_init_stream_case : forall bs v y0s ys zs,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        fby y0s ys zs ->
        case (init_stream bs) [(sfby v ys); y0s] zs.
      intros * Hsync Hfby1.
      eapply fby_case in Hfby1; eauto.
      unfold init_stream.
      rewrite const_val_enum; eauto.
    Qed.

    Definition value_to_bool' (v : value) :=
      match v with
      | Venum tag => if (tag ==b true_tag) then Some true
                    else if (tag ==b false_tag) then Some false
                         else None
      | _ => None
      end.

    Lemma arrow_case : forall bs y0s ys zs,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        arrow y0s ys zs ->
        case (sfby true_val (const_val bs false_val)) [ys;y0s] zs.
    Proof with eauto.
      cofix CoFix.
      intros [b bs] y0s ys zs Hsync Harrow.
      apply arrow_aligned in Hsync as [Hsync1 [Hsync2 Hsync3]]; [|auto].
      destruct b; inv Hsync1; inv Hsync2; inv Hsync3; inv Harrow.
      - rewrite const_val_Cons, sfby_Cons.
        econstructor; simpl.
        + rewrite sfby_const.
          clear - H0 H1 H2 H3. revert bs vs vs0 vs1 H1 H2 H3 H0.
          cofix CoFix. intros * Hsync1 Hsync2 Hsync3 Harrow.
          destruct bs as [[|] bs]; inv Hsync1; inv Hsync2; inv Hsync3; inv Harrow.
          1,2:rewrite const_val_Cons; econstructor; simpl; eauto.
          repeat constructor; auto; simpl; congruence.
          constructor. reflexivity.
        + repeat constructor; auto; simpl; congruence.
        + constructor. reflexivity.
      - rewrite const_val_Cons, sfby_Cons.
        constructor; simpl; eauto.
    Qed.

    Corollary arrow_init_stream_case : forall bs y0s ys zs,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        arrow y0s ys zs ->
        case (init_stream bs) [ys;y0s] zs.
    Proof.
      intros * Hsync Harrow.
      eapply arrow_case in Harrow; eauto.
      unfold init_stream.
      rewrite const_val_enum; auto.
    Qed.

    Lemma ac_sfby : forall v0 xs,
        abstract_clock (sfby v0 xs) ≡ abstract_clock xs.
    Proof.
      cofix CoFix. intros v0 [x xs].
      rewrite sfby_Cons.
      destruct x; constructor; simpl; auto.
    Qed.

    Lemma init_stream_ac : forall bs,
        abstract_clock (init_stream bs) ≡ bs.
    Proof.
      intros bs.
      unfold init_stream.
      rewrite ac_sfby. apply ac_enum.
    Qed.

    (** *** Additional stuff *)

    Import NormFby.

    Fact st_valid_after_NoDupMembers {A} : forall st (vars : list (ident * A)),
        NoDupMembers vars ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        NoDupMembers (vars++st_anns st).
    Proof.
      intros * Hndup Hvalid.
      eapply st_valid_NoDup in Hvalid.
      rewrite ps_of_list_ps_to_list_Perm in Hvalid. 2:rewrite <- fst_NoDupMembers; auto.
      unfold st_ids in Hvalid.
      rewrite Permutation_app_comm, <- map_app, <- fst_NoDupMembers in Hvalid; auto.
    Qed.

    Fact fresh_ident_refines' {B} : forall vars H a id (v : Stream svalue) (st st' : fresh_st B),
        st_valid_after st (PSP.of_list vars) ->
        Env.dom H (vars++st_ids st) ->
        fresh_ident norm2 a st = (id, st') ->
        Env.refines (@EqSt _) H (Env.add id v H).
    Proof with eauto.
      intros * Hvalid Hdom Hfresh.
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

    Fact fresh_ident_hist_st' : forall vars b ty ck id v H st st',
        st_valid_after st (PSP.of_list (map fst vars)) ->
        sem_clock H b ck (abstract_clock v) ->
        fresh_ident norm2 (ty, ck) st = (id, st') ->
        hist_st vars b H st ->
        hist_st vars b (Env.add id v H) st'.
    Proof with auto.
      intros * Hvalid Hsem Hfresh [H1 H2].
      assert (~In id (st_ids st)) as Hnin by (eapply Facts.fresh_ident_nIn in Hfresh; eauto).
      assert (st_valid_after st' (PSP.of_list (map fst vars))) as Hvalid2 by eauto.
      assert (Hfresh':=Hfresh). apply fresh_ident_anns in Hfresh'.
      assert (Env.refines (@EqSt _) H (Env.add id v H)) as Href.
      { eapply fresh_ident_refines' in Hfresh; eauto. }
      repeat split.
      - eapply fresh_ident_dom; eauto.
      - unfold st_clocks, LCS.sc_var_inv' in *.
        rewrite Hfresh'; simpl.
        unfold sc_var_inv.
        rewrite <- Permutation_middle. constructor.
        + exists v; split.
          * econstructor. eapply Env.add_1. 1,2:reflexivity.
          * eapply LCS.sem_clock_refines; eauto.
        + eapply LCS.sc_var_inv_refines with (H:=H); eauto.
    Qed.

    Lemma sem_clock_when_const : forall H bs bs' bs'' cs ck id x tx c,
        sem_clock H bs ck bs' ->
        sem_clock H bs (Con ck id (tx, x)) bs'' ->
        sem_var H id cs ->
        when x (const bs' c) cs (const bs'' c).
    Proof.
      intros * Hcl1 Hcl2 Hvar.
      rewrite when_spec. intros n.
      rewrite sem_clock_equiv in Hcl1, Hcl2.
      apply CIStr.sem_var_impl in Hvar.
      specialize (Hcl1 n). specialize (Hcl2 n). specialize (Hvar n).
      unfold tr_Stream in *; simpl in *.
      inv Hcl2; (eapply IStr.sem_var_instant_det in Hvar; eauto;
                 eapply IStr.sem_clock_instant_det in Hcl1; eauto).
      - right. right.
        exists (Vscalar (sem_cconst c)). repeat split; auto using const_true.
      - left.
        repeat split; auto using const_false.
      - right. left.
        exists (Vscalar (sem_cconst c)). exists b'. repeat split; eauto using const_true, const_false.
    Qed.

    Corollary add_whens_const_sem_exp : forall H b ck ty b' c,
        sem_clock H b ck b' ->
        sem_exp_ck G2 H b (add_whens (Econst c) ty ck) [const b' c].
    Proof.
      induction ck; try destruct p; intros * Hsem; assert (Hsem':=Hsem); inv Hsem'; simpl.
      constructor. rewrite H1; reflexivity.
      1,2,3: (eapply Swhen; eauto; simpl;
              repeat constructor; try eapply IHck; eauto;
              repeat constructor; eapply sem_clock_when_const; eauto).
    Qed.

    Lemma sem_clock_when_enum : forall H bs bs' bs'' cs ck id x tx c,
        sem_clock H bs ck bs' ->
        sem_clock H bs (Con ck id (tx, x)) bs'' ->
        sem_var H id cs ->
        when x (enum bs' c) cs (enum bs'' c).
    Proof.
      intros * Hcl1 Hcl2 Hvar.
      rewrite when_spec. intros n.
      rewrite sem_clock_equiv in Hcl1, Hcl2.
      apply CIStr.sem_var_impl in Hvar.
      specialize (Hcl1 n). specialize (Hcl2 n). specialize (Hvar n).
      unfold tr_Stream in *; simpl in *.
      inv Hcl2; (eapply IStr.sem_var_instant_det in Hvar; eauto;
                 eapply IStr.sem_clock_instant_det in Hcl1; eauto).
      - right. right.
        exists (Venum c). repeat split; auto using enum_true.
      - left.
        repeat split; auto using enum_false.
      - right. left.
        exists (Venum c). exists b'. repeat split; eauto using enum_true, enum_false.
    Qed.

    Corollary add_whens_enum_sem_exp : forall H b ck ty b' c,
        sem_clock H b ck b' ->
        sem_exp_ck G2 H b (add_whens (Eenum c ty) ty ck) [enum b' c].
    Proof.
      induction ck; try destruct p; intros * Hsem; assert (Hsem':=Hsem); inv Hsem'; simpl.
      constructor. rewrite H1; reflexivity.
      1,2,3: (eapply Swhen; eauto; simpl;
              repeat constructor; try eapply IHck; eauto;
              repeat constructor; eapply sem_clock_when_enum; eauto).
    Qed.

    Fact init_var_for_clock_sem : forall vars bs H ck bs' x eqs' st st',
        sem_clock H bs ck bs' ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars bs H st ->
        init_var_for_clock ck st = (x, eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars bs H' st' /\
            sem_var H' x (init_stream bs') /\
            Forall (sem_equation_ck G2 H' bs) eqs').
    Proof with eauto.
      intros * Hsemc Hvalid Histst Hinit.
      unfold init_var_for_clock in Hinit.
      destruct (fresh_ident _ _) eqn:Hident. repeat inv_bind.
      assert (st_valid_after st' (PSP.of_list (map fst vars))) as Hvalid1 by eauto.
      remember (Env.add x (init_stream bs' (* rs' *)) H) as H'.
      assert (Env.refines (@EqSt _) H H') as Href1.
      { subst. eapply fresh_ident_refines' in Hident; eauto.
        now destruct Histst. }
      assert (hist_st vars bs H' st') as Histst1.
      { subst. eapply fresh_ident_hist_st' in Hident...
        destruct Histst as (Hdom&Hsc).
        now rewrite init_stream_ac. }
      assert (st_valid_after st' (PSP.of_list (map fst vars))) as Hvalid2 by eauto.
      exists H'. repeat (split; eauto).
      + rewrite HeqH'. econstructor. 2:reflexivity.
        apply Env.add_1. reflexivity.
      + repeat constructor.
        apply Seq with (ss:=[[(init_stream bs' (* rs' *))]]); simpl; repeat constructor.
        * econstructor; repeat constructor.
          1,2:apply add_whens_enum_sem_exp; eauto using LCS.sem_clock_refines.
          repeat constructor. unfold init_stream.
          repeat rewrite const_val_const; subst.
          do 2 rewrite const_val_enum. apply sfby_fby; simpl; eauto.
          rewrite <- const_val_enum. apply enum_aligned.
        * econstructor. 2:reflexivity.
          rewrite HeqH'. apply Env.add_1. reflexivity.
    Qed.

    Hypothesis Hiface : global_iface_eq G1 G2.
    Hypothesis HGref : global_sem_refines G1 G2.

    Hypothesis HwcG1 : wc_global G1.

    Fact fby_iteexp_sem : forall vars bs H e0 e ty nck y0 y z e' eqs' st st' ,
        clockof e0 = [fst nck] ->
        wc_exp G1 (vars++st_clocks st) e0 ->
        wc_exp G1 (vars++st_clocks st) e ->
        sem_exp_ck G1 H bs e0 [y0] ->
        sem_exp_ck G1 H bs e [y] ->
        fby y0 y z ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars bs H st ->
        fby_iteexp e0 e (ty, nck) st = (e', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars bs H' st' /\
            sem_exp_ck G2 H' bs e' [z] /\
            Forall (sem_equation_ck G2 H' bs) eqs').
    Proof with eauto.
      intros * Hck Hwc0 Hwc Hsem0 Hsem Hfby Hvalid Histst Hiteexp.
      assert (st_follows st st') as Hfollows by (eapply fby_iteexp_st_follows; eauto).
      destruct nck as [ck ?]; simpl in *.
      unfold fby_iteexp in Hiteexp; repeat inv_bind.
      assert (Hsck:=Hsem0). eapply sc_exp with (env:=vars++st_clocks st) in Hsck... simpl in Hsck.
      2:(destruct Histst; auto).
      rewrite Hck in Hsck. eapply Forall2_singl in Hsck.

      eapply init_var_for_clock_sem in H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]...
      remember (abstract_clock y0) as bs'.
      remember (match ty with Tprimitive cty => Vscalar (Op.sem_cconst (Op.init_ctype cty))
                         | Tenum (_, n) => Venum 0 end) as v0.
      remember (sfby v0 y) as y'.
      remember (Env.add x2 y' H') as H''.
      assert (Env.refines (@EqSt _) H' H'') by (subst; destruct Histst1; eapply fresh_ident_refines' in H1; eauto).
      assert (hist_st vars bs H'' st') as Histst2.
      { subst. eapply fresh_ident_hist_st'...
        rewrite ac_sfby.
        rewrite ac_fby2, <- ac_fby1; eauto. eapply sem_clock_refines... }
      exists H''. repeat (split; eauto); try constructor.
      - etransitivity; eauto.
      - eapply Scase with (s:=(init_stream bs')) (vs:=[[[y']];[[y0]]]) (vd:=[[y0]]). 2:repeat constructor.
        + econstructor. eapply sem_var_refines...
        + intros ? Heq; inv Heq. repeat constructor.
          econstructor. eapply Env.add_1. 1,2:reflexivity.
        + intros ? Heq; inv Heq.
        + constructor; [|constructor]; auto; intros; try congruence.
          constructor; auto. constructor; auto. reflexivity.
        + repeat econstructor; eauto.
          eapply sem_ref_sem_exp...
          eapply sem_exp_refines; [|eauto]; etransitivity...
        + repeat econstructor; eauto.
          subst. eapply fby_init_stream_case; eauto using ac_aligned.
      - apply Seq with (ss:=[[y']]); repeat constructor.
        + eapply Sfby with (s0ss:=[[const_val bs' v0]]) (sss:=[[y]]); repeat constructor.
          * destruct ty as [|(?&?)]; simpl; rewrite Heqv0; subst.
            -- eapply sem_exp_ck_morph; eauto. 1,2:reflexivity.
               econstructor; eauto. eapply const_val_const.
               eapply add_whens_const_sem_exp.
               eapply sem_clock_refines; [|eauto]. etransitivity...
            -- eapply sem_exp_ck_morph; eauto. 1,2:reflexivity.
               econstructor; eauto. eapply const_val_enum.
               eapply add_whens_enum_sem_exp.
               eapply sem_clock_refines; [|eauto]. etransitivity...
          * eapply sem_ref_sem_exp...
            eapply sem_exp_refines; [|eauto]; etransitivity...
          (* * eapply bools_ofs_empty. *)
          * rewrite Heqy'.
            eapply sfby_fby.
            eapply fby_aligned in Hfby as [_ [? _]]; eauto.
            left. rewrite Heqbs'. apply ac_aligned.
        + econstructor.
          rewrite HeqH''. apply Env.add_1. 1,2:reflexivity.
      - solve_forall. eapply sem_equation_refines...
    Qed.

    Fact arrow_iteexp_sem : forall vars bs H e0 e ty nck y0 y z e' eqs' st st',
        clockof e0 = [fst nck] ->
        wc_exp G1 (vars++st_clocks st) e0 ->
        wc_exp G1 (vars++st_clocks st) e ->
        sem_exp_ck G1 H bs e0 [y0] ->
        sem_exp_ck G1 H bs e [y] ->
        arrow y0 y z ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars bs H st ->
        arrow_iteexp e0 e (ty, nck) st = (e', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars bs H' st' /\
            sem_exp_ck G2 H' bs e' [z] /\
            Forall (sem_equation_ck G2 H' bs) eqs').
    Proof with eauto.
      intros * Hck Hwc0 Hwc1 Hsem0 Hsem Harrow Hvalid Histst Hiteexp.
      assert (st_follows st st') as Hfollows by (eapply arrow_iteexp_st_follows; eauto).
      destruct nck as [ck ?]; simpl in *.
      unfold arrow_iteexp in Hiteexp. repeat inv_bind.
      assert (Hsck:=Hsem0). eapply sc_exp with (env:=vars++st_clocks st) in Hsck... simpl in Hsck.
      2:(destruct Histst; auto).
      rewrite Hck in Hsck. eapply Forall2_singl in Hsck.

      eapply init_var_for_clock_sem in H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]...
      remember (abstract_clock y0) as bs'.
      exists H'. repeat (split; auto).
       eapply Scase with (s:=(init_stream bs')) (vs:=[[[y]];[[y0]]]) (vd:=[[y0]]). 2:repeat constructor.
      - econstructor; eauto.
      - intros ? Heq; inv Heq. repeat constructor.
        eapply sem_ref_sem_exp...
        eapply sem_exp_refines...
      - intros ? Heq; inv Heq.
      - do 2 (constructor; auto); try congruence.
        intros. constructor; auto. reflexivity.
      - constructor; auto.
        eapply sem_ref_sem_exp...
        eapply sem_exp_refines...
      - simpl. repeat econstructor.
        eapply arrow_init_stream_case; eauto.
        subst. left. eapply ac_aligned.
    Qed.

    Fact normfby_equation_sem : forall vars bs H to_cut equ eqs' st st' ,
        wc_equation G1 (vars++st_clocks st) equ ->
        sem_equation_ck G1 H bs equ ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars bs H st ->
        normfby_equation to_cut equ st = (eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars bs H' st' /\
            Forall (sem_equation_ck G2 H' bs) eqs').
    Proof with eauto.
      intros * Hwc Hsem Hvalid Histst Hfby.
      inv_normfby_equation Hfby to_cut equ; try destruct x2 as (ty&ck&name).
      - (* constant fby *)
        destruct PS.mem; repeat inv_bind.
        + inv Hsem. inv H6; inv H5.
          simpl in H7; rewrite app_nil_r in H7. inv H7; inv H6.
          assert (Hsem':=H3). inversion_clear H3 as [| | | | |???????? Hsem0 Hsem1 Hsem| | | | |].
          inv Hsem0; inv H6. inv Hsem1; inv H7.
          simpl in Hsem; repeat rewrite app_nil_r in Hsem. inv Hsem; inv H9.
          destruct Hwc as [Hwc _]. apply Forall_singl in Hwc. assert (Hwc':=Hwc). inv Hwc'.
          apply Forall_singl in H7. rewrite Forall2_eq in H10; simpl in H10; rewrite app_nil_r in H10.

          remember (Env.add x2 y0 H) as H'.
          assert (Env.refines (@EqSt _) H H') as Href.
          { subst. destruct Histst as [Hdom _].
            eapply fresh_ident_refines' in H0... }
          assert (hist_st vars bs H' st') as Histst1.
          { subst. eapply fresh_ident_hist_st' in H0...
            eapply sc_exp in Hsem'... 2:destruct Histst; auto.
            simpl in Hsem'. inv Hsem'; auto.
          }
          exists H'. repeat (split; eauto).
          repeat constructor; auto.
          * eapply Seq with (ss:=[[y0]]); simpl; repeat constructor.
            2:eapply sem_var_refines; eauto.
            rewrite HeqH'. econstructor. eapply Env.add_1. 1,2:reflexivity.
          * eapply Seq with (ss:=[[y0]]); simpl; repeat constructor.
            -- eapply sem_ref_sem_exp... eapply sem_exp_refines...
            -- rewrite HeqH'. econstructor. eapply Env.add_1. 1,2:reflexivity.
        + exists H. repeat (split; eauto).
          constructor; auto.
          eapply sem_ref_sem_equation; eauto.
      - (* fby *)
        destruct Hwc as [Hwc _]. apply Forall_singl in Hwc. inv Hwc.
        apply Forall_singl in H4. rewrite Forall2_eq in H6; simpl in H6; rewrite app_nil_r in H6.
        inv Hsem. inv H11; inv H10. simpl in H12; rewrite app_nil_r in H12. inv H12; inv H11.
        inversion_clear H3 as [| | | | |???????? Hsem0 Hsem1 Hsem| | | | |].
        inv Hsem0; inv H11. inv Hsem1; inv H12.
        simpl in Hsem; repeat rewrite app_nil_r in Hsem. inv Hsem; inv H14.
        eapply fby_iteexp_sem with (nck:=(ck, name)) in H0 as [H' [Href1 [Hvalid1 [Hhistst1 [Hsem' Hsem'']]]]]...
        2:{ inv H5; auto. }
        exists H'. repeat (split; eauto).
        constructor; auto.
        eapply Seq with (ss:=[[y0]]); simpl; repeat constructor; auto.
        eapply sem_var_refines; eauto.
      - (* arrow *)
        destruct Hwc as [Hwc _]. apply Forall_singl in Hwc. inv Hwc.
        apply Forall_singl in H4. rewrite Forall2_eq in H6; simpl in H6; rewrite app_nil_r in H6.
        inv Hsem. inv H11; inv H10. simpl in H12; rewrite app_nil_r in H12. inv H12; inv H11.
        inversion_clear H3 as [| | | | | |???????? Hsem0 Hsem1 Hsem| | | |].
        inv Hsem0; inv H11. inv Hsem1; inv H12.
        simpl in Hsem; repeat rewrite app_nil_r in Hsem. inv Hsem; inv H14.
        eapply arrow_iteexp_sem with (nck:=(ck, name)) in H0 as [H' [Href1 [Hvalid1 [Hhistst1 [Hsem' Hsem'']]]]]...
        2:{ inv H5; auto. }
        exists H'. repeat (split; eauto).
        constructor; auto.
        eapply Seq with (ss:=[[y0]]); simpl; repeat constructor; auto.
        eapply sem_var_refines; eauto.
      - (* other *)
        exists H. repeat (split; eauto).
        constructor; auto.
        eapply sem_ref_sem_equation; eauto.
    Qed.

    Lemma normfby_block_sem : forall vars to_cut d blocks' bs H st st' ,
        unnested_block G1 d ->
        wc_block G1 (vars++st_clocks st) d ->
        sem_block_ck G1 H bs d ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars bs H st ->
        normfby_block to_cut d st = (blocks', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars bs H' st' /\
            Forall (sem_block_ck G2 H' bs) blocks').
    Proof.
      induction d using block_ind2; intros * Hun Hwc Hsem Hvalid Hist Hnorm;
        inv Hun; inv Hwc; inv Hsem; repeat inv_bind.
      - (* eq *)
        eapply normfby_equation_sem in H0 as (H'&?&?&?&?); eauto.
        exists H'. repeat (split; auto).
        rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
        constructor; auto.
      - (* reset *)
        simpl in Hnorm; cases; repeat inv_bind.
        apply Forall_singl in H. apply Forall_singl in H4.
        assert (forall k, exists H'k,
                     Env.refines (@EqSt _) (mask_hist k r H0) (mask_hist k r H'k) /\
                     st_valid_after st' (PSP.of_list (map fst vars)) /\
                     hist_st vars (maskb k r bs) (mask_hist k r H'k) st' /\
                     Forall (sem_block_ck G2 (mask_hist k r H'k) (maskb k r bs)) x0) as Hblocks'.
        { intros k. specialize (H12 k).
          apply Forall_singl in H12. eapply H in H12 as (H'k&?&?&(?&?)&?); eauto.
          2:eapply hist_st_mask; eauto.
          assert (slower_hist H'k (maskb k r bs)) as Hslow.
          { eapply sc_var_inv_slower_hist; eauto.
            unfold st_clocks. rewrite map_app, map_fst_idck; auto. }
          eapply slower_mask_hist in Hslow.
          exists H'k. repeat (split; auto).
          - rewrite <-Hslow; auto.
          - rewrite <-Hslow; auto.
          - rewrite <-Hslow; auto.
          - eapply Forall_impl; [|eauto]; intros.
            rewrite <-Hslow; auto.
        }
        eapply consolidate_mask_hist
          with (P := fun k H'k => Env.refines (@EqSt _) (mask_hist k r H0) H'k /\
                               st_valid_after st' (PSP.of_list (map fst vars)) /\
                               hist_st vars (maskb k r bs) H'k st' /\
                               Forall (sem_block_ck G2 H'k (maskb k r bs)) x0)
          in Hblocks' as (H'&HH').
        2:{ intros ????? Heq (?&?&(?&?)&?); subst. repeat (split; auto).
            1-3:rewrite <-Heq; auto.
            eapply Forall_impl; [|eauto]; intros.
            rewrite <-Heq; auto.
        }
        2:{ intros ????? (_&_&(Hdom1&_)&_) (_&_&(Hdom2&_)&_) Hdom.
            eapply Env.dom_intro; intros.
            eapply Env.dom_use in Hdom1. eapply Env.dom_use in Hdom2. eapply Env.dom_use in Hdom.
            rewrite Hdom2, <-Hdom1; eauto.
        }
        exists H'.
        assert (Env.refines (@EqSt _) H0 H') as Href.
        { eapply refines_unmask; intros.
          specialize (HH' k) as (?&_); eauto.
        }
        repeat (split; auto).
        + specialize (HH' 0) as (_&?&_&_); auto.
        + specialize (HH' 0) as (_&_&(Hdom&_)&_); auto.
          setoid_rewrite Env.dom_map in Hdom; auto.
        + eapply sc_var_inv_unmask.
          intros k. specialize (HH' k) as (_&_&(_&?)&_); eauto.
        + rewrite Forall_map. eapply Forall_forall; intros.
          econstructor; eauto.
          * eapply sem_ref_sem_exp; eauto. eapply sem_exp_refines; eauto.
          * intros ?. specialize (HH' k) as (_&_&_&?).
            constructor; auto. eapply Forall_forall in H7; eauto.
    Qed.

    Fact normfby_blocks_sem : forall vars bs to_cut blocks blocks' H st st' ,
        Forall (unnested_block G1) blocks ->
        Forall (wc_block G1 (vars++st_clocks st)) blocks ->
        Forall (sem_block_ck G1 H bs) blocks ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars bs H st ->
        normfby_blocks to_cut blocks st = (blocks', st') ->
        (exists H',
           Env.refines (@EqSt _) H H' /\
           hist_st vars bs H' st' /\
           Forall (sem_block_ck G2 H' bs) blocks').
    Proof with eauto.
      induction blocks; intros * Hunt Hwc Hsem Hvalid Hhistst Hfby;
        unfold normfby_blocks in Hfby; simpl in *; repeat inv_bind.
      - exists H; simpl; auto.
      - assert (normfby_blocks to_cut blocks x1 = (concat x2, st')) as Hnorm.
        { unfold normfby_blocks; repeat inv_bind.
          repeat eexists; eauto. repeat inv_bind; auto. }
        inv Hunt. inv Hwc. inv Hsem.
        assert (st_follows st x1) as Hfollows by (eapply normfby_block_st_follows in H0; eauto).
        eapply normfby_block_sem in H0 as [H' [Href1 [Hvalid1 [Hhistst1 Hsem1]]]]. 2-11:eauto.
        assert (Forall (sem_block_ck G1 H' bs) blocks) as Hsem'.
        { solve_forall. eapply sem_block_refines... } clear H9.
        eapply IHblocks in Hnorm as (H''&Href&Hdom&Hsem2). 2-11:eauto.
        2:solve_forall; repeat solve_incl.
        + exists H''. split;[|split]...
          * etransitivity...
          * simpl. apply Forall_app; split; eauto.
            solve_forall. eapply sem_block_refines...
    Qed.

    Fact init_st_hist_st {prefs} : forall b H (n: @node prefs),
        Env.dom H (List.map fst (n_in n++n_vars n++n_out n)) ->
        sc_var_inv (idck (n_in n++n_vars n++n_out n)) H b ->
        hist_st (idck (n_in n++n_vars n++n_out n)) b H init_st.
    Proof.
      intros b H n Hdom Hinv.
      repeat constructor.
      - unfold st_ids.
        rewrite init_st_anns; simpl.
        rewrite app_nil_r, map_fst_idck. assumption.
      - unfold st_clocks. rewrite init_st_anns; simpl.
        rewrite app_nil_r. assumption.
    Qed.

  End normfby_node_sem.

  Lemma normfby_node_sem : forall G1 G2 f n ins outs,
      global_iface_eq G1 G2 ->
      global_sem_refines G1 G2 ->
      unnested_global (Global G1.(enums) (n::G1.(nodes))) ->
      wc_global (Global G1.(enums) (n::G1.(nodes))) ->
      wc_global G2 ->
      Ordered_nodes (Global G1.(enums) (n::G1.(nodes))) ->
      Ordered_nodes (Global G2.(enums) ((normfby_node n)::G2.(nodes))) ->
      sem_node_ck (Global G1.(enums) (n::G1.(nodes))) f ins outs ->
      sem_node_ck (Global G2.(enums) ((normfby_node n)::G2.(nodes))) f ins outs.
  Proof with eauto.
    intros * Hiface Href Hunt HwcG HwcG' Hord1 Hord2 Hsem.
    assert (Ordered_nodes (Global G2.(enums) (normfby_node n :: G2.(nodes)))) as Hord'.
    { inv Hord2. destruct H1. constructor; [split|]... }

    inv Hsem; assert (Hfind:=H0). destruct (ident_eq_dec (n_name n) f).
    - erewrite find_node_now in H0; eauto. inv H0.
      inversion_clear HwcG as [|?? (?&?)].
      (* The semantics of equations can be given according to G only *)
      eapply sem_blocks_ck_cons in H3; eauto.
      2:{ inv Hord1. intro contra. apply H9 in contra as [? _]; auto. }
      rename H3 into Hbcks.

      remember (normfby_node n0) as n'.
      unfold normfby_node in Heqn'; inv Heqn'.
      specialize (n_nodup n0) as Hnd.
      eapply normfby_blocks_sem with (vars:=idck (n_in n0 ++ n_vars n0 ++ n_out n0))
        in Hbcks as (H'&Hre'&(Hdom&Hsc)&Heqs'')... 7:eapply surjective_pairing.
      eapply Snode with (H3:=H'); simpl...
      + erewrite find_node_now...
      + simpl. solve_forall. eapply sem_var_refines...
      + simpl. solve_forall. eapply sem_var_refines...
      + simpl.
        apply sem_blocks_ck_cons'; simpl...
        eapply find_node_not_Is_node_in in Hord2.
        2:erewrite find_node_now; eauto. eauto.
      + simpl. clear - Hdom Hsc Hunt. destruct (normfby_blocks _ _) eqn:Hbcks.
        eapply normfby_blocks_no_anon in Hbcks; eauto. 4:reflexivity.
        3:{ inv Hunt. destruct H1; eauto. }
        2:{ eapply init_st_valid.
            - apply norm2_not_in_norm1_prefs.
            - rewrite PS_For_all_Forall'.
              pose proof (n_good n0) as (Good&_).
              eapply Forall_incl; [eauto|].
              repeat rewrite map_app.
              do 2 apply incl_appr. apply incl_appl. reflexivity.
        }
        constructor; simpl.
        * rewrite Hbcks, app_nil_r.
          rewrite map_fst_idck in Hdom.
          repeat rewrite <-app_assoc. rewrite (Permutation_app_comm (st_anns _)).
          repeat rewrite app_assoc. now rewrite map_app, <-app_assoc.
        * eapply Forall_incl; eauto.
          repeat rewrite idck_app. repeat rewrite <-app_assoc.
          apply incl_appr', incl_appr'. now rewrite Permutation_app_comm.
      + destruct G1, G2; auto.
      + inv Hunt. inv H8. simpl in H3. inv H3; auto.
      + destruct H0 as (_&_&_&Hwc).
        unfold st_clocks. rewrite init_st_anns, app_nil_r. eauto.
      + eapply init_st_valid.
        * apply norm2_not_in_norm1_prefs.
        * rewrite <- ps_from_list_ps_of_list, PS_For_all_Forall'.
          pose proof (n_good n0) as (Good&_).
          eapply Forall_incl; [eauto|].
          rewrite map_fst_idck.
          repeat rewrite map_app.
          repeat apply incl_appr'. apply incl_appl. reflexivity.
      + inv H5. eapply init_st_hist_st; eauto.
        erewrite unnested_blocks_no_anon, app_nil_r in H3; eauto.
        inv Hunt. destruct H9; eauto.
    - erewrite find_node_other in Hfind; eauto.
      eapply sem_node_ck_cons'...
      destruct G2; apply Href.
      econstructor...
      eapply Forall_impl_In; [| eauto]. intros eq Hin Hsem.
      destruct G1; eapply sem_block_ck_cons...
      eapply find_node_later_not_Is_node_in in Hord1...
      intro Hisin. apply Hord1. unfold Is_node_in. rewrite Exists_exists.
      eexists...
  Qed.

  Fact normfby_global_names' : forall nds,
      Forall2 (fun n n' => n_name n = n_name n') nds (map normfby_node nds).
  Proof.
    induction nds; simpl; auto.
  Qed.

  Lemma normfby_global_refines : forall G,
      unnested_global G ->
      wc_global G ->
      global_sem_refines G (normfby_global G).
  Proof with eauto.
    intros (enms&nds).
    induction nds; intros * Hunt Hwc; simpl.
    - apply global_sem_ref_nil.
    - apply global_sem_ref_cons with (f:=n_name a)...
      + eapply normfby_global_wc, wc_global_Ordered_nodes in Hwc;
          unfold normfby_global in Hwc; simpl in Hwc...
      + inv Hunt; inv Hwc. eapply IHnds...
      + intros ins outs Hsem; simpl.
        eapply normfby_node_sem with (G1:=(Global enms nds)) (G2:=(Global _ _)) in Hsem...
        * apply normfby_global_eq.
        * inv Hunt; inv Hwc. eapply IHnds...
        * eapply normfby_global_wc in Hwc... inv Hwc...
        * eapply wc_global_Ordered_nodes.
          eapply normfby_global_wc in Hwc...
  Qed.

  Corollary normfby_global_sem : forall G f ins outs,
      unnested_global G ->
      wc_global G ->
      sem_node_ck G f ins outs ->
      sem_node_ck (normfby_global G) f ins outs.
  Proof.
    intros.
    eapply normfby_global_refines in H; eauto.
    apply H; auto.
  Qed.

  (** ** Conclusion *)

  Theorem normalize_global_sem : forall G f ins outs,
      wc_global G ->
      sem_node_ck G f ins outs ->
      sem_node_ck (normalize_global G) f ins outs.
  Proof with eauto.
    intros  * Hwc Hsem.
    unfold normalize_global.
    eapply normfby_global_sem.
    - eapply unnest_global_unnested_global...
    - eapply unnest_global_wc...
    - eapply unnest_global_sem...
  Qed.

End CORRECTNESS.

Module CorrectnessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (LCA : LCAUSALITY Ids Op OpAux Cks Syn)
       (Ty : LTYPING Ids Op OpAux Cks Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (Lord : LORDERED Ids Op OpAux Cks Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Syn Lord CStr)
       (LClockSem : LCLOCKSEMANTICS Ids Op OpAux Cks Syn Clo LCA Lord CStr Sem)
       (Norm : NORMALIZATION Ids Op OpAux Cks Syn)
       <: CORRECTNESS Ids Op OpAux Cks CStr Syn LCA Ty Clo Lord Sem LClockSem Norm.
  Include CORRECTNESS Ids Op OpAux Cks CStr Syn LCA Ty Clo Lord Sem LClockSem Norm.
End CorrectnessFun.
