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
From Velus Require Import Lustre.Normalization.NCausality.

(** * Correctness of the Normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type CORRECTNESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import CStr : COINDSTREAMS Ids Op OpAux Cks)
       (IStr : INDEXEDSTREAMS Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (LCA        : LCAUSALITY Ids Op OpAux Cks Syn)
       (Import Ty : LTYPING Ids Op OpAux Cks Syn)
       (Import Cl : LCLOCKING Ids Op OpAux Cks Syn)
       (Import Ord : LORDERED Ids Op OpAux Cks Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Cks Syn Ord CStr)
       (LCS : LCLOCKSEMANTICS Ids Op OpAux Cks Syn Cl LCA Ord CStr IStr Sem)
       (Import Norm : NORMALIZATION Ids Op OpAux Cks Syn LCA).

  Import Fresh Tactics Unnesting.
  Module Import Typing := NTypingFun Ids Op OpAux Cks Syn LCA Ty Norm.
  Module Import Clocking := NClockingFun Ids Op OpAux Cks Syn LCA Cl Norm.
  Module Import Causality := NCausalityFun Ids Op OpAux Cks Syn LCA Cl Norm.
  Import List.

  CoFixpoint default_stream : Stream svalue :=
    absent ⋅ default_stream.

  (** Some additional stuff *)

  Import Permutation.

  Fact fresh_ident_refines {B V} : forall vars H H' a id (v : V) (st st' : fresh_st B) reu,
      st_valid_reuse st (PSP.of_list vars) reu ->
      Env.dom H (vars++st_ids st) ->
      fresh_ident norm1 a st = (id, st') ->
      H' = Env.add id v H ->
      Env.refines eq H H'.
  Proof with eauto.
    intros * Hvalid Hdom Hfresh Heq.
    rewrite Heq.
    assert (st_valid_reuse st' (PSP.of_list vars) reu) as Hvalid' by eauto.
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
    + eapply Facts.fresh_ident_reuse_nIn in Hfresh; eauto.
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
      st_valid_reuse st aft reu ->
      idents_for_anns anns st = (ids, st') ->
      Forall (fun id => ~In id (st_ids st)) (map fst ids).
  Proof.
    intros * Hvalid Hids.
    eapply idents_for_anns_st_valid_reuse in Hvalid; eauto.
    apply st_valid_reuse_NoDup, NoDup_app_l in Hvalid.
    apply idents_for_anns_vars_perm in Hids.
    unfold st_ids in *.
    rewrite <- Hids in Hvalid.
    rewrite Forall_forall. intros x Hin.
    eapply NoDup_app_In; eauto.
  Qed.

  Fact idents_for_anns_dom {V} : forall vars H H' anns ids (vs : list V) st st' reu,
      length vs = length ids ->
      st_valid_reuse st (PSP.of_list vars) reu ->
      Env.dom H (vars++st_ids st) ->
      idents_for_anns anns st = (ids, st') ->
      H' = Env.adds (map fst ids) vs H ->
      Env.dom H' (vars++st_ids st').
  Proof with eauto.
    intros * Hlen Hvalid Hdom Hids Heq.
    apply idents_for_anns_vars_perm in Hids.
    rewrite Heq.
    apply Env.dom_adds with (ids0:=map fst ids) (vs0:=vs) in Hdom.
    2:(repeat rewrite_Forall_forall; solve_length).
    eapply Env.dom_Permutation; [|eauto].
    symmetry. rewrite Permutation_app_comm. rewrite <- app_assoc. apply Permutation_app_head.
    rewrite Permutation_app_comm. assumption.
  Qed.

  Fact idents_for_anns_refines {V} : forall vars H H' anns ids (vs : list V) st st' reu,
      length vs = length ids ->
      st_valid_reuse st (PSP.of_list vars) reu ->
      Env.dom H (vars++st_ids st) ->
      idents_for_anns anns st = (ids, st') ->
      H' = Env.adds (map fst ids) vs H ->
      Env.refines eq H H'.
  Proof with eauto.
    intros * Hlen Hvalid Hdom Hids Heq.
    assert (Forall (fun id => ~In id vars) (List.map fst ids)) as Hnvar.
    { assert (st_valid_reuse st' (PSP.of_list vars) reu) by eauto.
      apply idents_for_anns_incl_ids in Hids.
      solve_forall; simpl.
      assert (In i (map fst ids)) by (simpl_In; exists (i, a); eauto).
      apply Hids in H2.
      intro contra.
      eapply st_valid_reuse_NoDup, NoDup_app_In in H0; [|eauto].
      apply H0, in_or_app. left. rewrite ps_of_list_ps_to_list... }
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
    apply st_valid_reuse_NoDup, NoDup_app_l in Hvalid.
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
    apply st_valid_reuse_NoDup, NoDup_app_l in Hvalid.
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
    apply st_valid_reuse_NoDup in Hvalid.
    apply idents_for_anns'_vars_perm in Hids.
    unfold st_ids in *.
    rewrite <- Hids, Permutation_app_comm, Permutation_swap in Hvalid.
    rewrite Forall_forall. intros x Hin.
    eapply NoDup_app_In in Hvalid; eauto.
    rewrite <- app_assoc in Hvalid.
    repeat rewrite not_In_app in Hvalid. rewrite not_In_app.
    destruct Hvalid as (?&?&?); auto.
  Qed.

  Fact idents_for_anns'_dom {V} : forall vars H H' anns ids (vs : list V) st st' reu,
      length vs = length ids ->
      st_valid_reuse st (PSP.of_list vars) reu ->
      Env.dom H (vars++st_ids st) ->
      idents_for_anns' anns st = (ids, st') ->
      H' = Env.adds (map fst ids) vs H ->
      Env.dom H' (vars++st_ids st').
  Proof with eauto.
    intros * Hlen Hvalid Hdom Hids Heq.
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
      apply st_valid_reuse_NoDup in Hvalid'.
      eapply NoDup_app_In in Hvalid'; [|eauto].
      apply Hvalid', in_or_app; clear Hvalid'.
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
      eapply st_valid_reuse_NoDup, NoDup_app_In in H0; [|eauto].
      apply H0, in_or_app. rewrite ps_of_list_ps_to_list... }
    rewrite Heq. apply Env.refines_adds.
    eapply idents_for_anns'_nIn in Hids...
    rewrite Forall_forall in *. intros x1 Hin contra.
    erewrite Env.dom_use in contra...
    apply in_app_or in contra; destruct contra.
    + eapply Hnvar...
    + eapply Hids...
  Qed.

  Fact fresh_ident_dom {B V} : forall pref vars H H' a id (v : V) (st st' : fresh_st B),
      Env.dom H (vars++st_ids st) ->
      fresh_ident pref a st = (id, st') ->
      H' = Env.add id v H ->
      Env.dom H' (vars++st_ids st').
  Proof.
    intros * Hdom Hfresh Heq.
    apply Facts.fresh_ident_vars_perm in Hfresh.
    rewrite Heq.
    apply Env.dom_add_cons with (x:=id) (v0:=v) in Hdom.
    eapply Env.dom_Permutation; [| eauto].
    symmetry. rewrite Permutation_middle.
    apply Permutation_app_head. assumption.
  Qed.

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

    (** ** Conservation of sem_exp *)

    Fact unnest_reset_sem : forall vars b e H v e' eqs' st st' reusable,
        (forall e' eqs' st',
            unnest_exp G1 true e st = ([e'], eqs', st') ->
            exists H',
              Env.refines eq H H' /\
              st_valid_reuse st' (PSP.of_list vars) reusable /\
              Env.dom H' (vars++st_ids st') /\
              sem_exp G2 H' b e' [v] /\ Forall (sem_equation G2 H' b) eqs') ->
        wl_exp G1 e ->
        numstreams e = 1 ->
        sem_exp G1 H b e [v] ->
        st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (fresh_in e)) reusable) ->
        Env.dom H (vars++st_ids st) ->
        unnest_reset (unnest_exp G1 true) e st = (e', eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_reuse st' (PSP.of_list vars) reusable /\
            Env.dom H' (vars++st_ids st') /\
            sem_exp G2 H' b e' [v] /\
            Forall (sem_equation G2 H' b) eqs').
    Proof with eauto.
      intros * Hun Hwl Hnum Hsem Hvalid Histst Hnorm.
      unnest_reset_spec; simpl in *.
      1,2:assert (length l = 1) by (eapply unnest_exp_length in Hk0; eauto; congruence).
      1,2:singleton_length.
      - specialize (Hun _ _ _ eq_refl) as (H'&Href&Hval&Hdom&Hsem1&Hsem2).
        exists H'. repeat split; eauto.
      - specialize (Hun _ _ _ eq_refl) as (H'&Href&Hval&Hdom&Hsem1&Hsem2).
        assert (Href':=Hfresh); eapply fresh_ident_refines in Href'; eauto.
        exists (Env.add x2 v H'). repeat split. 5:constructor.
        + etransitivity; eauto.
        + eapply fresh_ident_st_valid_reuse in Hfresh; eauto.
        + eapply fresh_ident_dom in Hfresh; eauto.
        + repeat constructor.
          econstructor. eapply Env.add_1. 1,2:reflexivity.
        + eapply Seq with (ss:=[[v]]); simpl.
          1,2:repeat constructor.
          * eapply sem_exp_refines; eauto.
          * econstructor. eapply Env.add_1. 1,2:reflexivity.
        + solve_forall.
          eapply sem_equation_refines; eauto.
    Qed.

    Corollary unnest_resets_sem : forall vars b es H vs es' eqs' st st' reusable,
        NoDup (map fst (fresh_ins es)++PS.elements reusable) ->
        Forall (wl_exp G1) es ->
        Forall (fun e => numstreams e = 1) es ->
        Forall2 (fun e v => sem_exp G1 H b e [v]) es vs ->
        st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (fresh_ins es)) reusable) ->
        Env.dom H (vars++st_ids st) ->
        Forall2 (fun e v => forall H e' eqs' st st' reusable,
                     NoDup (map fst (fresh_in e)++PS.elements reusable) ->
                     wl_exp G1 e ->
                     sem_exp G1 H b e [v] ->
                     st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (fresh_in e)) reusable) ->
                     Env.dom H (vars++st_ids st) ->
                     unnest_exp G1 true e st = ([e'], eqs', st') ->
                     (exists H',
                         Env.refines eq H H' /\
                         st_valid_reuse st' (PSP.of_list vars) reusable /\
                         Env.dom H' (vars++st_ids st') /\
                         sem_exp G2 H' b e' [v] /\
                         Forall (sem_equation G2 H' b) eqs')) es vs ->
        mmap2 (unnest_reset (unnest_exp G1 true)) es st = (es', eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_reuse st' (PSP.of_list vars) reusable /\
            Env.dom H' (vars++st_ids st') /\
            Forall2 (fun e v => sem_exp G2 H' b e [v]) es' vs /\
            Forall (sem_equation G2 H' b) (concat eqs')).
    Proof with eauto.
      induction es; intros * Hndup Hwt Hnum Hsem Hvalid Histst Hf Hmap;
        inv Hwt; inv Hnum; inv Hsem; inv Hf; repeat inv_bind.
      - exists H; simpl. repeat (split; eauto).
      - unfold fresh_ins in *; simpl in *; rewrite map_app, ps_adds_app in Hvalid.
        assert (NoDup (map fst (fresh_ins es)++PS.elements reusable)) as Hndup2 by ndup_r Hndup.
        assert (NoDup (map fst (fresh_in a) ++ PS.elements (ps_adds (map fst (fresh_ins es)) reusable))) as Hndup1.
        { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
        eapply unnest_reset_sem in H0 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1'); eauto.
        assert (Forall2 (fun e v => sem_exp G1 H' b e [v]) es l') as Hsem'.
        { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
        eapply IHes in H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]...
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

    Fact unnest_arrow_sem : forall H bs e0s es er anns s0s ss rs r os,
        length e0s = length anns ->
        length es = length anns ->
        Forall2 (fun e s => sem_exp G2 H bs e [s]) e0s s0s ->
        Forall2 (fun e s => sem_exp G2 H bs e [s]) es ss ->
        Forall2 (fun er r => sem_exp G2 H bs er [r]) er rs ->
        bools_ofs rs r ->
        Forall3 (fun s0 s o => arrow s0 s r o) s0s ss os ->
        Forall2 (fun e s => sem_exp G2 H bs e [s]) (unnest_arrow e0s es er anns) os.
    Proof with eauto.
      intros * Hlen1 Hlen2 Hsem1 Hsem2 Hsemr Bools Hfby.
      unfold unnest_arrow.
      repeat rewrite_Forall_forall. 1:solve_length.
      repeat simpl_length. repeat simpl_nth. Unshelve. 2:exact ((hd_default [], hd_default []), default_ann).
      destruct (nth n (combine _ _)) as [[e0 e] ?] eqn:Hnth. repeat simpl_nth.
      econstructor...
      eapply Forall2_forall2; split; intros; eauto. eapply H1... congruence.
      1:repeat constructor...
      Unshelve. 1-2:exact default_stream.
    Qed.

    Fact unnest_fby_sem : forall H bs e0s es er anns s0s ss rs r os,
        length e0s = length anns ->
        length es = length anns ->
        Forall2 (fun e s => sem_exp G2 H bs e [s]) e0s s0s ->
        Forall2 (fun e s => sem_exp G2 H bs e [s]) es ss ->
        Forall2 (fun er r => sem_exp G2 H bs er [r]) er rs ->
        bools_ofs rs r ->
        Forall3 (fun s0 s o => fby s0 s r o) s0s ss os ->
        Forall2 (fun e s => sem_exp G2 H bs e [s]) (unnest_fby e0s es er anns) os.
    Proof with eauto.
      intros * Hlen1 Hlen2 Hsem1 Hsem2 Hsemr Bools Hfby.
      unfold unnest_fby.
      repeat rewrite_Forall_forall. 1:solve_length.
      repeat simpl_length. repeat simpl_nth. Unshelve. 2:exact ((hd_default [], hd_default []), default_ann).
      destruct (nth n (combine _ _)) as [[e0 e] ?] eqn:Hnth. repeat simpl_nth.
      econstructor...
      eapply Forall2_forall2; split; intros; eauto. eapply H1... congruence.
      1:repeat constructor...
      Unshelve. 1-2:exact default_stream.
    Qed.

    Fact unnest_when_sem : forall H bs es tys ckid b ck s ss os,
        length es = length tys ->
        Forall2 (fun e s => sem_exp G2 H bs e [s]) es ss ->
        sem_var H ckid s ->
        Forall2 (fun s' => when b s' s) ss os ->
        Forall2 (fun e s => sem_exp G2 H bs e [s]) (unnest_when ckid b es tys ck) os.
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
        Forall2 (Forall2 (fun e s => sem_exp G2 H bs e [s])) es vs ->
        Forall2Transpose (merge s) vs os ->
        Forall2 (fun e s => sem_exp G2 H bs e [s]) (unnest_merge (x, tx) es tys ck) os.
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
        sem_exp G2 H bs e [s] ->
        Forall2 (fun oes vs0 => forall es0, oes = Some es0 -> Forall2 (fun e s => sem_exp G2 H bs e [s]) es0 vs0) es vs ->
        Forall2 (fun oes vs0 => oes = None -> EqSts vs0 vd) es vs ->
        Forall2 (fun e s => sem_exp G2 H bs e [s]) d vd ->
        Forall2Transpose (case s) vs os ->
        Forall2 (fun e s => sem_exp G2 H bs e [s]) (unnest_case e es d tys ck) os.
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

    Fact mmap2_sem : forall vars b is_control es H vs es' eqs' st st' reusable,
        NoDup (map fst (fresh_ins es)++PS.elements reusable) ->
        Forall (wl_exp G1) es ->
        Forall2 (sem_exp G1 H b) es vs ->
        st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (fresh_ins es)) reusable) ->
        Env.dom H (vars++st_ids st) ->
        Forall
          (fun e => forall H vs is_control es' eqs' st st' reusable,
               NoDup (map fst (fresh_in e) ++ PS.elements reusable) ->
               wl_exp G1 e ->
               sem_exp G1 H b e vs ->
               st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (fresh_in e)) reusable) ->
               Env.dom H (vars ++ st_ids st) ->
               unnest_exp G1 is_control e st = (es', eqs', st') ->
               exists H' : Env.t (Stream svalue),
                 Env.refines eq H H' /\
                 st_valid_reuse st' (PSP.of_list vars) reusable /\
                 Env.dom H' (vars ++ st_ids st') /\
                 Forall2 (fun (e0 : exp) (v : Stream svalue) => sem_exp G2 H' b e0 [v]) es' vs /\ Forall (sem_equation G2 H' b) eqs') es ->
        mmap2 (unnest_exp G1 is_control) es st = (es', eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_reuse st' (PSP.of_list vars) reusable /\
            Env.dom H' (vars++st_ids st') /\
            Forall2 (fun es vs => Forall2 (fun e v => sem_exp G2 H' b e [v]) es vs) es' vs /\
            Forall (sem_equation G2 H' b) (concat eqs')).
    Proof with eauto.
      induction es; intros * Hndup Hwt Hsem Hvalid Histst Hf Hmap;
        inv Hwt; inv Hsem; inv Hf; repeat inv_bind.
      - exists H; simpl. repeat (split; eauto).
      - unfold fresh_ins in *; simpl in *; rewrite map_app, ps_adds_app in Hvalid.
        assert (NoDup (map fst (fresh_ins es)++PS.elements reusable)) as Hndup2 by ndup_r Hndup.
        assert (NoDup (map fst (fresh_in a) ++ PS.elements (ps_adds (map fst (fresh_ins es)) reusable))) as Hndup1.
        { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
        specialize (H5 _ _ _ _ _ _ _ _ Hndup1 H2 H4 Hvalid Histst H0) as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
        assert (Forall2 (sem_exp G1 H' b) es l') as Hsem'.
        { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
        eapply IHes in H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]...
        clear IHes H7.
        exists H''. repeat (split; eauto).
        + etransitivity...
        + constructor; eauto. subst.
          assert (length x = numstreams a) as Hlength1 by (eapply unnest_exp_length; eauto).
          assert (length y = numstreams a) as Hlength2 by (eapply sem_exp_numstreams; eauto).
          solve_forall.
          eapply sem_exp_refines; eauto.
        + apply Forall_app. split...
          solve_forall. eapply sem_equation_refines...
    Qed.

    Fact mmap2_mmap2_sem : forall vars b is_control es H vs es' eqs' st st' reusable,
        NoDup (map fst (flat_map fresh_ins es)++PS.elements reusable) ->
        Forall (Forall (wl_exp G1)) es ->
        Forall2 (Forall2 (sem_exp G1 H b)) es vs ->
        st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (flat_map fresh_ins es)) reusable) ->
        Env.dom H (vars++st_ids st) ->
        Forall
          (Forall
             (fun e => forall H vs is_control es' eqs' st st' reusable,
                  NoDup (map fst (fresh_in e) ++ PS.elements reusable) ->
                  wl_exp G1 e ->
                  sem_exp G1 H b e vs ->
                  st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (fresh_in e)) reusable) ->
                  Env.dom H (vars ++ st_ids st) ->
                  unnest_exp G1 is_control e st = (es', eqs', st') ->
                  exists H' : Env.t (Stream svalue),
                    Env.refines eq H H' /\
                    st_valid_reuse st' (PSP.of_list vars) reusable /\
                    Env.dom H' (vars ++ st_ids st') /\
                    Forall2 (fun (e0 : exp) (v : Stream svalue) => sem_exp G2 H' b e0 [v]) es' vs /\ Forall (sem_equation G2 H' b) eqs')) es ->
        mmap2 (fun es => bind2 (mmap2 (unnest_exp G1 is_control) es) (fun es0 eqs => ret (concat es0, concat eqs))) es st = (es', eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_reuse st' (PSP.of_list vars) reusable /\
            Env.dom H' (vars++st_ids st') /\
            Forall2 (fun es vs => Forall2 (fun e v => sem_exp G2 H' b e [v]) es vs) es' (List.map (@concat _) vs) /\
            Forall (sem_equation G2 H' b) (concat eqs')).
    Proof with eauto.
      induction es; intros * Hndup Hwt Hsem Hvalid Histst Hf Hmap;
        inv Hwt; inv Hsem; inv Hf; repeat inv_bind.
      - exists H; simpl. repeat (split; eauto).
      - unfold fresh_ins in *; simpl in *; rewrite map_app, ps_adds_app in Hvalid.
        assert (NoDup (map fst (flat_map fresh_ins es)++PS.elements reusable)) as Hndup2 by ndup_r Hndup.
        assert (NoDup (map fst (fresh_ins a) ++ PS.elements (ps_adds (map fst (flat_map fresh_ins es)) reusable))) as Hndup1.
        { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
        eapply mmap2_sem in H5 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1'); eauto.
        assert (Forall2 (Forall2 (sem_exp G1 H' b)) es l') as Hsem'.
        { do 2 (eapply Forall2_impl_In; [|eauto]; intros ?? _ _ ?). eapply sem_exp_refines... }
        eapply IHes in H1 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2')...
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

    Fact mmap2_mmap2_sem' : forall vars b is_control brs H vs es' eqs' st st' reusable,
        NoDup (map fst (flat_map (or_default_with [] fresh_ins) brs)++PS.elements reusable) ->
        (forall es, In (Some es) brs -> Forall (wl_exp G1) es) ->
        Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (sem_exp G1 H b) es vs) brs vs ->
        st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (flat_map (or_default_with [] fresh_ins) brs)) reusable) ->
        Env.dom H (vars++st_ids st) ->
        Forall
        (LiftO True
           (Forall
              (fun e : exp =>
               forall (H : history) (vs : list (Stream svalue)) (is_control : bool) (es' : list exp)
                 (eqs' : list equation) (st st' : fresh_st (type * clock)) (reusable : PS.t),
               NoDup (map fst (fresh_in e) ++ PS.elements reusable) ->
               wl_exp G1 e ->
               sem_exp G1 H b e vs ->
               st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (fresh_in e)) reusable) ->
               Env.dom H (vars ++ st_ids st) ->
               unnest_exp G1 is_control e st = (es', eqs', st') ->
               exists H' : Env.t (Stream svalue),
                 Env.refines eq H H' /\
                 st_valid_reuse st' (PSP.of_list vars) reusable /\
                 Env.dom H' (vars ++ st_ids st') /\
                 Forall2 (fun (e0 : exp) (v : Stream svalue) => sem_exp G2 H' b e0 [v]) es' vs /\
                 Forall (sem_equation G2 H' b) eqs'))) brs ->
        mmap2
          (or_default_with
             (ret (None, []))
             (fun es => bind2
                       (bind2 (mmap2 (unnest_exp G1 is_control) es) (fun es0 eqs => ret (concat es0, concat eqs)))
               (fun (es' : list exp) (eqs' : list equation) => ret (Some es', eqs')))) brs st = (es', eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_reuse st' (PSP.of_list vars) reusable /\
            Env.dom H' (vars++st_ids st') /\
            Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (fun e v => sem_exp G2 H' b e [v]) es vs) es'
                    (List.map (@concat _) vs) /\
            Forall (sem_equation G2 H' b) (concat eqs')).
    Proof with eauto.
      induction brs; intros * Hndup Hwt Hsem Hvalid Histst Hf Hmap;
        inv Hsem; inv Hf; repeat inv_bind.
      - exists H; simpl. repeat (split; eauto).
      - unfold fresh_ins in *; simpl in *; rewrite map_app, ps_adds_app in Hvalid.
        assert (NoDup (map fst (flat_map (or_default_with [] fresh_ins) brs)++PS.elements reusable)) as Hndup2 by ndup_r Hndup.
        assert (NoDup (map fst (or_default_with [] fresh_ins a) ++ PS.elements (ps_adds (map fst (flat_map (or_default_with [] fresh_ins) brs)) reusable))) as Hndup1.
        { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
        destruct a; simpl in *; repeat inv_bind; simpl.
        + eapply mmap2_sem in H3 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1'); eauto.
          assert (Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (sem_exp G1 H' b) es vs) brs l') as Hsem'.
          { clear - H4 Href1.
            eapply Forall2_impl_In; [|eauto]; intros; subst.
            specialize (H2 _ eq_refl). eapply Forall2_impl_In; [|eauto]; intros.
            eapply sem_exp_refines... }
          eapply IHbrs in H1 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2')...
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

    Lemma unnest_noops_exp_sem : forall vars b ck e H v e' eqs' st st' reusable,
        st_valid_reuse st (PSP.of_list vars) reusable ->
        Env.dom H (vars++st_ids st) ->
        sem_exp G2 H b e [v] ->
        unnest_noops_exp ck e st = (e', eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_reuse st' (PSP.of_list vars) reusable /\
            Env.dom H' (vars++st_ids st') /\
            sem_exp G2 H' b e' [v] /\
            Forall (sem_equation G2 H' b) eqs').
    Proof.
      unfold unnest_noops_exp.
      intros * Hvalid Hdom Hsem Hunt.
      destruct (hd _ _) as (?&?&?).
      destruct (is_noops_exp _ _); repeat inv_bind.
      - exists H. auto.
      - assert (Hfresh:=H0). eapply fresh_ident_refines in H0; eauto.
        exists (Env.add x v H). repeat split; eauto.
        + eapply fresh_ident_dom; eauto.
        + constructor. econstructor.
          eapply Env.add_1. 1,2:reflexivity.
        + constructor; auto.
          apply Seq with (ss:=[[v]]); simpl.
          * constructor; auto. eapply sem_exp_refines; eauto.
          * constructor; auto. econstructor.
            eapply Env.add_1. 1,2:reflexivity.
    Qed.

    Lemma unnest_noops_exps_sem : forall vars b cks es H vs es' eqs' st st' reusable,
        length es = length cks ->
        st_valid_reuse st (PSP.of_list vars) reusable ->
        Env.dom H (vars++st_ids st) ->
        Forall2 (fun e v => sem_exp G2 H b e [v]) es vs ->
        unnest_noops_exps cks es st = (es', eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_reuse st' (PSP.of_list vars) reusable /\
            Env.dom H' (vars++st_ids st') /\
            Forall2 (fun e v => sem_exp G2 H' b e [v]) es' vs /\
            Forall (sem_equation G2 H' b) eqs').
    Proof.
      unfold unnest_noops_exps.
      induction cks; intros * Hlen (* Hnormed *) (* Hnum *) Hvalid Hdom Hsem Hunt; repeat inv_bind; simpl; auto.
      1,2:destruct es; simpl in *; inv Hlen; repeat inv_bind.
      - inv Hsem. exists H. auto.
      - inv Hsem.
        eapply unnest_noops_exp_sem in H0 as (H'&?&?&?&?&?); eauto.
        assert (Forall2 (fun e v => sem_exp G2 H' b e [v]) es l') as Hsem'.
        { solve_forall. eapply sem_exp_refines; eauto. }
        eapply IHcks with (st:=x2) in Hsem' as (H''&?&?&?&?&?); eauto.
        2:inv_bind; repeat eexists; eauto; inv_bind; eauto.
        exists H''. repeat split; eauto.
        + etransitivity; eauto.
        + constructor; eauto.
          eapply sem_exp_refines; eauto.
        + simpl. rewrite Forall_app; split; auto.
          solve_forall. eapply sem_equation_refines; eauto.
    Qed.

    Hypothesis Hiface : global_iface_eq G1 G2.
    Hypothesis HGref : global_sem_refines G1 G2.

    Hint Constructors sem_exp.
    Fact unnest_exp_sem : forall vars b e H vs is_control es' eqs' st st' reusable,
        NoDup (map fst (fresh_in e) ++ PS.elements reusable) ->
        wl_exp G1 e ->
        sem_exp G1 H b e vs ->
        st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (fresh_in e)) reusable) ->
        Env.dom H (vars++st_ids st) ->
        unnest_exp G1 is_control e st = (es', eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_reuse st' (PSP.of_list vars) reusable /\
            Env.dom H' (vars++st_ids st') /\
            Forall2 (fun e v => sem_exp G2 H' b e [v]) es' vs /\
            Forall (sem_equation G2 H' b) eqs').
    Proof with eauto.
      induction e using exp_ind2; intros * Hndup Hwl Hsem Hvalid Histst Hnorm; repeat inv_bind. 11:inv Hwl; inv Hsem.
      - (* const *)
        inv Hsem. exists H. repeat (split; auto).
      - (* enum *)
        inv Hsem. exists H. repeat (split; auto).
      - (* var *)
        inv Hsem. exists H. repeat (split; auto).
      - (* unop *)
        inv Hsem. inv Hwl.
        assert (Htypeof:=H0). eapply unnest_exp_typeof in Htypeof...
        assert (Hnorm:=H0). eapply IHe in Hnorm as [H' [Href1 [Hvalid1 [Hdom1 [Hsem1 Hsem1']]]]]...
        eapply unnest_exp_length in H0... rewrite H6 in H0. singleton_length.
        inv Hsem1.
        exists H'. repeat (split; eauto).
        repeat econstructor... congruence.
      - (* binop *)
        inv Hsem; inv Hwl.
        simpl in *. rewrite map_app, ps_adds_app in Hvalid.
        assert (Htypeof1:=H0). eapply unnest_exp_typeof in Htypeof1...
        assert (Htypeof2:=H1). eapply unnest_exp_typeof in Htypeof2...
        assert (NoDup (map fst (fresh_in e1) ++ PS.elements (ps_adds (map fst (fresh_in e2)) reusable))) as Hndup1.
        { rewrite Permutation_PS_elements_ps_adds'. ndup_simpl... ndup_r Hndup. }
        eapply IHe1 in H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]... clear IHe1.
        eapply sem_exp_refines in H10; [| eauto].
        assert (NoDup (map fst (fresh_in e2) ++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
        eapply IHe2 in H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]... clear IHe2.
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
        inversion_clear Hwl as [| | | | |????? Hwl1 Hwl2 Hwlr Hl1 Hl2 Hlr| | | | |].
        inversion_clear Hsem as [| | | | |??????????? Hsem1 Hsem2 Hsemr Bools Fby| | | | |].
        simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
        assert (length (concat x2) = length (annots e0s)) as Hlength1 by (eapply mmap2_unnest_exp_length; eauto).
        assert (length (concat x6) = length (annots es)) as Hlength2 by (eapply mmap2_unnest_exp_length; eauto).
        assert (NoDup (map fst (fresh_ins er) ++ PS.elements reusable)) as Hndup3 by repeat ndup_r Hndup.
        assert (NoDup (map fst (fresh_ins es) ++ PS.elements (ps_adds (map fst (fresh_ins er)) reusable))) as Hndup2.
        { ndup_r Hndup. rewrite Permutation_PS_elements_ps_adds'... }
        assert (NoDup (map fst (fresh_ins e0s) ++ PS.elements (ps_adds (map fst (fresh_ins es)) (ps_adds (map fst (fresh_ins er)) reusable)))) as Hndup1.
        { repeat rewrite Permutation_PS_elements_ps_adds'... ndup_simpl... ndup_r Hndup. }
        assert (Forall (fun e => numstreams e = 1) (concat x2)) as Hnumstreams.
        { eapply mmap2_unnest_exp_numstreams in H3... }

        assert (length s0ss = length e0s) as Hlen1 by (eapply Forall2_length in Hsem1; eauto).
        assert (H2':=H3). eapply mmap2_sem in H3... clear H Hsem1.
        destruct H3 as [H' [Href1 [Histst1 [Hdom1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.

        assert (Forall2 (sem_exp G1 H' b) es sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
        assert (length sss = length es) as Hlen2 by (eapply Forall2_length in Hsem2; eauto).
        assert (H3':=H4). eapply mmap2_sem in H4... clear H0 Hsem2.
        destruct H4 as [H'' [Href2 [Hvalid2 [Hdom2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.

        assert (length sr = length er) as Hlen3 by (eapply Forall2_length in Hsemr; eauto).
        assert (Forall2 (fun er sr => sem_exp G1 H'' b er [sr]) er sr) as Hsemr' by (repeat rewrite_Forall_forall; repeat (eapply sem_exp_refines; eauto)).
        assert (Hr:=H5). eapply unnest_resets_sem in H5...
        2:{ solve_forall. eapply H13 in H11 as (H'''&?&?&?&?&?); eauto. exists H'''; repeat split; eauto.
            inv H18; eauto. }
        destruct H5 as (H'''&Href3&Hvalid3&Hdom3&Hsem3&Hsem3').

        assert (Forall2 (fun e v => sem_exp G2 H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
        { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
        specialize (idents_for_anns_length _ _ _ _ H6) as Hlength.
        assert (length vs = length a) as Hlength'''.
        { eapply Forall3_length in Fby as [_ ?]. eapply Forall2_length in Hsem2. congruence. }

        remember (Env.adds (List.map fst x8) vs H''') as H''''.
        assert (length x8 = length vs) as Hlength'''' by (rewrite Hlength, Hlength'''; auto).

        assert (Forall2 (sem_var H'''') (map fst x8) vs) as Hsemvars.
        { rewrite HeqH''''. eapply sem_var_adds; eauto.
          + rewrite map_length; auto.
          + eapply idents_for_anns_NoDupMembers in H6; eauto. rewrite <- fst_NoDupMembers; eauto. }

        assert (Env.refines eq H''' H'''') as Href4.
        { eapply idents_for_anns_refines in H6... }
        assert (Forall2 (fun e v => sem_exp G2 H'''' b e [v]) (unnest_fby (concat x2) (concat x6) x5 a) vs) as Hsemf.
        { eapply unnest_fby_sem; simpl... 2:congruence.
          + eapply mmap2_unnest_exp_length in H2'... congruence.
          + clear - Hsem1 Href2 Href3 Href4. eapply Forall2_impl_In... intros; simpl in *.
            repeat (eapply sem_exp_refines; eauto).
          + clear - Hsem2 Href2 Href3 Href4. eapply Forall2_impl_In... intros; simpl in *.
            repeat (eapply sem_exp_refines; eauto).
          + solve_forall. eapply sem_exp_refines; eauto. }

        exists H''''. repeat (split; eauto).
        * repeat (etransitivity; eauto).
        * eapply idents_for_anns_dom in H6; eauto.
        * clear - Hsemvars. solve_forall.
        * repeat rewrite Forall_app. repeat split.
          apply mk_equations_Forall.
          2-4:(solve_forall; repeat (eapply sem_equation_refines; eauto)).
          clear - Hsemvars Hsemf.
          remember (unnest_fby _ _ _ _) as fby. clear Heqfby.
          simpl_forall.
          repeat rewrite_Forall_forall. congruence.
          destruct (nth _ x8 _) eqn:Hnth1.
          econstructor.
          -- repeat constructor.
             eapply H0... congruence.
          -- repeat constructor.
             eapply H2 with (x1:=(i, a1))...
      - (* arrow *)
        inversion_clear Hwl as [| | | | | |????? Hwl1 Hwl2 Hwlr Hl1 Hl2 Hlr| | | |].
        inversion_clear Hsem as [| | | | | |??????????? Hsem1 Hsem2 Hsemr Bools Arrow| | | |].
        simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
        assert (length (concat x2) = length (annots e0s)) as Hlength1 by (eapply mmap2_unnest_exp_length; eauto).
        assert (length (concat x6) = length (annots es)) as Hlength2 by (eapply mmap2_unnest_exp_length; eauto).
        assert (NoDup (map fst (fresh_ins er) ++ PS.elements reusable)) as Hndup3 by repeat ndup_r Hndup.
        assert (NoDup (map fst (fresh_ins es) ++ PS.elements (ps_adds (map fst (fresh_ins er)) reusable))) as Hndup2.
        { ndup_r Hndup. rewrite Permutation_PS_elements_ps_adds'... }
        assert (NoDup (map fst (fresh_ins e0s) ++ PS.elements (ps_adds (map fst (fresh_ins es)) (ps_adds (map fst (fresh_ins er)) reusable)))) as Hndup1.
        { repeat rewrite Permutation_PS_elements_ps_adds'... ndup_simpl... ndup_r Hndup. }
        assert (Forall (fun e => numstreams e = 1) (concat x2)) as Hnumstreams.
        { eapply mmap2_unnest_exp_numstreams in H3... }

        assert (length s0ss = length e0s) as Hlen1 by (eapply Forall2_length in Hsem1; eauto).
        assert (H2':=H3). eapply mmap2_sem in H3... clear H Hsem1.
        destruct H3 as [H' [Href1 [Histst1 [Hdom1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.

        assert (Forall2 (sem_exp G1 H' b) es sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
        assert (length sss = length es) as Hlen2 by (eapply Forall2_length in Hsem2; eauto).
        assert (H3':=H4). eapply mmap2_sem in H4... clear H0 Hsem2.
        destruct H4 as [H'' [Href2 [Hvalid2 [Hdom2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.

        assert (length sr = length er) as Hlen3 by (eapply Forall2_length in Hsemr; eauto).
        assert (Forall2 (fun er sr => sem_exp G1 H'' b er [sr]) er sr) as Hsemr' by (repeat rewrite_Forall_forall; repeat (eapply sem_exp_refines; eauto)).
        assert (Hr:=H5). eapply unnest_resets_sem in H5...
        2:{ solve_forall. eapply H13 in H11 as (H'''&?&?&?&?&?); eauto. exists H'''; repeat split; eauto.
            inv H18; eauto. }
        destruct H5 as (H'''&Href3&Hvalid3&Hdom3&Hsem3&Hsem3').

        assert (Forall2 (fun e v => sem_exp G2 H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
        { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
        specialize (idents_for_anns_length _ _ _ _ H6) as Hlength.
        assert (length vs = length a) as Hlength'''.
        { eapply Forall3_length in Arrow as [_ ?]. eapply Forall2_length in Hsem2. congruence. }

        remember (Env.adds (List.map fst x8) vs H''') as H''''.
        assert (length x8 = length vs) as Hlength'''' by (rewrite Hlength, Hlength'''; auto).

        assert (Forall2 (sem_var H'''') (map fst x8) vs) as Hsemvars.
        { rewrite HeqH''''. eapply sem_var_adds; eauto.
          + rewrite map_length; auto.
          + eapply idents_for_anns_NoDupMembers in H6; eauto. rewrite <- fst_NoDupMembers; eauto. }

        assert (Env.refines eq H''' H'''') as Href4.
        { eapply idents_for_anns_refines in H6... }
        assert (Forall2 (fun e v => sem_exp G2 H'''' b e [v]) (unnest_arrow (concat x2) (concat x6) x5 a) vs) as Hsemf.
        { eapply unnest_arrow_sem; simpl... 2:congruence.
          + eapply mmap2_unnest_exp_length in H2'... congruence.
          + clear - Hsem1 Href2 Href3 Href4. eapply Forall2_impl_In... intros; simpl in *.
            repeat (eapply sem_exp_refines; eauto).
          + clear - Hsem2 Href2 Href3 Href4. eapply Forall2_impl_In... intros; simpl in *.
            repeat (eapply sem_exp_refines; eauto).
          + solve_forall. eapply sem_exp_refines; eauto. }

        exists H''''. repeat (split; eauto).
        * repeat (etransitivity; eauto).
        * eapply idents_for_anns_dom in H6; eauto.
        * clear - Hsemvars. solve_forall.
        * repeat rewrite Forall_app. repeat split.
          apply mk_equations_Forall.
          2-4:(solve_forall; repeat (eapply sem_equation_refines; eauto)).
          clear - Hsemvars Hsemf.
          remember (unnest_arrow _ _ _ _) as fby. clear Heqfby.
          simpl_forall.
          repeat rewrite_Forall_forall. congruence.
          destruct (nth _ x8 _) eqn:Hnth1.
          econstructor.
          -- repeat constructor.
             eapply H0... congruence.
          -- repeat constructor.
             eapply H2 with (x1:=(i, a1))...
      - (* when *)
        inv Hwl. inv Hsem. repeat inv_bind.
        assert (length (concat x1) = length (annots es)) as Hlength by (eapply mmap2_unnest_exp_length; eauto).
        assert (length es = length ss) by (apply Forall2_length in H11; auto).
        eapply mmap2_sem in H1... clear H.
        destruct H1 as [H' [Hvalid1 [Href1 [Hdom1 [Hsem1 Hsem1']]]]].
        apply Forall2_concat in Hsem1.
        exists H'. repeat (split; simpl; eauto).
        eapply unnest_when_sem... congruence.
        eapply sem_var_refines...
      - (* merge *)
        inv Hwl. inv Hsem. repeat inv_bind.
        simpl in *.

        assert (x <> []) as Hnnil.
        { eapply mmap2_length_1 in H1.
          intro contra; subst. destruct es; simpl in *; congruence. }

        assert (Forall (fun es => length es = length tys) x) as Hlen1.
        { eapply mmap2_mmap2_unnest_exp_length, Forall2_ignore1 in H1...
          eapply Forall_impl; [|eapply H1]; intros ? (?&Hin&Hlen).
          eapply Forall_forall in H7; eauto. congruence. }
        eapply mmap2_mmap2_sem in H1 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1')... clear H.

        assert (Forall2 (fun e v => sem_exp G2 H' b e [v])
                        (unnest_merge (x0, tx) x tys nck) vs) as Hsem'.
        { eapply unnest_merge_sem...
          eapply sem_var_refines... }
        destruct is_control; repeat inv_bind.
        + (* control *)
          exists H'. repeat (split; simpl; eauto).
        + (* exp *)
          remember (Env.adds (List.map fst x3) vs H') as H''.
          assert (length vs = length x3) as Hlength'.
          { eapply idents_for_anns_length in H. repeat simpl_length.
            apply Forall2Transpose_length, Forall_map in H13.
            inv H12; try congruence. inv H7. inv H13. inv H6.
            eapply sem_exps_numstreams in H1... congruence. }
          assert (Env.refines eq H' H'') as Href3.
          {eapply idents_for_anns_refines... }
          assert (Forall2 (sem_var H'') (map fst x3) vs) as Hvars.
          { rewrite HeqH''. eapply sem_var_adds... 1:rewrite map_length...
            rewrite <- fst_NoDupMembers. eapply idents_for_anns_NoDupMembers in H... }
          exists H''. repeat (split; eauto).
          * repeat (etransitivity; eauto).
          * eapply idents_for_anns_dom...
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
        inv Hwl. inv Hsem. repeat inv_bind.
        simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
        assert (NoDup (map fst (fresh_ins d) ++ PS.elements reusable)) as Hndup1.
        { repeat ndup_r Hndup. }
        assert (NoDup (map fst (flat_map (or_default_with [] fresh_ins) es) ++
                           PS.elements (ps_adds (map fst (fresh_ins d)) reusable))) as Hndup2.
        { ndup_simpl. rewrite Permutation_PS_elements_ps_adds'... ndup_r Hndup. }
        assert (NoDup
                  (map fst (fresh_in e) ++
                       PS.elements
                       (ps_adds (map fst (flat_map (or_default_with [] (flat_map fresh_in)) es))
                                (ps_adds (map fst (flat_map fresh_in d)) reusable)))) as Hndup3.
        { ndup_simpl. repeat rewrite Permutation_PS_elements_ps_adds'... ndup_r Hndup. }

        assert (length x = 1). 2:singleton_length.
        { eapply unnest_exp_length in H2... congruence. }
        eapply IHe in H2 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1')... clear IHe.
        eapply Forall2_singl in Hsem1.

        assert (x2 <> []) as Hnnil.
        { eapply mmap2_length_1 in H3.
          intro contra; subst. destruct es; simpl in *; congruence. }
        assert (Forall (LiftO True (fun es => length es = length tys)) x2) as Hlen1.
        { eapply mmap2_mmap2_unnest_exp_length', Forall2_ignore1 in H3...
          eapply Forall_impl; [|eapply H3]; intros [|] (?&Hin&Hlen); simpl; auto.
          - edestruct Hlen as (?&?&?); eauto; subst.
            erewrite <-H11; eauto.
          - eapply Forall_forall. intros [|] Hin; simpl; auto. }
        assert (Forall2 (fun es es' => es' = None -> es = None) es x2) as Hnone.
        { clear - H3. eapply mmap2_values, Forall3_ignore3 in H3.
          eapply Forall2_impl_In; [|eauto]; intros ?? _ _ (?&?&?&?) ?; subst.
          destruct a; auto; repeat inv_bind. }
        assert (Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (sem_exp G1 H' b) es vs) es vs0) as Hsems.
        { clear - Href1 H17.
          eapply Forall2_impl_In; [|eauto]; intros; subst. specialize (H2 _ eq_refl).
          eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines... }
        eapply mmap2_mmap2_sem' in H3 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2')... clear H.

        assert (length (concat x8) = length tys) as Hlen2.
        { eapply mmap2_unnest_exp_length in H4... congruence. }
        assert (Forall2 (sem_exp G1 H'' b) d vd) as Hsemd.
        { eapply Forall2_impl_In; [|eauto]; intros.
          eapply sem_exp_refines; [|eauto]. etransitivity... }
        eapply mmap2_sem in H4 as (H'''&Href3&Hvalid3&Histst3&Hsem3&Hsem3')... clear H0.
        eapply Forall2_concat in Hsem3.

        assert (Forall2 (fun e v => sem_exp G2 H''' b e [v])
                        (unnest_case e0 x2 (concat x8) tys nck) vs) as Hsem'.
        { eapply unnest_case_sem...
          - eapply sem_exp_refines; [|eauto]. etransitivity...
          - eapply Forall2_impl_In; [|eauto]; intros; subst.
            specialize (H2 _ eq_refl).
            eapply Forall2_impl_In; [|eauto]; intros.
            eapply sem_exp_refines...
          - clear - Hnone H19. rewrite Forall2_map_2.
            rewrite Forall2_swap_args in Hnone.
            eapply Forall2_trans_ex in H19; eauto.
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
          { eapply idents_for_anns_length in H. repeat simpl_length.
            clear - H8 H10 H11 H12 H13 H17 H19 H20 H21.
            apply Forall2Transpose_length, Forall_map in H21.
            inv H17; try congruence. inv H19. inv H21.
            destruct x.
            - specialize (H _ eq_refl). eapply sem_exps_numstreams in H; eauto with datatypes.
              rewrite <-H4, H, H11; eauto with datatypes.
            - eapply Forall2_concat, Forall2_length in H5; auto.
              eapply sem_exps_numstreams in H20...
              now rewrite <-H4, H5, <-H13. }
          assert (Env.refines eq H''' H'''') as Href4.
          { eapply idents_for_anns_refines... }
          assert (Forall2 (sem_var H'''') (map fst x) vs) as Hvars.
          { rewrite HeqH''''. eapply sem_var_adds... 1:rewrite map_length...
            rewrite <- fst_NoDupMembers. eapply idents_for_anns_NoDupMembers in H... }
          exists H''''. repeat (split; eauto).
          * repeat (etransitivity; eauto).
          * eapply idents_for_anns_dom...
          * clear - Hvars. solve_forall.
          * repeat rewrite Forall_app; repeat split.
            -- remember (unnest_case _ _ _ _ _) as case.
               assert (length case = length x) as Hlength''.
               { eapply idents_for_anns_length in H.
                 subst. rewrite unnest_case_length. solve_length. }
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
        repeat rewrite map_app, ps_adds_app in Hvalid.
        assert (a = map snd x8) as Hanns; subst.
        { eapply idents_for_anns'_values in H5... }
        specialize (idents_for_anns'_length _ _ _ _ H5) as Hlength1.
        assert (length (n_out n) = length vs) as Hlength2.
        { specialize (H23 0). inv H23. apply Forall2_length in H9.
          unfold idents in *. repeat rewrite map_length in H9. congruence. }
        assert (length es = length ss) as Hlength3.
        { apply Forall2_length in H19... }
        assert (length (concat x6) = length (n_in n)) as Hlength4.
        { eapply mmap2_unnest_exp_length in H2; eauto. congruence. }
        assert (NoDup (map fst (Syn.anon_streams (map snd x8))++ PS.elements reusable)) as Hndup2 by repeat ndup_r Hndup.
        assert (NoDup (map fst (fresh_ins er) ++ PS.elements (ps_adds (map fst (Syn.anon_streams (map snd x8))) reusable))) as Hndup3.
        { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }
        assert (NoDup (map fst (fresh_ins es) ++ PS.elements (ps_adds (map fst (fresh_ins er)) (ps_adds (map fst (Syn.anon_streams (map snd x8))) reusable)))) as Hndup4.
        { repeat rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }

        eapply mmap2_sem in H2... clear H.
        destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].

        eapply unnest_noops_exps_sem in H3 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2')...
        3:eapply Forall2_concat; eauto.
        2:{ unfold find_node_incks. rewrite H14.
            rewrite map_length. auto. }

        assert (length rs = length er) as Hlen3 by (eapply Forall2_length in H21; eauto).
        assert (Forall2 (fun er sr => sem_exp G1 H'' b er [sr]) er rs) as Hsemr' by (repeat rewrite_Forall_forall; repeat (eapply sem_exp_refines; eauto)).
        assert (Hr:=H4). eapply unnest_resets_sem in H4...
        2:{ solve_forall. eapply H17 in H12 as (H'''&?&?&?&?&?); eauto. exists H'''; repeat split; eauto.
            inv H25; eauto. }
        destruct H4 as (H'''&Href3&Hvalid3&Hdom3&Hsem3&Hsem3').

        assert (sem_exp G2 H''' b (Eapp f x2 x5 (map snd x8)) vs) as Hsem'.
        { eapply Sapp with (ss0:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss)))...
          + rewrite <- concat_map, Forall2_map_2.
            solve_forall. eapply sem_exp_refines...
          + intros k. specialize (H23 k).
            rewrite concat_map_singl2. eapply HGref; eauto. }
        remember (Env.adds (map fst x8) vs H''') as H''''.
        assert (length vs = length x8) as Hlen' by solve_length.
        assert (Env.refines eq H''' H'''') as Href4.
        { eapply idents_for_anns'_refines... }
        assert (NoDupMembers x8) as Hndup'.
        { eapply idents_for_anns'_NoDupMembers in H5... }
        assert (Forall2 (sem_var H'''') (map fst x8) vs) as Hvars.
        { rewrite HeqH''''. eapply sem_var_adds... 1:rewrite map_length... rewrite <- fst_NoDupMembers... }
        exists H''''. repeat (split; eauto).
        + repeat (etransitivity; eauto).
        + eapply idents_for_anns'_dom in H5...
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

    Corollary unnest_exps_sem : forall vars b es H vs es' eqs' st st' reusable,
        NoDup (map fst (fresh_ins es) ++ PS.elements reusable) ->
        Forall (wl_exp G1) es ->
        Forall2 (sem_exp G1 H b) es vs ->
        st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (fresh_ins es)) reusable) ->
        Env.dom H (vars++st_ids st) ->
        mmap2 (unnest_exp G1 false) es st = (es', eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_reuse st' (PSP.of_list vars) reusable /\
            Env.dom H' (vars++st_ids st') /\
            Forall2
              (fun (es : list exp) (vs : list (Stream svalue)) =>
                 Forall2 (fun e v => sem_exp G2 H' b e [v]) es vs) es' vs /\
            Forall (sem_equation G2 H' b) (concat eqs')).
    Proof.
      intros * Hndup Hwt Hsem Hvalid Hdom Hnorm.
      eapply mmap2_sem in Hnorm; eauto.
      repeat rewrite_Forall_forall.
      eapply unnest_exp_sem; eauto.
    Qed.

    Fact unnest_rhs_sem : forall vars b e H vs es' eqs' st st' reusable,
        NoDup (map fst (anon_in e) ++ PS.elements reusable) ->
        wl_exp G1 e ->
        sem_exp G1 H b e vs ->
        st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (anon_in e)) reusable) ->
        Env.dom H (vars++st_ids st) ->
        unnest_rhs G1 e st = (es', eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_reuse st' (PSP.of_list vars) reusable /\
            Env.dom H' (vars++st_ids st') /\
            (Forall2 (fun e v => sem_exp G2 H' b e [v]) es' vs \/
             exists e', (es' = [e'] /\ sem_exp G2 H' b e' vs)) /\
            Forall (sem_equation G2 H' b) eqs').
    Proof with eauto.
      intros * Hndup1 Hwt Hsem Hvalid Hhistst Hnorm.
      destruct e; try (eapply unnest_exp_sem in Hnorm as [H' [Href1 [Hvalid1 [Hhistst1 [Hsem1 Hsem2]]]]]; eauto;
                       exists H'; repeat (split; eauto)).
      1,2,3:unfold unnest_rhs in Hnorm; repeat inv_bind. 3:inv Hwt; inv Hsem.
      - (* fby *)
        inversion_clear Hwt as [| | | | |????? Hwl1 Hwl2 Hwlr Hl1 Hl2 Hlr| | | | |].
        inversion_clear Hsem as [| | | | |??????????? Hsem1 Hsem2 Hsemr Bools Fby| | | | |].
        assert (length x = length (annots l)) as Hlength1 by (eapply unnest_exps_length; eauto).
        assert (length x2 = length (annots l0)) as Hlength2 by (eapply unnest_exps_length; eauto).
        unfold unnest_exps in *. repeat inv_bind.
        simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
        assert (NoDup (map fst (fresh_ins l1) ++ PS.elements reusable)) as Hndup4 by repeat ndup_r Hndup1.
        assert (NoDup (map fst (fresh_ins l0) ++ PS.elements (ps_adds (map fst (fresh_ins l1)) reusable))) as Hndup3.
        { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup1. }
        assert (NoDup (map fst (fresh_ins l) ++ PS.elements (ps_adds (map fst (fresh_ins l0)) (ps_adds (map fst (fresh_ins l1)) reusable)))) as Hndup2.
        { repeat rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup1. }

        eapply unnest_exps_sem in H0... clear Hsem1.
        destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.
        assert (Forall2 (sem_exp G1 H' b) l0 sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).

        eapply unnest_exps_sem in H1... clear Hsem2.
        destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
        assert (Forall2 (fun e v => sem_exp G2 H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
        { repeat rewrite_Forall_forall. eapply sem_exp_refines... }

        assert (length sr = length l1) as Hlen3 by (eapply Forall2_length in Hsemr; eauto).
        assert (Forall2 (fun er sr => sem_exp G1 H'' b er [sr]) l1 sr) as Hsemr' by (repeat rewrite_Forall_forall; repeat (eapply sem_exp_refines; eauto)).
        assert (Hr:=H2). eapply unnest_resets_sem in H2...
        2:{ solve_forall. eapply unnest_exp_sem in H10 as (H'''&?&?&?&Sem1&?)... inv Sem1...
            exists H'''. repeat (split; eauto). }
        destruct H2 as (H'''&Href3&Hvalid3&Hdom3&Hsem3&Hsem3').

        exists H'''. repeat (split; auto).
        + repeat (etransitivity; eauto).
        + left. eapply unnest_fby_sem... 1,2:solve_length.
          1,2:solve_forall; eapply sem_exp_refines; eauto.
        + repeat rewrite Forall_app. repeat split...
          1,2:solve_forall; (eapply sem_equation_refines; [| eauto]; etransitivity; eauto).
      - (* arrow *)
        inversion_clear Hwt as [| | | | | |????? Hwl1 Hwl2 Hwlr Hl1 Hl2 Hlr| | | |].
        inversion_clear Hsem as [| | | | | |??????????? Hsem1 Hsem2 Hsemr Bools Fby| | | |].
        assert (length x = length (annots l)) as Hlength1 by (eapply unnest_exps_length; eauto).
        assert (length x2 = length (annots l0)) as Hlength2 by (eapply unnest_exps_length; eauto).
        unfold unnest_exps in *. repeat inv_bind.
        simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
        assert (NoDup (map fst (fresh_ins l1) ++ PS.elements reusable)) as Hndup4 by repeat ndup_r Hndup1.
        assert (NoDup (map fst (fresh_ins l0) ++ PS.elements (ps_adds (map fst (fresh_ins l1)) reusable))) as Hndup3.
        { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup1. }
        assert (NoDup (map fst (fresh_ins l) ++ PS.elements (ps_adds (map fst (fresh_ins l0)) (ps_adds (map fst (fresh_ins l1)) reusable)))) as Hndup2.
        { repeat rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup1. }

        eapply unnest_exps_sem in H0... clear Hsem1.
        destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.
        assert (Forall2 (sem_exp G1 H' b) l0 sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).

        eapply unnest_exps_sem in H1... clear Hsem2.
        destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
        assert (Forall2 (fun e v => sem_exp G2 H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
        { repeat rewrite_Forall_forall. eapply sem_exp_refines... }

        assert (length sr = length l1) as Hlen3 by (eapply Forall2_length in Hsemr; eauto).
        assert (Forall2 (fun er sr => sem_exp G1 H'' b er [sr]) l1 sr) as Hsemr' by (repeat rewrite_Forall_forall; repeat (eapply sem_exp_refines; eauto)).
        assert (Hr:=H2). eapply unnest_resets_sem in H2...
        2:{ solve_forall. eapply unnest_exp_sem in H10 as (H'''&?&?&?&Sem1&?)... inv Sem1...
            exists H'''. repeat (split; eauto). }
        destruct H2 as (H'''&Href3&Hvalid3&Hdom3&Hsem3&Hsem3').

        exists H'''. repeat (split; auto).
        + repeat (etransitivity; eauto).
        + left. eapply unnest_arrow_sem... 1,2:solve_length.
          1,2:solve_forall; eapply sem_exp_refines; eauto.
        + repeat rewrite Forall_app. repeat split...
          1,2:solve_forall; (eapply sem_equation_refines; [| eauto]; etransitivity; eauto).
      - (* app *)
        simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
        unfold unnest_exps in H0.
        repeat inv_bind.
        assert (NoDup (map fst (fresh_ins l0) ++ PS.elements reusable)) as Hndup4 by ndup_r Hndup1.
        assert (NoDup (map fst (fresh_ins l) ++ PS.elements (ps_adds (map fst (fresh_ins l0)) reusable))) as Hndup3.
        { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
        assert (length (concat x6) = length (n_in n)) as Hlength4.
        { eapply mmap2_unnest_exp_length in H0; eauto. congruence. }

        eapply unnest_exps_sem in H0...
        destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].

        eapply unnest_noops_exps_sem in H1 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2')...
        3:eapply Forall2_concat...
        2:{ unfold find_node_incks. rewrite H11, map_length; auto. }

        assert (length rs = length l0) as Hlen3 by (eapply Forall2_length in H18; eauto).
        assert (Forall2 (fun er sr => sem_exp G1 H'' b er [sr]) l0 rs) as Hsemr' by (repeat rewrite_Forall_forall; repeat (eapply sem_exp_refines; eauto)).
        assert (Hr:=H2). eapply unnest_resets_sem in H2...
        2:{ solve_forall. eapply unnest_exp_sem in H10 as (H'''&?&?&?&Sem1&?)... inv Sem1...
            exists H'''. repeat (split; eauto). }
        destruct H2 as (H'''&Href3&Hvalid3&Hdom3&Hsem3&Hsem3').

        exists H'''. repeat (split; auto).
        + repeat (etransitivity; eauto).
        + right. eexists; split...
          apply Sapp with (ss0:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))) (rs0:=rs) (bs0:=bs); eauto.
          * rewrite <- concat_map, Forall2_map_2; auto.
            solve_forall. repeat (eapply sem_exp_refines; eauto).
          * rewrite concat_map_singl2. intros k. eapply HGref; eauto.
        + repeat rewrite Forall_app.
          repeat split; solve_forall; (eapply sem_equation_refines; [| eauto]); eauto.
          etransitivity...
    Qed.

    Corollary mmap2_unnest_rhs_sem : forall vars b es H vs es' eqs' st st' reusable,
        NoDup (map fst (anon_ins es) ++ PS.elements reusable) ->
        Forall (wl_exp G1) es ->
        Forall2 (sem_exp G1 H b) es vs ->
        st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (anon_ins es)) reusable) ->
        Env.dom H (vars++st_ids st) ->
        mmap2 (unnest_rhs G1) es st = (es', eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_reuse st' (PSP.of_list vars) reusable /\
            Env.dom H' (vars++st_ids st') /\
            Forall2 (fun es' vs =>
                       Forall2 (fun e v => sem_exp G2 H' b e [v]) es' vs \/
                       exists e', (es' = [e'] /\ sem_exp G2 H' b e' vs)) es' vs /\
            Forall (sem_equation G2 H' b) (concat eqs')).
    Proof with eauto.
      induction es; intros * Hndup Hwt Hsem Hvalid Histst Hmap;
        repeat inv_bind.
      - exists H; simpl. inv Hsem. repeat (split; auto).
      - inv Hwt. inv Hsem.
        unfold anon_ins in *. simpl in *. rewrite map_app, ps_adds_app in Hvalid.
        assert (NoDup (map fst (anon_ins es) ++ PS.elements reusable)) as Hndup4 by ndup_r Hndup.
        assert (NoDup (map fst (anon_in a) ++ PS.elements (ps_adds (map fst (anon_ins es)) reusable))) as Hndup3.
        { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

        assert (st_follows st x1) as Hfollows1 by eauto.
        eapply unnest_rhs_sem in H0...
        destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
        assert (Forall2 (sem_exp G1 H' b) es l') as Hsem'.
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

    Corollary unnest_rhss_sem : forall vars b es H vs es' eqs' st st' reusable,
        NoDup (map fst (anon_ins es) ++ PS.elements reusable) ->
        Forall (wt_exp G1 (vars++st_tys st)) es ->
        Forall2 (sem_exp G1 H b) es vs ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_ins es)) reusable) ->
        Env.dom H (map fst vars++st_ids st) ->
        unnest_rhss G1 es st = (es', eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
            Env.dom H' (map fst vars++st_ids st') /\
            Forall (fun '(e, v) => sem_exp G2 H' b e v)
                   (combine_for_numstreams es' (concat vs)) /\
            Forall (sem_equation G2 H' b) eqs').
    Proof with eauto.
      intros * Hndup Hwt Hsem Hvalid Histst Hnorm.
      assert (Forall (wt_exp G2 (vars++st_tys st')) es') as Hwt'.
      { eapply unnest_rhss_wt in Hnorm as [? ?]... }
      unfold unnest_rhss in *.
      repeat inv_bind.
      eapply mmap2_unnest_rhs_sem in H0...
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

    Fact unnest_equation_sem : forall vars H b equ eqs' st st' reusable,
        NoDup (map fst (anon_in_eq equ) ++ PS.elements reusable) ->
        wt_equation G1 (vars++st_tys st) equ ->
        sem_equation G1 H b equ ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in_eq equ)) reusable) ->
        Env.dom H (map fst vars++st_ids st) ->
        unnest_equation G1 equ st = (eqs', st') ->
        (exists H', Env.refines eq H H' /\
               st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
               Env.dom H' (map fst vars++st_ids st') /\
               Forall (sem_equation G2 H' b) eqs').
    Proof with eauto.
      intros * Hndup Hwt Hsem Hvalid Histst Hnorm.
      unfold unnest_equation in Hnorm.
      destruct equ as [xs es]. inv Hwt. inv Hsem.
      repeat inv_bind.
      assert (annots x = annots es) as Hannots by (eapply unnest_rhss_annots; eauto).
      eapply unnest_rhss_sem in H2...
      destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      exists H'. repeat (split; eauto).
      apply Forall_app. split...
      clear Hsem1'.
      repeat rewrite_Forall_forall. simpl_length.
      assert (length xs = length (annots x)) as Hlen' by solve_length.
      destruct x1. repeat simpl_In. inv H7.
      assert (HIn := H8).
      eapply In_nth with (d:=(hd_default [], [])) in H8. destruct H8 as [n [Hn Hnth]].
      rewrite combine_for_numstreams_length in Hn; auto. rewrite <- (combine_for_numstreams_length _ (concat ss)) in Hn; solve_length.
      assert (HIn' := Hn).
      apply nth_In with (d:=(hd_default [], [])) in HIn'.
      specialize (Hsem1 _ HIn').
      destruct (nth _ _ _) eqn:Hnth' in Hsem1. rewrite Hnth' in HIn'.
      assert (e = e0) as Hee0.
      { rewrite split_nth in Hnth; inv Hnth.
        rewrite split_nth in Hnth'; inv Hnth'.
        repeat rewrite combine_for_numstreams_fst_split; solve_length. } subst.
      apply Seq with (ss0:=[l0]).
      + repeat constructor...
      + simpl. rewrite app_nil_r.
        repeat rewrite_Forall_forall.
        * rewrite <- Hannots in H2.
          replace (length l) with (numstreams e0). replace (length l0) with (numstreams e0). reflexivity.
          { eapply Forall_forall in HIn'. 2:eapply combine_for_numstreams_numstreams; solve_length.
            eauto. }
          { eapply Forall_forall in HIn. 2:eapply combine_for_numstreams_numstreams; solve_length.
            eauto. }
        * eapply sem_var_refines...
          specialize (combine_for_numstreams_nth_2 x xs (concat ss) n n0 e0 l l0
                                                   a b0 (hd_default [], []) (hd_default [], [])) as Hcomb.
          apply Hcomb in H7. clear Hcomb.
          2,3:solve_length.
          2:(rewrite combine_for_numstreams_length in Hn; auto; solve_length).
          2,3:auto.
          destruct H7 as (?&?&?&?).
          eapply H3... solve_length.
    Qed.

    Corollary unnest_equations_sem : forall vars b eqs H eqs' st st' reusable,
        NoDup (map fst (anon_in_eqs eqs) ++ PS.elements reusable) ->
        Forall (wt_equation G1 (vars ++ st_tys st)) eqs ->
        Forall (sem_equation G1 H b) eqs ->
        st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in_eqs eqs)) reusable) ->
        Env.dom H (map fst vars++st_ids st) ->
        unnest_equations G1 eqs st = (eqs', st') ->
        (exists H', Env.refines eq H H' /\
               Forall (sem_equation G2 H' b) eqs').
    Proof with eauto.
      induction eqs; intros * Hndup Hwt Hsem Hvalid Hdome Hnorm;
        unfold unnest_equations in *; inv Hwt; inv Hsem; repeat inv_bind; simpl.
      - exists H...
      - unfold anon_in_eqs in *; simpl in *. rewrite map_app, ps_adds_app in Hvalid.
        assert (NoDup (map fst (anon_in_eqs eqs) ++ PS.elements reusable)) as Hndup4 by ndup_r Hndup.
        assert (NoDup (map fst (anon_in_eq a) ++ PS.elements (ps_adds (map fst (anon_in_eqs eqs)) reusable))) as Hndup3.
        { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

        assert (Forall (wt_equation G1 (vars ++ st_tys x1)) eqs) as Hwt' by (solve_forall; repeat solve_incl).
        eapply unnest_equation_sem in H0...
        destruct H0 as [H' [Href1 [Hvalid1 [Histst1 Hsem1]]]].
        assert (Forall (sem_equation G1 H' b) eqs) by (solve_forall; eapply sem_equation_refines; eauto).

        assert (unnest_equations G1 eqs x1 = (concat x2, st')) as Hnorm.
        { unfold unnest_equations; repeat inv_bind; eauto. }
        eapply IHeqs in Hnorm...
        destruct Hnorm as [H'' [Href Hsem2]].
        exists H''. repeat split...
        + etransitivity...
        + eapply Forall_app. split...
          solve_forall. eapply sem_equation_refines...
    Qed.

    (** *** Preservation of the semantics while restricting an environment *)

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

    Fact sem_exp_restrict {prefs} : forall (G : @global prefs) vars H b e vs,
        wt_exp G vars e ->
        sem_exp G H b e vs ->
        sem_exp G (Env.restrict H (List.map fst vars)) b e vs.
    Proof with eauto.
      induction e using exp_ind2; intros vs Hwt Hsem; inv Hwt; inv Hsem.
      - (* const *) constructor...
      - (* enum *) constructor...
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
        + repeat rewrite_Forall_forall. eapply H2...
      - (* arrow *)
        econstructor...
        + repeat rewrite_Forall_forall. eapply H0...
        + repeat rewrite_Forall_forall. eapply H1...
        + repeat rewrite_Forall_forall. eapply H2...
      - (* when *)
        econstructor...
        + repeat rewrite_Forall_forall. eapply H0...
        + eapply sem_var_restrict...
      - (* merge *)
        econstructor...
        + eapply sem_var_restrict...
        + do 2 (eapply Forall2_impl_In; [|eauto]; intros).
          do 2 (eapply Forall_forall in H0; eauto).
          do 2 (eapply Forall_forall in H8; eauto).
      - (* case *)
        econstructor...
        + clear H21.
          do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst).
          do 2 (eapply Forall_forall in H0; eauto).
          eapply Forall_forall in H11; eauto.
        + eapply Forall2_impl_In; [|eauto]; intros.
          eapply Forall_forall in H1; eauto.
          eapply Forall_forall in H13; eauto.
      - (* app *)
        econstructor...
        + repeat rewrite_Forall_forall. eapply H0...
        + repeat rewrite_Forall_forall. eapply H1...
    Qed.

    Fact sem_equation_restrict {prefs} : forall (G : @global prefs) vars H b eq,
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
        Unshelve. eapply OpAux.bool_velus_type.
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

    Fact sem_equation_In {prefs} : forall (G : @global prefs) H b eqs,
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

    Fact unnest_node_sem_equation : forall H n ins,
        wt_node G1 n ->
        Env.dom H (List.map fst (n_in n ++ n_vars n ++ n_out n)) ->
        Forall2 (sem_var H) (idents (n_in n)) ins ->
        Forall (sem_equation G1 H (clocks_of ins)) (n_eqs n) ->
        exists H', Env.refines eq H H' /\
              Forall (sem_equation G2 H' (clocks_of ins)) (n_eqs (unnest_node G1 n)).
    Proof with eauto.
      intros * Hwt Hdom Hins Hsem.
      specialize (n_nodup n) as Hndup; rewrite fst_NoDupMembers in Hndup; repeat rewrite map_app in Hndup.
      eapply unnest_equations_sem with (eqs:=n_eqs n) (st:=init_st)...
      5: simpl; rewrite <- surjective_pairing; subst; reflexivity.
      - rewrite PSP.elements_empty, app_nil_r.
        repeat ndup_r Hndup...
      - unfold st_tys. rewrite init_st_anns, app_nil_r.
        destruct Hwt as [_ [_ [_ [_ Hwt]]]]; eauto.
      - rewrite map_fst_idty.
        apply init_st_valid_reuse.
        + replace (ps_adds _ PS.empty) with (ps_from_list (map fst (anon_in_eqs (n_eqs n)))); auto.
          rewrite ps_from_list_ps_of_list.
          repeat rewrite ps_of_list_ps_to_list_Perm; repeat rewrite map_app; repeat rewrite <- app_assoc in *; auto.
          repeat ndup_r Hndup.
          repeat rewrite app_assoc in Hndup. apply NoDup_app_l in Hndup.
          repeat rewrite <- app_assoc in Hndup; auto.
        + apply norm1_not_in_elab_prefs.
        + rewrite <- ps_from_list_ps_of_list, PS_For_all_Forall'.
          pose proof (n_good n) as (Good&_).
          eapply Forall_incl; [eauto|].
          repeat rewrite map_app.
          repeat apply incl_tl.
          repeat rewrite app_assoc. apply incl_appl. reflexivity.
        + replace (ps_adds _ PS.empty) with (ps_from_list (map fst (anon_in_eqs (n_eqs n)))); auto.
          rewrite PS_For_all_Forall'.
          pose proof (n_good n) as (Good&_).
          eapply Forall_incl; [eauto|].
          repeat rewrite map_app.
          repeat apply incl_tl.
          repeat apply incl_appr. reflexivity.
      - unfold st_ids. rewrite init_st_anns, app_nil_r, map_fst_idty...
    Qed.

    Lemma unnest_node_eq : forall f n ins outs,
        Forall2 (fun n n' => n_name n = n_name n') G1.(nodes) G2.(nodes) ->
        wt_global (Global G1.(enums) (n::G1.(nodes))) ->
        wc_global (Global G1.(enums) (n::G1.(nodes))) ->
        Ordered_nodes (Global G1.(enums) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(enums) ((unnest_node G1 n)::G2.(nodes))) ->
        sem_node (Global G1.(enums) (n::G1.(nodes))) f ins outs ->
        sem_node (Global G2.(enums) ((unnest_node G1 n)::G2.(nodes))) f ins outs.
    Proof with eauto.
      intros * Hnames HwtG HwcG Hord1 Hord2 Hsem.
      assert (Forall (fun n' => exists v, In v G1.(nodes) /\ n_name n <> n_name n') G2.(nodes)) as Hnames'.
      { assert (length G1.(nodes) = length G2.(nodes)) by (eapply Forall2_length in Hnames; eauto).
        destruct HwtG as (_&HwtG').
        inv HwtG'. destruct H2. eapply Forall2_ignore1. solve_forall. }

      inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
      - erewrite find_node_now in Hfind; eauto. inv Hfind.
        (*The semantics of equations can be given according to G only *)
        eapply Forall_sem_equation_global_tl in H3; eauto.
        2:{ inv Hord1. destruct H5 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }
        (* New env H' (restrict H) and its properties *)
        eapply LCS.sem_node_restrict in H3 as (Hdom&Hins'&Houts'&Heqs'); eauto.
        2:{ inv HwcG. destruct H5 as ((?&?&?&?)&_); auto. }
        remember (Env.restrict H (List.map fst (n_in n0++n_vars n0++n_out n0))) as H'.
        clear H1 H2 HeqH'.
        destruct HwtG as (_&HwtG'). inv HwtG'. destruct H2. rename H0 into Hwt.

        simpl in *.
        replace {| enums := enums G1; nodes := nodes G1 |} with G1 in Heqs', Hwt by (destruct G1; auto).
        eapply unnest_node_sem_equation in Heqs' as (H''&Href'&Heqs'')...
        eapply Snode with (H0:=H''); simpl. 5:reflexivity.
        + erewrite find_node_now; eauto.
        + simpl. repeat rewrite_Forall_forall. eapply sem_var_refines...
        + simpl. repeat rewrite_Forall_forall. eapply sem_var_refines...
        + clear Hins' Houts' Hdom.
          apply Forall_sem_equation_global_tl'; simpl...
          * eapply find_node_not_Is_node_in in Hord2.
            2:erewrite find_node_now; eauto. eauto.
          * eapply Forall_impl; [|eauto]; intros.
            destruct G2; auto.
      - erewrite find_node_other in Hfind; eauto.
        eapply sem_node_cons'...
        destruct G2; apply HGref.
        econstructor...
        eapply Forall_impl_In; [| eauto]. intros eq Hin Hsem.
        destruct G1; eapply sem_equation_global_tl...
        eapply find_node_later_not_Is_node_in in Hord1...
        intro Hisin. apply Hord1. rewrite Is_node_in_Exists. rewrite Exists_exists.
        eexists...
    Qed.

  End unnest_node_sem.

  Fact unnest_nodes_names' : forall enums nds,
      Forall2 (fun n n' => n_name n = n_name n') nds (unnest_nodes enums nds).
  Proof.
    intros.
    induction nds; simpl; auto.
  Qed.

  Fact wt_global_Ordered_nodes {prefs} : forall (G: @global prefs),
      wt_global G ->
      Ordered_nodes G.
  Proof.
    intros G Hwt.
    apply wl_global_Ordered_nodes; auto.
  Qed.
  Hint Resolve wt_global_Ordered_nodes.

  Lemma unnest_global_refines : forall G,
      wt_global G ->
      wc_global G ->
      global_sem_refines G (unnest_global G).
  Proof with eauto.
    intros (enms&nds).
    induction nds; intros * Hwt Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwt':=Hwt).
      eapply unnest_global_wt, wt_global_Ordered_nodes in Hwt' ;
        unfold unnest_global in Hwt'; simpl in Hwt'.
      apply global_sem_ref_cons with (f:=n_name a)...
      + destruct Hwt as (?&Hwt). inv Hwt. inv Hwc.
        eapply IHnds... split; auto.
      + intros ins outs Hsem; simpl in *.
        replace enms with ((Global enms (unnest_nodes enms nds)).(enums)); auto.
        eapply unnest_node_eq...
        * apply unnest_nodes_eq.
        * destruct Hwt as (?&Hwt). inv Hwt. inv Hwc.
          eapply IHnds... split; auto.
        * apply unnest_nodes_names'.
  Qed.

  Corollary unnest_global_sem : forall G f ins outs,
      wt_global G ->
      wc_global G ->
      sem_node G f ins outs ->
      sem_node (unnest_global G) f ins outs.
  Proof.
    intros.
    eapply unnest_global_refines in H; eauto.
    specialize (H f ins outs); auto.
  Qed.

  Corollary unnest_global_sem_clock_inputs : forall G f ins,
      LCS.sem_clock_inputs G f ins ->
      LCS.sem_clock_inputs (unnest_global G) f ins.
  Proof.
    intros.
    specialize (unnest_global_eq G) as Heq.
    destruct H as [H [n' [Hfind [Hvars Hsem]]]].
    eapply global_iface_eq_find in Heq as [? [? [Hname [_ [Hin Hout]]]]]; eauto.
    exists H. exists x. repeat split; auto.
    1,2:congruence.
  Qed.

  (** ** Additional clock-semantics properties *)

  Hint Constructors LCS.sem_exp_anon.
  Lemma normalized_lexp_sem_sem_anon {prefs} : forall (G : @global prefs) H b e vs,
      normalized_lexp e ->
      sem_exp G H b e vs ->
      LCS.sem_exp_anon G H b e vs.
  Proof.
    intros * Hnormed Hsem. revert vs Hsem.
    induction Hnormed; intros; inv Hsem; eauto.
    inv H8; inv H4. eauto.
  Qed.

  Lemma normalized_cexp_sem_sem_anon {prefs} : forall (G: @global prefs) H b e vs,
      normalized_cexp e ->
      sem_exp G H b e vs ->
      LCS.sem_exp_anon G H b e vs.
  Proof.
    induction e using exp_ind2; intros * Hnormed Hsem; inv Hnormed.
    1-13:try (solve [eapply normalized_lexp_sem_sem_anon; eauto]).
    1,2:inv Hsem; econstructor; eauto.
    - do 2 (eapply Forall2_impl_In; [|eauto]; intros).
      do 2 (eapply Forall_forall in H0; [|eauto]; intros).
      eapply Forall_forall in H2 as (?&?&?); eauto; subst.
      rewrite In_singleton in H5; subst.
      eapply H0; eauto.
    - clear H15. do 2 (eapply Forall2_impl_In; [|eauto]; subst; intros).
      do 2 (eapply Forall_forall in H0; [|eauto]; intros).
      eapply Forall_forall in H7 as (?&?&?); eauto; subst.
      rewrite In_singleton in H6; subst.
      eapply H0; eauto.
    - inv H16; inv H9.
      repeat constructor. inv H1; auto.
  Qed.

  Lemma unnested_equation_sem_sem_anon {prefs} : forall (G: @global prefs) env H b equ,
      unnested_equation G equ ->
      wc_equation G env equ ->
      sem_equation G H b equ ->
      LCS.sem_equation_anon G H b equ.
  Proof.
    intros * Hnormed Hwc Hsem.
    inv Hnormed; inv Hsem; intros.
    - inv H9; inv H8.
      inv H6.
      repeat (econstructor; eauto).
      + eapply Forall2_impl_In; [|eauto].
        intros. eapply normalized_lexp_sem_sem_anon; eauto. eapply Forall_forall; eauto.
      + eapply Forall2_impl_In; [|eauto]. intros * In1 In2 Sem.
        eapply normalized_lexp_sem_sem_anon; eauto.
        eapply Forall_forall in H3 as (?&(?&?)&?); eauto; subst; constructor.
      + destruct Hwc as (_&Hcks&_); simpl in *; rewrite app_nil_r in *.
        rewrite Forall2_map_2, Forall2_swap_args in Hcks.
        eapply Forall2_trans_ex in H10; [|eauto].
        eapply Forall2_impl_In; [|eauto]. intros (?&?&?) ? ? ? (?&?&?&?).
        destruct o; simpl in *; subst; auto.
    - inv H8; inv H7. inv H5.
      inv H10; inv H7. inv H13; inv H8.
      repeat (econstructor; eauto).
      1,2:eapply normalized_lexp_sem_sem_anon; eauto.
      eapply Forall2_impl_In; [|eauto]. intros * In1 In2 Sem.
      eapply normalized_lexp_sem_sem_anon; eauto.
      eapply Forall_forall in H2 as (?&(?&?)&?); eauto; subst; constructor.
    - inv H8; inv H7. inv H5.
      inv H10; inv H7. inv H13; inv H8.
      repeat (econstructor; eauto).
      1,2:eapply normalized_lexp_sem_sem_anon; eauto.
      eapply Forall2_impl_In; [|eauto]. intros * In1 In2 Sem.
      eapply normalized_lexp_sem_sem_anon; eauto.
      eapply Forall_forall in H2 as (?&(?&?)&?); eauto; subst; constructor.
    - inv H6; inv H5.
      repeat econstructor; eauto.
      eapply normalized_cexp_sem_sem_anon; eauto.
  Qed.

  Corollary normalized_equation_sem_sem_anon {prefs} : forall (G: @global prefs) env H b equ out,
      normalized_equation G out equ ->
      wc_equation G env equ ->
      sem_equation G H b equ ->
      LCS.sem_equation_anon G H b equ.
  Proof.
    intros.
    eapply unnested_equation_sem_sem_anon; eauto.
    eapply normalized_eq_unnested_eq; eauto.
  Qed.

  Lemma sc_lexp {prefs} : forall (G: @global prefs) H bs env e s ck,
      wc_global G ->
      LCS.sc_nodes G ->
      NoDupMembers env ->
      wc_env (idck env) ->
      LCS.sc_var_inv' (idck env) H bs ->
      normalized_lexp e ->
      clockof e = [ck] ->
      wt_exp G (idty env) e ->
      wc_exp G (idck env) e ->
      sem_exp G H bs e [s] ->
      sem_clock H bs ck (abstract_clock s).
  Proof.
    intros * ? ? ? ? ? Hnormed Hck ? ? Hsem.
    eapply normalized_lexp_sem_sem_anon in Hsem; eauto.
    eapply LCS.sc_exp in Hsem; eauto.
    2:rewrite NoDupMembers_idck; auto.
    rewrite Hck in Hsem; simpl in Hsem.
    inv Hsem; auto.
  Qed.

  (** ** Preservation of the semantics through the second pass *)

  Module Import CIStr := CoindIndexedFun Ids Op OpAux Cks CStr IStr.

  Section normfby_node_sem.
    Variable G1 : @global norm1_prefs.
    Variable G2 : @global norm2_prefs.

    (** *** Manipulation of initialization streams *)

    (** We want to specify the semantics of the init equations created during the normalization
      with idents stored in the env *)

    CoFixpoint const_val (b : Stream bool) (v : value) : Stream svalue :=
      (if Streams.hd b then present v else absent) ⋅ (const_val (Streams.tl b) v).

    Fact const_val_Cons : forall b bs v,
        const_val (b ⋅ bs) v =
        (if b then present v else absent) ⋅ (const_val bs v).
    Proof.
      intros b bs v.
      rewrite unfold_Stream at 1; reflexivity.
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

    CoFixpoint sfby_reset (v0 : value) (s : Stream svalue) (sr : Stream bool) (v : value) :=
      match s, sr with
      | absent ⋅ s', false ⋅ sr' => absent ⋅ (sfby_reset v0 s' sr' v)
      | (present v') ⋅ s', false ⋅ sr' => (present v) ⋅ (sfby_reset v0 s' sr' v')
      | absent ⋅ s', true ⋅ sr' => absent ⋅ (sfby_reset v0 s' sr' v0)
      | (present v') ⋅ s', true ⋅ sr' => (present v0) ⋅ (sfby_reset v0 s' sr' v')
      end.

    Fact sfby_reset_Cons : forall v0 x y s' sr' v,
        sfby_reset v0 (x ⋅ s') (y ⋅ sr') v =
        match x, y with
        | absent, false => absent ⋅ (sfby_reset v0 s' sr' v)
        | (present v'), false => (present v) ⋅ (sfby_reset v0 s' sr' v')
        | absent, true => absent ⋅ (sfby_reset v0 s' sr' v0)
        | (present v'), true => (present v0) ⋅ (sfby_reset v0 s' sr' v')
        end.
    Proof.
      intros.
      rewrite unfold_Stream at 1; simpl.
      destruct x, y; reflexivity.
    Qed.

    Add Parametric Morphism : sfby_reset
        with signature eq ==> @EqSt svalue ==> @EqSt bool ==> eq ==> @EqSt svalue
          as sfby_reset_EqSt.
    Proof.
      cofix CoFix.
      intros v [? ?] [? ?] Heq1 [? ?] [? ?] Heq2 ?.
      inv Heq1; inv Heq2; simpl in *; subst.
      constructor; simpl.
      + destruct s1, b0; auto.
      + destruct s1, b0; auto.
    Qed.

    Definition false_val := Venum 0.
    Definition true_val := Venum 1.

    Lemma ite_false : forall bs xs ys,
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

    Lemma sfby_reset_fby1 : forall bs v0 v v' s r,
        aligned s bs ->
        LiftO (v = v0) (fun v' => v = v') v' ->
        fby1 v' (const_val bs v0) s r (sfby_reset v0 s r v).
    Proof with eauto.
      cofix hold_fby1.
      intros [b bs] * Haligned Hlift.
      specialize (hold_fby1 bs).
      inv Haligned;
        rewrite const_val_Cons; rewrite unfold_Stream; simpl.
      - unfold_Stv r.
        + constructor. eapply hold_fby1; simpl; eauto.
        + destruct v'; simpl in *; subst.
          1,2:econstructor; eauto; eapply hold_fby1; simpl; eauto.
      - unfold_Stv r.
        + constructor. eapply hold_fby1; simpl; eauto.
        + destruct v'; simpl in *; subst.
          1,2:econstructor; eauto; eapply hold_fby1; simpl; eauto.
    Qed.

    Corollary hold_fby : forall bs v0 s r,
        aligned s bs ->
        fby (const_val bs v0) s r (sfby_reset v0 s r v0).
    Proof.
      intros * Hal.
      apply sfby_reset_fby1; simpl; auto.
    Qed.

    Definition init_stream bs rs :=
      sfby_reset true_val (enum bs 0) rs true_val.

    Instance init_stream_Proper:
      Proper (@EqSt bool ==> @EqSt bool ==> @EqSt svalue) init_stream.
    Proof.
      intros bs bs' Heq1 rs rs' Heq2.
      unfold init_stream. rewrite Heq1, Heq2. reflexivity.
    Qed.

    Lemma fby1_case : forall bs v v' y0s ys zs rs v1 v2,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        LiftO (v1 = true_val) (fun v' => v1 = false_val /\ v' = v2) v' ->
        fby1 v' y0s ys rs zs ->
        case (sfby_reset true_val (const_val bs false_val) rs v1) [(sfby_reset v ys (Streams.const false) v2);y0s] zs.
    Proof with eauto.
      cofix CoFix.
      intros [b bs] * Hsync Hv' Hfby1.
      eapply fby1_aligned in Hsync as [Hsync1 [Hsync2 Hsync3]]; [|eauto].
      inv Hfby1; inv Hsync1; inv Hsync2; inv Hsync3; simpl in *.
      1-5:rewrite CommonStreams.const_Cons, const_val_Cons; repeat rewrite sfby_reset_Cons.
      - constructor. eapply CoFix; eauto. simpl; auto.
        repeat constructor; auto.
      - econstructor.
        + eapply CoFix; eauto. simpl; auto.
        + repeat constructor; simpl; congruence.
        + constructor. reflexivity.
      - constructor.
        + eapply CoFix; eauto.
        + repeat constructor; auto.
      - subst; econstructor.
        + eapply CoFix; eauto. simpl; auto.
        + repeat constructor; simpl; congruence.
        + constructor. reflexivity.
      - destruct Hv'; subst. econstructor.
        + eapply CoFix; eauto. simpl; auto.
        + repeat constructor; simpl; congruence.
        + constructor. reflexivity.
    Qed.

    Corollary fby_init_stream_case : forall bs v y0s ys rs zs,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        fby y0s ys rs zs ->
        case (init_stream bs rs) [(sfby_reset v ys (Streams.const false) v); y0s] zs.
      intros * Hsync Hfby1.
      eapply fby1_case in Hfby1; eauto. 2:simpl; eauto.
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

    Lemma arrow1_case : forall bs b y0s ys zs rs v1,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        value_to_bool' v1 = Some b ->
        arrow1 b y0s ys rs zs ->
        case (sfby_reset true_val (const_val bs false_val) rs v1) [ys;y0s] zs.
    Proof with eauto.
      cofix CoFix.
      intros [b bs] * Hsync Hb Harrow1.
      eapply arrow1_aligned in Hsync as [Hsync1 [Hsync2 Hsync3]]; [|eauto].
      inv Harrow1; inv Hsync1; inv Hsync2; inv Hsync3; simpl in *.
      1-5:rewrite const_val_Cons, sfby_reset_Cons.
      - constructor.
        + eapply CoFix; eauto. simpl; auto.
        + repeat constructor; auto.
      - econstructor.
        + eapply CoFix; eauto. simpl; auto.
        + repeat constructor; simpl; congruence.
        + constructor. reflexivity.
      - constructor.
        + eapply CoFix; eauto.
        + repeat constructor; auto.
      - destruct v1; inv Hb.
        assert (e ==b true_tag = true) as Htag.
        { destruct (e ==b true_tag), (e ==b false_tag); eauto; inv H4. }
        rewrite equiv_decb_equiv in Htag; inv Htag.
        econstructor.
        + eapply CoFix; eauto. simpl; auto.
        + repeat constructor; simpl; congruence.
        + constructor. reflexivity.
      - destruct v1; inv Hb.
        assert (e ==b false_tag = true) as Htag.
        { destruct (e ==b true_tag), (e ==b false_tag); eauto; inv H4. }
        rewrite equiv_decb_equiv in Htag; inv Htag.
        econstructor.
        + eapply CoFix; eauto.
        + repeat constructor; simpl; congruence.
        + constructor. reflexivity.
    Qed.

    Corollary arrow_init_stream_case : forall bs y0s ys rs zs,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        arrow y0s ys rs zs ->
        case (init_stream bs rs) [ys;y0s] zs.
    Proof.
      intros * Hsync Harrow.
      eapply arrow1_case with (v1:=true_val) in Harrow; eauto.
      unfold init_stream.
      rewrite const_val_enum; auto.
    Qed.

    Lemma ac_sfby_reset : forall v0 xs rs v,
        abstract_clock (sfby_reset v0 xs rs v) ≡ abstract_clock xs.
    Proof.
      cofix CoFix. intros v0 [x xs] [r rs] v.
      rewrite sfby_reset_Cons.
      destruct x, r; constructor; simpl; auto.
    Qed.

    Lemma init_stream_ac : forall bs rs,
        abstract_clock (init_stream bs rs) ≡ bs.
    Proof.
      intros bs rs.
      unfold init_stream.
      rewrite ac_sfby_reset, <- ac_enum. 1,2:reflexivity.
    Qed.

    (** *** Additional stuff *)

    Definition st_vars (st : fresh_st (type * clock * option PS.t)) : list (ident * (type * clock)) :=
      idty (st_anns st).

    Fact st_ids_st_vars : forall st,
        st_ids st = map fst (st_vars st).
    Proof.
      intros. unfold st_ids, st_vars, idty.
      rewrite map_map; simpl.
      apply map_ext. intros [? [[? ?] ?]]; auto.
    Qed.

    Fact st_tys'_st_vars : forall st,
        st_tys' st = idty (st_vars st).
    Proof.
      intros. unfold st_tys', st_vars, idty.
      repeat rewrite map_map.
      apply map_ext. intros [? [[? ?] ?]]; auto.
    Qed.

    Fact st_clocks'_st_vars : forall st,
        st_clocks' st = idck (st_vars st).
    Proof.
      intros. unfold st_clocks', idck, st_vars, idty.
      repeat rewrite map_map.
      apply map_ext. intros [? [[? ?] ?]]; auto.
    Qed.

    Fact st_follows_vars_incl : forall st st',
        st_follows st st' ->
        incl (st_vars st) (st_vars st').
    Proof.
      intros.
      unfold st_vars. apply incl_map, st_follows_incl, H.
    Qed.

    Import NormFby.

    Fact st_valid_after_NoDupMembers : forall st vars,
        NoDupMembers vars ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        NoDupMembers (vars++st_vars st).
    Proof.
      intros * Hndup Hvalid.
      eapply st_valid_NoDup in Hvalid.
      rewrite ps_of_list_ps_to_list_Perm in Hvalid. 2:rewrite <- fst_NoDupMembers; auto.
      rewrite Permutation_app_comm, st_ids_st_vars, <- map_app, <- fst_NoDupMembers in Hvalid; auto.
    Qed.

    Fact fresh_ident_refines' {B V} : forall vars H H' a id (v : V) (st st' : fresh_st B),
        st_valid_after st (PSP.of_list vars) ->
        Env.dom H (vars++st_ids st) ->
        fresh_ident norm2 a st = (id, st') ->
        H' = Env.add id v H ->
        Env.refines eq H H'.
    Proof with eauto.
      intros * Hvalid Hdom Hfresh Heq.
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

    (** *** Relation between state and history *)

    Definition init_eqs_valids bs H (st : fresh_st (Op.type * clock * option PS.t)) :=
      Forall (fun '(id, (ck, xr)) =>
                (exists bs' rs rs',
                    sem_clock H bs ck bs' /\
                    Forall2 (sem_var H) (PSP.to_list xr) rs /\
                    bools_ofs rs rs' /\
                    sem_var H id (init_stream bs' rs'))) (st_inits st).

    Definition hist_st (vars : list (ident * clock)) b H st :=
      Env.dom H (map fst vars++st_ids st) /\
      init_eqs_valids b H st /\
      LCS.sc_var_inv' (vars++st_clocks' st) H b.

    Fact fresh_ident_init_eqs : forall vars b ty ck id v H st st',
        st_valid_after st (PSP.of_list vars) ->
        Env.dom H (vars ++ st_ids st) ->
        fresh_ident norm2 ((ty, ck), None) st = (id, st') ->
        init_eqs_valids b H st ->
        init_eqs_valids b (Env.add id v H) st'.
    Proof with auto.
      intros * Hvalid Hdom Hfresh Hinits.
      assert (~In id (st_ids st)) as Hnin by (eapply Facts.fresh_ident_nIn in Hfresh; eauto).
      assert (Env.refines eq H (Env.add id v H)) as Href.
      { eapply fresh_ident_refines' in Hfresh; eauto. }
      eapply fresh_ident_false_st_inits in Hfresh.
      unfold init_eqs_valids in *. rewrite Hfresh.
      solve_forall. destruct H1 as (bs'&rs&rs'&?&?&?&?).
      exists bs' ; exists rs; exists rs' ; repeat split; eauto.
      - eapply LCS.sem_clock_refines; eauto.
      - solve_forall.
        eapply sem_var_refines; eauto.
      - eapply sem_var_refines; eauto.
    Qed.

    Fact fresh_ident_hist_st : forall vars b ty ck id v H st st',
        st_valid_after st (PSP.of_list (map fst vars)) ->
        sem_clock H b ck (abstract_clock v) ->
        fresh_ident norm2 ((ty, ck), None) st = (id, st') ->
        hist_st vars b H st ->
        hist_st vars b (Env.add id v H) st'.
    Proof with auto.
      intros * Hvalid Hsem Hfresh [H1 [H2 H3]].
      assert (~In id (st_ids st)) as Hnin by (eapply Facts.fresh_ident_nIn in Hfresh; eauto).
      assert (st_valid_after st' (PSP.of_list (map fst vars))) as Hvalid2 by eauto.
      assert (Hfresh':=Hfresh). apply fresh_ident_anns in Hfresh'.
      assert (Env.refines eq H (Env.add id v H)) as Href.
      { eapply fresh_ident_refines' in Hfresh; eauto. }
      repeat split.
      - eapply fresh_ident_dom; eauto.
      - eapply fresh_ident_init_eqs in Hfresh; eassumption.
      - unfold st_clocks', LCS.sc_var_inv' in *.
        rewrite Hfresh'; simpl.
        rewrite <- Permutation_middle. constructor.
        + exists v; split.
          * econstructor. eapply Env.add_1. 1,2:reflexivity.
          * eapply LCS.sem_clock_refines; eauto.
        + eapply LCS.sc_var_inv'_refines with (H:=H); eauto.
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
        sem_exp G2 H b (add_whens (Econst c) ty ck) [const b' c].
    Proof.
      induction ck; try destruct p; intros * Hsem; assert (Hsem':=Hsem); inv Hsem'; simpl.
      constructor. rewrite H1; reflexivity.
      1,2,3: (eapply Swhen; eauto; simpl;
              repeat constructor;
              eapply sem_clock_when_const; eauto).
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
        sem_exp G2 H b (add_whens (Eenum c ty) ty ck) [enum b' c].
    Proof.
      induction ck; try destruct p; intros * Hsem; assert (Hsem':=Hsem); inv Hsem'; simpl.
      constructor. rewrite H1; reflexivity.
      1,2,3: (eapply Swhen; eauto; simpl;
              repeat constructor;
              eapply sem_clock_when_enum; eauto).
    Qed.

    Lemma Forall2_bools : forall H xs vs rs,
        Forall2 (sem_var H) xs vs ->
        bools_ofs vs rs ->
        exists vs' , Forall2 (sem_var H) (PSP.to_list (PSP.of_list xs)) vs' /\
                bools_ofs vs' rs.
    Proof.
      intros * Vars Bools; simpl.
      assert (SameElements eq xs (PSP.to_list (PSP.of_list xs))) as Same.
      { eapply ps_of_list_ps_to_list_SameElements; eauto. }
      assert (Vars':=Vars). eapply Forall2_SameElements_1 in Vars' as (vs'&Same'&?); eauto.
      rewrite Same' in Bools. 1-3:eauto using EqStrel_Reflexive.
      - intros * Eq1 Eq2 Var. rewrite <-Eq1, <-Eq2; auto.
      - eauto using sem_var_det.
    Qed.

    Lemma ps_equal_Forall2_bools :
      forall H xs ys vs vs' rs rs',
        PS.Equal xs (PSP.of_list ys) ->
        Forall2 (sem_var H) (PSP.to_list xs) vs ->
        Forall2 (sem_var H) ys vs' ->
        bools_ofs vs rs ->
        bools_ofs vs' rs' ->
        rs ≡ rs'.
    Proof.
      intros * Eq Vars Vars' Bools Bools'.
      assert (SameElements eq (PSP.to_list xs) ys) as Same.
      { eapply SE_trans. eapply SE_perm, PS_elements_Equal; eauto.
        symmetry. eapply ps_of_list_ps_to_list_SameElements. }
      eapply Forall2_SameElements_1 in Vars as (vs''&Same'&Vars); eauto.
      assert (EqSts vs' vs'') as HEqSts.
      { unfold EqSts. eapply Forall2_swap_args in Vars'. eapply Forall2_trans_ex in Vars; eauto.
        eapply Forall2_impl_In; [|eauto]. intros ?? _ _ (?&?&?&?).
        eapply sem_var_det in H2; eauto. }
      rewrite HEqSts in Bools'. rewrite Same' in Bools.
      eapply bools_ofs_det in Bools'; eauto.
      1,2:eauto using EqStrel_Reflexive.
      - intros * Eq1 Eq2 Var. rewrite <-Eq1, <-Eq2; auto.
      - eauto using sem_var_det.
    Qed.

    Fact init_var_for_clock_sem : forall vars bs H ck xr bs' rs rs' x eqs' st st',
        sem_clock H bs ck bs' ->
        Forall2 (sem_var H) (map fst xr) rs ->
        bools_ofs rs rs' ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars bs H st ->
        init_var_for_clock ck xr st = (x, eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars bs H' st' /\
            sem_var H' x (init_stream bs' rs') /\
            Forall (sem_equation G2 H' bs) eqs').
    Proof with eauto.
      intros * Hsemc Hr Hbools Hvalid Histst Hinit.
      unfold init_var_for_clock in Hinit.
      destruct find_init_var eqn:Hfind.
      - (* We already introduced such an equation previously.
         We will use the hist_st invariant to get some information back about it *)
        inv Hinit.
        exists H. repeat (split; eauto).
        destruct Histst as [_ [Hvalids _]]. unfold init_eqs_valids in Hvalids.
        rewrite Forall_forall in Hvalids.
        eapply st_inits_find_Some in Hfind as (?&Eq&Hfind).
        apply Hvalids in Hfind as (bs''&rs''&rs'''&?&?&?&?); subst.
      eapply sem_clock_det in Hsemc; eauto. rewrite <- Hsemc; auto.
      eapply ps_equal_Forall2_bools in Eq; eauto.
      rewrite <-Eq. assumption.
    - (* We need to introduce a new init equation to the history and state,
         and prove its properties *)
      clear Hfind.
      destruct (fresh_ident _ _) eqn:Hident. repeat inv_bind.
      assert (st_valid_after st' (PSP.of_list (map fst vars))) as Hvalid1 by eauto.
      remember (Env.add x (init_stream bs' rs') H) as H'.
      assert (Env.refines eq H H') as Href1 by (destruct Histst; eapply fresh_ident_refines' in Hident; eauto).
      assert (hist_st vars bs H' st') as Histst1.
      { destruct Histst as [H1 [H2 H3]].
        repeat split.
        - eapply fresh_ident_dom in Hident...
        - unfold init_eqs_valids in *.
          erewrite fresh_ident_true_st_inits...
          constructor.
          + eapply Forall2_bools in Hr as (rs''&?&?); eauto.
            exists bs'. exists rs''. exists rs'. repeat split...
            * eapply LCS.sem_clock_refines; eauto.
            * solve_forall.
              eapply sem_var_refines; eauto.
            * rewrite HeqH'. econstructor. eapply Env.add_1.
              1,2:reflexivity.
          + solve_forall.
            destruct H2 as [bs'' [rs'' [rs''' [? [? [? ?]]]]]].
            exists bs''. exists rs''. exists rs'''. repeat split; eauto.
            * eapply LCS.sem_clock_refines; eauto.
            * solve_forall.
              eapply sem_var_refines; eauto.
            * eapply sem_var_refines; eauto.
        - unfold st_clocks', LCS.sc_var_inv' in *.
          erewrite fresh_ident_anns; simpl; eauto.
          rewrite <- Permutation_middle; constructor; simpl.
          + exists (init_stream bs' rs'). split.
            * rewrite HeqH'. econstructor.
              eapply Env.add_1. 1,2:reflexivity.
            * rewrite init_stream_ac.
              eapply LCS.sem_clock_refines; eauto.
          + eapply Forall_impl; eauto. intros [? ?] [ss [? ?]].
            exists ss. split; [eapply sem_var_refines|eapply LCS.sem_clock_refines]; eauto.
      }
      assert (st_valid_after st' (PSP.of_list (map fst vars))) as Hvalid2 by eauto.
      exists H'. repeat (split; eauto).
      + rewrite HeqH'. econstructor. 2:reflexivity.
        apply Env.add_1. reflexivity.
      + repeat constructor.
        apply Seq with (ss:=[[(init_stream bs' rs')]]); simpl; repeat constructor.
        * econstructor; repeat constructor.
          1,2:apply add_whens_enum_sem_exp; eauto using LCS.sem_clock_refines.
          -- rewrite Forall2_map_1. rewrite Forall2_map_1 in Hr. eapply Forall2_impl_In; [|eauto].
             intros (?&?) ? _ _ ?. econstructor. eapply sem_var_refines; eauto.
          -- eauto.
          -- repeat constructor. unfold init_stream.
             repeat rewrite const_val_const; subst.
             do 2 rewrite const_val_enum. apply sfby_reset_fby1; simpl; eauto.
             rewrite <- const_val_enum. apply enum_aligned.
        * econstructor. 2:reflexivity.
          rewrite HeqH'. apply Env.add_1. reflexivity.
    Qed.

    Hypothesis Hiface : global_iface_eq G1 G2.
    Hypothesis HGref : LCS.global_sc_refines G1 G2.

    Hypothesis HwcG1 : wc_global G1.
    Hypothesis HscG1 : LCS.sc_nodes G1.

    Lemma sc_ref_sem_exp : forall H b vars e vs,
        NoDupMembers vars ->
        normalized_lexp e ->
        wc_exp G1 vars e ->
        LCS.sc_var_inv' vars H b ->
        sem_exp G1 H b e vs ->
        sem_exp G2 H b e vs.
    Proof.
      intros * Hnd Hnormed Hwc Hsc Hsem.
      eapply normalized_lexp_sem_sem_anon in Hsem; eauto.
      eapply LCS.sem_exp_anon_sem_exp.
      eapply LCS.sc_ref_sem_exp; eauto.
    Qed.

    Fact fby_iteexp_sem : forall vars bs H e0 e xr ty nck y0 y rs r z e' eqs' st st' ,
        NoDupMembers vars ->
        wc_env (idck vars++st_clocks' st) ->
        normalized_lexp e0 ->
        normalized_lexp e ->
        clockof e0 = [fst nck] ->
        wt_exp G1 (idty vars++st_tys' st) e0 ->
        wc_exp G1 (idck vars++st_clocks' st) e0 ->
        wc_exp G1 (idck vars++st_clocks' st) e ->
        sem_exp G1 H bs e0 [y0] ->
        sem_exp G1 H bs e [y] ->
        Forall2 (sem_var H) (map fst xr) rs ->
        bools_ofs rs r ->
        fby y0 y r z ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st (idck vars) bs H st ->
        fby_iteexp e0 e xr (ty, nck) st = (e', eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st (idck vars) bs H' st' /\
            sem_exp G2 H' bs e' [z] /\
            Forall (sem_equation G2 H' bs) eqs').
    Proof with eauto.
      intros * Hndup Hwenv Hnormed0 Hnormed Hck Hwt Hwc0 Hwc Hsem0 Hsem Hsr Hbools Hfby Hvalid Histst Hiteexp.
      assert (st_follows st st') as Hfollows by (eapply fby_iteexp_st_follows; eauto).
      destruct nck as [ck ?]; simpl in *.
      unfold fby_iteexp in Hiteexp; repeat inv_bind.
      assert (Hsck:=Hnormed0). eapply sc_lexp with (env:=vars++st_vars st) in Hsck...
      3,6:rewrite idck_app... 4:rewrite idty_app...
      2:{ eapply st_valid_after_NoDupMembers in Hvalid... }
      2:{ destruct Histst as [_ [_ ?]]. rewrite idck_app, <- st_clocks'_st_vars; auto. }
      eapply init_var_for_clock_sem in H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]...
      2:rewrite map_fst_idck...
      remember (abstract_clock y0) as bs'.
      remember (match ty with Tprimitive cty => Vscalar (Op.sem_cconst (Op.init_ctype cty))
                         | Tenum (_, n) => Venum 0 end) as v0.
      remember (sfby_reset v0 y (Streams.const false) v0) as y'.
      remember (Env.add x2 y' H') as H''.
      assert (Env.refines eq H' H'') by (destruct Histst1; eapply fresh_ident_refines' in H1; eauto).
      assert (hist_st (idck vars) bs H'' st') as Histst2.
      { eapply fresh_ident_hist_st in H1; eauto.
        rewrite HeqH''...
        rewrite Heqy', ac_sfby_reset.
        1: eapply LCS.sem_clock_refines; eauto.
        rewrite ac_fby2, <- ac_fby1, <- Heqbs'; eauto. }
      exists H''. repeat (split; eauto); try constructor.
      - etransitivity; eauto.
      - rewrite map_fst_idck in Hvalid1...
      - eapply Scase with (s:=(init_stream bs' r)) (vs:=[[[y']];[[y0]]]) (vd:=[[y']]). 2:repeat constructor.
        + econstructor. eapply sem_var_refines...
        + intros ? Heq; inv Heq.
        + intros ? Heq; inv Heq. repeat constructor.
          eapply sc_ref_sem_exp with (vars:=idck vars++st_clocks' st')...
          * rewrite st_clocks'_st_vars, <-idck_app, NoDupMembers_idck.
            eapply st_valid_after_NoDupMembers, fresh_ident_st_valid; eauto.
            now rewrite map_fst_idck in Hvalid1.
          * unfold st_clocks' in *. repeat solve_incl.
          * destruct Histst2 as (_&_&?); auto.
          * eapply sem_exp_refines; [| eauto]; etransitivity...
        + constructor; [|constructor]; auto; intros; try congruence.
          constructor; auto. constructor; auto. reflexivity.
        + do 2 (constructor; auto).
          rewrite HeqH''. econstructor. eapply Env.add_1. 1,2:reflexivity.
        + repeat econstructor; eauto.
          subst. eapply fby_init_stream_case; eauto using ac_aligned.
      - apply Seq with (ss:=[[y']]); repeat constructor.
        + eapply Sfby with (s0ss:=[[const_val bs' v0]]) (sss:=[[y]]); repeat constructor.
          * destruct ty as [|(?&?)]; simpl; rewrite Heqv0.
            -- rewrite <-const_val_const. eapply add_whens_const_sem_exp.
               eapply LCS.sem_clock_refines; [|eauto]. etransitivity...
            -- rewrite <-const_val_enum. eapply add_whens_enum_sem_exp.
               eapply LCS.sem_clock_refines; [|eauto]. etransitivity...
          * eapply sc_ref_sem_exp with (vars:=idck vars++st_clocks' st')...
            -- rewrite st_clocks'_st_vars, <-idck_app, NoDupMembers_idck.
               eapply st_valid_after_NoDupMembers, fresh_ident_st_valid; eauto.
               now rewrite map_fst_idck in Hvalid1.
            -- unfold st_clocks' in *. repeat solve_incl.
            -- destruct Histst2 as (_&_&?); auto.
            -- eapply sem_exp_refines; [| eauto]; etransitivity...
          * eapply bools_ofs_empty.
          * rewrite Heqy'.
            eapply sfby_reset_fby1.
            eapply fby_aligned in Hfby as [_ [? _]]; eauto.
            left. rewrite Heqbs'. apply ac_aligned. simpl; auto.
        + econstructor.
          rewrite HeqH''. apply Env.add_1. 1,2:reflexivity.
      - solve_forall. eapply sem_equation_refines...
    Qed.

    Fact arrow_iteexp_sem : forall vars bs H e0 e xr ty nck y0 y rs r z e' eqs' st st',
        NoDupMembers vars ->
        wc_env (idck vars++st_clocks' st) ->
        normalized_lexp e0 ->
        normalized_lexp e ->
        clockof e0 = [fst nck] ->
        wt_exp G1 (idty vars++st_tys' st) e0 ->
        wc_exp G1 (idck vars++st_clocks' st) e0 ->
        wc_exp G1 (idck vars++st_clocks' st) e ->
        sem_exp G1 H bs e0 [y0] ->
        sem_exp G1 H bs e [y] ->
        Forall2 (sem_var H) (map fst xr) rs ->
        bools_ofs rs r ->
        arrow y0 y r z ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st (idck vars) bs H st ->
        arrow_iteexp e0 e xr (ty, nck) st = (e', eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st (idck vars) bs H' st' /\
            sem_exp G2 H' bs e' [z] /\
            Forall (sem_equation G2 H' bs) eqs').
    Proof with eauto.
      intros * Hndup Hwenv Hnormed0 Hnormed1 Hck Hwt Hwc0 Hwc1 Hsem0 Hsem Hr Hbools Harrow Hvalid Histst Hiteexp.
      assert (st_follows st st') as Hfollows by (eapply arrow_iteexp_st_follows; eauto).
      destruct nck as [ck ?]; simpl in *.
      unfold arrow_iteexp in Hiteexp. repeat inv_bind.
      assert (Hsc0:=Hnormed0). eapply sc_lexp with (env:=vars++st_vars st) in Hsc0...
      3,6:rewrite idck_app... 4:rewrite idty_app...
      2:{ eapply st_valid_after_NoDupMembers in Hvalid... }
      2:{ destruct Histst as [_ [_ ?]]. rewrite idck_app, <- st_clocks'_st_vars; auto. }

      eapply init_var_for_clock_sem in H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]...
      2:rewrite map_fst_idck...
      remember (abstract_clock y0) as bs'.
      exists H'. repeat (split; auto).
      + rewrite map_fst_idck in Hvalid1...
      + eapply Scase with (s:=(init_stream bs' r)) (vs:=[[[y]];[[y0]]]) (vd:=[[y]]). 2:repeat constructor.
        * econstructor; eauto.
        * intros ? Heq; inv Heq.
        * intros ? Heq; inv Heq. repeat constructor.
         eapply sc_ref_sem_exp with (vars:=idck vars++st_clocks' st')...
          -- rewrite st_clocks'_st_vars, <-idck_app, NoDupMembers_idck.
             eapply st_valid_after_NoDupMembers; eauto.
             now rewrite map_fst_idck in Hvalid1.
          -- unfold st_clocks' in *. repeat solve_incl.
          -- destruct Histst1 as (_&_&?); auto.
         -- eapply sem_exp_refines...
        * do 2 (constructor; auto). 2:intros Heq; inv Heq.
          constructor; auto. reflexivity.
        * constructor; auto.
          eapply sc_ref_sem_exp with (vars:=idck vars++st_clocks' st')...
          -- rewrite st_clocks'_st_vars, <-idck_app, NoDupMembers_idck.
             eapply st_valid_after_NoDupMembers; eauto.
             now rewrite map_fst_idck in Hvalid1.
          -- unfold st_clocks' in *. repeat solve_incl.
          -- destruct Histst1 as (_&_&?); auto.
          -- eapply sem_exp_refines...
        * subst. repeat econstructor. eapply arrow_init_stream_case...
          left. apply ac_aligned.
    Qed.

    Fact fby_equation_sc_exp : forall H vars bs e0 ck s0s ss r vs,
        NoDupMembers vars ->
        wc_env (idck vars) ->
        normalized_lexp e0 ->
        wt_exp G1 (idty vars) e0 ->
        wc_exp G1 (idck vars) e0 ->
        clockof e0 = [ck] ->
        sem_exp G1 H bs e0 [s0s] ->
        fby s0s ss r vs ->
        LCS.sc_var_inv' (idck vars) H bs ->
        sem_clock H bs ck (abstract_clock vs).
    Proof with eauto.
      intros * Hndup Hwenv Hnormed Hwt Hwc Hck Hsem Hfby Hinv.
      eapply sc_lexp in Hnormed. 2-10:eauto.
      rewrite ac_fby1 in Hnormed; eauto.
    Qed.

    Fact fby_equation_sem : forall vars bs H to_cut equ eqs' st st' ,
        NoDupMembers vars ->
        wc_env (idck vars++st_clocks' st) ->
        unnested_equation G1 equ ->
        wt_equation G1 (idty vars++st_tys' st) equ ->
        wc_equation G1 (idck vars++st_clocks' st) equ ->
        sem_equation G1 H bs equ ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st (idck vars) bs H st ->
        fby_equation to_cut equ st = (eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st (idck vars) bs H' st' /\
            Forall (sem_equation G2 H' bs) eqs').
    Proof with eauto.
      intros * Hndup Hwcenv Hunt Hwt Hwc Hsem Hvalid Histst Hfby.
      inv_fby_equation Hfby to_cut equ; try destruct x3 as (ty&ck&name).
      - (* constant fby *)
        destruct PS.mem; repeat inv_bind.
        + inv Hsem. inv H6; inv H5.
          simpl in H7; rewrite app_nil_r in H7. inv H7; inv H6.
          assert(Hsem':=H3). inversion_clear H3 as [| | | | |??????????? Hsem0 Hsem1 Hsemr Bools Hsem| | | | |].
          inv Hsem0; inv H6. inv Hsem1; inv H7.
          simpl in Hsem; repeat rewrite app_nil_r in Hsem. inv Hsem; inv H9.
          destruct Hwt as [Hwt _]. apply Forall_singl in Hwt. inv Hwt. apply Forall_singl in H9.
          destruct Hwc as [Hwc _]. apply Forall_singl in Hwc. assert (Hwc':=Hwc). inv Hwc'.
          apply Forall_singl in H16. rewrite Forall2_eq in H19; simpl in H19; rewrite app_nil_r in H19.

          remember (Env.add x3 y0 H) as H'.
          assert (Env.refines eq H H') as Href.
          { destruct Histst as [Hdom _]; rewrite map_fst_idck in Hdom.
            eapply fresh_ident_refines' in H0... }
          assert (hist_st (idck vars) bs H' st') as Histst1.
          { eapply fresh_ident_hist_st in H0...
            + rewrite HeqH'...
            + rewrite map_fst_idck...
            + eapply fby_equation_sc_exp with (vars:=vars++st_vars st) (e0:=x0)...
              * eapply st_valid_after_NoDupMembers in Hvalid...
              * rewrite idck_app; eauto.
              * clear - Hunt. inv Hunt; auto. inv H0; inv H.
              * rewrite idty_app. rewrite st_tys'_st_vars in *; auto.
              * rewrite idck_app. rewrite st_clocks'_st_vars in *; auto.
              * destruct Histst as [_ [_ ?]]. rewrite idck_app, <- st_clocks'_st_vars...
          }
          exists H'. repeat (split; eauto).
          repeat constructor; auto.
          * eapply Seq with (ss:=[[y0]]); simpl; repeat constructor.
            2:eapply sem_var_refines; eauto.
            rewrite HeqH'. econstructor. eapply Env.add_1. 1,2:reflexivity.
          * eapply Seq with (ss:=[[y0]]); simpl; repeat constructor.
            { eapply LCS.sem_exp_anon_sem_exp.
              destruct Histst1 as (_&_&?); eauto.
              eapply LCS.sc_ref_sem_exp with (vars0:=idck vars++st_clocks' st'); eauto.
              - rewrite st_clocks'_st_vars, <-idck_app, NoDupMembers_idck.
                eapply st_valid_after_NoDupMembers; eauto.
              - unfold st_clocks' in *. repeat solve_incl.
              - econstructor. 4:eauto. 1,2:econstructor; eauto.
                4:simpl; repeat rewrite app_nil_r; econstructor; eauto. 4:econstructor.
                1,2:eapply normalized_lexp_sem_sem_anon; eauto. 2,4:eapply sem_exp_refines; eauto.
                1,2:(clear - Hunt; inv Hunt; auto; inv H0; inv H).
                eapply Forall2_impl_In; [|eauto]. intros ?? Hin1 _ ?.
                eapply normalized_lexp_sem_sem_anon; eauto. 2:eapply sem_exp_refines; eauto.
                clear - Hunt Hin1.
                inv Hunt. 2:inv H0; inv H.
                eapply Forall_forall in H6 as (?&?&?); eauto.
                subst. destruct x4; auto.
            }
            rewrite HeqH'. econstructor. eapply Env.add_1. 1,2:reflexivity.
        + exists H. repeat (split; eauto).
          constructor; auto.
          { eapply unnested_equation_sem_sem_anon in Hsem; eauto.
            eapply LCS.sem_equation_anon_sem_equation.
            eapply LCS.sc_ref_sem_equation; eauto.
            - rewrite st_clocks'_st_vars, <-idck_app, NoDupMembers_idck.
              eapply st_valid_after_NoDupMembers; eauto.
            - destruct Histst as (?&?&?); auto.
          }
      - (* fby *)
        destruct Hwt as [Hwt _]. apply Forall_singl in Hwt. inv Hwt. apply Forall_singl in H5.
        destruct Hwc as [Hwc _]. apply Forall_singl in Hwc. inv Hwc.
        apply Forall_singl in H12. rewrite Forall2_eq in H15; simpl in H15; rewrite app_nil_r in H15.
        inv Hsem. inv H20; inv H19. simpl in H21; rewrite app_nil_r in H21. inv H21; inv H20.
        inversion_clear H3 as [| | | | |??????????? Hsem0 Hsem1 Hsemr Bools Hsem| | | | |].
        inv Hsem0; inv H20. inv Hsem1; inv H21.
        simpl in Hsem; repeat rewrite app_nil_r in Hsem. inv Hsem; inv H23.
        assert (normalized_lexp x0).
        { clear - Hunt. inv Hunt; eauto. inv H0; inv H. }
        assert (normalized_lexp x1).
        { clear - Hunt. inv Hunt; eauto. inv H0; inv H. }
        eapply fby_iteexp_sem with (nck:=(ck, name)) in H0 as [H' [Href1 [Hvalid1 [Hhistst1 [Hsem' Hsem'']]]]]...
        2:{ inv H13; auto. }
        2:{ clear - Hr Hsemr.
            rewrite Forall2_swap_args in Hr.
            eapply Forall2_trans_ex in Hsemr; eauto.
            rewrite Forall2_map_1. eapply Forall2_impl_In; eauto.
            intros (?&?) ? _ _ (?&?&(?&?)&?); subst. inv H2; auto. }
        exists H'. repeat (split; eauto).
        constructor; auto.
        eapply Seq with (ss:=[[y0]]); simpl; repeat constructor; auto.
        eapply sem_var_refines; eauto.
      - (* arrow *)
        destruct Hwt as [Hwt _]. apply Forall_singl in Hwt. inv Hwt. apply Forall_singl in H5.
        destruct Hwc as [Hwc _]. apply Forall_singl in Hwc. inv Hwc.
        apply Forall_singl in H12. rewrite Forall2_eq in H15; simpl in H15; rewrite app_nil_r in H15.
        inv Hsem. inv H20; inv H19. simpl in H21; rewrite app_nil_r in H21. inv H21; inv H20.
        inversion_clear H3 as [| | | | | |??????????? Hsem0 Hsem1 Hsemr Bools Hsem| | | |].
        inv Hsem0; inv H20. inv Hsem1; inv H21.
        simpl in Hsem; repeat rewrite app_nil_r in Hsem. inv Hsem; inv H23.
        assert (normalized_lexp x0).
        { clear - Hunt. inv Hunt; eauto. inv H0; inv H. }
        assert (normalized_lexp x1).
        { clear - Hunt. inv Hunt; eauto. inv H0; inv H. }
        eapply arrow_iteexp_sem with (nck:=(ck, name)) in H0 as [H' [Href1 [Hvalid1 [Hhistst1 [Hsem' Hsem'']]]]]...
        2:{ inv H13; auto. }
        2:{ clear - Hr Hsemr.
            rewrite Forall2_swap_args in Hr.
            eapply Forall2_trans_ex in Hsemr; eauto.
            rewrite Forall2_map_1. eapply Forall2_impl_In; eauto.
            intros (?&?) ? _ _ (?&?&(?&?)&?); subst. inv H2; auto. }
        exists H'. repeat (split; eauto).
        constructor; auto.
        eapply Seq with (ss:=[[y0]]); simpl; repeat constructor; auto.
        eapply sem_var_refines; eauto.
      - (* other *)
        exists H. repeat (split; eauto).
        constructor; auto.
        { eapply unnested_equation_sem_sem_anon in Hsem; eauto.
            eapply LCS.sem_equation_anon_sem_equation.
            eapply LCS.sc_ref_sem_equation; eauto.
            - rewrite st_clocks'_st_vars, <-idck_app, NoDupMembers_idck.
              eapply st_valid_after_NoDupMembers; eauto.
            - destruct Histst as (?&?&?); auto.
        }
    Qed.

    Fact fby_equations_sem : forall vars bs to_cut eqs eqs' H st st' ,
        NoDupMembers vars ->
        wc_env (idck vars++st_clocks' st) ->
        Forall (unnested_equation G1) eqs ->
        Forall (wt_equation G1 (idty vars++st_tys' st)) eqs ->
        Forall (wc_equation G1 (idck vars++st_clocks' st)) eqs ->
        Forall (sem_equation G1 H bs) eqs ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st (idck vars) bs H st ->
        fby_equations to_cut eqs st = (eqs', st') ->
        (exists H',
            Env.refines eq H H' /\
            Forall (sem_equation G2 H' bs) eqs').
    Proof with eauto.
      induction eqs; intros * Hndup Hwcenv Hunt Hwt Hwc Hsem Hvalid Hhistst Hfby;
        unfold fby_equations in Hfby; simpl in *; repeat inv_bind.
      - exists H; simpl...
      - assert (fby_equations to_cut eqs x1 = (concat x2, st')) as Hnorm.
        { unfold fby_equations; repeat inv_bind.
          repeat eexists; eauto. repeat inv_bind; auto. }
        inv Hunt. inv Hwt. inv Hwc. inv Hsem.
        assert (st_follows st x1) as Hfollows by (eapply fby_equation_st_follows in H0; eauto).
        assert (wc_env (idck vars ++ st_clocks' x1)) as Hwenv1.
        { eapply fby_equation_wc_eq in H0 as [_ ?]... }
        eapply fby_equation_sem in H0 as [H' [Href1 [Hvalid1 [Hhistst1 Hsem1]]]]. 2-11:eauto.
        assert (Forall (sem_equation G1 H' bs) eqs) as Hsem'.
        { solve_forall. eapply sem_equation_refines... } clear H11.
        eapply IHeqs in Hnorm as [H'' [Href Hsem2]]. 2-11:eauto.
        2,3:solve_forall; repeat solve_incl.
        + exists H''. split.
          * etransitivity...
          * simpl. apply Forall_app; split; eauto.
            solve_forall. eapply sem_equation_refines...
        + repeat rewrite st_tys'_st_vars. solve_incl.
          eapply st_follows_vars_incl...
        + repeat rewrite st_clocks'_st_vars. solve_incl.
          eapply st_follows_vars_incl...
    Qed.

    Fact init_st_hist_st {prefs} : forall b H (n: @node prefs),
        Env.dom H (List.map fst (n_in n++n_vars n++n_out n)) ->
        LCS.sc_var_inv' (idck (n_in n++n_vars n++n_out n)) H b ->
        hist_st (idck (n_in n++n_vars n++n_out n)) b H init_st.
    Proof.
      intros b H n Hdom Hinv.
      repeat constructor.
      - unfold st_ids.
        rewrite init_st_anns; simpl.
        rewrite app_nil_r, map_fst_idck. assumption.
      - unfold init_eqs_valids, st_inits.
        rewrite init_st_anns. constructor.
      - unfold st_clocks'. rewrite init_st_anns; simpl.
        rewrite app_nil_r. assumption.
    Qed.

    Fact normfby_node_sem_equation : forall H n ins,
        unnested_node G1 n ->
        wt_node G1 n ->
        wc_node G1 n ->
        LCA.node_causal n ->
        Env.dom H (map fst (n_in n ++ n_vars n ++ n_out n)) ->
        Forall2 (sem_var H) (idents (n_in n)) ins ->
        Forall2 (fun xc => sem_clock H (clocks_of ins) (snd xc)) (idck (n_in n)) (map abstract_clock ins) ->
        Forall (sem_equation G1 H (clocks_of ins)) (n_eqs n) ->
        exists H' : Env.t (Stream svalue),
          Env.refines eq H H' /\ Forall (sem_equation G2 H' (clocks_of ins)) (n_eqs (normfby_node n)).
    Proof with eauto.
      intros * Hunt Hwt Hwc Hcaus Hdom Hvars Hsemclock Hsem.
      assert (NoDup (map fst (n_in n ++ n_vars n ++ n_out n))) as Hndup.
      { specialize (n_nodup n) as Hndup; rewrite fst_NoDupMembers in Hndup.
        repeat rewrite map_app in Hndup. repeat rewrite app_assoc in Hndup. apply NoDup_app_l in Hndup.
        repeat rewrite <- app_assoc in Hndup. repeat rewrite <- map_app in Hndup... }
      eapply fby_equations_sem with (vars:=(n_in n++n_vars n++n_out n)) (eqs:=n_eqs n) (st:=init_st)...
      7: simpl; rewrite <- surjective_pairing; subst; reflexivity.
      3:rewrite st_tys'_st_vars. 2,4:rewrite st_clocks'_st_vars.
      2,3,4:unfold st_vars; rewrite init_st_anns, app_nil_r.
      - rewrite fst_NoDupMembers...
      - destruct Hwc as [_ [_ [? _]]].
        rewrite (Permutation_app_comm (n_vars _))...
      - destruct Hwc as [_ [_ [_ ?]]]...
      - destruct Hwt as [_ [_ [_ [_ ?]]]]...
      - eapply init_st_valid.
        + eapply norm2_not_in_norm1_prefs.
        + rewrite PS_For_all_Forall, ps_of_list_ps_to_list_Perm...
          pose proof (n_good n) as (Good&_).
          eapply Forall_incl; eauto.
          apply incl_map, incl_appr', incl_appr', incl_appl; auto.
      - subst. eapply init_st_hist_st...
        eapply LCS.sc_node_sc_var_inv'; eauto.
        + eapply Forall_impl_In; [|eauto]. intros.
          unfold unnested_node in Hunt.
          destruct Hwc as (_&_&_&Hwc).
          eapply unnested_equation_sem_sem_anon; eauto. 1,2:eapply Forall_forall; eauto.
    Qed.

  End normfby_node_sem.

  Lemma normfby_node_eq : forall G1 G2 f n ins outs,
      Forall2 (fun n n' => n_name n = n_name n') G1.(nodes) G2.(nodes) ->
      global_iface_eq G1 G2 ->
      LCS.global_sc_refines G1 G2 ->
      unnested_global (Global G1.(enums) (n::G1.(nodes))) ->
      wt_global (Global G1.(enums) (n::G1.(nodes))) ->
      wc_global (Global G1.(enums) (n::G1.(nodes))) ->
      wt_global G2 ->
      wc_global G2 ->
      Ordered_nodes (Global G1.(enums) (n::G1.(nodes))) ->
      Ordered_nodes (Global G2.(enums) ((normfby_node n)::G2.(nodes))) ->
      Forall LCA.node_causal (n::G1.(nodes)) ->
      Forall LCA.node_causal G2.(nodes) ->
      sem_node (Global G1.(enums) (n::G1.(nodes))) f ins outs ->
      LCS.sem_clock_inputs (Global G1.(enums) (n::G1.(nodes))) f ins ->
      sem_node (Global G2.(enums) ((normfby_node n)::G2.(nodes))) f ins outs.
  Proof with eauto.
    intros * Hnames Hiface Href Hunt HwtG HwcG HwtG' HwcG' Hord1 Hord2 Hcaus1 Hcaus2 Hsem Hinputs.
    assert (LCS.sc_nodes G1) as HscG1.
    { destruct HwtG as (_&HwtG). inversion_clear HwtG as [|?? (?&?)]. inversion_clear HwcG as [|?? (?&?)].
      inv Hord1. inv Hcaus1.
      eapply LCS.l_sem_node_clock... }
    assert (LCS.sc_nodes G2) as HscG2.
    { eapply LCS.l_sem_node_clock... }
    assert (Forall (fun n' => exists v, In v G1.(nodes) /\ n_name n <> n_name n') G2.(nodes)) as Hnames'.
    { assert (length G1.(nodes) = length G2.(nodes)) by (eapply Forall2_length in Hnames; eauto).
      destruct HwtG as (_&HwtG). inversion_clear HwtG as [|?? (?&?)]. eapply Forall2_ignore1. solve_forall. }
    assert (Ordered_nodes (Global G2.(enums) (normfby_node n :: G2.(nodes)))) as Hord'.
    { inv Hord2. destruct H1. constructor; [split|]... }

    inv Hsem; assert (Hfind:=H0). destruct (ident_eq_dec (n_name n) f).
    - erewrite find_node_now in H0; eauto. inv H0.
      inversion_clear HwcG as [|?? (?&?)].
      (* The semantics of equations can be given according to G only *)
      eapply Forall_sem_equation_global_tl in H3; eauto.
      2:{ inv Hord1. intro contra. apply H8 in contra as [? _]; auto. }
      (* New env H' (restrict H) and its properties *)
      eapply LCS.sem_node_restrict in H3 as (Hdom&Hins'&Houts'&Heqs'); eauto.
      2:destruct H0 as (?&?&?&?); auto.
      remember (Env.restrict H (List.map fst (n_in n0++n_vars n0++n_out n0))) as H'.
      clear H1 H2 HeqH'.

      destruct HwtG as (_&HwtG). inversion_clear HwtG as [|?? (?&?)]. rename H1 into Hwt.
      inv Hcaus1.

      eapply normfby_node_sem_equation in Heqs' as (H''&Hre'&Heqs'')...
      assert (Forall2 (sem_var H'') (idents (n_in n0)) ins) as Hins''.
      { repeat rewrite_Forall_forall. eapply sem_var_refines... }
      eapply Snode with (H1:=H''); simpl. 5:reflexivity.
      + erewrite find_node_now; eauto.
      + simpl; eauto.
      + simpl. repeat rewrite_Forall_forall. eapply sem_var_refines...
      + clear Hins' Houts' Hdom.
        apply Forall_sem_equation_global_tl'...
        eapply find_node_not_Is_node_in in Hord2...
        erewrite find_node_now; eauto.
        assert (normalized_node G2 (normfby_node n0)) as Hunt'.
        { inversion_clear Hunt as [|?? (?&?)]; simpl in *.
          eapply normfby_node_normalized_node, iface_eq_unnested_node; destruct G1; eauto.
        }
        assert (wc_node G2 (normfby_node n0)) as Hwc'.
        { inversion_clear Hunt as [|?? (?&?)]; simpl in *.
          eapply normfby_node_wc; eauto; destruct G1; eauto. }
        assert (Forall (LCS.sem_equation_anon G2 H'' (clocks_of ins)) (n_eqs (normfby_node n0))) as Heqs'''.
        { eapply Forall_impl_In; [|eapply Heqs''].
          intros. eapply normalized_equation_sem_sem_anon; eauto.
          eapply Forall_forall in Hunt'; eauto.
          destruct Hwc' as (_&_&_&Hwc'). eapply Forall_forall in Hwc'; eauto.
        } clear Heqs''.
        assert (LCS.sc_var_inv' (idck (n_in (normfby_node n0) ++ n_vars (normfby_node n0) ++ n_out (normfby_node n0))) H'' (clocks_of ins)) as Hinv.
        { destruct Hinputs as (H'''&?&Hfind'&?&Hcks).
          rewrite Hfind in Hfind'; inv Hfind'.
          eapply LCS.sc_node_sc_var_inv'; [|eauto| | | | |]; eauto.
          + inversion_clear Hunt as [|?? (?&?)]; simpl in *.
            eapply normfby_node_causal; eauto; simpl; destruct G1; eauto.
          + eapply LCS.sem_clocks_det' in Hcks; eauto. destruct H0; auto.
        }
        eapply Forall_impl_In; [|eauto]. intros.
        eapply LCS.sem_equation_anon_sem_equation in H6; eauto.
        destruct G2; auto.
      + destruct G1, G2; auto.
      + destruct G1; auto.
      + inversion_clear Hunt as [|?? (?&?)]; auto.
      + destruct Hinputs as (H''&?&?&?&?).
        rewrite H1 in Hfind. inv Hfind.
        destruct H0 as (?&_).
        eapply LCS.sem_clocks_det' in H9; eauto.
    - specialize (Href f ins outs).
      erewrite find_node_other in H0; eauto.
      eapply sem_node_cons'...
      destruct G2; apply Href. split. 1:rewrite <- LCS.sem_clock_inputs_cons in Hinputs...
      econstructor...
      eapply Forall_impl_In; [| eauto]. intros eq Hin Hsem.
      destruct G1; eapply sem_equation_global_tl...
      eapply find_node_later_not_Is_node_in in Hord1...
      intro Hisin. apply Hord1. rewrite Is_node_in_Exists. rewrite Exists_exists.
      eexists...
  Qed.

  Fact iface_eq_sem_clocks_input {prefs1 prefs2} :
    forall (G1: @global prefs1) (G2: @global prefs2) f ins,
      global_iface_eq G1 G2 ->
      LCS.sem_clock_inputs G1 f ins ->
      LCS.sem_clock_inputs G2 f ins.
  Proof.
    intros * (_&Hglob) [H [n [Hfind [Hinputs Hsem]]]].
    specialize (Hglob f). rewrite Hfind in Hglob; inv Hglob.
    destruct H2 as (Hname&_&Hins&_).
    exists H. exists sy. repeat split; auto; congruence.
  Qed.

  Fact normfby_global_names' : forall nds,
      Forall2 (fun n n' => n_name n = n_name n') nds (map normfby_node nds).
  Proof.
    induction nds; simpl; auto.
  Qed.

  Lemma normfby_global_refines : forall G,
      unnested_global G ->
      wt_global G ->
      wc_global G ->
      Forall LCA.node_causal G.(nodes) ->
      LCS.global_sc_refines G (normfby_global G).
  Proof with eauto.
    intros (enms&nds).
    induction nds; intros * Hunt Hwt Hwc Hcaus; simpl.
    - apply LCS.global_sc_ref_nil.
    - apply LCS.global_sc_ref_cons with (f:=n_name a)...
      + eapply normfby_global_wt, wt_global_Ordered_nodes in Hwt;
          unfold normfby_global in Hwt; simpl in Hwt...
      + inv Hunt; destruct Hwt as (?&Hwt); inv Hwt; inv Hwc; inv Hcaus.
        eapply IHnds... split; auto.
      + intros ins outs Hsem. destruct Hsem as [Hinputs Hsem]. split; simpl in *.
        * eapply iface_eq_sem_clocks_input... eapply normfby_global_eq.
        * replace enms with (normfby_global (Global enms nds)).(enums) by auto.
          eapply normfby_node_eq with (G1:=Global enms nds); simpl...
          -- apply normfby_global_names'.
          -- apply normfby_global_eq.
          -- inv Hunt; destruct Hwt as (?&Hwt); inv Hwt; inv Hwc; inv Hcaus.
             eapply IHnds... split; auto.
          -- destruct Hwt as (?&Hwt). inversion_clear Hwt as [|?? (?&?) Hwt']...
             eapply normfby_global_wt... split; auto.
          -- inv Hunt. inversion_clear Hwc as [|?? (?&?) Hwc']...
             eapply normfby_global_wc...
          -- eapply wt_global_Ordered_nodes.
             eapply normfby_global_wt in Hwt...
          -- inv Hwc. inv Hunt. inversion_clear Hcaus as [|?? _ Hcaus'].
             replace nds with (Global enms nds).(nodes) in Hcaus' by auto.
             eapply normfby_global_causal in Hcaus'; simpl in Hcaus'...
  Qed.

  Corollary normfby_global_sem : forall G f ins outs,
      unnested_global G ->
      wt_global G ->
      wc_global G ->
      Ordered_nodes G ->
      Forall LCA.node_causal G.(nodes) ->
      sem_node G f ins outs ->
      LCS.sem_clock_inputs G f ins ->
      sem_node (normfby_global G) f ins outs.
  Proof.
    intros.
    eapply normfby_global_refines in H; eauto.
    specialize (H f ins outs (conj H5 H4)) as [_ ?]; eauto.
  Qed.

  Corollary normfby_global_sem_clock_inputs : forall G f ins,
      LCS.sem_clock_inputs G f ins ->
      LCS.sem_clock_inputs (normfby_global G) f ins.
  Proof.
    intros.
    specialize (normfby_global_eq G) as Heq.
    destruct H as [H [n' [Hfind [Hvars Hsem]]]].
    eapply global_iface_eq_find in Heq as [? [? [Hname [_ [Hin Hout]]]]]; eauto.
    exists H. exists x. repeat split; auto.
    1,2:congruence.
  Qed.

  (** ** Conclusion *)

  Theorem normalize_global_sem : forall G G' f ins outs,
      wt_global G ->
      wc_global G ->
      sem_node G f ins outs ->
      LCS.sem_clock_inputs G f ins ->
      normalize_global G = Errors.OK G' ->
      sem_node G' f ins outs.
  Proof with eauto.
    intros  * Hwt Hwc Hsem Hclocks Hnorm.
    unfold normalize_global in Hnorm. destruct (LCA.check_causality _) eqn:Hcaus; inv Hnorm.
    eapply normfby_global_sem.
    - eapply unnest_global_unnested_global...
    - eapply unnest_global_wt...
    - eapply unnest_global_wc...
    - eapply wt_global_Ordered_nodes, unnest_global_wt; eauto.
    - eapply LCA.check_causality_correct in Hcaus; eauto.
      eapply wt_global_wl_global, unnest_global_wt...
    - eapply unnest_global_sem...
    - eapply unnest_global_sem_clock_inputs...
  Qed.

  Corollary normalize_global_sem_clock_inputs : forall G G' f ins,
      LCS.sem_clock_inputs G f ins ->
      normalize_global G = Errors.OK G' ->
      LCS.sem_clock_inputs G' f ins.
  Proof.
    intros * Hsc Hnorm.
    unfold normalize_global in Hnorm.
    destruct (LCA.check_causality _) eqn:Hcheck; inv Hnorm.
    apply normfby_global_sem_clock_inputs, unnest_global_sem_clock_inputs, Hsc.
  Qed.

  (** ** In addition : normalization only produces causal programs *)

  Lemma normalize_global_causal : forall G G',
      wc_global G ->
      normalize_global G = Errors.OK G' ->
      Forall LCA.node_causal G'.(nodes).
  Proof.
    intros * Hwc Hnorm.
    unfold normalize_global in Hnorm.
    apply Errors.bind_inversion in Hnorm as [? [H1 H2]]. inv H2.
    eapply Causality.normfby_global_causal.
    3:apply LCA.check_causality_correct in H1; eauto.
    eapply unnest_global_unnested_global; eauto.
    1,2:eapply unnest_global_wc in Hwc; eauto.
  Qed.

End CORRECTNESS.

Module CorrectnessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (IStr : INDEXEDSTREAMS Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (LCA : LCAUSALITY Ids Op OpAux Cks Syn)
       (Ty : LTYPING Ids Op OpAux Cks Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (Lord : LORDERED Ids Op OpAux Cks Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Syn Lord CStr)
       (LClockSem : LCLOCKSEMANTICS Ids Op OpAux Cks Syn Clo LCA Lord CStr IStr Sem)
       (Norm : NORMALIZATION Ids Op OpAux Cks Syn LCA)
       <: CORRECTNESS Ids Op OpAux Cks CStr IStr Syn LCA Ty Clo Lord Sem LClockSem Norm.
  Include CORRECTNESS Ids Op OpAux Cks CStr IStr Syn LCA Ty Clo Lord Sem LClockSem Norm.
End CorrectnessFun.
