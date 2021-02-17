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
From Velus Require Import Lustre.Normalization.NCausality Lustre.Normalization.NOrdered.

(** * Correctness of the Normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type CORRECTNESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import CStr : COINDSTREAMS Op OpAux)
       (IStr : INDEXEDSTREAMS Op OpAux)
       (Import Syn : LSYNTAX Ids Op)
       (LCA        : LCAUSALITY Ids Op Syn)
       (Import Ty : LTYPING Ids Op Syn)
       (Import Cl : LCLOCKING Ids Op Syn)
       (Import Ord : LORDERED Ids Op Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Syn Ord CStr)
       (LCS : LCLOCKSEMANTICS Ids Op OpAux Syn Cl LCA Ord CStr IStr Sem)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn LCA).

  Import Fresh Tactics Unnesting.
  Module Import Typing := NTypingFun Ids Op OpAux Syn LCA Ty Norm.
  Module Import Clocking := NClockingFun Ids Op OpAux Syn LCA Cl Norm.
  Module Ordered := NOrderedFun Ids Op OpAux Syn LCA Ord Norm.
  Module Import Causality := NCausalityFun Ids Op OpAux Syn LCA Cl Norm.
  Import List.

  CoFixpoint default_stream : Stream OpAux.value :=
    absent ⋅ default_stream.

  Fact unnest_exp_sem_length : forall G vars e is_control es' eqs' st st',
      wt_exp G (vars++Typing.st_tys st) e ->
      unnest_exp is_control e st = (es', eqs', st') ->
      Forall (fun e => forall v H b,
                  sem_exp G H b e v ->
                  length v = 1) es'.
  Proof.
    intros G vars e is_control es' eqs' st st' Hwt Hnorm.
    specialize (unnest_exp_numstreams _ _ _ _ _ _ Hnorm) as Hnumstreams.
    eapply unnest_exp_wt in Hnorm as [Hwt' _]; eauto.
    repeat rewrite_Forall_forall.
    specialize (Hnumstreams _ H). specialize (Hwt' _ H).
    rewrite <- Hnumstreams.
    eapply sem_exp_numstreams; eauto.
  Qed.

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

  (** ** Conservation of sem_exp *)

  Fact unnest_reset_sem : forall G vars b e H v e' eqs' st st' reusable,
      LiftO True (fun e => forall e' eqs' st',
                   unnest_exp true e st = ([e'], eqs', st') ->
                   exists H',
                     Env.refines eq H H' /\
                     st_valid_reuse st' (PSP.of_list vars) reusable /\
                     Env.dom H' (vars++st_ids st') /\
                     sem_exp G H' b e' [v] /\ Forall (sem_equation G H' b) eqs') e ->
      LiftO True (wl_exp G) e ->
      LiftO True (fun e => numstreams e = 1) e ->
      LiftO True (fun e => sem_exp G H b e [v]) e ->
      st_valid_reuse st (PSP.of_list vars) (ps_adds (match e with None => [] | Some e => map fst (fresh_in e) end) reusable) ->
      Env.dom H (vars++st_ids st) ->
      unnest_reset (unnest_exp true) e st = (e', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list vars) reusable /\
          Env.dom H' (vars++st_ids st') /\
          LiftO True (fun e' => sem_exp G H' b e' [v]) e' /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros * Hun Hwl Hnum Hsem Hvalid Histst Hnorm.
    unnest_reset_spec; simpl in *.
    1,2:assert (length l = 1) by (eapply unnest_exp_length in Hk0; eauto; congruence).
    1,2:singleton_length.
    - eapply Hun in Hk0 as [H' [Href [Hval [Hdom [Hsem1 Hsem2]]]]].
      exists H'. repeat split; eauto.
    - eapply Hun in Hk0 as [H' [Href [Hval [Hdom [Hsem1 Hsem2]]]]].
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
    - exists H. repeat split; auto.
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
    (* | |- incl (st_vars ?st1) (st_vars _) => *)
    (*   eapply st_follows_vars_incl; repeat solve_st_follows *)
    | |- incl (st_tys ?st1) (st_tys _) =>
      eapply st_follows_tys_incl; repeat solve_st_follows
    | |- incl (st_clocks ?st1) (st_clocks _) =>
      eapply st_follows_clocks_incl; repeat solve_st_follows
    end; auto.

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

  Fact unnest_arrow_sem : forall G H bs e0s es anns s0s ss os,
      length e0s = length anns ->
      length es = length anns ->
      Forall2 (fun e s => sem_exp G H bs e [s]) e0s s0s ->
      Forall2 (fun e s => sem_exp G H bs e [s]) es ss ->
      Forall3 arrow s0s ss os ->
      Forall2 (fun e s => sem_exp G H bs e [s]) (unnest_arrow e0s es anns) os.
  Proof with eauto.
    intros * Hlen1 Hlen2 Hsem1 Hsem2 Hfby.
    unfold unnest_arrow.
    repeat rewrite_Forall_forall. 1:solve_length.
    repeat simpl_length. repeat simpl_nth. Unshelve. 2:exact ((hd_default [], hd_default []), default_ann).
    destruct (nth n (combine _ _)) as [[e0 e] ?] eqn:Hnth. repeat simpl_nth.
    eapply Sarrow.
    - repeat constructor...
    - repeat constructor...
    - simpl. repeat constructor...
      Unshelve. 1,2:exact default_stream.
  Qed.

  Fact unnest_fby_sem : forall G H bs e0s es anns s0s ss os,
      length e0s = length anns ->
      length es = length anns ->
      Forall2 (fun e s => sem_exp G H bs e [s]) e0s s0s ->
      Forall2 (fun e s => sem_exp G H bs e [s]) es ss ->
      Forall3 fby s0s ss os ->
      Forall2 (fun e s => sem_exp G H bs e [s]) (unnest_fby e0s es anns) os.
  Proof with eauto.
    intros * Hlen1 Hlen2 Hsem1 Hsem2 Hfby.
    unfold unnest_fby.
    repeat rewrite_Forall_forall. 1:solve_length.
    repeat simpl_length. repeat simpl_nth. Unshelve. 2:exact ((hd_default [], hd_default []), default_ann).
    destruct (nth n (combine _ _)) as [[e0 e] ?] eqn:Hnth. repeat simpl_nth.
    eapply Sfby.
    - repeat constructor...
    - repeat constructor...
    - simpl. repeat constructor...
      Unshelve. 1,2:exact default_stream.
  Qed.

  Fact unnest_when_sem : forall G H bs es tys ckid b ck s ss os,
      length es = length tys ->
      Forall2 (fun e s => sem_exp G H bs e [s]) es ss ->
      sem_var H ckid s ->
      Forall2 (fun s' => when b s' s) ss os ->
      Forall2 (fun e s => sem_exp G H bs e [s]) (unnest_when ckid b es tys ck) os.
  Proof with eauto.
    intros * Hlen Hsem Hvar Hwhen.
    unfold unnest_when. simpl_forall.
    repeat rewrite_Forall_forall. 1:congruence.
    eapply Swhen with (ss:=[[nth n ss default_stream]])...
    - repeat constructor...
      eapply H1... congruence.
  Qed.

  Fact unnest_merge_sem : forall G H bs ets efs tys ckid ck s ts fs os,
      length ets = length tys ->
      length efs = length tys ->
      Forall2 (fun e s => sem_exp G H bs e [s]) ets ts ->
      Forall2 (fun e s => sem_exp G H bs e [s]) efs fs ->
      sem_var H ckid s ->
      Forall3 (merge s) ts fs os ->
      Forall2 (fun e s => sem_exp G H bs e [s]) (unnest_merge ckid ets efs tys ck) os.
  Proof with eauto.
    intros * Hlen1 Hlen2 Hsem1 Hsem2 Hvar Hwhen.
    unfold unnest_merge. simpl_forall.
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

  Fact unnest_ite_sem : forall G H bs e ets efs tys ck s ts fs os,
      length ets = length tys ->
      length efs = length tys ->
      sem_exp G H bs e [s] ->
      Forall2 (fun e s => sem_exp G H bs e [s]) ets ts ->
      Forall2 (fun e s => sem_exp G H bs e [s]) efs fs ->
      Forall3 (ite s) ts fs os ->
      Forall2 (fun e s => sem_exp G H bs e [s]) (unnest_ite e ets efs tys ck) os.
  Proof with eauto.
    intros * Hlen1 Hlen2 Hsem1 Hsem2 Hsem3 Hwhen.
    unfold unnest_ite. simpl_forall.
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

  Fact map_bind2_sem : forall G vars b is_control es H vs es' eqs' st st' reusable,
      NoDup (map fst (fresh_ins es)++PS.elements reusable) ->
      Forall (wl_exp G) es ->
      Forall2 (sem_exp G H b) es vs ->
      st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (fresh_ins es)) reusable) ->
      Env.dom H (vars++st_ids st) ->
      Forall2 (fun e v => forall H es' eqs' st st' reusable,
                   NoDup (map fst (fresh_in e)++PS.elements reusable) ->
                   wl_exp G e ->
                   sem_exp G H b e v ->
                   st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (fresh_in e)) reusable) ->
                   Env.dom H (vars++st_ids st) ->
                   unnest_exp is_control e st = (es', eqs', st') ->
                   (exists H',
                       Env.refines eq H H' /\
                       st_valid_reuse st' (PSP.of_list vars) reusable /\
                       Env.dom H' (vars++st_ids st') /\
                       Forall2 (fun e v => sem_exp G H' b e [v]) es' v /\
                       Forall (sem_equation G H' b) eqs')) es vs ->
      map_bind2 (unnest_exp is_control) es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list vars) reusable /\
          Env.dom H' (vars++st_ids st') /\
          Forall2 (fun es vs => Forall2 (fun e v => sem_exp G H' b e [v]) es vs) es' vs /\
          Forall (sem_equation G H' b) (concat eqs')).
  Proof with eauto.
    induction es; intros * Hndup Hwt Hsem Hvalid Histst Hf Hmap;
      inv Hwt; inv Hsem; inv Hf; repeat inv_bind.
    - exists H; simpl. repeat (split; eauto).
    - unfold fresh_ins in *; simpl in *; rewrite map_app, ps_adds_app in Hvalid.
      assert (NoDup (map fst (fresh_ins es)++PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (fresh_in a) ++ PS.elements (ps_adds (map fst (fresh_ins es)) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
      specialize (H7 _ _ _ _ _ _ Hndup1 H2 H4 Hvalid Histst H0) as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      assert (Forall2 (sem_exp G H' b) es l') as Hsem'.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
      eapply IHes in H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]...
      clear IHes H9.
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

  Hint Constructors sem_exp.
  Fact unnest_exp_sem : forall G vars b e H vs is_control es' eqs' st st' reusable,
      NoDup (map fst (fresh_in e) ++ PS.elements reusable) ->
      wl_exp G e ->
      sem_exp G H b e vs ->
      st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (fresh_in e)) reusable) ->
      Env.dom H (vars++st_ids st) ->
      unnest_exp is_control e st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list vars) reusable /\
          Env.dom H' (vars++st_ids st') /\
          Forall2 (fun e v => sem_exp G H' b e [v]) es' vs /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction e using exp_ind2; intros * Hndup Hwl Hsem Hvalid Histst Hnorm;
      inv Hwl; inv Hsem. 1-10:repeat inv_bind.
    - (* const *)
      exists H. repeat (split; eauto).
    - (* var *)
      exists H. repeat (split; eauto).
    - (* unop *)
      assert (Htypeof:=H0). eapply unnest_exp_typeof in Htypeof...
      specialize (IHe _ _ _ _ _ _ _ _ Hndup H3 H8 Hvalid Histst H0) as [H' [Href1 [Hvalid1 [Hdom1 [Hsem1 Hsem1']]]]].
      eapply unnest_exp_length in H0... rewrite H5 in H0. singleton_length.
      inv Hsem1; clear H7.
      exists H'. repeat (split; eauto).
      repeat econstructor... congruence.
    - (* binop *)
      simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      assert (Htypeof1:=H0). eapply unnest_exp_typeof in Htypeof1...
      assert (Htypeof2:=H1). eapply unnest_exp_typeof in Htypeof2...
      assert (NoDup (map fst (fresh_in e1) ++ PS.elements (ps_adds (map fst (fresh_in e2)) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'. ndup_simpl... ndup_r Hndup. }
      eapply IHe1 in H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]... clear IHe1.
      eapply sem_exp_refines in H12; [| eauto].
      assert (NoDup (map fst (fresh_in e2) ++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      eapply IHe2 in H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]... clear IHe2.
      inv Hsem1. inv Hsem2. inv H4. inv H11.
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
      simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      assert (length (concat x2) = length (annots e0s)) as Hlength1 by (eapply map_bind2_unnest_exp_length; eauto).
      assert (length (concat x6) = length (annots es)) as Hlength2 by (eapply map_bind2_unnest_exp_length; eauto).
      assert (NoDup (map fst (fresh_ins es) ++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (fresh_ins e0s) ++ PS.elements (ps_adds (map fst (concat (map fresh_in es))) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
      assert (Forall (fun e => numstreams e = 1) (concat x2)) as Hnumstreams.
      { eapply map_bind2_unnest_exp_numstreams in H2... }

      assert (length s0ss = length e0s) as Hlen1 by (eapply Forall2_length in H12; eauto).
      assert (H2':=H2). eapply map_bind2_sem in H2... 2:solve_forall. clear H.
      destruct H2 as [H' [Href1 [Histst1 [Hdom1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.

      assert (Forall2 (sem_exp G H' b) es sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
      assert (length sss = length es) as Hlen2 by (eapply Forall2_length in H14; eauto).
      assert (H3':=H3). eapply map_bind2_sem in H3... 2:solve_forall. clear H0.
      destruct H3 as [H'' [Href2 [Hvalid2 [Hdom2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.

      assert (Forall2 (fun (e : exp) (v : Stream OpAux.value) => sem_exp G H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
      specialize (idents_for_anns_length _ _ _ _ H4) as Hlength.
      assert (length vs = length a) as Hlength'''.
      { eapply Forall3_length in H15 as [_ ?]. eapply Forall2_length in Hsem2. congruence. }

      remember (Env.adds (List.map fst x5) vs H'') as H'''.
      assert (length x5 = length vs) as Hlength'''' by (rewrite Hlength, Hlength'''; auto).

      assert (Forall2 (sem_var H''') (map fst x5) vs) as Hsemvars.
      { rewrite HeqH'''. eapply sem_var_adds; eauto.
        + rewrite map_length; auto.
        + eapply idents_for_anns_NoDupMembers in H4; eauto. rewrite <- fst_NoDupMembers; eauto. }

      assert (Env.refines eq H'' H''') as Href4.
      { eapply idents_for_anns_refines in H4... }
      assert (Forall2 (fun e v => sem_exp G H''' b e [v]) (unnest_fby (concat x2) (concat x6) a) vs) as Hsemf.
      { eapply unnest_fby_sem... 2:congruence.
        + eapply map_bind2_unnest_exp_length in H2'... congruence.
        + clear - Hsem1 Href2 Href4. solve_forall. repeat (eapply sem_exp_refines; eauto).
        + clear - Hsem2 Href2 Href4. solve_forall. repeat (eapply sem_exp_refines; eauto). }

      exists H'''. repeat (split; eauto).
      * repeat (etransitivity; eauto).
      * eapply idents_for_anns_dom in H4; eauto.
      * clear - Hsemvars. solve_forall.
      * repeat rewrite Forall_app. repeat split.
        -- clear - Hsemvars Hsemf.
           remember (unnest_fby _ _ _) as fby. clear Heqfby.
           simpl_forall.
           repeat rewrite_Forall_forall. 1:congruence.
           destruct (nth _ x5 _) eqn:Hnth1.
           econstructor.
           ++ repeat constructor.
              eapply H0... congruence.
           ++ repeat constructor.
              eapply H2 with (x1:=(i, a1))...
        -- solve_forall. repeat (eapply sem_equation_refines; eauto).
        -- solve_forall. repeat (eapply sem_equation_refines; eauto).
           Unshelve. exact default_stream.
    - (* arrow *)
      simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      assert (length (concat x2) = length (annots e0s)) as Hlength1 by (eapply map_bind2_unnest_exp_length; eauto).
      assert (length (concat x6) = length (annots es)) as Hlength2 by (eapply map_bind2_unnest_exp_length; eauto).
      assert (NoDup (map fst (fresh_ins es) ++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (fresh_ins e0s) ++ PS.elements (ps_adds (map fst (concat (map fresh_in es))) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
      assert (Forall (fun e => numstreams e = 1) (concat x2)) as Hnumstreams.
      { eapply map_bind2_unnest_exp_numstreams in H2... }

      assert (length s0ss = length e0s) as Hlen1 by (eapply Forall2_length in H12; eauto).
      assert (H2':=H2). eapply map_bind2_sem in H2... 2:solve_forall. clear H.
      destruct H2 as [H' [Href1 [Histst1 [Hdom1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.

      assert (Forall2 (sem_exp G H' b) es sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).
      assert (length sss = length es) as Hlen2 by (eapply Forall2_length in H14; eauto).
      assert (H3':=H3). eapply map_bind2_sem in H3... 2:solve_forall. clear H0.
      destruct H3 as [H'' [Href2 [Hvalid2 [Hdom2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.

      assert (Forall2 (fun (e : exp) (v : Stream OpAux.value) => sem_exp G H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }
      specialize (idents_for_anns_length _ _ _ _ H4) as Hlength.
      assert (length vs = length a) as Hlength'''.
      { eapply Forall3_length in H15 as [_ ?]. eapply Forall2_length in Hsem2. congruence. }

      remember (Env.adds (List.map fst x5) vs H'') as H'''.
      assert (length x5 = length vs) as Hlength'''' by (rewrite Hlength, Hlength'''; auto).

      assert (Forall2 (sem_var H''') (map fst x5) vs) as Hsemvars.
      { rewrite HeqH'''. eapply sem_var_adds; eauto.
        + rewrite map_length; auto.
        + eapply idents_for_anns_NoDupMembers in H4; eauto. rewrite <- fst_NoDupMembers; eauto. }

      assert (Env.refines eq H'' H''') as Href4.
      { eapply idents_for_anns_refines in H4... }
      assert (Forall2 (fun e v => sem_exp G H''' b e [v]) (unnest_arrow (concat x2) (concat x6) a) vs) as Hsemf.
      { eapply unnest_arrow_sem... 2:congruence.
        + eapply map_bind2_unnest_exp_length in H2'... congruence.
        + clear - Hsem1 Href2 Href4. solve_forall. repeat (eapply sem_exp_refines; eauto).
        + clear - Hsem2 Href2 Href4. solve_forall. repeat (eapply sem_exp_refines; eauto). }

      exists H'''. repeat (split; eauto).
      * repeat (etransitivity; eauto).
      * eapply idents_for_anns_dom in H4; eauto.
      * clear - Hsemvars. solve_forall.
      * repeat rewrite Forall_app. repeat split.
        -- clear - Hsemvars Hsemf.
           remember (unnest_arrow _ _ _) as fby. clear Heqfby.
           simpl_forall.
           repeat rewrite_Forall_forall. 1:congruence.
           destruct (nth _ x5 _) eqn:Hnth1.
           econstructor.
           ++ repeat constructor.
              eapply H0... congruence.
           ++ repeat constructor.
              eapply H2 with (x1:=(i, a1))...
        -- solve_forall. repeat (eapply sem_equation_refines; eauto).
        -- solve_forall. repeat (eapply sem_equation_refines; eauto).
           Unshelve. exact default_stream.
    - (* when *)
      assert (length (concat x1) = length (annots es)) as Hlength by (eapply map_bind2_unnest_exp_length; eauto).
      assert (length es = length ss) by (apply Forall2_length in H11; auto).
      eapply map_bind2_sem in H1... 2:solve_forall. clear H.
      destruct H1 as [H' [Hvalid1 [Href1 [Hdom1 [Hsem1 Hsem1']]]]].
      apply Forall2_concat in Hsem1.
      exists H'. repeat (split; simpl; eauto).
      eapply unnest_when_sem... congruence.
      eapply sem_var_refines...
    - (* merge *)
      simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      assert (length (concat x3) = length (annots ets)) as Hlength1 by (eapply map_bind2_unnest_exp_length; eauto).
      assert (length (concat x6) = length (annots efs)) as Hlength2 by (eapply map_bind2_unnest_exp_length; eauto).
      assert (length (concat ts) = length (annots ets)) as Hlength1' by (eapply sem_exps_numstreams; eauto).
      assert (NoDup (map fst (fresh_ins efs) ++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (fresh_ins ets) ++ PS.elements (ps_adds (map fst (concat (map fresh_in efs))) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

      assert (length ets = length ts) by (apply Forall2_length in H15; auto).
      eapply map_bind2_sem in H2... 2:solve_forall. clear H.
      destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.

      assert (length efs = length fs) by (apply Forall2_length in H16; auto).
      assert (Forall2 (sem_exp G H' b) efs fs) as Hsemf' by (solve_forall; eapply sem_exp_refines; eauto). clear H16.
      eapply map_bind2_sem in H3... 2:solve_forall.
      destruct H3 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
      assert (length (annots ets) = length (annots efs)) as Hlen' by congruence.
      assert (Forall2 (fun e v => sem_exp G H'' b e [v])
                      (unnest_merge x (concat x3) (concat x6) tys nck) vs) as Hsem'.
      { eapply unnest_merge_sem... 1,2:congruence.
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
          apply Forall3_length in H17 as [? ?]; congruence. }
        assert (Env.refines eq H'' H''') as Href3.
        {eapply idents_for_anns_refines... }
        assert (Forall2 (sem_var H''') (map fst x0) vs) as Hvars.
        { rewrite HeqH'''. eapply sem_var_adds... 1:rewrite map_length...
          rewrite <- fst_NoDupMembers. eapply idents_for_anns_NoDupMembers in H2... }
        exists H'''. repeat (split; eauto).
        * repeat (etransitivity; eauto).
        * eapply idents_for_anns_dom...
        * clear - Hvars. solve_forall.
        * repeat rewrite Forall_app; repeat split.
          -- remember (unnest_merge _ _ _ _ _) as merge.
             assert (length merge = length x0) as Hlength''.
             { eapply idents_for_anns_length in H2. clear - Heqmerge H17 H2 H9 Hlength1 Hlength2 Hlen'.
               rewrite Heqmerge, unnest_merge_length; solve_length. }
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
      { eapply unnest_exp_length in H2... congruence. }
      assert (length (concat x5) = length (annots ets)) as Hlength1 by (eapply map_bind2_unnest_exp_length; eauto).
      assert (length (concat x8) = length (annots efs)) as Hlength2 by (eapply map_bind2_unnest_exp_length; eauto).
      assert (length (concat ts) = length (annots ets)) as Hlength1' by (eapply sem_exps_numstreams; eauto).
      assert (NoDup (map fst (fresh_ins efs) ++ PS.elements reusable)) as Hndup3 by repeat ndup_r Hndup.
      assert (NoDup (map fst (fresh_ins ets) ++ PS.elements (ps_adds (map fst (concat (map fresh_in efs))) reusable))) as Hndup2.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }
      assert (NoDup
                (map fst (fresh_in e) ++
                     PS.elements (ps_adds (map fst (fresh_ins ets)) (ps_adds (map fst (fresh_ins efs)) reusable)))) as Hndup1.
      { repeat rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }

      assert (length ets = length ts) by (apply Forall2_length in H17; auto).
      eapply IHe in H2... clear IHe.
      destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. inv Hsem1; rename H16 into Hsem1. clear H21.

      assert (length efs = length fs) by (apply Forall2_length in H18; auto).
      assert (Forall2 (sem_exp G H' b) ets ts) as Hsemt' by (solve_forall; eapply sem_exp_refines; eauto). clear H17.
      eapply map_bind2_sem in H3... 2:solve_forall. clear H.
      destruct H3 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.

      assert (length efs = length fs) by (apply Forall2_length in H18; auto).
      assert (Forall2 (sem_exp G H'' b) efs fs) as Hsemf' by (solve_forall; repeat (eapply sem_exp_refines; eauto)). clear H18.
      eapply map_bind2_sem in H4... 2:solve_forall. clear H0.
      destruct H4 as [H''' [Href3 [Hvalid3 [Histst3 [Hsem3 Hsem3']]]]]. apply Forall2_concat in Hsem3.

      assert (Forall2 (fun e v => sem_exp G H''' b e [v])
                      (unnest_ite e0 (concat x5) (concat x8) tys nck) vs) as Hsem'.
      { eapply unnest_ite_sem... 1,2:congruence.
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
          apply Forall3_length in H19 as [? ?]; congruence. }
        assert (Env.refines eq H''' H'''') as Href4.
        { eapply idents_for_anns_refines... }
        assert (Forall2 (sem_var H'''') (map fst x) vs) as Hvars.
        { rewrite HeqH''''. eapply sem_var_adds... 1:rewrite map_length...
          rewrite <- fst_NoDupMembers. eapply idents_for_anns_NoDupMembers in H0... }
        exists H''''. repeat (split; eauto).
        * repeat (etransitivity; eauto).
        * eapply idents_for_anns_dom in H0...
        * clear - Hvars. solve_forall.
        * repeat rewrite Forall_app; repeat split.
          2,3,4: (solve_forall; repeat (eapply sem_equation_refines; eauto)).
          remember (unnest_ite _ _ _ _ _) as ite.
          assert (length ite = length x) as Hlength''.
          { eapply idents_for_anns_length in H0. clear - Heqite H19 H0 Hlength1 Hlength2 H11 H12.
            rewrite Heqite, unnest_ite_length; solve_length. }
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
      { destruct H14. apply Forall2_length in H11.
        rewrite H5 in H8; inv H8. unfold idents in *. solve_length. }
      assert (length es = length ss) as Hlength3.
      { apply Forall2_length in H13... }
      assert (NoDup (map fst (Syn.anon_streams (map snd x1))++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (fresh_ins es) ++ PS.elements (ps_adds (map fst (Syn.anon_streams (map snd x1))) reusable))).
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

      eapply map_bind2_sem in H2... 2:solve_forall... clear H0.
      destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].

      assert (sem_exp G H' b (Eapp f (concat x2) None (map snd x1)) vs) as Hsem'.
      { apply Sapp with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))).
        + apply Forall2_concat.
          do 2 solve_forall.
        + rewrite concat_map_singl2. assumption. }
      remember (Env.adds (map fst x1) vs H') as H''.
      assert (length vs = length x1) as Hlen' by solve_length.
      assert (Env.refines eq H' H'') as Href2.
      { eapply idents_for_anns'_refines... }
      assert (NoDupMembers x1) as Hndup'.
      { eapply idents_for_anns'_NoDupMembers in H3... }
      assert (Forall2 (sem_var H'') (map fst x1) vs) as Hvars.
      { rewrite HeqH''. eapply sem_var_adds... 1:rewrite map_length... rewrite <- fst_NoDupMembers... }
      exists H''. repeat (split; eauto).
      + etransitivity...
      + eapply idents_for_anns'_dom in H3...
      + clear - Hvars. solve_forall.
      + rewrite app_nil_r. constructor.
        * apply Seq with (ss:=[vs]).
          -- repeat constructor...
             eapply sem_exp_refines...
          -- simpl. rewrite app_nil_r; auto.
        * solve_forall. eapply sem_equation_refines...
    - (* app (reset) *)
      do 5 inv_bind.
      assert (Hs:=H3). eapply unnest_reset_Some in Hs as [er' ?]; subst.
      simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
      assert (a = map snd x5) as Hanns; subst.
      { eapply idents_for_anns'_values in H4... }
      specialize (idents_for_anns'_length _ _ _ _ H4) as Hlength1.
      assert (length (n_out n) = length vs) as Hlength2.
      { specialize (H19 0). inv H19. apply Forall2_length in H14.
        unfold idents in *. repeat rewrite map_length in H14. congruence. }
      assert (length es = length ss) as Hlength3.
      { apply Forall2_length in H15... }
      (* assert (length x6 = 1). 2:singleton_length. *)
      (* { eapply unnest_exp_length in H3... congruence. } *)
      assert (NoDup (map fst (Syn.anon_streams (map snd x5))++ PS.elements reusable)) as Hndup2 by repeat ndup_r Hndup.
      assert (NoDup (map fst (fresh_in r) ++ PS.elements (ps_adds (map fst (Syn.anon_streams (map snd x5))) reusable))) as Hndup3.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }
      assert (NoDup (map fst (fresh_ins es) ++ PS.elements (ps_adds (map fst (fresh_in r)) (ps_adds (map fst (Syn.anon_streams (map snd x5))) reusable)))) as Hndup4.
      { repeat rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }

      apply bind2_spec in H2 as [? [? [? [? Hret]]]]. rewrite ret_spec in Hret; inv Hret.
      eapply map_bind2_sem in H2... 2:solve_forall... clear H0.
      destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].

      assert (sem_exp G H' b r [rs]) as Hsemr' by (eapply sem_exp_refines; eauto). clear H17.
      eapply (unnest_reset_sem _ _ _ (Some r)) in H3; simpl...
      2:{ clear H3. intros. eapply H in H0 as [H'' [? [? [? [? ?]]]]]; eauto.
          inv H5.
          exists H''. repeat split; eauto. }
      destruct H3 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]].

      assert (sem_exp G H'' b (Eapp f (concat x2) (Some er') (map snd x5)) vs) as Hsem'.
      { eapply Sreset with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss)))...
        + apply Forall2_concat. repeat solve_forall.
          repeat (eapply sem_exp_refines; eauto).
        + intros k. specialize (H19 k).
          rewrite concat_map_singl2. assumption. }
      remember (Env.adds (map fst x5) vs H'') as H'''.
      assert (length vs = length x5) as Hlen' by solve_length.
      assert (Env.refines eq H'' H''') as Href4.
      { eapply idents_for_anns'_refines... }
      assert (NoDupMembers x5) as Hndup'.
      { eapply idents_for_anns'_NoDupMembers in H4... }
      assert (Forall2 (sem_var H''') (map fst x5) vs) as Hvars.
      { rewrite HeqH'''. eapply sem_var_adds... 1:rewrite map_length... rewrite <- fst_NoDupMembers... }
      exists H'''. repeat (split; eauto).
      + repeat (etransitivity; eauto).
      + eapply idents_for_anns'_dom in H4...
      + clear - Hvars. solve_forall.
      + constructor; [| repeat rewrite Forall_app; repeat split].
        * apply Seq with (ss:=[vs]).
          -- repeat constructor...
             eapply sem_exp_refines...
          -- simpl. rewrite app_nil_r; auto.
        * solve_forall. repeat (eapply sem_equation_refines; eauto).
        * solve_forall. repeat (eapply sem_equation_refines; eauto).
  Qed.

  Corollary unnest_exps_sem : forall G vars b es H vs es' eqs' st st' reusable,
      NoDup (map fst (fresh_ins es) ++ PS.elements reusable) ->
      Forall (wl_exp G) es ->
      Forall2 (sem_exp G H b) es vs ->
      st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (fresh_ins es)) reusable) ->
      Env.dom H (vars++st_ids st) ->
      map_bind2 (unnest_exp false) es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list vars) reusable /\
          Env.dom H' (vars++st_ids st') /\
          Forall2
            (fun (es : list exp) (vs : list (Stream OpAux.value)) =>
             Forall2 (fun e v => sem_exp G H' b e [v]) es vs) es' vs /\
          Forall (sem_equation G H' b) (concat eqs')).
  Proof.
    intros * Hndup Hwt Hsem Hvalid Hdom Hnorm.
    eapply map_bind2_sem in Hnorm; eauto.
    repeat rewrite_Forall_forall.
    specialize (nth_In _ a H2) as Hin.
    eapply unnest_exp_sem with (e:=(nth n es a)); eauto.
  Qed.

  Fact unnest_rhs_sem : forall G vars b e H vs es' eqs' st st' reusable,
      NoDup (map fst (anon_in e) ++ PS.elements reusable) ->
      wl_exp G e ->
      sem_exp G H b e vs ->
      st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (anon_in e)) reusable) ->
      Env.dom H (vars++st_ids st) ->
      unnest_rhs e st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list vars) reusable /\
          Env.dom H' (vars++st_ids st') /\
          (Forall2 (fun e v => sem_exp G H' b e [v]) es' vs \/
           exists e', (es' = [e'] /\ sem_exp G H' b e' vs)) /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros * Hndup1 Hwt Hsem Hvalid Hhistst Hnorm.
    destruct e; try eapply unnest_exp_sem in Hnorm; eauto.
    1,2,3,4,7,8,9: (destruct Hnorm as [H' [Href1 [Hvalid1 [Hhistst1 [Hsem1 Hsem2]]]]];
                    exists H'; repeat (split; eauto)).
    1,2,3:(unfold unnest_rhs in Hnorm;inv Hwt; inv Hsem).
    - (* fby *)
      simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
      repeat inv_bind.
      assert (length x = length (annots l)) as Hlength1 by (eapply unnest_exps_length; eauto).
      assert (length x2 = length (annots l0)) as Hlength2 by (eapply unnest_exps_length; eauto).
      unfold unnest_exps in *. repeat inv_bind.
      assert (NoDup (map fst (fresh_ins l0) ++ PS.elements reusable)) as Hndup4 by ndup_r Hndup1.
      assert (NoDup (map fst (fresh_ins l) ++ PS.elements (ps_adds (map fst (fresh_ins l0)) reusable))) as Hndup3.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

      eapply unnest_exps_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.
      assert (Forall2 (sem_exp G H' b) l0 sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).

      eapply unnest_exps_sem in H1...
      destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
      assert (Forall2 (fun (e : exp) (v : Stream OpAux.value) => sem_exp G H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }

      exists H''. repeat (split; auto).
      + repeat (etransitivity; eauto).
      + left. eapply unnest_fby_sem... 1,2:solve_length.
      + repeat rewrite Forall_app. repeat split...
        solve_forall. eapply sem_equation_refines; [| eauto]. etransitivity...
    - (* arrow *)
      simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
      repeat inv_bind.
      assert (length x = length (annots l)) as Hlength1 by (eapply unnest_exps_length; eauto).
      assert (length x2 = length (annots l0)) as Hlength2 by (eapply unnest_exps_length; eauto).
      unfold unnest_exps in *. repeat inv_bind.
      assert (NoDup (map fst (fresh_ins l0) ++ PS.elements reusable)) as Hndup4 by ndup_r Hndup1.
      assert (NoDup (map fst (fresh_ins l) ++ PS.elements (ps_adds (map fst (fresh_ins l0)) reusable))) as Hndup3.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

      eapply unnest_exps_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.
      assert (Forall2 (sem_exp G H' b) l0 sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).

      eapply unnest_exps_sem in H1...
      destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
      assert (Forall2 (fun (e : exp) (v : Stream OpAux.value) => sem_exp G H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }

      exists H''. repeat (split; auto).
      + repeat (etransitivity; eauto).
      + left. eapply unnest_arrow_sem... 1,2:solve_length.
      + repeat rewrite Forall_app. repeat split...
        solve_forall. eapply sem_equation_refines; [| eauto]. etransitivity...
    - (* app *)
      repeat inv_bind. unfold unnest_exps in H0; repeat inv_bind.
      eapply unnest_exps_sem in H0...
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
      do 2 inv_bind. unfold unnest_exps in H0.
      assert (Hs:=H1). eapply unnest_reset_Some in Hs as [er' ?]; subst.
      apply bind2_spec in H0 as [? [? [? [? Hret]]]]. rewrite ret_spec in Hret; inv Hret.
      assert (NoDup (map fst (fresh_in r) ++ PS.elements reusable)) as Hndup4 by ndup_r Hndup1.
      assert (NoDup (map fst (fresh_ins l) ++ PS.elements (ps_adds (map fst (fresh_in r)) reusable))) as Hndup3.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

      eapply unnest_exps_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].

      assert (sem_exp G H' b r [rs]) as Hsemr'.
      { eapply sem_exp_refines; eauto. } clear H15.
      eapply (unnest_reset_sem _ _ _ (Some r)) in H1; simpl...
      2:(clear H1; intros;
         eapply unnest_exp_sem in H0 as [H'' [? [? [? [? ?]]]]]; eauto;
         inv H6; exists H''; repeat split; eauto).
      repeat inv_bind.
      destruct H1 as [H''' [Href3 [Hvalid3 [Histst3 [Hsem3 Hsem3']]]]].
      exists H'''. repeat (split; auto).
      + repeat (etransitivity; eauto).
      + right. eexists; split...
        apply Sreset with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))) (rs:=rs) (bs:=bs); eauto.
        * apply Forall2_concat.
          solve_forall. solve_forall. repeat (eapply sem_exp_refines; eauto).
        * rewrite concat_map_singl2. assumption.
      + repeat rewrite Forall_app.
        repeat split; solve_forall; (eapply sem_equation_refines; [| eauto]); eauto.
  Qed.

  Corollary map_bind2_unnest_rhs_sem : forall G vars b es H vs es' eqs' st st' reusable,
      NoDup (map fst (anon_ins es) ++ PS.elements reusable) ->
      Forall (wl_exp G) es ->
      Forall2 (sem_exp G H b) es vs ->
      st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (anon_ins es)) reusable) ->
      Env.dom H (vars++st_ids st) ->
      map_bind2 unnest_rhs es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list vars) reusable /\
          Env.dom H' (vars++st_ids st') /\
          Forall2 (fun es' vs =>
                     Forall2 (fun e v => sem_exp G H' b e [v]) es' vs \/
                     exists e', (es' = [e'] /\ sem_exp G H' b e' vs)) es' vs /\
          Forall (sem_equation G H' b) (concat eqs')).
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

  Corollary unnest_rhss_sem : forall G vars b es H vs es' eqs' st st' reusable,
      NoDup (map fst (anon_ins es) ++ PS.elements reusable) ->
      Forall (wt_exp G (vars++st_tys st)) es ->
      Forall2 (sem_exp G H b) es vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_ins es)) reusable) ->
      Env.dom H (map fst vars++st_ids st) ->
      unnest_rhss es st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
          Env.dom H' (map fst vars++st_ids st') /\
          Forall (fun '(e, v) => sem_exp G H' b e v)
                 (combine_for_numstreams es' (concat vs)) /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros * Hndup Hwt Hsem Hvalid Histst Hnorm.
    assert (Forall (wt_exp G (vars++st_tys st')) es') as Hwt'.
    { eapply unnest_rhss_wt in Hnorm as [? ?]... }
    unfold unnest_rhss in *.
    repeat inv_bind.
    eapply map_bind2_unnest_rhs_sem in H0...
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

  Fact unnest_equation_sem : forall G vars H b equ eqs' st st' reusable,
      NoDup (map fst (anon_in_eq equ) ++ PS.elements reusable) ->
      wt_equation G (vars++st_tys st) equ ->
      sem_equation G H b equ ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in_eq equ)) reusable) ->
      Env.dom H (map fst vars++st_ids st) ->
      unnest_equation equ st = (eqs', st') ->
      (exists H', Env.refines eq H H' /\
             st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
             Env.dom H' (map fst vars++st_ids st') /\
             Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros * Hndup Hwt Hsem Hvalid Histst Hnorm.
    unfold unnest_equation in Hnorm.
    destruct equ as [xs es]. inv Hwt. inv Hsem.
    repeat inv_bind.
    assert (typesof x = typesof es) as Hannots by (eapply unnest_rhss_typesof; eauto).
    eapply unnest_rhss_sem in H2...
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

  Corollary unnest_equations_sem : forall G vars b eqs H eqs' st st' reusable,
      NoDup (map fst (anon_in_eqs eqs) ++ PS.elements reusable) ->
      Forall (wt_equation G (vars ++ st_tys st)) eqs ->
      Forall (sem_equation G H b) eqs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in_eqs eqs)) reusable) ->
      Env.dom H (map fst vars++st_ids st) ->
      unnest_equations eqs st = (eqs', st') ->
      (exists H', Env.refines eq H H' /\
             Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction eqs; intros * Hndup Hwt Hsem Hvalid Hdome Hnorm;
      unfold unnest_equations in *; inv Hwt; inv Hsem; repeat inv_bind; simpl.
    - exists H...
    - unfold anon_in_eqs in *; simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      assert (NoDup (map fst (anon_in_eqs eqs) ++ PS.elements reusable)) as Hndup4 by ndup_r Hndup.
      assert (NoDup (map fst (anon_in_eq a) ++ PS.elements (ps_adds (map fst (anon_in_eqs eqs)) reusable))) as Hndup3.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

      assert (Forall (wt_equation G (vars ++ st_tys x1)) eqs) as Hwt' by (solve_forall; repeat solve_incl).
      eapply unnest_equation_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 Hsem1]]]].
      assert (Forall (sem_equation G H' b) eqs) by (solve_forall; eapply sem_equation_refines; eauto).

      assert (unnest_equations eqs x1 = (concat x2, st')) as Hnorm.
      { unfold unnest_equations; repeat inv_bind. repeat eexists; eauto. inv_bind; eauto. }
      eapply IHeqs in Hnorm...
      destruct Hnorm as [H'' [Href Hsem2]].
      exists H''. repeat split...
      + etransitivity...
      + eapply Forall_app. split...
        solve_forall. eapply sem_equation_refines...
  Qed.

  (** *** Preservation of sem_node *)

  Fact unnest_node_sem_equation : forall G H n Hwl Hpref ins,
      wt_node G n ->
      Env.dom H (List.map fst (n_in n ++ n_vars n ++ n_out n)) ->
      Forall2 (sem_var H) (idents (n_in n)) ins ->
      Forall (sem_equation G H (clocks_of ins)) (n_eqs n) ->
      (* Forall2 (fun xc : ident * clock => sem_clock H (clocks_of ins) (snd xc)) (idck (n_in n)) (map abstract_clock ins) -> *)
      exists H', Env.refines eq H H' /\
            Forall (sem_equation G H' (clocks_of ins)) (n_eqs (unnest_node n Hwl Hpref)).
  Proof with eauto.
    intros * Hwt Hdom Hins Hsem.
    specialize (n_nodup n) as Hndup; rewrite fst_NoDupMembers in Hndup; repeat rewrite map_app in Hndup.
    eapply unnest_equations_sem with (eqs:=n_eqs n) (st:=init_st)...
    5: simpl; rewrite <- surjective_pairing; subst; reflexivity.
    - rewrite PSP.elements_empty, app_nil_r.
      repeat ndup_r Hndup...
    - unfold st_tys. rewrite init_st_anns, app_nil_r.
      destruct Hwt as [_ [_ [_ Hwt]]]; eauto.
    - rewrite map_fst_idty.
      apply init_st_valid_reuse.
      + replace (ps_adds _ PS.empty) with (ps_from_list (map fst (anon_in_eqs (n_eqs n)))); auto.
        rewrite ps_from_list_ps_of_list.
        repeat rewrite ps_of_list_ps_to_list_Perm; repeat rewrite map_app; repeat rewrite <- app_assoc in *; auto.
        repeat ndup_r Hndup.
        repeat rewrite app_assoc in Hndup. apply NoDup_app_l in Hndup.
        repeat rewrite <- app_assoc in Hndup; auto.
      + apply norm1_not_in_elab_prefs.
      + rewrite <- ps_from_list_ps_of_list, PS_For_all_Forall', <- Hpref.
        pose proof (n_good n) as (Good&_).
        eapply Forall_incl; [eauto|].
        repeat rewrite map_app.
        repeat apply incl_tl.
        repeat rewrite app_assoc. apply incl_appl. reflexivity.
      + replace (ps_adds _ PS.empty) with (ps_from_list (map fst (anon_in_eqs (n_eqs n)))); auto.
        rewrite PS_For_all_Forall', <- Hpref.
        pose proof (n_good n) as (Good&_).
        eapply Forall_incl; [eauto|].
        repeat rewrite map_app.
        repeat apply incl_tl.
        repeat apply incl_appr. reflexivity.
    - unfold st_ids. rewrite init_st_anns, app_nil_r, map_fst_idty...
  Qed.

  Lemma unnest_node_eq : forall G G' f n Hwl Hpref ins outs,
      Forall2 (fun n n' => n_name n = n_name n') G G' ->
      global_iface_eq G G' ->
      global_sem_refines G G' ->
      wt_global (n::G) ->
      wc_global (n::G) ->
      Ordered_nodes (n::G) ->
      Ordered_nodes ((unnest_node n Hwl Hpref)::G') ->
      sem_node (n::G) f ins outs ->
      sem_node ((unnest_node n Hwl Hpref)::G') f ins outs.
  Proof with eauto.
    intros * Hnames Hiface Href HwtG HwcG Hord1 Hord2 Hsem.
    assert (Forall (fun n' => exists v, In v G /\ n_name n <> n_name n') G') as Hnames'.
    { assert (length G = length G') by (eapply Forall2_length in Hnames; eauto).
      inv HwtG. eapply Forall2_ignore1. solve_forall. }
    assert (Ordered_nodes (n :: G')) as Hord'.
    { inv Hord2. constructor... clear H2.
      inv Hord1. intros ? Hisin. apply H4 in Hisin as [Hneq Hname].
      split; auto. clear - Hnames Hname.
      induction Hnames; inv Hname.
      + left; auto.
      + right; auto. }

    inv Hsem; assert (Hfind:=H0); simpl in H0. destruct (ident_eqb (n_name n) f) eqn:Hident.
    - inv H0. inv HwcG.
      (*The semantics of equations can be given according to G only *)
      eapply Forall_sem_equation_global_tl in H3; eauto.
      2:{ inv Hord1. intro contra. apply H9 in contra as [? _]; auto. }
      (* New env H' (restrict H) and its properties *)
      eapply LCS.sem_node_restrict in H3 as (Hdom&Hins'&Houts'&Heqs'); eauto.
      2:destruct H6 as (?&?&?&?); auto.
      remember (Env.restrict H (List.map fst (n_in n0++n_vars n0++n_out n0))) as H'.
      clear H H1 H2 HeqH'.
      inversion_clear HwtG. rename H0 into Hwt.

      eapply unnest_node_sem_equation in Heqs' as (H''&Href'&Heqs'')...
      eapply Snode with (H:=H''); simpl. 5:reflexivity.
      + rewrite Hident; reflexivity.
      + simpl. repeat rewrite_Forall_forall. eapply sem_var_refines...
      + simpl. repeat rewrite_Forall_forall. eapply sem_var_refines...
      + clear Hins' Houts' Hdom.
        apply Forall_sem_equation_global_tl'...
        eapply find_node_not_Is_node_in in Hord2...
        simpl. rewrite ident_eqb_refl...
        eapply Forall_impl; [|eauto]. intros. eapply sem_ref_sem_equation; eauto.
    - specialize (Href f ins outs).
      rewrite ident_eqb_neq in Hident.
      eapply sem_node_cons'...
      apply Href.
      econstructor...
      eapply Forall_impl_In; [| eauto]. intros eq Hin Hsem.
      eapply sem_equation_global_tl...
      eapply find_node_later_not_Is_node_in in Hord1...
      intro Hisin. apply Hord1. rewrite Is_node_in_Exists. rewrite Exists_exists.
      eexists...
  Qed.

  Fact unnest_global_names' : forall G Hwl Hpref,
      Forall2 (fun n n' => n_name n = n_name n') G (unnest_global G Hwl Hpref).
  Proof.
    intros.
    specialize (Ordered.unnest_global_names G Hwl Hpref) as Hnames.
    rewrite <- Forall2_eq, Forall2_swap_args in Hnames.
    solve_forall.
  Qed.

  Lemma unnest_global_refines : forall G Hwl Hprefs,
      wt_global G ->
      wc_global G ->
      Ordered_nodes G ->
      global_sem_refines G (unnest_global G Hwl Hprefs).
  Proof with eauto.
    intros G Hwl. specialize (unnest_global_eq G Hwl) as Heq.
    induction G; intros * Hwt Hwc Hordered; simpl.
    - apply global_sem_ref_nil.
    - apply global_sem_ref_cons with (f:=n_name a)...
      + eapply Ordered.unnest_global_ordered in Hordered.
        simpl in Hordered...
      + inv Hwt; inv Hwc; inv Hordered.
        eapply IHG... eapply unnest_global_eq...
      + intros ins outs Hsem.
        eapply unnest_node_eq...
        * apply unnest_global_names'.
        * apply unnest_global_eq.
        * inv Hwt; inv Hwc; inv Hordered.
          eapply IHG... eapply unnest_global_eq...
        * eapply Ordered.unnest_global_ordered in Hordered.
          simpl in Hordered...
  Qed.

  Fact wt_global_ordered_nodes : forall G,
      wt_global G ->
      Ordered_nodes G.
  Proof.
    intros.
    apply wl_global_ordered_nodes; auto.
    apply wt_global_NoDup; auto.
  Qed.
  Hint Resolve wt_global_ordered_nodes.

  Corollary unnest_global_sem : forall G Hwl Hprefs f ins outs,
      wt_global G ->
      wc_global G ->
      sem_node G f ins outs ->
      sem_node (unnest_global G Hwl Hprefs) f ins outs.
  Proof.
    intros.
    eapply unnest_global_refines with (Hwl:=Hwl) in H; eauto.
    specialize (H f ins outs); auto.
  Qed.

  Corollary unnest_global_sem_clock_inputs : forall G Hwl Hprefs f ins,
      LCS.sem_clock_inputs G f ins ->
      LCS.sem_clock_inputs (unnest_global G Hwl Hprefs) f ins.
  Proof.
    intros.
    specialize (unnest_global_eq G Hwl Hprefs) as Heq.
    destruct H as [H [n' [Hfind [Hvars Hsem]]]].
    eapply global_iface_eq_find in Heq as [? [? [Hname [_ [Hin Hout]]]]]; eauto.
    exists H. exists x. repeat split; auto.
    1,2:congruence.
  Qed.

  (** ** Preservation of the semantics through the second pass *)

  (** *** Manipulation of initialization streams *)

  (** We want to specify the semantics of the init equations created during the normalization
      with idents stored in the env *)

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
      const b c ≡ const_val b (Op.sem_const c).
  Proof.
    cofix const_val_const.
    intros [b0 b] c; simpl.
    constructor; simpl; auto.
  Qed.

  CoFixpoint hold (v : Op.val) (str : Stream OpAux.value) :=
    match str with
    | (present v') ⋅ str' => (present v) ⋅ (hold v' str')
    | absent ⋅ str' => absent ⋅ (hold v str')
    end.

  Fact hold_Cons : forall v y ys,
      hold v (y ⋅ ys) =
      match y with
      | present v' => (present v) ⋅ (hold v' ys)
      | absent => absent ⋅ (hold v ys)
      end.
  Proof.
    intros v y ys.
    rewrite unfold_Stream at 1; simpl.
    destruct y; reflexivity.
  Qed.

  Add Parametric Morphism : hold
      with signature eq ==> @EqSt value ==> @EqSt value
    as hold_EqSt.
  Proof.
    cofix CoFix.
    intros v [x xs] [y ys] Heq.
    inv Heq; simpl in *; subst.
    constructor; simpl.
    + destruct y; auto.
    + destruct y; auto.
  Qed.

  Lemma hold_const : forall bs v,
      hold v (const_val bs v) ≡ (const_val bs v).
  Proof.
    cofix CoFix.
    intros [b bs] v.
    rewrite const_val_Cons.
    destruct b; rewrite hold_Cons; constructor; simpl; auto.
  Qed.

  Lemma ite_false : forall bs xs ys,
      aligned xs bs ->
      aligned ys bs ->
      ite (const_val bs false_val) xs ys ys.
  Proof.
    cofix CoFix.
    intros [b bs] xs ys Hsync1 Hsync2.
    rewrite const_val_Cons.
    inv Hsync1; inv Hsync2; constructor; auto.
  Qed.

  Lemma hold_fby1 : forall bs v y ys,
      aligned ys bs ->
      fby1 y (const_val bs v) ys (hold y ys).
  Proof with eauto.
    cofix hold_fby1.
    intros [b bs] v y ys Hsync.
    specialize (hold_fby1 bs).
    inv Hsync;
      rewrite const_val_Cons; rewrite unfold_Stream; simpl.
    - constructor...
    - constructor...
  Qed.

  Lemma hold_fby1' : forall y y0s ys zs,
      fby1 y y0s ys zs ->
      zs ≡ (hold y ys).
  Proof.
    cofix CoFix.
    intros y y0s ys zs Hfby1.
    inv Hfby1; constructor; simpl; eauto.
  Qed.

  Lemma hold_fby : forall b v y,
      aligned y b ->
      fby (const_val b v) y (hold v y).
  Proof with eauto.
    cofix hold_fby.
    intros [b bs] v y Hsync.
    rewrite const_val_Cons.
    rewrite unfold_Stream; simpl.
    destruct b; simpl; inv Hsync.
    - econstructor. eapply hold_fby1...
    - econstructor; simpl...
  Qed.

  Definition init_stream bs :=
    hold true_val (const bs false_const).

  Instance init_stream_Proper:
    Proper (@EqSt bool ==> @EqSt value) init_stream.
  Proof.
    intros bs bs' Heq.
    unfold init_stream. rewrite Heq. reflexivity.
  Qed.

  Lemma fby_ite : forall bs v y0s ys zs,
      (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
      fby y0s ys zs ->
      ite (hold true_val (const_val bs false_val)) y0s (hold v ys) zs.
  Proof with eauto.
    cofix fby_init_stream_ite.
    intros [b bs] v y0s ys zs Hsync Hfby1.
    apply LCS.fby_aligned in Hsync as [Hsync1 [Hsync2 Hsync3]]; [|auto].
    destruct b; inv Hsync1; inv Hsync2; inv Hsync3.
    - repeat rewrite const_val_Cons.
      inv Hfby1.
      repeat rewrite hold_Cons. constructor.
      rewrite hold_const.
      rewrite <- hold_fby1'...
      apply ite_false...
    - rewrite const_val_Cons. repeat rewrite hold_Cons.
      inv Hfby1.
      constructor; auto.
  Qed.

  Corollary fby_init_stream_ite : forall bs v y0s ys zs,
      (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
      fby y0s ys zs ->
      ite (init_stream bs) y0s (hold v ys) zs.
  Proof.
    intros * Hsync Hfby1.
    eapply fby_ite in Hfby1; eauto.
    unfold init_stream.
    rewrite const_val_const. rewrite sem_false_const. eassumption.
  Qed.

  Lemma arrow_ite : forall bs y0s ys zs,
      (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
      arrow y0s ys zs ->
      ite (hold true_val (const_val bs false_val)) y0s ys zs.
  Proof.
    cofix CoFix.
    intros [b bs] y0s ys zs Hsync Harrow.
    apply LCS.arrow_aligned in Hsync as [Hsync1 [Hsync2 Hsync3]]; [|auto].
    destruct b; inv Hsync1; inv Hsync2; inv Hsync3; inv Harrow.
    - rewrite const_val_Cons, hold_Cons.
      constructor.
      rewrite hold_const.
      clear - H0 H1 H2 H3. revert bs vs vs0 vs1 H1 H2 H3 H0.
      cofix CoFix. intros * Hsync1 Hsync2 Hsync3 Harrow.
      destruct bs as [[|] bs]; inv Hsync1; inv Hsync2; inv Hsync3; inv Harrow.
      1,2:rewrite const_val_Cons; constructor; auto.
    - rewrite const_val_Cons, hold_Cons.
      constructor; auto.
  Qed.

  Corollary arrow_init_stream_ite : forall bs y0s ys zs,
      (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
      arrow y0s ys zs ->
      ite (init_stream bs) y0s ys zs.
  Proof.
    intros * Hsync Harrow.
    eapply arrow_ite in Harrow; eauto.
    unfold init_stream.
    rewrite const_val_const. rewrite sem_false_const. eassumption.
  Qed.

  Lemma ac_hold : forall c vs,
      abstract_clock (hold c vs) ≡ abstract_clock vs.
  Proof.
    cofix CoFix. intros c [v vs].
    rewrite hold_Cons.
    destruct v; constructor; simpl; auto.
  Qed.

  Lemma init_stream_ac : forall bs,
      abstract_clock (init_stream bs) ≡ bs.
  Proof.
    intros bs.
    unfold init_stream.
    rewrite ac_hold, <- ac_const. 1,2:reflexivity.
  Qed.

  (** *** Additional stuff *)

  Definition st_vars (st : fresh_st (type * clock * bool)) : list (ident * (type * clock)) :=
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
    eapply Facts.st_valid_after_NoDupMembers in Hvalid; eauto.
    rewrite fst_NoDupMembers, map_app, <- st_ids_st_vars; auto.
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

  Definition init_eqs_valids bs H (st : fresh_st (Op.type * clock * bool)) :=
    Forall (fun '(id, ck) =>
              (exists bs', sem_clock H bs ck bs' /\
                      sem_var H id (init_stream bs'))) (st_inits st).

  Definition hist_st (vars : list (ident * clock)) b H st :=
    Env.dom H (map fst vars++st_ids st) /\
    init_eqs_valids b H st /\
    LCS.sc_var_inv' (vars++st_clocks' st) H b.

  Fact fresh_ident_init_eqs : forall vars b ty ck id v H st st',
      st_valid_after st (PSP.of_list vars) ->
      Env.dom H (vars ++ st_ids st) ->
      fresh_ident norm2 ((ty, ck), false) st = (id, st') ->
      init_eqs_valids b H st ->
      init_eqs_valids b (Env.add id v H) st'.
  Proof with auto.
    intros * Hvalid Hdom Hfresh Hinits.
    assert (~In id (st_ids st)) as Hnin by (eapply Facts.fresh_ident_nIn in Hfresh; eauto).
    assert (Env.refines eq H (Env.add id v H)) as Href.
    { eapply fresh_ident_refines' in Hfresh; eauto. }
    eapply fresh_ident_false_st_inits in Hfresh.
    unfold init_eqs_valids in *. rewrite Hfresh.
    solve_forall. destruct H1 as [bs' [? ?]].
    exists bs'; split.
    - eapply LCS.sem_clock_refines; eauto.
    - eapply sem_var_refines; eauto.
  Qed.

  Fact fresh_ident_hist_st : forall vars b ty ck id v H st st',
      st_valid_after st (PSP.of_list (map fst vars)) ->
      sem_clock H b ck (abstract_clock v) ->
      fresh_ident norm2 ((ty, ck), false) st = (id, st') ->
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

  Module Import CIStr := CoindIndexedFun Op OpAux CStr IStr.

  Fact sem_clock_when : forall H bs bs' bs'' cs ck id ckb c,
      sem_clock H bs ck bs' ->
      sem_clock H bs (Con ck id ckb) bs'' ->
      sem_var H id cs ->
      when ckb (const bs' c) cs (const bs'' c).
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
      exists (sem_const c). exists c0. repeat split; auto using const_true.
    - left.
      repeat split; auto using const_false.
    - right. left.
      exists (sem_const c). exists c0. repeat split; auto using const_true, const_false.
      destruct b; auto.
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

  Fact init_var_for_clock_sem : forall G vars bs H ck bs' x eqs' st st',
      sem_clock H bs ck bs' ->
      st_valid_after st (PSP.of_list (map fst vars)) ->
      hist_st vars bs H st ->
      init_var_for_clock ck st = (x, eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_after st' (PSP.of_list (map fst vars)) /\
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
      destruct Histst as [_ [Hvalids _]]. unfold init_eqs_valids in Hvalids.
      rewrite Forall_forall in Hvalids.
      eapply find_some in Hfind. destruct p as [[ty' ck'] isinit].
      repeat rewrite Bool.andb_true_iff in Hfind. destruct Hfind as [Hin [[Hisinit Hcl] Hty]].
      rewrite OpAux.type_eqb_eq in Hty.
      rewrite Clocks.clock_eqb_eq in Hcl. subst.
      assert (In (x, ck) (st_inits st')) as Hin'.
      { unfold st_inits. simpl_In. exists bool_type. simpl_In. exists true.
        rewrite filter_In. rewrite equiv_decb_refl; auto. }
      apply Hvalids in Hin' as [bs'' [? ?]].
      eapply sem_clock_det in Hsemc; eauto. rewrite <- Hsemc; auto.
    - (* We need to introduce a new init equation to the history and state,
         and prove its properties *)
      clear Hfind.
      destruct (fresh_ident _ _) eqn:Hident. repeat inv_bind.
      assert (st_valid_after st' (PSP.of_list (map fst vars))) as Hvalid1 by eauto.
      remember (Env.add x (init_stream bs') H) as H'.
      assert (Env.refines eq H H') as Href1 by (destruct Histst; eapply fresh_ident_refines' in Hident; eauto).
      assert (hist_st vars bs H' st') as Histst1.
      { destruct Histst as [H1 [H2 H3]].
        repeat split.
        - eapply fresh_ident_dom in Hident...
        - unfold init_eqs_valids in *.
          erewrite fresh_ident_true_st_inits...
          constructor.
          + exists bs'. split; [eapply LCS.sem_clock_refines|]; eauto.
            rewrite HeqH'. econstructor. eapply Env.add_1.
            1,2:reflexivity.
          + solve_forall.
            destruct H2 as [bs'' [? ?]].
            exists bs''. split; [eapply LCS.sem_clock_refines|eapply sem_var_refines]; eauto.
        - unfold st_clocks', LCS.sc_var_inv' in *.
          erewrite fresh_ident_anns; simpl; eauto.
          rewrite <- Permutation_middle; constructor; simpl.
          + exists (init_stream bs'). split.
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
        apply Seq with (ss:=[[(init_stream bs')]]); simpl; repeat constructor.
        * eapply Sfby with (s0ss:=[[(const bs' true_const)]]) (sss:=[[(const bs' false_const)]]); repeat constructor.
          -- apply add_whens_sem_exp. eauto using LCS.sem_clock_refines.
          -- apply add_whens_sem_exp. eauto using LCS.sem_clock_refines.
          -- unfold init_stream.
             repeat rewrite const_val_const; subst.
             rewrite <- sem_true_const. apply hold_fby.
             rewrite <- const_val_const. apply const_aligned.
        * econstructor. 2:reflexivity.
          rewrite HeqH'. apply Env.add_1. reflexivity.
  Qed.

  Hint Constructors LCS.sem_exp_anon.
  Lemma normalized_lexp_sem_sem_anon : forall G H b e vs,
      normalized_lexp e ->
      sem_exp G H b e vs ->
      LCS.sem_exp_anon G H b e vs.
  Proof.
    intros * Hnormed Hsem. revert vs Hsem.
    induction Hnormed; intros; inv Hsem; eauto.
    inv H8; inv H4. eauto.
  Qed.

  Lemma normalized_cexp_sem_sem_anon : forall G H b e vs,
      normalized_cexp e ->
      sem_exp G H b e vs ->
      LCS.sem_exp_anon G H b e vs.
  Proof.
    intros * Hnormed Hsem. revert vs Hsem.
    induction Hnormed; intros.
    - inv Hsem. inv H9; inv H4. inv H10; inv H5.
      econstructor; eauto.
    - inv Hsem. inv H10; inv H5. inv H11; inv H6.
      econstructor; eauto.
      eapply normalized_lexp_sem_sem_anon; eauto.
    - eapply normalized_lexp_sem_sem_anon; eauto.
  Qed.

  Lemma unnested_equation_sem_sem_anon : forall G env H b equ,
      unnested_equation equ ->
      wc_equation G env equ ->
      sem_equation G H b equ ->
      LCS.sem_equation_anon G H b equ.
  Proof.
    intros * Hnormed Hwc Hsem.
    inv Hnormed; inv Hsem; intros.
    - inv H6; inv H5.
      inv H3.
      repeat (econstructor; eauto).
      + eapply Forall2_impl_In; [|eauto].
        intros. eapply normalized_lexp_sem_sem_anon; eauto. eapply Forall_forall; eauto.
      + destruct Hwc as (_&Hcks&_); simpl in *; rewrite app_nil_r in *.
        rewrite Forall2_map_2, Forall2_swap_args in Hcks.
        eapply Forall2_trans_ex in H7; [|eauto].
        eapply Forall2_impl_In; [|eauto]. intros (?&?&?) ? ? ? (?&?&?&?).
        destruct o; simpl in *; subst; auto.
    - inv H6; inv H5.
      inv H3.
      do 3 (econstructor; eauto).
      + eapply Forall2_impl_In; [|eauto].
        intros. eapply normalized_lexp_sem_sem_anon; eauto. eapply Forall_forall; eauto.
      + eapply normalized_lexp_sem_sem_anon; eauto.
      + destruct Hwc as (_&Hcks&_); simpl in *; rewrite app_nil_r in *.
        rewrite Forall2_map_2, Forall2_swap_args in Hcks.
        eapply Forall2_trans_ex in H7; [|eauto].
        eapply Forall2_impl_In; [|eauto]. intros (?&?&?) ? ? ? (?&?&?&?).
        destruct o; simpl in *; subst; auto.
    - inv H7; inv H6.
      inv H4. inv H10; inv H6. inv H12; inv H7.
      repeat econstructor; eauto.
      1,2:eapply normalized_lexp_sem_sem_anon; eauto.
    - inv H7; inv H6.
      inv H4. inv H10; inv H6. inv H12; inv H7.
      repeat econstructor; eauto.
      1,2:eapply normalized_lexp_sem_sem_anon; eauto.
    - inv H6; inv H5.
      repeat econstructor; eauto.
      eapply normalized_cexp_sem_sem_anon; eauto.
  Qed.

  Corollary normalized_equation_sem_sem_anon : forall G env H b equ out,
      normalized_equation out equ ->
      wc_equation G env equ ->
      sem_equation G H b equ ->
      LCS.sem_equation_anon G H b equ.
  Proof.
    intros.
    eapply unnested_equation_sem_sem_anon; eauto.
    eapply normalized_eq_unnested_eq; eauto.
  Qed.

  Lemma sc_lexp :  forall G H bs env e s ck,
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

  Lemma sc_cexp : forall G env H b e vs,
      wc_global G ->
      LCS.sc_nodes G ->
      NoDupMembers env ->
      LCS.sc_var_inv' env H b ->
      normalized_cexp e ->
      wc_exp G env e ->
      sem_exp G H b e vs ->
      Forall2 (sem_clock H b) (clockof e) (map abstract_clock vs).
  Proof.
    intros * HwcG Hsc Hnd Hinv Hnormed Hwc Hsem.
    eapply LCS.sc_exp; eauto.
    eapply normalized_cexp_sem_sem_anon; eauto.
  Qed.

  Fact fby_iteexp_sem : forall G vars bs H e0 e ty nck y0 y z e' eqs' st st',
      wc_global G ->
      LCS.sc_nodes G ->
      NoDupMembers vars ->
      wc_env (idck vars++st_clocks' st) ->
      normalized_lexp e0 ->
      clockof e0 = [fst nck] ->
      wt_exp G (idty vars++st_tys' st) e0 ->
      wc_exp G (idck vars++st_clocks' st) e0 ->
      sem_exp G H bs e0 [y0] ->
      sem_exp G H bs e [y] ->
      fby y0 y z ->
      st_valid_after st (PSP.of_list (map fst vars)) ->
      hist_st (idck vars) bs H st ->
      fby_iteexp e0 e (ty, nck) st = (e', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_after st' (PSP.of_list (map fst vars)) /\
          hist_st (idck vars) bs H' st' /\
          sem_exp G H' bs e' [z] /\
          Forall (sem_equation G H' bs) eqs').
  Proof with eauto.
    intros * HwcG Hsc Hndup Hwenv Hnormed Hck Hwt Hwc Hsem0 Hsem Hfby Hvalid Histst Hiteexp.
    destruct nck as [ck ?]; simpl in *.
    unfold fby_iteexp in Hiteexp; repeat inv_bind.
    eapply sc_lexp with (env:=vars++st_vars st) in Hnormed...
    3,6:rewrite idck_app... 4:rewrite idty_app...
    2:{ eapply st_valid_after_NoDupMembers in Hvalid... }
    2:{ destruct Histst as [_ [_ ?]]. rewrite idck_app, <- st_clocks'_st_vars; auto. }
    eapply init_var_for_clock_sem with (G:=G) in H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]...
    2: rewrite map_fst_idck...
    remember (abstract_clock y0) as bs'.
    remember (hold (Op.sem_const (Op.init_type ty)) y) as y'.
    remember (Env.add x2 y' H') as H''.
    assert (Env.refines eq H' H'') by (destruct Histst1; eapply fresh_ident_refines' in H1; eauto).
    assert (hist_st (idck vars) bs H'' st') as Histst2.
    { eapply fresh_ident_hist_st in H1; eauto.
      rewrite HeqH''...
      rewrite Heqy', ac_hold.
      1: eapply LCS.sem_clock_refines; eauto.
      rewrite LCS.ac_fby2, <- LCS.ac_fby1, <- Heqbs'; eauto. }
    exists H''. repeat (split; eauto); try constructor.
    + etransitivity; eauto.
    + rewrite map_fst_idck in Hvalid1...
    + eapply Site with (s:=(init_stream bs')) (ts:=[[y0]]) (fs:=[[y']]); repeat constructor.
      * eapply sem_var_refines...
      * eapply sem_exp_refines; [| eauto]. etransitivity...
      * econstructor.
        rewrite HeqH''. eapply Env.add_1. 1,2:reflexivity.
      * subst. eapply fby_init_stream_ite...
        left. apply ac_aligned.
    + apply Seq with (ss:=[[y']]); repeat constructor.
      * eapply Sfby with (s0ss:=[[const bs' (init_type ty)]]) (sss:=[[y]]); repeat constructor.
        -- eapply add_whens_sem_exp...
           eapply LCS.sem_clock_refines; [|eauto]. etransitivity...
        -- eapply sem_exp_refines; [| eauto]. etransitivity...
        -- rewrite Heqy'.
           rewrite const_val_const.
           eapply hold_fby.
           eapply LCS.fby_aligned in Hfby as [_ [? _]]; eauto.
           left. rewrite Heqbs'. apply ac_aligned.
      * econstructor.
        rewrite HeqH''. apply Env.add_1. 1,2:reflexivity.
    + solve_forall. eapply sem_equation_refines...
  Qed.

  Fact arrow_iteexp_sem : forall G vars bs H e0 e ty nck y0 y z e' eqs' st st',
      wc_global G ->
      LCS.sc_nodes G ->
      NoDupMembers vars ->
      wc_env (idck vars++st_clocks' st) ->
      normalized_lexp e0 ->
      clockof e0 = [fst nck] ->
      wt_exp G (idty vars++st_tys' st) e0 ->
      wc_exp G (idck vars++st_clocks' st) e0 ->
      sem_exp G H bs e0 [y0] ->
      sem_exp G H bs e [y] ->
      arrow y0 y z ->
      st_valid_after st (PSP.of_list (map fst vars)) ->
      hist_st (idck vars) bs H st ->
      arrow_iteexp e0 e (ty, nck) st = (e', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_after st' (PSP.of_list (map fst vars)) /\
          hist_st (idck vars) bs H' st' /\
          sem_exp G H' bs e' [z] /\
          Forall (sem_equation G H' bs) eqs').
  Proof with eauto.
    intros * HwcG Hsc Hndup Hwenv Hnormed1 Hck Hwt Hwc Hsem0 Hsem Harrow Hvalid Histst Hiteexp.
    destruct nck as [ck ?]; simpl in *.
    unfold arrow_iteexp in Hiteexp. repeat inv_bind.
    eapply sc_lexp with (env:=vars++st_vars st) in Hnormed1...
    3,6:rewrite idck_app... 4:rewrite idty_app...
    2:{ eapply st_valid_after_NoDupMembers in Hvalid... }
    2:{ destruct Histst as [_ [_ ?]]. rewrite idck_app, <- st_clocks'_st_vars; auto. }

    eapply init_var_for_clock_sem with (G:=G) in H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]...
    2: rewrite map_fst_idck...
    remember (abstract_clock y0) as bs'.
    exists H'. repeat (split; auto).
    + rewrite map_fst_idck in Hvalid1...
    + eapply Site with (s:=(init_stream bs')) (ts:=[[y0]]) (fs:=[[y]]); repeat constructor...
      * eapply sem_exp_refines...
      * eapply sem_exp_refines...
      * subst. eapply arrow_init_stream_ite...
        left. apply ac_aligned.
  Qed.

  Fact fby_equation_sc_exp : forall G H vars bs e0 ck s0s ss vs,
      wc_global G ->
      LCS.sc_nodes G ->
      NoDupMembers vars ->
      wc_env (idck vars) ->
      normalized_lexp e0 ->
      wt_exp G (idty vars) e0 ->
      wc_exp G (idck vars) e0 ->
      clockof e0 = [ck] ->
      sem_exp G H bs e0 [s0s] ->
      fby s0s ss vs ->
      LCS.sc_var_inv' (idck vars) H bs ->
      sem_clock H bs ck (abstract_clock vs).
  Proof with eauto.
    intros * HwG Hsc Hndup Hwenv Hnormed Hwt Hwc Hck Hsem Hfby Hinv.
    eapply sc_lexp in Hnormed. 2-10:eauto.
    rewrite LCS.ac_fby1 in Hnormed; eauto.
  Qed.

  Fact fby_equation_sem : forall G vars bs H to_cut equ eqs' st st',
      wc_global G ->
      LCS.sc_nodes G ->
      NoDupMembers vars ->
      wc_env (idck vars++st_clocks' st) ->
      unnested_equation equ ->
      wt_equation G (idty vars++st_tys' st) equ ->
      wc_equation G (idck vars++st_clocks' st) equ ->
      sem_equation G H bs equ ->
      st_valid_after st (PSP.of_list (map fst vars)) ->
      hist_st (idck vars) bs H st ->
      fby_equation to_cut equ st = (eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_after st' (PSP.of_list (map fst vars)) /\
          hist_st (idck vars) bs H' st' /\
          Forall (sem_equation G H' bs) eqs').
  Proof with eauto.
    intros * HwcG Hsc Hndup Hwcenv Hunt Hwt Hwc Hsem Hvalid Hhistst Hfby.
    inv_fby_equation Hfby to_cut equ; try destruct x2 as (ty&ck&name).
    - (* constant fby *)
      destruct PS.mem; repeat inv_bind.
      + inv Hsem. inv H6; inv H5.
        simpl in H7; rewrite app_nil_r in H7. inv H7; inv H6.
        assert(Hsem':=H3). inv H3.
        inv H9; inv H6. inv H11; inv H7.
        simpl in *. repeat rewrite app_nil_r in *.
        inv H12; inv H9.
        destruct Hwt as [Hwt _]. apply Forall_singl in Hwt. inv Hwt.
        apply Forall_singl in H7.
        destruct Hwc as [Hwc _]. apply Forall_singl in Hwc; inv Hwc.
        apply Forall_singl in H13. rewrite Forall2_eq in H15; simpl in H15; rewrite app_nil_r in H15.

        remember (Env.add x2 y0 H) as H'.
        assert (Env.refines eq H H') as Href.
        { destruct Hhistst as [Hdom _]; rewrite map_fst_idck in Hdom.
          eapply fresh_ident_refines' in H0... }
        assert (hist_st (idck vars) bs H' st') as Histst1.
        { eapply fresh_ident_hist_st in H0...
          + rewrite HeqH'...
          + rewrite map_fst_idck...
          + eapply fby_equation_sc_exp with (vars:=vars++st_vars st) (e0:=x0)...
            * eapply st_valid_after_NoDupMembers in Hvalid...
            * rewrite idck_app; eauto.
            * clear - Hunt. inv Hunt; auto. inv H0; inv H.
            * rewrite idty_app. rewrite st_tys'_st_vars in *. repeat solve_incl.
            * rewrite idck_app. rewrite st_clocks'_st_vars in *. repeat solve_incl.
            * destruct Hhistst as [_ [_ ?]]. rewrite idck_app, <- st_clocks'_st_vars...
        }
        exists H'. repeat (split; eauto).
        repeat constructor; auto.
        * eapply Seq with (ss:=[[y0]]); simpl; repeat constructor.
          2:eapply sem_var_refines; eauto.
          rewrite HeqH'. econstructor. eapply Env.add_1. 1,2:reflexivity.
        * eapply Seq with (ss:=[[y0]]); simpl; repeat constructor.
          eapply sem_exp_refines; eauto.
          rewrite HeqH'. econstructor. eapply Env.add_1. 1,2:reflexivity.
      + exists H. repeat (split; eauto).
    - (* fby *)
      destruct Hwt as [Hwt _]. apply Forall_singl in Hwt; inv Hwt.
      apply Forall_singl in H4.
      destruct Hwc as [Hwc _]. apply Forall_singl in Hwc; inv Hwc.
      apply Forall_singl in H9. rewrite Forall2_eq in H11; simpl in H11; rewrite app_nil_r in H11.
      inv Hsem. inv H16; inv H15. simpl in *; rewrite app_nil_r in *. inv H17; inv H16.
      inv H3. inv H19; inv H16. inv H21; inv H17.
      simpl in *; repeat rewrite app_nil_r in *. inv H22; inv H19.
      assert (normalized_lexp x0).
      { clear - Hunt. inv Hunt; eauto. inv H0; inv H. }
      eapply fby_iteexp_sem with (nck:=(ck, name)) in H0 as [H' [Href1 [Hvalid1 [Hhistst1 [Hsem' Hsem'']]]]]...
      exists H'. repeat (split; eauto).
      constructor; auto.
      eapply Seq with (ss:=[[y0]]); simpl; repeat constructor; auto.
      eapply sem_var_refines; eauto.
    - (* arrow *)
      destruct Hwt as [Hwt _]. apply Forall_singl in Hwt; inv Hwt.
      apply Forall_singl in H4.
      destruct Hwc as [Hwc _]. apply Forall_singl in Hwc; inv Hwc.
      apply Forall_singl in H9. simpl in *; rewrite app_nil_r, Forall2_eq in H11.
      inv Hsem. inv H16; inv H15.
      inv H3. inv H19; inv H15. inv H21; inv H16.
      simpl in *; repeat rewrite app_nil_r in *. inv H17; inv H18. inv H22; inv H19.
      inv Hunt. 2:(inv H2; inv H1).
      eapply arrow_iteexp_sem with (nck:=(ck, name)) in H0 as [H' [Href [Hvalid1 [Hhistst1 [Hsem1 Hsem1']]]]]; eauto.
      exists H'. repeat (split; auto).
      constructor; auto.
      econstructor; eauto.
      constructor; auto. eapply sem_var_refines; eauto.
    - (* other *) exists H. repeat (split; eauto).
  Qed.

  Fact fby_equations_sem : forall G vars bs to_cut eqs eqs' H st st',
      wc_global G ->
      LCS.sc_nodes G ->
      NoDupMembers vars ->
      wc_env (idck vars++st_clocks' st) ->
      Forall unnested_equation eqs ->
      Forall (wt_equation G (idty vars++st_tys' st)) eqs ->
      Forall (wc_equation G (idck vars++st_clocks' st)) eqs ->
      Forall (sem_equation G H bs) eqs ->
      st_valid_after st (PSP.of_list (map fst vars)) ->
      hist_st (idck vars) bs H st ->
      fby_equations to_cut eqs st = (eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          Forall (sem_equation G H' bs) eqs').
  Proof with eauto.
    induction eqs; intros * HwcG Hsc Hndup Hwcenv Hunt Hwt Hwc Hsem Hvalid Hhistst Hfby;
      unfold fby_equations in Hfby; simpl in *; repeat inv_bind.
    - exists H...
    - assert (fby_equations to_cut eqs x1 = (concat x2, st')) as Hnorm.
      { unfold fby_equations; repeat inv_bind.
        repeat eexists; eauto. repeat inv_bind; auto. }
      inv Hunt. inv Hwt. inv Hwc. inv Hsem.
      assert (st_follows st x1) as Hfollows by (eapply fby_equation_st_follows in H0; eauto).
      assert (wc_env (idck vars ++ st_clocks' x1)) as Hwenv1.
      { eapply fby_equation_wc_eq in H0 as [_ ?]... }
      eapply fby_equation_sem in H0 as [H' [Href1 [Hvalid1 [Hhistst1 Hsem1]]]]...
      assert (Forall (sem_equation G H' bs) eqs) as Hsem'.
      { solve_forall. eapply sem_equation_refines... } clear H11.
      eapply IHeqs in Hnorm as [H'' [Href Hsem2]]...
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

  Fact init_st_hist_st : forall b H n,
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

  Fact normfby_node_sem_equation : forall G H to_cut n Hwl Hpref ins,
      wc_global G ->
      LCS.sc_nodes G ->
      unnested_node n ->
      wt_node G n ->
      wc_node G n ->
      LCA.node_causal n ->
      Env.dom H (map fst (n_in n ++ n_vars n ++ n_out n)) ->
      Forall2 (sem_var H) (idents (n_in n)) ins ->
      Forall2 (fun xc => sem_clock H (clocks_of ins) (snd xc)) (idck (n_in n)) (map abstract_clock ins) ->
      Forall (sem_equation G H (clocks_of ins)) (n_eqs n) ->
      exists H' : Env.t (Stream value),
        Env.refines eq H H' /\ Forall (sem_equation G H' (clocks_of ins)) (n_eqs (normfby_node to_cut n Hwl Hpref)).
  Proof with eauto.
    intros * HwcG HscG Hunt Hwt Hwc Hcaus Hdom Hvars Hsemclock Hsem.
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
    - destruct Hwt as [_ [_ [_ ?]]]...
    - eapply init_st_valid.
      + eapply norm2_not_in_norm1_prefs.
      + rewrite PS_For_all_Forall, ps_of_list_ps_to_list_Perm...
        pose proof (n_good n) as (Good&_).
        rewrite <- Hpref.
        eapply Forall_incl; eauto.
        apply incl_map, incl_appr', incl_appr', incl_appl; auto.
    - subst. eapply init_st_hist_st...
      eapply LCS.sc_node_sc_var_inv'; eauto.
      + eapply Forall_impl_In; [|eauto]. intros.
        unfold unnested_node in Hunt.
        destruct Hwc as (_&_&_&Hwc).
        eapply unnested_equation_sem_sem_anon; eauto. 1,2:eapply Forall_forall; eauto.
  Qed.

  Lemma normfby_node_eq : forall G G' f n Hwl Hpref ins outs to_cut,
      Forall2 (fun n n' => n_name n = n_name n') G G' ->
      global_iface_eq G G' ->
      LCS.global_sc_refines G G' ->
      wt_global (n::G) ->
      wc_global (n::G) ->
      wt_global G' ->
      wc_global G' ->
      Ordered_nodes (n::G) ->
      Ordered_nodes ((normfby_node to_cut n Hwl Hpref)::G') ->
      Forall LCA.node_causal (n::G) ->
      Forall LCA.node_causal G' ->
      sem_node (n::G) f ins outs ->
      LCS.sem_clock_inputs (n::G) f ins ->
      sem_node ((normfby_node to_cut n Hwl Hpref)::G') f ins outs.
  Proof with eauto.
    intros * Hnames Hiface Href HwtG HwcG HwtG' HwcG' Hord1 Hord2 Hcaus1 Hcaus2 Hsem Hinputs.
    assert (LCS.sc_nodes G) as HscG.
    { inv HwtG. inv HwcG. inv Hord1. inv Hcaus1. eapply LCS.l_sem_node_clock... }
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
    assert (LCS.sc_nodes G') as HscG'.
    { inv HwtG''. inv HwcG''. inv Hord2. eapply LCS.l_sem_node_clock... }

    inv Hsem; assert (Hfind:=H0); simpl in H0. destruct (ident_eqb (n_name n) f) eqn:Hident.
    - inv H0. inv HwcG.
      (*The semantics of equations can be given according to G only *)
      eapply Forall_sem_equation_global_tl in H3; eauto.
      2:{ inv Hord1. intro contra. apply H9 in contra as [? _]; auto. }
      (* New env H' (restrict H) and its properties *)
      eapply LCS.sem_node_restrict in H3 as (Hdom&Hins'&Houts'&Heqs'); eauto.
      2:destruct H6 as (?&?&?&?); auto.
      remember (Env.restrict H (List.map fst (n_in n0++n_vars n0++n_out n0))) as H'.
      clear H H1 H2 HeqH'.

      inversion_clear HwtG. rename H0 into Hwt.
      inv Hcaus1.

      eapply normfby_node_sem_equation with (to_cut:=to_cut) (Hwl:=Hwl) in Heqs' as (H''&Hre'&Heqs'')...
      assert (Forall2 (sem_var H'') (idents (n_in n0)) ins) as Hins''.
      { repeat rewrite_Forall_forall. eapply sem_var_refines... }
      eapply Snode with (H:=H''); simpl. 5:reflexivity.
      + rewrite Hident; reflexivity.
      + simpl; eauto.
      + simpl. repeat rewrite_Forall_forall. eapply sem_var_refines...
      + clear Hins' Houts' Hdom.
        apply Forall_sem_equation_global_tl'...
        eapply find_node_not_Is_node_in in Hord2...
        simpl. rewrite ident_eqb_refl...
        assert (normalized_node (normfby_node to_cut n0 Hwl Hpref)) as Hunt'.
        { eapply normfby_node_normalized_node. }
        assert (wc_node G (normfby_node to_cut n0 Hwl Hpref)) as Hwc'.
        { eapply normfby_node_wc; eauto. }
        assert (Forall (LCS.sem_equation_anon G H'' (clocks_of ins)) (n_eqs (normfby_node to_cut n0 Hwl Hpref))) as Heqs'''.
        { eapply Forall_impl_In; [|eapply Heqs''].
          intros. eapply normalized_equation_sem_sem_anon; eauto.
          eapply Forall_forall in Hunt'; eauto.
          destruct Hwc' as (_&_&_&Hwc'). eapply Forall_forall in Hwc'; eauto.
        } clear Heqs''.
        assert (LCS.sc_var_inv' (idck (n_in (normfby_node to_cut n0 Hwl Hpref) ++
                                            n_vars (normfby_node to_cut n0 Hwl Hpref) ++
                                            n_out (normfby_node to_cut n0 Hwl Hpref))) H'' (clocks_of ins)) as Hinv.
        { destruct Hinputs as (H'''&?&Hfind'&?&Hcks).
          rewrite Hfind in Hfind'; inv Hfind'.
          eapply LCS.sc_node_sc_var_inv'; eauto.
          + eapply normfby_node_causal; eauto.
          + eapply LCS.sem_clocks_det' in Hcks; eauto. destruct H6; auto.
        }
        eapply Forall_impl_In; [|eauto]. intros.
        eapply LCS.sc_ref_sem_equation, LCS.sem_equation_anon_sem_equation in H2; eauto.
        2:destruct Hwc' as (_&_&_&Hwc'); eapply Forall_forall in Hwc'; eauto.
        rewrite NoDupMembers_idck, fst_NoDupMembers. apply node_NoDup.
      + destruct Hinputs as (H''&?&?&?&?).
        rewrite H0 in Hfind. inv Hfind.
        destruct H6 as (?&_).
        eapply LCS.sem_clocks_det' in H8; eauto.
    - specialize (Href f ins outs).
      rewrite ident_eqb_neq in Hident.
      eapply sem_node_cons'...
      apply Href. split. 1:rewrite <- LCS.sem_clock_inputs_cons in Hinputs...
      econstructor...
      eapply Forall_impl_In; [| eauto]. intros eq Hin Hsem.
      eapply sem_equation_global_tl...
      eapply find_node_later_not_Is_node_in in Hord1...
      intro Hisin. apply Hord1. rewrite Is_node_in_Exists. rewrite Exists_exists.
      eexists...
  Qed.

  Fact iface_eq_sem_clocks_input : forall G G' f ins,
      global_iface_eq G G' ->
      LCS.sem_clock_inputs G f ins ->
      LCS.sem_clock_inputs G' f ins.
  Proof.
    intros * Hglob [H [n [Hfind [Hinputs Hsem]]]].
    specialize (Hglob f). rewrite Hfind in Hglob; inv Hglob.
    destruct H2 as (Hname&_&Hins&_).
    exists H. exists sy. repeat split; auto; congruence.
  Qed.

  Fact normfby_global_names' : forall G Hwl Hprefs,
      Forall2 (fun n n' => n_name n = n_name n') G (normfby_global G Hwl Hprefs).
  Proof.
    intros.
    specialize (Ordered.normfby_global_names G Hwl Hprefs) as Hnames.
    rewrite <- Forall2_eq, Forall2_swap_args in Hnames.
    solve_forall.
  Qed.

  Lemma normfby_global_refines : forall G Hunt Hprefs,
      wt_global G ->
      wc_global G ->
      Forall LCA.node_causal G ->
      LCS.global_sc_refines G (normfby_global G Hunt Hprefs).
  Proof with eauto.
    intros G Hunt. specialize (normfby_global_eq G Hunt) as Heq.
    induction G; intros * Hwt Hwc Hcaus; simpl.
    - apply LCS.global_sc_ref_nil.
    - apply LCS.global_sc_ref_cons with (f:=n_name a)...
      + eapply wt_global_ordered_nodes.
        eapply Typing.normfby_global_wt in Hwt; eauto.
      + inv Hwt; inv Hwc; inv Hcaus.
        eapply IHG... eapply normfby_global_eq...
      + intros ins outs Hsem. destruct Hsem as [Hinputs Hsem]. split.
        * eapply iface_eq_sem_clocks_input...
        * eapply normfby_node_eq...
          -- apply normfby_global_names'.
          -- apply normfby_global_eq.
          -- inv Hwt; inv Hwc; inv Hcaus.
             eapply IHG... eapply normfby_global_eq...
          -- inv Hwt. eapply normfby_global_wt...
          -- inv Hwc. eapply normfby_global_wc...
          -- eapply wt_global_ordered_nodes.
             eapply normfby_global_wt in Hwt...
          -- inv Hwc. inv Hcaus.
             eapply normfby_global_causal; eauto.
  Qed.

  Corollary normfby_global_sem : forall G Hunt Hprefs f ins outs,
      wt_global G ->
      wc_global G ->
      Ordered_nodes G ->
      Forall LCA.node_causal G ->
      sem_node G f ins outs ->
      LCS.sem_clock_inputs G f ins ->
      sem_node (normfby_global G Hunt Hprefs) f ins outs.
  Proof.
    intros.
    eapply normfby_global_refines with (Hunt:=Hunt) in H; eauto.
    specialize (H f ins outs (conj H4 H3)) as [_ ?]; eauto.
  Qed.

  Corollary normfby_global_sem_clock_inputs : forall G Hwl Hprefs f ins,
      LCS.sem_clock_inputs G f ins ->
      LCS.sem_clock_inputs (normfby_global G Hwl Hprefs) f ins.
  Proof.
    intros.
    specialize (normfby_global_eq G Hwl Hprefs) as Heq.
    destruct H as [H [n' [Hfind [Hvars Hsem]]]].
    eapply global_iface_eq_find in Heq as [? [? [Hname [_ [Hin Hout]]]]]; eauto.
    exists H. exists x. repeat split; auto.
    1,2:congruence.
  Qed.

  (** ** Conclusion *)

  Theorem normalize_global_sem : forall G Hwl Hprefs G' f ins outs,
      wt_global G ->
      wc_global G ->
      sem_node G f ins outs ->
      LCS.sem_clock_inputs G f ins ->
      normalize_global G Hwl Hprefs = Errors.OK G' ->
      sem_node G' f ins outs.
  Proof with eauto.
    intros  * Hwt Hwc Hsem Hclocks Hnorm.
    unfold normalize_global in Hnorm. destruct (LCA.check_causality _) eqn:Hcaus; inv Hnorm.
    eapply normfby_global_sem.
    - eapply unnest_global_wt...
    - eapply unnest_global_wc...
    - eapply Ordered.unnest_global_ordered...
    - eapply LCA.check_causality_correct in Hcaus; eauto.
      + eapply wt_global_wl_global, unnest_global_wt...
    - eapply unnest_global_sem...
    - eapply unnest_global_sem_clock_inputs...
  Qed.

  Corollary normalize_global_sem_clock_inputs : forall G G' Hwl Hprefs f ins,
      LCS.sem_clock_inputs G f ins ->
      normalize_global G Hwl Hprefs = Errors.OK G' ->
      LCS.sem_clock_inputs G' f ins.
  Proof.
    intros * Hsc Hnorm.
    unfold normalize_global in Hnorm.
    destruct (LCA.check_causality _) eqn:Hcheck; inv Hnorm.
    apply normfby_global_sem_clock_inputs, unnest_global_sem_clock_inputs, Hsc.
  Qed.

  (** ** In addition : normalization only produces causal programs *)

  Lemma normalize_global_causal : forall G G' Hwl Hprefs,
      wc_global G ->
      normalize_global G Hwl Hprefs = Errors.OK G' ->
      Forall LCA.node_causal G'.
  Proof.
    intros * Hwc Hnorm.
    unfold normalize_global in Hnorm.
    apply Errors.bind_inversion in Hnorm as [? [H1 H2]]. inv H2.
    eapply normfby_global_causal.
    2:apply LCA.check_causality_correct in H1; eauto.
    1,2:eapply unnest_global_wc in Hwc; eauto.
  Qed.

End CORRECTNESS.

Module CorrectnessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (CStr : COINDSTREAMS Op OpAux)
       (IStr : INDEXEDSTREAMS Op OpAux)
       (Syn : LSYNTAX Ids Op)
       (LCA : LCAUSALITY Ids Op Syn)
       (Ty : LTYPING Ids Op Syn)
       (Clo : LCLOCKING Ids Op Syn)
       (Lord : LORDERED Ids Op Syn)
       (Sem : LSEMANTICS Ids Op OpAux Syn Lord CStr)
       (LClockSem : LCLOCKSEMANTICS Ids Op OpAux Syn Clo LCA Lord CStr IStr Sem)
       (Norm : NORMALIZATION Ids Op OpAux Syn LCA)
       <: CORRECTNESS Ids Op OpAux CStr IStr Syn LCA Ty Clo Lord Sem LClockSem Norm.
  Include CORRECTNESS Ids Op OpAux CStr IStr Syn LCA Ty Clo Lord Sem LClockSem Norm.
End CorrectnessFun.
