From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

Require Import Omega.

From Velus Require Import Common Ident.
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
       (Import LClockSem : LCLOCKSEMANTICS Ids Op OpAux Syn Ty Cl LCA Ord CStr IStr Sem)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn LCA).

  Import Fresh Tactics.
  Module Import Typing := NTypingFun Ids Op OpAux Syn LCA Ty Norm.
  Module Import Clocking := NClockingFun Ids Op OpAux Syn LCA Cl Norm.
  Module Ordered := NOrderedFun Ids Op OpAux Syn LCA Ord Norm.
  Module Import Causality := NCausalityFun Ids Op OpAux Syn LCA Cl Norm.
  Import List.

  CoFixpoint default_stream : Stream OpAux.value :=
    absent ⋅ default_stream.

  Fact normalize_exp_sem_length : forall G vars e is_control es' eqs' st st',
      wt_exp G (vars++Typing.st_tys st) e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (fun e => forall v H b,
                  sem_exp G H b e v ->
                  length v = 1) es'.
  Proof.
    intros G vars e is_control es' eqs' st st' Hwt Hnorm.
    specialize (normalize_exp_numstreams _ _ _ _ _ _ Hnorm) as Hnumstreams.
    eapply normalize_exp_wt in Hnorm as [Hwt' _]; eauto.
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

  Fact normalize_reset_sem : forall G vars b e H v e' eqs' st st' reusable,
      sem_exp G H b e [v] ->
      st_valid_reuse st (PSP.of_list vars) reusable ->
      Env.dom H (vars++st_ids st) ->
      normalize_reset e st = (e', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list vars) reusable /\
          Env.dom H' (vars++st_ids st') /\
          sem_exp G H' b e' [v] /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros * Hsem Hvalid Histst Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind.
    - exists H. repeat (split; auto).
    - destruct (List.hd _ _) as [? [? ?]] eqn:Heqann; repeat inv_bind.
      assert (st_follows st st') as Hfollows by eauto.
      assert (st_valid_after st (PSP.of_list vars)) as Hvalid' by eauto.
      remember (Env.add x v H) as H'.
      assert (Env.dom H' (vars++st_ids st')).
      { subst. eapply fresh_ident_dom in H0; eauto. }
      assert (Env.refines eq H H') as Href.
      { eapply fresh_ident_refines with (st0:=st)... }
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

  Fact normalize_fby_sem : forall G H bs e0s es anns s0s ss os,
      length e0s = length anns ->
      length es = length anns ->
      Forall2 (fun e s => sem_exp G H bs e [s]) e0s s0s ->
      Forall2 (fun e s => sem_exp G H bs e [s]) es ss ->
      Forall3 fby s0s ss os ->
      Forall2 (fun e s => sem_exp G H bs e [s]) (normalize_fby e0s es anns) os.
  Proof with eauto.
    intros * Hlen1 Hlen2 Hsem1 Hsem2 Hfby.
    unfold normalize_fby.
    repeat rewrite_Forall_forall. 1:solve_length.
    repeat simpl_length. repeat simpl_nth. Unshelve. 2:exact ((hd_default [], hd_default []), default_ann).
    destruct (nth n (combine _ _)) as [[e0 e] ?] eqn:Hnth. repeat simpl_nth.
    eapply Sfby.
    - repeat constructor...
    - repeat constructor...
    - simpl. repeat constructor...
      Unshelve. 1,2:exact default_stream.
  Qed.

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
                   normalize_exp is_control e st = (es', eqs', st') ->
                   (exists H',
                       Env.refines eq H H' /\
                       st_valid_reuse st' (PSP.of_list vars) reusable /\
                       Env.dom H' (vars++st_ids st') /\
                       Forall2 (fun e v => sem_exp G H' b e [v]) es' v /\
                       Forall (sem_equation G H' b) eqs')) es vs ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
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
        assert (length x = numstreams a) as Hlength1 by (eapply normalize_exp_length; eauto).
        assert (length y = numstreams a) as Hlength2 by (eapply sem_exp_numstreams; eauto).
        solve_forall.
        eapply sem_exp_refines; eauto.
      + apply Forall_app. split...
        solve_forall. eapply sem_equation_refines...
  Qed.

  Hint Constructors sem_exp.
  Fact normalize_exp_sem : forall G vars b e H vs is_control es' eqs' st st' reusable,
      NoDup (map fst (fresh_in e) ++ PS.elements reusable) ->
      wl_exp G e ->
      sem_exp G H b e vs ->
      st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (fresh_in e)) reusable) ->
      Env.dom H (vars++st_ids st) ->
      normalize_exp is_control e st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list vars) reusable /\
          Env.dom H' (vars++st_ids st') /\
          Forall2 (fun e v => sem_exp G H' b e [v]) es' vs /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction e using exp_ind2; intros * Hndup Hwl Hsem Hvalid Histst Hnorm;
      inv Hwl; inv Hsem; repeat inv_bind.
    - (* const *)
      exists H. repeat (split; eauto).
    - (* var *)
      exists H. repeat (split; eauto).
    - (* unop *)
      assert (Htypeof:=H0). eapply normalize_exp_typeof in Htypeof...
      specialize (IHe _ _ _ _ _ _ _ _ Hndup H3 H8 Hvalid Histst H0) as [H' [Href1 [Hvalid1 [Hdom1 [Hsem1 Hsem1']]]]].
      eapply normalize_exp_length in H0... rewrite H5 in H0. singleton_length.
      inv Hsem1; clear H7.
      exists H'. repeat (split; eauto).
      repeat econstructor... congruence.
    - (* binop *)
      simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      assert (Htypeof1:=H0). eapply normalize_exp_typeof in Htypeof1...
      assert (Htypeof2:=H1). eapply normalize_exp_typeof in Htypeof2...
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
      assert (length (concat x2) = length (annots e0s)) as Hlength1 by (eapply map_bind2_normalize_exp_length; eauto).
      assert (length (concat x6) = length (annots es)) as Hlength2 by (eapply map_bind2_normalize_exp_length; eauto).
      assert (NoDup (map fst (fresh_ins es) ++ PS.elements reusable)) as Hndup2 by ndup_r Hndup.
      assert (NoDup (map fst (fresh_ins e0s) ++ PS.elements (ps_adds (map fst (concat (map fresh_in es))) reusable))) as Hndup1.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }
      assert (Forall (fun e => numstreams e = 1) (concat x2)) as Hnumstreams.
      { eapply map_bind2_normalize_exp_numstreams in H2... }

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
      assert (Forall2 (fun e v => sem_exp G H''' b e [v]) (normalize_fby (concat x2) (concat x6) a) vs) as Hsemf.
      { eapply normalize_fby_sem... 2:congruence.
        + eapply map_bind2_normalize_exp_length in H2'... congruence.
        + clear - Hsem1 Href2 Href4. solve_forall. repeat (eapply sem_exp_refines; eauto).
        + clear - Hsem2 Href2 Href4. solve_forall. repeat (eapply sem_exp_refines; eauto). }

      exists H'''. repeat (split; eauto).
      * repeat (etransitivity; eauto).
      * eapply idents_for_anns_dom in H4; eauto.
      * clear - Hsemvars. solve_forall.
      * repeat rewrite Forall_app. repeat split.
        -- clear - Hsemvars Hsemf.
           remember (normalize_fby _ _ _) as fby. clear Heqfby.
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
      assert (length (concat x1) = length (annots es)) as Hlength by (eapply map_bind2_normalize_exp_length; eauto).
      assert (length es = length ss) by (apply Forall2_length in H11; auto).
      eapply map_bind2_sem in H1... 2:solve_forall. clear H.
      destruct H1 as [H' [Hvalid1 [Href1 [Hdom1 [Hsem1 Hsem1']]]]].
      apply Forall2_concat in Hsem1.
      exists H'. repeat (split; simpl; eauto).
      eapply normalize_when_sem... congruence.
      eapply sem_var_refines...
    - (* merge *)
      simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      assert (length (concat x3) = length (annots ets)) as Hlength1 by (eapply map_bind2_normalize_exp_length; eauto).
      assert (length (concat x6) = length (annots efs)) as Hlength2 by (eapply map_bind2_normalize_exp_length; eauto).
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
                      (normalize_merge x (concat x3) (concat x6) tys nck) vs) as Hsem'.
      { eapply normalize_merge_sem... 1,2:congruence.
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
          -- remember (normalize_merge _ _ _ _ _) as merge.
             assert (length merge = length x0) as Hlength''.
             { eapply idents_for_anns_length in H2. clear - Heqmerge H17 H2 H9 Hlength1 Hlength2 Hlen'.
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
      { eapply normalize_exp_length in H2... congruence. }
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
                      (normalize_ite e0 (concat x5) (concat x8) tys nck) vs) as Hsem'.
      { eapply normalize_ite_sem... 1,2:congruence.
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
          remember (normalize_ite _ _ _ _ _) as ite.
          assert (length ite = length x) as Hlength''.
          { eapply idents_for_anns_length in H0. clear - Heqite H19 H0 Hlength1 Hlength2 H11 H12.
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
      simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
      assert (a = map snd x5) as Hanns; subst.
      { eapply idents_for_anns'_values in H4... }
      specialize (idents_for_anns'_length _ _ _ _ H4) as Hlength1.
      assert (length (n_out n) = length vs) as Hlength2.
      { specialize (H19 0). inv H19. apply Forall2_length in H16.
        rewrite H13 in H10; inv H10. unfold idents in *. solve_length. }
      assert (length es = length ss) as Hlength3.
      { apply Forall2_length in H15... }
      assert (length x6 = 1). 2:singleton_length.
      { eapply normalize_exp_length in H3... congruence. }
      assert (NoDup (map fst (Syn.anon_streams (map snd x5))++ PS.elements reusable)) as Hndup2 by repeat ndup_r Hndup.
      assert (NoDup (map fst (fresh_in r) ++ PS.elements (ps_adds (map fst (Syn.anon_streams (map snd x5))) reusable))) as Hndup3.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }
      assert (NoDup (map fst (fresh_ins es) ++ PS.elements (ps_adds (map fst (fresh_in r)) (ps_adds (map fst (Syn.anon_streams (map snd x5))) reusable)))) as Hndup4.
      { repeat rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... ndup_r Hndup. }

      eapply map_bind2_sem in H2... 2:solve_forall... clear H0.
      destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].

      assert (sem_exp G H' b r [rs]) as Hsemr' by (eapply sem_exp_refines; eauto). clear H17.
      eapply H in H3... clear H.
      destruct H3 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. inv Hsem2; clear H13.

      eapply normalize_reset_sem in H5...
      destruct H5 as [H''' [Href3 [Hvalid3 [Histst3 [Hsem3 Hsem3']]]]].

      assert (sem_exp G H''' b (Eapp f (concat x2) (Some x9) (map snd x5)) vs) as Hsem'.
      { eapply Sreset with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss)))...
        + apply Forall2_concat. repeat solve_forall.
          repeat (eapply sem_exp_refines; eauto).
        + intros k. specialize (H19 k).
          rewrite concat_map_singl2. assumption. }
      remember (Env.adds (map fst x5) vs H''') as H''''.
      assert (length vs = length x5) as Hlen' by solve_length.
      assert (Env.refines eq H''' H'''') as Href4.
      { eapply idents_for_anns'_refines... }
      assert (NoDupMembers x5) as Hndup'.
      { eapply idents_for_anns'_NoDupMembers in H4... }
      assert (Forall2 (sem_var H'''') (map fst x5) vs) as Hvars.
      { rewrite HeqH''''. eapply sem_var_adds... 1:rewrite map_length... rewrite <- fst_NoDupMembers... }
      exists H''''. repeat (split; eauto).
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
        * solve_forall. repeat (eapply sem_equation_refines; eauto).
  Qed.

  Corollary normalize_exps_sem : forall G vars b es H vs es' eqs' st st' reusable,
      NoDup (map fst (fresh_ins es) ++ PS.elements reusable) ->
      Forall (wl_exp G) es ->
      Forall2 (sem_exp G H b) es vs ->
      st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (fresh_ins es)) reusable) ->
      Env.dom H (vars++st_ids st) ->
      map_bind2 (normalize_exp false) es st = (es', eqs', st') ->
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
    eapply normalize_exp_sem with (e:=(nth n es a)); eauto.
  Qed.

  Fact normalize_rhs_sem : forall G vars b e H vs es' eqs' st st' reusable,
      NoDup (map fst (anon_in e) ++ PS.elements reusable) ->
      wl_exp G e ->
      sem_exp G H b e vs ->
      st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (anon_in e)) reusable) ->
      Env.dom H (vars++st_ids st) ->
      normalize_rhs e st = (es', eqs', st') ->
      (exists H',
          Env.refines eq H H' /\
          st_valid_reuse st' (PSP.of_list vars) reusable /\
          Env.dom H' (vars++st_ids st') /\
          (Forall2 (fun e v => sem_exp G H' b e [v]) es' vs \/
           exists e', (es' = [e'] /\ sem_exp G H' b e' vs)) /\
          Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros * Hndup1 Hwt Hsem Hvalid Hhistst Hnorm.
    destruct e; try eapply normalize_exp_sem in Hnorm; eauto.
    1,2,3,4,6,7,8: (destruct Hnorm as [H' [Href1 [Hvalid1 [Hhistst1 [Hsem1 Hsem2]]]]];
                    exists H'; repeat (split; eauto)).
    1,2:(unfold normalize_rhs in Hnorm). 1,2:(inv Hwt; inv Hsem).
    - (* fby *)
      simpl in *. repeat rewrite map_app, ps_adds_app in Hvalid.
      repeat inv_bind.
      assert (length x = length (annots l)) as Hlength1 by (eapply normalize_exps_length; eauto).
      assert (length x2 = length (annots l0)) as Hlength2 by (eapply normalize_exps_length; eauto).
      unfold normalize_exps in *. repeat inv_bind.
      assert (NoDup (map fst (fresh_ins l0) ++ PS.elements reusable)) as Hndup4 by ndup_r Hndup1.
      assert (NoDup (map fst (fresh_ins l) ++ PS.elements (ps_adds (map fst (fresh_ins l0)) reusable))) as Hndup3.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

      eapply normalize_exps_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.
      assert (Forall2 (sem_exp G H' b) l0 sss) as Hsem' by (repeat rewrite_Forall_forall; eapply sem_exp_refines; eauto).

      eapply normalize_exps_sem in H1...
      destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
      assert (Forall2 (fun (e : exp) (v : Stream OpAux.value) => sem_exp G H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
      { repeat rewrite_Forall_forall. eapply sem_exp_refines... }

      exists H''. repeat (split; auto).
      + repeat (etransitivity; eauto).
      + left. eapply normalize_fby_sem... 1,2:solve_length.
      + repeat rewrite Forall_app. repeat split...
        solve_forall. eapply sem_equation_refines; [| eauto]. etransitivity...
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
      assert (NoDup (map fst (fresh_in r) ++ PS.elements reusable)) as Hndup4 by ndup_r Hndup1.
      assert (NoDup (map fst (fresh_ins l) ++ PS.elements (ps_adds (map fst (fresh_in r)) reusable))) as Hndup3.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

      eapply normalize_exps_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
      assert (length x4 = 1) as Hlength2. 2:singleton_length.
      { eapply normalize_exp_length in H1... congruence. }
      assert (sem_exp G H' b r [rs]) as Hsem' by (eapply sem_exp_refines; eauto). clear H15.

      assert (normalized_lexp e) as Hnormed by (eapply normalize_exp_normalized_lexp in H1; inv H1; eauto).
      eapply normalize_exp_sem in H1...
      destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. inv Hsem2; clear H12.
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

  Corollary map_bind2_normalize_rhs_sem : forall G vars b es H vs es' eqs' st st' reusable,
      NoDup (map fst (anon_ins es) ++ PS.elements reusable) ->
      Forall (wl_exp G) es ->
      Forall2 (sem_exp G H b) es vs ->
      st_valid_reuse st (PSP.of_list vars) (ps_adds (map fst (anon_ins es)) reusable) ->
      Env.dom H (vars++st_ids st) ->
      map_bind2 normalize_rhs es st = (es', eqs', st') ->
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

  Corollary normalize_rhss_sem : forall G vars b es H vs es' eqs' st st' reusable,
      NoDup (map fst (anon_ins es) ++ PS.elements reusable) ->
      Forall (wt_exp G (vars++st_tys st)) es ->
      Forall2 (sem_exp G H b) es vs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_ins es)) reusable) ->
      Env.dom H (map fst vars++st_ids st) ->
      normalize_rhss es st = (es', eqs', st') ->
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
    { eapply normalize_rhss_wt in Hnorm as [? ?]... }
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

  Fact untuple_equation_sem : forall G vars H b equ eqs' st st' reusable,
      NoDup (map fst (anon_in_eq equ) ++ PS.elements reusable) ->
      wt_equation G (vars++st_tys st) equ ->
      sem_equation G H b equ ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in_eq equ)) reusable) ->
      Env.dom H (map fst vars++st_ids st) ->
      untuple_equation equ st = (eqs', st') ->
      (exists H', Env.refines eq H H' /\
             st_valid_reuse st' (PSP.of_list (map fst vars)) reusable /\
             Env.dom H' (map fst vars++st_ids st') /\
             Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    intros * Hndup Hwt Hsem Hvalid Histst Hnorm.
    unfold untuple_equation in Hnorm.
    destruct equ as [xs es]. inv Hwt. inv Hsem.
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

  Corollary untuple_equations_sem : forall G vars b eqs H eqs' st st' reusable,
      NoDup (map fst (anon_in_eqs eqs) ++ PS.elements reusable) ->
      Forall (wt_equation G (vars ++ st_tys st)) eqs ->
      Forall (sem_equation G H b) eqs ->
      st_valid_reuse st (PSP.of_list (map fst vars)) (ps_adds (map fst (anon_in_eqs eqs)) reusable) ->
      Env.dom H (map fst vars++st_ids st) ->
      untuple_equations eqs st = (eqs', st') ->
      (exists H', Env.refines eq H H' /\
             Forall (sem_equation G H' b) eqs').
  Proof with eauto.
    induction eqs; intros * Hndup Hwt Hsem Hvalid Hdome Hnorm;
      unfold untuple_equations in *; inv Hwt; inv Hsem; repeat inv_bind; simpl.
    - exists H...
    - unfold anon_in_eqs in *; simpl in *. rewrite map_app, ps_adds_app in Hvalid.
      assert (NoDup (map fst (anon_in_eqs eqs) ++ PS.elements reusable)) as Hndup4 by ndup_r Hndup.
      assert (NoDup (map fst (anon_in_eq a) ++ PS.elements (ps_adds (map fst (anon_in_eqs eqs)) reusable))) as Hndup3.
      { rewrite Permutation_PS_elements_ps_adds'; ndup_simpl... }

      assert (Forall (wt_equation G (vars ++ st_tys x1)) eqs) as Hwt' by (solve_forall; repeat solve_incl).
      eapply untuple_equation_sem in H0...
      destruct H0 as [H' [Href1 [Hvalid1 [Histst1 Hsem1]]]].
      assert (Forall (sem_equation G H' b) eqs) by (solve_forall; eapply sem_equation_refines; eauto).

      assert (untuple_equations eqs x1 = (concat x2, st')) as Hnorm.
      { unfold untuple_equations; repeat inv_bind. repeat eexists; eauto. inv_bind; eauto. }
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

  (** *** Preservation of sem_node *)

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

  Fact untuple_node_sem_equation : forall G H n Hwl ins,
      wt_node G n ->
      Env.dom H (List.map fst (n_in n ++ n_vars n ++ n_out n)) ->
      Forall2 (sem_var H) (idents (n_in n)) ins ->
      Forall (sem_equation G H (clocks_of ins)) (n_eqs n) ->
      (* Forall2 (fun xc : ident * clock => sem_clock H (clocks_of ins) (snd xc)) (idck (n_in n)) (map abstract_clock ins) -> *)
      exists H', Env.refines eq H H' /\
            Forall (sem_equation G H' (clocks_of ins)) (n_eqs (untuple_node n Hwl)).
  Proof with eauto.
    intros * Hwt Hdom Hins Hsem.
    remember (@init_st (Op.type * clock)
                (first_unused_ident (self::out::(map fst (n_in n++n_vars n++n_out n++anon_in_eqs (n_eqs n)))))) as init.
    specialize (n_nodup n) as Hndup; rewrite fst_NoDupMembers in Hndup; repeat rewrite map_app in Hndup.
    eapply untuple_equations_sem with (eqs:=n_eqs n) (st:=init)...
    5: simpl; rewrite <- surjective_pairing; subst; reflexivity.
    - rewrite PSP.elements_empty, app_nil_r.
      repeat ndup_r Hndup...
    - unfold st_tys. rewrite Heqinit, init_st_anns, app_nil_r.
      destruct Hwt as [_ [_ [_ Hwt]]]; eauto.
    - rewrite Heqinit.
      apply init_st_valid_reuse.
      rewrite ps_adds_of_list.
      + repeat rewrite ps_of_list_ps_to_list_Perm.
        * unfold idty. rewrite map_map, <- map_app, <- fst_NoDupMembers. repeat rewrite <- app_assoc. eapply (n_nodup n).
        * repeat ndup_r Hndup.
        * repeat rewrite <- map_app in Hndup. repeat rewrite app_assoc in Hndup.
          rewrite <- fst_NoDupMembers in Hndup. rewrite <- fst_NoDupMembers, NoDupMembers_idty. apply NoDupMembers_app_l in Hndup.
          repeat rewrite <- app_assoc in Hndup...
      + rewrite <- ps_adds_of_list, PS_For_all_ps_adds; split. 2:apply PS_For_all_empty.
        eapply Forall_incl. eapply first_unused_ident_gt; reflexivity.
        apply incl_tl, incl_tl. rewrite map_fst_idty. apply incl_map, incl_appr', incl_appr', incl_appl, incl_refl.
      + rewrite PS_For_all_ps_adds; split. 2:apply PS_For_all_empty.
        eapply Forall_incl. eapply first_unused_ident_gt; reflexivity.
        apply incl_tl, incl_tl, incl_map, incl_appr, incl_appr, incl_appr, incl_refl.
    - unfold st_ids. rewrite Heqinit, init_st_anns, app_nil_r, map_fst_idty...
  Qed.

  Lemma untuple_node_eq : forall G G' f n Hwl ins outs,
      Forall2 (fun n n' => n_name n = n_name n') G G' ->
      global_iface_eq G G' ->
      global_sem_refines G G' ->
      wt_global (n::G) ->
      Ordered_nodes (n::G) ->
      Ordered_nodes ((untuple_node n Hwl)::G') ->
      sem_node (n::G) f ins outs ->
      sem_node ((untuple_node n Hwl)::G') f ins outs.
  Proof with eauto.
    intros * Hnames Hiface Href HwtG Hord1 Hord2 Hsem.
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
      assert (Forall (sem_equation G H (clocks_of ins)) (n_eqs n0)).
      { eapply Forall_sem_equation_global_tl...
        eapply find_node_not_Is_node_in in Hord1... }
      inversion_clear HwtG; rename H2 into Hwt.
      assert (Forall (sem_equation G H' (clocks_of ins)) (n_eqs n0)) as Hsem'.
      { destruct Hwt as [_ [_ [_ Hwt]]].
        rewrite HeqH'.
        clear Hin Hout.
        repeat rewrite_Forall_forall.
        specialize (H0 _ H6). specialize (Hwt _ H6).
        eapply sem_equation_restrict in H0...
        unfold idty in H0. rewrite map_map in H0. simpl in H0... } clear H0.
      assert (Forall (sem_equation G' H' (clocks_of ins)) (n_eqs n0)) as Hsem''.
      { destruct Hwt as [_ [_ [_ Hwt']]].
        assert (Permutation (n_in n0 ++ n_out n0 ++ n_vars n0) (n_in n0 ++ n_vars n0 ++ n_out n0)) as Hperm.
        { apply Permutation_app_head, Permutation_app_comm. }
        solve_forall.
        eapply sem_ref_sem_equation... }

      eapply untuple_node_sem_equation in Hsem''...
      2: eapply iface_eq_wt_node...
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
      apply Href.
      econstructor...
      eapply Forall_impl_In; [| eauto]. intros eq Hin Hsem.
      eapply sem_equation_global_tl...
      eapply find_node_later_not_Is_node_in in Hord1...
      intro Hisin. apply Hord1. rewrite Is_node_in_Exists. rewrite Exists_exists.
      eexists...
  Qed.

  Fact untuple_global_names' : forall G Hwl,
      Forall2 (fun n n' => n_name n = n_name n') G (untuple_global G Hwl).
  Proof.
    intros.
    specialize (Ordered.untuple_global_names G Hwl) as Hnames.
    rewrite <- Forall2_eq, Forall2_swap_args in Hnames.
    solve_forall.
  Qed.

  Lemma untuple_global_refines : forall G Hwl,
      wt_global G ->
      Ordered_nodes G ->
      global_sem_refines G (untuple_global G Hwl).
  Proof with eauto.
    intros G Hwl. specialize (untuple_global_eq G Hwl) as Heq.
    induction G; intros * Hwt Hordered; simpl.
    - apply global_sem_ref_nil.
    - apply global_sem_ref_cons with (f:=n_name a)...
      + eapply Ordered.untuple_global_ordered in Hordered.
        simpl in Hordered...
      + inv Hwt; inv Hordered.
        eapply IHG... eapply untuple_global_eq...
      + intros ins outs Hsem.
        eapply untuple_node_eq...
        * apply untuple_global_names'.
        * apply untuple_global_eq.
        * inv Hwt; inv Hordered.
          eapply IHG... eapply untuple_global_eq...
        * eapply Ordered.untuple_global_ordered in Hordered.
          simpl in Hordered...
  Qed.

  Corollary untuple_global_sem : forall G Hwl f ins outs,
      wt_global G ->
      Ordered_nodes G ->
      sem_node G f ins outs ->
      sem_node (untuple_global G Hwl) f ins outs.
  Proof.
    intros.
    eapply untuple_global_refines with (Hwl:=Hwl) in H; eauto.
    specialize (H f ins outs); auto.
  Qed.

  Corollary untuple_global_sem_clock_inputs : forall G Hwl f ins,
      sem_clock_inputs G f ins ->
      sem_clock_inputs (untuple_global G Hwl) f ins.
  Proof.
    intros.
    specialize (untuple_global_eq G Hwl) as Heq.
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

  CoFixpoint delay (v : Op.val) (str : Stream OpAux.value) :=
    match str with
    | (present v') ⋅ str' => (present v) ⋅ (delay v' str')
    | absent ⋅ str' => absent ⋅ (delay v str')
    end.

  Fact delay_Cons : forall v y ys,
      delay v (y ⋅ ys) =
      match y with
      | present v' => (present v) ⋅ (delay v' ys)
      | absent => absent ⋅ (delay v ys)
      end.
  Proof.
    intros v y ys.
    rewrite unfold_Stream at 1; simpl.
    destruct y; reflexivity.
  Qed.

  Add Parametric Morphism : delay
      with signature eq ==> @EqSt value ==> @EqSt value
    as delay_EqSt.
  Proof.
    cofix CoFix.
    intros v [x xs] [y ys] Heq.
    inv Heq; simpl in *; subst.
    constructor; simpl.
    + destruct y; auto.
    + destruct y; auto.
  Qed.

  Lemma delay_const : forall bs v,
      delay v (const_val bs v) ≡ (const_val bs v).
  Proof.
    cofix CoFix.
    intros [b bs] v.
    rewrite const_val_Cons.
    destruct b; rewrite delay_Cons; constructor; simpl; auto.
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

  Lemma delay_fby1 : forall bs v y ys,
      aligned ys bs ->
      fby1 y (const_val bs v) ys (delay y ys).
  Proof with eauto.
    cofix delay_fby1.
    intros [b bs] v y ys Hsync.
    specialize (delay_fby1 bs).
    inv Hsync;
      rewrite const_val_Cons; rewrite unfold_Stream; simpl.
    - constructor...
    - constructor...
  Qed.

  Lemma delay_fby1' : forall y y0s ys zs,
      fby1 y y0s ys zs ->
      zs ≡ (delay y ys).
  Proof.
    cofix CoFix.
    intros y y0s ys zs Hfby1.
    inv Hfby1; constructor; simpl; eauto.
  Qed.

  Lemma delay_fby : forall b v y,
      aligned y b ->
      fby (const_val b v) y (delay v y).
  Proof with eauto.
    cofix delay_fby.
    intros [b bs] v y Hsync.
    rewrite const_val_Cons.
    rewrite unfold_Stream; simpl.
    destruct b; simpl; inv Hsync.
    - econstructor. eapply delay_fby1...
    - econstructor; simpl...
  Qed.

  Definition init_stream bs :=
    delay true_val (const bs false_const).

  Instance init_stream_Proper:
    Proper (@EqSt bool ==> @EqSt value) init_stream.
  Proof.
    intros bs bs' Heq.
    unfold init_stream. rewrite Heq. reflexivity.
  Qed.

  Lemma fby_ite : forall bs v y0s ys zs,
      (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
      fby y0s ys zs ->
      ite (delay true_val (const_val bs false_val)) y0s (delay v ys) zs.
  Proof with eauto.
    cofix fby_init_stream_ite.
    intros [b bs] v y0s ys zs Hsync Hfby1.
    apply fby_aligned in Hsync as [Hsync1 [Hsync2 Hsync3]]; [|auto].
    destruct b; inv Hsync1; inv Hsync2; inv Hsync3.
    - repeat rewrite const_val_Cons.
      inv Hfby1.
      repeat rewrite delay_Cons. constructor.
      rewrite delay_const.
      rewrite <- delay_fby1'...
      apply ite_false...
    - rewrite const_val_Cons. repeat rewrite delay_Cons.
      inv Hfby1.
      constructor; auto.
  Qed.

  Corollary fby_init_stream_ite : forall bs v y0s ys zs,
      (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
      fby y0s ys zs ->
      ite (init_stream bs) y0s (delay v ys) zs.
  Proof.
    intros * Hsync Hfby1.
    eapply fby_ite in Hfby1; eauto.
    unfold init_stream.
    rewrite const_val_const. rewrite sem_false_const. eassumption.
  Qed.

  Lemma ac_delay : forall c vs,
      abstract_clock (delay c vs) ≡ abstract_clock vs.
  Proof.
    cofix CoFix. intros c [v vs].
    rewrite delay_Cons.
    destruct v; constructor; simpl; auto.
  Qed.

  Lemma init_stream_ac : forall bs,
      abstract_clock (init_stream bs) ≡ bs.
  Proof.
    intros bs.
    unfold init_stream.
    rewrite ac_delay, <- ac_const. 1,2:reflexivity.
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

  Fact st_valid_reuse_NoDupMembers : forall st vars reusable,
      NoDupMembers vars ->
      st_valid_reuse st (PSP.of_list (map fst vars)) reusable ->
      NoDupMembers (vars++st_vars st).
  Proof.
    intros * Hndup Hvalid.
    eapply st_valid_after_NoDupMembers; eauto using st_valid_reuse_st_valid.
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

  (** *** Relation between state and history *)

  Definition init_eqs_valids bs H (st : fresh_st (Op.type * clock * bool)) :=
    Forall (fun '(id, ck) =>
              (exists bs', sem_clock H bs ck bs' /\
                      sem_var H id (init_stream bs'))) (st_inits st).

  Definition hist_st (vars : list (ident * clock)) b H st :=
    Env.dom H (map fst vars++st_ids st) /\
    init_eqs_valids b H st /\
    sc_var_inv' (vars++st_clocks' st) H b.

  Fact fresh_ident_init_eqs : forall vars b ty ck id v H st st',
      st_valid_after st (PSP.of_list vars) ->
      Env.dom H (vars ++ st_ids st) ->
      fresh_ident ((ty, ck), false) st = (id, st') ->
      init_eqs_valids b H st ->
      init_eqs_valids b (Env.add id v H) st'.
  Proof with auto.
    intros * Hvalid Hdom Hfresh Hinits.
    assert (~In id (st_ids st)) as Hnin by (eapply Facts.fresh_ident_nIn in Hfresh; eauto).
    assert (Env.refines eq H (Env.add id v H)) as Href.
    { eapply fresh_ident_refines in Hfresh; eauto. }
    eapply fresh_ident_false_st_inits in Hfresh.
    unfold init_eqs_valids in *. rewrite Hfresh.
    solve_forall. destruct H1 as [bs' [? ?]].
    exists bs'; split.
    - eapply sem_clock_refines; eauto.
    - eapply sem_var_refines; eauto.
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
    - unfold st_clocks', sc_var_inv' in *.
      rewrite Hfresh'; simpl.
      rewrite <- Permutation_middle. constructor.
      + exists v; split.
        * econstructor. eapply Env.add_1. 1,2:reflexivity.
        * eapply sem_clock_refines; eauto.
      + eapply sc_var_inv'_refines with (H:=H); eauto.
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
      { unfold st_inits. repeat simpl_In. exists (x, (bool_type, ck, true)); split; auto.
        rewrite filter_In. rewrite equiv_decb_refl; auto. }
      apply Hvalids in Hin' as [bs'' [? ?]].
      eapply sem_clock_det in Hsemc; eauto. rewrite <- Hsemc; auto.
    - (* We need to introduce a new init equation to the history and state,
         and prove its properties *)
      clear Hfind.
      destruct (fresh_ident _ _) eqn:Hident. repeat inv_bind.
      assert (st_valid_after st' (PSP.of_list (map fst vars))) as Hvalid1 by eauto.
      remember (Env.add x (init_stream bs') H) as H'.
      assert (Env.refines eq H H') as Href1 by (destruct Histst; eapply fresh_ident_refines in Hident; eauto).
      assert (hist_st vars bs H' st') as Histst1.
      { destruct Histst as [H1 [H2 H3]].
        repeat split.
        - eapply fresh_ident_dom in Hident...
        - unfold init_eqs_valids in *.
          erewrite fresh_ident_true_st_inits...
          constructor.
          + exists bs'. split; [eapply sem_clock_refines|]; eauto.
            rewrite HeqH'. econstructor. eapply Env.add_1.
            1,2:reflexivity.
          + solve_forall.
            destruct H2 as [bs'' [? ?]].
            exists bs''. split; [eapply sem_clock_refines|eapply sem_var_refines]; eauto.
        - unfold st_clocks', sc_var_inv' in *.
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
      assert (st_valid_after st' (PSP.of_list (map fst vars))) as Hvalid2 by eauto.
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
             rewrite <- sem_true_const. apply delay_fby.
             rewrite <- const_val_const. apply const_aligned.
        * econstructor. 2:reflexivity.
          rewrite HeqH'. apply Env.add_1. reflexivity.
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

  Fact fby_iteexp_sem : forall G vars bs H e0 e ty nck y0 y z e' eqs' st st',
      wc_global G ->
      sc_nodes G ->
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
    unfold fby_iteexp in Hiteexp.
    destruct (is_constant e0); repeat inv_bind.
    - (* e0 is a constant, no equation is introduced *)
      exists H. repeat (split; eauto).
      repeat (econstructor; eauto).
    - (* e0 is not a constant, we have to introduce an ite equation and (maybe) an init equation *)
      eapply sc_normalized_lexp with (env:=vars++st_vars st) in Hnormed...
      3,6:rewrite idck_app... 4:rewrite idty_app...
      2:{ eapply st_valid_after_NoDupMembers in Hvalid... }
      2:{ destruct Histst as [_ [_ ?]]. rewrite idck_app, <- st_clocks'_st_vars; auto. }
      eapply init_var_for_clock_sem with (G:=G) in H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]...
      2: rewrite map_fst_idck...
      remember (abstract_clock y0) as bs'.
      remember (delay (Op.sem_const (Op.init_type ty)) y) as y'.
      remember (Env.add x2 y' H') as H''.
      assert (Env.refines eq H' H'') by (destruct Histst1; eapply fresh_ident_refines in H1; eauto).
      assert (hist_st (idck vars) bs H'' st') as Histst2.
      { eapply fresh_ident_hist_st in H1; eauto.
        rewrite HeqH''...
        rewrite Heqy', ac_delay.
        1: eapply sem_clock_refines; eauto.
        rewrite ac_fby2, <- ac_fby1, <- Heqbs'; eauto. }
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
             eapply sem_clock_refines; [|eauto]. etransitivity...
          -- eapply sem_exp_refines; [| eauto]. etransitivity...
          -- rewrite Heqy'.
             rewrite const_val_const.
             eapply delay_fby.
             eapply fby_aligned in Hfby as [_ [? _]]; eauto.
             left. rewrite Heqbs'. apply ac_aligned.
        * econstructor.
          rewrite HeqH''. apply Env.add_1. 1,2:reflexivity.
      + solve_forall. eapply sem_equation_refines...
  Qed.

  Fact fby_equation_sc_exp : forall G H vars bs e0 ck s0s ss vs,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      wc_env (idck vars) ->
      normalized_lexp e0 ->
      wt_exp G (idty vars) e0 ->
      wc_exp G (idck vars) e0 ->
      clockof e0 = [ck] ->
      sem_exp G H bs e0 [s0s] ->
      fby s0s ss vs ->
      sc_var_inv' (idck vars) H bs ->
      sem_clock H bs ck (abstract_clock vs).
  Proof with eauto.
    intros * HwG Hsc Hndup Hwenv Hnormed Hwt Hwc Hck Hsem Hfby Hinv.
    eapply sc_normalized_lexp in Hnormed. 2-10:eauto.
    rewrite ac_fby1 in Hnormed; eauto.
  Qed.

  Fact fby_equation_sem : forall G vars bs H to_cut equ eqs' st st',
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      wc_env (idck vars++st_clocks' st) ->
      untupled_equation equ ->
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
    inv_fby_equation Hfby to_cut equ.
    - destruct x2 as [ty [ck name]]; repeat inv_bind.
      assert (st_follows st x4) as Hfollows1 by (eapply fby_iteexp_st_follows with (ann:=(ty, (ck, name))) in H0; eauto).
      inv Hunt. 2:inv H3; inv H2.
      destruct Hwt as [Hwt _]. inv Hwt; clear H6. inv H5. inv H8; clear H6.
      destruct Hwc as [Hwc _]. inv Hwc; clear H8. inv H6. inv H13; clear H8.
      rewrite Forall2_eq in H15;  unfold clock_of_nclock, stripname in H15; simpl in H15; rewrite app_nil_r in H15.
      inv Hsem. inv H19; inv H18. inv H8. inv H22; inv H18. inv H24; inv H19.
      simpl in *; repeat rewrite app_nil_r in *.
      inv H20; inv H21. inv H25; inv H22.
      assert (wc_env (idck (vars ++ st_vars x4))) as Hwenv1.
      { eapply fby_iteexp_wc_env in H0...
        + rewrite idck_app, <- st_clocks'_st_vars...
        + eapply normalized_lexp_wc_exp_clockof in H6...
          rewrite <- H15 in H6; inv H6... }
      eapply fby_iteexp_sem in H0 as [H' [Href1 [Hvalid1 [Hhistst1 [Hsem1 Hsem1']]]]]...
      destruct (PS.mem _ _); repeat inv_bind.
      + remember (Env.add x6 y2 H') as H''.
        assert (Env.refines eq H' H'') as Href2.
        { destruct Hhistst1 as [Hdom1 _]; rewrite map_fst_idck in Hdom1.
          eapply fresh_ident_refines in H0... }
        assert (hist_st (idck vars) bs H'' st') as Histst2.
        { eapply fresh_ident_hist_st in H0...
          + rewrite HeqH''...
          + rewrite map_fst_idck...
          + eapply fby_equation_sc_exp with (vars:=vars++st_vars x4) (e0:=x0)...
            * eapply st_valid_after_NoDupMembers in Hvalid1...
            * rewrite idty_app. rewrite st_tys'_st_vars in *. repeat solve_incl.
              apply st_follows_vars_incl...
            * rewrite idck_app. rewrite st_clocks'_st_vars in *. repeat solve_incl.
              apply st_follows_vars_incl...
            * eapply sem_exp_refines...
            * destruct Hhistst1 as [_ [_ ?]]. rewrite idck_app, <- st_clocks'_st_vars...
        }
        exists H''. repeat (split; eauto).
        * etransitivity; eauto.
        * repeat constructor.
          -- eapply Seq with (ss:=[[y2]]); simpl; repeat constructor.
             ++ subst; econstructor.
                eapply Env.add_1. 1,2:reflexivity.
             ++ eapply sem_var_refines; [|eauto]. etransitivity...
          -- eapply Seq with (ss:=[[y2]]); simpl; repeat constructor.
             ++ eapply sem_exp_refines...
             ++ subst; econstructor.
                eapply Env.add_1. 1,2:reflexivity.
          -- solve_forall. eapply sem_equation_refines...
      + exists H'. repeat (split; eauto).
        constructor; eauto.
        econstructor; eauto. simpl. constructor; auto.
        eapply sem_var_refines; eauto.
    - exists H. repeat (split; eauto).
  Qed.

  Fact fby_equations_sem : forall G vars bs to_cut eqs eqs' H st st',
      wc_global G ->
      sc_nodes G ->
      NoDupMembers vars ->
      wc_env (idck vars++st_clocks' st) ->
      Forall untupled_equation eqs ->
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
      sc_var_inv' (idck (n_in n++n_vars n++n_out n)) H b ->
      hist_st (idck (n_in n++n_vars n++n_out n)) b H
              (init_st (first_unused_ident (self::out::(map fst (n_in n++n_vars n++n_out n++anon_in_eqs (n_eqs n)))))).
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

  Fact normfby_node_sem_equation : forall G H to_cut n Hwl ins,
      wc_global G ->
      sc_nodes G ->
      untupled_node n ->
      wt_node G n ->
      wc_node G n ->
      sc_node' G n ->
      Env.dom H (map fst (n_in n ++ n_vars n ++ n_out n)) ->
      Forall2 (sem_var H) (idents (n_in n)) ins ->
      Forall2 (fun xc => sem_clock H (clocks_of ins) (snd xc)) (idck (n_in n)) (map abstract_clock ins) ->
      Forall (sem_equation G H (clocks_of ins)) (n_eqs n) ->
      exists H' : Env.t (Stream value),
        Env.refines eq H H' /\ Forall (sem_equation G H' (clocks_of ins)) (n_eqs (normfby_node to_cut n Hwl)).
  Proof with eauto.
    intros * HwcG HscG Hunt Hwt Hwc Hsc Hdom Hvars Hsemclock Hsem.
    remember (first_unused_ident (self::out::(map fst (n_in n++n_vars n++n_out n++anon_in_eqs (n_eqs n))))) as id0.
    remember (@init_st (Op.type * clock * bool) id0) as init.
    assert (NoDup (map fst (n_in n ++ n_vars n ++ n_out n))) as Hndup.
    { specialize (n_nodup n) as Hndup; rewrite fst_NoDupMembers in Hndup.
      repeat rewrite map_app in Hndup. repeat rewrite app_assoc in Hndup. apply NoDup_app_l in Hndup.
      repeat rewrite <- app_assoc in Hndup. repeat rewrite <- map_app in Hndup... }
    eapply fby_equations_sem with (vars:=(n_in n++n_vars n++n_out n)) (eqs:=n_eqs n) (st:=init)...
    7: simpl; rewrite <- surjective_pairing; subst; reflexivity.
    3:rewrite st_tys'_st_vars. 2,4:rewrite st_clocks'_st_vars.
    2,3,4:unfold st_vars; rewrite Heqinit, init_st_anns, app_nil_r.
    - rewrite fst_NoDupMembers...
    - destruct Hwc as [_ [_ [? _]]].
      rewrite (Permutation_app_comm (n_vars _))...
    - destruct Hwc as [_ [_ [_ ?]]]...
    - destruct Hwt as [_ [_ [_ ?]]]...
    - rewrite Heqinit.
      apply init_st_valid.
      rewrite PS_For_all_Forall, ps_of_list_ps_to_list_Perm...
      symmetry in Heqid0. eapply first_unused_ident_gt, Forall_incl in Heqid0...
      apply incl_tl, incl_tl, incl_map, incl_appr', incl_appr', incl_appl; auto.
    - subst. eapply init_st_hist_st...
      eapply sc_node_sc_var_inv...
  Qed.

  Lemma normfby_node_eq : forall G G' f n Hwl ins outs to_cut,
      Forall2 (fun n n' => n_name n = n_name n') G G' ->
      global_iface_eq G G' ->
      global_sc_refines G G' ->
      wt_global (n::G) ->
      wc_global (n::G) ->
      wt_global G' ->
      wc_global G' ->
      Ordered_nodes (n::G) ->
      Ordered_nodes ((normfby_node to_cut n Hwl)::G') ->
      Forall LCA.node_causal (n::G) ->
      Forall LCA.node_causal G' ->
      sem_node (n::G) f ins outs ->
      sem_clock_inputs (n::G) f ins ->
      sem_node ((normfby_node to_cut n Hwl)::G') f ins outs.
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
      assert (Forall (sem_equation G H (clocks_of ins)) (n_eqs n0)).
      { eapply Forall_sem_equation_global_tl...
        eapply find_node_not_Is_node_in in Hord1... }
      inversion_clear HwtG; rename H2 into Hwt.
      inversion_clear HwcG; rename H3 into Hwc.
      assert (Forall (sem_equation G H' (clocks_of ins)) (n_eqs n0)) as Hsem'.
      { destruct Hwt as [_ [_ [_ Hwt]]].
        rewrite HeqH'.
        clear Hin Hout.
        repeat rewrite_Forall_forall.
        specialize (H0 _ H8). specialize (Hwt _ H8).
        eapply sem_equation_restrict in H0...
        unfold idty in H0. rewrite map_map in H0. simpl in H0... } clear H0.
      assert (Forall (sem_equation G' H' (clocks_of ins)) (n_eqs n0)) as Hsem''.
      { destruct Hwt as [_ [_ [_ Hwt']]].
        destruct H5 as [Hwcclocks1 [_ [Hwcclocks Hwc']]].
        assert (sc_var_inv' (idck (n_in n0 ++ n_vars n0 ++ n_out n0)) H' (clocks_of ins)) as Hinv.
        { eapply sc_node_sc_var_inv with (G:=G)...
          rewrite ident_eqb_eq in Hident. eapply inputs_clocked_vars... }
        assert (Permutation (n_in n0 ++ n_out n0 ++ n_vars n0) (n_in n0 ++ n_vars n0 ++ n_out n0)) as Hperm.
        { apply Permutation_app_head, Permutation_app_comm. }
        solve_forall.
        eapply sc_ref_sem_equation. 7,8:eauto. 1-8:eauto.
        + assert (Hndup:=n_nodup n0). repeat rewrite app_assoc in *.
          eapply NoDupMembers_anon_in_eq'...
        + rewrite <- Hperm... }

      eapply normfby_node_sem_equation in Hsem''...
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

  Fact normfby_global_names' : forall G Hwl,
      Forall2 (fun n n' => n_name n = n_name n') G (normfby_global G Hwl).
  Proof.
    intros.
    specialize (Ordered.normfby_global_names G Hwl) as Hnames.
    rewrite <- Forall2_eq, Forall2_swap_args in Hnames.
    solve_forall.
  Qed.

  Lemma normfby_global_refines : forall G Hunt,
      wt_global G ->
      wc_global G ->
      Ordered_nodes G ->
      Forall LCA.node_causal G ->
      global_sc_refines G (normfby_global G Hunt).
  Proof with eauto.
    intros G Hunt. specialize (normfby_global_eq G Hunt) as Heq.
    induction G; intros * Hwt Hwc Hordered Hcaus; simpl.
    - apply global_sc_ref_nil.
    - apply global_sc_ref_cons with (f:=n_name a)...
      + eapply Ordered.normfby_global_ordered in Hordered.
        simpl in Hordered...
      + inv Hwt; inv Hwc; inv Hordered; inv Hcaus.
        eapply IHG... eapply normfby_global_eq...
      + intros ins outs Hsem. destruct Hsem as [Hinputs Hsem]. split.
        * eapply iface_eq_sem_clocks_input...
        * eapply normfby_node_eq...
          -- apply normfby_global_names'.
          -- apply normfby_global_eq.
          -- inv Hwt; inv Hwc; inv Hordered; inv Hcaus.
             eapply IHG... eapply normfby_global_eq...
          -- inv Hwt. eapply normfby_global_wt...
          -- inv Hwc. eapply normfby_global_wc...
          -- eapply Ordered.normfby_global_ordered in Hordered.
             simpl in Hordered...
          -- inv Hwc. inv Hcaus.
             eapply Causality.normfby_global_causal; auto.
  Qed.

  Corollary normfby_global_sem : forall G Hunt f ins outs,
      wt_global G ->
      wc_global G ->
      Ordered_nodes G ->
      Forall LCA.node_causal G ->
      sem_node G f ins outs ->
      sem_clock_inputs G f ins ->
      sem_node (normfby_global G Hunt) f ins outs.
  Proof.
    intros.
    eapply normfby_global_refines with (Hunt:=Hunt) in H; eauto.
    specialize (H f ins outs (conj H4 H3)) as [_ ?]; auto.
  Qed.

  (** ** Conclusion *)

  Theorem normalize_global_sem : forall G Hwl G' f ins outs,
      wt_global G ->
      wc_global G ->
      Ordered_nodes G ->
      sem_node G f ins outs ->
      sem_clock_inputs G f ins ->
      normalize_global G Hwl = Errors.OK G' ->
      sem_node G' f ins outs.
  Proof with eauto.
    intros * Hwt Hwc Hord Hsem Hclocks Hnorm.
    unfold normalize_global in Hnorm. destruct (LCA.check_causality _) eqn:Hcaus; inv Hnorm.
    eapply normfby_global_sem.
    - eapply untuple_global_wt...
    - eapply untuple_global_wc...
    - eapply Ordered.untuple_global_ordered...
    - eapply Causality.check_causality_correct in Hcaus; eauto.
      + eapply untuple_global_untupled_global.
      + eapply wt_global_wl_global, untuple_global_wt...
    - eapply untuple_global_sem...
    - eapply untuple_global_sem_clock_inputs...
  Qed.

  (** ** In addition : normalization only produces causal programs *)

  Lemma normalize_global_causal : forall G Hwl G',
      wc_global G ->
      normalize_global G Hwl = Errors.OK G' ->
      Forall LCA.node_causal G'.
  Proof.
    intros * Hwc Hnorm.
    unfold normalize_global in Hnorm.
    apply Errors.bind_inversion in Hnorm as [? [H1 H2]]. inv H2.
    eapply Causality.normfby_global_causal.
    2:apply Causality.check_causality_correct in H1; eauto.
    1,3:eapply untuple_global_wc in Hwc; eauto.
    eapply untuple_global_untupled_global.
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
       (LClockSem : LCLOCKSEMANTICS Ids Op OpAux Syn Ty Clo LCA Lord CStr IStr Sem)
       (Norm : NORMALIZATION Ids Op OpAux Syn LCA)
       <: CORRECTNESS Ids Op OpAux CStr IStr Syn LCA Ty Clo Lord Sem LClockSem Norm.
  Include CORRECTNESS Ids Op OpAux CStr IStr Syn LCA Ty Clo Lord Sem LClockSem Norm.
End CorrectnessFun.
