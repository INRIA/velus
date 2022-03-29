From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LCausality Lustre.LSemantics Lustre.LClockSemantics.
From Velus Require Import Lustre.Normalization.Normalization.
From Velus Require Import Lustre.Normalization.NTyping Lustre.Normalization.NClocking.
From Velus Require Import Lustre.SubClock.SCCorrectness.

(** * Correctness of the Normalization *)

Module Type CORRECTNESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (LCA        : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Import Ty : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import Cl : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import Ord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (Import LCS : LCLOCKSEMANTICS Ids Op OpAux Cks Senv Syn Ty Cl LCA Ord CStr Sem)
       (Import Norm : NORMALIZATION Ids Op OpAux Cks Senv Syn).

  Module Import SCT := SCCorrectnessFun Ids Op OpAux Cks CStr Senv Syn Ty Cl LCA Ord Sem LCS SC. Import SC.

  Import Fresh Tactics Unnesting.
  Module Import Typing := NTypingFun Ids Op OpAux Cks Senv Syn Ty Norm.
  Module Import Clocking := NClockingFun Ids Op OpAux Cks Senv Syn Cl Norm.
  Import List.

  CoFixpoint default_stream : Stream svalue :=
    absent ⋅ default_stream.

  Import Permutation.

  (** *** Relation between state and history *)

  Definition hist_st vars b H st :=
    Env.dom (fst H) (map fst vars++st_ids st) /\
    LCS.sc_vars (vars++st_senv st) H b.

  (** *** Correctness of the first pass *)

  Import Unnesting.

  Fact fresh_ident_refines {B} pref : forall hint vars H a id (v: Stream svalue) (st st' : fresh_st B),
      Fresh.st_valid_after st pref (PSP.of_list vars) ->
      Env.dom H (vars++st_ids st) ->
      fresh_ident pref hint a st = (id, st') ->
      Env.refines (@EqSt _) H (Env.add id v H).
  Proof with eauto.
    intros * Hvalid Hdom Hfresh.
    assert (Fresh.st_valid_after st' pref (PSP.of_list vars)) as Hvalid' by eauto with fresh norm.
    eapply Env.refines_add. apply EqStrel_Reflexive.
    intro contra. erewrite Env.dom_use in contra; [| eauto].
    apply in_app_or in contra. destruct contra.
    + eapply Facts.fresh_ident_In in Hfresh.
      assert (In id (st_ids st')).
      { unfold st_ids, idty. simpl_In; simpl in *.
        exists (id, a); auto. }
      apply st_valid_NoDup in Hvalid'.
      eapply NoDup_app_In in Hvalid'; [|eauto].
      apply Hvalid'; clear Hvalid'.
      rewrite ps_of_list_ps_to_list...
    + eapply Facts.fresh_ident_nIn in Hfresh; eauto.
  Qed.

  Fact fresh_ident_dom {B V} : forall pref hint vars H a id (v : V) (st st' : fresh_st B),
      Env.dom H (vars++st_ids st) ->
      fresh_ident pref hint a st = (id, st') ->
      Env.dom (Env.add id v H) (vars++st_ids st').
  Proof.
    intros * Hdom Hfresh.
    apply Facts.fresh_ident_vars_perm in Hfresh.
    apply Env.dom_add_cons with (x:=id) (v:=v) in Hdom.
    eapply Env.dom_Permutation; [| eauto].
    symmetry. rewrite Permutation_middle.
    apply Permutation_app_head. assumption.
  Qed.

  Fact fresh_ident_hist_st pref : forall hint vars b ty ck id v H Hl st st',
      (forall x, ~IsLast vars x) ->
      Fresh.st_valid_after st pref (PSP.of_list (map fst vars)) ->
      sem_clock H b ck (abstract_clock v) ->
      fresh_ident pref hint (ty, ck) st = (id, st') ->
      hist_st vars b (H, Hl) st ->
      hist_st vars b (Env.add id v H, Hl) st'.
  Proof with auto.
    intros * Hnl Hvalid Hsem Hfresh [Hdom Hsc].
    assert (~In id (st_ids st)) as Hnin by (eapply Facts.fresh_ident_nIn in Hfresh; eauto).
    assert (Fresh.st_valid_after st' pref (PSP.of_list (map fst vars))) as Hvalid2 by eauto with fresh norm.
    assert (Hfresh':=Hfresh). apply fresh_ident_anns in Hfresh'.
    assert (Env.refines (@EqSt _) H (Env.add id v H)) as Href.
    { eapply fresh_ident_refines in Hfresh; eauto. }
    repeat split; auto; try intros * Hck.
    - eapply fresh_ident_dom; eauto.
    - unfold LCS.sc_vars, st_senv in *.
      rewrite Hfresh' in Hck. simpl_app. simpl in *. rewrite <-Permutation_middle in Hck.
      inv Hck. inv H0.
      + inv H1. exists v; split.
        * econstructor. eapply Env.add_1. 1,2:reflexivity.
        * eapply sem_clock_refines; eauto.
      + eapply LCS.sc_vars_refines with (H:=H) in Hsc as ((?&?&?)&?); eauto with senv.
        reflexivity.
    - intros * Hla. exfalso.
      eapply NoLast_app; [|eauto]. split; auto. apply senv_of_tyck_NoLast.
  Qed.

  Fact idents_for_anns_NoDupMembers : forall anns ids st st' aft,
      st_valid_after st aft ->
      idents_for_anns anns st = (ids, st') ->
      NoDupMembers ids.
  Proof.
    intros * Hvalid Hids.
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
    intros * Hvalid Hids.
    eapply idents_for_anns_st_valid_after in Hvalid; eauto.
    apply st_valid_NoDup in Hvalid.
    apply idents_for_anns_vars_perm in Hids.
    unfold st_ids in *.
    rewrite <- Hids in Hvalid.
    rewrite Forall_forall. intros x Hin.
    rewrite <-app_assoc in Hvalid.
    eapply NoDup_app_In in Hvalid; eauto.
    contradict Hvalid.
    repeat rewrite in_app_iff in *; auto.
  Qed.

  Fact idents_for_anns_refines : forall vars H anns ids (vs : list (Stream svalue)) st st',
      length vs = length ids ->
      st_valid_after st (PSP.of_list vars) ->
      Env.dom H (vars++st_ids st) ->
      idents_for_anns anns st = (ids, st') ->
      Env.refines (@EqSt _) H (Env.adds (map fst ids) vs H).
  Proof with eauto.
    intros * Hlen Hvalid Hdom Hids.
    assert (Forall (fun id => ~In id vars) (List.map fst ids)) as Hnvar.
    { assert (st_valid_after st' (PSP.of_list vars)) by eauto with norm.
      apply idents_for_anns_incl_ids in Hids.
      solve_forall; simpl.
      assert (In i (map fst ids)) by solve_In.
      apply Hids in H2.
      intro contra.
      eapply st_valid_NoDup, NoDup_app_In in H0; [|eauto].
      apply H0. rewrite ps_of_list_ps_to_list... }
    apply refines_eq_EqSt, Env.refines_adds; eauto with env.
    eapply idents_for_anns_nIn in Hids...
    rewrite Forall_forall in *. intros x1 Hin contra.
    erewrite Env.dom_use in contra...
    rewrite in_app_iff in contra; destruct contra as [?|?].
    + eapply Hnvar...
    + eapply Hids; eauto using in_or_app.
  Qed.

  Fact idents_for_anns_hist_st : forall vars b anns H Hl ids vs st st',
      (forall x, ~IsLast vars x) ->
      Forall2 (fun ck v => sem_clock H b ck v) (map snd anns) (map abstract_clock vs) ->
      st_valid_after st (PSP.of_list (map fst vars)) ->
      idents_for_anns anns st = (ids, st') ->
      hist_st vars b (H, Hl) st ->
      hist_st vars b (Env.adds (map fst ids) vs H, Hl) st'.
  Proof.
    setoid_rewrite Forall2_map_1. setoid_rewrite Forall2_map_2.
    induction anns as [|(?&?)]; intros * Hnl Hcks Hvalid Hids Hhist; inv Hcks;
      repeat inv_bind; simpl; subst; auto.
    rewrite Env.adds_cons.
    eapply IHanns in H1; eauto with fresh norm.
    - eapply Forall2_impl_In; [|eauto]; intros; simpl in *.
      eapply sem_clock_refines; [|eauto].
      eapply fresh_ident_refines; eauto.
      destruct Hhist as (Hdom&_); eauto.
    - eapply fresh_ident_hist_st; eauto.
  Qed.

  Ltac solve_incl :=
    repeat unfold idty; repeat unfold idck;
    match goal with
    | Hiface : global_iface_incl ?G1 ?G2, H : wt_clock (enums ?G1) _ ?ck |- wt_clock (enums ?G2) _ ?ck =>
      eapply iface_incl_wt_clock; eauto
    | H : wc_clock ?l1 ?ck |- wc_clock ?l2 ?ck =>
      eapply wc_clock_incl; [| eauto]
    | Hiface : global_iface_incl ?G1 ?G2, H : wt_exp ?G1 _ ?e |- wt_exp ?G2 _ ?e =>
      eapply iface_incl_wt_exp; eauto
    | H : wt_exp ?G ?l1 ?e |- wt_exp ?G ?l2 ?e =>
      eapply wt_exp_incl; [| |eauto]; intros
    | H : wc_exp ?G ?l1 ?e |- wc_exp ?G ?l2 ?e =>
      eapply wc_exp_incl; [| |eauto]; intros
    | H : wt_equation ?G ?l1 ?eq |- wt_equation ?G ?l2 ?eq =>
      eapply wt_equation_incl; [| |eauto]; intros
    | H : wt_block ?G ?l1 ?eq |- wt_block ?G ?l2 ?eq =>
      eapply wt_block_incl; [| |eauto]; intros
    | H : wc_equation ?G ?l1 ?eq |- wc_equation ?G ?l2 ?eq =>
      eapply wc_equation_incl; [| |eauto]; intros
    | H : wc_block ?G ?l1 ?eq |- wc_block ?G ?l2 ?eq =>
      eapply wc_block_incl; [| |eauto]; intros
    | |- incl ?l1 ?l1 => reflexivity
    | |- incl (map ?f ?l1) (map ?f ?l2) => eapply incl_map
    | |- incl ?l1 (?l1 ++ ?l2) => apply incl_appl
    | |- incl (?l1 ++ ?l2) (?l1 ++ ?l3) => apply incl_appr'
    | |- incl ?l1 (?l2 ++ ?l3) => apply incl_appr
    | |- incl ?l1 (?a::?l2) => apply incl_tl
    | |- incl (st_anns ?st1) (st_anns _) =>
      apply st_follows_incl; repeat solve_st_follows
    | |- incl (st_senv ?st1) (st_senv _) => apply incl_map
    | H : HasType ?l1 ?x ?ty |- HasType ?l2 ?x ?ty =>
        eapply HasType_incl; [|eauto]
    | H : HasClock ?l1 ?x ?ty |- HasClock ?l2 ?x ?ty =>
        eapply HasClock_incl; [|eauto]
    | H : IsLast ?l1 ?x |- IsLast ?l2 ?x =>
        eapply IsLast_incl; [|eauto]
    end; auto.

  Section unnest_node_sem.
    Variable G1 : @global nolocal_top_block local_prefs.
    Variable G2 : @global nolocal_top_block norm1_prefs.

    Hypothesis HwcG1 : wc_global G1.
    Hypothesis HwcG2 : wc_global G2.
    Hypothesis Hifaceeq : global_iface_incl G1 G2.

    Hint Resolve iface_incl_wc_exp : norm.

    (** ** Conservation of sem_exp *)

    Fact unnest_reset_sem : forall vars b e H Hl v e' eqs' st st',
        (forall x, ~IsLast vars x) ->
        (forall e' eqs' st',
            unnest_exp G1 true e st = ([e'], eqs', st') ->
            exists H',
              Env.refines (@EqSt _) H H' /\
              st_valid_after st' (PSP.of_list (map fst vars)) /\
              hist_st vars b (H', Hl) st' /\
              sem_exp_ck G2 (H', Hl) b e' [v] /\ Forall (sem_equation_ck G2 (H', Hl) b) eqs')  ->
        wc_exp G1 (vars++st_senv st) e ->
        numstreams e = 1 ->
        sem_exp_ck G1 (H, Hl) b e [v] ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars b (H, Hl) st ->
        unnest_reset (unnest_exp G1 true) e st = (e', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars b (H', Hl) st' /\
            sem_exp_ck G2 (H', Hl) b e' [v] /\
            Forall (sem_equation_ck G2 (H', Hl) b) eqs').
    Proof with eauto.
      intros * Hnl Hun Hwc Hnum Hsem Hvalid Histst Hnorm.
      unnest_reset_spec; simpl in *.
      1,2:assert (length l = 1) by (eapply unnest_exp_length in Hk0; eauto with lclocking norm; congruence).
      1,2:singleton_length.
      - specialize (Hun _ _ _ eq_refl) as (H'&Href&Hval&Histst1&Hsem1&Hsem2).
        exists H'. repeat (split; eauto).
      - specialize (Hun _ _ _ eq_refl) as (H'&Href&Hval&Histst1&Hsem1&Hsem2).
        assert (Href':=Hfresh); eapply fresh_ident_refines in Href'; eauto.
        2:(destruct Histst1 as (Hdom1&_); ndup_simpl; eauto).
        exists (Env.add x1 v H'). split;[|split;[|split;[|split]]]; eauto with fresh norm.
        + etransitivity; eauto.
        + eapply fresh_ident_hist_st in Hfresh; eauto.
          assert (Hk:=Hk0). eapply unnest_exp_annot in Hk0; eauto with lclocking.
          rewrite <-length_annot_numstreams, <-Hk0 in Hnum. simpl in Hnum; rewrite app_nil_r in Hnum.
          singleton_length.
          eapply sc_exp with (Γ:=vars++st_senv f) in Hsem1; eauto with env fresh norm.
          * rewrite clockof_annot, Hsingl in Hsem1. simpl in Hsem1. inv Hsem1; auto.
          * destruct Histst1. auto.
          * eapply unnest_exp_wc in Hwc as (Hwc'&_). 2-4:eauto.
            apply Forall_singl in Hwc'. auto.
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

    Corollary unnest_resets_sem : forall vars b es H Hl vs es' eqs' st st',
        (forall x, ~IsLast vars x) ->
        Forall (wc_exp G1 (vars++st_senv st)) es ->
        Forall (fun e => numstreams e = 1) es ->
        Forall2 (fun e v => sem_exp_ck G1 (H, Hl) b e [v]) es vs ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars b (H, Hl) st ->
        Forall2 (fun e v => forall H e' eqs' st st',
                     wc_exp G1 (vars++st_senv st) e ->
                     sem_exp_ck G1 (H, Hl) b e [v] ->
                     st_valid_after st (PSP.of_list (map fst vars)) ->
                     hist_st vars b (H, Hl) st ->
                     unnest_exp G1 true e st = ([e'], eqs', st') ->
                     (exists H',
                         Env.refines (@EqSt _) H H' /\
                         st_valid_after st' (PSP.of_list (map fst vars)) /\
                         hist_st vars b (H', Hl) st' /\
                         sem_exp_ck G2 (H', Hl) b e' [v] /\
                         Forall (sem_equation_ck G2 (H', Hl) b) eqs')) es vs ->
        mmap2 (unnest_reset (unnest_exp G1 true)) es st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars b (H', Hl) st' /\
            Forall2 (fun e v => sem_exp_ck G2 (H', Hl) b e [v]) es' vs /\
            Forall (sem_equation_ck G2 (H', Hl) b) (concat eqs')).
    Proof with eauto.
      induction es; intros * Hnl Hwt Hnum Hsem Hvalid Histst Hf Hmap;
        inv Hwt; inv Hnum; inv Hsem; inv Hf; repeat inv_bind.
      - exists H; simpl. repeat (split; eauto with env).
      - assert (Hr:=H0). eapply unnest_reset_sem in H0 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1'); eauto.
        assert (Forall2 (fun e v => sem_exp_ck G1 (H', Hl) b e [v]) es l') as Hsem'.
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

    Hint Constructors Forall3 : datatypes.

    Fact unnest_arrow_sem : forall H bs e0s es anns s0s ss os,
        length e0s = length anns ->
        length es = length anns ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) e0s s0s ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) es ss ->
        Forall3 (fun s0 s o => arrow s0 s o) s0s ss os ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) (unnest_arrow e0s es anns) os.
    Proof with eauto with datatypes.
      intros * Hlen1 Hlen2 Hsem1 Hsem2 Hfby.
      unfold unnest_arrow.
      rewrite_Forall_forall. solve_length.
      repeat simpl_length. repeat simpl_nth. Unshelve. 2:exact ((hd_default [], hd_default []), default_ann).
      destruct (nth n (combine _ _)) as [[e0 e] ?] eqn:Hnth. repeat simpl_nth.
      econstructor... econstructor...
      Unshelve. 1-2:exact default_stream.
    Qed.

    Fact unnest_fby_sem : forall H bs e0s es anns s0s ss os,
        length e0s = length anns ->
        length es = length anns ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) e0s s0s ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) es ss ->
        Forall3 (fun s0 s o => fby s0 s o) s0s ss os ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) (unnest_fby e0s es anns) os.
    Proof with eauto with datatypes.
      intros * Hlen1 Hlen2 Hsem1 Hsem2 Hfby.
      unfold unnest_fby.
      rewrite_Forall_forall. 1:solve_length.
      repeat simpl_length. repeat simpl_nth. Unshelve. 2:exact ((hd_default [], hd_default []), default_ann).
      destruct (nth n (combine _ _)) as [[e0 e] ?] eqn:Hnth. repeat simpl_nth.
      econstructor... econstructor...
      Unshelve. 1-2:exact default_stream.
    Qed.

    Fact unnest_when_sem : forall H bs es tys ckid b ck s ss os,
        length es = length tys ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) es ss ->
        sem_var (fst H) ckid s ->
        Forall2 (fun s' => when b s' s) ss os ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) (unnest_when ckid b es tys ck) os.
    Proof with eauto.
      intros * Hlen Hsem Hvar Hwhen.
      unfold unnest_when. simpl_forall.
      rewrite_Forall_forall. 1:congruence.
      eapply Swhen with (ss:=[[nth n ss default_stream]])...
      - repeat constructor...
        eapply H1... congruence.
    Qed.

    Lemma Forall2Brs_hd_inv (P : _ -> _ -> Prop) : forall es v vs,
        (forall x v, List.Exists (fun es => In x (snd es)) es -> P x v -> length v = 1) ->
        Forall2Brs P es (v :: vs) ->
        Forall2Brs P (map (fun '(i, es) => (i, [hd_default es])) es) [v].
    Proof.
      induction es; intros * Hp Hf; inv Hf; simpl.
      - inv H. constructor; auto.
      - destruct vs2; [inv H4|].
        destruct vs1; simpl in *; [inv H4|]. inv H1.
        assert (Hp':=H5). eapply Hp in Hp'; eauto. 2:left; left; auto.
        singleton_length. inv H4.
        econstructor; eauto; simpl. eauto with datatypes.
    Qed.

    Lemma Forall2Brs_tl_inv (P : _ -> _ -> Prop) : forall es v vs,
        (forall x v, List.Exists (fun es => In x (snd es)) es -> P x v -> length v = 1) ->
        Forall2Brs P es (v :: vs) ->
        Forall2Brs P (List.map (fun '(i, es) => (i, List.tl es)) es) vs.
    Proof.
      induction es; intros * Hp Hf; inv Hf; simpl.
      - inv H. constructor; auto.
      - destruct vs2; [inv H4|].
        destruct vs1; simpl in *; [inv H4|]. inv H1.
        econstructor; eauto.
        + eapply Hp in H5; eauto. 2:left; left; auto.
          singleton_length. inv H4; auto.
    Qed.

    Fact unnest_merge_sem vars : forall H bs tys x tx es ck s vs os,
        es <> [] ->
        Forall (fun es => Forall (wc_exp G2 vars) (snd es)) es ->
        Forall (fun es => length (annots (snd es)) = length tys) es ->
        Forall (fun es => Forall (fun e => numstreams e = 1) (snd es)) es ->
        sem_var (fst H) x s ->
        Forall2Brs (sem_exp_ck G2 H bs) es vs ->
        Forall2 (merge s) vs os ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) (unnest_merge (x, tx) es tys ck) os.
    Proof with eauto.
      induction tys; intros * Hnnil Hwc Hlen Hnum Hvar Hsem Hmerge; simpl in *; auto.
      - eapply Forall2Brs_length1 in Hsem.
        2:{ do 2 (eapply Forall_forall; intros). eapply sem_exp_numstreams, sem_exp_ck_sem_exp; eauto.
            do 2 (eapply Forall_forall in Hwc; eauto with lclocking).
        }
        inv Hsem; try congruence. inv Hlen.
        rewrite H0 in H4. destruct vs; simpl in *; try congruence.
        inv Hmerge; auto.
      - assert (length vs = S (length tys)) as Hlen'.
        { eapply Forall2Brs_length1 in Hsem.
          2:{ do 2 (eapply Forall_forall; intros). eapply sem_exp_numstreams, sem_exp_ck_sem_exp; eauto.
              do 2 (eapply Forall_forall in Hwc; eauto with lclocking). }
          inv Hsem; try congruence. inv Hlen.
          congruence. }
        destruct vs; simpl in *; inv Hlen'.
        assert (forall x v, Exists (fun es0 => In x (snd es0)) es -> sem_exp_ck G2 H bs x v -> length v = 1) as Hlv.
        { intros ?? Hex Hse. eapply Exists_exists in Hex as (?&Hin1&Hin2).
          do 2 (eapply Forall_forall in Hwc; eauto). do 2 (eapply Forall_forall in Hnum; eauto).
          eapply sem_exp_ck_sem_exp, sem_exp_numstreams in Hse; eauto with lclocking.
          congruence.
        }
        inv Hmerge; simpl. constructor; eauto.
        + econstructor; eauto.
          eapply Forall2Brs_hd_inv; eauto.
        + eapply IHtys; eauto.
          * contradict Hnnil. apply map_eq_nil in Hnnil; auto.
          * rewrite Forall_map.
            eapply Forall_impl; [|eapply Hwc]; intros (?&?) ?; simpl in *.
            inv H0; simpl; auto.
          * rewrite Forall_map.
            eapply Forall_impl_In; [|eapply Hlen]; intros (?&?) Hin Hl; simpl in *.
            destruct l0; simpl in *; try congruence.
            eapply Forall_forall in Hnum; eauto. inv Hnum.
            rewrite app_length, length_annot_numstreams, H4 in Hl. inv Hl; auto.
          * rewrite Forall_map.
            eapply Forall_impl; [|eapply Hnum]; intros (?&?) Hf; simpl in *.
            inv Hf; simpl in *; auto.
          * eapply Forall2Brs_tl_inv; eauto.
    Qed.

    Fact unnest_case_sem vars : forall H bs tys ec es d ck s vs vd os,
        es <> [] ->
        Forall (fun es => Forall (wc_exp G2 vars) (snd es)) es ->
        Forall (fun es => length (annots (snd es)) = length tys) es ->
        Forall (fun es => Forall (fun e => numstreams e = 1) (snd es)) es ->
        sem_exp_ck G2 H bs ec [s] ->
        LiftO True (fun _ => wt_streams [s] (typeof ec)) d ->
        Forall2Brs (sem_exp_ck G2 H bs) es vs ->
        LiftO (vd = List.map (fun _ => None) tys) (fun d => exists vd', vd = List.map Some vd' /\ Forall2 (fun d v => sem_exp_ck G2 H bs d [v]) d vd') d ->
        Forall3 (case s) vs vd os ->
        Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) (unnest_case ec es d tys ck) os.
    Proof with eauto.
      induction tys; intros * Hnnil Hwc Hlen Hnum Hec Hwt Hsem Hsd Hmerge; simpl in *; auto.
      - eapply Forall2Brs_length1 in Hsem.
        2:{ do 2 (eapply Forall_forall; intros). eapply sem_exp_numstreams, sem_exp_ck_sem_exp; eauto.
            do 2 (eapply Forall_forall in Hwc; eauto with lclocking).
        }
        inv Hsem; try congruence. inv Hlen.
        rewrite H0 in H4. destruct vs; simpl in *; try congruence.
        inv Hmerge; auto.
      - assert (length vs = S (length tys)) as Hlen'.
        { eapply Forall2Brs_length1 in Hsem.
          2:{ do 2 (eapply Forall_forall; intros). eapply sem_exp_numstreams, sem_exp_ck_sem_exp; eauto.
              do 2 (eapply Forall_forall in Hwc; eauto with lclocking). }
          inv Hsem; try congruence. inv Hlen.
          congruence. }
        destruct vs; simpl in *; inv Hlen'.
        assert (forall x v, Exists (fun es0 => In x (snd es0)) es -> sem_exp_ck G2 H bs x v -> length v = 1) as Hlv.
        { intros ?? Hex Hse. eapply Exists_exists in Hex as (?&Hin1&Hin2).
          do 2 (eapply Forall_forall in Hwc; eauto). do 2 (eapply Forall_forall in Hnum; eauto).
          eapply sem_exp_ck_sem_exp, sem_exp_numstreams in Hse; eauto with lclocking.
          congruence.
        }
        inv Hmerge; simpl. constructor; eauto.
        + destruct d; simpl in *.
          * destruct Hsd as (?&Hsome&Hf).
            destruct x; simpl in *; inv Hsome. inv Hf.
            econstructor; eauto; simpl; eauto with datatypes.
            eapply Forall2Brs_hd_inv; eauto.
          * inv Hsd.
            econstructor; eauto; simpl; eauto with datatypes.
            eapply Forall2Brs_hd_inv; eauto.
        + eapply IHtys; eauto.
          * contradict Hnnil. apply map_eq_nil in Hnnil; auto.
          * rewrite Forall_map.
            eapply Forall_impl; [|eapply Hwc]; intros (?&?) ?; simpl in *.
            inv H0; simpl; auto.
          * rewrite Forall_map.
            eapply Forall_impl_In; [|eapply Hlen]; intros (?&?) Hin Hl; simpl in *.
            destruct l0; simpl in *; try congruence.
            eapply Forall_forall in Hnum; eauto. inv Hnum.
            rewrite app_length, length_annot_numstreams, H4 in Hl. inv Hl; auto.
          * rewrite Forall_map.
            eapply Forall_impl; [|eapply Hnum]; intros (?&?) Hf; simpl in *.
            inv Hf; simpl in *; auto.
          * destruct d; simpl in *; auto.
          * eapply Forall2Brs_tl_inv; eauto.
          * destruct d; simpl in *.
            -- destruct Hsd as (?&Hsome&Hf).
               destruct x; simpl in *; inv Hsome.
               repeat esplit; eauto. inv Hf; eauto.
            -- inv Hsd; auto.
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

    Fact mmap2_sem : forall vars b is_control es H Hl vs es' eqs' st st',
        (forall x, ~IsLast vars x) ->
        Forall (wc_exp G1 (vars++st_senv st)) es ->
        Forall2 (sem_exp_ck G1 (H, Hl) b) es vs ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars b (H, Hl) st ->
        Forall
          (fun e => forall H Hl vs is_control es' eqs' st st',
               (forall x, ~IsLast vars x) ->
               wc_exp G1 (vars++st_senv st) e ->
               sem_exp_ck G1 (H, Hl) b e vs ->
               st_valid_after st (PSP.of_list (map fst vars)) ->
               hist_st vars b (H, Hl) st ->
               unnest_exp G1 is_control e st = (es', eqs', st') ->
               exists H' : Env.t (Stream svalue),
                 Env.refines (@EqSt _) H H' /\
                 st_valid_after st' (PSP.of_list (map fst vars)) /\
                 hist_st vars b (H', Hl) st' /\
                 Forall2 (fun (e0 : exp) (v : Stream svalue) => sem_exp_ck G2 (H', Hl) b e0 [v]) es' vs /\
                 Forall (sem_equation_ck G2 (H', Hl) b) eqs') es ->
        mmap2 (unnest_exp G1 is_control) es st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars b (H', Hl) st' /\
            Forall2 (fun es vs => Forall2 (fun e v => sem_exp_ck G2 (H', Hl) b e [v]) es vs) es' vs /\
            Forall (sem_equation_ck G2 (H', Hl) b) (concat eqs')).
    Proof with eauto.
      induction es; intros * Hnl Hwc Hsem Hvalid Histst Hf Hmap;
        inv Hwc; inv Hsem; inv Hf; repeat inv_bind.
      - exists H; simpl. repeat (split; eauto with env).
      - assert (Hun1:=H0). eapply H5 in H0 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1'); eauto.
        assert (Forall2 (sem_exp_ck G1 (H', Hl) b) es l') as Hsem'.
        { eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines... }
        eapply IHes in H1 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2'); eauto.
        2:(solve_forall; repeat solve_incl).
        clear IHes H7.
        exists H''. repeat (split; eauto).
        + etransitivity...
        + constructor; eauto. subst.
          assert (length x = numstreams a) as Hlength1 by (eapply unnest_exp_length; eauto with lclocking).
          assert (length y = numstreams a) as Hlength2 by (eapply sem_exp_numstreams, sem_exp_ck_sem_exp; eauto with lclocking).
          solve_forall.
          eapply sem_exp_refines; eauto.
        + apply Forall_app. split...
          solve_forall. eapply sem_equation_refines...
    Qed.

    Hint Constructors Forall2Brs : norm.

    Fact mmap2_mmap2_sem : forall vars b is_control es H Hl vs es' eqs' st st',
        (forall x, ~IsLast vars x) ->
        Forall (fun es => Forall (wc_exp G1 (vars++st_senv st)) (snd es)) es ->
        Forall2Brs (sem_exp_ck G1 (H, Hl) b) es vs ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars b (H, Hl) st ->
        Forall
          (fun es => Forall
             (fun e => forall H Hl vs is_control es' eqs' st st',
                  (forall x, ~IsLast vars x) ->
                  wc_exp G1 (vars++st_senv st) e ->
                  sem_exp_ck G1 (H, Hl) b e vs ->
                  st_valid_after st (PSP.of_list (map fst vars)) ->
                  hist_st vars b (H, Hl) st ->
                  unnest_exp G1 is_control e st = (es', eqs', st') ->
                  exists H' : Env.t (Stream svalue),
                    Env.refines (@EqSt _) H H' /\
                    st_valid_after st' (PSP.of_list (map fst vars)) /\
                    hist_st vars b (H', Hl) st' /\
                    Forall2 (fun e0 v => sem_exp_ck G2 (H', Hl) b e0 [v]) es' vs /\
                    Forall (sem_equation_ck G2 (H', Hl) b) eqs') (snd es)) es ->
        mmap2 (fun '(i, es) => bind2 (mmap2 (unnest_exp G1 is_control) es) (fun es' eqs' => ret ((i, concat es'), concat eqs'))) es st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars b (H', Hl) st' /\
            Forall2Brs (sem_exp_ck G2 (H', Hl) b) es' vs /\
            Forall (sem_equation_ck G2 (H', Hl) b) (concat eqs')).
    Proof with eauto.
      induction es; intros * Hnl Hwc Hsem Hvalid Histst Hf Hmap;
        inv Hwc; inv Hsem; inv Hf; repeat inv_bind.
      - exists H; simpl. repeat (split; eauto with env norm).
      - eapply mmap2_sem in H6 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1'); eauto.
        assert (Forall2Brs (sem_exp_ck G1 (H', Hl) b) es vs2) as Hsem'.
        { eapply Forall2Brs_impl_In; [|eauto]; intros ?? _ ?.
          eapply sem_exp_refines... }
        eapply IHes in H1 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2')... clear IHes H8.
        2:(solve_forall; solve_forall; repeat solve_incl).
        exists H''. repeat (split; eauto).
        + etransitivity...
        + econstructor.
          { eapply Forall2_concat. erewrite Forall2_map_2.
            eapply Forall2_impl_In; [|eauto]; intros; simpl in *. erewrite Forall2_map_2.
            eapply Forall2_impl_In; [|eauto]; intros; simpl in *. instantiate (1:=fun x => [x]); simpl.
            eapply sem_exp_refines...
          }
          2:{ rewrite <-concat_map, concat_map_singl1; eauto. }
          eauto.
        + apply Forall_app. split...
          solve_forall. eapply sem_equation_refines...
    Qed.

    Lemma unnest_noops_exp_sem : forall vars b cki e H Hl v e' eqs' st st',
        (forall x, ~IsLast vars x) ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars b (H, Hl) st ->
        normalized_lexp e ->
        wc_exp G2 (vars++st_senv st) e ->
        sem_exp_ck G2 (H, Hl) b e [v] ->
        unnest_noops_exp cki e st = (e', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars b (H', Hl) st' /\
            sem_exp_ck G2 (H', Hl) b e' [v] /\
            Forall (sem_equation_ck G2 (H', Hl) b) eqs').
    Proof.
      unfold unnest_noops_exp.
      intros * Hnl Hvalid Hdom Hnormed Hwc Hsem Hunt.
      assert (numstreams e = 1) as Hnum by (eapply normalized_lexp_numstreams; eauto).
      rewrite <-length_annot_numstreams in Hnum. singleton_length.
      destruct p as (?&?).
      destruct (is_noops_exp _ _); repeat inv_bind.
      - exists H; auto with env.
      - assert (Hfresh:=H0).
        assert (Env.refines (EqSt (A:=svalue)) H (Env.add x v H)) as Href.
        { eapply fresh_ident_refines; eauto.
          destruct Hdom as (Hdom&_); auto. }
        exists (Env.add x v H). split;[|split;[|split;[|split]]]; auto.
        + eapply fresh_ident_st_valid; eauto.
        + eapply fresh_ident_hist_st; eauto.
          eapply sc_exp in Hsem; eauto. 2:destruct Hdom; auto.
          rewrite clockof_annot, Hsingl in Hsem; inv Hsem; eauto.
        + constructor. econstructor.
          eapply Env.add_1. 1,2:reflexivity.
        + constructor; auto.
          apply Seq with (ss:=[[v]]); simpl.
          * constructor; auto. eapply sem_exp_refines; eauto.
          * constructor; auto. econstructor.
            eapply Env.add_1. 1,2:reflexivity.
    Qed.

    Lemma unnest_noops_exps_sem : forall vars b cks es H Hl vs es' eqs' st st',
        (forall x, ~IsLast vars x) ->
        length es = length cks ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars b (H, Hl) st ->
        Forall normalized_lexp es ->
        Forall (wc_exp G2 (vars++st_senv st)) es ->
        Forall2 (fun e v => sem_exp_ck G2 (H, Hl) b e [v]) es vs ->
        unnest_noops_exps cks es st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars b (H', Hl) st' /\
            Forall2 (fun e v => sem_exp_ck G2 (H', Hl) b e [v]) es' vs /\
            Forall (sem_equation_ck G2 (H', Hl) b) eqs').
    Proof.
      unfold unnest_noops_exps.
      induction cks; intros * Hnl Hlen Hvalid Hdom Hnormed Hwc Hsem Hunt; repeat inv_bind; simpl; auto.
      1,2:destruct es; simpl in *; inv Hlen; repeat inv_bind.
      - inv Hsem. exists H. auto with env.
      - inv Hsem. inv Hnormed. inv Hwc.
        assert (Hnoops:=H0). eapply unnest_noops_exp_sem in H0 as (H'&?&?&?&?&?); eauto.
        assert (Forall2 (fun e v => sem_exp_ck G2 (H', Hl) b e [v]) es l') as Hsem'.
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

    Hint Resolve sem_ref_sem_exp : lcsem.
    Hint Constructors sem_exp_ck : lcsem.

    Fact unnest_exp_sem : forall vars b e H Hl vs is_control es' eqs' st st',
        (forall x, ~IsLast vars x) ->
        wc_exp G1 (vars++st_senv st) e ->
        sem_exp_ck G1 (H, Hl) b e vs ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars b (H, Hl) st ->
        unnest_exp G1 is_control e st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars b (H', Hl) st' /\
            Forall2 (fun e v => sem_exp_ck G2 (H', Hl) b e [v]) es' vs /\
            Forall (sem_equation_ck G2 (H', Hl) b) eqs').
    Proof with eauto with norm lclocking.
      induction e using exp_ind2; intros * Hnl Hwc Hsem Hvalid Histst Hnorm; repeat inv_bind. 11,12:inv Hwc; inv Hsem.
      - (* const *)
        inv Hsem. exists H. repeat (split; auto with lcsem env).
      - (* enum *)
        inv Hsem. exists H. repeat (split; auto with lcsem env).
      - (* var *)
        inv Hsem. exists H. repeat (split; auto with lcsem env).
      - (* last *)
        inv Hsem. exists H. repeat (split; auto with lcsem env).
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
        assert (Htypeof1:=H0). eapply unnest_exp_typeof in Htypeof1...
        assert (Htypeof2:=H1). eapply unnest_exp_typeof in Htypeof2...
        assert (Hun1:=H0). eapply IHe1 in H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]... clear IHe1.
        eapply sem_exp_refines in H10; eauto.
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
        inversion_clear Hsem as [| | | | | |???????? Hsem1 Hsem2 Fby| | | | | |].
        assert (length (concat x2) = length (annots e0s)) as Hlength1 by (eapply mmap2_unnest_exp_length; eauto with lclocking).
        assert (length (concat x6) = length (annots es)) as Hlength2 by (eapply mmap2_unnest_exp_length; eauto with lclocking).
        assert (Forall (fun e => numstreams e = 1) (concat x2)) as Hnumstreams.
        { eapply mmap2_unnest_exp_numstreams in H2... }

        assert (length s0ss = length e0s) as Hlen1 by (eapply Forall2_length in Hsem1; eauto).
        assert (H2':=H2). eapply mmap2_sem in H2... clear H.
        destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1' Hsem1'']]]]]. apply Forall2_concat in Hsem1'.

        assert (Forall2 (sem_exp_ck G1 (H', Hl) b) es sss) as Hsem' by (rewrite_Forall_forall; eapply sem_exp_refines; eauto).
        assert (length sss = length es) as Hlen2 by (eapply Forall2_length in Hsem2; eauto).
        assert (H3':=H3). eapply mmap2_sem in H3... clear H0.
        2:solve_forall; repeat solve_incl.
        destruct H3 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2' Hsem2'']]]]]. apply Forall2_concat in Hsem2'.

        assert (Forall2 (fun e v => sem_exp_ck G2 (H'', Hl) b e [v]) (concat x2) (concat s0ss)) as Hsem''.
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

        assert (Forall2 (fun e v => sem_exp_ck G2 (H'''', Hl) b e [v]) (unnest_fby (concat x2) (concat x6) a) vs) as Hsemf.
        { eapply unnest_fby_sem; simpl...
          + eapply mmap2_unnest_exp_length in H2'... eapply Forall2_length in Hl1. solve_length.
          + eapply mmap2_unnest_exp_length in H3'... eapply Forall2_length in Hl2. solve_length.
          + clear - Hsem1' Href2 Href4. eapply Forall2_impl_In... intros; simpl in *.
            repeat (eapply sem_exp_refines; eauto).
          + clear - Hsem2' Href2 Href4. eapply Forall2_impl_In... intros; simpl in *.
            repeat (eapply sem_exp_refines; eauto). }

        exists H''''. split;[|split;[|split;[|split]]];eauto with norm.
        * repeat (etransitivity; eauto).
        * subst. eapply idents_for_anns_hist_st in H4; eauto.
          eapply sc_exps2 in Hsem1'; eauto. 2:destruct Histst1...
          2:{ eapply mmap2_unnest_exp_wc. 1,2,4:eauto. eauto. }
          erewrite mmap2_unnest_exp_clocksof in Hsem1'. 3:eauto. 2:eauto.
          apply Forall2_eq in Hl1. rewrite Hl1.
          clear - Hsem1' Fby Href2. rewrite Forall2_map_2 in *.
          revert Fby Hsem1'. generalize (clocksof e0s) (concat s0ss) (concat sss).
          induction vs; intros * Fby Hsem1'; inv Fby; inv Hsem1'; constructor; eauto.
          eapply ac_fby1 in H3. rewrite <-H3.
          eapply sem_clock_refines...
        * clear - Hsemvars. solve_forall. eauto with lcsem.
        * repeat rewrite Forall_app. repeat split.
          apply mk_equations_Forall.
          2-3:(solve_forall; repeat (eapply sem_equation_refines; eauto)).
          clear - Hsemvars Hsemf.
          remember (unnest_fby _ _ _) as fby. clear Heqfby.
          simpl_forall.
          rewrite_Forall_forall. congruence.
          destruct (nth _ x5 _) eqn:Hnth1.
          econstructor.
          -- repeat constructor.
             eapply H0... congruence.
          -- repeat constructor.
             eapply H2 with (x1:=(i, a1))...
      - (* arrow *)
        inversion_clear Hwc as [| | | | | | |??? Hwc1 Hwc2 Hl1 Hl2| | | |].
        inversion_clear Hsem as [| | | | | | |???????? Hsem1 Hsem2 Arrow| | | | |].
        assert (length (concat x2) = length (annots e0s)) as Hlength1 by (eapply mmap2_unnest_exp_length; eauto with lclocking).
        assert (length (concat x6) = length (annots es)) as Hlength2 by (eapply mmap2_unnest_exp_length; eauto with lclocking).
        assert (Forall (fun e => numstreams e = 1) (concat x2)) as Hnumstreams.
        { eapply mmap2_unnest_exp_numstreams in H2... }

        assert (length s0ss = length e0s) as Hlen1 by (eapply Forall2_length in Hsem1; eauto).
        assert (H2':=H2). eapply mmap2_sem in H2... clear H.
        destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1' Hsem1'']]]]]. apply Forall2_concat in Hsem1'.

        assert (Forall2 (sem_exp_ck G1 (H', Hl) b) es sss) as Hsem' by (rewrite_Forall_forall; eapply sem_exp_refines; eauto).
        assert (length sss = length es) as Hlen2 by (eapply Forall2_length in Hsem2; eauto).
        assert (H3':=H3). eapply mmap2_sem in H3... clear H0.
        2:solve_forall; repeat solve_incl.
        destruct H3 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2' Hsem2'']]]]]. apply Forall2_concat in Hsem2'.

        assert (Forall2 (fun e v => sem_exp_ck G2 (H'', Hl) b e [v]) (concat x2) (concat s0ss)) as Hsem''.
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

        assert (Forall2 (fun e v => sem_exp_ck G2 (H'''', Hl) b e [v]) (unnest_arrow (concat x2) (concat x6) a) vs) as Hsemf.
        { eapply unnest_arrow_sem; simpl...
          + eapply mmap2_unnest_exp_length in H2'... eapply Forall2_length in Hl1. solve_length.
          + eapply mmap2_unnest_exp_length in H3'... eapply Forall2_length in Hl2. solve_length.
          + clear - Hsem1' Href2 Href4. eapply Forall2_impl_In... intros; simpl in *.
            repeat (eapply sem_exp_refines; eauto).
          + clear - Hsem2' Href2 Href4. eapply Forall2_impl_In... intros; simpl in *.
            repeat (eapply sem_exp_refines; eauto). }

        exists H''''. split;[|split;[|split;[|split]]];eauto with norm.
        * repeat (etransitivity; eauto).
        * subst. eapply idents_for_anns_hist_st in H4; eauto.
          eapply sc_exps2 in Hsem1'; eauto. 2:destruct Histst1...
          2:{ eapply mmap2_unnest_exp_wc. 1,2,4:eauto. eauto. }
          erewrite mmap2_unnest_exp_clocksof in Hsem1'. 3:eauto. 2:eauto.
          apply Forall2_eq in Hl1. rewrite Hl1.
          clear - Hsem1' Arrow Href2. rewrite Forall2_map_2 in *.
          revert Arrow Hsem1'. generalize (clocksof e0s) (concat s0ss) (concat sss).
          induction vs; intros * Arrow Hsem1'; inv Arrow; inv Hsem1'; constructor; eauto.
          eapply ac_arrow1 in H3. rewrite <-H3.
          eapply sem_clock_refines...
      * clear - Hsemvars. solve_forall. auto with lcsem.
        * repeat rewrite Forall_app. repeat split.
          apply mk_equations_Forall.
          2-3:(solve_forall; repeat (eapply sem_equation_refines; eauto)).
          clear - Hsemvars Hsemf.
          remember (unnest_arrow _ _ _) as arrow. clear Heqarrow.
          simpl_forall.
          rewrite_Forall_forall. congruence.
          destruct (nth _ x5 _) eqn:Hnth1.
          econstructor.
          -- repeat constructor.
             eapply H0... congruence.
          -- repeat constructor.
             eapply H2 with (x1:=(i, a1))...

      - (* when *)
        inv Hwc. inv Hsem. repeat inv_bind.
        assert (length (concat x1) = length (annots es)) as Hlength by (eapply mmap2_unnest_exp_length; eauto with lclocking).
        assert (length es = length ss) by (apply Forall2_length in H13; auto).
        eapply mmap2_sem in H1... clear H.
        destruct H1 as [H' [Hvalid1 [Href1 [Hhistst1 [Hsem1 Hsem1']]]]].
        apply Forall2_concat in Hsem1.
        exists H'. repeat (split; simpl; eauto).
        eapply unnest_when_sem... solve_length.
        eapply sem_var_refines...

      - (* merge *)
        inv Hwc. inv Hsem. repeat inv_bind.
        eapply mmap2_mmap2_sem in H as (Hi1&Href1&Hvalid1&Histst1&Hsem1&Hsem1')...
        assert (Forall2 (fun e v => sem_exp_ck G2 (Hi1, Hl) b e [v])
                        (unnest_merge (x0, tx) x tys ck) vs) as Hsem'.
        { eapply unnest_merge_sem...
          - eapply mmap2_length_1 in H1.
            destruct es, x; simpl in *; try congruence; auto.
          - eapply mmap2_mmap2_unnest_exp_wc; eauto.
          - eapply mmap2_mmap2_unnest_exp_annots in H1. 2:eapply Forall_impl; [|eapply H6]; intros (?&?); eauto with lclocking.
            eapply Forall_forall; intros.
            eapply Forall2_ignore1, Forall_forall in H1 as ((?&?)&Hin2&?); eauto.
            eapply Forall_forall in H8; eauto.
            rewrite H1, H8, length_clocksof_annots; eauto.
          - eapply mmap2_mmap2_unnest_exp_numstreams; eauto.
          - eapply sem_var_refines... }
        destruct is_control; repeat inv_bind.
        + (* control *)
          exists Hi1. repeat (split; simpl; eauto).
        + (* exp *)
          remember (Env.adds (List.map fst x3) vs Hi1) as Hi2.
          assert (length vs = length x3) as Hlength'.
          { eapply idents_for_anns_length in H. repeat simpl_length.
            apply Forall2Brs_length1 in H15.
            2:{ do 2 (eapply Forall_forall; intros); eapply sem_exp_numstreams, sem_exp_ck_sem_exp; eauto.
                do 2 (eapply Forall_forall in H6; eauto with lclocking). }
            inv H15; try congruence. inv H8; auto.
            eapply Forall2_length in H16. solve_length. }
          assert (Env.refines (@EqSt _) Hi1 Hi2) as Href3.
          { subst. eapply idents_for_anns_refines...
            destruct Histst1 as (Hdom1&_). ndup_simpl... }
          assert (Forall2 (sem_var Hi2) (map fst x3) vs) as Hvars.
          { rewrite HeqHi2. eapply sem_var_adds... 1:rewrite map_length...
            rewrite <- fst_NoDupMembers. eapply idents_for_anns_NoDupMembers in H... }
          exists Hi2. split;[|split;[|split;[|split]]]; eauto with norm.
          * repeat (etransitivity; eauto).
          * subst. eapply idents_for_anns_hist_st...
            erewrite map_map, map_ext, <-unnest_merge_clocksof with (nck:=ck); auto.
            { change Hi1 with (fst (Hi1, Hl)). eapply sc_exps2; eauto. destruct Histst1; eauto.
              - eapply unnest_merge_wc_exp; eauto.
                + repeat solve_incl.
                + eapply mmap2_length_1 in H1.
                  contradict H5; subst; destruct es; simpl in *; congruence.
                + eapply mmap2_mmap2_unnest_exp_length in H1; eauto.
                  2:{ eapply Forall_impl; [|eapply H6]; eauto; intros; simpl in *.
                      eapply Forall_impl; eauto with lclocking. }
                  eapply Forall_forall; intros.
                  eapply Forall2_ignore1, Forall_forall in H1 as (?&?&Heq)...
                  eapply Forall_forall in H8...
                  rewrite Heq, H8. solve_length.
                + eapply mmap2_mmap2_unnest_exp_wc...
                + eapply mmap2_mmap2_unnest_exp_clocksof1; eauto.
            }
          * clear - Hvars. solve_forall. eauto with lcsem.
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

      - (* case (total) *)
        repeat inv_bind.
        assert (length x = 1). 2:singleton_length.
        { eapply unnest_exp_length in H2... rewrite H2, <-length_clockof_numstreams, H7; auto. }
        assert (Hun1:=H2). eapply IHe in H2 as (Hi1&Href1&Hvalid1&Histst1&Hsem1&Hsem1')... clear IHe.
        eapply Forall2_singl in Hsem1.

        assert (Forall (fun es => Forall (wc_exp G1 (vars ++ st_senv x1)) (snd es)) es) as Hwces.
        { do 2 (eapply Forall_forall; intros).
          do 2 (eapply Forall_forall in H9; eauto). repeat solve_incl. }
        assert (Forall2Brs (sem_exp_ck G1 (Hi1, Hl) b) es vs0) as Hses.
        { eapply Forall2Brs_impl_In; [|eauto]; intros ?? _ Hse.
          eapply sem_exp_refines... }
        eapply mmap2_mmap2_sem in H as (Hi2&Href2&Hvalid2&Histst2&Hsem2&Hsem2')...

        assert (Forall2 (fun e v => sem_exp_ck G2 (Hi2, Hl) b e [v])
                        (unnest_case e0 x2 None tys ck) vs) as Hsem'.
        { eapply unnest_case_sem...
          - eapply mmap2_length_1 in H3.
            destruct es, x2; simpl in *; try congruence; auto.
          - eapply mmap2_mmap2_unnest_exp_wc; eauto.
          - eapply mmap2_mmap2_unnest_exp_annots in H3. 2:eapply Forall_impl; [|eapply H9]; intros (?&?); eauto with lclocking.
            eapply Forall_forall; intros.
            eapply Forall2_ignore1, Forall_forall in H3 as ((?&?)&Hin2&?); eauto.
            eapply Forall_forall in H11; eauto.
            rewrite H2, H11, length_clocksof_annots; eauto.
          - eapply mmap2_mmap2_unnest_exp_numstreams; eauto.
          - eapply sem_exp_refines...
          - simpl. reflexivity. }
        destruct is_control; repeat inv_bind.
        + (* control *)
          exists Hi2. repeat (split; simpl; eauto).
          * etransitivity...
          * apply Forall_app; split; auto.
            eapply Forall_impl_In; [|eauto]; intros. eapply sem_equation_refines...
        + (* exp *)
          remember (Env.adds (List.map fst x) vs Hi2) as Hi3.
          assert (length vs = length x) as Hlength'.
          { eapply idents_for_anns_length in H. repeat simpl_length.
            apply Forall2Brs_length1 in H21.
            2:{ simpl_Forall; eapply sem_exp_numstreams, sem_exp_ck_sem_exp; eauto with lclocking. }
            inv H21; try congruence. inv H11; auto.
            eapply Forall3_length in H22 as (?&?). solve_length. }
          assert (Env.refines (@EqSt _) Hi2 Hi3) as Href3.
          { subst. eapply idents_for_anns_refines...
            destruct Histst2 as (Hdom1&_). ndup_simpl... }
          assert (Forall2 (sem_var Hi3) (map fst x) vs) as Hvars.
          { rewrite HeqHi3. eapply sem_var_adds... 1:rewrite map_length...
            rewrite <- fst_NoDupMembers. eapply idents_for_anns_NoDupMembers in H... }
          exists Hi3. split;[|split;[|split;[|split]]]; eauto with norm.
          * repeat (etransitivity; eauto).
          * subst. eapply idents_for_anns_hist_st...
            erewrite map_map, map_ext, <-unnest_case_clocksof with (nck:=ck); auto.
            { change Hi2 with (fst (Hi2, Hl)). eapply sc_exps2; eauto. destruct Histst2; eauto.
              - eapply unnest_case_wc_exp; eauto.
                + eapply unnest_exp_wc in Hun1 as (Hwc&_); eauto. apply Forall_singl in Hwc.
                  repeat solve_incl.
                + eapply unnest_exp_clockof in Hun1; eauto with lclocking. simpl in Hun1; rewrite app_nil_r in Hun1.
                  congruence.
                + eapply mmap2_length_1 in H3.
                  contradict H8; subst; destruct es; simpl in *; congruence.
                + eapply mmap2_mmap2_unnest_exp_length in H3; eauto.
                  2:{ eapply Forall_impl; [|eapply H9]; eauto; intros; simpl in *.
                      eapply Forall_impl; eauto with lclocking. }
                  eapply Forall_forall; intros.
                  eapply Forall2_ignore1, Forall_forall in H3 as (?&?&Heq)...
                  eapply Forall_forall in H11...
                  rewrite Heq, H11. solve_length.
                + eapply mmap2_mmap2_unnest_exp_wc...
                + eapply mmap2_mmap2_unnest_exp_clocksof2; eauto.
            }
          * clear - Hvars. solve_forall. eauto with lcsem.
          * repeat rewrite Forall_app; repeat split.
            -- remember (unnest_case _ _ _ _ _) as merge.
               assert (length merge = length x) as Hlength''.
               { eapply idents_for_anns_length in H.
                 subst. rewrite unnest_case_length. solve_length. }
               clear - Hvars Hsem' Href3 Hlength''. apply mk_equations_Forall. simpl_forall.
               rewrite Forall2_swap_args in Hsem'.
               eapply Forall2_trans_ex in Hsem'; [|eauto].
               eapply Forall2_impl_In; [|eauto]. intros (?&?) ? _ _ (?&?&?&?).
               apply Seq with (ss:=[[x0]]); simpl.
               1,2:repeat constructor... eapply sem_exp_refines...
            -- solve_forall. repeat (eapply sem_equation_refines; eauto).
            -- solve_forall. repeat (eapply sem_equation_refines; eauto).

      - (* case (default) *)
        repeat inv_bind. simpl in *.
        assert (length x = 1). 2:singleton_length.
        { eapply unnest_exp_length in H2... rewrite H2, <-length_clockof_numstreams, H7; auto. }
        assert (Hun1:=H2). eapply IHe in H2 as (Hi1&Href1&Hvalid1&Histst1&Hsem1&Hsem1')... clear IHe.
        eapply Forall2_singl in Hsem1.

        assert (Forall (fun es => Forall (wc_exp G1 (vars ++ st_senv x1)) (snd es)) es) as Hwces.
        { simpl_Forall. repeat solve_incl. }
        assert (Forall2Brs (sem_exp_ck G1 (Hi1, Hl) b) es vs0) as Hses.
        { eapply Forall2Brs_impl_In; [|eauto]; intros ?? _ Hse.
          eapply sem_exp_refines... }
        eapply mmap2_mmap2_sem in H as (Hi2&Href2&Hvalid2&Histst2&Hsem2&Hsem2')...

        assert (Forall (wc_exp G1 (vars ++ st_senv x4)) d0) as Hwd.
        { eapply Forall_forall; intros.
          specialize (H12 _ eq_refl). eapply Forall_forall in H12... repeat solve_incl. }
        assert (Forall2 (sem_exp_ck G1 (Hi2, Hl) b) d0 vd) as Hsd.
        { eapply Forall2_impl_In; [|eauto]. intros.
          eapply sem_exp_refines; [|eauto]. etransitivity... }
        eapply mmap2_sem in H0 as (Hi3&Href3&Hvalid3&Histst3&Hsem3&Hsem3')...

        assert (Forall2 (fun e v => sem_exp_ck G2 (Hi3, Hl) b e [v])
                        (unnest_case e0 x2 (Some (concat x5)) tys ck) vs) as Hsem'.
        { eapply unnest_case_sem...
          - eapply mmap2_length_1 in H3.
            destruct es, x2; simpl in *; try congruence; auto.
          - eapply mmap2_mmap2_unnest_exp_wc; eauto.
          - eapply mmap2_mmap2_unnest_exp_annots in H3. 2:eapply Forall_impl; [|eapply H9]; intros (?&?); eauto with lclocking.
            eapply Forall_forall; intros.
            eapply Forall2_ignore1, Forall_forall in H3 as ((?&?)&Hin2&?); eauto.
            eapply Forall_forall in H11; eauto.
            rewrite H0, H11, length_clocksof_annots; eauto.
          - eapply mmap2_mmap2_unnest_exp_numstreams; eauto.
          - repeat (eapply sem_exp_refines; eauto).
          - simpl. eapply unnest_exp_typeof in Hun1; eauto with lclocking.
            simpl in *; rewrite app_nil_r in *. congruence.
          - eapply Forall2Brs_impl_In; [|eauto]; intros ?? _ Hse.
            eapply sem_exp_refines...
          - simpl. repeat esplit; eauto.
            apply Forall2_concat; auto. }
        destruct is_control; repeat inv_bind.
        + (* control *)
          exists Hi3. repeat (split; simpl; eauto).
          * do 2 (etransitivity; eauto).
          * repeat rewrite Forall_app; repeat split; auto.
            1,2:eapply Forall_impl_In; [|eauto]; intros. 1,2:repeat (eapply sem_equation_refines; eauto).
        + (* exp *)
          remember (Env.adds (List.map fst x) vs Hi3) as Hi4.
          assert (length vs = length x) as Hlength'.
          { eapply idents_for_anns_length in H. repeat simpl_length.
            apply Forall2Brs_length1 in H21.
            2:{ do 2 (eapply Forall_forall; intros); eapply sem_exp_numstreams, sem_exp_ck_sem_exp; eauto.
                do 2 (eapply Forall_forall in H9; eauto with lclocking). }
            inv H21; try congruence. inv H11; auto.
            eapply Forall3_length in H23 as (?&?). solve_length. }
          assert (Env.refines (@EqSt _) Hi3 Hi4) as Href4.
          { subst. eapply idents_for_anns_refines...
            destruct Histst3 as (Hdom1&_). ndup_simpl... }
          assert (Forall2 (sem_var Hi4) (map fst x) vs) as Hvars.
          { rewrite HeqHi4. eapply sem_var_adds... 1:rewrite map_length...
            rewrite <- fst_NoDupMembers. eapply idents_for_anns_NoDupMembers in H... }
          exists Hi4. split;[|split;[|split;[|split]]]; eauto with norm.
          * repeat (etransitivity; eauto).
          * subst. eapply idents_for_anns_hist_st...
            erewrite map_map, map_ext, <-unnest_case_clocksof with (nck:=ck); auto.
            { change Hi3 with (fst (Hi3, Hl)). eapply sc_exps2; eauto. destruct Histst3; eauto.
              - eapply unnest_case_wc_exp; eauto.
                + eapply unnest_exp_wc in Hun1 as (Hwc&_); eauto. apply Forall_singl in Hwc.
                  repeat solve_incl.
                + eapply unnest_exp_clockof in Hun1; eauto with lclocking. simpl in Hun1; rewrite app_nil_r in Hun1.
                  congruence.
                + eapply mmap2_length_1 in H3.
                  contradict H8; subst; destruct es; simpl in *; congruence.
                + eapply mmap2_mmap2_unnest_exp_length in H3; eauto.
                  2:{ eapply Forall_impl; [|eapply H9]; eauto; intros; simpl in *.
                      eapply Forall_impl; eauto with lclocking. }
                  eapply Forall_forall; intros.
                  eapply Forall2_ignore1, Forall_forall in H3 as (?&?&Heq)...
                  eapply Forall_forall in H11...
                  rewrite Heq, H11. solve_length.
                + eapply mmap2_mmap2_unnest_exp_wc in H3 as (Hwc&_)...
                  eapply Forall_impl; [|eapply Hwc]; intros; simpl in *.
                  eapply Forall_impl; [|eauto]; intros.
                  repeat solve_incl.
                + eapply mmap2_mmap2_unnest_exp_clocksof2; eauto.
                + simpl. erewrite length_clocksof_annots, mmap2_unnest_exp_annots_length. 3:eauto. 2:eauto with lclocking.
                  specialize (H14 _ eq_refl). solve_length.
                + simpl. eapply mmap2_unnest_exp_wc...
                + simpl. eapply mmap2_unnest_exp_clocksof'''; eauto.
            }
          * clear - Hvars. solve_forall. eauto with lcsem.
          * repeat rewrite Forall_app; repeat split.
            -- remember (unnest_case _ _ _ _ _) as merge.
               assert (length merge = length x) as Hlength''.
               { eapply idents_for_anns_length in H.
                 subst. rewrite unnest_case_length. solve_length. }
               clear - Hvars Hsem' Href4 Hlength''. apply mk_equations_Forall. simpl_forall.
               rewrite Forall2_swap_args in Hsem'.
               eapply Forall2_trans_ex in Hsem'; [|eauto].
               eapply Forall2_impl_In; [|eauto]. intros (?&?) ? _ _ (?&?&?&?).
               apply Seq with (ss:=[[x0]]); simpl.
               1,2:repeat constructor... eapply sem_exp_refines...
            -- solve_forall. repeat (eapply sem_equation_refines; eauto).
            -- solve_forall. repeat (eapply sem_equation_refines; eauto).
            -- solve_forall. repeat (eapply sem_equation_refines; eauto).

      - (* app *)
        assert (a = map snd x8) as Hanns; subst.
        { eapply idents_for_anns_values in H5... }
        specialize (idents_for_anns_length _ _ _ _ H5) as Hlength1.
        assert (length (n_out n) = length vs) as Hlength2.
        { specialize (H23 0). inv H23. apply Forall2_length in H9.
          unfold idents in *. repeat rewrite map_length in H9. congruence. }
        assert (length es = length ss) as Hlength3.
        { apply Forall2_length in H19... }
        assert (length (concat x6) = length (n_in n)) as Hlength4.
        { eapply mmap2_unnest_exp_length in H2; eauto with lclocking. eapply Forall2_length in H13.
          rewrite map_length in H13. rewrite H13. subst_length. now rewrite length_nclocksof_annots. }

        assert (Hun1:=H2). eapply mmap2_sem in H2... clear H.
        destruct H2 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].

        assert (Hun2:=H3). eapply unnest_noops_exps_sem in H3 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2'); eauto.
        3:{ eapply mmap2_normalized_lexp in Hun1. 1,3:eauto with lclocking.
            apply NoLast_app; split; auto. apply senv_of_tyck_NoLast. }
        4:eapply Forall2_concat; eauto.
        2:{ unfold find_node_incks. now rewrite H12, map_length. }
        2:{ eapply mmap2_unnest_exp_wc in Hun1 as (?&?); eauto. }

        assert (length rs = length er) as Hlen3 by (eapply Forall2_length in H21; eauto).
        assert (Forall2 (fun er sr => sem_exp_ck G1 (H'', Hl) b er [sr]) er rs) as Hsemr' by (rewrite_Forall_forall; repeat (eapply sem_exp_refines; eauto)).
        assert (Hun3:=H4). eapply unnest_resets_sem in H4...
        2:(solve_forall; repeat solve_incl).
        2:{ eapply Forall_impl; [|eapply H15]; intros ? Hck. destruct Hck as (?&Hck).
            rewrite <-length_clockof_numstreams, Hck; auto. }
        2:{ solve_forall. eapply H16 in H11 as (H'''&?&?&?&?&?); eauto. exists H'''; split;[|split;[|split;[|split]]]; eauto.
            inv H24; eauto. }
        destruct H4 as (H'''&Href3&Hvalid3&Histst3&Hsem3&Hsem3').

        assert (sem_exp_ck G2 (H''', Hl) b (Eapp f x2 x5 (map snd x8)) vs) as Hsem'.
        { eapply Sapp with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss)))...
          + rewrite <- concat_map, Forall2_map_2.
            solve_forall. eapply sem_exp_refines...
          + intros k. specialize (H23 k).
            rewrite concat_map_singl2. eapply HGref; eauto. }
        remember (Env.adds (map fst x8) vs H''') as H''''.
        assert (length vs = length x8) as Hlen'.
        { eapply Forall2_length in H14. rewrite 2 map_length in H14. solve_length. }
        assert (Env.refines (@EqSt _) H''' H'''') as Href4.
        { subst. eapply idents_for_anns_refines...
          destruct Histst3 as (Hdom3&_); auto.
        }
        assert (NoDupMembers x8) as Hndup'.
        { eapply idents_for_anns_NoDupMembers in H5... }
        assert (Forall2 (sem_var H'''') (map fst x8) vs) as Hvars.
        { rewrite HeqH''''. eapply sem_var_adds... 1:rewrite map_length... rewrite <- fst_NoDupMembers... }
        exists H''''. split;[|split;[|split;[|split]]]...
        + repeat (etransitivity; eauto).
        + subst. assert (Hids:=H5). eapply idents_for_anns_hist_st in H5...
          assert (Hwc:=H10). eapply mmap2_unnest_exp_wc in H10 as (Hwc'&_); eauto.
          eapply Forall2_concat in Hsem1.
          erewrite map_ext, <-map_map.
          change H''' with (fst (H''', Hl)). eapply sc_outside_mask' with (es:=es) (G:=G1); eauto.
          4:intros (?&?); auto.
          * eapply Forall2_impl_In; [|eauto]; intros; simpl in *.
            repeat (eapply sem_exp_refines; eauto).
          * rewrite 2 Forall2_map_1. rewrite Forall2_map_1 in Hvars.
            eapply Forall2_impl_In; [|eauto]; intros (?&?&?) ? _ _ _; simpl; auto.
          * eapply sc_exps in H19; eauto. 2:destruct Histst; auto.
            eapply Forall2_impl_In; [|eauto]; intros.
            repeat (eapply sem_clock_refines; eauto).
        + clear - Hvars. solve_forall. eauto with lcsem.
        + constructor; [| repeat rewrite Forall_app; repeat split].
          * apply Seq with (ss:=[vs]).
            -- repeat constructor...
               eapply sem_exp_refines...
            -- simpl. rewrite app_nil_r; auto.
          * solve_forall. repeat (eapply sem_equation_refines; eauto).
          * solve_forall. repeat (eapply sem_equation_refines; eauto).
          * solve_forall. eapply sem_equation_refines...
            Unshelve. 1,2:exact default_stream.
    Qed.

    Corollary unnest_exps_sem : forall vars b es H Hl vs es' eqs' st st',
        (forall x, ~IsLast vars x) ->
        Forall (wc_exp G1 (vars++st_senv st)) es ->
        Forall2 (sem_exp_ck G1 (H, Hl) b) es vs ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars b (H, Hl) st ->
        mmap2 (unnest_exp G1 false) es st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars b (H', Hl) st' /\
            Forall2
              (fun (es : list exp) (vs : list (Stream svalue)) =>
                 Forall2 (fun e v => sem_exp_ck G2 (H', Hl) b e [v]) es vs) es' vs /\
            Forall (sem_equation_ck G2 (H', Hl) b) (concat eqs')).
    Proof.
      intros * Hnl Hwt Hsem Hvalid Hhistst Hnorm.
      eapply mmap2_sem in Hnorm; eauto.
      rewrite_Forall_forall.
      eapply unnest_exp_sem; eauto.
    Qed.

    Fact unnest_rhs_sem : forall vars b e H Hl vs es' eqs' st st',
        (forall x, ~IsLast vars x) ->
        wc_exp G1 (vars++st_senv st) e ->
        sem_exp_ck G1 (H, Hl) b e vs ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars b (H, Hl) st ->
        unnest_rhs G1 e st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars b (H', Hl) st' /\
            (Forall2 (fun e v => sem_exp_ck G2 (H', Hl) b e [v]) es' vs \/
             exists e', (es' = [e'] /\ sem_exp_ck G2 (H', Hl) b e' vs)) /\
            Forall (sem_equation_ck G2 (H', Hl) b) eqs').
    Proof with eauto with norm lclocking.
      intros * Hnl Hwt Hsem Hvalid Histst Hnorm.
      destruct e; try (eapply unnest_exp_sem in Hnorm as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem2]]]]]; eauto;
                       exists H'; repeat (split; eauto)).
      1,2,3:unfold unnest_rhs in Hnorm; repeat inv_bind. 3:inv Hwt; inv Hsem.
      - (* fby *)
        inversion_clear Hwt as [| | | | | |??? Hwc1 Hwc2 Hl1 Hl2 | | | | |].
        inversion_clear Hsem as [| | | | | |???????? Hsem1 Hsem2 Fby| | | | | |].
        assert (length x = length (annots l)) as Hlength1 by (eapply unnest_exps_length; eauto with lclocking).
        assert (length x2 = length (annots l0)) as Hlength2 by (eapply unnest_exps_length; eauto with lclocking).
        unfold unnest_exps in *. repeat inv_bind.

        assert (Hun1:=H0). eapply unnest_exps_sem in H0... clear Hsem1.
        destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.
        assert (Forall2 (sem_exp_ck G1 (H', Hl) b) l0 sss) as Hsem' by (rewrite_Forall_forall; eapply sem_exp_refines; eauto).

        eapply unnest_exps_sem in H1... clear Hsem2.
        2:(solve_forall; repeat solve_incl).
        destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
        assert (Forall2 (fun e v => sem_exp_ck G2 (H'', Hl) b e [v]) (concat x2) (concat s0ss)) as Hsem''.
        { solve_forall. eapply sem_exp_refines... }

        exists H''. repeat (split; auto).
        + repeat (etransitivity; eauto).
        + left. eapply unnest_fby_sem...
          * eapply Forall2_length in Hl1; solve_length.
          * eapply Forall2_length in Hl2; solve_length.
        + repeat rewrite Forall_app. repeat split...
          solve_forall; (eapply sem_equation_refines; [|eauto]; etransitivity; eauto with env).
      - (* arrow *)
        inversion_clear Hwt as [| | | | | | |??? Hwc1 Hwc2 Hl1 Hl2| | | |].
        inversion_clear Hsem as [| | | | | | |???????? Hsem1 Hsem2 Fby| | | | |].
        assert (length x = length (annots l)) as Hlength1 by (eapply unnest_exps_length; eauto with lclocking).
        assert (length x2 = length (annots l0)) as Hlength2 by (eapply unnest_exps_length; eauto with lclocking).
        unfold unnest_exps in *. repeat inv_bind.

        assert (Hun1:=H0). eapply unnest_exps_sem in H0... clear Hsem1.
        destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]. apply Forall2_concat in Hsem1.
        assert (Forall2 (sem_exp_ck G1 (H', Hl) b) l0 sss) as Hsem' by (rewrite_Forall_forall; eapply sem_exp_refines; eauto).

        eapply unnest_exps_sem in H1... clear Hsem2.
        2:(solve_forall; repeat solve_incl).
        destruct H1 as [H'' [Href2 [Hvalid2 [Histst2 [Hsem2 Hsem2']]]]]. apply Forall2_concat in Hsem2.
        assert (Forall2 (fun e v => sem_exp_ck G2 (H'', Hl) b e [v]) (concat x2) (concat s0ss)) as Hsem''.
        { solve_forall. eapply sem_exp_refines... }

        exists H''. repeat (split; auto).
        + repeat (etransitivity; eauto).
        + left. eapply unnest_arrow_sem...
          * eapply Forall2_length in Hl1; solve_length.
          * eapply Forall2_length in Hl2; solve_length.
        + repeat rewrite Forall_app. repeat split...
          solve_forall; (eapply sem_equation_refines; [|eauto]; etransitivity; eauto with env).
      - (* app *)
        unfold unnest_exps in H0.
        repeat inv_bind.
        assert (length (concat x6) = length (n_in n)) as Hlength4.
        { eapply mmap2_unnest_exp_length in H0; eauto with lclocking.
          eapply Forall2_length in H10. rewrite map_length in H10. solve_length.
          now rewrite length_nclocksof_annots. }

        assert (Hun1:=H0). eapply unnest_exps_sem in H0...
        destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].

        assert (Hun2:=H1). eapply unnest_noops_exps_sem in H1 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2'); eauto.
        3:{ eapply mmap2_normalized_lexp in Hun1. 1,3:eauto with lclocking.
            apply NoLast_app; split; auto. apply senv_of_tyck_NoLast. }
        4:eapply Forall2_concat...
        2:{ unfold find_node_incks. rewrite H9, map_length; auto. }
        2:{ eapply mmap2_unnest_exp_wc. 1,2,4:eauto. solve_forall; repeat solve_incl. }

        assert (length rs = length l0) as Hlen3 by (eapply Forall2_length in H18; eauto).
        assert (Forall2 (fun er sr => sem_exp_ck G1 (H'', Hl) b er [sr]) l0 rs) as Hsemr'
            by (solve_forall; repeat (eapply sem_exp_refines; eauto)).
        assert (Hr:=H2). eapply unnest_resets_sem in H2...
        2:(solve_forall; repeat solve_incl).
        2:{ solve_forall.
            now rewrite <-length_clockof_numstreams, H1. }
        2:{ solve_forall. eapply unnest_exp_sem in H13 as (H'''&?&?&?&Sem1&?)... inv Sem1...
            exists H'''. repeat (split; eauto). }
        destruct H2 as (H'''&Href3&Hvalid3&Hhistst3&Hsem3&Hsem3').

        exists H'''. repeat (split; auto).
        + repeat (etransitivity; eauto).
        + right. eexists; split...
          apply Sapp with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))) (rs:=rs) (bs:=bs); eauto.
          * rewrite <- concat_map, Forall2_map_2; auto.
            solve_forall. repeat (eapply sem_exp_refines; eauto).
          * rewrite concat_map_singl2. intros k. eapply HGref, H20; eauto.
        + repeat rewrite Forall_app.
          repeat split; solve_forall; (eapply sem_equation_refines; [|eauto]); eauto.
          etransitivity...
    Qed.

    Corollary mmap2_unnest_rhs_sem : forall vars b es H Hl vs es' eqs' st st',
        (forall x, ~IsLast vars x) ->
        Forall (wc_exp G1 (vars++st_senv st)) es ->
        Forall2 (sem_exp_ck G1 (H, Hl) b) es vs ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars b (H, Hl) st ->
        mmap2 (unnest_rhs G1) es st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars b (H', Hl) st' /\
            Forall2 (fun es' vs =>
                       Forall2 (fun e v => sem_exp_ck G2 (H', Hl) b e [v]) es' vs \/
                       exists e', (es' = [e'] /\ sem_exp_ck G2 (H', Hl) b e' vs)) es' vs /\
            Forall (sem_equation_ck G2 (H', Hl) b) (concat eqs')).
    Proof with eauto.
      induction es; intros * Hnl Hwt Hsem Hvalid Histst Hmap;
        repeat inv_bind.
      - exists H; simpl. inv Hsem. repeat (split; auto with env).
      - inv Hwt. inv Hsem.

        assert (st_follows st x1) as Hfollows1 by eauto with norm.
        eapply unnest_rhs_sem in H0...
        destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].
        assert (Forall2 (sem_exp_ck G1 (H', Hl) b) es l') as Hsem'.
        { eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines; eauto. }

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

    Corollary unnest_rhss_sem : forall vars b es H Hl vs es' eqs' st st',
        (forall x, ~IsLast vars x) ->
        Forall (wc_exp G1 (vars++st_senv st)) es ->
        Forall2 (sem_exp_ck G1 (H, Hl) b) es vs ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars b (H, Hl) st ->
        unnest_rhss G1 es st = (es', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars b (H', Hl) st' /\
            Forall (fun '(e, v) => sem_exp_ck G2 (H', Hl) b e v)
                   (combine_for_numstreams es' (concat vs)) /\
            Forall (sem_equation_ck G2 (H', Hl) b) eqs').
    Proof with eauto with lclocking.
      intros * Hnl Hwt Hsem Hvalid Histst Hnorm.
      assert (Forall (wc_exp G2 (vars++st_senv st')) es') as Hwt'.
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
        + rewrite CommonList.skipn_app...
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
        simpl in *; try lia.
      rewrite app_length in *. rewrite length_annot_numstreams in *.
      destruct n.
      - inv Hnth1; inv Hnth2.
        rewrite firstn_length in Hn0; rewrite Nat.min_glb_lt_iff in Hn0; destruct Hn0.
        exists n0. repeat split...
        + rewrite nth_firstn_1...
        + rewrite nth_firstn_1...
      - apply Lt.lt_S_n in Hn.
        eapply IHes in Hn. 4,5,6:eauto.
        + destruct Hn as [n' [Hlen' [Hnth1' Hnth2']]].
          exists (n'+(numstreams a)).
          repeat split.
          * rewrite skipn_length in Hlen'. lia.
          * rewrite nth_skipn in Hnth1'...
          * rewrite nth_skipn in Hnth2'...
        + rewrite skipn_length. lia.
        + rewrite skipn_length. lia.
    Qed.

    Fact unnest_equation_sem : forall vars H Hl b equ eqs' st st',
        (forall x, ~IsLast vars x) ->
        wc_equation G1 (vars++st_senv st) equ ->
        sem_equation_ck G1 (H, Hl) b equ ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars b (H, Hl) st ->
        unnest_equation G1 equ st = (eqs', st') ->
        (exists H', Env.refines (@EqSt _) H H' /\
               st_valid_after st' (PSP.of_list (map fst vars)) /\
               hist_st vars b (H', Hl) st' /\
               Forall (sem_equation_ck G2 (H', Hl) b) eqs').
    Proof with eauto with norm lclocking.
      intros * Hnl Hwt Hsem Hvalid Histst Hnorm.
      unfold unnest_equation in Hnorm.
      destruct equ as [xs es]. inv Hwt; inv Hsem.
      - (* app *)
        assert (length xs = length anns) as Hlen.
        { eapply Forall3_length in H6 as (_&Hlen). rewrite map_length in Hlen; auto. }

        unfold unnest_rhss in *.
        repeat inv_bind. unfold unnest_exps in H0; repeat inv_bind.
        inv H12; inv H16. inv H14. simpl in *; rewrite app_nil_r in *.
        assert (length (concat x) = length (n_in n)) as Hlength4.
        { eapply mmap2_unnest_exp_length in H0; eauto with lclocking.
          eapply Forall2_length in H5. rewrite map_length in H5. solve_length.
          now rewrite length_nclocksof_annots. }

        assert (Hun1:=H0). eapply unnest_exps_sem in H0...
        destruct H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]].

        assert (Hun2:=H1). eapply unnest_noops_exps_sem in H1 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2'); eauto.
        3:{ eapply mmap2_normalized_lexp in Hun1. 1,3:eauto with lclocking.
            apply NoLast_app; split; auto. apply senv_of_tyck_NoLast. }
        4:eapply Forall2_concat...
        2:{ unfold find_node_incks. rewrite H4, map_length; auto. }
        2:{ eapply mmap2_unnest_exp_wc. 1,2,4:eauto. solve_forall; repeat solve_incl. }

        assert (length rs = length er) as Hlen3 by (eapply Forall2_length in H21; eauto).
        assert (Forall2 (fun er sr => sem_exp_ck G1 (H'', Hl) b er [sr]) er rs) as Hsemr'
            by (solve_forall; repeat (eapply sem_exp_refines; eauto)).
        assert (Hr:=H9). eapply unnest_resets_sem in H9...
        2:(solve_forall; repeat solve_incl).
        2:{ solve_forall.
            now rewrite <-length_clockof_numstreams, H1. }
        2:{ solve_forall. eapply unnest_exp_sem in H15 as (H'''&?&?&?&Sem1&?)... inv Sem1...
            exists H'''. repeat (split; eauto). }
        destruct H9 as (H'''&Href3&Hvalid3&Hhistst3&Hsem3&Hsem3').

        exists H'''. repeat (split; auto). 2:constructor.
        + repeat (etransitivity; eauto).
        + econstructor. econstructor; eauto.
          apply Sapp with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))) (rs:=rs) (bs:=bs); eauto.
          * rewrite <- concat_map, Forall2_map_2; auto.
            solve_forall. repeat (eapply sem_exp_refines; eauto).
          * rewrite concat_map_singl2. intros k. eapply HGref, H23; eauto.
          * simpl; rewrite app_nil_r. rewrite firstn_all2; [|rewrite Hlen; reflexivity].
            eapply Forall2_impl_In; [|eauto]; intros.
            eapply sem_var_refines; [|eauto]. repeat (etransitivity; eauto).
        + rewrite skipn_all2; [|rewrite Hlen; reflexivity]; simpl.
          repeat rewrite Forall_app.
          repeat split; solve_forall; (eapply sem_equation_refines; [|eauto]); eauto.
          etransitivity...

      - (* general case *)
        repeat inv_bind.
        assert (annots x = annots es) as Hannots by (eapply unnest_rhss_annots; eauto with lclocking).
        assert (Hun:=H2). eapply unnest_rhss_sem in H0 as (H'&Href1&Hvalid1&Histst1&Hsem1&Hsem1')...
        exists H'. repeat (split; eauto).
        apply Forall_app. split...
        clear Hsem1'.
        assert (length (concat ss) = length (annots es)) as Hlen1.
        { eapply sem_exps_ck_sem_exps, sem_exps_numstreams in H7; eauto with lclocking. }
        assert (length xs = length (annots x)) as Hlen2.
        { rewrite Hannots, <-Hlen1.
          rewrite_Forall_forall. simpl_length. congruence. }
        rewrite_Forall_forall.
        destruct x1. simpl_In. assert (HIn:=Hin).
        eapply In_nth with (d:=(hd_default [], [])) in Hin. destruct Hin as [n [Hn Hnth]].
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
        apply Seq with (ss:=[l0]).
        + repeat constructor...
        + simpl. rewrite app_nil_r.
          rewrite_Forall_forall.
          * replace (length l) with (numstreams e0). replace (length l0) with (numstreams e0). reflexivity.
            { eapply Forall_forall in HIn'. 2:eapply combine_for_numstreams_numstreams; try congruence.
              eauto. }
            { eapply Forall_forall in HIn. 2:eapply combine_for_numstreams_numstreams; try congruence.
              eauto. }
          * eapply sem_var_refines...
            specialize (combine_for_numstreams_nth_2 x xs (concat ss) n n0 e0 l l0
                                                     a b0 (hd_default [], []) (hd_default [], [])) as Hcomb.
            apply Hcomb in H7. clear Hcomb.
            2,3:congruence.
            2:(rewrite combine_for_numstreams_length in Hn; auto; congruence).
            2,3:auto.
            destruct H7 as (?&?&?&?).
            eapply H1...
    Qed.

    Lemma hist_st_mask : forall vars bs H st r k,
        hist_st vars bs H st ->
        hist_st vars (maskb k r bs) (mask_hist k r H) st.
    Proof.
      intros * (?&?).
      split.
      - eapply Env.dom_map; eauto.
      - eapply LCS.sc_vars_mask; eauto.
    Qed.

    Lemma hist_st_unmask : forall vars bs H st r,
        (forall k, hist_st vars (maskb k r bs) (mask_hist k r H) st) ->
        hist_st vars bs H st.
    Proof.
      intros * Hk.
      constructor.
      - eapply Env.dom_map. eapply (Hk 0).
      - eapply sc_vars_unmask. intros. eapply Hk.
    Qed.

    Fact mmap_unnest_block_sem : forall vars b blocks H Hl blocks' st st',
        Forall
         (fun d : block => forall H Hl b blocks' st st',
          wc_block G1 (vars ++ st_senv st) d ->
          sem_block_ck G1 (H, Hl) b d ->
          st_valid_after st (PSP.of_list (map fst vars)) ->
          hist_st vars b (H, Hl) st ->
          unnest_block G1 d st = (blocks', st') ->
          exists H' : Env.t (Stream svalue),
            Env.refines (EqSt (A:=svalue)) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars b (H', Hl) st' /\
            Forall (sem_block_ck G2 (H', Hl) b) blocks') blocks ->
        Forall (wc_block G1 (vars ++ st_senv st)) blocks ->
        Forall (sem_block_ck G1 (H, Hl) b) blocks ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars b (H, Hl) st ->
        mmap (unnest_block G1) blocks st = (blocks', st') ->
        (exists H', Env.refines (@EqSt _) H H' /\
               st_valid_after st' (PSP.of_list (map fst vars)) /\
               hist_st vars b (H', Hl) st' /\
               Forall (sem_block_ck G2 (H', Hl) b) (concat blocks')).
    Proof with eauto with env.
      induction blocks; intros * Hf Hwc Hsem Hvalid Histst Hnorm;
        inv Hf; inv Hwc; inv Hsem; repeat inv_bind; simpl.
      - exists H...
      - assert (Forall (wc_block G1 (vars ++ st_senv x0)) blocks) as Hwc'.
        { solve_forall. repeat solve_incl. }
        eapply H2 in H0 as (H'&Href1&Hvalid1&Histst1&Hsem1)...
        assert (Forall (sem_block_ck G1 (H', Hl) b) blocks) by (solve_forall; eapply sem_block_refines; eauto).

        eapply IHblocks in H1 as (H''&Href2&Hvalid2&Histst2&Hsem2)...
        exists H''. split;[|split;[|split]]...
        + etransitivity...
        + eapply Forall_app. split...
          solve_forall. eapply sem_block_refines...
    Qed.

    Lemma unnest_block_sem : forall vars d H Hl b blocks' st st',
        (forall x, ~IsLast vars x) ->
        wc_block G1 (vars++st_senv st) d ->
        sem_block_ck G1 (H, Hl) b d ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars b (H, Hl) st ->
        unnest_block G1 d st = (blocks', st') ->
        (exists H', Env.refines (@EqSt _) H H' /\
               st_valid_after st' (PSP.of_list (map fst vars)) /\
               hist_st vars b (H', Hl) st' /\
               Forall (sem_block_ck G2 (H', Hl) b) blocks').
    Proof with eauto.
      intros * Hnl. revert H Hl b blocks' st st'.
      induction d using block_ind2; intros * Hwc Hsem Hvalid Histst Hnorm;
        inv Hwc; inv Hsem; repeat inv_bind.
      - (* Equation *)
        eapply unnest_equation_sem in H0 as (H'&?&?&?&?); eauto.
        exists H'. split;[|split;[|split]]; auto.
        rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
        constructor; auto.
      - (* Reset *)
        assert (forall k, exists H',
                     Env.refines (@EqSt _) (CStr.mask_hist k r H0) (CStr.mask_hist k r H') /\
                     st_valid_after x0 (PSP.of_list (map fst vars)) /\
                     hist_st vars (maskb k r b) (mask_hist k r (H', Hl)) x0 /\
                     Forall (sem_block_ck G2 (mask_hist k r (H', Hl)) (maskb k r b)) (concat x)) as Hbck.
        { intros k. specialize (H11 k).
          eapply mmap_unnest_block_sem in H1 as (H'&Href1&Hvalid1&Histst1&Hsem1); eauto.
          2:apply hist_st_mask...
          destruct Histst1 as (Hdom1&Hsc1).
          assert (Env.Equiv (@EqSt _) H' (CStr.mask_hist k r H')) as Heqmask.
          { unfold st_ids in Hdom1. rewrite <-map_fst_senv_of_tyck, <-map_app in Hdom1.
            eapply slower_mask_hist. eapply sc_vars_slower_hist in Hsc1; eauto. }
          exists H'. repeat (split; auto); intros.
          1-2:rewrite <-Heqmask; auto.
          - edestruct Hsc1 as ((?&Hv&Hck)&_); eauto. rewrite Heqmask in Hv, Hck; eauto.
          - edestruct Hsc1 as (_&(?&Hv&Hck)); eauto. rewrite Heqmask in Hv, Hck; eauto.
          - solve_forall. eapply sem_block_ck_morph; eauto. 2:reflexivity.
            split; auto. reflexivity.
        }
        eapply consolidate_mask_hist
          with (P := fun k H'k => Env.refines (@EqSt _) (CStr.mask_hist k r H0) H'k /\
                               st_valid_after x0 (PSP.of_list (map fst vars)) /\
                               hist_st vars (maskb k r b) (H'k, CStr.mask_hist k r Hl) x0 /\
                               Forall (sem_block_ck G2 (H'k, CStr.mask_hist k r Hl) (maskb k r b)) (concat x))
               in Hbck as (H'&HH').
        2:{ intros ????? Heq (?&?&(?&Hsc1)&?); subst. repeat (split; auto); intros.
            1-2:rewrite <-Heq; auto.
            - edestruct Hsc1 as ((?&Hv&Hck)&_); eauto. rewrite Heq in Hv, Hck; eauto.
            - edestruct Hsc1 as (_&(?&Hv&Hck)); eauto. rewrite Heq in Hv, Hck; eauto.
            - simpl_Forall. eapply sem_block_ck_morph; eauto. 2:reflexivity.
              split; auto. reflexivity.
        }
        2:{ intros ????? (_&_&(Hdom1&_)&_) (_&_&(Hdom2&_)&_) Hdom.
            eapply Env.dom_intro; intros.
            eapply Env.dom_use in Hdom1. eapply Env.dom_use in Hdom2. eapply Env.dom_use in Hdom.
            rewrite Hdom2, <-Hdom1; eauto.
        }
        assert (Env.refines (@EqSt _) H0 H') as Href1.
        { eapply refines_unmask; intros. eapply HH'. }
        eapply unnest_reset_sem with (vars:=vars) (H:=H') in H2 as (H''&Href2&Hvalid2&Histst2&Hsem2&Hsem2')...
        3:(solve_forall; repeat solve_incl).
        3:now rewrite <-length_clockof_numstreams, H6.
        3:(eapply sem_exp_refines; eauto).
        3:eapply (HH' 0).
        3:{ eapply hist_st_unmask; intros. eapply HH'; eauto. }
        2:{ intros * Hun. eapply unnest_exp_sem with (H:=H') (vs:=[sr]) in Hun as (H''&Href'&Hvalid'&Histst'&Hsem'&Hsem''); eauto.
            exists H''. split;[|split;[|split;[|split]]]; eauto.
            inv Hsem'; auto.
            repeat solve_incl.
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
      - exists H0. repeat (esplit; eauto with env).
        constructor; eauto. eapply sem_ref_sem_block; eauto. econstructor; eauto.
      - exists H0. repeat (esplit; eauto with env).
        constructor; eauto. eapply sem_ref_sem_block; eauto. econstructor; eauto.
      - exists H0. repeat (esplit; eauto with env).
        constructor; eauto. eapply sem_ref_sem_block; eauto. econstructor; eauto.
    Qed.

    Corollary unnest_blocks_sem : forall vars b blocks H Hl blocks' st st',
        (forall x, ~IsLast vars x) ->
        Forall (wc_block G1 (vars ++ st_senv st)) blocks ->
        Forall (sem_block_ck G1 (H, Hl) b) blocks ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars b (H, Hl) st ->
        unnest_blocks G1 blocks st = (blocks', st') ->
        (exists H', Env.refines (@EqSt _) H H' /\
               st_valid_after st' (PSP.of_list (map fst vars)) /\
               hist_st vars b (H', Hl) st' /\
               Forall (sem_block_ck G2 (H', Hl) b) blocks').
    Proof with eauto.
      intros * Hnl Hwc Hsem Hvalid Histst Hnorm.
      unfold unnest_blocks in Hnorm. repeat inv_bind.
      eapply mmap_unnest_block_sem in H0; eauto.
      solve_forall.
      eapply unnest_block_sem in H8; eauto.
    Qed.

    (** *** Preservation of sem_node *)

    Lemma local_hist_sc_vars : forall xs ys H H' Hl bs,
        (forall x, InMembers x ys -> ~In x (map fst xs)) ->
        (forall x vs, sem_var H' x vs -> ~InMembers x ys -> sem_var H x vs) ->
        Env.dom H (map fst xs) ->
        Env.dom H' (map fst (Env.elements H) ++ map fst ys) ->
        sc_vars xs (H, Hl) bs ->
        sc_vars ys (H', Hl) bs ->
        sc_vars (xs ++ ys) (H', Hl) bs.
    Proof.
      intros * Hnd Hv Hdom1 Hdom2 Hsc1 Hsc2.
      apply sc_vars_app; auto.
      - intros * Hin1 Hin2.
        eapply Hnd; eauto. now apply fst_InMembers.
      - eapply sc_vars_refines; [|reflexivity|eauto].
        eapply local_hist_dom_refines; eauto.
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
        eapply sem_block_ck_cons in H3; eauto. rename H3 into Hblksem.
        2:{ inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }

        inv HwcG. destruct H4 as (Hwc&_). simpl in *.
        replace {| enums := enums G1; nodes := nodes G1 |} with G1 in Hblksem, Hwc by (destruct G1; auto).
        remember (unnest_node G1 n0) as n'.
        unfold unnest_node in Heqn'; inv Heqn'.
        specialize (n_nodup n0) as Hnd.
        pose proof (n_syn n0) as Hsyn. inv Hsyn.
        rewrite <-H0 in *. inv Hblksem. inv H5.
        simpl in *. repeat rewrite app_nil_r in *.
        destruct Hwc as (_&_&Hwc). rewrite <-H0 in Hwc. inv Hwc.
        assert (forall x, ~IsLast (senv_of_inout (n_in n0 ++ n_out n0) ++ senv_of_locs locs) x) as Hnl.
        { apply NoLast_app; split.
          - apply senv_of_inout_NoLast.
          - intros * Hil. inv Hil. simpl_In. simpl_Forall. subst; simpl in *; congruence.
        }
        inv H10. inv H11.
        assert (Forall (sem_block_ck G1 (Hi', Env.empty _) (clocks_of ins)) blks) as Hsem.
        { simpl_Forall.
          eapply sem_block_change_lasts;
            eauto using nolocal_noswitch, noswitch_noauto, noauto_nolast with lclocking.
        }

        eapply unnest_blocks_sem with (vars:=senv_of_inout (n_in n0 ++ n_out n0) ++ senv_of_locs locs)
          in Hsem as (Hf&Href&_&(Hdom&Hsc)&Hsem); eauto. 5:eapply surjective_pairing.
        eapply Snode with (H:=H); simpl; eauto.
        + erewrite find_node_now; eauto.
        + assumption.
        + assumption.
        + apply sem_block_ck_cons'; simpl...
          2:{ eapply find_node_not_Is_node_in in Hord2.
            2:erewrite find_node_now; eauto. eauto. }
          rewrite <-H0.
          do 2 econstructor. 6:destruct G2; eauto.
          * intros ?? Hv Hnin1.
            assert (In x (map fst (n_in n0 ++ n_out n0))) as Hinx0.
            { assert (Env.In x Hf) as Hin by (inv Hv; econstructor; eauto).
              eapply Env.dom_use in Hin; [|eauto].
              rewrite map_app, map_fst_senv_of_inout, map_fst_senv_of_locs in Hin.
              repeat rewrite in_app_iff in Hin. destruct Hin as [[Hin|Hin]|Hin]; auto; exfalso.
              - apply Hnin1. now apply InMembers_app, or_introl, fst_InMembers.
              - apply Hnin1. apply InMembers_app, or_intror, fst_InMembers.
                solve_In.
            }
            eapply H14; eauto.
            -- rewrite map_fst_senv_of_inout in H7.
              eapply sem_var_refines_iff. 1,4:eauto. eapply Env.dom_dom_lb; eauto.
               erewrite <-Env.dom_use in Hinx0; [|eauto].
               eapply Env.In_Members, fst_InMembers in Hinx0.
               apply in_app_iff; eauto.
            -- contradict Hnin1. apply InMembers_app; auto.
          * eapply local_hist_dom; eauto; simpl.
            rewrite map_fst_senv_of_inout.
            clear - Hdom. simpl_app.
            repeat rewrite map_map in *. simpl in *.
            erewrite map_ext with (l:=n_in _), map_ext with (l:=n_out _), map_ext with (l:=locs); eauto.
            1-3:intros; destruct_conjs; auto.
          * reflexivity.
          * intros. apply in_app_iff in H5 as [|]. simpl_Forall; congruence. simpl_In.
          * eapply sc_vars_incl; [|eauto]. solve_incl_app.
            erewrite map_map, map_ext; try reflexivity. intros; destruct_conjs; auto.
        + simpl.
          constructor; simpl; auto.
        + unfold st_senv. rewrite init_st_anns, app_nil_r. auto.
        + simpl.
          rewrite map_app, map_fst_senv_of_inout,
            map_fst_senv_of_locs, <-map_fst_idty with (xs:=locs), <-map_app, <-app_assoc.
          eapply unnest_node_init_st_valid; eauto.
        + constructor.
          * rewrite map_app, map_fst_senv_of_locs.
            erewrite local_hist_dom in H15; eauto. simpl in H15.
            unfold st_ids. rewrite init_st_anns, app_nil_r. auto.
          * unfold st_senv. rewrite init_st_anns, app_nil_r.
            eapply local_hist_sc_vars with (H:=H); eauto.
            1-4:repeat rewrite map_fst_senv_of_inout in *; repeat rewrite map_fst_senv_of_locs in *; auto.
            1,2:repeat setoid_rewrite InMembers_senv_of_locs; auto.
            1:{ destruct Hnd as (_&Hnd). inv Hnd. inv H10. auto. }
            eapply sc_vars_change_lasts; eauto.
            eapply NoLast_app; eauto.
      - erewrite find_node_other in Hfind; eauto.
        eapply sem_node_ck_cons'...
        destruct G2; apply HGref.
        econstructor...
        destruct G1; eapply sem_block_ck_cons...
        eapply find_node_later_not_Is_node_in in Hord1...
    Qed.

  End unnest_node_sem.

  Local Hint Resolve wc_global_Ordered_nodes : norm.

  Lemma unnest_global_refines : forall G,
      wc_global G ->
      global_sem_refines G (unnest_global G).
  Proof with eauto with norm.
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
        * apply iface_eq_iface_incl, unnest_nodes_eq.
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
    Variable G1 : @global nolocal_top_block norm1_prefs.
    Variable G2 : @global nolocal_top_block norm2_prefs.

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
        case (const_val bs false_val) [(1, ys); (0, xs)] None xs.
    Proof.
      cofix CoFix.
      intros [b bs] xs ys Hsync1 Hsync2.
      rewrite const_val_Cons. unfold false_val.
      inv Hsync1; inv Hsync2; econstructor; simpl; eauto.
      + repeat constructor; simpl; congruence.
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

    Global Instance init_stream_Proper:
      Proper (@EqSt bool ==> @EqSt svalue) init_stream.
    Proof.
      intros bs bs' Heq1.
      unfold init_stream. rewrite Heq1. reflexivity.
    Qed.

    Lemma fby_case : forall bs v y0s ys zs,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        fby y0s ys zs ->
        case (sfby true_val (const_val bs false_val)) [(1, y0s);(0, sfby v ys)] None zs.
    Proof with eauto.
      cofix CoFix.
    intros [b bs] v y0s ys zs Hsync Hfby1.
    apply fby_aligned in Hsync as [Hsync1 [Hsync2 Hsync3]]; [|auto].
    destruct b; inv Hsync1; inv Hsync2; inv Hsync3.
    - repeat rewrite const_val_Cons.
      inv Hfby1.
      repeat rewrite sfby_Cons. econstructor; simpl.
      + rewrite sfby_const.
        assert (vs1 ≡ sfby v1 vs0) as Heq by (eapply sfby_fby1'; eauto).
        rewrite Heq.
        apply case_false... rewrite <-Heq; auto.
      + repeat constructor; simpl; auto; congruence.
      + constructor.
      + repeat constructor.
    - rewrite const_val_Cons. repeat rewrite sfby_Cons.
      inv Hfby1.
      constructor; auto.
      eapply CoFix; eauto. simpl; auto.
    Qed.

    Corollary fby_init_stream_case : forall bs v y0s ys zs,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        fby y0s ys zs ->
        case (init_stream bs) [(1, y0s); (0, sfby v ys)] None zs.
      intros * Hsync Hfby1.
      eapply fby_case in Hfby1; eauto.
      unfold init_stream.
      rewrite const_val_enum; eauto.
    Qed.

    Lemma arrow_case : forall bs y0s ys zs,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        arrow y0s ys zs ->
        case (sfby true_val (const_val bs false_val)) [(1,y0s);(0,ys)] None zs.
    Proof with eauto.
      cofix CoFix.
      intros [b bs] y0s ys zs Hsync Harrow.
      apply arrow_aligned in Hsync as [Hsync1 [Hsync2 Hsync3]]; [|auto].
      destruct b; inv Hsync1; inv Hsync2; inv Hsync3; inv Harrow.
      - rewrite const_val_Cons, sfby_Cons.
        econstructor; simpl; auto.
        + rewrite sfby_const.
          clear - H0 H1 H2 H3. revert bs vs vs0 vs1 H1 H2 H3 H0.
          cofix CoFix. intros * Hsync1 Hsync2 Hsync3 Harrow.
          destruct bs as [[|] bs]; inv Hsync1; inv Hsync2; inv Hsync3; inv Harrow.
          1,2:rewrite const_val_Cons; econstructor; simpl; eauto.
          repeat constructor; auto; simpl; congruence.
        + repeat constructor; auto; simpl; congruence.
      - rewrite const_val_Cons, sfby_Cons.
        constructor; simpl; eauto.
    Qed.

    Corollary arrow_init_stream_case : forall bs y0s ys zs,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        arrow y0s ys zs ->
        case (init_stream bs) [(1,y0s);(0,ys)] None zs.
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

    Fact fresh_ident_refines' {B} : forall hint vars H a id (v : Stream svalue) (st st' : fresh_st B),
        st_valid_after st (PSP.of_list vars) ->
        Env.dom H (vars++st_ids st) ->
        fresh_ident norm2 hint a st = (id, st') ->
        Env.refines (@EqSt _) H (Env.add id v H).
    Proof with eauto with norm.
      intros * Hvalid Hdom Hfresh.
      assert (st_valid_after st' (PSP.of_list vars)) as Hvalid' by eauto with fresh norm.
      eapply Env.refines_add; eauto using EqStrel_Reflexive.
      intro contra. erewrite Env.dom_use in contra; [| eauto].
      apply in_app_or in contra. destruct contra.
      + eapply Facts.fresh_ident_In in Hfresh.
        assert (In id (st_ids st')).
        { unfold st_ids, idty. simpl_In; simpl in *.
          exists (id, a); auto. }
        apply st_valid_NoDup in Hvalid'.
        eapply NoDup_app_In in Hvalid'; [|eauto].
        apply Hvalid'; clear Hvalid'.
        rewrite ps_of_list_ps_to_list...
      + eapply Facts.fresh_ident_nIn in Hfresh...
    Qed.

    Fact init_var_for_clock_sem : forall vars bs H Hl ck bs' x eqs' st st',
        (forall x, ~IsLast vars x) ->
        sem_clock H bs ck bs' ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars bs (H, Hl) st ->
        init_var_for_clock ck st = (x, eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars bs (H', Hl) st' /\
            sem_var H' x (init_stream bs') /\
            Forall (sem_equation_ck G2 (H', Hl) bs) eqs').
    Proof with eauto.
      intros * Hnl Hsemc Hvalid Histst Hinit.
      unfold init_var_for_clock in Hinit.
      destruct (fresh_ident _ _) eqn:Hident. repeat inv_bind.
      assert (st_valid_after st' (PSP.of_list (map fst vars))) as Hvalid1 by eauto with fresh norm.
      remember (Env.add x (init_stream bs' (* rs' *)) H) as H'.
      assert (Env.refines (@EqSt _) H H') as Href1.
      { subst. eapply fresh_ident_refines' in Hident; eauto.
        now destruct Histst. }
      assert (hist_st vars bs (H', Hl) st') as Histst1.
      { subst. eapply fresh_ident_hist_st in Hident...
        destruct Histst as (Hdom&Hsc).
        now rewrite init_stream_ac. }
      assert (st_valid_after st' (PSP.of_list (map fst vars))) as Hvalid2 by eauto with fresh.
      exists H'. repeat (split; eauto).
      + rewrite HeqH'. econstructor. 2:reflexivity.
        apply Env.add_1. reflexivity.
      + repeat constructor.
        apply Seq with (ss:=[[(init_stream bs' (* rs' *))]]); simpl; repeat constructor.
        * econstructor; repeat constructor.
          1,2:apply add_whens_enum_sem; eauto using sem_clock_refines.
          repeat constructor. unfold init_stream.
          repeat rewrite const_val_const; subst.
          do 2 rewrite const_val_enum. apply sfby_fby; simpl; eauto.
          rewrite <- const_val_enum. apply enum_aligned.
        * econstructor. 2:reflexivity.
          rewrite HeqH'. apply Env.add_1. reflexivity.
    Qed.

    Hypothesis Hiface : global_iface_incl G1 G2.
    Hypothesis HGref : global_sem_refines G1 G2.

    Hypothesis HwcG1 : wc_global G1.

    Hint Constructors Forall3 : datatypes.

    Fact fby_iteexp_sem : forall vars bs H Hl e0 e ty nck y0 y z e' eqs' st st' ,
        (forall x, ~IsLast vars x) ->
        normalized_lexp e0 ->
        clockof e0 = [nck] ->
        wc_exp G1 (vars++st_senv st) e0 ->
        wc_exp G1 (vars++st_senv st) e ->
        sem_exp_ck G1 (H, Hl) bs e0 [y0] ->
        sem_exp_ck G1 (H, Hl) bs e [y] ->
        fby y0 y z ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars bs (H, Hl) st ->
        fby_iteexp e0 e (ty, nck) st = (e', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars bs (H', Hl) st' /\
            sem_exp_ck G2 (H', Hl) bs e' [z] /\
            Forall (sem_equation_ck G2 (H', Hl) bs) eqs').
    Proof with eauto.
      intros * Hnl Hnormed Hck Hwc0 Hwc Hsem0 Hsem Hfby Hvalid Histst Hiteexp.
      assert (st_follows st st') as Hfollows by (eapply fby_iteexp_st_follows; eauto).
      unfold fby_iteexp in Hiteexp; repeat inv_bind.
      assert (Hsck:=Hsem0). eapply sc_exp with (Γ:=vars++st_senv st) in Hsck... simpl in Hsck.
      2:(destruct Histst; auto).
      rewrite Hck in Hsck. eapply Forall2_singl in Hsck.

      eapply init_var_for_clock_sem in H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]...
      remember (abstract_clock y0) as bs'.
      remember (match ty with Tprimitive cty => Vscalar (Op.sem_cconst (Op.init_ctype cty))
                         | Tenum (_, n) => Venum 0 end) as v0.
      remember (sfby v0 y) as y'.
      remember (Env.add x2 y' H') as H''.
      assert (Env.refines (@EqSt _) H' H'') by (subst; destruct Histst1; eapply fresh_ident_refines' in H1; eauto).
      assert (hist_st vars bs (H'', Hl) st') as Histst2.
      { subst. eapply fresh_ident_hist_st...
        rewrite ac_sfby.
        rewrite ac_fby2, <- ac_fby1; eauto. eapply sem_clock_refines... }
      exists H''. repeat (split; eauto with fresh norm); try constructor.
      - etransitivity; eauto.
      - eapply ScaseTotal with (s:=(init_stream bs')) (vs:=[[(1, y0);(0, y')]]).
        + econstructor. eapply sem_var_refines...
        + econstructor. 2:econstructor. 3:econstructor.
          1,2:constructor; eauto.
          4,5:simpl; rewrite app_nil_r; econstructor; eauto with datatypes.
          * eapply sem_exp_refines; [|eauto using sem_ref_sem_exp].
            etransitivity; eauto.
          * subst. do 2 econstructor; eauto. eapply Env.add_1. 1,2:reflexivity.
          * simpl. constructor; auto.
        + constructor; auto with datatypes. subst.
          eapply fby_init_stream_case; eauto using ac_aligned.
      - apply Seq with (ss:=[[y']]); repeat constructor.
        + eapply Sfby with (s0ss:=[[const_val bs' v0]]) (sss:=[[y]]); repeat constructor.
          * destruct ty as [|(?&?)]; simpl; rewrite Heqv0; subst.
            -- eapply sem_exp_ck_morph; eauto. 1,2:reflexivity.
               econstructor; eauto. eapply const_val_const.
               eapply add_whens_const_sem.
               eapply sem_clock_refines; [|eauto]. etransitivity...
            -- eapply sem_exp_ck_morph; eauto. 1,2:reflexivity.
               econstructor; eauto. eapply const_val_enum.
               eapply add_whens_enum_sem.
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

    Fact arrow_iteexp_sem : forall vars bs H Hl e0 e ty nck y0 y z e' eqs' st st',
        (forall x, ~IsLast vars x) ->
        normalized_lexp e0 ->
        clockof e0 = [nck] ->
        wc_exp G1 (vars++st_senv st) e0 ->
        wc_exp G1 (vars++st_senv st) e ->
        sem_exp_ck G1 (H, Hl) bs e0 [y0] ->
        sem_exp_ck G1 (H, Hl) bs e [y] ->
        arrow y0 y z ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars bs (H, Hl) st ->
        arrow_iteexp e0 e (ty, nck) st = (e', eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars bs (H', Hl) st' /\
            sem_exp_ck G2 (H', Hl) bs e' [z] /\
            Forall (sem_equation_ck G2 (H', Hl) bs) eqs').
    Proof with eauto.
      intros * Hnl Hnormed Hck Hwc0 Hwc1 Hsem0 Hsem Harrow Hvalid Histst Hiteexp.
      assert (st_follows st st') as Hfollows by (eapply arrow_iteexp_st_follows; eauto).
      unfold arrow_iteexp in Hiteexp. repeat inv_bind.
      assert (Hsck:=Hsem0). eapply sc_exp with (Γ:=vars++st_senv st) in Hsck... simpl in Hsck.
      2:(destruct Histst; auto).
      rewrite Hck in Hsck. eapply Forall2_singl in Hsck.

      eapply init_var_for_clock_sem in H0 as [H' [Href1 [Hvalid1 [Histst1 [Hsem1 Hsem1']]]]]...
      remember (abstract_clock y0) as bs'.
      exists H'. repeat (split; auto).
       eapply ScaseTotal with (s:=(init_stream bs')) (vs:=[[(1, y0);(0, y)]]).
      - econstructor; eauto.
      - econstructor. 2:econstructor. 3:econstructor.
        1,2:constructor; eauto; eapply sem_exp_refines; [|eauto using sem_ref_sem_exp]; eauto.
        2,3:simpl; constructor; eauto with datatypes. auto.
      - simpl. repeat econstructor.
        eapply arrow_init_stream_case; eauto.
        subst. left. eapply ac_aligned.
    Qed.

    Fact normfby_equation_sem : forall vars bs H Hl to_cut equ eqs' st st' ,
        (forall x, ~IsLast vars x) ->
        unnested_equation G1 equ ->
        wc_equation G1 (vars++st_senv st) equ ->
        sem_equation_ck G1 (H, Hl) bs equ ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars bs (H, Hl) st ->
        normfby_equation to_cut equ st = (eqs', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars bs (H', Hl) st' /\
            Forall (sem_equation_ck G2 (H', Hl) bs) eqs').
    Proof with eauto.
      intros * Hnl Hun Hwc Hsem Hvalid Histst Hfby.
      inv_normfby_equation Hfby to_cut equ; try destruct x2 as (ty&ck).
      - (* constant fby *)
        destruct PS.mem; repeat inv_bind.
        + inv Hsem. inv H6; inv H5.
          simpl in H7; rewrite app_nil_r in H7. inv H7; inv H6.
          assert (Hsem':=H3). inversion_clear H3 as [| | | | | |???????? Hsem0 Hsem1 Hsem| | | | | |].
          inv Hsem0; inv H6. inv Hsem1; inv H7.
          simpl in Hsem; repeat rewrite app_nil_r in Hsem. inv Hsem; inv H9.
          inv Hwc. rename H6 into Hwc. apply Forall_singl in Hwc. assert (Hwc':=Hwc). inv Hwc'.
          apply Forall_singl in H9. rewrite Forall2_eq in H11; simpl in H11; rewrite app_nil_r in H11.

          remember (Env.add x2 y0 H) as H'.
          assert (Env.refines (@EqSt _) H H') as Href.
          { subst. destruct Histst as [Hdom _].
            eapply fresh_ident_refines' in H0... }
          assert (hist_st vars bs (H', Hl) st') as Histst1.
          { subst. eapply fresh_ident_hist_st in H0...
            inv Hun. 2:inv H2; inv H1.
            eapply sc_exp in H3... 2:destruct Histst; auto.
            simpl in H3; rewrite <-H11 in H3. apply Forall2_singl in H3.
            apply ac_fby1 in H8. now rewrite <-H8.
          }
          exists H'. repeat (split; eauto with norm fresh).
          repeat constructor; auto.
          * eapply Seq with (ss:=[[y0]]); simpl; repeat constructor.
            2:eapply sem_var_refines; eauto.
            rewrite HeqH'. econstructor. eapply Env.add_1. 1,2:reflexivity.
          * eapply Seq with (ss:=[[y0]]); simpl; repeat constructor.
            -- eapply sem_ref_sem_exp... eapply sem_exp_refines...
            -- rewrite HeqH'. econstructor. eapply Env.add_1. 1,2:reflexivity.
        + exists H. repeat (split; eauto with env).
          constructor; auto.
          eapply sem_ref_sem_equation; eauto.
      - (* fby *)
        inv Hwc. rename H3 into Hwc. clear H4.
        apply Forall_singl in Hwc. inv Hwc.
        apply Forall_singl in H4. rewrite Forall2_eq in H6; simpl in H6; rewrite app_nil_r in H6.
        inv Hsem. inv H10; inv H9. simpl in H11; rewrite app_nil_r in H11. inv H11; inv H10.
        inversion_clear H3 as [| | | | | |???????? Hsem0 Hsem1 Hsem| | | | | |].
        inv Hsem0; inv H10. inv Hsem1; inv H11.
        simpl in Hsem; repeat rewrite app_nil_r in Hsem. inv Hsem; inv H13.
        eapply fby_iteexp_sem with (nck:=ck) in H0 as [H' [Href1 [Hvalid1 [Hhistst1 [Hsem' Hsem'']]]]]...
        2:{ inv Hun; auto. inv H2; inv H1. }
        2:{ inv H5; auto. }
        exists H'. repeat (split; eauto).
        constructor; auto.
        eapply Seq with (ss:=[[y0]]); simpl; repeat constructor; auto.
        eapply sem_var_refines; eauto.
      - (* arrow *)
        inv Hwc. rename H3 into Hwc. clear H4. apply Forall_singl in Hwc. inv Hwc.
        apply Forall_singl in H4. rewrite Forall2_eq in H6; simpl in H6; rewrite app_nil_r in H6.
        inv Hsem. inv H10; inv H9. simpl in *; rewrite app_nil_r in *. inv H11; inv H10.
        inversion_clear H3 as [| | | | | | |???????? Hsem0 Hsem1 Hsem| | | | |].
        inv Hsem0; inv H10. inv Hsem1; inv H11.
        simpl in Hsem; repeat rewrite app_nil_r in Hsem. inv Hsem; inv H13.
        eapply arrow_iteexp_sem with (nck:=ck) in H0 as [H' [Href1 [Hvalid1 [Hhistst1 [Hsem' Hsem'']]]]]...
        2:{ inv Hun; auto. inv H2; inv H1. }
        2:{ inv H5; auto. }
        exists H'. repeat (split; eauto).
        constructor; auto.
        eapply Seq with (ss:=[[y0]]); simpl; repeat constructor; auto.
        eapply sem_var_refines; eauto.
      - (* other *)
        exists H. repeat (split; eauto with env).
        constructor; auto.
        eapply sem_ref_sem_equation; eauto.
    Qed.

    Lemma normfby_block_sem : forall vars to_cut d blocks' bs H Hl st st' ,
        (forall x, ~IsLast vars x) ->
        unnested_block G1 d ->
        wc_block G1 (vars++st_senv st) d ->
        sem_block_ck G1 (H, Hl) bs d ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars bs (H, Hl) st ->
        normfby_block to_cut d st = (blocks', st') ->
        (exists H',
            Env.refines (@EqSt _) H H' /\
            st_valid_after st' (PSP.of_list (map fst vars)) /\
            hist_st vars bs (H', Hl) st' /\
            Forall (sem_block_ck G2 (H', Hl) bs) blocks').
    Proof.
      induction d using block_ind2; intros * Hnl Hun Hwc Hsem Hvalid Hist Hnorm;
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
                     Env.refines (@EqSt _) (CStr.mask_hist k r H0) (CStr.mask_hist k r H'k) /\
                     st_valid_after st' (PSP.of_list (map fst vars)) /\
                     hist_st vars (maskb k r bs) (mask_hist k r (H'k, Hl)) st' /\
                     Forall (sem_block_ck G2 (mask_hist k r (H'k, Hl)) (maskb k r bs)) x0) as Hblocks'.
        { intros k. specialize (H12 k).
          apply Forall_singl in H12. eapply H in H12 as (H'k&?&?&(?&?)&?); eauto.
          2:eapply hist_st_mask; eauto.
          assert (slower_hist H'k (maskb k r bs)) as Hslow.
          { eapply sc_vars_slower_hist in H10; eauto.
            unfold st_senv. rewrite map_app, map_fst_senv_of_tyck; auto. }
          eapply slower_mask_hist in Hslow.
          exists H'k. repeat (split; auto); intros. 1-2:rewrite <-Hslow; auto.
          - edestruct H10 as ((?&Hv&Hck)&_); eauto. rewrite Hslow in Hv, Hck; eauto.
          - edestruct H10 as (_&(?&Hv&Hck)); eauto. rewrite Hslow in Hv, Hck; eauto.
          - solve_forall. eapply sem_block_ck_morph; eauto. 2:reflexivity.
            split; auto. reflexivity.
        }
        eapply consolidate_mask_hist
          with (P := fun k H'k => Env.refines (@EqSt _) (CStr.mask_hist k r H0) H'k /\
                               st_valid_after st' (PSP.of_list (map fst vars)) /\
                               hist_st vars (maskb k r bs) (H'k, CStr.mask_hist k r Hl) st' /\
                               Forall (sem_block_ck G2 (H'k, CStr.mask_hist k r Hl) (maskb k r bs)) x0)
          in Hblocks' as (H'&HH').
        2:{ intros ????? Heq (?&?&(?&Hsc)&?); subst. repeat (split; auto); intros.
            1-2:rewrite <-Heq; auto.
            - edestruct Hsc as ((?&Hv&Hck)&_); eauto. rewrite Heq in Hv, Hck; eauto.
            - edestruct Hsc as (_&(?&Hv&Hck)); eauto. rewrite Heq in Hv, Hck; eauto.
            - simpl_Forall. eapply sem_block_ck_morph; eauto. 2:reflexivity.
              split; auto. reflexivity.
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
        split; [|split; [|split; [split|]]]; auto.
        repeat (split; auto).
        + specialize (HH' 0) as (_&?&_&_); auto.
        + specialize (HH' 0) as (_&_&(Hdom&_)&_); auto.
          setoid_rewrite Env.dom_map in Hdom; auto.
        + eapply sc_vars_unmask.
          intros k. specialize (HH' k) as (_&_&(_&?)&_); eauto.
        + rewrite Forall_map. eapply Forall_forall; intros.
          econstructor; eauto.
          * eapply sem_ref_sem_exp; eauto. eapply sem_exp_refines; eauto.
          * intros ?. specialize (HH' k) as (_&_&_&?).
            constructor; auto. eapply Forall_forall in H5; eauto.
    Qed.

    Fact normfby_blocks_sem : forall vars bs to_cut blocks blocks' H Hl st st' ,
        (forall x, ~IsLast vars x) ->
        Forall (unnested_block G1) blocks ->
        Forall (wc_block G1 (vars++st_senv st)) blocks ->
        Forall (sem_block_ck G1 (H, Hl) bs) blocks ->
        st_valid_after st (PSP.of_list (map fst vars)) ->
        hist_st vars bs (H, Hl) st ->
        normfby_blocks to_cut blocks st = (blocks', st') ->
        (exists H',
           Env.refines (@EqSt _) H H' /\
           hist_st vars bs (H', Hl) st' /\
           Forall (sem_block_ck G2 (H', Hl) bs) blocks').
    Proof with eauto.
      induction blocks; intros * Hnl Hunt Hwc Hsem Hvalid Hhistst Hfby;
        unfold normfby_blocks in Hfby; simpl in *; repeat inv_bind.
      - exists H; simpl; auto with env.
      - assert (normfby_blocks to_cut blocks x1 = (concat x2, st')) as Hnorm.
        { unfold normfby_blocks; repeat inv_bind.
          repeat eexists; eauto. repeat inv_bind; auto. }
        inv Hunt. inv Hwc. inv Hsem.
        assert (st_follows st x1) as Hfollows by (eapply normfby_block_st_follows in H0; eauto).
        eapply normfby_block_sem in H0 as [H' [Href1 [Hvalid1 [Hhistst1 Hsem1]]]]. 2-7:eauto.
        assert (Forall (sem_block_ck G1 (H', Hl) bs) blocks) as Hsem'.
        { solve_forall. eapply sem_block_refines... } clear H9.
        eapply IHblocks in Hnorm as (H''&Href&Hdom&Hsem2). 2-7:eauto.
        2:solve_forall; repeat solve_incl.
        + exists H''. split;[|split]...
          * etransitivity...
          * simpl. apply Forall_app; split; eauto.
            solve_forall. eapply sem_block_refines...
    Qed.

    Fact init_st_hist_st : forall b H xs,
        Env.dom (fst H) (List.map fst xs) ->
        sc_vars xs H b ->
        hist_st xs b H init_st.
    Proof.
      intros b H n Hdom Hinv.
      repeat constructor.
      - unfold st_ids.
        rewrite init_st_anns; simpl.
        rewrite app_nil_r. assumption.
      - destruct Hinv. unfold st_senv. rewrite init_st_anns; simpl.
        rewrite app_nil_r. assumption.
      - destruct Hinv. unfold st_senv. rewrite init_st_anns; simpl.
        rewrite app_nil_r. assumption.
    Qed.

  End normfby_node_sem.

  Lemma normfby_node_sem : forall G1 G2 f n ins outs,
      global_iface_incl G1 G2 ->
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
      eapply sem_block_ck_cons in H3; eauto.
      2:{ inv Hord1. intro contra. apply H9 in contra as [? _]; auto. }
      rename H3 into Hblksem.

      remember (normfby_node n0) as n'.
      unfold normfby_node in Heqn'; inv Heqn'.
      specialize (n_nodup n0) as Hnd.
      inversion_clear Hunt as [|?? [[??? Hblk ?] _] Hunt'].
      rewrite Hblk in *. inv Hblksem. inv H5.
      simpl in *. repeat rewrite app_nil_r in *. rewrite map_fst_senv_of_inout in H8.
      destruct H0 as (_&_&Hwc). rewrite Hblk in Hwc. inv Hwc.
      assert (forall x, ~IsLast (senv_of_inout (n_in n0 ++ n_out n0) ++ senv_of_locs locs) x) as Hnl.
      { apply NoLast_app; split.
        - apply senv_of_inout_NoLast.
        - intros * Hil. inv Hil. simpl_In. simpl_Forall. subst; simpl in *; congruence.
      }
      inv H10. inv H11.
      assert (Forall (sem_block_ck G1 (Hi', Env.empty _) (clocks_of ins)) blks) as Hsem.
      { simpl_Forall. eapply sem_block_change_lasts; eauto with lclocking.
        - pose proof (n_syn n0) as Hsyn. inv Hsyn. rewrite Hblk in H11; inv H11.
          simpl_Forall; eauto using nolocal_noswitch, noswitch_noauto, noauto_nolast.
        - destruct G1; eauto.
      }

      eapply normfby_blocks_sem with (vars:=senv_of_inout (n_in n0 ++ n_out n0) ++ senv_of_locs locs)
        in Hsem as (Hf&Hre'&(Hdom&Hsc)&Heqs'')... 6:eapply surjective_pairing.
      eapply Snode with (H:=H); simpl...
      + erewrite find_node_now...
      + assumption.
      + assumption.
      + apply sem_block_ck_cons'; simpl...
          2:{ eapply find_node_not_Is_node_in in Hord2.
            2:erewrite find_node_now; eauto. eauto. }
          rewrite Hblk.
          do 2 econstructor. 6:destruct G2; eauto.
          * intros ?? Hv Hnin1.
            assert (In x1 (map fst (n_in n0 ++ n_out n0))) as Hinx0.
            { assert (Env.In x1 Hf) as Hin by (inv Hv; econstructor; eauto).
              eapply Env.dom_use in Hin; [|eauto].
              rewrite map_app, map_fst_senv_of_inout, map_fst_senv_of_locs in Hin.
              repeat rewrite in_app_iff in Hin. destruct Hin as [[Hin|Hin]|Hin]; auto; exfalso.
              - apply Hnin1. now apply InMembers_app, or_introl, fst_InMembers.
              - apply Hnin1. apply InMembers_app, or_intror, fst_InMembers.
                solve_In.
            }
            eapply H14; eauto.
            -- eapply sem_var_refines_iff. 1,4:eauto. eapply Env.dom_dom_lb; eauto.
               erewrite <-Env.dom_use in Hinx0; [|eauto].
               eapply Env.In_Members, fst_InMembers in Hinx0.
               apply in_app_iff; auto.
            -- contradict Hnin1. apply InMembers_app; auto.
          * eapply local_hist_dom; eauto; simpl.
            clear - Hdom. simpl_app.
            repeat rewrite map_map in *. simpl in *.
            erewrite map_ext with (l:=n_in _), map_ext with (l:=n_out _), map_ext with (l:=locs) in Hdom; eauto.
            1-3:intros; destruct_conjs; auto.
          * reflexivity.
          * intros. apply in_app_iff in H0 as [|]. simpl_Forall; congruence. simpl_In.
          * eapply sc_vars_incl; [|eauto]. solve_incl_app.
            erewrite map_map, map_ext; try reflexivity. intros; destruct_conjs; auto.
      + simpl. constructor; simpl; auto.
        now rewrite map_fst_senv_of_inout.
      + destruct G1, G2; auto.
      + destruct G1. unfold st_senv. rewrite init_st_anns, app_nil_r. auto.
      + rewrite map_app, map_fst_senv_of_inout,
            map_fst_senv_of_locs, <-map_fst_idty with (xs:=locs), <-map_app, <-app_assoc.
        eapply normfby_node_init_st_valid; eauto.
      + eapply init_st_hist_st; eauto.
        * rewrite map_app, map_fst_senv_of_inout, map_fst_senv_of_locs.
          eapply local_hist_dom; eauto.
        * eapply local_hist_sc_vars with (H:=H); eauto.
          1-4:repeat rewrite map_fst_senv_of_inout in *; repeat rewrite map_fst_senv_of_locs in *; auto.
          1,2:repeat setoid_rewrite InMembers_senv_of_locs; auto.
          1:{ destruct Hnd as (_&Hnd). inv Hnd. inv H10. auto. }
          eapply sc_vars_change_lasts; eauto.
          eapply NoLast_app; eauto.
    - erewrite find_node_other in Hfind; eauto.
      eapply sem_node_ck_cons'...
      destruct G2; apply Href.
      econstructor...
      destruct G1; eapply sem_block_ck_cons...
      eapply find_node_later_not_Is_node_in in Hord1...
  Qed.

  Lemma normfby_global_refines : forall G,
      unnested_global G ->
      wc_global G ->
      global_sem_refines G (normfby_global G).
  Proof with eauto with norm.
    intros (enms&nds).
    induction nds; intros * Hunt Hwc; simpl.
    - apply global_sem_ref_nil.
    - apply global_sem_ref_cons with (f:=n_name a)...
      + eapply normfby_global_wc, wc_global_Ordered_nodes in Hwc;
          unfold normfby_global in Hwc; simpl in Hwc...
      + inv Hunt; inv Hwc. eapply IHnds...
      + intros ins outs Hsem; simpl.
        eapply normfby_node_sem with (G1:=(Global enms nds)) (G2:=(Global _ _)) in Hsem...
        * apply iface_eq_iface_incl, normfby_global_eq.
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
  Proof with eauto with lclocking.
    intros * Hwc Hsem.
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
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (LCA : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Ty : LTYPING Ids Op OpAux Cks Senv Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Lord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
       (LClockSem : LCLOCKSEMANTICS Ids Op OpAux Cks Senv Syn Ty Clo LCA Lord CStr Sem)
       (Norm : NORMALIZATION Ids Op OpAux Cks Senv Syn)
       <: CORRECTNESS Ids Op OpAux Cks CStr Senv Syn LCA Ty Clo Lord Sem LClockSem Norm.
  Include CORRECTNESS Ids Op OpAux Cks CStr Senv Syn LCA Ty Clo Lord Sem LClockSem Norm.
End CorrectnessFun.
