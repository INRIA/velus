From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common.
From Velus Require Import Operators FunctionalEnvironment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LSemantics Lustre.LClockedSemantics.
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
       (Import Ty : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import Cl : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import Ord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (Import LCS : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Cl Ord CStr Sem)
       (Import Norm : NORMALIZATION Ids Op OpAux Cks Senv Syn).

  Module Import SCT := SCCorrectnessFun Ids Op OpAux Cks CStr Senv Syn Cl Ord Sem LCS SC. Import SC.

  Import Fresh Tactics Unnesting.
  Module Import Typing := NTypingFun Ids Op OpAux Cks Senv Syn Ty Norm.
  Module Import Clocking := NClockingFun Ids Op OpAux Cks Senv Syn Cl Norm.
  Import List.

  CoFixpoint default_stream : Stream svalue :=
    absent ⋅ default_stream.

  Import Permutation.

  (** *** Relation between state and history *)

  Definition hist_st {pref} vars b H (st: fresh_st pref _) :=
    dom H (vars++st_senv st) /\
    LCS.sc_vars (vars++st_senv st) H b.

  Lemma fresh_ident_refines : forall pref prefs vars hint H a id (v: Stream svalue) (st st' : fresh_st pref _),
      ~PS.In pref prefs ->
      Forall (AtomOrGensym prefs) (map fst vars) ->
      dom H (vars++st_senv st) ->
      fresh_ident hint a st = (id, st') ->
      FEnv.refines (@EqSt _) H (FEnv.add (Var id) v H).
  Proof with eauto.
    intros * Hnpref Hat Hdom Hfresh.
    eapply FEnv.add_refines; auto using EqStrel_Reflexive.
    intro contra. apply Hdom, IsVar_app in contra as [contra|contra].
    + eapply Facts.fresh_ident_In in Hfresh.
      inv contra. simpl_In. simpl_Forall.
      assert (In id (st_ids st')).
      { unfold st_ids, idty. solve_In. }
      eapply Facts.st_valid_AtomOrGensym_nIn; eauto.
    + inv contra. simpl_In.
      eapply Facts.fresh_ident_nIn in Hfresh; eauto. eapply Hfresh. solve_In.
  Qed.

  Fact fresh_ident_dom : forall pref hint vars H a id v (st st' : fresh_st pref _),
      dom H (vars++st_senv st) ->
      fresh_ident hint a st = (id, st') ->
      dom (FEnv.add (Var id) v H) (vars++st_senv st').
  Proof.
    intros * (D1&D2) Hfresh. unfold st_senv in *.
    destruct_conjs.
    apply Ker.fresh_ident_anns in Hfresh. rewrite Hfresh; simpl.
    split; intros ?; rewrite FEnv.add_In; [rewrite D1|rewrite D2];
      rewrite <-Permutation_middle;
      (split; [intros [Eq|]; try inv Eq; eauto with senv datatypes
              |intros Var; inv Var; simpl in *]).
    - take (_ \/ _) and destruct it; subst; eauto with senv.
    - take (_ \/ _) and destruct it; inv_equalities; simpl in *; try congruence.
      right. econstructor; eauto.
  Qed.

  Fact fresh_ident_hist_st : forall pref prefs vars hint b ty ck id v H (st st': fresh_st pref _),
      ~PS.In pref prefs ->
      Forall (fun '(x, _) => AtomOrGensym prefs x) vars ->
      (forall x, ~IsLast vars x) ->
      sem_clock (var_history H) b ck (abstract_clock v) ->
      fresh_ident hint (ty, ck) st = (id, st') ->
      hist_st vars b H st ->
      hist_st vars b (FEnv.add (Var id) v H) st'.
  Proof with auto.
    intros * Hnpref Hat Hnl Hsem Hfresh [Hdom Hsc].
    assert (~In id (st_ids st)) as Hnin by (eapply Facts.fresh_ident_nIn in Hfresh; eauto).
    assert (Hfresh':=Hfresh). apply fresh_ident_anns in Hfresh'.
    assert (FEnv.refines (@EqSt _) H (FEnv.add (Var id) v H)) as Href.
    { eapply fresh_ident_refines with (vars:=vars) in Hfresh; eauto.
      simpl_Forall; auto. }
    destruct Hsc as (Hsc1&Hsc2). split; [|split]; auto.
    - eapply fresh_ident_dom; eauto.
    - intros * Hck Hv. unfold st_senv in *.
      rewrite Hfresh' in Hck. simpl_app. simpl in *. rewrite <-Permutation_middle in Hck.
      inv Hck. inv H0.
      + inv H1. inv Hv. rewrite FEnv.gss in H1; inv H1.
        rewrite H2. eapply sem_clock_refines; eauto using var_history_refines.
      + eapply sem_clock_refines, Hsc1; eauto using var_history_refines with senv.
        inv Hv. econstructor; eauto. rewrite FEnv.gso in H2; auto.
        intro contra; inv contra.
        take (In _ (_ ++ _)) and apply in_app_iff in it as [Hin|Hin].
        * eapply Facts.fresh_ident_nIn' with (aft:=map fst vars); eauto.
          clear Hin. simpl_Forall; auto.
          solve_In.
        * eapply Hnin. unfold st_ids. solve_In.
    - intros * Hck Hla. exfalso.
      eapply NoLast_app; [|eauto]. split; auto. apply senv_of_tyck_NoLast.
  Qed.

  (** *** Correctness of the first pass *)

  Section unnest_node_sem.

    Variable G1 : @global nolocal local_prefs.
    Variable G2 : @global nolocal norm1_prefs.

    Hypothesis HwcG1 : wc_global G1.
    Hypothesis HwcG2 : wc_global G2.
    Hypothesis Hifaceeq : global_iface_incl G1 G2.
    Hypothesis HGref : global_sem_refines G1 G2.

    Hint Resolve iface_incl_wc_exp : norm.

    Section unnest_block_sem.

      Variable vars : static_env.

      Hypothesis Atoms : Forall (fun '(x, _) => AtomOrGensym local_prefs x) vars.
      Hypothesis NoLast : forall x, ~IsLast vars x.
      Import Unnesting.

      Corollary fresh_ident_refines1 : forall hint H a id (v: Stream svalue) (st st': fresh_st norm1 _),
          dom H (vars++st_senv st) ->
          fresh_ident hint a st = (id, st') ->
          FEnv.refines (@EqSt _) H (FEnv.add (Var id) v H).
      Proof.
        intros.
        eapply fresh_ident_refines with (vars:=vars); eauto using norm1_not_in_local_prefs.
        simpl_Forall; auto.
      Qed.

      Corollary fresh_ident_hist_st1 : forall hint b ty ck id v H (st st': fresh_st norm1 _),
          sem_clock (var_history H) b ck (abstract_clock v) ->
          fresh_ident hint (ty, ck) st = (id, st') ->
          hist_st vars b H st ->
          hist_st vars b (FEnv.add (Var id) v H) st'.
      Proof.
        intros.
        eapply fresh_ident_hist_st; eauto using norm1_not_in_local_prefs.
      Qed.

      Fact idents_for_anns_NoDupMembers : forall anns ids st st',
          idents_for_anns anns st = (ids, st') ->
          NoDupMembers ids.
      Proof.
        intros * Hids.
        apply idents_for_anns_vars_perm in Hids.
        specialize (st_valid_NoDup st') as Hvalid.
        rewrite fst_NoDupMembers in *.
        rewrite <- Hids in Hvalid.
        apply NoDup_app_l in Hvalid; auto.
      Qed.

      Corollary idents_for_anns_NoDup : forall anns ids st st',
          idents_for_anns anns st = (ids, st') ->
          NoDup (map (fun '(x, _) => Var x) ids).
      Proof.
        intros * Ids.
        apply idents_for_anns_NoDupMembers, fst_NoDupMembers in Ids.
        erewrite map_ext, <-map_map. apply FinFun.Injective_map_NoDup; eauto.
        2:intros; destruct_conjs; reflexivity.
        intros ?? Eq. now inv Eq.
      Qed.

      Fact idents_for_anns_nIn : forall anns ids st st',
          idents_for_anns anns st = (ids, st') ->
          Forall (fun id => ~In id (st_ids st)) (map fst ids).
      Proof.
        intros * Hids.
        specialize (st_valid_NoDup st') as Hvalid.
        apply idents_for_anns_vars_perm in Hids.
        unfold st_ids in *.
        rewrite <- Hids in Hvalid.
        rewrite Forall_forall. intros x Hin.
        eapply NoDup_app_In in Hvalid; eauto.
      Qed.

      Fact idents_for_anns_refines : forall H anns ids (vs : list (Stream svalue)) st st',
          length vs = length ids ->
          dom H (vars++st_senv st) ->
          idents_for_anns anns st = (ids, st') ->
          H ⊑ (H + FEnv.of_list (combine (map (fun '(x, _) => Var x) ids) vs)).
      Proof with eauto.
        intros * Hlen Hdom Hids ?? Hfind.
        do 2 esplit; try reflexivity.
        apply FEnv.union2; auto.
        assert (Forall (fun id => ~In id (map fst vars)) (List.map fst ids)) as Hnvar.
        { apply idents_for_anns_incl_ids in Hids.
          simpl_Forall. intros contra. simpl_In. simpl_Forall.
          eapply Facts.st_valid_AtomOrGensym_nIn; eauto using norm1_not_in_local_prefs.
          eapply Hids. solve_In. }
        rewrite FEnv.of_list_None, fst_InMembers, combine_map_fst'; auto. 2:solve_length.
        eapply idents_for_anns_nIn in Hids...
        intros Hin; simpl_In; simpl_Forall; simpl_In.
        assert (FEnv.In (Var i) H) as contra by (econstructor; eauto).
        apply Hdom, IsVar_app in contra as [Hv|]; eauto.
        - inv Hv. rewrite fst_InMembers in H0; eauto.
        - inv H0. eapply Hids. solve_In.
      Qed.

      Fact idents_for_anns_hist_st : forall b anns H ids vs st st',
          Forall2 (fun ck v => sem_clock (var_history H) b ck v) (map snd anns) (map abstract_clock vs) ->
          idents_for_anns anns st = (ids, st') ->
          hist_st vars b H st ->
          hist_st vars b (H + FEnv.of_list (combine (map (fun '(x, _) => Var x) ids) vs)) st'.
      Proof.
        setoid_rewrite Forall2_map_1. setoid_rewrite Forall2_map_2.
        unfold idents_for_anns.
        induction anns as [|(?&?)]; intros * Hf Hids Hhist;
          inv Hf; repeat inv_bind; simpl.
        - unfold FEnv.of_list; simpl.
          assert (FEnv.Equiv (@EqSt _) (H + (fun x => None)) H) as Heq.
          { intros ?. unfold FEnv.union. simpl. reflexivity. }
          destruct Hhist as (Hdom&Hsc). split.
          + split; intros ?; rewrite Heq; apply Hdom.
          + eapply sc_vars_morph. 1,3,4:eauto; reflexivity. auto.
        - eapply fresh_ident_hist_st1 in H0 as Hhist'; eauto.
          assert (Hids:=H1). eapply IHanns with (vs:=l') in H1 as (Hdom'&Hsc'). 3:eauto.
          2:{ simpl_Forall. eapply sem_clock_refines; eauto.
              eapply var_history_refines, fresh_ident_refines1; eauto. now destruct Hhist. }
          split; simpl in *.
          + destruct Hdom' as (D1&D2). split; intros ?; [rewrite <-D1|rewrite <-D2].
            1,2:rewrite 2 FEnv.union_In, FEnv.add_In, 2 FEnv.of_list_In; simpl.
            1,2:split; intros; repeat (take (_ \/ _) and destruct it); auto.
          + eapply sc_vars_morph. 4:eauto. 1,3:reflexivity.
            intros ?; simpl.
            unfold FEnv.union, FEnv.of_list, FEnv.add; simpl.
            repeat cases_eqn Heq; try reflexivity.
            all:repeat
                  match goal with
                  | H: Some _ = Some _ |- _ => inv H
                  | H:find _ _ = Some _ |- _ => apply find_some in H as (?In&?F)
                  | H:find _ _ = None |- _ => eapply find_none in H; [|now eauto]
                  | H:(_ ==b _) = true |- _ => rewrite equiv_decb_equiv in H; inv H; simpl in *; subst
                  | H: _ = Some _ |- _ => inv_equalities
                  end; try reflexivity; try congruence.
            * exfalso. apply in_combine_l in In.
              eapply idents_for_anns_nIn in Hids. simpl_In. simpl_Forall.
              eapply Facts.fresh_ident_Inids in H0; eauto.
            * eapply NoDupMembers_det in In0; [subst| |eauto]. subst; reflexivity.
              apply NoDup_NoDupMembers_combine.
              apply idents_for_anns_NoDup in Hids; auto.
            * exfalso. rewrite not_equiv_decb_equiv in Heq0. eapply Heq0. reflexivity.
      Qed.

      Ltac solve_incl :=
        repeat unfold idty; repeat unfold idck;
        match goal with
        | Hiface : global_iface_incl ?G1 ?G2, H : wt_clock (types ?G1) _ ?ck |- wt_clock (types ?G2) _ ?ck =>
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

      (** ** Conservation of sem_exp *)

      Fact unnest_reset_sem : forall b e H v e' eqs' st st',
          (forall e' eqs' st',
              unnest_exp G1 true e st = ([e'], eqs', st') ->
              exists H',
                FEnv.refines (@EqSt _) H H' /\
                  hist_st vars b H' st' /\
                  sem_exp_ck G2 H' b e' [v] /\ Forall (sem_equation_ck G2 H' b) eqs')  ->
          wc_exp G1 (vars++st_senv st) e ->
          numstreams e = 1 ->
          sem_exp_ck G1 H b e [v] ->
          hist_st vars b H st ->
          unnest_reset (unnest_exp G1 true) e st = (e', eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars b H' st' /\
                sem_exp_ck G2 H' b e' [v] /\
                Forall (sem_equation_ck G2 H' b) eqs').
      Proof with eauto.
        intros * Hun Hwc Hnum Hsem Histst Hnorm.
        unnest_reset_spec; simpl in *.
        1,2:assert (length l = 1) by (eapply unnest_exp_length in Hk0; eauto with lclocking norm; congruence).
        1,2:singleton_length.
        - specialize (Hun _ _ _ eq_refl) as (H'&Href&Histst1&Hsem1&Hsem2).
          exists H'. repeat (split; eauto).
        - specialize (Hun _ _ _ eq_refl) as (H'&Href&Histst1&Hsem1&Hsem2).
          assert (Href':=Hfresh); eapply fresh_ident_refines1 in Href'; eauto.
          2:(destruct Histst1 as (Hdom1&_); eauto).
          exists (FEnv.add (Var x1) v H'). split;[|split;[|split]]; eauto with fresh norm.
          + etransitivity; eauto.
          + eapply fresh_ident_hist_st1 in Hfresh; eauto.
            assert (Hk:=Hk0). eapply unnest_exp_annot in Hk0; eauto with lclocking.
            rewrite <-length_annot_numstreams, <-Hk0 in Hnum. simpl in Hnum; rewrite app_nil_r in Hnum.
            singleton_length.
            eapply sc_exp with (Γ:=vars++st_senv f) in Hsem1; eauto with env fresh norm.
            * rewrite clockof_annot, Hsingl in Hsem1. simpl in Hsem1. inv Hsem1; auto.
            * destruct Histst1. auto.
            * eapply unnest_exp_wc in Hwc as (Hwc'&_). 2-4:eauto.
              apply Forall_singl in Hwc'. auto.
          + repeat constructor.
            econstructor. eapply FEnv.gss. reflexivity.
          + constructor.
            eapply Seq with (ss:=[[v]]); simpl.
            1,2:repeat constructor.
            * eapply sem_exp_refines; eauto.
            * econstructor. eapply FEnv.gss. reflexivity.
            * simpl_Forall; eauto using sem_equation_refines.
      Qed.

      Corollary unnest_resets_sem : forall b es H vs es' eqs' st st',
          Forall (wc_exp G1 (vars++st_senv st)) es ->
          Forall (fun e => numstreams e = 1) es ->
          Forall2 (fun e v => sem_exp_ck G1 H b e [v]) es vs ->
          hist_st vars b H st ->
          Forall2 (fun e v => forall H e' eqs' st st',
                       wc_exp G1 (vars++st_senv st) e ->
                       sem_exp_ck G1 H b e [v] ->
                       hist_st vars b H st ->
                       unnest_exp G1 true e st = ([e'], eqs', st') ->
                       (exists H',
                           FEnv.refines (@EqSt _) H H' /\
                             hist_st vars b H' st' /\
                             sem_exp_ck G2 H' b e' [v] /\
                             Forall (sem_equation_ck G2 H' b) eqs')) es vs ->
          mmap2 (unnest_reset (unnest_exp G1 true)) es st = (es', eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars b H' st' /\
                Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es' vs /\
                Forall (sem_equation_ck G2 H' b) (concat eqs')).
      Proof with eauto.
        induction es; intros * Hwt Hnum Hsem Histst Hf Hmap;
          inv Hwt; inv Hnum; inv Hsem; inv Hf; repeat inv_bind.
        - exists H; simpl. repeat (split; eauto). reflexivity.
        - assert (Hr:=H0). eapply unnest_reset_sem in H0 as (H'&Href1&Histst1&Hsem1&Hsem1'); eauto.
          assert (Forall2 (fun e v => sem_exp_ck G1 H' b e [v]) es l') as Hsem'.
          { eapply Forall2_impl_In; [|eapply H8]; intros. eapply sem_exp_refines... }
          eapply IHes in H1 as (H''&Href2&Histst2&Hsem2&Hsem2')...
          2:simpl_Forall; repeat solve_incl.
          clear IHes H9.
          exists H''. repeat (split; eauto).
          + etransitivity...
          + constructor; eauto. subst.
            eapply sem_exp_refines; eauto.
          + apply Forall_app. split...
            simpl_Forall; eauto using sem_equation_refines.
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
        rewrite Forall2_swap_args in Hsem1, Hsem2.
        eapply Forall3_trans_ex1 in Hfby; eauto. eapply Forall3_trans_ex2 in Hfby; eauto.
        simpl_Forall. apply Forall3_combine'1, Forall3_ignore2'', Forall3_combine'1. solve_length.
        eapply Forall3_impl_In; [|eauto]. intros; destruct_conjs.
        econstructor... econstructor...
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
        rewrite Forall2_swap_args in Hsem1, Hsem2.
        eapply Forall3_trans_ex1 in Hfby; eauto. eapply Forall3_trans_ex2 in Hfby; eauto.
        simpl_Forall. apply Forall3_combine'1, Forall3_ignore2'', Forall3_combine'1. solve_length.
        eapply Forall3_impl_In; [|eauto]. intros; destruct_conjs.
        econstructor... econstructor...
      Qed.

      Fact unnest_when_sem : forall H bs es tys ckid tx b ck s ss os,
          length es = length tys ->
          Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) es ss ->
          sem_var H (Var ckid) s ->
          Forall2 (fun s' => when b s' s) ss os ->
          Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) (unnest_when (ckid, tx) b es tys ck) os.
      Proof with eauto.
        intros * Hlen Hsem Hvar Hwhen.
        unfold unnest_when. simpl_Forall.
        eapply Forall3_combine'1, Forall3_ignore2''; auto.
        eapply Forall2_trans_ex in Hwhen; eauto. simpl_Forall.
        eapply Swhen with (ss:=[[_]])...
        simpl. repeat constructor. auto.
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

      Fact unnest_merge_sem : forall vars H bs tys x tx es ck s vs os,
          es <> [] ->
          Forall (fun es => Forall (wc_exp G2 vars) (snd es)) es ->
          Forall (fun es => length (annots (snd es)) = length tys) es ->
          Forall (fun es => Forall (fun e => numstreams e = 1) (snd es)) es ->
          sem_var H (Var x) s ->
          Forall2Brs (sem_exp_ck G2 H bs) es vs ->
          Forall2 (merge s) vs os ->
          Forall2 (fun e s => sem_exp_ck G2 H bs e [s]) (unnest_merge (x, tx) es tys ck) os.
      Proof with eauto.
        induction tys; intros * Hnnil Hwc Hlen Hnum Hvar Hsem Hmerge; simpl in *; auto.
        - eapply Forall2Brs_length1 in Hsem.
          2:{ simpl_Forall. eapply sem_exp_ck_numstreams; eauto with lclocking. }
          inv Hsem; try congruence. inv Hlen.
          rewrite H0 in H4. destruct vs; simpl in *; try congruence.
          inv Hmerge; auto.
        - assert (length vs = S (length tys)) as Hlen'.
          { eapply Forall2Brs_length1 in Hsem.
            2:{ simpl_Forall. eapply sem_exp_ck_numstreams; eauto with lclocking. }
            inv Hsem; try congruence. inv Hlen.
            congruence. }
          destruct vs; simpl in *; inv Hlen'.
          assert (forall x v, Exists (fun es0 => In x (snd es0)) es -> sem_exp_ck G2 H bs x v -> length v = 1) as Hlv.
          { intros ?? Hex Hse. eapply Exists_exists in Hex as (?&Hin1&Hin2).
            do 2 (eapply Forall_forall in Hwc; eauto). do 2 (eapply Forall_forall in Hnum; eauto).
            eapply sem_exp_ck_numstreams in Hse; eauto with lclocking.
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

      Fact unnest_case_sem : forall vars H bs tys ec es d ck s vs vd os,
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
          2:{ simpl_Forall. eapply sem_exp_ck_numstreams; eauto with lclocking. }
          inv Hsem; try congruence. inv Hlen.
          rewrite H0 in H4. destruct vs; simpl in *; try congruence.
          inv Hmerge; auto.
        - assert (length vs = S (length tys)) as Hlen'.
          { eapply Forall2Brs_length1 in Hsem.
            2:{ simpl_Forall. eapply sem_exp_ck_numstreams; eauto with lclocking. }
            inv Hsem; try congruence. inv Hlen.
            congruence. }
          destruct vs; simpl in *; inv Hlen'.
          assert (forall x v, Exists (fun es0 => In x (snd es0)) es -> sem_exp_ck G2 H bs x v -> length v = 1) as Hlv.
          { intros ?? Hex Hse. eapply Exists_exists in Hex as (?&Hin1&Hin2).
            simpl_Forall.
            eapply sem_exp_ck_numstreams in Hse; eauto with lclocking.
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

      Lemma sem_new_vars : forall H xs vs,
          length xs = length vs ->
          NoDup xs ->
          Forall2 (sem_var (H + FEnv.of_list (combine xs vs))) xs vs.
      Proof.
        intros * Hlen Hndup.
        eapply Forall2_forall2; split; auto; intros; subst.
        apply sem_var_union3', sem_var_of_list; eauto using NoDup_NoDupMembers_combine.
        rewrite <-combine_nth; auto. apply nth_In.
        now rewrite combine_length, <-Hlen, Nat.min_id.
      Qed.

      Fact mmap2_sem : forall b is_control es H vs es' eqs' st st',
          Forall (wc_exp G1 (vars++st_senv st)) es ->
          Forall2 (sem_exp_ck G1 H b) es vs ->
          hist_st vars b H st ->
          Forall
            (fun e => forall H vs is_control es' eqs' st st',
                 wc_exp G1 (vars++st_senv st) e ->
                 sem_exp_ck G1 H b e vs ->
                 hist_st vars b H st ->
                 unnest_exp G1 is_control e st = (es', eqs', st') ->
                 exists H' : FEnv.t (Stream svalue),
                   FEnv.refines (@EqSt _) H H' /\
                     hist_st vars b H' st' /\
                     Forall2 (fun (e0 : exp) (v : Stream svalue) => sem_exp_ck G2 H' b e0 [v]) es' vs /\
                     Forall (sem_equation_ck G2 H' b) eqs') es ->
          mmap2 (unnest_exp G1 is_control) es st = (es', eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars b H' st' /\
                Forall2 (fun es vs => Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es vs) es' vs /\
                Forall (sem_equation_ck G2 H' b) (concat eqs')).
      Proof with eauto.
        induction es; intros * Hwc Hsem Histst Hf Hmap;
          inv Hwc; inv Hsem; inv Hf; repeat inv_bind.
        - exists H; simpl. repeat (split; eauto with env). reflexivity.
        - assert (Hun1:=H0). eapply H5 in H0 as (H'&Href1&Histst1&Hsem1&Hsem1'); eauto.
          assert (Forall2 (sem_exp_ck G1 H' b) es l') as Hsem'.
          { eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines... }
          eapply IHes in H1 as (H''&Href2&Histst2&Hsem2&Hsem2'); eauto.
          2:(simpl_Forall; repeat solve_incl).
          clear IHes H7.
          exists H''. repeat (split; eauto).
          + etransitivity...
          + constructor; eauto. subst.
            assert (length x = numstreams a) as Hlength1 by (eapply unnest_exp_length; eauto with lclocking).
            assert (length y = numstreams a) as Hlength2 by (eapply sem_exp_ck_numstreams; eauto with lclocking).
            simpl_Forall; eauto using sem_exp_refines.
          + apply Forall_app. split...
            simpl_Forall; eauto using sem_equation_refines...
      Qed.

      Hint Constructors Forall2Brs : norm.

      Fact mmap2_mmap2_sem : forall b is_control es H vs es' eqs' st st',
          Forall (fun es => Forall (wc_exp G1 (vars++st_senv st)) (snd es)) es ->
          Forall2Brs (sem_exp_ck G1 H b) es vs ->
          hist_st vars b H st ->
          Forall
            (fun es => Forall
                      (fun e => forall H vs is_control es' eqs' st st',
                           wc_exp G1 (vars++st_senv st) e ->
                           sem_exp_ck G1 H b e vs ->
                           hist_st vars b H st ->
                           unnest_exp G1 is_control e st = (es', eqs', st') ->
                           exists H' : FEnv.t (Stream svalue),
                             FEnv.refines (@EqSt _) H H' /\
                               hist_st vars b H' st' /\
                               Forall2 (fun e0 v => sem_exp_ck G2 H' b e0 [v]) es' vs /\
                               Forall (sem_equation_ck G2 H' b) eqs') (snd es)) es ->
          mmap2 (fun '(i, es) => bind2 (mmap2 (unnest_exp G1 is_control) es) (fun es' eqs' => ret ((i, concat es'), concat eqs'))) es st = (es', eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars b H' st' /\
                Forall2Brs (sem_exp_ck G2 H' b) es' vs /\
                Forall (sem_equation_ck G2 H' b) (concat eqs')).
      Proof with eauto.
        induction es; intros * Hwc Hsem Histst Hf Hmap;
          inv Hwc; inv Hsem; inv Hf; repeat inv_bind.
        - exists H; simpl. repeat (split; eauto with env norm). reflexivity.
        - eapply mmap2_sem in H6 as (H'&Href1&Histst1&Hsem1&Hsem1'); eauto.
          assert (Forall2Brs (sem_exp_ck G1 H' b) es vs2) as Hsem'.
          { eapply Forall2Brs_impl_In; [|eauto]; intros ?? _ ?.
            eapply sem_exp_refines... }
          eapply IHes in H1 as (H''&Href2&Histst2&Hsem2&Hsem2')... clear IHes H8.
          2:(simpl_Forall; repeat solve_incl).
          exists H''. repeat (split; eauto).
          + etransitivity...
          + econstructor. instantiate (1:=concat (map (map (fun x => [x])) vs1)).
            { eapply Forall2_concat. simpl_Forall.
              eapply sem_exp_refines...
            }
            2:{ rewrite <-concat_map, concat_map_singl1; eauto. }
            eauto.
          + apply Forall_app. split...
            simpl_Forall; eauto using sem_equation_refines.
      Qed.

      Lemma unnest_noops_exp_sem : forall b cki e H v e' eqs' st st',
          hist_st vars b H st ->
          normalized_lexp e ->
          wc_exp G2 (vars++st_senv st) e ->
          sem_exp_ck G2 H b e [v] ->
          unnest_noops_exp cki e st = (e', eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars b H' st' /\
                sem_exp_ck G2 H' b e' [v] /\
                Forall (sem_equation_ck G2 H' b) eqs').
      Proof.
        unfold unnest_noops_exp.
        intros * Hdom Hnormed Hwc Hsem Hunt.
        assert (numstreams e = 1) as Hnum by (eapply normalized_lexp_numstreams; eauto).
        rewrite <-length_annot_numstreams in Hnum. singleton_length.
        destruct p as (?&?).
        destruct (is_noops_exp _ _); repeat inv_bind.
        - exists H; repeat (split; auto). reflexivity.
        - assert (Hfresh:=H0).
          assert (FEnv.refines (EqSt (A:=svalue)) H (FEnv.add (Var x) v H)) as Href.
          { eapply fresh_ident_refines1; eauto.
            destruct Hdom as (Hdom&_); auto. }
          exists (FEnv.add (Var x) v H). split;[|split;[|split]]; auto.
          + eapply fresh_ident_hist_st1; eauto.
            eapply sc_exp in Hsem; eauto. 2:destruct Hdom; auto.
            rewrite clockof_annot, Hsingl in Hsem; inv Hsem; eauto.
          + constructor. econstructor.
            eapply FEnv.gss. reflexivity.
          + constructor; auto.
            apply Seq with (ss:=[[v]]); simpl.
            * constructor; auto. eapply sem_exp_refines; eauto.
            * constructor; auto. econstructor.
              eapply FEnv.gss. reflexivity.
      Qed.

      Lemma unnest_noops_exps_sem : forall b cks es H vs es' eqs' st st',
          length es = length cks ->
          hist_st vars b H st ->
          Forall normalized_lexp es ->
          Forall (wc_exp G2 (vars++st_senv st)) es ->
          Forall2 (fun e v => sem_exp_ck G2 H b e [v]) es vs ->
          unnest_noops_exps cks es st = (es', eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars b H' st' /\
                Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es' vs /\
                Forall (sem_equation_ck G2 H' b) eqs').
      Proof.
        unfold unnest_noops_exps.
        induction cks; intros * Hlen Hdom Hnormed Hwc Hsem Hunt; repeat inv_bind; simpl; auto.
        1,2:destruct es; simpl in *; inv Hlen; repeat inv_bind.
        - inv Hsem. exists H. repeat (split; auto). reflexivity.
        - inv Hsem. inv Hnormed. inv Hwc.
          assert (Hnoops:=H0). eapply unnest_noops_exp_sem in H0 as (H'&?&?&?&?); eauto.
          assert (Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es l') as Hsem'.
          { eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines; eauto. }
          eapply IHcks with (st:=x2) in Hsem' as (H''&?&?&?&?); eauto.
          2:simpl_Forall; repeat solve_incl; eauto using unnest_noops_exp_st_follows.
          2:inv_bind; repeat eexists; eauto; inv_bind; eauto.
          exists H''. split;[|split;[|split]]; eauto.
          + etransitivity; eauto.
          + constructor; eauto using sem_exp_refines.
          + simpl. rewrite Forall_app; split; auto.
            simpl_Forall; eauto using sem_equation_refines.
      Qed.

      Hint Resolve sem_ref_sem_exp : lcsem.
      Hint Constructors sem_exp_ck : lcsem.

      Fact unnest_exp_sem : forall b e H vs is_control es' eqs' st st',
          wc_exp G1 (vars++st_senv st) e ->
          sem_exp_ck G1 H b e vs ->
          hist_st vars b H st ->
          unnest_exp G1 is_control e st = (es', eqs', st') ->
          (exists H',
              H ⊑ H' /\
                hist_st vars b H' st' /\
                Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es' vs /\
                Forall (sem_equation_ck G2 H' b) eqs').
      Proof with eauto with norm lclocking.
        induction e using exp_ind2; intros * Hwc Hsem Histst Hnorm; repeat inv_bind. 12,13:inv Hwc; inv Hsem.
        - (* const *)
          inv Hsem. exists H. repeat (split; auto with lcsem). reflexivity.
        - (* enum *)
          inv Hsem. exists H. repeat (split; auto with lcsem). reflexivity.
        - (* var *)
          inv Hsem. exists H. repeat (split; auto with lcsem). reflexivity.
        - (* last *)
          inv Hsem. exists H. repeat (split; auto with lcsem). reflexivity.
        - (* unop *)
          inv Hsem. inv Hwc.
          assert (Htypeof:=H0). eapply unnest_exp_typeof in Htypeof...
          assert (Hnorm:=H0). eapply IHe in Hnorm as [H' [Href1 [Hhistst1 [Hsem1 Hsem1']]]]...
          eapply unnest_exp_length in H0... rewrite <-length_clockof_numstreams, H5 in H0. singleton_length.
          inv Hsem1.
          exists H'. repeat (split; eauto).
          repeat econstructor... congruence.
        - (* binop *)
          inv Hsem; inv Hwc.
          assert (Htypeof1:=H0). eapply unnest_exp_typeof in Htypeof1...
          assert (Htypeof2:=H1). eapply unnest_exp_typeof in Htypeof2...
          assert (Hun1:=H0). eapply IHe1 in H0 as [H' [Href1 [Histst1 [Hsem1 Hsem1']]]]... clear IHe1.
          eapply sem_exp_refines in H10; eauto.
          eapply IHe2 in H1 as [H'' [Href2 [Histst2 [Hsem2 Hsem2']]]]... clear IHe2.
          2:repeat solve_incl.
          inv Hsem1; inv H4. inv Hsem2; inv H5.
          simpl in *; rewrite app_nil_r in *.
          exists H''. repeat (split; eauto).
          + etransitivity...
          + repeat econstructor...
            * eapply sem_exp_refines...
            * congruence.
            * congruence.
          + apply Forall_app. split; simpl_Forall; eauto using sem_equation_refines.

        - (* extcall *)
          destruct_conjs; repeat inv_bind.
          eapply sc_exp in Hsem as Hsck... 2:destruct Histst; auto.
          inv Hwc; inv Hsem. simpl_Forall.

          assert (Hnorm1:=H1). eapply mmap2_sem in H1... clear H.
          destruct H1 as [H' [Href1 [Histst1 [Hsem1' Hsem1'']]]]. apply Forall2_concat in Hsem1'.

          assert (Hnorm2:=H2). eapply fresh_ident_refines1 in H2... 2:destruct Histst1...
          eapply fresh_ident_hist_st1 with (H:=H') in Hnorm2 as Histst2...
          2:eapply sem_clock_refines; eauto using var_history_refines.

          assert (sem_var (FEnv.add (Var x2) vs0 H') (Var x2) vs0) as Hv.
          { repeat constructor. econstructor; simpl.
            rewrite FEnv.gss; eauto. reflexivity. }
          exists (FEnv.add (Var x2) vs0 H'). split;[|split;[|split]]; eauto with norm.
          + etransitivity...
          + repeat constructor; eauto.
          + repeat constructor; eauto.
            2:simpl_Forall; eauto using sem_equation_refines.
            econstructor. econstructor; eauto. 1,2:simpl; econstructor.
            2:instantiate (1:=map (fun x => [x]) (concat ss)).
            all:try rewrite concat_map_singl1; eauto; simpl_Forall; eauto using sem_exp_refines.
            eapply mmap2_unnest_exp_typesof in Hnorm1; eauto with lclocking.
            congruence.

        - (* fby *)
          inversion_clear Hwc as [| | | | | | |??? Hwc1 Hwc2 Hl1 Hl2 | | | | |].
          inversion_clear Hsem as [| | | | | | |???????? Hsem1 Hsem2 Fby| | | | | |].
          assert (length (concat x2) = length (annots e0s)) as Hlength1 by (eapply mmap2_unnest_exp_length; eauto with lclocking).
          assert (length (concat x6) = length (annots es)) as Hlength2 by (eapply mmap2_unnest_exp_length; eauto with lclocking).
          assert (Forall (fun e => numstreams e = 1) (concat x2)) as Hnumstreams.
          { eapply mmap2_unnest_exp_numstreams in H2... }

          assert (length s0ss = length e0s) as Hlen1 by (eapply Forall2_length in Hsem1; eauto).
          assert (H2':=H2). eapply mmap2_sem in H2... clear H.
          destruct H2 as [H' [Href1 [Histst1 [Hsem1' Hsem1'']]]]. apply Forall2_concat in Hsem1'.

          assert (Forall2 (sem_exp_ck G1 H' b) es sss) as Hsem' by (simpl_Forall; eauto using sem_exp_refines).
          assert (length sss = length es) as Hlen2 by (eapply Forall2_length in Hsem2; eauto).
          assert (H3':=H3). eapply mmap2_sem in H3... clear H0.
          2:simpl_Forall; repeat solve_incl.
          destruct H3 as [H'' [Href2 [Histst2 [Hsem2' Hsem2'']]]]. apply Forall2_concat in Hsem2'.

          assert (Forall2 (fun e v => sem_exp_ck G2 H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
          { eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines... }
          specialize (idents_for_anns_length _ _ _ _ H4) as Hlength.
          assert (length vs = length a) as Hlength'''.
          { eapply Forall3_length in Fby as [_ ?]. eapply Forall2_length in Hsem2'. eapply Forall2_length in Hl2.
            solve_length. }

          remember (H'' + FEnv.of_list (combine (List.map (fun '(x, _) => Var x) x5) vs)) as H''''.
          assert (length x5 = length vs) as Hlength'''' by (rewrite Hlength, Hlength'''; auto).

          assert (Forall2 (sem_var H'''') (List.map (fun '(x, _) => Var x) x5) vs) as Hsemvars.
          { rewrite HeqH''''. eapply sem_new_vars; eauto.
            + rewrite map_length; auto.
            + eapply idents_for_anns_NoDup in H4; eauto. }

          assert (FEnv.refines (@EqSt _) H'' H'''') as Href4.
          { subst. eapply idents_for_anns_refines in H4...
            destruct Histst2 as (Hdom2&_)... }
          clear Hlength'''.

          assert (Forall2 (fun e v => sem_exp_ck G2 H'''' b e [v]) (unnest_fby (concat x2) (concat x6) a) vs) as Hsemf.
          { eapply unnest_fby_sem; simpl...
            + eapply mmap2_unnest_exp_length in H2'... eapply Forall2_length in Hl1. solve_length.
            + eapply mmap2_unnest_exp_length in H3'... eapply Forall2_length in Hl2. solve_length.
            + clear - Hsem1' Href2 Href4. eapply Forall2_impl_In... intros; simpl in *.
              repeat (eapply sem_exp_refines; eauto).
            + clear - Hsem2' Href2 Href4. eapply Forall2_impl_In... intros; simpl in *.
              repeat (eapply sem_exp_refines; eauto). }

          exists H''''. split;[|split;[|split]];eauto with norm.
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
            eapply sem_clock_refines; eauto using var_history_refines.
          * clear - Hsemvars. simpl_Forall; eauto with lcsem.
          * repeat rewrite Forall_app. repeat split.
            apply mk_equations_Forall.
            2-3:(simpl_Forall; repeat (eapply sem_equation_refines; eauto)).
            clear - Hsemvars Hsemf.
            remember (unnest_fby _ _ _) as fby. clear Heqfby.
            simpl_Forall. eapply Forall2_swap_args, Forall2_trans_ex in Hsemf; eauto.
            simpl_Forall.
            econstructor.
            -- repeat constructor; eauto.
            -- simpl. repeat constructor; eauto.

        - (* arrow *)
          inversion_clear Hwc as [| | | | | | | |??? Hwc1 Hwc2 Hl1 Hl2| | | |].
          inversion_clear Hsem as [| | | | | | | |???????? Hsem1 Hsem2 Arrow| | | | |].
          assert (length (concat x2) = length (annots e0s)) as Hlength1 by (eapply mmap2_unnest_exp_length; eauto with lclocking).
          assert (length (concat x6) = length (annots es)) as Hlength2 by (eapply mmap2_unnest_exp_length; eauto with lclocking).
          assert (Forall (fun e => numstreams e = 1) (concat x2)) as Hnumstreams.
          { eapply mmap2_unnest_exp_numstreams in H2... }

          assert (length s0ss = length e0s) as Hlen1 by (eapply Forall2_length in Hsem1; eauto).
          assert (H2':=H2). eapply mmap2_sem in H2... clear H.
          destruct H2 as [H' [Href1 [Histst1 [Hsem1' Hsem1'']]]]. apply Forall2_concat in Hsem1'.

          assert (Forall2 (sem_exp_ck G1 H' b) es sss) as Hsem' by (simpl_Forall; eapply sem_exp_refines; eauto).
          assert (length sss = length es) as Hlen2 by (eapply Forall2_length in Hsem2; eauto).
          assert (H3':=H3). eapply mmap2_sem in H3... clear H0.
          2:simpl_Forall; repeat solve_incl.
          destruct H3 as [H'' [Href2 [Histst2 [Hsem2' Hsem2'']]]]. apply Forall2_concat in Hsem2'.

          assert (Forall2 (fun e v => sem_exp_ck G2 H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''.
          { eapply Forall2_impl_In; [|eauto]; intros. eapply sem_exp_refines... }
          specialize (idents_for_anns_length _ _ _ _ H4) as Hlength.
          assert (length vs = length a) as Hlength'''.
          { eapply Forall3_length in Arrow as [_ ?]. eapply Forall2_length in Hsem2'. eapply Forall2_length in Hl2.
            solve_length. }

          remember (H'' + FEnv.of_list (combine (List.map (fun '(x, _) => Var x) x5) vs)) as H''''.
          assert (length x5 = length vs) as Hlength'''' by (rewrite Hlength, Hlength'''; auto).

          assert (Forall2 (sem_var H'''') (map (fun '(x, _) => Var x) x5) vs) as Hsemvars.
          { rewrite HeqH''''. eapply sem_new_vars; eauto.
            + rewrite map_length; auto.
            + eapply idents_for_anns_NoDup in H4; eauto. }

          assert (FEnv.refines (@EqSt _) H'' H'''') as Href4.
          { subst. eapply idents_for_anns_refines in H4...
            destruct Histst2 as (Hdom2&_)... }
          clear Hlength'''.

          assert (Forall2 (fun e v => sem_exp_ck G2 H'''' b e [v]) (unnest_arrow (concat x2) (concat x6) a) vs) as Hsemf.
          { eapply unnest_arrow_sem; simpl...
            + eapply mmap2_unnest_exp_length in H2'... eapply Forall2_length in Hl1. solve_length.
            + eapply mmap2_unnest_exp_length in H3'... eapply Forall2_length in Hl2. solve_length.
            + clear - Hsem1' Href2 Href4. simpl_Forall; eauto using sem_exp_refines.
            + clear - Hsem2' Href2 Href4. simpl_Forall; eauto using sem_exp_refines. }

          exists H''''. split;[|split;[|split]];eauto with norm.
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
            eapply sem_clock_refines; eauto using var_history_refines.
          * clear - Hsemvars. simpl_Forall; auto with lcsem.
          * repeat rewrite Forall_app. repeat split.
            apply mk_equations_Forall.
            2-3:(simpl_Forall; eauto using sem_equation_refines).
            clear - Hsemvars Hsemf.
            remember (unnest_arrow _ _ _) as arrow. clear Heqarrow.
            simpl_Forall. eapply Forall2_swap_args, Forall2_trans_ex in Hsemf; eauto.
            simpl_Forall.
            econstructor.
            -- repeat constructor; eauto.
            -- simpl. repeat constructor; eauto.

        - (* when *)
          inv Hwc. inv Hsem. repeat inv_bind.
          assert (length (concat x1) = length (annots es)) as Hlength by (eapply mmap2_unnest_exp_length; eauto with lclocking).
          assert (length es = length ss) by (apply Forall2_length in H14; auto).
          eapply mmap2_sem in H1... clear H.
          destruct H1 as [H' [Href1 [Hhistst1 [Hsem1 Hsem1']]]].
          apply Forall2_concat in Hsem1.
          exists H'. repeat (split; simpl; eauto).
          eapply unnest_when_sem... solve_length.
          eapply sem_var_refines...

        - (* merge *)
          inv Hwc. inv Hsem. repeat inv_bind.
          eapply mmap2_mmap2_sem in H as (Hi1&Href1&Histst1&Hsem1&Hsem1')...
          assert (Forall2 (fun e v => sem_exp_ck G2 Hi1 b e [v])
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
            remember (Hi1 + FEnv.of_list (combine (List.map (fun '(x, _) => Var x) x3) vs)) as Hi2.
            assert (length vs = length x3) as Hlength'.
            { eapply idents_for_anns_length in H. repeat simpl_length.
              apply Forall2Brs_length1 in H15.
              2:{ simpl_Forall. eapply sem_exp_ck_numstreams; eauto with lclocking. }
              inv H15; try congruence. inv H8; auto.
              eapply Forall2_length in H16. solve_length. }
            assert (FEnv.refines (@EqSt _) Hi1 Hi2) as Href3.
            { subst. eapply idents_for_anns_refines...
              destruct Histst1 as (Hdom1&_)... }
            assert (Forall2 (sem_var Hi2) (map (fun '(x, _) => Var x) x3) vs) as Hvars.
            { rewrite HeqHi2. eapply sem_new_vars... 1:rewrite map_length...
              eapply idents_for_anns_NoDup... }
            exists Hi2. split;[|split;[|split]]; eauto with norm.
            * repeat (etransitivity; eauto).
            * subst. eapply idents_for_anns_hist_st...
              erewrite map_map, map_ext, <-unnest_merge_clocksof with (nck:=ck); auto.
              { eapply sc_exps2; eauto. destruct Histst1; eauto.
                - eapply unnest_merge_wc_exp; eauto.
                  + repeat solve_incl.
                  + eapply mmap2_length_1 in H1.
                    contradict H5; subst; destruct es; simpl in *; congruence.
                  + eapply mmap2_mmap2_unnest_exp_length in H1; eauto.
                    2:{ simpl_Forall; eauto with lclocking. }
                    eapply Forall2_ignore1 in H1. simpl_Forall.
                    rewrite H3, H8. solve_length.
                  + eapply mmap2_mmap2_unnest_exp_wc...
                  + eapply mmap2_mmap2_unnest_exp_clocksof1; eauto.
              }
            * clear - Hvars. simpl_Forall. eauto with lcsem.
            * repeat rewrite Forall_app; repeat split.
              -- remember (unnest_merge _ _ _ _) as merge.
                 assert (length merge = length x3) as Hlength''.
                 { eapply idents_for_anns_length in H.
                   subst. rewrite unnest_merge_length. solve_length. }
                 clear - Hvars Hsem' Href3 Hlength''. apply mk_equations_Forall. simpl_forall.
                 eapply Forall2_swap_args, Forall2_trans_ex in Hsem'; [|eauto].
                 simpl_Forall.
                 apply Seq with (ss:=[[x]]); simpl.
                 1,2:repeat constructor... eapply sem_exp_refines...
              -- simpl_Forall. repeat (eapply sem_equation_refines; eauto).

        - (* case (total) *)
          repeat inv_bind.
          assert (length x = 1). 2:singleton_length.
          { eapply unnest_exp_length in H2... rewrite H2, <-length_clockof_numstreams, H7; auto. }
          assert (Hun1:=H2). eapply IHe in H2 as (Hi1&Href1&Histst1&Hsem1&Hsem1')... clear IHe.
          eapply Forall2_singl in Hsem1.

          assert (Forall (fun es => Forall (wc_exp G1 (vars ++ st_senv x1)) (snd es)) es) as Hwces.
          { simpl_Forall. repeat solve_incl. }
          assert (Forall2Brs (sem_exp_ck G1 Hi1 b) es vs0) as Hses.
          { eapply Forall2Brs_impl_In; [|eauto]; intros ?? _ Hse.
            eapply sem_exp_refines... }
          eapply mmap2_mmap2_sem in H as (Hi2&Href2&Histst2&Hsem2&Hsem2')...

          assert (Forall2 (fun e v => sem_exp_ck G2 Hi2 b e [v])
                    (unnest_case e0 x2 None tys ck) vs) as Hsem'.
          { eapply unnest_case_sem...
            - eapply mmap2_length_1 in H3.
              destruct es, x2; simpl in *; try congruence; auto.
            - eapply mmap2_mmap2_unnest_exp_wc; eauto.
            - eapply mmap2_mmap2_unnest_exp_annots in H3. 2:eapply Forall_impl; [|eapply H9]; intros (?&?); eauto with lclocking.
              eapply Forall2_ignore1 in H3. simpl_Forall.
              rewrite H3, H11, length_clocksof_annots; eauto.
            - eapply mmap2_mmap2_unnest_exp_numstreams; eauto.
            - eapply sem_exp_refines...
            - simpl. reflexivity.
            - eapply Forall2_forall2 in H22 as (Len&Case).
              assert (length vs0 = length tys) as Len1.
              { apply Forall2Brs_length1 in H21.
                2:simpl_Forall; eapply sem_exp_ck_numstreams; eauto with lclocking.
                inv H21; try congruence. simpl_Forall.
                solve_length. }
              eapply Forall3_forall3. repeat split; auto.
              + now rewrite map_length.
              + intros * N Nth1 Nth2 Nth3.
                erewrite map_nth' with (d':=OpAux.bool_velus_type) in Nth2; [|congruence]; subst.
                eapply Case; eauto.
          }
          destruct is_control; repeat inv_bind.
          + (* control *)
            exists Hi2. repeat (split; simpl; eauto).
            * etransitivity...
            * apply Forall_app; split; auto.
              simpl_Forall; eauto using sem_equation_refines.
          + (* exp *)
            remember (Hi2 + FEnv.of_list (combine (List.map (fun '(x, _) => Var x) x) vs)) as Hi3.
            assert (length vs = length x) as Hlength'.
            { eapply idents_for_anns_length in H. repeat simpl_length.
              apply Forall2Brs_length1 in H21.
              2:{ simpl_Forall; eapply sem_exp_ck_numstreams; eauto with lclocking. }
              inv H21; try congruence. inv H11; auto.
              eapply Forall2_length in H22 as ?. solve_length. }
            assert (FEnv.refines (@EqSt _) Hi2 Hi3) as Href3.
            { subst. eapply idents_for_anns_refines...
              destruct Histst2 as (Hdom1&_)... }
            assert (Forall2 (sem_var Hi3) (map (fun '(x, _) => Var x) x) vs) as Hvars.
            { rewrite HeqHi3. eapply sem_new_vars... 1:rewrite map_length...
              eapply idents_for_anns_NoDup; eauto. }
            exists Hi3. split;[|split;[|split]]; eauto with norm.
            * repeat (etransitivity; eauto).
            * subst. eapply idents_for_anns_hist_st...
              erewrite map_map, map_ext, <-unnest_case_clocksof with (nck:=ck); auto.
              { eapply sc_exps2; eauto. destruct Histst2; eauto.
                - eapply unnest_case_wc_exp; eauto.
                  + eapply unnest_exp_wc in Hun1 as (Hwc&_); eauto. apply Forall_singl in Hwc.
                    repeat solve_incl.
                  + eapply unnest_exp_clockof in Hun1; eauto with lclocking. simpl in Hun1; rewrite app_nil_r in Hun1.
                    congruence.
                  + eapply mmap2_length_1 in H3.
                    contradict H8; subst; destruct es; simpl in *; congruence.
                  + eapply mmap2_mmap2_unnest_exp_length in H3; eauto.
                    2:{ simpl_Forall; eauto with lclocking. }
                    eapply Forall2_ignore1 in H3. simpl_Forall.
                    rewrite H4, H11. solve_length.
                  + eapply mmap2_mmap2_unnest_exp_wc...
                  + eapply mmap2_mmap2_unnest_exp_clocksof2; eauto.
              }
            * clear - Hvars. simpl_Forall; eauto with lcsem.
            * repeat rewrite Forall_app; repeat split. 2,3:simpl_Forall; eauto using sem_equation_refines.
              remember (unnest_case _ _ _ _ _) as merge.
              assert (length merge = length x) as Hlength''.
              { eapply idents_for_anns_length in H.
                subst. rewrite unnest_case_length. solve_length. }
              clear - Hvars Hsem' Href3 Hlength''. apply mk_equations_Forall. simpl_forall.
              rewrite Forall2_swap_args in Hsem'.
              eapply Forall2_trans_ex in Hsem'; [|eauto]. simpl_Forall.
              apply Seq with (ss:=[[x0]]); simpl.
              1,2:repeat constructor... eapply sem_exp_refines...

        - (* case (default) *)
          repeat inv_bind. simpl in *.
          assert (length x = 1). 2:singleton_length.
          { eapply unnest_exp_length in H2... rewrite H2, <-length_clockof_numstreams, H7; auto. }
          assert (Hun1:=H2). eapply IHe in H2 as (Hi1&Href1&Histst1&Hsem1&Hsem1')... clear IHe.
          eapply Forall2_singl in Hsem1.

          assert (Forall (fun es => Forall (wc_exp G1 (vars ++ st_senv x1)) (snd es)) es) as Hwces.
          { simpl_Forall. repeat solve_incl. }
          assert (Forall2Brs (sem_exp_ck G1 Hi1 b) es vs0) as Hses.
          { eapply Forall2Brs_impl_In; [|eauto]; intros ?? _ Hse.
            eapply sem_exp_refines... }
          eapply mmap2_mmap2_sem in H as (Hi2&Href2&Histst2&Hsem2&Hsem2')...

          assert (Forall (wc_exp G1 (vars ++ st_senv x4)) d0) as Hwd.
          { eapply Forall_forall; intros.
            specialize (H12 _ eq_refl). eapply Forall_forall in H12... repeat solve_incl. }
          assert (Forall2 (sem_exp_ck G1 Hi2 b) d0 vd) as Hsd.
          { simpl_Forall; eauto using sem_exp_refines. }
          eapply mmap2_sem in H0 as (Hi3&Href3&Histst3&Hsem3&Hsem3')...

          assert (Forall2 (fun e v => sem_exp_ck G2 Hi3 b e [v])
                    (unnest_case e0 x2 (Some (concat x5)) tys ck) vs) as Hsem'.
          { eapply unnest_case_sem...
            - eapply mmap2_length_1 in H3.
              destruct es, x2; simpl in *; try congruence; auto.
            - eapply mmap2_mmap2_unnest_exp_wc; eauto.
            - eapply mmap2_mmap2_unnest_exp_annots in H3. 2:simpl_Forall; eauto with lclocking.
              eapply Forall2_ignore1 in H3. simpl_Forall.
              rewrite H2, H11, length_clocksof_annots; eauto.
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
              1,2:simpl_Forall; eauto using sem_equation_refines.
          + (* exp *)
            remember (Hi3 + FEnv.of_list (combine (map (fun '(x, _) => Var x) x) vs)) as Hi4.
            assert (length vs = length x) as Hlength'.
            { eapply idents_for_anns_length in H. repeat simpl_length.
              apply Forall2Brs_length1 in H21.
              2:{ simpl_Forall; eapply sem_exp_ck_numstreams; eauto with lclocking. }
              inv H21; try congruence. inv H11; auto.
              eapply Forall3_length in H23 as (?&?). solve_length. }
            assert (FEnv.refines (@EqSt _) Hi3 Hi4) as Href4.
            { subst. eapply idents_for_anns_refines...
              destruct Histst3 as (Hdom1&_)... }
            assert (Forall2 (sem_var Hi4) (map (fun '(x, _) => Var x) x) vs) as Hvars.
            { rewrite HeqHi4. eapply sem_new_vars... 1:rewrite map_length...
              eapply idents_for_anns_NoDup; eauto. }
            exists Hi4. split;[|split;[|split]]; eauto with norm.
            * repeat (etransitivity; eauto).
            * subst. eapply idents_for_anns_hist_st...
              erewrite map_map, map_ext, <-unnest_case_clocksof with (nck:=ck); auto.
              { eapply sc_exps2; eauto. destruct Histst3; eauto.
                - eapply unnest_case_wc_exp; eauto.
                  + eapply unnest_exp_wc in Hun1 as (Hwc&_); eauto. apply Forall_singl in Hwc.
                    repeat solve_incl.
                  + eapply unnest_exp_clockof in Hun1; eauto with lclocking. simpl in Hun1; rewrite app_nil_r in Hun1.
                    congruence.
                  + eapply mmap2_length_1 in H3.
                    contradict H8; subst; destruct es; simpl in *; congruence.
                  + eapply mmap2_mmap2_unnest_exp_length in H3; eauto.
                    2:{ simpl_Forall; eauto with lclocking. }
                    eapply Forall2_ignore1 in H3. simpl_Forall.
                    rewrite H3, H11. solve_length.
                  + eapply mmap2_mmap2_unnest_exp_wc in H3 as (Hwc&_)...
                    simpl_Forall. repeat solve_incl.
                  + eapply mmap2_mmap2_unnest_exp_clocksof2; eauto.
                  + simpl. erewrite length_clocksof_annots, mmap2_unnest_exp_annots_length. 3:eauto. 2:eauto with lclocking.
                    specialize (H14 _ eq_refl). solve_length.
                  + simpl. eapply mmap2_unnest_exp_wc...
                  + simpl. eapply mmap2_unnest_exp_clocksof'''; eauto.
              }
            * clear - Hvars. simpl_Forall; eauto with lcsem.
            * repeat rewrite Forall_app; repeat split. 2-4:simpl_Forall; eauto using sem_equation_refines.
              remember (unnest_case _ _ _ _ _) as merge.
              assert (length merge = length x) as Hlength''.
              { eapply idents_for_anns_length in H.
                subst. rewrite unnest_case_length. solve_length. }
              clear - Hvars Hsem' Href4 Hlength''. apply mk_equations_Forall. simpl_Forall.
              eapply Forall2_swap_args, Forall2_trans_ex in Hsem'; [|eauto]. simpl_Forall.
              apply Seq with (ss:=[[x0]]); simpl.
              1,2:repeat constructor... eapply sem_exp_refines...

        - (* app *)
          assert (a = map snd x8) as Hanns; subst.
          { eapply idents_for_anns_values in H5... }
          specialize (idents_for_anns_length _ _ _ _ H5) as Hlength1.
          assert (length (n_out n) = length vs) as Hlength2.
          { specialize (H23 0). inv H23. rewrite H12 in H7; inv H7. apply Forall2_length in H9.
            unfold idents in *. repeat rewrite map_length in H9. auto. }
          assert (length es = length ss) as Hlength3.
          { apply Forall2_length in H19... }
          assert (length (concat x6) = length (n_in n)) as Hlength4.
          { eapply mmap2_unnest_exp_length in H2; eauto with lclocking. eapply Forall2_length in H13.
            rewrite map_length in H13. rewrite H13. subst_length. now rewrite length_nclocksof_annots. }

          assert (Hun1:=H2). eapply mmap2_sem in H2... clear H.
          destruct H2 as [H' [Href1 [Histst1 [Hsem1 Hsem1']]]].

          assert (Hun2:=H3). eapply unnest_noops_exps_sem in H3 as (H''&Href2&Histst2&Hsem2&Hsem2'); eauto.
          3:{ eapply mmap2_normalized_lexp in Hun1. 1,3:eauto with lclocking.
              apply NoLast_app; split; auto. apply senv_of_tyck_NoLast. }
          4:eapply Forall2_concat; eauto.
          2:{ unfold find_node_incks. now rewrite H12, map_length. }
          2:{ eapply mmap2_unnest_exp_wc in Hun1 as (?&?); eauto. }

          assert (length rs = length er) as Hlen3 by (eapply Forall2_length in H21; eauto).
          assert (Forall2 (fun er sr => sem_exp_ck G1 H'' b er [sr]) er rs) as Hsemr' by (simpl_Forall; eauto using sem_exp_refines).
          assert (Hun3:=H4). eapply unnest_resets_sem in H4...
          2:(simpl_Forall; repeat solve_incl).
          2:{ eapply Forall_impl; [|eapply H15]; intros ? Hck. destruct Hck as (?&Hck).
              rewrite <-length_clockof_numstreams, Hck; auto. }
          2:{ simpl_Forall. eapply H0 in H9 as (H'''&?&?&?&?); eauto. exists H'''; split;[|split;[|split]]; eauto.
              simpl_Forall; eauto. }
          destruct H4 as (H'''&Href3&Histst3&Hsem3&Hsem3').

          assert (sem_exp_ck G2 H''' b (Eapp f x2 x5 (map snd x8)) vs) as Hsem'.
          { eapply Sapp with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss)))...
            + rewrite <- concat_map.
              simpl_Forall; eauto using sem_exp_refines.
            + intros k. specialize (H23 k).
              rewrite concat_map_singl2. eapply HGref; eauto. }
          remember (H''' + FEnv.of_list (combine (map (fun '(x, _) => Var x) x8) vs)) as H''''.
          assert (length vs = length x8) as Hlen'.
          { eapply Forall2_length in H14. rewrite 2 map_length in H14. solve_length. }
          assert (FEnv.refines (@EqSt _) H''' H'''') as Href4.
          { subst. eapply idents_for_anns_refines...
            destruct Histst3 as (Hdom3&_); auto.
          }
          assert (Forall2 (sem_var H'''') (map (fun '(x, _) => Var x) x8) vs) as Hvars.
          { rewrite HeqH''''. eapply sem_new_vars... 1:rewrite map_length...
            eapply idents_for_anns_NoDup; eauto. }
          exists H''''. split;[|split;[|split]]...
          + repeat (etransitivity; eauto).
          + subst. assert (Hids:=H5). eapply idents_for_anns_hist_st in H5...
            assert (Hwc:=H10). eapply mmap2_unnest_exp_wc in H10 as (Hwc'&_); eauto.
            eapply Forall2_concat in Hsem1.
            erewrite map_ext, <-map_map.
            eapply sc_outside_mask' with (es:=es) (G:=G1); eauto.
            4:intros (?&?); auto.
            * simpl_Forall; eauto using sem_exp_refines.
            * simpl_Forall; auto.
            * eapply sc_exps in H19; eauto. 2:destruct Histst; auto.
              simpl_Forall; eauto 7 using sem_clock_refines, var_history_refines.
          + clear - Hvars. simpl_Forall; eauto with lcsem.
          + constructor; [| repeat rewrite Forall_app; repeat split].
            2-4:simpl_Forall; eauto using sem_equation_refines.
            apply Seq with (ss:=[vs]).
            * repeat constructor...
              eapply sem_exp_refines...
            * simpl. rewrite app_nil_r; simpl_Forall; auto.
      Qed.

      Corollary unnest_exps_sem : forall b es H vs es' eqs' st st',
          Forall (wc_exp G1 (vars++st_senv st)) es ->
          Forall2 (sem_exp_ck G1 H b) es vs ->
          hist_st vars b H st ->
          mmap2 (unnest_exp G1 false) es st = (es', eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars b H' st' /\
                Forall2
                  (fun (es : list exp) (vs : list (Stream svalue)) =>
                     Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es vs) es' vs /\
                Forall (sem_equation_ck G2 H' b) (concat eqs')).
      Proof.
        intros * Hwt Hsem Hhistst Hnorm.
        eapply mmap2_sem in Hnorm; eauto.
        simpl_Forall.
        eapply unnest_exp_sem in H5; eauto.
      Qed.

      Fact unnest_rhs_sem : forall b e H vs es' eqs' st st',
          wc_exp G1 (vars++st_senv st) e ->
          sem_exp_ck G1 H b e vs ->
          hist_st vars b H st ->
          unnest_rhs G1 e st = (es', eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars b H' st' /\
                (Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es' vs \/
                   exists e', (es' = [e'] /\ sem_exp_ck G2 H' b e' vs)) /\
                Forall (sem_equation_ck G2 H' b) eqs').
      Proof with eauto with norm lclocking.
        intros * Hwt Hsem Histst Hnorm.
        destruct e; try (eapply unnest_exp_sem in Hnorm as [H' [Href1 [Histst1 [Hsem1 Hsem2]]]]; eauto;
                         exists H'; repeat (split; eauto)).
        1-4:unfold unnest_rhs in Hnorm; repeat inv_bind. 4:inv Hwt; inv Hsem.
        - (* extcall *)
          inv Hwt. inv Hsem.
          unfold unnest_exps in *; repeat inv_bind.
          assert (Hnorm1:=H0). eapply unnest_exps_sem in H0...
          destruct H0 as [H' [Href1 [Histst1 [Hsem1 Hsem1']]]]. apply Forall2_concat in Hsem1.

          exists H'. repeat (split; auto).
          repeat constructor. econstructor.
          2:instantiate (1:=map (fun x => [x]) (concat ss)).
          all:try rewrite concat_map_singl1; eauto; simpl_Forall; eauto using sem_exp_refines.
          eapply mmap2_unnest_exp_typesof in Hnorm1; eauto with lclocking.
          congruence.

        - (* fby *)
          inversion_clear Hwt as [| | | | | | |??? Hwc1 Hwc2 Hl1 Hl2 | | | | |].
          inversion_clear Hsem as [| | | | | | |???????? Hsem1 Hsem2 Fby| | | | | |].
          assert (length x = length (annots l)) as Hlength1 by (eapply unnest_exps_length; eauto with lclocking).
          assert (length x2 = length (annots l0)) as Hlength2 by (eapply unnest_exps_length; eauto with lclocking).
          unfold unnest_exps in *. repeat inv_bind.

          assert (Hun1:=H0). eapply unnest_exps_sem in H0... clear Hsem1.
          destruct H0 as [H' [Href1 [Histst1 [Hsem1 Hsem1']]]]. apply Forall2_concat in Hsem1.
          assert (Forall2 (sem_exp_ck G1 H' b) l0 sss) as Hsem' by (simpl_Forall; eauto using sem_exp_refines).

          eapply unnest_exps_sem in H1... clear Hsem2.
          2:(simpl_Forall; repeat solve_incl).
          destruct H1 as [H'' [Href2 [Histst2 [Hsem2 Hsem2']]]]. apply Forall2_concat in Hsem2.
          assert (Forall2 (fun e v => sem_exp_ck G2 H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''
              by (simpl_Forall; eauto using sem_exp_refines).

          exists H''. repeat (split; auto).
          + repeat (etransitivity; eauto).
          + left. eapply unnest_fby_sem...
            * eapply Forall2_length in Hl1; solve_length.
            * eapply Forall2_length in Hl2; solve_length.
          + repeat rewrite Forall_app. repeat split...
            simpl_Forall; eauto using sem_equation_refines.

        - (* arrow *)
          inversion_clear Hwt as [| | | | | | | |??? Hwc1 Hwc2 Hl1 Hl2| | | |].
          inversion_clear Hsem as [| | | | | | | |???????? Hsem1 Hsem2 Fby| | | | |].
          assert (length x = length (annots l)) as Hlength1 by (eapply unnest_exps_length; eauto with lclocking).
          assert (length x2 = length (annots l0)) as Hlength2 by (eapply unnest_exps_length; eauto with lclocking).
          unfold unnest_exps in *. repeat inv_bind.

          assert (Hun1:=H0). eapply unnest_exps_sem in H0... clear Hsem1.
          destruct H0 as [H' [Href1 [Histst1 [Hsem1 Hsem1']]]]. apply Forall2_concat in Hsem1.
          assert (Forall2 (sem_exp_ck G1 H' b) l0 sss) as Hsem' by (simpl_Forall; eauto using sem_exp_refines).

          eapply unnest_exps_sem in H1... clear Hsem2.
          2:(simpl_Forall; repeat solve_incl).
          destruct H1 as [H'' [Href2 [Histst2 [Hsem2 Hsem2']]]]. apply Forall2_concat in Hsem2.
          assert (Forall2 (fun e v => sem_exp_ck G2 H'' b e [v]) (concat x2) (concat s0ss)) as Hsem''
              by (simpl_Forall; eauto using sem_exp_refines).

          exists H''. repeat (split; auto).
          + repeat (etransitivity; eauto).
          + left. eapply unnest_arrow_sem...
            * eapply Forall2_length in Hl1; solve_length.
            * eapply Forall2_length in Hl2; solve_length.
          + repeat rewrite Forall_app. repeat split...
            simpl_Forall; eauto using sem_equation_refines.

        - (* app *)
          unfold unnest_exps in H0.
          repeat inv_bind.
          assert (length (concat x6) = length (n_in n)) as Hlength4.
          { eapply mmap2_unnest_exp_length in H0; eauto with lclocking.
            eapply Forall2_length in H10. rewrite map_length in H10. solve_length.
            now rewrite length_nclocksof_annots. }

          assert (Hun1:=H0). eapply unnest_exps_sem in H0...
          destruct H0 as [H' [Href1 [Histst1 [Hsem1 Hsem1']]]].

          assert (Hun2:=H1). eapply unnest_noops_exps_sem in H1 as (H''&Href2&Histst2&Hsem2&Hsem2'); eauto.
          3:{ eapply mmap2_normalized_lexp in Hun1. 1,3:eauto with lclocking.
              apply NoLast_app; split; auto. apply senv_of_tyck_NoLast. }
          4:eapply Forall2_concat...
          2:{ unfold find_node_incks. rewrite H9, map_length; auto. }
          2:{ eapply mmap2_unnest_exp_wc. 1,2,4:eauto. simpl_Forall; repeat solve_incl. }

          assert (length rs = length l0) as Hlen3 by (eapply Forall2_length in H18; eauto).
          assert (Forall2 (fun er sr => sem_exp_ck G1 H'' b er [sr]) l0 rs) as Hsemr'
              by (simpl_Forall; eauto using sem_exp_refines).
          assert (Hr:=H2). eapply unnest_resets_sem in H2...
          2:(simpl_Forall; repeat solve_incl).
          2:{ simpl_Forall.
              now rewrite <-length_clockof_numstreams, H1. }
          2:{ simpl_Forall. eapply unnest_exp_sem in H14 as (H'''&?&?&Sem1&?)... inv Sem1... }
          destruct H2 as (H'''&Href3&Hhistst3&Hsem3&Hsem3').

          exists H'''. repeat (split; auto).
          + repeat (etransitivity; eauto).
          + right. eexists; split...
            apply Sapp with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))) (rs:=rs) (bs:=bs); eauto.
            * rewrite <- concat_map, Forall2_map_2; auto.
              simpl_Forall; eauto using sem_exp_refines.
            * rewrite concat_map_singl2. intros k. eapply HGref, H20; eauto.
          + repeat rewrite Forall_app.
            repeat split; simpl_Forall; eauto using sem_equation_refines.
      Qed.

      Corollary mmap2_unnest_rhs_sem : forall b es H vs es' eqs' st st',
          Forall (wc_exp G1 (vars++st_senv st)) es ->
          Forall2 (sem_exp_ck G1 H b) es vs ->
          hist_st vars b H st ->
          mmap2 (unnest_rhs G1) es st = (es', eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars b H' st' /\
                Forall2 (fun es' vs =>
                           Forall2 (fun e v => sem_exp_ck G2 H' b e [v]) es' vs \/
                             exists e', (es' = [e'] /\ sem_exp_ck G2 H' b e' vs)) es' vs /\
                Forall (sem_equation_ck G2 H' b) (concat eqs')).
      Proof with eauto.
        induction es; intros * Hwt Hsem Histst Hmap;
          repeat inv_bind.
        - exists H; simpl. inv Hsem. repeat (split; auto). reflexivity.
        - inv Hwt. inv Hsem.

          assert (st_follows st x1) as Hfollows1 by eauto with norm.
          eapply unnest_rhs_sem in H0...
          destruct H0 as [H' [Href1 [Histst1 [Hsem1 Hsem1']]]].
          assert (Forall2 (sem_exp_ck G1 H' b) es l') as Hsem' by (simpl_Forall; eauto using sem_exp_refines).

          eapply IHes in H1... clear IHes.
          2:(simpl_Forall; repeat solve_incl).
          destruct H1 as [H'' [Href2 [Histst2 [Hsem2 Hsem2']]]].
          exists H''. repeat (split; eauto).
          + etransitivity...
          + constructor...
            destruct Hsem1.
            * left. simpl_Forall; eauto using sem_exp_refines.
            * right. destruct H0 as [e' [? H0]]; subst.
              exists e'. split... eapply sem_exp_refines...
          + apply Forall_app. split...
            simpl_Forall; eauto using sem_equation_refines.
      Qed.

      Corollary unnest_rhss_sem : forall b es H vs es' eqs' st st',
          Forall (wc_exp G1 (vars++st_senv st)) es ->
          Forall2 (sem_exp_ck G1 H b) es vs ->
          hist_st vars b H st ->
          unnest_rhss G1 es st = (es', eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars b H' st' /\
                Forall (fun '(e, v) => sem_exp_ck G2 H' b e v)
                  (combine_for_numstreams es' (concat vs)) /\
                Forall (sem_equation_ck G2 H' b) eqs').
      Proof with eauto with lclocking.
        intros * Hwt Hsem Histst Hnorm.
        assert (Forall (wc_exp G2 (vars++st_senv st')) es') as Hwt'.
        { eapply unnest_rhss_wc in Hnorm as [? ?]... }
        unfold unnest_rhss in *.
        repeat inv_bind.
        eapply mmap2_unnest_rhs_sem in H0...
        destruct H0 as [H' [Href1 [Histst1 [Hsem1 Hsem1']]]].
        exists H'. repeat (split; eauto).
        clear Hsem. induction Hsem1; simpl...
        simpl. destruct H0.
        - induction H0; simpl in *...
          inv Hwt'.
          assert (numstreams x = 1) as Hnumstreams.
          { eapply sem_exp_ck_numstreams in H0... }
          constructor.
          + rewrite Hnumstreams; simpl...
          + rewrite Hnumstreams; simpl...
        - destruct H0 as [? [? H0]]; subst; simpl in *.
          inv Hwt'.
          assert (numstreams x1 = length y) as Hnumstreams.
          { eapply sem_exp_ck_numstreams in H0... }
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
        - apply Nat.succ_lt_mono in Hn.
          eapply IHes in Hn. 4,5,6:eauto.
          + destruct Hn as [n' [Hlen' [Hnth1' Hnth2']]].
            exists (n'+(numstreams a))%nat.
            repeat split.
            * rewrite skipn_length in Hlen'. lia.
            * rewrite nth_skipn in Hnth1'...
            * rewrite nth_skipn in Hnth2'...
          + rewrite skipn_length. lia.
          + rewrite skipn_length. lia.
      Qed.

      Fact unnest_equation_sem : forall H b equ eqs' st st',
          wc_equation G1 (vars++st_senv st) equ ->
          sem_equation_ck G1 H b equ ->
          hist_st vars b H st ->
          unnest_equation G1 equ st = (eqs', st') ->
          (exists H', FEnv.refines (@EqSt _) H H' /\
                   hist_st vars b H' st' /\
                   Forall (sem_equation_ck G2 H' b) eqs').
      Proof with eauto with norm lclocking.
        intros * Hwt Hsem Histst Hnorm.
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
          destruct H0 as [H' [Href1 [Histst1 [Hsem1 Hsem1']]]].

          assert (Hun2:=H1). eapply unnest_noops_exps_sem in H1 as (H''&Href2&Histst2&Hsem2&Hsem2'); eauto.
          3:{ eapply mmap2_normalized_lexp in Hun1. 1,3:eauto with lclocking.
              apply NoLast_app; split; auto. apply senv_of_tyck_NoLast. }
          4:eapply Forall2_concat...
          2:{ unfold find_node_incks. rewrite H4, map_length; auto. }
          2:{ eapply mmap2_unnest_exp_wc. 1,2,4:eauto. simpl_Forall; repeat solve_incl. }

          assert (length rs = length er) as Hlen3 by (eapply Forall2_length in H21; eauto).
          assert (Forall2 (fun er sr => sem_exp_ck G1 H'' b er [sr]) er rs) as Hsemr'
              by (simpl_Forall; repeat (eapply sem_exp_refines; eauto)).
          assert (Hr:=H9). eapply unnest_resets_sem in H9...
          2:(simpl_Forall; repeat solve_incl).
          2:{ simpl_Forall.
              now rewrite <-length_clockof_numstreams, H1. }
          2:{ simpl_Forall. eapply unnest_exp_sem in H16 as (H'''&?&?&Sem1&?)... inv Sem1... }
          destruct H9 as (H'''&Href3&Hhistst3&Hsem3&Hsem3').

          exists H'''. repeat (split; auto). 2:constructor.
          + repeat (etransitivity; eauto).
          + econstructor. econstructor; eauto.
            apply Sapp with (ss:=(concat (List.map (fun x => List.map (fun x => [x]) x) ss))) (rs:=rs) (bs:=bs); eauto.
            * rewrite <- concat_map, Forall2_map_2; auto.
              simpl_Forall. repeat (eapply sem_exp_refines; eauto).
            * rewrite concat_map_singl2. intros k. eapply HGref, H23; eauto.
            * simpl; rewrite app_nil_r. rewrite firstn_all2; [|rewrite Hlen; reflexivity].
              simpl_Forall; eauto using sem_var_refines.
          + rewrite skipn_all2; [|rewrite Hlen; reflexivity]; simpl.
            repeat rewrite Forall_app.
            repeat split; simpl_Forall; eauto using sem_equation_refines.

        - (* general case *)
          repeat inv_bind.
          assert (annots x = annots es) as Hannots by (eapply unnest_rhss_annots; eauto with lclocking).
          assert (Hun:=H2). eapply unnest_rhss_sem in H0 as (H'&Href1&Histst1&Hsem1&Hsem1')...
          exists H'. repeat (split; eauto).
          apply Forall_app. split...
          clear Hsem1'.
          assert (length (concat ss) = length (annots es)) as Hlen1.
          { eapply sem_exps_ck_numstreams in H7; eauto with lclocking. }
          assert (length xs = length (annots x)) as Hlen2.
          { rewrite Hannots, <-Hlen1.
            rewrite_Forall_forall. simpl_length. congruence. }
          rewrite_Forall_forall.
          simpl_In. assert (HIn:=Hin).
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

      Lemma hist_st_mask {pref} : forall vars bs H (st: fresh_st pref _) r k,
          hist_st vars bs H st ->
          hist_st vars (maskb k r bs) (mask_hist k r H) st.
      Proof.
        intros * (?&?).
        split.
        - eapply dom_map; eauto.
        - eapply LCS.sc_vars_mask; eauto.
      Qed.

      Lemma hist_st_unmask {pref} : forall vars bs H (st: fresh_st pref _) r,
          (forall k, hist_st vars (maskb k r bs) (mask_hist k r H) st) ->
          hist_st vars bs H st.
      Proof.
        intros * Hk.
        constructor.
        - eapply dom_map. eapply (Hk 0).
        - eapply sc_vars_unmask. intros. eapply Hk.
      Qed.

      Fact mmap_unnest_block_sem : forall b blocks H blocks' st st',
          Forall
            (fun d : block => forall H b blocks' st st',
                 wc_block G1 (vars ++ st_senv st) d ->
                 sem_block_ck G1 H b d ->
                 hist_st vars b H st ->
                 unnest_block G1 d st = (blocks', st') ->
                 exists H' : FEnv.t (Stream svalue),
                   FEnv.refines (EqSt (A:=svalue)) H H' /\
                     hist_st vars b H' st' /\
                     Forall (sem_block_ck G2 H' b) blocks') blocks ->
          Forall (wc_block G1 (vars ++ st_senv st)) blocks ->
          Forall (sem_block_ck G1 H b) blocks ->
          hist_st vars b H st ->
          mmap (unnest_block G1) blocks st = (blocks', st') ->
          (exists H', FEnv.refines (@EqSt _) H H' /\
                   hist_st vars b H' st' /\
                   Forall (sem_block_ck G2 H' b) (concat blocks')).
      Proof with eauto.
        induction blocks; intros * Hf Hwc Hsem Histst Hnorm;
          inv Hf; inv Hwc; inv Hsem; repeat inv_bind; simpl.
        - exists H. repeat (split; auto). reflexivity.
        - assert (Forall (wc_block G1 (vars ++ st_senv x0)) blocks) as Hwc'.
          { simpl_Forall. repeat solve_incl. }
          eapply H2 in H0 as (H'&Href1&Histst1&Hsem1)...
          assert (Forall (sem_block_ck G1 H' b) blocks) by (simpl_Forall; eapply sem_block_refines; eauto).

          eapply IHblocks in H1 as (H''&Href2&Histst2&Hsem2)...
          exists H''. split;[|split]...
          + etransitivity...
          + eapply Forall_app. split...
            simpl_Forall. eapply sem_block_refines...
      Qed.

      Lemma unnest_block_sem : forall d H b blocks' st st',
          wc_block G1 (vars++st_senv st) d ->
          sem_block_ck G1 H b d ->
          hist_st vars b H st ->
          unnest_block G1 d st = (blocks', st') ->
          (exists H', FEnv.refines (@EqSt _) H H' /\
                   hist_st vars b H' st' /\
                   Forall (sem_block_ck G2 H' b) blocks').
      Proof with eauto.
        induction d using block_ind2; intros * Hwc Hsem Histst Hnorm;
          inv Hwc; inv Hsem; repeat inv_bind.
        - (* Equation *)
          eapply unnest_equation_sem in H0 as (H'&?&?&?); eauto.
          exists H'. split;[|split]; auto.
          simpl_Forall.
          constructor; auto.
        - exists H. repeat (split; auto). reflexivity.
          constructor; eauto. eapply sem_ref_sem_block; eauto. econstructor; eauto.
        - (* Reset *)
          assert (forall k, exists H',
                     FEnv.refines (@EqSt _) (CStr.mask_hist k r H0) (CStr.mask_hist k r H') /\
                       hist_st vars (maskb k r b) (mask_hist k r H') x0 /\
                       Forall (sem_block_ck G2 (mask_hist k r H') (maskb k r b)) (concat x)) as Hbck.
          { intros k. specialize (H11 k).
            eapply mmap_unnest_block_sem in H1 as (H'&Href1&Histst1&Hsem1); eauto.
            2:apply hist_st_mask...
            destruct Histst1 as (Hdom1&Hsc1).
            assert (FEnv.Equiv (@EqSt _) H' (CStr.mask_hist k r H')) as Heqmask.
            { unfold st_ids in Hdom1.
              eapply slower_mask_hist. eapply sc_vars_slower_hist in Hsc1; eauto using dom_dom_ub. }
            exists H'. split; [|split; [split|]]; intros.
            1:rewrite <-Heqmask; auto.
            - now apply dom_map.
            - unfold mask_hist. simpl. eapply sc_vars_morph. 1,3,4:eauto; reflexivity.
              apply Heqmask.
            - simpl_Forall. eapply sem_block_ck_morph; eauto. reflexivity.
          }
          eapply consolidate_mask_hist
            with (P := fun k H'k => FEnv.refines (@EqSt _) (CStr.mask_hist k r H0) H'k /\
                                   hist_st vars (maskb k r b) H'k x0 /\
                                   Forall (sem_block_ck G2 H'k (maskb k r b)) (concat x))
            in Hbck as (H'&HH').
          2:{ intros ????? Heq (?&(?&Hsc1)&?); subst. split; [|split; [split|]]; intros; auto.
              2:split; intros ?. 1-3:rewrite <-Heq; auto.
              1,2:eapply H9; eauto.
              - eapply sc_vars_morph; eauto. reflexivity.
              - simpl_Forall. eapply sem_block_ck_morph; eauto. reflexivity.
          }
          2:{ intros ?? (_&(Hdom1&_)&_); simpl. eapply dom_fenv_dom; eauto. }
          assert (FEnv.refines (@EqSt _) H0 H') as Href1.
          { eapply refines_unmask; intros. eapply HH'. }
          eapply unnest_reset_sem with (H:=H') in H2 as (H''&Href2&Histst2&Hsem2&Hsem2')...
          3:(simpl_Forall; repeat solve_incl).
          3:now rewrite <-length_clockof_numstreams, H6.
          3:(eapply sem_exp_refines; eauto).
          3:{ eapply hist_st_unmask; intros. eapply HH'; eauto. }
          2:{ intros * Hun. eapply unnest_exp_sem with (H:=H') (vs:=[sr]) in Hun as (H''&Href'&Histst'&Hsem'&Hsem''); eauto.
              exists H''. split;[|split;[|split]]; eauto.
              inv Hsem'; auto.
              repeat solve_incl.
              eapply sem_exp_refines; eauto.
              eapply hist_st_unmask; intros. eapply HH'; eauto.
          }
          exists H''. split;[|split]; eauto.
          + etransitivity...
          + apply Forall_app. split; simpl_Forall.
            * econstructor; eauto.
              intros k. constructor; auto.
              specialize (HH' k) as (_&_&Hsem'). simpl_Forall.
              eapply sem_block_refines; [|eauto]. eapply refines_mask; eauto.
            * constructor; auto.
        - exists H0. repeat (split; auto). reflexivity.
          constructor; eauto. eapply sem_ref_sem_block; eauto. econstructor; eauto.
        - exists H0. repeat (split; auto). reflexivity.
          constructor; eauto. eapply sem_ref_sem_block; eauto. econstructor; eauto.
        - exists H0. repeat (split; auto). reflexivity.
          constructor; eauto. eapply sem_ref_sem_block; eauto. econstructor; eauto.
        - exists H0. repeat (split; auto). reflexivity.
          constructor; eauto. eapply sem_ref_sem_block; eauto. econstructor; eauto.
      Qed.

      Corollary unnest_blocks_sem : forall b blocks H blocks' st st',
          Forall (wc_block G1 (vars ++ st_senv st)) blocks ->
          Forall (sem_block_ck G1 H b) blocks ->
          hist_st vars b H st ->
          unnest_blocks G1 blocks st = (blocks', st') ->
          (exists H', FEnv.refines (@EqSt _) H H' /\
                   hist_st vars b H' st' /\
                   Forall (sem_block_ck G2 H' b) blocks').
      Proof with eauto.
        intros * Hwc Hsem Histst Hnorm.
        unfold unnest_blocks in Hnorm. repeat inv_bind.
        eapply mmap_unnest_block_sem in H0; eauto.
        simpl_Forall.
        eapply unnest_block_sem in H6; eauto.
      Qed.

    End unnest_block_sem.

    (** *** Preservation of sem_node *)

    Lemma unnest_node_sem : forall f n ins outs,
        wc_global (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        Ordered_nodes (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(types) G2.(externs) ((unnest_node G1 n)::G2.(nodes))) ->
        sem_node_ck (Global G1.(types) G1.(externs) (n::G1.(nodes))) f ins outs ->
        sem_node_ck (Global G2.(types) G2.(externs) ((unnest_node G1 n)::G2.(nodes))) f ins outs.
    Proof with eauto.
      intros * HwcG Hord1 Hord2 Hsem.

      inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
      - erewrite find_node_now in Hfind; eauto. inv Hfind.
        (*The semantics of equations can be given according to G only *)
        assert (~Is_node_in_block (n_name n0) (n_block n0)) as Blk.
        { inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }
        eapply sem_block_ck_cons1 in Blk; eauto. clear H3.

        inv HwcG. take (_ /\ _) and destruct it as (Hwc&_). simpl in *.
        replace {| types := types G1; nodes := nodes G1 |} with G1 in Blk, Hwc by (destruct G1; auto).
        remember (unnest_node G1 n0) as n'.
        unfold unnest_node in Heqn'; inv Heqn'.
        specialize (n_nodup n0) as (Hnd1&Hnd2).
        pose proof (n_good n0) as (Hgood1&Hgood2&_).
        pose proof (n_syn n0) as Hsyn. inversion_clear Hsyn as [?? Hsyn1 Hsyn2 _]. inv Hsyn2.
        rewrite <-H0 in *. inv Blk. inv_scope.
        simpl in *. repeat rewrite app_nil_r in *.
        inversion_clear Hwc as [? _ _ Hwc']. rewrite <-H0 in Hwc'. inv Hwc'.
        assert (forall x, ~ IsLast (senv_of_ins (n_in n0) ++ senv_of_decls (n_out n0) ++ senv_of_decls locs) x) as Hnl.
        { repeat rewrite NoLast_app; repeat split; auto using senv_of_ins_NoLast.
          - intros * Hl. inv Hl. simpl_In. simpl_Forall. subst; simpl in *; congruence.
          - intros * Hl. inv Hl. simpl_In. simpl_Forall. subst; simpl in *; congruence. }
        repeat inv_scope'. subst Γ'.
        assert (Forall (sem_block_ck G1 (H + Hi') (clocks_of ins)) blks) as Hsem by auto.

        eapply unnest_blocks_sem with (vars:=senv_of_ins (n_in n0) ++ senv_of_decls (n_out n0) ++ senv_of_decls locs)
          in Hsem as (Hf&Href&(Hdom&Hsc)&Hsem); eauto. 5:eapply surjective_pairing.
        2:{ inv Hgood2. take (GoodLocalsScope _ _ _) and inv it.
            rewrite app_assoc. apply Forall_app; split; simpl_Forall; simpl_In; simpl_Forall; auto.
            eapply Forall_forall in Hgood1; eauto. rewrite <-map_fst_senv_of_ins, <-map_fst_senv_of_decls, <-map_app. solve_In. }
        2:{ unfold st_senv. now rewrite init_st_anns, app_nil_r, app_assoc. }
        2:{ take (clocked_node _ _ _) and destruct it as (Hdom&Hsc).
            constructor; simpl.
            * unfold st_senv. rewrite init_st_anns, app_nil_r, app_assoc.
              apply local_hist_dom; auto.
            * unfold st_senv. rewrite init_st_anns, app_nil_r, app_assoc.
              eapply local_hist_sc_vars with (H:=H); eauto using dom_dom_ub. reflexivity.
              inv Hnd2. take (NoDupScope _ _ _) and inv it.
              intros ?? contra; rewrite IsVar_fst, map_app, map_fst_senv_of_ins, map_fst_senv_of_decls in contra. eapply H16; eauto.
        }
        assert (Href':=Href). eapply FEnv.union_refines_inv in Href' as (Hi''&Heq&Href'&Hdom'); auto using EqStrel_Reflexive.
        2:{ intros * Hin Hin2. destruct x; apply H4 in Hin; apply H9 in Hin2.
            2:{ inv Hin2. simpl_In. simpl_Forall. subst; simpl in *; congruence. }
            inv Hnd2. take (NoDupScope _ _ _) and inv it.
            take (forall x, InMembers x locs -> ~ _) and eapply it.
            + eapply IsVar_senv_of_decls; eauto.
            + now rewrite IsVar_fst, map_app, map_fst_senv_of_ins, map_fst_senv_of_decls in Hin. }

        eapply Snode with (H:=H); simpl; eauto.
        + erewrite find_node_now; eauto.
        + assumption.
        + assumption.
        + apply sem_block_ck_cons2; simpl...
          2:{ eapply find_node_not_Is_node_in in Hord2.
              2:erewrite find_node_now; eauto. auto. }
          rewrite <-H0.
          do 2 econstructor.
          3:destruct G2; simpl_Forall; rewrite Heq; eauto.
          *{ destruct Hdom as (D1&DL1). destruct H4 as ((D2&DL2)&_).
             split; intros *; simpl in *.
             - rewrite Hdom', D1, D2. setoid_rewrite senv_of_decls_app. rewrite <-st_senv_senv_of_decls.
               repeat rewrite IsVar_app.
               split; [intros ([[In|[In|In]]|In]&Hnin)|intros [In|In]]; try congruence; auto.
               + exfalso. eapply Hnin; eauto.
               + exfalso. eapply Hnin; eauto.
               + split; auto. intros contra.
                 inv Hnd2. take (NoDupScope _ _ _) and inv it.
                 eapply H16; eauto. eapply IsVar_senv_of_decls; eauto.
                 now rewrite 2 IsVar_fst, map_fst_senv_of_ins, map_fst_senv_of_decls, <-in_app_iff in contra.
               + split; auto.
                 intros contra. rewrite 2 IsVar_fst, map_fst_senv_of_ins, map_fst_senv_of_decls, <-in_app_iff in contra.
                 inv In. simpl_In. simpl_Forall.
                 eapply Facts.st_valid_AtomOrGensym_nIn; eauto using norm1_not_in_local_prefs.
                 unfold st_ids. solve_In.
             - rewrite Hdom', DL1, DL2. setoid_rewrite senv_of_decls_app. rewrite <-st_senv_senv_of_decls.
               repeat rewrite IsLast_app.
               split; [intros ([[In|[In|In]]|In]&Hnin)|intros [In|In]]; try congruence; auto.
               + exfalso. eapply Hnin; eauto.
               + exfalso. eapply Hnin; eauto.
               + inv In. simpl_In. simpl_Forall. subst; simpl in *; congruence.
               + inv In. simpl_In. congruence.
           }
          * eapply sc_vars_morph, sc_vars_incl; [reflexivity| |reflexivity| |eauto].
            now symmetry. setoid_rewrite senv_of_decls_app. rewrite <-st_senv_senv_of_decls.
            solve_incl_app.
        + simpl. now subst bs.
      - erewrite find_node_other in Hfind; eauto.
        eapply sem_node_ck_cons2...
        destruct G2; apply HGref.
        destruct G1; econstructor...
        eapply sem_block_ck_cons1; eauto.
        eapply find_node_later_not_Is_node_in in Hord1...
    Qed.

  End unnest_node_sem.

  Local Hint Resolve wc_global_Ordered_nodes : norm.

  Lemma unnest_global_refines : forall G,
      wc_global G ->
      global_sem_refines G (unnest_global G).
  Proof with eauto with norm.
    intros [].
    induction nodes0; intros * Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      eapply unnest_global_wc, wc_global_Ordered_nodes in Hwc' ;
        unfold unnest_global in Hwc'; simpl in Hwc'.
      apply global_sem_ref_cons with (f:=n_name a)...
      + inv Hwc. eapply IHnodes0...
      + intros ins outs Hsem; simpl in *.
        change types0 with ((Global types0 externs0 (unnest_nodes types0 externs0 nodes0)).(types)).
        eapply unnest_node_sem...
        * inv Hwc; eauto.
        * change (Global types0 externs0 (unnest_nodes types0 externs0 nodes0))
            with (unnest_global (Global types0 externs0 nodes0)).
          eapply unnest_global_wc. inv Hwc; auto.
        * apply iface_eq_iface_incl, unnest_nodes_eq.
        * inv Hwc. eapply IHnodes0...
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
    Variable G1 : @global nolocal norm1_prefs.
    Variable G2 : @global nolocal norm2_prefs.

    Hypothesis Hiface : global_iface_incl G1 G2.
    Hypothesis HGref : global_sem_refines G1 G2.

    Hypothesis HwcG1 : wc_global G1.

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

    Section normfby_block_sem.

      Variable vars : static_env.

      Hypothesis Atoms : Forall (fun '(x, _) => AtomOrGensym norm1_prefs x) vars.
      Hypothesis NoLast : forall x, ~IsLast vars x.

      Import NormFby.

      Fact fresh_ident_refines2 : forall hint H a id (v : Stream svalue) (st st' : fresh_st norm2 _),
          dom H (vars++st_senv st) ->
          fresh_ident hint a st = (id, st') ->
          FEnv.refines (@EqSt _) H (FEnv.add (Var id) v H).
      Proof.
        intros.
        eapply fresh_ident_refines with (vars:=vars); eauto using norm2_not_in_norm1_prefs.
        simpl_Forall; auto.
      Qed.

      Fact fresh_ident_hist_st2 : forall hint b ty ck id v H (st st': fresh_st norm2 _),
          sem_clock (var_history H) b ck (abstract_clock v) ->
          fresh_ident hint (ty, ck) st = (id, st') ->
          hist_st vars b H st ->
          hist_st vars b (FEnv.add (Var id) v H) st'.
      Proof.
        intros.
        eapply fresh_ident_hist_st; eauto using norm2_not_in_norm1_prefs.
      Qed.

      Fact init_var_for_clock_sem : forall bs H ck bs' x eqs' st st',
          sem_clock (var_history H) bs ck bs' ->
          hist_st vars bs H st ->
          init_var_for_clock ck st = (x, eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars bs H' st' /\
                sem_var H' (Var x) (init_stream bs') /\
                Forall (sem_equation_ck G2 H' bs) eqs').
      Proof with eauto.
        intros * Hsemc Histst Hinit.
        unfold init_var_for_clock in Hinit.
        destruct (fresh_ident _ _) eqn:Hident. repeat inv_bind.
        remember (FEnv.add (Var x) (init_stream bs' (* rs' *)) H) as H'.
        assert (H ⊑ H') as Href1.
        { subst. eapply fresh_ident_refines2 in Hident; eauto.
          now destruct Histst. }
        assert (hist_st vars bs H' st') as Histst1.
        { subst. eapply fresh_ident_hist_st2 in Hident...
          destruct Histst as (Hdom&Hsc).
          now rewrite init_stream_ac. }
        exists H'. repeat (split; eauto).
        + rewrite HeqH'. econstructor. 2:reflexivity.
          apply FEnv.gss.
        + repeat constructor.
          apply Seq with (ss:=[[(init_stream bs' (* rs' *))]]); simpl; repeat constructor.
          * econstructor; repeat constructor.
            1,2:apply add_whens_enum_sem; eauto using sem_clock_refines, var_history_refines.
            repeat constructor. unfold init_stream.
            repeat rewrite const_val_const; subst.
            do 2 rewrite const_val_enum. apply sfby_fby; simpl; eauto.
            rewrite <- const_val_enum. apply enum_aligned.
          * econstructor. 2:reflexivity.
            rewrite HeqH'. apply FEnv.gss.
      Qed.

      Hint Constructors Forall3 : datatypes.

      Fact fby_iteexp_sem : forall bs H e0 e ty nck y0 y z e' eqs' st st' ,
          normalized_lexp e0 ->
          clockof e0 = [nck] ->
          wc_exp G1 (vars++st_senv st) e0 ->
          wc_exp G1 (vars++st_senv st) e ->
          sem_exp_ck G1 H bs e0 [y0] ->
          sem_exp_ck G1 H bs e [y] ->
          fby y0 y z ->
          hist_st vars bs H st ->
          fby_iteexp e0 e (ty, nck) st = (e', eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars bs H' st' /\
                sem_exp_ck G2 H' bs e' [z] /\
                Forall (sem_equation_ck G2 H' bs) eqs').
      Proof with eauto.
        intros * Hnormed Hck Hwc0 Hwc Hsem0 Hsem Hfby Histst Hiteexp.
        assert (st_follows st st') as Hfollows by (eapply fby_iteexp_st_follows; eauto).
        unfold fby_iteexp in Hiteexp; repeat inv_bind.
        assert (Hsck:=Hsem0). eapply sc_exp with (Γ:=vars++st_senv st) in Hsck... simpl in Hsck.
        2:(destruct Histst; auto).
        rewrite Hck in Hsck. eapply Forall2_singl in Hsck.

        eapply init_var_for_clock_sem in H0 as [H' [Href1 [Histst1 [Hsem1 Hsem1']]]]...
        remember (abstract_clock y0) as bs'.
        remember (match ty with
                  | Tprimitive cty => Vscalar (Op.sem_cconst (Op.init_ctype cty))
                  | Tenum _ n => Venum 0 end) as v0.
        remember (sfby v0 y) as y'.
        remember (FEnv.add (Var x2) y' H') as H''.
        assert (FEnv.refines (@EqSt _) H' H'') by (subst; destruct Histst1; eapply fresh_ident_refines2 in H1; eauto).
        assert (hist_st vars bs H'' st') as Histst2.
        { subst. eapply fresh_ident_hist_st2...
          rewrite ac_sfby.
          rewrite ac_fby2, <- ac_fby1; eauto using sem_clock_refines, var_history_refines. }
        exists H''. repeat (split; eauto with fresh norm); try constructor.
        - etransitivity; eauto.
        - eapply ScaseTotal with (s:=(init_stream bs')) (vs:=[[(1, y0);(0, y')]]).
          + econstructor. eapply sem_var_refines...
          + econstructor. 2:econstructor. 3:econstructor.
            1,2:constructor; eauto.
            4,5:simpl; rewrite app_nil_r; econstructor; eauto with datatypes.
            * eapply sem_exp_refines; [|eauto using sem_ref_sem_exp].
              etransitivity; eauto.
            * subst. do 2 econstructor; eauto. eapply FEnv.gss. reflexivity.
            * simpl. constructor; auto.
          + constructor; auto with datatypes. subst.
            eapply fby_init_stream_case; eauto using ac_aligned.
        - apply Seq with (ss:=[[y']]); repeat constructor.
          + eapply Sfby with (s0ss:=[[const_val bs' v0]]) (sss:=[[y]]); repeat constructor.
            * destruct ty as [|]; simpl; rewrite Heqv0; subst.
              -- eapply sem_exp_ck_morph; eauto. 1,2:reflexivity.
                 econstructor; eauto. eapply const_val_const.
                 eapply add_whens_const_sem; eauto using sem_clock_refines, var_history_refines.
              -- eapply sem_exp_ck_morph; eauto. 1,2:reflexivity.
                 econstructor; eauto. eapply const_val_enum.
                 eapply add_whens_enum_sem; eauto using sem_clock_refines, var_history_refines.
            * eapply sem_ref_sem_exp; eauto using sem_exp_refines.
            (* * eapply bools_ofs_empty. *)
            * rewrite Heqy'.
              eapply sfby_fby.
              eapply fby_aligned in Hfby as [_ [? _]]; eauto.
              left. rewrite Heqbs'. apply ac_aligned.
          + econstructor.
            rewrite HeqH''. apply FEnv.gss. reflexivity.
        - simpl_Forall; eauto using sem_equation_refines.
      Qed.

      Fact arrow_iteexp_sem : forall bs H e0 e ty nck y0 y z e' eqs' st st',
          normalized_lexp e0 ->
          clockof e0 = [nck] ->
          wc_exp G1 (vars++st_senv st) e0 ->
          wc_exp G1 (vars++st_senv st) e ->
          sem_exp_ck G1 H bs e0 [y0] ->
          sem_exp_ck G1 H bs e [y] ->
          arrow y0 y z ->
          hist_st vars bs H st ->
          arrow_iteexp e0 e (ty, nck) st = (e', eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars bs H' st' /\
                sem_exp_ck G2 H' bs e' [z] /\
                Forall (sem_equation_ck G2 H' bs) eqs').
      Proof with eauto.
        intros * Hnormed Hck Hwc0 Hwc1 Hsem0 Hsem Harrow Histst Hiteexp.
        assert (st_follows st st') as Hfollows by (eapply arrow_iteexp_st_follows; eauto).
        unfold arrow_iteexp in Hiteexp. repeat inv_bind.
        assert (Hsck:=Hsem0). eapply sc_exp with (Γ:=vars++st_senv st) in Hsck... simpl in Hsck.
        2:(destruct Histst; auto).
        rewrite Hck in Hsck. eapply Forall2_singl in Hsck.

        eapply init_var_for_clock_sem in H0 as [H' [Href1 [Histst1 [Hsem1 Hsem1']]]]...
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

      Fact normfby_equation_sem : forall bs H to_cut equ eqs' st st' ,
          unnested_equation G1 equ ->
          wc_equation G1 (vars++st_senv st) equ ->
          sem_equation_ck G1 H bs equ ->
          hist_st vars bs H st ->
          normfby_equation to_cut equ st = (eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars bs H' st' /\
                Forall (sem_equation_ck G2 H' bs) eqs').
      Proof with eauto.
        intros * Hun Hwc Hsem Histst Hfby.
        inv_normfby_equation Hfby to_cut equ; try destruct x2 as (ty&ck).
        - (* constant fby *)
          destruct PS.mem; repeat inv_bind.
          + inv Hsem. inv H6; inv H5.
            simpl in H7; rewrite app_nil_r in H7. inv H7; inv H6.
            assert (Hsem':=H3). inversion_clear H3 as [| | | | | | |???????? Hsem0 Hsem1 Hsem| | | | | |].
            inv Hsem0; inv H6. inv Hsem1; inv H7.
            simpl in Hsem; repeat rewrite app_nil_r in Hsem. inv Hsem; inv H9.
            inv Hwc. rename H6 into Hwc. apply Forall_singl in Hwc. assert (Hwc':=Hwc). inv Hwc'.
            simpl in *. simpl_Forall. rewrite app_nil_r in *.

            remember (FEnv.add (Var x2) y0 H) as H'.
            assert (FEnv.refines (@EqSt _) H H') as Href.
            { subst. destruct Histst as [Hdom _].
              eapply fresh_ident_refines2 in H0... }
            assert (hist_st vars bs H' st') as Histst1.
            { subst. eapply fresh_ident_hist_st2 in H0...
              inv Hun. 2:inv H2; inv H1.
              eapply sc_exp in H3... 2:destruct Histst; auto.
              simpl in H3; rewrite <-H7 in H3. simpl_Forall.
              apply ac_fby1 in H8. now rewrite <-H8.
            }
            exists H'. repeat (split; eauto with norm fresh).
            repeat constructor; auto.
            * eapply Seq with (ss:=[[y0]]); simpl; repeat constructor.
              2:eapply sem_var_refines; eauto.
              rewrite HeqH'. econstructor. eapply FEnv.gss. reflexivity.
            * eapply Seq with (ss:=[[y0]]); simpl; repeat constructor.
              -- eapply sem_ref_sem_exp... eapply sem_exp_refines...
              -- rewrite HeqH'. econstructor. eapply FEnv.gss. reflexivity.
          + exists H. repeat (split; eauto). reflexivity.
            constructor; auto.
            eapply sem_ref_sem_equation; eauto.
        - (* fby *)
          inv Hwc. rename H3 into Hwc. clear H4.
          apply Forall_singl in Hwc. inv Hwc. simpl_Forall. rewrite app_nil_r in *.
          inv Hsem. simpl_Forall. rewrite app_nil_r in *; subst.
          inversion_clear H11 as [| | | | | | |???????? Hsem0 Hsem1 Hsem| | | | | |].
          simpl_Forall. repeat rewrite app_nil_r in *. inv Hsem; inv H13.
          eapply fby_iteexp_sem in H0 as [H' [Href1 [Hhistst1 [Hsem' Hsem'']]]]...
          2:{ inv Hun; auto. inv H2; inv H1. }
          exists H'. repeat (split; eauto).
          constructor; auto.
          eapply Seq with (ss:=[[y]]); simpl; repeat constructor; auto.
          eapply sem_var_refines; eauto.
        - (* arrow *)
          inv Hwc. rename H3 into Hwc. clear H4. simpl_Forall. inv H3. simpl_Forall. rewrite app_nil_r in *.
          inv Hsem. simpl_Forall. rewrite app_nil_r in *; subst.
          inversion_clear H11 as [| | | | | | | |???????? Hsem0 Hsem1 Hsem| | | | |].
          simpl_Forall. repeat rewrite app_nil_r in *. inv Hsem; inv H13.
          eapply arrow_iteexp_sem in H0 as [H' [Href1 [Hhistst1 [Hsem' Hsem'']]]]...
          2:{ inv Hun; auto. inv H2; inv H1. }
          exists H'. repeat (split; eauto).
          constructor; auto.
          eapply Seq with (ss:=[[y]]); simpl; repeat constructor; auto.
          eapply sem_var_refines; eauto.
        - (* other *)
          exists H. repeat (split; eauto). reflexivity.
          constructor; auto.
          eapply sem_ref_sem_equation; eauto.
      Qed.

      Lemma normfby_block_sem : forall to_cut d blocks' bs H st st' ,
          unnested_block G1 d ->
          wc_block G1 (vars++st_senv st) d ->
          sem_block_ck G1 H bs d ->
          hist_st vars bs H st ->
          normfby_block to_cut d st = (blocks', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars bs H' st' /\
                Forall (sem_block_ck G2 H' bs) blocks').
      Proof.
        induction d using block_ind2; intros * Hun Hwc Hsem Hist Hnorm;
          inv Hun; inv Hwc; inv Hsem; repeat inv_bind.
        - (* eq *)
          eapply normfby_equation_sem in H0 as (H'&?&?&?); eauto.
          exists H'. repeat (split; auto).
          simpl_Forall.
          constructor; auto.
        - (* reset *)
          simpl in Hnorm; cases; repeat inv_bind.
          apply Forall_singl in H. apply Forall_singl in H4.
          assert (forall k, exists H'k,
                     FEnv.refines (@EqSt _) (CStr.mask_hist k r H0) (CStr.mask_hist k r H'k) /\
                       hist_st vars (maskb k r bs) (mask_hist k r H'k) st' /\
                       Forall (sem_block_ck G2 (mask_hist k r H'k) (maskb k r bs)) x0) as Hblocks'.
          { intros k. specialize (H12 k).
            apply Forall_singl in H12. eapply H in H12 as (H'k&?&(?&Hsc)&?); eauto.
            2:eapply hist_st_mask; eauto.
            assert (slower_hist H'k (maskb k r bs)) as Hslow.
            { eapply sc_vars_slower_hist in Hsc; eauto using dom_dom_ub. }
            eapply slower_mask_hist in Hslow.
            exists H'k. split; [|split; [split|]]; intros.
            - rewrite <-Hslow; auto.
            - now apply dom_map.
            - unfold mask_hist. simpl. eapply sc_vars_morph. 1,3,4:eauto; reflexivity.
              apply Hslow.
            - simpl_Forall. eapply sem_block_ck_morph; eauto. reflexivity.
          }
          eapply consolidate_mask_hist
            with (P := fun k H'k => FEnv.refines (@EqSt _) (CStr.mask_hist k r H0) H'k /\
                                   hist_st vars (maskb k r bs) H'k st' /\
                                   Forall (sem_block_ck G2 H'k (maskb k r bs)) x0)
            in Hblocks' as (H'&HH').
          2:{ intros ????? Heq (?&(?&Hsc1)&?); subst. split; [|split; [split|]]; intros; auto.
              2:split; intros ?. 1-3:rewrite <-Heq; auto.
              1,2:eapply H9; eauto.
              - eapply sc_vars_morph; eauto. reflexivity.
              - simpl_Forall. eapply sem_block_ck_morph; eauto. reflexivity.
          }
          2:{ intros ?? (_&(Hdom1&_)&_); simpl. eapply dom_fenv_dom; eauto. }
          exists H'.
          assert (FEnv.refines (@EqSt _) H0 H') as Href.
          { eapply refines_unmask; intros.
            specialize (HH' k) as (?&_); eauto.
          }
          split; [|split; [split|]]; auto.
          + specialize (HH' 0) as (_&(Hdom&_)&_); auto.
            setoid_rewrite dom_map in Hdom; auto.
          + eapply sc_vars_unmask.
            intros k. specialize (HH' k) as (_&(_&?)&_); eauto.
          + simpl_Forall. econstructor; eauto.
            * eapply sem_ref_sem_exp; eauto. eapply sem_exp_refines; eauto.
            * intros ?. specialize (HH' k) as (_&_&?).
              constructor; auto. eapply Forall_forall in H5; eauto.
      Qed.

      Fact normfby_blocks_sem : forall bs to_cut blocks blocks' H st st' ,
          Forall (unnested_block G1) blocks ->
          Forall (wc_block G1 (vars++st_senv st)) blocks ->
          Forall (sem_block_ck G1 H bs) blocks ->
          hist_st vars bs H st ->
          normfby_blocks to_cut blocks st = (blocks', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars bs H' st' /\
                Forall (sem_block_ck G2 H' bs) blocks').
      Proof with eauto.
        induction blocks; intros * Hunt Hwc Hsem Hhistst Hfby;
          unfold normfby_blocks in Hfby; simpl in *; repeat inv_bind.
        - exists H; simpl; repeat (split; auto). reflexivity.
        - assert (normfby_blocks to_cut blocks x1 = (concat x2, st')) as Hnorm.
          { unfold normfby_blocks; repeat inv_bind.
            repeat eexists; eauto. repeat inv_bind; auto. }
          inv Hunt. inv Hwc. inv Hsem.
          assert (st_follows st x1) as Hfollows by (eapply normfby_block_st_follows in H0; eauto).
          eapply normfby_block_sem in H0 as [H' [Href1 [Hhistst1 Hsem1]]]. 2-5:eauto.
          assert (Forall (sem_block_ck G1 H' bs) blocks) as Hsem'.
          { simpl_Forall. eapply sem_block_refines... } clear H9.
          eapply IHblocks in Hnorm as (H''&Href&Hdom&Hsem2). 2-5:eauto.
          2:simpl_Forall; repeat solve_incl.
          + exists H''. split;[|split]...
            * etransitivity...
            * simpl. apply Forall_app; split; eauto.
              simpl_Forall. eapply sem_block_refines...
      Qed.

    End normfby_block_sem.

    Fact init_st_hist_st : forall b H xs,
        dom H xs ->
        sc_vars xs H b ->
        hist_st xs b H (@init_st norm2 _).
    Proof.
      intros b H n Hdom (?&?).
      split; [|split].
      1-3:unfold st_senv; rewrite init_st_anns, app_nil_r; auto.
    Qed.

    Lemma normfby_node_sem : forall f n ins outs,
        unnested_global (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        wc_global (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        wc_global G2 ->
        Ordered_nodes (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(types) G2.(externs) ((normfby_node n)::G2.(nodes))) ->
        sem_node_ck (Global G1.(types) G1.(externs) (n::G1.(nodes))) f ins outs ->
        sem_node_ck (Global G2.(types) G2.(externs) ((normfby_node n)::G2.(nodes))) f ins outs.
    Proof with eauto.
      intros * Hunt HwcG HwcG' Hord1 Hord2 Hsem.
      assert (Ordered_nodes (Global G2.(types) G2.(externs) (normfby_node n :: G2.(nodes)))) as Hord'.
      { inv Hord2. destruct H1. constructor; [split|]... }

      inv Hsem; assert (Hfind:=H0). destruct (ident_eq_dec (n_name n) f).
      - erewrite find_node_now in H0; eauto. inv H0.
        inversion_clear HwcG as [|?? (?&?)].
        (* The semantics of equations can be given according to G only *)
        assert (~Is_node_in_block (n_name n0) (n_block n0)) as Blk.
        { inv Hord1. destruct H9 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }
        eapply sem_block_ck_cons1 in Blk; eauto. clear H3.

        remember (normfby_node n0) as n'.
        unfold normfby_node in Heqn'; inv Heqn'.
        specialize (n_nodup n0) as (Hnd1&Hnd2).
        specialize (n_good n0) as (Hgood1&Hgood2&_).
        pose proof (n_syn n0) as Hsyn. inversion_clear Hsyn as [?? Hsyn1 Hsyn2 _]. inv Hsyn2.
        inversion_clear Hunt as [|?? [[??? Hblk ?] _] Hunt'].
        rewrite Hblk in *. symmetry in H3; inv H3. inv Blk. inv_scope.
        simpl in *. repeat rewrite app_nil_r in *.
        inversion_clear H0 as [? _ _ Hwc]. rewrite Hblk in Hwc. inv Hwc.
        assert (forall x, ~ IsLast (senv_of_ins (n_in n0) ++ senv_of_decls (n_out n0) ++ senv_of_decls locs) x) as Hnl.
        { repeat rewrite NoLast_app; repeat split; auto using senv_of_ins_NoLast.
          - intros * Hl. inv Hl. simpl_In. simpl_Forall. subst; simpl in *; congruence.
          - intros * Hl. inv Hl. simpl_In. simpl_Forall. subst; simpl in *; congruence. }
        repeat inv_scope'. subst Γ'.
        assert (Forall (sem_block_ck G1 (H + Hi') bs) blks) as Hsem by (destruct G1; auto).

        eapply normfby_blocks_sem
          with (vars:=senv_of_ins (n_in n0) ++ senv_of_decls (n_out n0) ++ senv_of_decls locs)
               (to_cut := (PS.union (ps_from_list (map fst (n_out n0))) (cut_next_cycles blks))) (st:=init_st)
          in Hsem as (Hf&Href&(Hdom&Hsc)&Heqs'')... 6:eapply surjective_pairing.
        2:{ inv Hgood2. take (GoodLocalsScope _ _ _) and inv it.
            rewrite app_assoc. apply Forall_app; split; simpl_Forall; simpl_In; simpl_Forall; auto.
            eapply Forall_forall in Hgood1; eauto. rewrite <-map_fst_senv_of_ins, <-map_fst_senv_of_decls, <-map_app. solve_In. }
        2:now destruct G1.
        2:{ destruct G1. unfold st_senv. now rewrite init_st_anns, app_nil_r, app_assoc. }
        2:{ take (clocked_node _ _ _) and destruct it as (Hdom&Hsc).
            constructor; simpl.
            * unfold st_senv. rewrite init_st_anns, app_nil_r, app_assoc.
              apply local_hist_dom; auto.
            * unfold st_senv. rewrite init_st_anns, app_nil_r, app_assoc.
              eapply local_hist_sc_vars with (H:=H); eauto using dom_dom_ub. reflexivity.
              inv Hnd2. take (NoDupScope _ _ _) and inv it.
              intros ?? contra; rewrite IsVar_fst, map_app, map_fst_senv_of_ins, map_fst_senv_of_decls in contra. eapply H18; eauto.
        }
        assert (Href':=Href). eapply FEnv.union_refines_inv in Href' as (Hi''&Heq&Href'&Hdom'); auto using EqStrel_Reflexive.
        2:{ intros * Hin Hin2. destruct x1; apply H4 in Hin; apply H12 in Hin2.
            2:{ inv Hin2. simpl_In. simpl_Forall. subst; simpl in *; congruence. }
            inv Hnd2. take (NoDupScope _ _ _) and inv it.
            take (forall x, InMembers x locs -> ~ _) and eapply it.
            + eapply IsVar_senv_of_decls; eauto.
            + now rewrite IsVar_fst, map_app, map_fst_senv_of_ins, map_fst_senv_of_decls in Hin. }

        eapply Snode with (H:=H); simpl...
        + erewrite find_node_now...
        + assumption.
        + assumption.
        + apply sem_block_ck_cons2; simpl...
          2:{ eapply find_node_not_Is_node_in in Hord2.
              2:erewrite find_node_now; eauto. auto. }
          rewrite Hblk.
          do 2 econstructor.
          3:{ destruct G2; eauto.
              simpl_Forall. eapply sem_block_ck_morph. 4:eauto. 2,3:reflexivity.
              symmetry. eapply Heq. }
          *{ destruct Hdom as (D1&DL1). destruct H4 as ((D2&DL2)&_).
             split; intros *; simpl in *.
             - rewrite Hdom', D1, D2. setoid_rewrite senv_of_decls_app. rewrite <-st_senv_senv_of_decls.
               repeat rewrite IsVar_app.
               split; [intros ([[In|[In|In]]|In]&Hnin)|intros [In|In]]; try congruence; auto.
               + exfalso. eapply Hnin; eauto.
               + exfalso. eapply Hnin; eauto.
               + split; auto. intros contra.
                 inv Hnd2. take (NoDupScope _ _ _) and inv it.
                 eapply H18; eauto. eapply IsVar_senv_of_decls; eauto.
                 now rewrite 2 IsVar_fst, map_fst_senv_of_ins, map_fst_senv_of_decls, <-in_app_iff in contra.
               + split; auto.
                 intros contra. rewrite 2 IsVar_fst, map_fst_senv_of_ins, map_fst_senv_of_decls, <-in_app_iff in contra.
                 inv In. simpl_In. simpl_Forall.
                 eapply Facts.st_valid_AtomOrGensym_nIn; eauto using norm2_not_in_norm1_prefs.
                 unfold st_ids. solve_In.
             - rewrite Hdom', DL1, DL2. setoid_rewrite senv_of_decls_app. rewrite <-st_senv_senv_of_decls.
               repeat rewrite IsLast_app.
               split; [intros ([[In|[In|In]]|In]&Hnin)|intros [In|In]]; try congruence; auto.
               + exfalso. eapply Hnin; eauto.
               + exfalso. eapply Hnin; eauto.
               + inv In. simpl_In. simpl_Forall. subst; simpl in *; congruence.
               + inv In. simpl_In. congruence.
           }
          * eapply sc_vars_morph, sc_vars_incl; [reflexivity| |reflexivity| |eauto].
            now symmetry. setoid_rewrite senv_of_decls_app. rewrite <-st_senv_senv_of_decls.
            solve_incl_app.
        + simpl. now subst bs.
      - erewrite find_node_other in Hfind; eauto.
        eapply sem_node_ck_cons2...
        destruct G2; apply HGref.
        destruct G1; econstructor...
        eapply sem_block_ck_cons1; eauto.
        eapply find_node_later_not_Is_node_in in Hord1...
    Qed.

  End normfby_node_sem.

  Lemma normfby_global_refines : forall G,
      unnested_global G ->
      wc_global G ->
      global_sem_refines G (normfby_global G).
  Proof with eauto with norm.
    intros [].
    induction nodes0; intros * Hunt Hwc; simpl.
    - apply global_sem_ref_nil.
    - apply global_sem_ref_cons with (f:=n_name a)...
      + eapply normfby_global_wc, wc_global_Ordered_nodes in Hwc;
          unfold normfby_global in Hwc; simpl in Hwc...
      + inv Hunt; inv Hwc. eapply IHnodes0...
      + intros ins outs Hsem; simpl.
        eapply normfby_node_sem with (G1:=(Global types0 externs0 nodes0)) (G2:=(Global _ _ _)) in Hsem...
        * apply iface_eq_iface_incl, normfby_global_eq.
        * inv Hunt; inv Hwc. eapply IHnodes0...
        * inv Hwc; simpl in *...
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
       (Ty : LTYPING Ids Op OpAux Cks Senv Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Lord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
       (LClockSem : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Clo Lord CStr Sem)
       (Norm : NORMALIZATION Ids Op OpAux Cks Senv Syn)
       <: CORRECTNESS Ids Op OpAux Cks CStr Senv Syn Ty Clo Lord Sem LClockSem Norm.
  Include CORRECTNESS Ids Op OpAux Cks CStr Senv Syn Ty Clo Lord Sem LClockSem Norm.
End CorrectnessFun.
