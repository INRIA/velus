From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LSemantics Lustre.LClockedSemantics.
From Velus Require Import Lustre.SubClock.SCCorrectness.
From Velus Require Import Lustre.ClockSwitch.ClockSwitch.
From Velus Require Import Lustre.ClockSwitch.CSClocking.

Module Type CSCORRECTNESS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS Ids Op OpAux)
       (Import CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Import Senv  : STATICENV Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Ty    : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import Cl    : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import Ord   : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem          : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (Import LCS   : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Cl Ord CStr Sem)
       (Import CS    : CLOCKSWITCH Ids Op OpAux Cks Senv Syn).

  Module Import SCT := SCCorrectnessFun Ids Op OpAux Cks CStr Senv Syn Cl Ord Sem LCS SC. Import SC.

  Module Clocking := CSClockingFun Ids Op OpAux Cks Senv Syn Cl CS.
  Module Import CIStr := CoindIndexedFun Ids Op OpAux Cks CStr IStr.

  Import Fresh Facts Tactics List.

  Section switch_block.
    Variable G1 : @global noauto_block auto_prefs.
    Variable G2 : @global noswitch_block switch_prefs.

    Hypothesis HwcG1 : wc_global G1.
    Hypothesis HGref : global_sem_refines G1 G2.

    Import Permutation.
    Import Fresh Facts Tactics List.

    Lemma cond_eq_sem envty : forall Hi Hl bs e ty ck vs x xcs eqs' st st' aft,
        Forall (AtomOrGensym auto_prefs) envty ->
        st_valid_after st switch aft ->
        FEnv.dom_ub Hi (envty ++ st_ids st) ->
        sem_exp_ck G2 (Hi, Hl) bs e [vs] ->
        sem_clock Hi bs ck (abstract_clock vs) ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        exists Hi',
          FEnv.refines (@EqSt _) Hi Hi' /\
            sem_var Hi' x vs /\
            Forall (sem_equation_ck G2 (Hi', Hl) bs) eqs' /\
            (forall x, FEnv.In x Hi' <-> FEnv.In x Hi \/ In x (map fst xcs)) /\
            FEnv.dom_ub Hi' (envty ++ st_ids st') /\
            sc_vars (senv_of_tyck xcs) (Hi', Hl) bs.
    Proof.
      intros * Hat Hst Hdom Hsem Hsemck Hcond.
      destruct e; simpl in *; repeat (take ann and destruct it); repeat inv_bind.
      3:{ inv Hsem. exists Hi; repeat split; simpl; eauto with fenv.
          + reflexivity.
          + intros [|[]]; auto.
          + intros * Hca. inv Hca. inv H.
          + intros * Hca. inv Hca. inv H. }
      1-11:(assert (FEnv.refines (@EqSt _) Hi (FEnv.add x vs Hi)) as Href;
            [eapply FEnv.add_refines; intros Henvin; try reflexivity;
             eapply Hdom, in_app_iff in Henvin as [Hin|Hin]; eauto;
             [eapply fresh_ident_prefixed in H as (?&?&?); subst;
              eapply Forall_forall in Hat; eauto; eapply contradict_AtomOrGensym in Hat; eauto using switch_not_in_auto_prefs
             |eapply fresh_ident_nIn; eauto]
            |]).
      1-11:(assert (sem_var (FEnv.add x vs Hi) x vs) as Hv;
            [econstructor; try reflexivity; apply FEnv.gss; reflexivity|]).
      1-11:
        (exists (FEnv.add x vs Hi); split; [|split; [|split; [|split; [|split]]]]; eauto; simpl;
              [do 2 (econstructor; eauto);
               [econstructor; eauto using sem_exp_refines|
                constructor; auto]
              |intros; rewrite FEnv.add_In, or_comm; apply or_iff_compat_l;
               split; [intros|intros [|[]]]; auto
              |intros ?; rewrite <-fresh_ident_vars_perm, <-Permutation_middle; eauto; apply FEnv.add_dom_ub; auto
              |split]).
      1-22:(intros * Hck; inv Hck; try (intros Hca; inv Hca);
            repeat (take (_ \/ False) and destruct it as [|[]]); inv_equalities;
            simpl in *; try congruence;
            do 2 esplit; eauto using Sem.sem_clock_refines).
    Qed.

    Lemma sem_clock_Con_filter Hi bs' bs : forall ck xc tx tn e sc,
        wt_stream sc (Tenum tx tn) ->
        slower sc bs ->
        sem_var Hi xc sc ->
        sem_clock Hi bs' ck (abstract_clock sc) ->
        sem_clock Hi bs' (Con ck xc (Tenum tx tn, e)) (ffilterb e sc bs).
    Proof.
      intros * Hwt Hslow Hv Hck.
      rewrite sem_clock_equiv in *. rewrite sem_var_equiv in *.
      intros n. specialize (Hv n). specialize (Hck n).
      rewrite tr_Stream_nth in Hv.
      repeat rewrite tr_Stream_nth in *. rewrite ac_nth in Hck. rewrite ffilterb_nth.
      setoid_rewrite SForall_forall in Hwt. specialize (Hwt n).
      rewrite slower_nth in Hslow. specialize (Hslow n).
      destruct (sc # n) eqn:Hsc; simpl; setoid_rewrite Hsc in Hck.
      - constructor; auto.
      - destruct (bs # n); [|specialize (Hslow eq_refl); setoid_rewrite Hsc in Hslow; congruence].
        destruct (_ ==b _) eqn:Heq.
        + rewrite equiv_decb_equiv in Heq; inv Heq.
          constructor; auto.
        + inv Hwt.
          eapply IStr.Son_abs2; [eauto|eauto|].
          intro contra; subst. rewrite equiv_decb_refl in Heq. congruence.
    Qed.

    Lemma when_filter : forall tx tn e vs sc,
        wt_stream sc (Tenum tx tn) ->
        abstract_clock vs ≡ abstract_clock sc ->
        when e vs sc (ffilterv e sc vs).
    Proof.
      intros * Hwt Hac.
      apply when_spec; intros n.
      setoid_rewrite SForall_forall in Hwt. specialize (Hwt n).
      eapply eqst_ntheq with (n:=n) in Hac. repeat rewrite ac_nth in Hac.
      rewrite ffilterv_nth.
      destruct (vs # n) eqn:Hvs, (sc # n) eqn:Hsc; setoid_rewrite Hsc in Hac; try congruence; simpl; auto.
      right. inv Hwt.
      destruct (_ ==b _) eqn:Heq.
      - rewrite equiv_decb_equiv in Heq; inv Heq.
        eauto.
      - left. repeat esplit; eauto.
        intro contra; subst.
        rewrite equiv_decb_refl in Heq. congruence.
    Qed.

    Lemma when_free_sem Hi' Hl bs' : forall x y ty ck cx tx tn e sc vs,
        sem_var Hi' cx sc ->
        wt_stream sc (Tenum tx tn) ->
        sem_var Hi' x vs ->
        abstract_clock vs ≡ abstract_clock sc ->
        sem_var Hi' y (ffilterv e sc vs) ->
        sem_block_ck G2 (Hi', Hl) bs' (when_free x y ty ck cx (Tenum tx tn) e).
    Proof.
      intros * Hcx Hwt Hx Hac Hy.
      constructor. econstructor. repeat constructor.
      2:{ simpl. rewrite app_nil_r; repeat constructor. eauto. }
      econstructor; eauto. repeat constructor; eauto.
      simpl. repeat constructor.
      eapply when_filter; eauto.
    Qed.

    Lemma merge_filter {A} : forall c vs (brs : list (enumtag * A)) tx tn,
        wt_stream c (Tenum tx tn) ->
        abstract_clock vs ≡ abstract_clock c ->
        Permutation (map fst brs) (seq 0 (length tn)) ->
        merge c (map (fun '(k, _) => (k, ffilterv k c vs)) brs) vs.
    Proof.
      intros * Hwt Hac Hperm.
      apply merge_spec. intros n.
      eapply SForall_forall in Hwt. instantiate (1:=n) in Hwt.
      eapply eqst_ntheq with (n:=n) in Hac. repeat rewrite ac_nth in Hac.
      destruct (c # n) eqn:Hc, (vs # n) eqn:Hvs; setoid_rewrite Hc in Hac; simpl in *; try congruence; [left|right].
      - repeat split; auto.
        apply Forall_map, Forall_forall; intros (?&?) ?; simpl.
        rewrite ffilterv_nth, Hc; simpl; auto.
      - inv Hwt. repeat esplit; eauto.
        + rewrite CommonList.Exists_map.
          assert (In v1 (map fst brs)) as Hin.
          { rewrite Hperm. apply in_seq; lia. }
          apply in_map_iff in Hin as ((?&?)&?&Hin); subst.
          eapply Exists_exists. do 2 esplit; eauto; simpl.
          split; auto. rewrite ffilterv_nth, Hc, equiv_decb_refl; auto.
        + rewrite Forall_map. apply Forall_forall; intros (?&?) ? Hneq.
          rewrite ffilterv_nth, Hc; simpl. destruct (_ ==b _) eqn:Heq; auto.
          rewrite equiv_decb_equiv in Heq. inv Heq; congruence.
    Qed.

    Lemma merge_defs_sem Hi Hi' Hl bs' : forall sub x ty ck xc tx tn subs c vs,
        Permutation (map fst subs) (seq 0 (length tn)) ->
        (forall x0 y vs, Env.find x0 sub = Some y -> sem_var Hi x0 vs -> sem_var Hi' y vs) ->
        (forall x0 vs, Env.find x0 sub = None -> sem_var Hi x0 vs -> sem_var Hi' x0 vs) ->
        sem_var Hi' xc c ->
        wt_stream c (Tenum tx tn) ->
        sem_var Hi x vs ->
        abstract_clock vs ≡ abstract_clock c ->
        Forall (fun '(k, sub) => sem_var Hi' (rename_var sub x) (ffilterv k c vs)) subs ->
        sem_block_ck G2 (Hi', Hl) bs' (merge_defs sub x ty ck xc (Tenum tx tn) subs).
    Proof.
      intros * Hperm Hsub Hnsub Hxc Hwt Hx Hac Hx'.
      constructor. econstructor. repeat constructor.
      2:{ simpl; rewrite app_nil_r; repeat constructor.
          eapply rename_var_sem, Hx; eauto. }
      eapply Smerge with (vs:=[List.map (fun '(k, _) => (k, ffilterv k c vs)) subs]); eauto.
      - clear Hperm.
        induction subs as [|(?&?)]; simpl; inv Hx'; repeat constructor.
        econstructor; eauto.
        1,2:repeat constructor; eauto.
      - repeat constructor. eapply merge_filter; eauto.
    Qed.

    Lemma new_idents_sem {A} envty frees defs bck tx tn xc :
      forall Hi Hi' Hl bs' (branches : list (enumtag * A)) xs sc st st' aft,
        st_valid_after st switch aft ->
        Forall (AtomOrGensym auto_prefs) envty ->
        FEnv.dom_ub Hi' (envty ++ st_ids st) ->
        sem_var Hi' xc sc ->
        sem_clock Hi' bs' bck (abstract_clock sc) ->
        wt_stream sc (Tenum tx tn) ->
        Forall (fun '(x, _) => exists vs, sem_var Hi x vs /\ abstract_clock vs ≡ abstract_clock sc) (frees++defs) ->
        mmap
          (fun '(k, _) =>
             bind (new_idents bck xc (Tenum tx tn) k frees)
                  (fun nfrees =>
                     bind (new_idents bck xc (Tenum tx tn) k defs)
                          (fun ndefs => ret (k, Env.from_list (map (fun '(x, y2, _) => (x, y2)) (nfrees ++ ndefs)), nfrees, ndefs)))) branches st = (xs, st') ->
        exists Hi'',
          Hi' ⊑ Hi'' /\
          (forall x, FEnv.In x Hi'' <-> FEnv.In x Hi' \/ InMembers x (flat_map (fun '(_, _, nfrees, ndefs) => (map (fun '(_, x, (ty, ck)) => (x, (ty, ck, xH, @None (exp * ident)))) (nfrees++ndefs))) xs)) /\
          FEnv.dom_ub Hi'' (envty ++ st_ids st') /\
          Forall (fun '(k, sub, _, _) => (forall x y vs, Env.find x sub = Some y -> sem_var Hi x vs -> sem_var Hi'' y (ffilterv k sc vs))) xs /\
          sc_vars (flat_map (fun '(_, _, nfrees, ndefs) => (map (fun '(_, x, (ty, ck)) => (x, Build_annotation ty ck xH None)) (nfrees++ndefs))) xs) (Hi'', Hl) bs'.
    Proof.
      intros * Hst Hat Hdomub Hx Hsemck Hwt Hsc Hmmap.
      remember (Hi' + FEnv.of_list (flat_map (fun '(k, _, nfrees, ndefs) =>
                                                map (fun '(x, nx, _) => (nx, ffilterv k sc (or_default (Streams.const absent) (Hi x))))
                                                    (nfrees++ndefs)) xs)) as Hi'2.
      exists Hi'2.
      assert (st_valid_after st' switch aft) as Hvalid'.
      { eapply mmap_st_valid; eauto.
        eapply Forall_forall; intros (?&?) ? (((?&?)&?)&?) ????; repeat inv_bind.
        do 2 (eapply new_idents_st_valid; [|eauto]; auto). }
      assert (Hi' ⊑ Hi'2) as Href.
      { subst. intros ?? Hfind. do 2 esplit; try reflexivity. apply FEnv.union2; auto.
        apply FEnv.of_list_None; intros Hinm; apply fst_InMembers in Hinm.
        eapply new_idents_st_ids' in Hmmap.
        assert (FEnv.In x Hi') as Hin2 by (econstructor; eauto).
        apply Hdomub, in_app_iff in Hin2 as [Hin2|Hin2].
        - eapply Forall_forall in Hat; eauto.
          eapply st_valid_after_AtomOrGensym_nIn in Hvalid'; eauto using switch_not_in_auto_prefs.
          eapply Hvalid'. rewrite Hmmap. apply in_or_app, or_intror. solve_In. auto.
        - eapply st_valid_NoDup, NoDup_app_l in Hvalid'. rewrite Hmmap in Hvalid'.
          eapply NoDup_app_In in Hvalid'; eauto.
          eapply Hvalid'.
          solve_In. auto.
      }
      assert (NoDupMembers
                (flat_map
                   (fun '(k, _, nfrees, ndefs) =>
                      map (fun '(x2, nx, _) => (nx, ffilterv k sc (or_default (Streams.const absent) (Hi x2))))
                          (nfrees ++ ndefs)) xs)) as Hnd'.
      { eapply st_valid_NoDup, NoDup_app_l in Hvalid'.
        erewrite new_idents_st_ids' in Hvalid'; eauto. apply NoDup_app_r in Hvalid'.
        erewrite fst_NoDupMembers.
        rewrite flat_map_concat_map, concat_map, map_map in *. erewrite map_ext; eauto.
        intros (((?&?)&?)&?). erewrite 2 map_map, map_ext; eauto. intros ((?&?)&?&?); auto.
      }

      split; [|split; [|repeat split]]; auto.
      - intros. subst.
        rewrite FEnv.union_In, FEnv.of_list_In. apply or_iff_compat_l.
        erewrite 2 fst_InMembers, 2 flat_map_concat_map, 2 concat_map, 2 map_map, map_ext with (f:=fun _ => map _ _); try reflexivity.
        intros; destruct_conjs. erewrite 2 map_map. apply map_ext. intros; destruct_conjs; auto.
      - intros ? Hin; subst. erewrite new_idents_st_ids'; eauto. rewrite app_assoc, in_app_iff.
        apply FEnv.union_In in Hin as [Hin|Hin]; auto.
        right. apply FEnv.of_list_In, fst_InMembers in Hin.
        solve_In; auto.
      - eapply mmap_values, Forall2_ignore1 in Hmmap.
        eapply Forall_impl_In; [|eauto]; intros (((?&?)&?)&?) Hin ((?&?)&?&?&?&?) ??? Hfind Hv; repeat inv_bind.
        inv Hv.
        econstructor. 2:rewrite H4; reflexivity.
        apply FEnv.union3', FEnv.of_list_In_find; auto.
        apply Env.from_list_find_In in Hfind. repeat (solve_In; simpl).
        rewrite H3; simpl; auto.
      - intros * Hck. inv Hck. simpl_In.
        eapply mmap_values, Forall2_ignore1, Forall_forall in Hmmap as ((?&?)&?&?&?&?); eauto; repeat inv_bind.
        assert (InMembers i (frees++defs)) as Hin3. 2:eapply InMembers_In in Hin3 as (?&Hin3).
        { erewrite fst_InMembers, map_app, <-2 new_idents_old; eauto.
          rewrite <-map_app. apply in_map_iff; do 2 esplit; eauto. auto. }
        assert (c = Con bck xc (Tenum tx tn, e0)); subst.
        { apply in_app_iff in Hin0 as [Hin'|Hin'];
            eapply Clocking.new_idents_In_inv_ck in Hin'; eauto. }
        eapply Forall_forall in Hsc; eauto; simpl in *. destruct Hsc as (vs&Hv&Hac).
        exists (ffilterv e0 sc vs). split; auto.
        + inv Hv. econstructor. 2:rewrite H4; reflexivity.
          eapply FEnv.union3', FEnv.of_list_In_find; auto.
          repeat (solve_In; simpl).
          rewrite H3; simpl; auto.
        + eapply Sem.sem_clock_refines; eauto. rewrite ac_ffilter.
          apply sem_clock_Con_filter; eauto.
          rewrite Hac. apply ac_slower.
      - intros * Hck Hca. exfalso. inv Hca. simpl_In. congruence.
    Qed.

    Fact switch_blocks_sem' aft : forall bck sub Γty Γck Hi Hi' Hl bs bs' blks blks' st st',
        Forall
          (fun blk => forall bck sub Γty Γck Hi Hi' Hl bs bs' blk' st st',
               (forall x, ~IsLast Γck x) ->
               (forall x, Env.In x sub -> InMembers x Γck) ->
               (forall x y vs, Env.find x sub = Some y -> sem_var Hi x vs -> sem_var Hi' y vs) ->
               (forall x vs, Env.find x sub = None -> sem_var Hi x vs -> sem_var Hi' x vs) ->
               st_valid_after st switch aft ->
               incl (map fst Γck) (map fst Γty) ->
               NoDupMembers Γty ->
               NoDupMembers Γck ->
               Forall (AtomOrGensym auto_prefs) (map fst Γty) ->
               FEnv.dom_ub Hi (map fst Γty) ->
               sc_vars Γck (Hi, Hl) bs ->
               FEnv.dom_ub Hi' (map fst Γty ++ st_ids st) ->
               sem_clock Hi' bs' bck bs ->
               noauto_block blk ->
               NoDupLocals (map fst Γty) blk ->
               GoodLocals auto_prefs blk ->
               wt_block G1 Γty blk ->
               wc_block G1 Γck blk ->
               sem_block_ck G1 (Hi, Hl) bs blk ->
               switch_block Γck bck sub blk st = (blk', st') ->
               sem_block_ck G2 (Hi', Hl) bs' blk') blks ->
        (forall x, ~IsLast Γck x) ->
        (forall x, Env.In x sub -> InMembers x Γck) ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi x vs -> sem_var Hi' y vs) ->
        (forall x vs, Env.find x sub = None -> sem_var Hi x vs -> sem_var Hi' x vs) ->
        st_valid_after st switch aft ->
        incl (map fst Γck) (map fst Γty) ->
        NoDupMembers Γty ->
        NoDupMembers Γck ->
        Forall (AtomOrGensym auto_prefs) (map fst Γty) ->
        FEnv.dom_ub Hi (map fst Γty) ->
        sc_vars Γck (Hi, Hl) bs ->
        FEnv.dom_ub Hi' (map fst Γty ++ st_ids st) ->
        sem_clock Hi' bs' bck bs ->
        Forall noauto_block blks ->
        Forall (NoDupLocals (map fst Γty)) blks ->
        Forall (GoodLocals auto_prefs) blks ->
        Forall (wt_block G1 Γty) blks ->
        Forall (wc_block G1 Γck) blks ->
        Forall (sem_block_ck G1 (Hi, Hl) bs) blks ->
        mmap (switch_block Γck bck sub) blks st = (blks', st') ->
        Forall (sem_block_ck G2 (Hi', Hl) bs') blks'.
    Proof.
      intros * Hf Hnl1 Hsubin Hsub Hnsub Hvalid Hincl Hnd1 Hnd2 Hat Hdom1 Hsc Hdom2 Hbck Hnl2 Hnd3 Hgood Hwt Hwc Hsem Hmmap.
      eapply mmap_values_valid_follows, Forall2_ignore1 in Hmmap;
        eauto using switch_block_st_valid, switch_block_st_follows.
      simpl_Forall. eapply Hf; eauto.
      - simpl_Forall; auto.
      - eapply FEnv.dom_ub_incl; eauto.
        apply incl_app; [solve_incl_app|apply incl_appr, incl_map, st_follows_incl]; auto.
    Qed.

    Lemma switch_scope_sem {A} P_na P_nd P_good P_wt P_wc P_sem1 f_switch (P_sem2: _ -> _ -> Prop) aft :
      forall locs caus (blk: A) bck sub Γty Γck Hi Hi' Hl bs bs' s' st st',
        (forall x, ~IsLast Γck x) ->
        (forall x, Env.In x sub -> InMembers x Γck) ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi x vs -> sem_var Hi' y vs) ->
        (forall x vs, Env.find x sub = None -> sem_var Hi x vs -> sem_var Hi' x vs) ->
        st_valid_after st switch aft ->
        incl (map fst Γck) (map fst Γty) ->
        NoDupMembers Γty ->
        NoDupMembers Γck ->
        Forall (AtomOrGensym auto_prefs) (map fst Γty) ->
        FEnv.dom_ub Hi (map fst Γty) ->
        sc_vars Γck (Hi, Hl) bs ->
        FEnv.dom_ub Hi' (map fst Γty ++ st_ids st) ->
        sem_clock Hi' bs' bck bs ->
        noauto_scope P_na (Scope locs caus blk) ->
        NoDupScope P_nd (map fst Γty) (Scope locs caus blk) ->
        GoodLocalsScope P_good auto_prefs (Scope locs caus blk) ->
        wt_scope P_wt G1 Γty (Scope locs caus blk) ->
        wc_scope P_wc G1 Γck (Scope locs caus blk) ->
        sem_scope_ck (fun Hi => sem_exp_ck G1 Hi bs) P_sem1 (Hi, Hl) bs (Scope locs caus blk) ->
        switch_scope f_switch Γck bck sub (Scope locs caus blk) st = (s', st') ->
        (forall Γty Γck Hi Hi' Hl blk' st st',
            (forall x, ~IsLast Γck x) ->
            (forall x, Env.In x sub -> InMembers x Γck) ->
            (forall x y vs, Env.find x sub = Some y -> sem_var Hi x vs -> sem_var Hi' y vs) ->
            (forall x vs, Env.find x sub = None -> sem_var Hi x vs -> sem_var Hi' x vs) ->
            st_valid_after st switch aft ->
            incl (map fst Γck) (map fst Γty) ->
            NoDupMembers Γty ->
            NoDupMembers Γck ->
            Forall (AtomOrGensym auto_prefs) (map fst Γty) ->
            FEnv.dom_ub Hi (map fst Γty) ->
            sc_vars Γck (Hi, Hl) bs ->
            FEnv.dom_ub Hi' (map fst Γty ++ st_ids st) ->
            sem_clock Hi' bs' bck bs ->
            P_na blk ->
            P_nd (map fst Γty) blk ->
            P_good blk ->
            P_wt Γty blk ->
            P_wc Γck blk ->
            P_sem1 (Hi, Hl) blk ->
            f_switch Γck blk st = (blk', st') ->
            P_sem2 (Hi', Hl) blk') ->
        sem_scope_ck (fun Hi => sem_exp_ck G2 Hi bs') P_sem2 (Hi', Hl) bs' s'.
    Proof.
      intros * Hnl1 Hsubin Hsub Hnsub Hvalid Hincl Hnd1 Hnd2 Hat Hdom Hsc Hdomub Hbck Hnl2 Hnd3 Hgood Hwt Hwc Hsem Hmmap Hind;
        inv Hnl2; inv Hnd3; inv Hgood; inv Hwt; inv Hwc; inv Hsem; simpl in *; repeat inv_bind.
      assert (forall x, InMembers x locs -> ~FEnv.In x Hi') as Hnin.
      { intros ? Hinm Hin.
        eapply Hdomub, in_app_iff in Hin as [|]; eauto.
        - eapply H7; eauto.
        - eapply st_valid_after_AtomOrGensym_nIn; eauto using switch_not_in_auto_prefs.
          eapply fst_InMembers, Forall_forall in Hinm; eauto.
      }

      assert (forall x y vs,
                 Env.find x sub = Some y -> sem_var Hi'0 x vs ->
                 sem_var ((FEnv.restrict Hi'0 (map fst locs)) + Hi') y vs) as Hsub'.
      { intros ??? Hfind Hv.
        destruct (InMembers_dec x0 locs ident_eq_dec).
        - exfalso. apply Env.find_In, Hsubin, fst_InMembers, Hincl in Hfind.
          eapply H7; eauto.
        - eapply Sem.sem_var_refines; [|eapply Hsub]; eauto. eauto using FEnv.union_refines4', EqStrel_Reflexive. }
      assert (forall x vs,
                 Env.find x sub = None -> sem_var Hi'0 x vs ->
                 sem_var ((FEnv.restrict Hi'0 (map fst locs)) + Hi') x vs) as Hnsub'.
      { intros ?? Hfind Hv.
        destruct (InMembers_dec x0 locs ident_eq_dec).
        - inv Hv. econstructor; eauto.
          eapply FEnv.union2.
          +  eapply FEnv.restrict_find; eauto. now rewrite <-fst_InMembers.
          + apply FEnv.not_find_In; eauto.
        - eapply Sem.sem_var_refines; [|eapply Hnsub]; eauto using FEnv.union_refines4', EqStrel_Reflexive. }

      eapply Sscope with (Hi':=(FEnv.restrict Hi'0 (map fst locs)) + Hi'); eauto.
      - intros ?? Hv1 Hnim.
        erewrite fst_InMembers, map_map, map_ext with (g:=fst) in Hnim. 2:intros; destruct_conjs; auto.
        inv Hv1. econstructor; eauto.
        apply FEnv.union4 in H5 as [Hfind|]; eauto.
        apply FEnv.restrict_find_inv in Hfind as (?&?). contradiction.
      - intros. rewrite FEnv.union_In, fst_InMembers, map_map.
        erewrite (map_ext (fun x => fst (let '(x, (ty, ck, cx, o)) := x in (_, _))) fst). 2:intros; destruct_conjs; auto.
        rewrite FEnv.restrict_In, H20, fst_InMembers.
        split; [intros [(?&?)|]|intros [|]]; auto.
      - intros; simpl_In. simpl_Forall. congruence.
      - split; intros * Hck.
        2:{ intros Hca. inv Hca. simpl_In. simpl_Forall. subst; simpl in *. congruence. }
        inv Hck; simpl_In. edestruct H24 as ((?&?&?)&_). econstructor; solve_In. eauto.
        do 2 esplit.
        *{ inv H0. simpl_In. econstructor; eauto.
           eapply FEnv.union2. eapply FEnv.restrict_find; eauto.
           - eapply in_map_iff. do 2 esplit; eauto. auto.
           - apply FEnv.not_find_In; eauto using In_InMembers.
        }
        *{ eapply subclock_clock_sem. 1,2,4:eauto.
           eapply Sem.sem_clock_refines; [|eauto]; eauto using FEnv.union_refines4', EqStrel_Reflexive.
          }
      - eapply Hind with (Γty:=Γty++_) in H; eauto.
        + rewrite NoLast_app. split; auto.
          intros * Hla. inv Hla. simpl_In; simpl_Forall. subst; simpl in *; congruence.
        + intros ? Hin. apply InMembers_app; auto.
        + rewrite 2 map_app, map_fst_senv_of_locs.
          eapply incl_appl'. auto.
        + eapply NoDupMembers_app; eauto. rewrite NoDupMembers_senv_of_locs; auto.
          intros ? Hin1 Hin2. rewrite InMembers_senv_of_locs in Hin2.
          eapply H7; eauto. apply fst_InMembers; auto.
        + eapply NoDupMembers_app; eauto. rewrite NoDupMembers_senv_of_locs; auto.
          intros ? Hinm1 Hinm2. rewrite InMembers_senv_of_locs in Hinm2.
          eapply H7; eauto. apply Hincl, fst_InMembers; auto.
        + rewrite map_app, map_fst_senv_of_locs. apply Forall_app; auto.
        + rewrite map_app, map_fst_senv_of_locs. eapply local_hist_dom_ub; eauto.
        + apply sc_vars_app; auto.
          2:eapply sc_vars_refines; [| |eauto]; eauto using local_hist_dom_ub_refines.
          intros ? Hinm1 Hinm2. rewrite InMembers_senv_of_locs in Hinm2.
          eapply H7; eauto. apply Hincl, fst_InMembers; auto.
        + intros ?. rewrite FEnv.union_In, FEnv.restrict_In, map_app, map_fst_senv_of_locs, (Permutation_app_comm (map fst Γty)), <-app_assoc, in_app_iff.
          intros [(?&?)|]; auto.
        + eapply Sem.sem_clock_refines; [|eauto]; eauto using FEnv.union_refines4', EqStrel_Reflexive.
        + now rewrite map_app, map_fst_senv_of_locs.
    Qed.

    Lemma switch_block_sem aft : forall blk bck sub Γty Γck Hi Hi' Hl bs bs' blk' st st',
        (forall x, ~IsLast Γck x) ->
        (forall x, Env.In x sub -> InMembers x Γck) ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi x vs -> sem_var Hi' y vs) ->
        (forall x vs, Env.find x sub = None -> sem_var Hi x vs -> sem_var Hi' x vs) ->
        st_valid_after st switch aft ->
        incl (map fst Γck) (map fst Γty) ->
        NoDupMembers Γty ->
        NoDupMembers Γck ->
        Forall (AtomOrGensym auto_prefs) (map fst Γty) ->
        FEnv.dom_ub Hi (map fst Γty) ->
        sc_vars Γck (Hi, Hl) bs ->
        FEnv.dom_ub Hi' (map fst Γty ++ st_ids st) ->
        sem_clock Hi' bs' bck bs ->
        noauto_block blk ->
        NoDupLocals (map fst Γty) blk ->
        GoodLocals auto_prefs blk ->
        wt_block G1 Γty blk ->
        wc_block G1 Γck blk ->
        sem_block_ck G1 (Hi, Hl) bs blk ->
        switch_block Γck bck sub blk st = (blk', st') ->
        sem_block_ck G2 (Hi', Hl) bs' blk'.
    Proof.
      Opaque switch_scope.
      induction blk using block_ind2;
        intros * Hnl1 Hsubin Hsub Hnsub Hvalid Hincl Hnd1 Hnd2 Hat Hdom Hsc Hdomub Hbck Hnl2 Hnd3 Hgood Hwt Hwc Hsem Hmmap;
        inv Hnl2; inv Hnd3; inv Hgood; inv Hwt; inv Hwc; inv Hsem; simpl in *; repeat inv_bind.
      - (* equation *)
        constructor. eapply subclock_equation_sem; eauto.

      - (* reset *)
        econstructor; eauto.
        1:{ eapply subclock_exp_sem; eauto. }
        intros k. eapply switch_blocks_sem' with (Hi:=mask_hist k r Hi) in H0; eauto.
        + intros ??? Hfind Hv.
          eapply sem_var_mask_inv in Hv as (?&Hv&Heq). rewrite Heq.
          eapply sem_var_mask; eauto.
        + intros ?? Hfind Hv.
          eapply sem_var_mask_inv in Hv as (?&Hv&Heq). rewrite Heq.
          eapply sem_var_mask; eauto.
        + apply FEnv.dom_ub_map; auto.
        + eapply sc_vars_mask in Hsc; eauto.
        + apply FEnv.dom_ub_map; auto.
        + eapply sem_clock_mask; eauto.

      - (* switch *)
        destruct (partition _ _) eqn:Hpart. apply partition_Partition in Hpart.
        repeat inv_bind. destruct x. repeat inv_bind.
        rename x into subs.

        assert (sem_clock Hi bs ck (abstract_clock sc)) as Hsemck.
        { eapply sc_exp in H15; eauto.
          rewrite H12 in H15; simpl in H15. now inv H15. }
        repeat rewrite subclock_exp_typeof, H6 in *; simpl in *.
        repeat rewrite subclock_exp_clockof, H12 in *; simpl in *.
        assert (sem_clock Hi' bs' (subclock_clock bck sub ck) (abstract_clock sc)) as Hsemck'.
        { eapply subclock_clock_sem; eauto. }

        assert (incl (l ++ filter (fun '(_, ann) => ann.(clo) ==b ck) l0) Γck) as Hincl1.
        { apply Partition_Permutation in Hpart. rewrite Hpart.
          apply incl_app; [solve_incl_app|apply incl_appr, incl_filter', incl_refl]. }

        assert (NoDupMembers (l ++ filter (fun '(_, ann) => ann.(clo) ==b ck) l0)) as Hnd'.
        {  apply Partition_Permutation in Hpart. rewrite Hpart in Hnd2.
           apply NoDupMembers_app; eauto using NoDupMembers_app_l, NoDupMembers_app_r, NoDupMembers_filter.
           intros ? Hinm1 Hinm2.
           eapply NoDupMembers_app_InMembers in Hnd2; eauto. eapply Hnd2, filter_InMembers'; eauto. }

        assert ( Forall (fun '(x, _) => exists vs : Stream svalue, sem_var Hi x vs /\ abstract_clock vs ≡ abstract_clock sc)
                        (filter (fun '(_, ann) => ann.(clo) ==b ck) l0 ++ l)) as Hsc'.
        { eapply Forall_forall; intros (?&?) Hin.
          rewrite Permutation_app_comm in Hincl1.
          edestruct Hsc as ((?&Hv&Hck)&_). 1:apply Hincl1 in Hin; eauto with senv.
          do 2 esplit; eauto.
          assert (clo a = ck); subst. 2:eapply sem_clock_det; eauto.
          apply in_app_iff in Hin as [Hin|Hin].
          - apply filter_In in Hin as (?&Hin'). rewrite equiv_decb_equiv in Hin'; inv Hin'; auto.
          - assert (Is_defined_in i0 (Bswitch ec branches)) as Hdef.
            { eapply vars_defined_Is_defined_in.
              eapply Partition_Forall1, Forall_forall in Hpart; eauto; simpl in *.
              apply PSF.mem_2; auto. }
            inv Hdef. simpl_Exists. simpl_Forall.
            destruct s. eapply wc_scope_Is_defined_in, InMembers_In in H22 as (?&?); eauto.
            2:{ intros; simpl_Exists; simpl_Forall; eauto using wc_block_Is_defined_in. }
            assert (HasClock Γ' i0 x4.(clo)) as Hck' by eauto with senv.
            eapply H14 in Hck' as (Hin'&?); subst. inv Hin'.
            eapply NoDupMembers_det with (t:=a) in H24; eauto. congruence.
            eapply Hincl1; auto using in_or_app.
        }

        assert (sem_exp_ck G2 (Hi', Hl) bs' (subclock_exp bck sub ec) [sc]) as Hsem.
        { eapply subclock_exp_sem; eauto. }
        assert (Hcond:=H0). eapply cond_eq_sem in H0 as (Hi1&Href1&Hv1&Hsem1&Hdom1&Hdomub1&Hsc1); eauto.
        assert (Hni:=H4). eapply new_idents_sem with (bs':=bs') (Hl:=Hl) in H4 as (Hi2&Href2&Hdom2&Hdomub2&Hv2&Hsc2); eauto with fresh.
        2:eapply Sem.sem_clock_refines; eauto.
        2:take (wt_streams [_] [_]) and inv it; auto.

        assert (forall x, InMembers x (l ++ filter (fun '(_, ann) => ann.(clo) ==b ck) l0) ->
                     Forall (fun '(_, sub, _, _) => Env.In x sub) subs) as Hinsubs.
        { intros ? Hinm. eapply mmap_values, Forall2_ignore1 in Hni; eauto.
          eapply Forall_impl; [|eapply Hni]; intros (((?&?)&?)&?) ((?&?)&?&?&?&?); repeat inv_bind.
          apply Env.In_from_list, fst_InMembers.
          erewrite map_map, map_ext, map_app, 2 new_idents_old, <-map_app; eauto. 2:intros ((?&?)&(?&?)); auto.
          now rewrite <-fst_InMembers, Permutation_app_comm. }

        constructor. eapply Sscope with (Hi':=Hi2); eauto. 6:repeat rewrite Forall_app; repeat split.
        + intros ?? Hsemv Hnin. rewrite fst_InMembers, map_app, in_app_iff, not_or' in Hnin. destruct Hnin as (Hnin1&Hnin2).
          eapply Sem.sem_var_refines'. 3:eauto. 2:etransitivity; eauto.
          eapply Sem.sem_var_In, Hdom2 in Hsemv as [Hsemv|Hin]; try (apply fst_InMembers in Hin; contradiction).
          apply Hdom1 in Hsemv as [|Hin]; auto.
          exfalso. eapply Hnin1. solve_In.
        + clear - Hdom1 Hdom2. intros.
          rewrite Hdom2, Hdom1, InMembers_app, 3 fst_InMembers.
          split; intros; repeat (take (_ \/ _) and destruct it; destruct_conjs); auto.
          * right; left. solve_In.
          * left; right; solve_In.
        + reflexivity.
        + intros. apply in_app_iff in H0 as [|]; simpl_In.
        + simpl_app. apply sc_vars_app.
          * intros * Hinm1 Hinm2. rewrite fst_InMembers in Hinm1, Hinm2.
            assert (st_valid_after x2 switch aft) as Hvalid'.
            { eapply mmap_st_valid; eauto. simpl_Forall; repeat inv_bind.
              do 2 (eapply new_idents_st_valid; [|eauto]). auto.
              eapply cond_eq_st_valid; eauto. }
            apply st_valid_NoDup, NoDup_app_l in Hvalid'.
            apply new_idents_st_ids' in Hni. apply cond_eq_st_ids in Hcond.
            rewrite Hni, Hcond in Hvalid'. simpl_app. simpl_In.
            eapply NoDup_app_r, NoDup_app_In in Hvalid'. 2:solve_In.
            eapply Hvalid'. solve_In. auto.
          * eapply sc_vars_refines; eauto. reflexivity.
            erewrite map_map, map_ext; eauto. intros (?&?&?); auto.
          * clear - Hsc2. erewrite flat_map_concat_map in *.
            erewrite concat_map, map_map, map_ext; eauto.
            intros; destruct_conjs; auto. erewrite map_map, map_ext; eauto.
            intros; destruct_conjs; auto.
        + simpl_Forall.
          assert (Is_defined_in i0 (Bswitch ec branches)) as Hdef.
          { eapply vars_defined_Is_defined_in.
            eapply Partition_Forall1, Forall_forall in Hpart; eauto; simpl in *.
            apply PSF.mem_2; auto. }
          inv Hdef. simpl_Exists. simpl_Forall.
          destruct s. eapply wc_scope_Is_defined_in, InMembers_In in H19 as (?&Hin1); eauto.
          2:{ intros; simpl_Exists; simpl_Forall; eauto using wc_block_Is_defined_in. }
          assert (HasClock Γ' i0 x.(clo)) as Hck by eauto with senv.
          eapply H14 in Hck as (Hin'&?); subst. inv Hin'.
          edestruct Hsc as ((?&Hv&Hck)&_); eauto with senv.
          eapply merge_defs_sem; eauto using Sem.sem_var_refines.
          * rewrite <-H8.
            replace (map fst (map _ subs)) with (map fst branches). reflexivity.
            clear - Hni. apply mmap_values in Hni.
            induction Hni as [|(?&?) (((?&?)&?)&?)]; simpl; auto.
            destruct H as (?&?&?); repeat inv_bind.
            f_equal; auto.
          * take (wt_streams [_] [_]) and inv it; auto.
          * eapply sem_clock_det in Hsemck; eauto.
          * rewrite Forall_map. eapply Forall_impl_In; [|eapply Hv2]; intros (((?&?)&?)&?) Hinxs Hsub'.
            eapply Hsub'; eauto.
            assert (Env.In i0 t0) as Henvin.
            { eapply Forall_forall in Hinsubs; eauto. 2:eapply InMembers_app; left; eauto using In_InMembers.
              simpl in *; auto. }
            inv Henvin. unfold rename_var, Env.MapsTo in *.
            rewrite H23 in *; auto.
        + eapply CS.mmap2_values' in H18. eapply mmap_values, Forall3_ignore3' with (zs:=x3) in Hni.
          2:{ eapply Forall3_length in H18 as (?&?); congruence. }
          2:eapply mmap_length in Hni; eauto.
          2:{ eapply mmap_st_valid, cond_eq_st_valid; eauto.
              simpl_Forall; repeat inv_bind.
              do 2 (eapply new_idents_st_valid; [|eauto]); eauto. }
          2:{ intros (?&?) (((?&?)&?)&?) ?????; repeat inv_bind.
              eapply switch_scope_st_valid; eauto. }
          2:{ intros (?&?) (((?&?)&?)&?) ????; repeat inv_bind.
              eapply switch_scope_st_follows; eauto. }
          eapply Forall3_Forall3 in Hni; eauto. clear H15.
          eapply Forall_concat, Forall_forall; intros ? Hin1.
          eapply Forall3_ignore12, Forall_forall in Hni as ((?&?)&?&Hin2&Hin3&(?&?&Hvalid'&Hfollows'&?)&?&?&?); eauto; repeat inv_bind.
          constructor.
          *{ constructor. simpl_Forall. destruct s.
             assert (wc_scope (fun Γ => Forall (wc_block G1 Γ)) G1 (map (fun '(x, ann) => (x, ann_with_clock ann Cbase)) (l ++ filter (fun '(_, ann) => ann.(clo) ==b ck) l0)) (Scope l2 l3 l4)) as Hwc'.
             { eapply wc_scope_incl; [| |eauto|].
               + intros * Hin. apply H14 in Hin as (Hin&?); subst.
                 inv Hin; econstructor; solve_In.
                 2:{ apply Partition_Permutation in Hpart. rewrite Hpart in H22.
                     rewrite in_app_iff in *. destruct H22; eauto; right; solve_In.
                     apply equiv_decb_refl. }
                 simpl; eauto. auto.
               + intros * Hin. apply H16, Hnl1 in Hin as [].
               + intros; simpl in *; simpl_Forall; eauto using wc_block_incl. }

             eapply switch_scope_sem
               with (Hi:=FEnv.restrict (ffilter_hist e sc Hi) (map fst (l ++ filter (fun '(_, ann) => ann.(clo) ==b ck) l0)))
                    (Hi':=Hi2)
                    (Γty:=Γty)
                    (bs:=ffilterb e sc bs) in H0; eauto.
             - intros * Hla. eapply Hnl1. inv Hla. simpl_In.
               eapply IsLast_incl; eauto with senv.
             - intros ? Hin. apply Env.In_from_list in Hin.
               rewrite fst_InMembers in Hin. rewrite fst_InMembers.
               erewrite map_map, map_ext, map_app, <-2 new_idents_old, <-map_app, Permutation_app_comm; eauto.
               erewrite map_map, map_ext in Hin; eauto. intros ((?&?)&(?&?)); auto. intros (?&?); auto.
             - intros ??? Hfind Hv. eapply Sem.sem_var_restrict_inv in Hv as (?&Hv).
               eapply sem_var_ffilter_inv in Hv as (?&Hv&Heq).
               rewrite Heq; eauto.
             - intros ?? Hfind Hv. eapply Sem.sem_var_restrict_inv in Hv as (Hin&_). exfalso.
               apply Env.Props.P.F.not_find_in_iff in Hfind. apply Hfind, Env.In_from_list.
               rewrite fst_InMembers.
               erewrite map_app, <-2 new_idents_old, <-map_app, Permutation_app_comm in Hin; eauto.
               erewrite map_map, map_ext; eauto. intros ((?&?)&(?&?)); auto.
             - etransitivity; [|eauto].
               erewrite map_map, map_ext. apply incl_map; auto. intros (?&?); auto.
             - clear - Hnd'.
               erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; auto. intros (?&?); auto.
             - simpl_Forall; auto.
             - eapply FEnv.restrict_dom_ub', FEnv.dom_ub_map; eauto.
             - split; intros * Hck.
               2:{ intros Hca. exfalso. inv Hca. simpl_In. apply Hincl1 in Hin.
                   eapply Hnl1; econstructor; eauto. }
               inv Hck. simpl_In. eapply Forall_forall in Hsc'. 2:rewrite Permutation_app_comm; eauto.
               edestruct Hsc' as (vs&Hv&Hck).
               exists (ffilterv e sc vs). split.
               + eapply Sem.sem_var_restrict, sem_var_ffilter; eauto.
                 apply in_map_iff. do 2 esplit; eauto. auto.
               + constructor. rewrite ac_ffilter, Hck.
                 apply ffilterb_both_slower; eauto using ac_slower, sc_slower, ac_aligned.
             - eapply FEnv.dom_ub_incl; eauto. apply incl_app; [solve_incl_app|apply incl_appr].
               apply incl_map, st_follows_incl; auto.
             - eapply sem_clock_Con_filter; eauto.
               + take (wt_streams [_] [_]) and inv it; auto.
               + eapply sc_slower; eauto using ac_aligned.
               + eapply Sem.sem_var_refines; eauto.
               + eapply Sem.sem_clock_refines; [|eauto]. etransitivity; eauto.
             - erewrite map_ext, <-map_map. eapply sem_scope_restrict1; eauto.
               3:intros; destruct_conjs; auto.
               + unfold wc_env. simpl_Forall. simpl_In. constructor.
               + eapply sem_scope_change_lasts with (P_nolast:=Forall (nolast_block)); [| |eauto with lclocking|eauto|].
                 * inv H1. constructor; auto. simpl_Forall; eauto using noauto_nolast.
                 * intros * Hnl. eapply Hnl1; eauto.
                 * eapply wx_scope_incl with (P_wx:=fun Γ => Forall (wx_block Γ)), wc_scope_wx_scope. 5:eauto. all:eauto.
                   1,2:intros * Hin; (try eapply IsVar_incl; try eapply IsLast_incl; eauto).
                   -- inv Hin. apply fst_InMembers in H22. simpl_In.
                      econstructor; eauto using In_InMembers.
                   -- inv Hin. simpl_In.
                      econstructor; eauto.
                   -- intros; simpl in *; simpl_Forall. eapply wx_block_incl; eauto.
                   -- intros; simpl in *; simpl_Forall; eauto with lclocking.
                 * destruct H19 as (Hfilter1&Hfilter2).
                   apply filter_hist_ffilter_hist in Hfilter1.
                   eapply sem_scope_refines1; eauto.
                 * intros; simpl in *; simpl_Forall; eauto using sem_block_change_lasts.
             - intros; simpl in *.
               eapply switch_blocks_sem'; eauto.
           }
          *{ simpl_Forall.
             assert (InMembers i0 (filter (fun '(_, ann) => ann.(clo) ==b ck) l0)) as Hin.
             { eapply new_idents_In_inv in H22 as (?&?&?); eauto using In_InMembers. }
             apply InMembers_In in Hin as (?&Hin).
             eapply Forall_forall in Hsc'; eauto using in_or_app; simpl in *. destruct Hsc' as (?&Hv&Heq).
             eapply when_free_sem; eauto.
             - eapply Sem.sem_var_refines; eauto.
             - take (wt_streams [_] [_]) and inv it; auto.
             - eapply Sem.sem_var_refines; [|eapply rename_var_sem; eauto].
               etransitivity; eauto.
             - eapply Hv2; eauto.
               apply Env.find_In_from_list.
               + apply in_map_iff; do 2 esplit; eauto using in_or_app. auto.
               + erewrite fst_NoDupMembers, map_map, map_ext, map_app, 2 new_idents_old, <-map_app, <-fst_NoDupMembers. 2,3:eauto.
                 now rewrite Permutation_app_comm.
                 intros ((?&?)&(?&?)); auto.
           }
        + rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
          constructor. eapply sem_equation_refines; eauto.

      - (* local *)
        constructor.
        eapply switch_scope_sem; eauto.
        intros. eapply switch_blocks_sem'; eauto.
        Transparent switch_scope.
    Qed.

  End switch_block.

  Lemma switch_node_sem G1 G2 : forall f n ins outs,
      global_sem_refines G1 G2 ->
      CommonTyping.wt_program wt_node {| types := types G1; nodes := n :: nodes G1 |} ->
      wc_global (Global G1.(types) (n::G1.(nodes))) ->
      Ordered_nodes (Global G1.(types) (n::G1.(nodes))) ->
      Ordered_nodes (Global G2.(types) ((switch_node n)::G2.(nodes))) ->
      sem_node_ck (Global G1.(types) (n::G1.(nodes))) f ins outs ->
      sem_node_ck (Global G2.(types) ((switch_node n)::G2.(nodes))) f ins outs.
  Proof with eauto.
    intros * HGref Hwt Hwc Hord1 Hord2 Hsem.

    inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
    - erewrite find_node_now in Hfind; eauto. inv Hfind.
      (* The semantics of the block can be given according to G only *)
      eapply sem_block_ck_cons in H3; eauto. rename H3 into Hblksem.
      2:{ inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }

      replace {| types := types G1; nodes := nodes G1 |} with G1 in Hblksem by (destruct G1; auto).
      pose proof (n_nodup n0) as (Hnd1&Hnd2).
      pose proof (n_good n0) as (Hgood1&Hgood2&_).
      inv Hwc. destruct H4 as (Hwc&_); simpl in Hwc.
      destruct H5 as (Hdom1&Hsc1).
      inv Hwt. destruct H4 as (Hwt&_); simpl in Hwt.
      eapply switch_block_sem in Hblksem...
      17:eapply surjective_pairing.
      eapply Snode with (H:=H); simpl... 1-19:repeat rewrite map_fst_idty in *; auto.
      + erewrite find_node_now...
      + eauto.
      + eauto.
      + apply sem_block_ck_cons'; simpl; auto.
        2:{ eapply find_node_not_Is_node_in in Hord2.
            2:erewrite find_node_now; eauto. eauto. }
        destruct (switch_block _ _ _ _ _) as (?&?) eqn:Hil. destruct G2; rewrite Hil...
      + simpl. constructor; simpl; auto.
      + apply senv_of_inout_NoLast.
      + intros ? Hin. apply Env.Props.P.F.empty_in_iff in Hin. inv Hin.
      + intros * Hfind. rewrite Env.gempty in Hfind. congruence.
      + eapply init_st_valid; eauto using switch_not_in_auto_prefs, PS_For_all_empty.
      + reflexivity.
      + apply NoDupMembers_map; auto. intros; destruct_conjs; auto.
      + apply NoDupMembers_map; auto. intros; destruct_conjs; auto.
      + now rewrite map_fst_senv_of_inout.
      + eapply FEnv.dom_ub_incl; eauto using FEnv.dom_dom_ub. solve_incl_app.
      + eapply FEnv.dom_ub_incl; eauto using FEnv.dom_dom_ub. solve_incl_app.
      + constructor. reflexivity.
      + apply n_syn.
      + now rewrite map_fst_senv_of_inout.
      + destruct Hwt as (?&?&?&?), G1; auto.
      + destruct Hwc as (?&?&?), G1; auto.
    - erewrite find_node_other in Hfind...
      eapply sem_node_ck_cons'...
      destruct G2; apply HGref.
      econstructor...
      destruct G1; eapply sem_block_ck_cons...
      eapply find_node_later_not_Is_node_in in Hord1...
  Qed.

  Lemma switch_global_refines : forall G,
      wt_global G ->
      wc_global G ->
      global_sem_refines G (switch_global G).
  Proof with eauto using wc_global_Ordered_nodes.
    intros (enms&nds) (_&Hwt). revert Hwt.
    induction nds; intros * Hwt Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      eapply Clocking.switch_global_wc, wc_global_Ordered_nodes in Hwc' ;
        unfold switch_global in Hwc'; simpl in Hwc'.
      apply global_sem_ref_cons with (f:=n_name a)...
      + inv Hwc. inv Hwt. eapply IHnds...
      + intros ins outs Hsem; simpl in *.
        change enms with ((Global enms (map switch_node nds)).(types)).
        eapply switch_node_sem with (G1:=Global enms nds)...
        inv Hwt; inv Hwc...
  Qed.

  Theorem switch_global_sem : forall G f ins outs,
      wt_global G ->
      wc_global G ->
      sem_node_ck G f ins outs ->
      sem_node_ck (switch_global G) f ins outs.
  Proof.
    intros.
    eapply switch_global_refines in H; eauto.
    specialize (H f ins outs); auto.
  Qed.

End CSCORRECTNESS.

Module CSCorrectnessFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS Ids Op OpAux)
       (CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Senv  : STATICENV Ids Op OpAux Cks)
       (Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Ty    : LTYPING Ids Op OpAux Cks Senv Syn)
       (Clo   : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Lord  : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
       (LCS   : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Clo Lord CStr Sem)
       (CS    : CLOCKSWITCH Ids Op OpAux Cks Senv Syn)
       <: CSCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Ty Clo Lord Sem LCS CS.
  Include CSCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Ty Clo Lord Sem LCS CS.
End CSCorrectnessFun.
