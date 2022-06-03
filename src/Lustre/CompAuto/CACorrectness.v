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
From Velus Require Import StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LSemantics Lustre.LClockedSemantics.
From Velus Require Import Lustre.CompAuto.CompAuto Lustre.CompAuto.CAClocking.
From Velus Require Import Lustre.SubClock.SCCorrectness.

Module Type CACORRECTNESS
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
       (Import CA  : COMPAUTO Ids Op OpAux Cks Senv Syn).

  Module Import SCC := SCCorrectnessFun Ids Op OpAux Cks CStr Senv Syn Cl Ord Sem LCS SC. Import SC.

  Import Fresh Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  Definition stres_proj1 := stres_st.
  Definition stres_proj2 (stres : Stream (synchronous (enumtag * bool))) :=
    Streams.map (fun x => match x with
                       | absent => absent
                       | present (_, b) => present (Venum (if (b : bool) then OpAux.true_tag else OpAux.false_tag)) end) stres.

  Add Parametric Morphism : stres_proj2
      with signature @EqSt _ ==> @EqSt _
        as stres_proj2_EqSt.
  Proof.
    cofix CoFix; intros.
    inv H; constructor; simpl; eauto.
    now rewrite H0.
  Qed.

  Fact ac_stres_proj1 : forall xs,
      abstract_clock (stres_proj1 xs) ≡ abstract_clock xs.
  Proof.
    intros *.
    apply ntheq_eqst; intros. rewrite 2 ac_nth. setoid_rewrite Str_nth_map.
    destruct (xs # n) as [|(?&?)]; auto.
  Qed.

  Fact ac_stres_proj2 : forall xs,
      abstract_clock (stres_proj2 xs) ≡ abstract_clock xs.
  Proof.
    intros *.
    apply ntheq_eqst; intros. rewrite 2 ac_nth. setoid_rewrite Str_nth_map.
    destruct (xs # n) as [|(?&?)]; auto.
  Qed.

  Fact stres_proj1_const : forall bs x r,
      stres_proj1 (const_stres bs (x, r)) ≡ enum bs x.
  Proof.
    intros *.
    apply ntheq_eqst; intros. repeat setoid_rewrite Str_nth_map.
    rewrite enum_nth'. destruct (bs # n); auto.
  Qed.

  Fact stres_proj2_const : forall bs x r,
      stres_proj2 (const_stres bs (x, r)) ≡ enum bs (if r then true_tag else false_tag).
  Proof.
    intros *.
    apply ntheq_eqst; intros. repeat setoid_rewrite Str_nth_map.
    rewrite enum_nth'. destruct (bs # n); auto.
  Qed.

  Fact stres_proj1_fselect : forall e k stres xs,
      stres_proj1 (fselect absent e k stres xs) ≡ fselectv e k stres (stres_proj1 xs).
  Proof.
    intros *. unfold fselectv, fselect.
    apply ntheq_eqst; intros n.
    setoid_rewrite Str_nth_map. rewrite 2 mask_nth, 2 ffilter_nth.
    repeat setoid_rewrite Str_nth_map.
    destruct (_ =? _), (stres # n) as [|(?&?)]; auto.
    destruct (_ ==b _); auto.
  Qed.

  Fact stres_proj2_fselect : forall e k stres xs,
      stres_proj2 (fselect absent e k stres xs) ≡ fselectv e k stres (stres_proj2 xs).
  Proof.
    intros *. unfold fselectv, fselect.
    apply ntheq_eqst; intros n.
    setoid_rewrite Str_nth_map. rewrite 2 mask_nth, 2 ffilter_nth.
    repeat setoid_rewrite Str_nth_map.
    destruct (_ =? _), (stres # n) as [|(?&?)]; auto.
    destruct (_ ==b _); auto.
  Qed.

  Import Permutation.

  Section sem_node.
    Variable G1 : @global nolast_block last_prefs.
    Variable G2 : @global noauto_block auto_prefs.

    Hypothesis HwcG : wc_global G1.
    Hypothesis Href : global_sem_refines G1 G2.

    Ltac auto_block_simpl_Forall :=
      repeat
        simpl_Forall;
        (match goal with
         | Hmap: mmap2 _ _ _ = (?blks', _, _), Hin:In _ ?blks' |- _ =>
           eapply mmap2_values_valid, Forall3_ignore13 in Hmap;
           eauto using auto_block_st_valid; simpl_Forall
         | _ => idtac
         end; repeat inv_bind);
        eauto.

    Fact case_choose_first1 : forall e r bs vs bs' stres,
        bools_of vs bs' ->
        abstract_clock vs ≡ bs ->
        abstract_clock stres ≡ bs ->
        case vs [(true_tag, enum bs e); (false_tag, stres_proj1 stres)] None (stres_proj1 (choose_first (const_stres bs' (e, r)) stres)).
    Proof.
      intros * Hbools Hac1 Hac2.
      apply case_spec; intros; simpl.
      apply eqst_ntheq with (n:=n) in Hac1; rewrite ac_nth in Hac1.
      apply eqst_ntheq with (n:=n) in Hac2; rewrite ac_nth in Hac2.
      eapply bools_of_nth with (n:=n) in Hbools as [(Hv&Hb)|[(Hv&Hb)|(Hv&Hb)]];
        [right;left|right;left|left]; setoid_rewrite Hv in Hac1;
          destruct (stres # n) as [|(?&?)] eqn:Hst; try congruence.
      - do 2 esplit. repeat (split; eauto).
        + repeat constructor; simpl.
          * rewrite enum_nth', <-Hac1; congruence.
          * setoid_rewrite Str_nth_map. rewrite Hst; congruence.
        + left. split; auto.
          rewrite enum_nth', <-Hac1; eauto.
        + setoid_rewrite Str_nth_map. rewrite choose_first_nth. setoid_rewrite Str_nth_map.
          rewrite Hb; auto.
                - do 2 esplit. repeat (split; eauto).
        + repeat constructor; simpl.
          * rewrite enum_nth', <-Hac1; congruence.
          * setoid_rewrite Str_nth_map. rewrite Hst; congruence.
        + right; left. split; auto.
          setoid_rewrite Str_nth_map. rewrite Hst; eauto.
        + setoid_rewrite Str_nth_map. rewrite choose_first_nth. setoid_rewrite Str_nth_map.
          rewrite Hb, Hst; auto.
      - repeat split; auto.
        + repeat constructor; simpl.
          * rewrite enum_nth', <-Hac1; congruence.
          * setoid_rewrite Str_nth_map. rewrite Hst; congruence.
        + setoid_rewrite Str_nth_map. rewrite choose_first_nth. setoid_rewrite Str_nth_map.
          rewrite Hb. rewrite Hst; auto.
    Qed.

    Fact case_choose_first2 : forall e r bs vs bs' stres,
        bools_of vs bs' ->
        abstract_clock vs ≡ bs ->
        abstract_clock stres ≡ bs ->
        case vs [(true_tag, enum bs (if (r : bool) then true_tag else false_tag));
                (false_tag, stres_proj2 stres)] None (stres_proj2 (choose_first (const_stres bs' (e, r)) stres)).
    Proof.
      intros * Hbools Hac1 Hac2.
      apply case_spec; intros; simpl.
      apply eqst_ntheq with (n:=n) in Hac1; rewrite ac_nth in Hac1.
      apply eqst_ntheq with (n:=n) in Hac2; rewrite ac_nth in Hac2.
      eapply bools_of_nth with (n:=n) in Hbools as [(Hv&Hb)|[(Hv&Hb)|(Hv&Hb)]];
        [right;left|right;left|left]; setoid_rewrite Hv in Hac1;
          destruct (stres # n) as [|(?&?)] eqn:Hst; try congruence.
      - do 2 esplit. repeat (split; eauto).
        + repeat constructor; simpl.
          * rewrite enum_nth', <-Hac1; congruence.
          * setoid_rewrite Str_nth_map. rewrite Hst; congruence.
        + left. split; auto.
          rewrite enum_nth', <-Hac1; eauto.
        + setoid_rewrite Str_nth_map. rewrite choose_first_nth. setoid_rewrite Str_nth_map.
          rewrite Hb; auto.
      - do 2 esplit. repeat (split; eauto).
        + repeat constructor; simpl.
          * rewrite enum_nth', <-Hac1; congruence.
          * setoid_rewrite Str_nth_map. rewrite Hst; congruence.
        + right; left. split; auto.
          setoid_rewrite Str_nth_map. rewrite Hst; eauto.
        + setoid_rewrite Str_nth_map. rewrite choose_first_nth. setoid_rewrite Str_nth_map.
          rewrite Hb, Hst; auto.
      - repeat split; auto.
        + repeat constructor; simpl.
          * rewrite enum_nth', <-Hac1; congruence.
          * setoid_rewrite Str_nth_map. rewrite Hst; congruence.
        + setoid_rewrite Str_nth_map. rewrite choose_first_nth. setoid_rewrite Str_nth_map.
          rewrite Hb. rewrite Hst; auto.
    Qed.

    Lemma init_state_exp_sem Γ : forall Hi Hl bs tx ck bs' trans oth stres0,
        Forall (fun '(e, _) => wc_exp G1 Γ e /\ clockof e = [Cbase]) trans ->
        sem_clock Hi bs ck bs' ->
        sc_vars Γ (Hi, Hl) bs' ->
        sem_transitions_ck G1 (Hi, Hl) bs' (List.map (fun '(e, t) => (e, (t, false))) trans) (oth, false) stres0 ->
        sem_exp_ck G2 (Hi, Hl) bs (init_state_exp tx ck trans oth) [stres_proj1 stres0].
    Proof.
      induction trans as [|(?&?)]; intros * Hwc Hck Hsc Hsem; inv Hwc; inv Hsem; destruct_conjs.
      - rewrite H0, stres_proj1_const.
        eapply add_whens_enum_sem; eauto.
      - econstructor.
        + eapply subclock_exp_sem; eauto. intros * Hfind. rewrite Env.gempty in Hfind; inv Hfind.
        + econstructor; eauto using add_whens_enum_sem.
          econstructor; eauto. 2,3:simpl; repeat constructor; eauto.
          constructor; eauto.
        + simpl. repeat constructor.
          rewrite H13. eapply case_choose_first1; eauto.
          * eapply sc_exp in H8; eauto.
            take (clockof _ = _) and rewrite it in H8; simpl_Forall. inv H4.
            now symmetry.
          * eapply sc_transitions in H12; eauto. simpl_Forall; eauto.
    Qed.

    Lemma trans_exp_sem Γ : forall Hi Hl bs tx (* ck *) (* bs' *) trans oth stres,
        Forall (fun '(e, _) => wc_exp G1 Γ e /\ clockof e = [Cbase]) trans ->
        sc_vars Γ (Hi, Hl) bs ->
        sem_transitions_ck G1 (Hi, Hl) bs trans (oth, false) stres ->
        exists vss, Forall2 (sem_exp_ck G2 (Hi, Hl) bs) (trans_exp tx trans oth) vss
               /\ concat vss = [stres_proj1 stres; stres_proj2 stres].
    Proof.
      induction trans as [|(?&?)]; intros * Hwc Hsc Hsem; inv Hwc; inv Hsem; destruct_conjs.
      - exists [[stres_proj1 stres]; [stres_proj2 stres]]. split; auto.
        constructor; [|constructor]; auto.
        1,2:constructor.
        + rewrite <-stres_proj1_const.
          setoid_rewrite H0; reflexivity.
        + apply ntheq_eqst; intro. apply eqst_ntheq with (n:=n) in H0.
          setoid_rewrite Str_nth_map. rewrite H0, enum_nth'. setoid_rewrite Str_nth_map.
          destruct (bs # n); auto.
      - assert (Htrans:=H11). eapply IHtrans in H11 as (?&Hsem&Hconcat); eauto.
        do 2 esplit. constructor; auto.
        econstructor; eauto using sem_ref_sem_exp.
        3:simpl; rewrite app_nil_r; reflexivity.
        + econstructor. 1,2:econstructor; eauto. 2:econstructor; eauto.
          1,2:constructor; reflexivity.
          2,3:simpl. 3:do 3 (constructor; auto).
          2:{ rewrite Hconcat. do 3 (constructor; auto). }
          repeat constructor.
        + eapply sc_exp in H5; eauto.
          take (clockof _ = _) and rewrite it in H5; simpl_Forall. inv H4.
          eapply sc_transitions in Htrans; eauto.
          simpl. repeat constructor.
          * rewrite H12. apply case_choose_first1; eauto.
            now symmetry.
          * rewrite H12. apply case_choose_first2; eauto.
            now symmetry.
    Qed.

    Lemma sem_transitions_init_noreset Γ : forall ck ini oth Hi Hl bs bs' stres,
        Forall (fun '(e, _) => wc_exp G1 Γ e /\ clockof e = [Cbase]) ini ->
        sem_clock Hi bs ck bs' ->
        sc_vars Γ (Hi, Hl) bs' ->
        sem_transitions_ck G1 (Hi, Hl) bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres ->
        stres_proj2 stres ≡ enum bs' false_tag.
    Proof.
      induction ini as [|(?&?)]; intros * Hwc Hck Hsc Hsem; inv Hwc; inv Hsem; destruct_conjs.
      - apply ntheq_eqst; intros n. apply eqst_ntheq with (n:=n) in H0.
        setoid_rewrite Str_nth_map. rewrite H0, enum_nth'. setoid_rewrite Str_nth_map.
        destruct (bs' # n); simpl; auto.
      - apply ntheq_eqst; intros n. apply eqst_ntheq with (n:=n) in H13.
        assert (abstract_clock vs ≡ bs') as Hac.
        { eapply sc_exp in H8; eauto. take (clockof _ = _) and rewrite it in H8; simpl_Forall.
          inv H4. now symmetry. }
        setoid_rewrite Str_nth_map. rewrite H13, enum_nth', choose_first_nth. setoid_rewrite Str_nth_map.
        eapply IHini, eqst_ntheq with (n:=n) in H12 as Hind; eauto.
        setoid_rewrite Str_nth_map in Hind. rewrite enum_nth' in Hind.
        apply eqst_ntheq with (n:=n) in Hac. rewrite ac_nth in Hac.
        destruct (bs' # n) eqn:Hb', (bs'0 # n) eqn:Hb, (stres1 # n) as [|(?&?)] eqn:Hst;
          auto; try congruence.
        apply bools_of_nth with (n:=n) in H11 as [(Hv&?)|[(?&?)|(?&?)]]; try congruence.
        setoid_rewrite Hv in Hac; congruence.
    Qed.

    Fact fby1_stres_proj1 : forall b e xs ys zs,
        fby1 (e, b) xs ys zs ->
        fby1 (Venum e) (stres_proj1 xs) (stres_proj1 ys) (stres_proj1 zs).
    Proof.
      unfold stres_proj1, stres_st.
      cofix CoFix; intros * Hfby; inv Hfby; simpl; repeat rewrite map_Cons.
      - econstructor; eauto.
      - destruct w, s. econstructor; eauto.
    Qed.

    Fact fby_stres_proj1 : forall xs ys zs,
        fby xs ys zs ->
        fby (stres_proj1 xs) (stres_proj1 ys) (stres_proj1 zs).
    Proof.
      unfold stres_proj1, stres_st.
      cofix CoFix; intros * Hfby; inv Hfby; simpl; repeat rewrite map_Cons.
      - econstructor; eauto.
      - destruct x, y. econstructor; eauto using fby1_stres_proj1.
    Qed.

    Fact fby1_stres_proj2 : forall b e xs ys zs,
        fby1 (e, b) xs ys zs ->
        fby1 (Venum (if (b : bool) then true_tag else false_tag)) (stres_proj2 xs) (stres_proj2 ys) (stres_proj2 zs).
    Proof.
      unfold stres_proj2.
      cofix CoFix; intros * Hfby; inv Hfby; simpl; repeat rewrite map_Cons.
      - econstructor; eauto.
      - destruct w, s. econstructor; eauto.
    Qed.

    Fact fby_stres_proj2 : forall xs ys zs,
        fby xs ys zs ->
        fby (stres_proj2 xs) (stres_proj2 ys) (stres_proj2 zs).
    Proof.
      unfold stres_proj2.
      cofix CoFix; intros * Hfby; inv Hfby; simpl; repeat rewrite map_Cons.
      - econstructor; eauto.
      - destruct x, y. econstructor; eauto using fby1_stres_proj2.
    Qed.

    Opaque FEnv.restrict.

    Fact bools_of_stres_proj2 : forall xs,
        bools_of (stres_proj2 xs) (stres_res xs).
    Proof.
      intros.
      apply bools_of_nth; intros n.
      repeat setoid_rewrite Str_nth_map.
      destruct (xs # n) as [|(?&?)]; auto.
      destruct b; auto.
    Qed.

    Fact bools_of_ffilter e : forall sc xs bs,
        bools_of xs bs ->
        bools_of (ffilterv e sc xs) (ffilterb e sc bs).
    Proof.
      intros * Hbools. rewrite bools_of_nth in *.
      intros n. repeat rewrite ffilterv_nth. repeat rewrite ffilterb_nth.
      specialize (Hbools n) as [(Hx&Hb)|[(Hx&Hb)|(Hx&Hb)]];
        destruct (_ ==b _); auto.
    Qed.

    Lemma fselect_mask_ffilter_hist : forall Hi e k stres,
        FEnv.Equiv (EqSt (A:=svalue))
                  (fselect_hist e k stres Hi)
                  (CStr.mask_hist k (ffilterb e (stres_st stres) (stres_res stres))
                                  (ffilter_hist e (stres_st stres) Hi)).
    Proof.
      intros.
      unfold fselect_hist, CStr.mask_hist, ffilter_hist.
      rewrite FEnv.map_map; auto using EqStrel_Reflexive.
      eapply FEnv.map_Equiv. 2:reflexivity.
      intros * Heq. now rewrite Heq.
    Qed.

    Definition default_ann : annotation :=
      Build_annotation OpAux.bool_velus_type Cbase xH None.

    Lemma auto_block_sem aft : forall blk Γty Γck Hi bs blk' tys st st',
        (forall x, IsVar Γck x -> AtomOrGensym last_prefs x) ->
        st_valid_after st auto aft ->
        NoDupLocals (List.map fst Γck) blk ->
        GoodLocals last_prefs blk ->
        nolast_block blk ->
        wt_block G1 Γty blk ->
        wc_block G1 Γck blk ->
        FEnv.dom_ub (fst Hi) (List.map fst Γck) ->
        sc_vars Γck Hi bs ->
        sem_block_ck G1 Hi bs blk ->
        auto_block blk st = (blk', tys, st') ->
        sem_block_ck G2 Hi bs blk'.
    Proof.
      induction blk using block_ind2; intros * Hat Hvalid Hnd Hgood Hnl Hwt Hwc Hdom Hsc Hsem Haut;
        inv Hnd; inv Hgood; inv Hnl; inv Hwt; inv Hwc; inv Hsem; repeat inv_bind.

      - (* equation *)
        constructor; eauto using sem_ref_sem_equation.

      - (* reset *)
        econstructor; eauto using sem_ref_sem_exp.
        intros k. specialize (H16 k).
        auto_block_simpl_Forall.
        eapply H; eauto using sc_vars_mask.
        + setoid_rewrite FEnv.dom_ub_map; auto.

      - (* switch *)
        econstructor; eauto using sem_ref_sem_exp.
        auto_block_simpl_Forall.
        2:{ intros; destruct_conjs; destruct s1; repeat inv_bind.
            eapply mmap2_st_valid; eauto. simpl_Forall; eauto using auto_block_st_valid. }
        destruct H21 as (Hfilter1&Hfilter2). apply filter_hist_ffilter_hist in Hfilter1.
        assert (sem_clock t bs ck (abstract_clock sc)) as Hsemck.
        { eapply sc_exp in H15; eauto.
          take (clockof _ = _) and rewrite it in H15; simpl_Forall; auto. }
        do 2 esplit.
        1:{ instantiate (1:=(_,_)). split; simpl in *; eauto.
            eapply filter_hist_restrict_ac with (xs:=List.map fst Γ').
            intros * Hin Hv; simpl_In. edestruct H14 as (?&Hbase); eauto with senv.
            destruct Hsc as ((?&Hv'&Hsemck')&_); eauto.
            eapply sem_var_det in Hv; eauto. rewrite <-Hv.
            eapply sem_clock_det in Hsemck; eauto.
        }
        inv H1. inv H2. inv H3. inv H11.
        eapply sem_scope_refines1, sem_scope_restrict1 in H23. 3,4:eauto.
        2:{ eapply Forall_forall; intros; simpl_In. edestruct H14 as (?&Hbase); eauto with senv.
            rewrite Hbase. constructor. }
        inv H17. inv H23.
        assert (incl (List.map fst Γ') (List.map fst Γck)) as Hincl.
        { intros ? Hin; simpl_In. edestruct H14 as (Hck'&?); eauto with senv.
          inv Hck'. solve_In. }
        repeat inv_bind. econstructor; eauto.
        1:{ intros. simpl_Forall. edestruct H42; eauto; destruct_conjs.
            eauto 8 using sem_ref_sem_exp. }
        auto_block_simpl_Forall.
        eapply H with (Γck:=Γ'++_); eauto.
        + intros * Hin.
          inv Hin. rewrite InMembers_app, 2 fst_InMembers in H22. destruct H22; simpl_In.
          * eapply Hat. edestruct H14; eauto with senv.
          * simpl_Forall; auto.
        + eapply NoDupLocals_incl; eauto.
          intros ? Hin; simpl_In. rewrite in_app_iff in *. destruct Hin0 as [|]; simpl_In.
          * left. eapply Hincl. solve_In.
          * right. solve_In.
        + rewrite map_app, map_fst_senv_of_locs.
          eapply local_hist_dom_ub; eauto using FEnv.restrict_dom_ub.
        + eapply sc_vars_app; eauto.
          * intros * Hinm1 Hinm2. rewrite fst_InMembers in Hinm1. rewrite InMembers_senv_of_locs in Hinm2.
            eapply H30; eauto.
          * eapply sc_vars_refines with (Hl:=t0), sc_vars_restrict, sc_vars_morph, sc_vars_ffilter, Hsc; try reflexivity; eauto.
            2:{ simpl_Forall. simpl_In.
                edestruct H14 as (?&Hbase); eauto with senv; subst. rewrite Hbase; constructor. }
            2:split; simpl in *; [reflexivity|now symmetry].
            eapply local_hist_dom_ub_refines; eauto using FEnv.dom_ub_incl, FEnv.restrict_dom_ub.

      - (* automaton (weak) *)
        assert (length x1 = length states) as Hlen
            by (eapply generate_constructors_length; eauto).
        assert (st_valid_after x2 auto aft) as Hvalid' by eauto with fresh.
        destruct Hi as (Hi&Hl).
        assert (Forall (fun id => ~IsVar Γck id) [x3;x5;x7;x9]) as Hnin1.
        { simpl_Forall; simpl in *. intros Hv.
          apply Hat in Hv.
          repeat (take (CA.fresh_ident _ = _) and eapply fresh_ident_prefixed in it as (?&?&?); subst).
          take (_ \/ _ \/ _) and destruct it as [|[|[|[|]]]]; subst; try eapply contradict_AtomOrGensym in Hv; eauto using auto_not_in_last_prefs.
        }
        assert (Forall (fun id => ~ FEnv.In id Hi) [x3;x5;x7;x9]) as Hnin2.
        { simpl_Forall; simpl in *. intros Henvin. eapply Hdom, fst_InMembers in Henvin; eauto.
          assert (IsVar Γck x13) as Hv by eauto with senv.
          take (_ \/ _ \/ _) and destruct it as [|[|[|[|]]]]; subst; eauto.
        }
        assert (NoDup [x3;x5;x7;x9]) as Hnd.
        { eapply fresh_idents_NoDup; eauto 7 with fresh. }
        remember (Hi + (FEnv.of_list [(x3, stres_proj1 stres); (x5, stres_proj1 stres1);
                                      (x7, stres_proj2 stres); (x9, stres_proj2 stres1)])) as Hi'.
        assert (FEnv.refines (@EqSt _) Hi Hi') as Href'.
        { subst. intros ?? Hfind. do 2 esplit; [reflexivity|].
          apply FEnv.union2; auto. destruct (FEnv.of_list _ _) eqn:contra; auto.
          apply FEnv.of_list_find_In in contra; simpl_Forall.
          assert (FEnv.In x13 Hi) as Hin by (econstructor; eauto).
          destruct contra as [Heq|[Heq|[Heq|[Heq|[]]]]]; inv Heq; congruence. }

        assert (abstract_clock stres ≡ bs') as Hac.
        { eapply sc_transitions in H23; eauto. 3:simpl_Forall; eauto.
          - apply ac_fby1 in H24. now rewrite <-H24.
          - eapply sc_vars_subclock; eauto. }

        assert (incl (List.map fst Γ') (List.map fst Γck)) as Hinclfst.
        { intros ??. simpl_In. edestruct H17; eauto with senv.
          take (HasClock _ _ _) and inv it. solve_In. }

        constructor. eapply Sscope with (Hi':=Hi').
        + intros * Hsem Hninm. subst.
          apply sem_var_union in Hsem as [Hin|Hin]; auto.
          exfalso. inv Hin. take (FEnv.of_list _ _ = _) and apply FEnv.of_list_find_In in it as Hin; simpl_Forall.
          destruct Hin as [He|[He|[He|[He|He]]]]; inv He; auto 8.
        + subst. intros ?. rewrite FEnv.union_In, FEnv.of_list_In, 2 fst_InMembers; reflexivity.
        + reflexivity.
        + simpl. intros * [He|[He|[He|[He|He]]]]; inv He; auto.
        + split; intros * Hcka.
          2:{ intros Hla. inv Hla; simpl_In.
              destruct Hin as [He|[He|[He|[He|He]]]]; inv He; simpl in *; congruence. }
          simpl in *.
          inv Hcka; simpl in *. take (_ \/ _ \/ _) and destruct it as [He|[He|[He|[He|He]]]]; inv He; do 2 esplit; simpl.

          Local Ltac sem_new_vars :=
            subst; eapply sem_var_union3', sem_var_of_list; eauto with datatypes;
            try rewrite fst_NoDupMembers; auto.

          1,3,5,7:sem_new_vars.
          1-4:(eapply sem_clock_refines; eauto;
               try rewrite ac_stres_proj1; try rewrite ac_stres_proj2;
               try rewrite Hac; auto).
          1,2:apply ac_fby2 in H24; rewrite H24, Hac; auto.
        + repeat constructor.
          *{ econstructor. repeat constructor. 2:simpl; rewrite app_nil_r; repeat constructor.
             econstructor; repeat constructor.
             3,4,6,7:sem_new_vars.
             - eapply sem_exp_refines; [eauto|].
               eapply init_state_exp_sem; eauto using sc_vars_subclock.
             - eapply add_whens_enum_sem, sem_clock_refines; eauto.
             - repeat constructor.
               + apply fby_stres_proj1; auto.
               + eapply sem_transitions_init_noreset in H22; eauto using sc_vars_subclock.
                 rewrite <-H22.
                 apply fby_stres_proj2; auto.
           }
          *{ econstructor; simpl.
             - repeat constructor. sem_new_vars.
             - repeat constructor.
               eapply sem_transitions_ck_sem_transitions, sem_automaton_wt_state1 in H23; eauto.
               + apply SForall_forall; intros n. apply SForall_forall with (n:=n) in H23.
                 setoid_rewrite Str_nth_map. destruct (stres # n) as [|(?&?)] eqn:Hst; simpl in *; auto.
                 constructor; simpl.
                 eapply eq_ind with (P:=fun x => match x with absent => True | present (e, _) => e < length states end) in H23; [|eauto].
                 simpl in *; auto. congruence.
               + simpl_Forall; eauto.
               + rewrite <-H11. apply fst_InMembers; auto.
               + simpl_Forall; auto. inv H36; destruct_conjs; simpl_Forall; auto.
               + simpl_Forall; destruct s; destruct_conjs; intros. specialize (H25 k); destruct_conjs.
                 inv H37; destruct_conjs.
                 esplit; eauto using sem_transitions_ck_sem_transitions.
             - auto_block_simpl_Forall; eauto using fresh_ident_st_valid.
               2:{ intros; destruct_conjs; repeat inv_bind; eauto using auto_scope_st_valid2. }
               do 2 esplit. split. instantiate (1:=(_,_)). 2:simpl; reflexivity.
               1:{ simpl. apply filter_hist_restrict_ac with (xs:=x3::x5::x7::x9::List.map fst Γ').
                   intros * Hin Hsem.
                   eapply sem_var_union in Hsem; eauto.
                   simpl in *. repeat rewrite <-or_assoc in Hin.
                   destruct Hin as [Hin|Hin], Hsem as [Hsem|Hsem].
                   - exfalso. eapply sem_var_In in Hsem; eauto.
                     destruct Hin as [[[|]|]|]; subst; eauto.
                   - apply sem_var_of_list' in Hsem as (?&Heq1&[Heq|[Heq|[Heq|[Heq|Heq]]]]); inv Heq;
                       rewrite Heq1; repeat rewrite ac_stres_proj1; repeat rewrite ac_stres_proj2.
                     + reflexivity.
                     + apply ac_fby2 in H24; auto.
                     + reflexivity.
                     + apply ac_fby2 in H24; auto.
                   - rewrite ac_stres_proj1, Hac. eapply sem_clock_det; eauto.
                     simpl_In. edestruct H17; eauto with senv.
                     edestruct Hsc as ((?&Hv'&Hck)&_); eauto.
                     eapply sem_var_det in Hsem; eauto. rewrite <-Hsem; auto.
                   - exfalso. eapply Hinclfst in Hin. simpl_In.
                     assert (IsVar Γck x17) as Hv by eauto with senv.
                     apply sem_var_of_list' in Hsem as (?&_&[Heq|[Heq|[Heq|[Heq|Heq]]]]); inv Heq; eauto.
               }
               econstructor; eauto. 2:reflexivity.
               1:{ intros. split; [intros ?|intros [|[]]]; auto. }
               1:{ intros * Hin; inv Hin. }
               1:{ split; intros * Hca; inv Hca; simpl in *; take False and inv it. }
               repeat constructor. econstructor.
               + econstructor; simpl. apply sem_var_restrict; eauto with datatypes.
                 apply sem_var_ffilter. sem_new_vars.
               + apply bools_of_ffilter, bools_of_stres_proj2.
               + intros k. specialize (H25 k); destruct_conjs.
                 take (select_hist _ _ _ _ _) and destruct it as (Hsel1&Hsel2). apply select_hist_fselect_hist in Hsel1. simpl in *.
                 inv H1. inv H2. inv H3.
                 eapply sem_scope_refines2, sem_scope_restrict2 in H25. 3,4:eauto.
                 2:{ apply Forall_forall; intros; simpl_In.
                     edestruct H17 as (?&Hbase); eauto with senv. rewrite Hbase; constructor. }
                 inv H39. inv H38. inv H25. destruct_conjs. repeat inv_bind.
                 repeat constructor.
                 remember (Hi' + FEnv.of_list (List.map (fun '(x, s) => (x, fselectv e k stres s))
                                                        [(x3, stres_proj1 stres); (x5, stres_proj1 stres1); (x7, stres_proj2 stres); (x9, stres_proj2 stres1)])) as Hi''.
                 assert (FEnv.refines (@EqSt _) Hi' Hi'') as Href''.
                 { subst. intros ?? Hfind. do 2 esplit; [reflexivity|].
                   eapply FEnv.union2; eauto.
                   destruct (FEnv.of_list _ _) eqn:Hfind'; auto. exfalso.
                   apply FEnv.of_list_find_In in Hfind'; simpl_In.
                   assert (FEnv.In x14 Hi') as Hin' by (econstructor; eauto).
                   take (forall x, FEnv.In x Hi' <-> _) and rewrite it, FEnv.restrict_In in Hin'.
                   destruct Hin' as [(Hin'&_)|Hin'].
                   - apply FEnv.map_in_iff in Hin'.
                     repeat (take (_ \/ _) and destruct it; subst); inv_equalities; eauto.
                   - apply fst_InMembers in Hin'; simpl_In; simpl_Forall.
                     repeat (take (CA.fresh_ident _ = _) and apply fresh_ident_prefixed in it as (?&?&?)); subst.
                     destruct Hin as [|[|[|[|]]]]; inv_equalities; auto.
                     all:eapply contradict_AtomOrGensym; eauto using auto_not_in_last_prefs.
                 }
                 remember (maskb _ _ _) as bs''.
                 assert (sc_vars (Γ' ++ senv_of_locs locs) (Hi', Hl') bs'') as Hsc'.
                 { eapply sc_vars_app; subst; eauto.
                   - intros ??. rewrite InMembers_senv_of_locs. intros ?.
                     eapply H46, Hinclfst, fst_InMembers; eauto.
                   - subst. eapply sc_vars_refines, sc_vars_restrict, sc_vars_fselect. 6-8:eauto.
                     + eapply local_hist_dom_ub_refines with (xs:=List.map fst Γ'); eauto using FEnv.restrict_dom_ub.
                       intros * Hinm Hin. eapply H46; eauto.
                     + rewrite <-Hsel2; auto.
                     + reflexivity.
                     + simpl_Forall; simpl_In.
                       edestruct H17 as (?&Hbase); eauto with senv. rewrite Hbase; constructor.
                     + now rewrite Hac.
                 }
                 repeat constructor.
                 eapply Sscope with (Hi':=Hi'') (Hl':=Hl'). 6:constructor.
                 *{ intros. subst. unfold CStr.mask_hist; simpl.
                    eapply sem_var_union in H52 as [Hv|Hv].
                    - apply H42 in Hv; auto.
                      apply sem_var_restrict_inv in Hv as (Hin&Hv).
                      apply sem_var_fselect_inv in Hv as (?&Hv&Heq). rewrite Heq.
                      apply sem_var_mask, sem_var_restrict, sem_var_ffilter; eauto with datatypes.
                      inv Hv. econstructor; eauto. apply FEnv.union2; auto.
                      destruct (FEnv.of_list _ _) eqn:Hfind; auto. exfalso.
                      assert (FEnv.In x14 Hi) by (econstructor; eauto).
                      apply FEnv.of_list_find_In in Hfind as [|[|[|[|]]]]; inv_equalities; auto.
                    - apply sem_var_of_list' in Hv as (?&Heq&?); simpl_In. rewrite Heq.
                      apply sem_var_mask, sem_var_restrict, sem_var_ffilter.
                      + simpl. destruct Hin as [He|[He|[He|[He|He]]]]; inv He; auto.
                      + sem_new_vars.
                 }
                 *{ subst. intros ?.
                    rewrite FEnv.union_In, FEnv.of_list_In, H55.
                    setoid_rewrite FEnv.map_in_iff; simpl. rewrite 2 FEnv.restrict_In.
                    repeat setoid_rewrite FEnv.map_in_iff. rewrite FEnv.union_In, FEnv.of_list_In, fst_InMembers; simpl.
                    split; intros; repeat (take (_ \/ _) and destruct it; destruct_conjs); auto 8. now exfalso.
                   }
                 * etransitivity; [|eauto]. rewrite Hsel2.
                   unfold CStr.mask_hist; simpl. rewrite fselect_mask_ffilter_hist.
                   reflexivity.
                 * intros * Hin. simpl_Forall. congruence.
                 * subst. eapply sc_vars_refines. 3:eauto. 2:reflexivity. eauto.
                 *{ eapply sem_transitions_refines, sem_transitions_restrict with (Γ:=((x3, default_ann)::(x5, default_ann)::(x7, default_ann)::(x9, default_ann)::Γ' ++ senv_of_locs locs)) in H2; eauto.
                    2:{ simpl_Forall. eapply wx_exp_incl. 3:eauto with lclocking.
                        1,2:intros * Hv; inv Hv; econstructor; eauto using inmembers_cons with datatypes. }
                    eapply trans_exp_sem in H2 as (ss&Htranssem&Hconcat); eauto.
                    + repeat constructor. econstructor. 2:rewrite Hconcat; simpl.
                      * eapply Forall2_impl_In; [|eauto]; intros.
                        subst. eapply sem_exp_refines; [|eauto].
                        eapply FEnv.restrict_refines; eauto using EqStrel_Reflexive, EqStrel_Transitive.
                      * assert (forall x, In x [x3;x5;x7;x9] -> ~FEnv.In x Hi').
                        { intros * Hin Hinenv. inv Hinenv.
                          eapply sem_var_restrict_inv in H42 as (_&Hv).
                          - eapply sem_var_In in Hv. setoid_rewrite FEnv.map_in_iff in Hv. instantiate (1:=x14) in Hv.
                            destruct Hin as [|[|[|[|]]]]; subst; eauto.
                          - econstructor; eauto. reflexivity.
                          - intros Hinm. apply fst_InMembers in Hinm; simpl_In; simpl_Forall.
                            repeat (take (CA.fresh_ident _ = _) and eapply fresh_ident_prefixed in it as (?&?&?); subst).
                            destruct Hin as [|[|[|[|]]]]; subst; try eapply contradict_AtomOrGensym in H13; eauto using auto_not_in_last_prefs.
                        }
                        repeat constructor; subst; [rewrite stres_proj1_fselect|rewrite stres_proj2_fselect].
                        1,2:sem_new_vars; simpl in *; auto.
                    + simpl_Forall; eauto.
                    + eapply sc_vars_restrict; eauto.
                      * intros ??; simpl; eauto with datatypes.
                      * simpl_app. apply Forall_app; split; simpl_Forall.
                        -- edestruct H17 as (?&Hbase); eauto with senv. rewrite Hbase; constructor.
                        -- eapply wc_clock_incl; [|eauto]. repeat apply incl_tl. reflexivity.
                      * eapply sc_vars_refines; [eauto|reflexivity|subst;eauto].
                   }
                 *{ auto_block_simpl_Forall.
                    eapply sem_block_refines, H with (Hi:=(FEnv.restrict _ _,_)) (Γck:=Γ'++_); eauto.
                    - etransitivity; [|eauto]. eapply FEnv.restrict_refines; eauto using EqStrel_Reflexive, EqStrel_Transitive.
                    - intros * Hv. inv Hv. apply InMembers_app in H60 as [Hin|Hin]; apply fst_InMembers in Hin; simpl_In.
                      + apply Hat. edestruct H17; eauto with senv.
                      + simpl_Forall; auto.
                    - eapply NoDupLocals_incl; [|eauto]. rewrite map_app, map_fst_senv_of_locs.
                      eapply incl_appl'.
                      intros ? Hin. simpl_In.
                      edestruct H17 as (Hck&_); eauto with senv. inv Hck; solve_In.
                    - apply FEnv.restrict_dom_ub.
                    - subst. apply sc_vars_restrict; eauto.
                      + reflexivity.
                      + simpl_Forall; simpl_In.
                        apply in_app_iff in Hin as [Hin|Hin]; simpl_In; simpl_Forall; eauto.
                        edestruct H17 as (_&Hbase); eauto with senv. rewrite Hbase; constructor.
                    - eapply sem_block_restrict; subst; eauto.
                      unfold wc_env. simpl_Forall; simpl_In.
                      apply in_app_iff in Hin as [Hin|Hin]; simpl_In; simpl_Forall; eauto.
                      edestruct H17 as (_&Hbase); eauto with senv. rewrite Hbase; constructor.
                   }
            }

      - (* automaton (strong) *)
        assert (length x1 = length states) as Hlen
            by (eapply generate_constructors_length; eauto).
        assert (st_valid_after x2 auto aft) as Hvalid' by eauto with fresh.
        destruct Hi as (Hi&Hl).
        assert (Forall (fun id => ~IsVar Γck id) [x3;x5;x7;x9]) as Hnin1.
        { simpl_Forall; simpl in *. intros Hv.
          apply Hat in Hv.
          repeat (take (CA.fresh_ident _ = _) and eapply fresh_ident_prefixed in it as (?&?&?); subst).
          take (_ \/ _ \/ _) and destruct it as [|[|[|[|]]]]; subst; try eapply contradict_AtomOrGensym in Hv; eauto using auto_not_in_last_prefs.
        }
        assert (Forall (fun id => ~ FEnv.In id Hi) [x3;x5;x7;x9]) as Hnin2.
        { simpl_Forall; simpl in *. intros Henvin. eapply Hdom, fst_InMembers in Henvin; eauto.
          assert (IsVar Γck x13) as Hv by eauto with senv.
          take (_ \/ _ \/ _) and destruct it as [|[|[|[|]]]]; subst; eauto.
        }
        assert (NoDup [x3;x5;x7;x9]) as Hnd.
        { eapply fresh_idents_NoDup; eauto using fresh_ident_st_valid. }
        remember (Hi + FEnv.of_list [(x3, stres_proj1 stres); (x5, stres_proj1 stres1);
                                     (x7, stres_proj2 stres); (x9, stres_proj2 stres1)]) as Hi'.
        assert (FEnv.refines (@EqSt _) Hi Hi') as Href'.
        { subst. intros ?? Hfind. do 2 esplit; [reflexivity|].
          apply FEnv.union2; auto. destruct (FEnv.of_list _ _) eqn:contra; auto.
          apply FEnv.of_list_find_In in contra; simpl_Forall.
          assert (FEnv.In x13 Hi) as Hin by (econstructor; eauto).
          destruct contra as [Heq|[Heq|[Heq|[Heq|[]]]]]; inv Heq; congruence. }

        assert (abstract_clock stres ≡ bs') as Hac.
        { take (fby _ _ _) and apply ac_fby1 in it. rewrite <-it. apply const_stres_ac. }
        assert (abstract_clock stres1 ≡ bs') as Hac1.
        { take (fby _ _ _) and apply ac_fby2 in it. now rewrite it. }

        assert (incl (List.map fst Γ') (List.map fst Γck)) as Hinclfst.
        { intros ??. simpl_In. edestruct H16; eauto with senv.
          take (HasClock _ _ _) and inv it. solve_In. }

        constructor. eapply Sscope with (Hi':=Hi').
        + intros * Hsem Hninm. subst.
          apply sem_var_union in Hsem as [Hin|Hin]; auto.
          exfalso. inv Hin. take (FEnv.of_list _ _ = _) and apply FEnv.of_list_find_In in it as Hin; simpl_Forall.
          destruct Hin as [He|[He|[He|[He|He]]]]; inv He; auto 8.
        + subst. intros ?. rewrite FEnv.union_In, FEnv.of_list_In, 2 fst_InMembers; reflexivity.
        + reflexivity.
        + simpl. intros * [He|[He|[He|[He|He]]]]; inv He; auto.
        + split; intros * Hcka.
          2:{ intros Hla. inv Hla; simpl_In.
              destruct Hin as [He|[He|[He|[He|He]]]]; inv He; simpl in *; congruence. }
          simpl in *.
          inv Hcka; simpl in *. take (_ \/ _ \/ _) and destruct it as [He|[He|[He|[He|He]]]]; inv He; do 2 esplit; simpl.

          1,3,5,7:sem_new_vars.
          1-4:(eapply sem_clock_refines; eauto;
               try rewrite ac_stres_proj1; try rewrite ac_stres_proj2;
               try rewrite Hac; auto).
          1,2:take (fby _ _ _) and apply ac_fby2 in it; rewrite it, Hac; auto.
        + repeat constructor.
          *{ econstructor. repeat constructor. 2:simpl; rewrite app_nil_r; repeat constructor.
             econstructor; repeat constructor.
             3,4,6,7:sem_new_vars.
             - eapply add_whens_enum_sem, sem_clock_refines; eauto.
             - eapply add_whens_enum_sem, sem_clock_refines; eauto.
             - repeat constructor.
               + apply fby_stres_proj1 in H21; auto.
                 rewrite stres_proj1_const in H21; auto.
               + apply fby_stres_proj2 in H21. rewrite stres_proj2_const in H21; auto.
           }
          *{ econstructor; simpl.
             - repeat constructor. sem_new_vars.
             - repeat constructor.
               take (fby _ _ _) and eapply sem_automaton_wt_state2 in it; eauto.
               + apply SForall_forall; intros n. apply SForall_forall with (n:=n) in it.
                 setoid_rewrite Str_nth_map. destruct (stres # n) as [|(?&?)] eqn:Hst; simpl in *; auto.
                 constructor; simpl.
                 eapply eq_ind with (P:=fun x => match x with absent => True | present (e, _) => e < length states end) in it; [|eauto].
                 simpl in *; auto. congruence.
               + rewrite <-H10. apply fst_InMembers; auto.
               + simpl_Forall; auto.
               + simpl_Forall; destruct s; destruct_conjs; intros. specialize (H22 k); destruct_conjs.
                 esplit; eauto using sem_transitions_ck_sem_transitions.
             - simpl_Forall.
               do 2 esplit. split. instantiate (1:=(_,_)). 2:simpl; reflexivity.
               1:{ simpl. apply filter_hist_restrict_ac with (xs:=x3::x5::x7::x9::List.map fst Γ').
                   intros * Hin Hsem.
                   eapply sem_var_union in Hsem; eauto.
                   simpl in *. repeat rewrite <-or_assoc in Hin.
                   destruct Hin as [Hin|Hin], Hsem as [Hsem|Hsem].
                   - exfalso. eapply sem_var_In in Hsem; eauto.
                     destruct Hin as [[[|]|]|]; subst; eauto.
                   - apply sem_var_of_list' in Hsem as (?&Heq1&[Heq|[Heq|[Heq|[Heq|Heq]]]]); inv Heq;
                       rewrite Heq1; repeat rewrite ac_stres_proj1; repeat rewrite ac_stres_proj2.
                     + reflexivity.
                     + apply ac_fby2 in H21; auto.
                     + reflexivity.
                     + apply ac_fby2 in H21; auto.
                   - rewrite ac_stres_proj1, Hac. eapply sem_clock_det; eauto.
                     simpl_In. edestruct H16; eauto with senv.
                     edestruct Hsc as ((?&Hv'&Hck)&_); eauto.
                     eapply sem_var_det in Hsem; eauto. rewrite <-Hsem; auto.
                   - exfalso. eapply Hinclfst in Hin. simpl_In.
                     assert (IsVar Γck x13) as Hv by eauto with senv.
                     apply sem_var_of_list' in Hsem as (?&_&[Heq|[Heq|[Heq|[Heq|Heq]]]]); inv Heq; eauto.
               }
               econstructor; eauto. 2:reflexivity.
               1:{ intros. split; [intros ?|intros [|[]]]; auto. }
               1:{ intros * Hin; inv Hin. }
               1:{ split; intros * Hca; inv Hca; simpl in *; take False and inv it. }
               repeat constructor. econstructor.
               + econstructor; simpl. apply sem_var_restrict; eauto with datatypes.
                 apply sem_var_ffilter. sem_new_vars.
               + apply bools_of_ffilter, bools_of_stres_proj2.
               + intros k. specialize (H22 k); destruct_conjs.
                 take (select_hist _ _ _ _ _) and destruct it as (Hsel1&Hsel2). apply select_hist_fselect_hist in Hsel1. simpl in *.
                 repeat constructor.
                 *{ eapply sem_transitions_refines, sem_transitions_restrict with (Γ:=((x3, default_ann)::(x5, default_ann)::(x7, default_ann)::(x9, default_ann)::Γ')) in H35; eauto.
                    2:{ simpl_Forall. eapply wx_exp_incl. 3:eauto with lclocking.
                        1,2:intros * Hv; inv Hv; econstructor; eauto using inmembers_cons with datatypes. }
                    eapply sem_equation_ck_morph. 2,3:reflexivity.
                    1:{ instantiate (1:=(FEnv.restrict _ _,_)). split.
                        - setoid_rewrite <-FEnv.restrict_map; auto using EqStrel_Reflexive. apply FEnv.restrict_Equiv.
                          setoid_rewrite <-fselect_mask_ffilter_hist. reflexivity.
                        - simpl. setoid_rewrite <-fselect_mask_ffilter_hist. apply Hsel2. }
                    eapply trans_exp_sem in H35 as (ss&Htranssem&Hconcat); eauto.
                    - repeat constructor. econstructor. 2:rewrite Hconcat; simpl.
                      + eapply Forall2_impl_In; [|eauto]; intros.
                        subst. eapply sem_exp_refines; [|simpl; eauto].
                        eapply FEnv.restrict_refines'.
                        eapply FEnv.refines_map; [|eauto].
                        intros * Heq; now rewrite Heq.
                      + repeat constructor; subst; [rewrite stres_proj1_fselect|rewrite stres_proj2_fselect].
                        1,2:eapply sem_var_restrict, sem_var_fselect; eauto with datatypes.
                        1,2:sem_new_vars; simpl in *; auto.
                    - simpl_Forall; eauto.
                    - eapply sc_vars_restrict; eauto.
                      + intros ??; simpl; eauto with datatypes.
                      + simpl_Forall; simpl_In; simpl_Forall.
                        edestruct H16 as (?&Hbase); eauto with senv. rewrite Hbase; constructor.
                      + eapply sc_vars_morph, sc_vars_fselect; eauto. 2:reflexivity.
                        split; [reflexivity|simpl; now symmetry].
                        now rewrite Hac.
                   }
            }
          *{ econstructor; simpl.
             - repeat constructor. sem_new_vars.
             - repeat constructor.
               take (fby _ _ _) and eapply sem_automaton_wt_state3 in it; eauto.
               + apply SForall_forall; intros n. apply SForall_forall with (n:=n) in it.
                 setoid_rewrite Str_nth_map. destruct (stres1 # n) as [|(?&?)] eqn:Hst; simpl in *; auto.
                 constructor; simpl.
                 eapply eq_ind with (P:=fun x => match x with absent => True | present (e, _) => e < length states end) in it; [|eauto].
                 simpl in *; auto. congruence.
               + rewrite <-H10. apply fst_InMembers; auto.
               + simpl_Forall; auto.
               + simpl_Forall; destruct s; destruct_conjs; intros. specialize (H22 k); destruct_conjs.
                 esplit; eauto using sem_transitions_ck_sem_transitions.
             - auto_block_simpl_Forall; eauto 8 using fresh_ident_st_valid.
               2:{ intros; destruct_conjs; destruct s1; destruct_conjs; repeat inv_bind.
                   eapply mmap2_st_valid; simpl_Forall; eauto using auto_block_st_valid. }
               do 2 esplit. split. instantiate (1:=(_,_)). 2:simpl; reflexivity.
               1:{ simpl. apply filter_hist_restrict_ac with (xs:=x3::x5::x7::x9::List.map fst Γ').
                   intros * Hin Hsem.
                   eapply sem_var_union in Hsem; eauto.
                   simpl in *. repeat rewrite <-or_assoc in Hin.
                   destruct Hin as [Hin|Hin], Hsem as [Hsem|Hsem].
                   - exfalso. eapply sem_var_In in Hsem; eauto.
                     destruct Hin as [[[|]|]|]; subst; eauto.
                   - apply sem_var_of_list' in Hsem as (?&Heq1&[Heq|[Heq|[Heq|[Heq|Heq]]]]); inv Heq;
                       rewrite Heq1; repeat rewrite ac_stres_proj1; repeat rewrite ac_stres_proj2; try reflexivity.
                     + now rewrite Hac, <-Hac1.
                     + now rewrite Hac, <-Hac1.
                   - rewrite ac_stres_proj1, Hac1. eapply sem_clock_det; eauto.
                     simpl_In. edestruct H16; eauto with senv.
                     edestruct Hsc as ((?&Hv'&Hck)&_); eauto.
                     eapply sem_var_det in Hsem; eauto. rewrite <-Hsem; auto.
                   - exfalso. eapply Hinclfst in Hin. simpl_In.
                     assert (IsVar Γck x17) as Hv by eauto with senv.
                     apply sem_var_of_list' in Hsem as (?&_&[Heq|[Heq|[Heq|[Heq|Heq]]]]); inv Heq; eauto.
               }
               econstructor; eauto. 2:reflexivity.
               1:{ intros. split; [intros ?|intros [|[]]]; auto. }
               1:{ intros * Hin; inv Hin. }
               1:{ split; intros * Hca; inv Hca; simpl in *; take False and inv it. }
               repeat constructor. econstructor.
               + econstructor; simpl. apply sem_var_restrict; eauto with datatypes.
                 apply sem_var_ffilter. sem_new_vars.
               + apply bools_of_ffilter, bools_of_stres_proj2.
               + intros k. specialize (H23 k); destruct_conjs.
                 take (select_hist _ _ _ _ _) and destruct it as (Hsel1&Hsel2). apply select_hist_fselect_hist in Hsel1. simpl in *.
                 inv H1. inv H2. inv H3.
                 take (sem_scope_ck _ _ _ _ _) and eapply sem_scope_refines3, sem_scope_restrict3 in it. 3,4:eauto.
                 2:{ apply Forall_forall; intros; simpl_In.
                     edestruct H16 as (?&Hbase); eauto with senv. rewrite Hbase; constructor. }
                 inv H36. inv H37. inv it. destruct_conjs. repeat inv_bind.
                 repeat constructor.
                 remember (Hi' + FEnv.of_list (List.map (fun '(x, s) => (x, fselectv e k stres1 s))
                                                        [(x3, stres_proj1 stres); (x5, stres_proj1 stres1); (x7, stres_proj2 stres); (x9, stres_proj2 stres1)])) as Hi''.
                 assert (FEnv.refines (@EqSt _) Hi' Hi'') as Href''.
                 { subst. intros ?? Hfind. do 2 esplit; [reflexivity|].
                   eapply FEnv.union2; eauto.
                   destruct (FEnv.of_list _ _) eqn:Hfind'; auto. exfalso.
                   apply FEnv.of_list_find_In in Hfind'; simpl_In.
                   assert (FEnv.In x13 Hi') as Hin' by (econstructor; eauto).
                   take (forall x, FEnv.In x Hi' <-> _) and rewrite it, FEnv.restrict_In in Hin'.
                   destruct Hin' as [(Hin'&_)|Hin'].
                   - apply FEnv.map_in_iff in Hin'.
                     repeat (take (_ \/ _) and destruct it; subst); inv_equalities; eauto.
                   - apply fst_InMembers in Hin'; simpl_In; simpl_Forall.
                     repeat (take (CA.fresh_ident _ = _) and apply fresh_ident_prefixed in it as (?&?&?)); subst.
                     destruct Hin as [|[|[|[|]]]]; inv_equalities; auto.
                     all:eapply contradict_AtomOrGensym; eauto using auto_not_in_last_prefs.
                 }
                 remember (maskb _ _ _) as bs''.
                 assert (sc_vars (Γ' ++ senv_of_locs locs) (Hi', Hl') bs'') as Hsc'.
                 { eapply sc_vars_app; subst; eauto.
                   - intros ??. rewrite InMembers_senv_of_locs. intros ?.
                     eapply H45, Hinclfst, fst_InMembers; eauto.
                   - subst. eapply sc_vars_refines, sc_vars_restrict, sc_vars_fselect. 6-8:eauto.
                     + eapply local_hist_dom_ub_refines with (xs:=List.map fst Γ'); eauto using FEnv.restrict_dom_ub.
                       intros * Hinm Hin. eapply H45; eauto.
                     + rewrite <-Hsel2; auto.
                     + reflexivity.
                     + simpl_Forall; simpl_In.
                       edestruct H16 as (?&Hbase); eauto with senv. rewrite Hbase; constructor.
                     + now rewrite Hac1.
                 }
                 repeat constructor.
                 eapply Sscope with (Hi':=Hi'') (Hl':=Hl').
                 *{ intros. subst. unfold CStr.mask_hist; simpl.
                    take (sem_var (_ + _) _ _) and eapply sem_var_union in it as [Hv|Hv].
                    - apply H41 in Hv; auto.
                      apply sem_var_restrict_inv in Hv as (Hin&Hv).
                      apply sem_var_fselect_inv in Hv as (?&Hv&Heq). rewrite Heq.
                      apply sem_var_mask, sem_var_restrict, sem_var_ffilter; eauto with datatypes.
                      inv Hv. econstructor; eauto. apply FEnv.union2; auto.
                      destruct (FEnv.of_list _ _) eqn:Hfind; auto. exfalso.
                      assert (FEnv.In x13 Hi) by (econstructor; eauto).
                      apply FEnv.of_list_find_In in Hfind as [|[|[|[|]]]]; inv_equalities; auto.
                    - apply sem_var_of_list' in Hv as (?&Heq&?); simpl_In. rewrite Heq.
                      apply sem_var_mask, sem_var_restrict, sem_var_ffilter.
                      + simpl. destruct Hin as [He|[He|[He|[He|He]]]]; inv He; auto.
                      + sem_new_vars.
                 }
                 *{ subst. intros ?.
                    rewrite FEnv.union_In, FEnv.of_list_In, H53.
                    setoid_rewrite FEnv.map_in_iff; simpl. rewrite 2 FEnv.restrict_In.
                    repeat setoid_rewrite FEnv.map_in_iff. rewrite FEnv.union_In, FEnv.of_list_In, fst_InMembers; simpl.
                    split; intros; repeat (take (_ \/ _) and destruct it; destruct_conjs); auto 8. now exfalso.
                   }
                 * etransitivity; [|eauto]. rewrite Hsel2.
                   unfold CStr.mask_hist; simpl. rewrite fselect_mask_ffilter_hist.
                   reflexivity.
                 * intros * Hin. simpl_Forall. congruence.
                 * subst. eapply sc_vars_refines. 3:eauto. 2:reflexivity. eauto.
                 *{ auto_block_simpl_Forall.
                    eapply sem_block_refines, H with (Hi:=(FEnv.restrict _ _,_)) (Γck:=Γ'++_); eauto.
                    - etransitivity; [|eauto]. eapply FEnv.restrict_refines; eauto using EqStrel_Reflexive, EqStrel_Transitive.
                    - intros * Hv. inv Hv. take (InMembers _ (_ ++ _)) and apply InMembers_app in it as [Hin|Hin]; apply fst_InMembers in Hin; simpl_In.
                      + apply Hat. edestruct H16; eauto with senv.
                      + simpl_Forall; auto.
                    - eapply NoDupLocals_incl; [|eauto]. rewrite map_app, map_fst_senv_of_locs.
                      eapply incl_appl'.
                      intros ? Hin. simpl_In.
                      edestruct H16 as (Hck&_); eauto with senv. inv Hck; solve_In.
                    - apply FEnv.restrict_dom_ub.
                    - subst. apply sc_vars_restrict; eauto.
                      + reflexivity.
                      + simpl_Forall; simpl_In.
                        apply in_app_iff in Hin as [Hin|Hin]; simpl_In; simpl_Forall; eauto.
                        edestruct H16 as (_&Hbase); eauto with senv. rewrite Hbase; constructor.
                    - eapply sem_block_restrict; subst; eauto.
                      unfold wc_env. simpl_Forall; simpl_In.
                      apply in_app_iff in Hin as [Hin|Hin]; simpl_In; simpl_Forall; eauto.
                      edestruct H16 as (_&Hbase); eauto with senv. rewrite Hbase; constructor.
                   }
            }

      - (* local *)
        inv H2. inv H1. inv H3. inv H5. inv H6. inv H8.
        do 2 econstructor; eauto.
        1:{ intros. simpl_Forall. congruence. }
        auto_block_simpl_Forall.
        eapply H with (Γck:=Γck++senv_of_locs locs); eauto.
        + intros * Hv. apply IsVar_app in Hv as [Hv|Hv]; auto.
          inv Hv. apply fst_InMembers in H23; simpl_In. simpl_Forall; auto.
        + rewrite map_app, map_fst_senv_of_locs; auto.
        + rewrite map_app, map_fst_senv_of_locs. eapply local_hist_dom_ub; eauto.
        + eapply sc_vars_app; eauto.
          * intros * Hinm1 Hinm2. rewrite fst_InMembers in Hinm1. rewrite InMembers_senv_of_locs in Hinm2.
            eapply H13; eauto.
          * eapply sc_vars_refines; [| |eauto]; eauto.
            eapply local_hist_dom_ub_refines; eauto.
    Qed.

    Lemma auto_node_sem : forall f n ins outs,
        wt_global (Global G1.(types) (n::G1.(nodes))) ->
        wc_global (Global G1.(types) (n::G1.(nodes))) ->
        Ordered_nodes (Global G1.(types) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(types) ((fst (auto_node n))::G2.(nodes))) ->
        sem_node_ck (Global G1.(types) (n::G1.(nodes))) f ins outs ->
        sem_node_ck (Global G2.(types) ((fst (auto_node n))::G2.(nodes))) f ins outs.
    Proof with eauto.
      intros * (_&Hwt) Hwc Hord1 Hord2 Hsem.

      inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
      - erewrite find_node_now in Hfind; eauto. inv Hfind.
        (*The semantics of equations can be given according to G only *)
        eapply sem_block_ck_cons in H3; eauto. rename H3 into Hblksem.
        2:{ inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }

        replace {| types := types G1; nodes := nodes G1 |} with G1 in Hblksem by (destruct G1; auto).
        pose proof (n_nodup n0) as (Hnd1&Hnd2).
        pose proof (n_good n0) as (Hgood1&Hgood2&_).
        inv Hwc. destruct H4 as (Hwc&_); simpl in Hwc.
        inv Hwt. destruct H4 as (Hwt&_); simpl in Hwt.
        destruct H5 as (Hdom1&Hsc1).
        eapply auto_block_sem in Hblksem; eauto.
        9:rewrite surjective_pairing with (p:=auto_block _ _), surjective_pairing with (p:=fst _); reflexivity.
        eapply Snode; eauto.
        + erewrite find_node_now; eauto.
        + eauto.
        + eauto.
        + apply sem_block_ck_cons'; simpl...
          2:{ eapply find_node_not_Is_node_in in Hord2.
            2:erewrite find_node_now; eauto. eauto. }
          destruct G2; eauto.
        + simpl. constructor; simpl; auto.
        + intros * Hv. inv Hv. apply fst_InMembers in H0. simpl_In. simpl_Forall; auto.
        + eapply init_st_valid; eauto using auto_not_in_last_prefs, PS_For_all_empty.
        + rewrite map_fst_senv_of_inout. apply n_nodup.
        + apply n_syn.
        + destruct Hwt as (_&_&_&Hwt). destruct G1; eauto.
        + destruct Hwc as (_&_&Hwc). destruct G1; auto.
        + apply FEnv.dom_dom_ub; auto.
      - erewrite find_node_other in Hfind; eauto.
        eapply sem_node_ck_cons'...
        destruct G2; apply Href.
        econstructor...
        destruct G1; eapply sem_block_ck_cons...
        eapply find_node_later_not_Is_node_in in Hord1...
    Qed.

  End sem_node.

  Module Clocking := CAClockingFun Ids Op OpAux Cks Senv Syn Cl CA.

  Lemma auto_global_refines : forall G,
      wt_global G ->
      wc_global G ->
      global_sem_refines G (auto_global G).
  Proof with eauto using wc_global_Ordered_nodes.
    intros (enms&nds) (Htypes&Hwt). unfold auto_global; simpl.
    generalize (enms ++ flat_map snd (List.map auto_node nds)). revert enms Htypes Hwt.
    induction nds; intros * Htypes Hwt * Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      eapply Clocking.auto_global_wc, wc_global_Ordered_nodes in Hwc'.
      assert (global_sem_refines {| types := enms; nodes := nds |} {| types := l; nodes := List.map fst (List.map auto_node nds) |}) as Hind.
      { inv Hwt. inv Hwc. eapply IHnds... }
      apply global_sem_ref_cons with (f:=n_name a)...
      + eapply Ordered_nodes_change_types; eauto.
      + intros ins outs Hsem; simpl in *.
        change l with ((Global l (List.map fst (List.map auto_node nds))).(types)).
        eapply auto_node_sem with (G1:=Global enms nds)...
        1-3:inv Hwt; inv Hwc...
        * destruct H1. constructor... constructor...
        * eapply Ordered_nodes_change_types; eauto.
  Qed.

  Theorem auto_global_sem : forall G f ins outs,
      wt_global G ->
      wc_global G ->
      sem_node_ck G f ins outs ->
      sem_node_ck (auto_global G) f ins outs.
  Proof.
    intros.
    eapply auto_global_refines in H; eauto.
    specialize (H f ins outs); auto.
  Qed.

End CACORRECTNESS.

Module CACorrectnessFun
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
       (CA : COMPAUTO Ids Op OpAux Cks Senv Syn)
       <: CACORRECTNESS Ids Op OpAux Cks CStr Senv Syn Ty Clo Lord Sem LClockSem CA.
  Include CACORRECTNESS Ids Op OpAux Cks CStr Senv Syn Ty Clo Lord Sem LClockSem CA.
End CACorrectnessFun.
