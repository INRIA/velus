From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LCausality Lustre.LSemantics Lustre.LClockSemantics.
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
       (LCA        : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Import Ty : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import Cl : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import Ord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (Import LCS : LCLOCKSEMANTICS Ids Op OpAux Cks Senv Syn Ty Cl LCA Ord CStr Sem)
       (Import CA  : COMPAUTO Ids Op OpAux Cks Senv Syn).

  Module Import SCC := SCCorrectnessFun Ids Op OpAux Cks CStr Senv Syn Ty Cl LCA Ord Sem LCS SC. Import SC.

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

  Fact sem_var_adds' : forall H xs x vs,
      sem_var (Env.adds' xs H) x vs ->
      (exists vs', vs ≡ vs' /\ In (x, vs') xs) \/ sem_var H x vs.
  Proof.
    intros * Hv. inv Hv.
    eapply Env.find_adds'_In in H1 as [Hin|Hfind]; eauto using sem_var.
  Qed.

  Lemma sem_var_disj_adds' : forall xs Hi2 x vs,
      NoDupMembers xs ->
      (forall x, InMembers x xs -> ~Env.In x Hi2) ->
      sem_var (Env.adds' xs Hi2) x vs <-> (exists vs', vs ≡ vs' /\ In (x, vs') xs) \/ sem_var Hi2 x vs.
  Proof.
    intros * Hnd Hdisj.
    split.
    - eapply sem_var_adds'.
    - intros [(?&Heq&Hin)|Hv]; [|inv Hv]; econstructor; eauto; unfold Env.MapsTo in *.
      + eapply Env.In_find_adds'; eauto.
      + erewrite Env.gsso'; eauto.
        intros Hinm. eapply Hdisj; eauto.
        econstructor; eauto.
  Qed.

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

    Opaque Env.restrict Env.adds'.

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
        Env.Equiv (EqSt (A:=svalue))
                  (fselect_hist e k stres Hi)
                  (CStr.mask_hist k (ffilterb e (stres_st stres) (stres_res stres))
                                  (ffilter_hist e (stres_st stres) Hi)).
    Proof.
      intros.
      unfold fselect_hist, CStr.mask_hist, ffilter_hist.
      rewrite Env.map_map.
      eapply Env.map_Equiv. 2:reflexivity.
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
        Env.dom_ub (fst Hi) (List.map fst Γck) ->
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
        + setoid_rewrite Env.dom_ub_map; auto.

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
        1:{ intros. simpl_Forall. edestruct H40; eauto; destruct_conjs.
            eauto 8 using sem_ref_sem_exp. }
        auto_block_simpl_Forall.
        eapply H with (Γck:=Γ'++_); eauto.
        + intros * Hin.
          inv Hin. rewrite InMembers_app, 2 fst_InMembers in H23. destruct H23; simpl_In.
          * eapply Hat. edestruct H14; eauto with senv.
          * simpl_Forall; auto.
        + eapply NoDupLocals_incl; eauto.
          intros ? Hin; simpl_In. rewrite in_app_iff in *. destruct Hin0 as [|]; simpl_In.
          * left. eapply Hincl. solve_In.
          * right. solve_In.
        + rewrite map_app, map_fst_senv_of_locs. eapply local_hist_dom_ub; eauto.
          apply Env.restrict_dom_ub.
        + eapply sc_vars_app; eauto.
          * intros * Hinm1 Hinm2. rewrite fst_InMembers in Hinm1. rewrite InMembers_senv_of_locs in Hinm2.
            eapply H29; eauto.
          * eapply sc_vars_refines with (Hl:=t0), sc_vars_restrict, sc_vars_morph, sc_vars_ffilter, Hsc; try reflexivity; eauto.
            2:{ simpl_Forall. simpl_In.
                edestruct H14 as (?&Hbase); eauto with senv; subst. rewrite Hbase; constructor. }
            2:split; simpl in *; [reflexivity|now symmetry].
            eapply local_hist_dom_ub_refines; eauto using Env.dom_ub_incl, Env.restrict_dom_ub.

      - (* automaton *)
        destruct Hi as (Hi&Hl).
        assert (Forall (fun id : Env.key => ~IsVar Γck id) [x1;x3;x5;x7]) as Hnin1.
        { simpl_Forall; simpl in *. intros Hv.
          apply Hat in Hv.
          repeat (take (CA.fresh_ident _ = _) and eapply fresh_ident_prefixed in it as (?&?&?); subst).
          destruct H21 as [|[|[|[|]]]]; subst; try eapply contradict_AtomOrGensym in Hv; eauto using auto_not_in_last_prefs.
        }
        assert (Forall (fun id : Env.key => ~ Env.In id Hi) [x1;x3;x5;x7]) as Hnin2.
        { simpl_Forall; simpl in *. intros Henvin. eapply Env.dom_ub_use, fst_InMembers in Henvin; eauto.
          assert (IsVar Γck x11) as Hv by eauto with senv.
          destruct H21 as [|[|[|[|]]]]; subst; eauto.
        }
        assert (NoDup [x1;x3;x5;x7]) as Hnd.
        { eapply fresh_idents_NoDup; eauto using fresh_ident_st_valid. }
        remember (Env.adds' [(x1, stres_proj1 stres); (x3, stres_proj1 stres1);
                             (x5, stres_proj2 stres); (x7, stres_proj2 stres1)] Hi) as Hi'.
        assert (Env.refines (@EqSt _) Hi Hi') as Href'.
        { subst. apply Env.refines_adds'; auto using EqStrel_Reflexive, EqStrel_Transitive. }

        assert (abstract_clock stres ≡ bs') as Hac.
        { eapply sc_transitions in H23; eauto. 3:simpl_Forall; eauto.
          - apply ac_fby1 in H24. now rewrite <-H24.
          - eapply sc_vars_subclock; eauto. }

        assert (incl (List.map fst Γ') (List.map fst Γck)) as Hinclfst.
        { intros ??. simpl_In. edestruct H16; eauto with senv.
          inv H21. solve_In. }

        constructor. eapply Sscope with (Hi':=Hi').
        + intros * Hsem Hninm. subst.
          apply sem_var_adds' in Hsem as [(?&Heq&Hin)|]; auto.
          exfalso. apply Hninm; simpl in *.
          destruct Hin as [He|[He|[He|[He|He]]]]; inv He; auto.
        + subst. rewrite Permutation_app_comm.
          pose proof (Env.dom_elements Hi) as Hdom'.
          eapply Env.dom_adds' with (xs:=[(x1, stres_proj1 stres); (x3, stres_proj1 stres1); (x5, stres_proj2 stres); (x7, stres_proj2 stres1)]) in Hdom'.
          simpl in *; auto.
        + reflexivity.
        + simpl. intros * [He|[He|[He|[He|He]]]]; inv He; auto.
        + split; intros * Hcka.
          2:{ intros Hla. inv Hla; simpl_In.
              destruct Hin as [He|[He|[He|[He|He]]]]; inv He; simpl in *; congruence. }
          simpl in *.
          inv Hcka; simpl in *. destruct H21 as [He|[He|[He|[He|He]]]]; inv He; do 2 esplit; simpl.

          Local Ltac sem_new_vars :=
            subst; eapply sem_var_disj_adds';
            [apply fst_NoDupMembers; auto
            |intros ?; rewrite fst_InMembers; intros;
             match goal with
             | Hnin : Forall (fun _ => ~Env.In _ _) _ |- _ => eapply Forall_forall in Hnin; eauto
             | _ => idtac
             end
            |left; do 2 esplit; try reflexivity; eauto with datatypes].

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
               eapply sem_transitions_ck_sem_transitions, sem_automaton_wt_state in H23; eauto.
               + apply SForall_forall; intros n. apply SForall_forall with (n:=n) in H23.
                 setoid_rewrite Str_nth_map. destruct (stres # n) as [|(?&?)] eqn:Hst; simpl in *; auto.
                 constructor; simpl.
                 eapply eq_ind with (P:=fun x => match x with absent => True | present (e, _) => e < length states end) in H23; [|eauto].
                 simpl in *; auto.
               + simpl_Forall; eauto.
               + rewrite <-H10. apply fst_InMembers; auto.
               + simpl_Forall; auto. inv H12; destruct_conjs; simpl_Forall; auto.
               + simpl_Forall. specialize (H25 k); destruct_conjs.
                 inv H26; destruct_conjs.
                 esplit; eauto using sem_transitions_ck_sem_transitions.
             - auto_block_simpl_Forall; eauto 8 using fresh_ident_st_valid.
               2:{ intros; destruct_conjs; destruct s1 as [?(?&?)]; repeat inv_bind.
                   eapply mmap2_st_valid; simpl_Forall; eauto using auto_block_st_valid. }
               do 2 esplit. split. instantiate (1:=(_,_)). 2:simpl; reflexivity.
               1:{ simpl. apply filter_hist_restrict_ac with (xs:=x1::x3::x5::x7::List.map fst Γ').
                   intros * Hin Hsem.
                   eapply sem_var_adds' in Hsem; eauto.
                   simpl in *. repeat rewrite <-or_assoc in Hin.
                   destruct Hin as [Hin|Hin], Hsem as [Hsem|Hsem].
                   - destruct Hsem as (?&Heq1&[Heq|[Heq|[Heq|[Heq|Heq]]]]); inv Heq;
                       rewrite Heq1; repeat rewrite ac_stres_proj1; repeat rewrite ac_stres_proj2.
                     + reflexivity.
                     + apply ac_fby2 in H24; auto.
                     + reflexivity.
                     + apply ac_fby2 in H24; auto.
                   - exfalso. eapply sem_var_In in Hsem; eauto.
                     destruct Hin as [[[|]|]|]; subst; eauto.
                   - exfalso. eapply Hinclfst in Hin. simpl_In.
                     assert (IsVar Γck x15) as Hv by eauto with senv.
                     destruct H38 as [Heq|[Heq|[Heq|[Heq|Heq]]]]; inv Heq; eauto.
                   - rewrite ac_stres_proj1, Hac. eapply sem_clock_det; eauto.
                     simpl_In. edestruct H16; eauto with senv.
                     edestruct Hsc as ((?&Hv'&Hck)&_); eauto.
                     eapply sem_var_det in Hsem; eauto. rewrite <-Hsem; auto.
               }
               econstructor; eauto. 2:reflexivity.
               1:{ rewrite app_nil_r. apply Env.dom_elements. }
               1:{ intros * Hin; inv Hin. }
               1:{ split; intros * Hca; inv Hca; simpl in *; take False and inv it. }
               repeat constructor. econstructor.
               + econstructor; simpl. apply sem_var_restrict; eauto with datatypes.
                 apply sem_var_ffilter. sem_new_vars.
                 destruct H37 as [Heq|[Heq|[Heq|[Heq|Heq]]]]; inv Heq; eauto.
               + apply bools_of_ffilter, bools_of_stres_proj2.
               + intros k. specialize (H25 k); destruct_conjs.
                 destruct H25 as (Hsel1&Hsel2). apply select_hist_fselect_hist in Hsel1. simpl in *.
                 inv H1. inv H2. inv H3.
                 eapply sem_scope_refines2, sem_scope_restrict2 in H37. 3,4:eauto.
                 2:{ apply Forall_forall; intros; simpl_In.
                     edestruct H16 as (?&Hbase); eauto with senv. rewrite Hbase; constructor. }
                 inv H12. inv H19. inv H37. destruct_conjs. repeat inv_bind.
                 repeat constructor.
                 remember ((Env.adds' (List.map (fun '(x, s) => (x, fselectv e k stres s))
                                                [(x1, stres_proj1 stres); (x3, stres_proj1 stres1); (x5, stres_proj2 stres); (x7, stres_proj2 stres1)]) Hi')) as Hi''.
                 assert (Env.refines (@EqSt _) Hi' Hi'') as Href''.
                 { subst. eapply Env.refines_adds'; eauto using EqStrel_Reflexive, EqStrel_Transitive.
                   simpl_Forall. intro Hin. eapply Env.dom_use in Hin; eauto.
                   apply in_app_iff in Hin as [Hin|Hin]; simpl_In.
                   - apply Env.elements_In, Env.restrict_In_iff in Hin0 as (Hin0&_).
                     setoid_rewrite Env.Props.P.F.map_in_iff in Hin0.
                     repeat (take (_ \/ _) and destruct it; subst); eauto.
                   - simpl_Forall.
                     repeat (take (CA.fresh_ident _ = _) and apply fresh_ident_prefixed in it as (?&?&?)); subst.
                     destruct H50 as [|[|[|[|]]]]; subst; auto.
                     all:eapply contradict_AtomOrGensym; eauto using auto_not_in_last_prefs.
                 }
                 remember (maskb _ _ _) as bs''.
                 assert (sc_vars (Γ' ++ senv_of_locs locs) (Hi', Hl') bs'') as Hsc'.
                 { eapply sc_vars_app; subst; eauto.
                   - intros ??. rewrite InMembers_senv_of_locs. intros ?.
                     eapply H43, Hinclfst, fst_InMembers; eauto.
                   - subst. eapply sc_vars_refines, sc_vars_restrict, sc_vars_fselect. 6-8:eauto.
                     + eapply local_hist_dom_ub_refines with (xs:=List.map fst Γ'); eauto using Env.restrict_dom_ub.
                       intros * Hinm Hin. eapply H43; eauto.
                     + rewrite <-Hsel2; auto.
                     + reflexivity.
                     + simpl_Forall; simpl_In.
                       edestruct H16 as (?&Hbase); eauto with senv. rewrite Hbase; constructor.
                     + now rewrite Hac.
                 }
                 repeat constructor.
                 eapply Sscope with (Hi':=Hi'') (Hl':=Hl'). 6:constructor.
                 *{ intros. subst. unfold CStr.mask_hist; simpl.
                    eapply sem_var_adds' in H50 as [(?&Heq&Hin)|Hv]; simpl_In.
                    - rewrite Heq. apply sem_var_mask, sem_var_restrict, sem_var_ffilter.
                      + simpl. destruct Hin0 as [He|[He|[He|[He|He]]]]; inv He; auto.
                      + apply sem_var_disj_adds'; auto.
                        * rewrite fst_NoDupMembers; simpl; auto.
                        * intros * Hin. rewrite fst_InMembers in Hin; simpl in *.
                          destruct Hin as [|[|[|[|]]]]; subst; auto.
                        * left. do 2 esplit; [reflexivity|]; auto.
                    - apply H46 in Hv; auto.
                      apply sem_var_restrict_inv in Hv as (Hin&Hv).
                      apply sem_var_fselect_inv in Hv as (?&Hv&Heq). rewrite Heq.
                      apply sem_var_mask, sem_var_restrict, sem_var_ffilter; eauto with datatypes.
                      apply sem_var_disj_adds'; auto.
                      + rewrite fst_NoDupMembers; simpl; auto.
                      + intros * Hinm. rewrite fst_InMembers in Hinm; simpl in *.
                        destruct Hinm as [|[|[|[|]]]]; subst; auto.
                 }
                 *{ subst. apply Env.dom_intro; intros.
                    erewrite Env.In_adds_spec', Env.dom_use; eauto.
                    rewrite 2 in_app_iff, <-or_assoc. apply or_iff_compat_r; simpl.
                    rewrite <-2 fst_InMembers, <-2 Env.In_Members; simpl.
                    setoid_rewrite Env.Props.P.F.map_in_iff. rewrite 2 Env.restrict_In_iff.
                    repeat setoid_rewrite Env.Props.P.F.map_in_iff.
                    rewrite Env.In_adds_spec', fst_InMembers; simpl.
                    split; [intros [|(?&?)]|intros ([|]&?)]; auto.
                    - split; auto.
                      repeat take (_ \/ _) and destruct it; auto. take False and inv it.
                    - split; auto.
                    - repeat take (_ \/ _) and destruct it; subst; auto.
                      exfalso; eauto.
                   }
                 * etransitivity; [|eauto]. rewrite Hsel2.
                   unfold CStr.mask_hist; simpl. rewrite fselect_mask_ffilter_hist.
                   reflexivity.
                 * intros * Hin. simpl_Forall. congruence.
                 * subst. eapply sc_vars_refines. 3:eauto. 2:reflexivity. eauto.
                 *{ eapply sem_transitions_refines, sem_transitions_restrict with (Γ:=((x1, default_ann)::(x3, default_ann)::(x5, default_ann)::(x7, default_ann)::Γ' ++ senv_of_locs locs)) in H2; eauto.
                    2:{ simpl_Forall. eapply wx_exp_incl. 3:eauto with lclocking.
                        1,2:intros * Hv; inv Hv; econstructor; eauto using inmembers_cons with datatypes. }
                    eapply trans_exp_sem in H2 as (ss&Htranssem&Hconcat); eauto.
                    + repeat constructor. econstructor. 2:rewrite Hconcat; simpl.
                      * eapply Forall2_impl_In; [|eauto]; intros.
                        subst. eapply sem_exp_refines; [|eauto].
                        eapply Env.restrict_refines; eauto using EqStrel_Reflexive, EqStrel_Transitive.
                      * assert (forall x, In x [x1;x3;x5;x7] -> ~Env.In x Hi').
                        { intros * Hin Hinenv. inv Hinenv.
                          eapply sem_var_restrict_inv in H46 as (_&Hv).
                          - eapply sem_var_In, Env.map_2 in Hv. instantiate (1:=x12) in Hv.
                            destruct Hin as [|[|[|[|]]]]; subst; eauto.
                          - econstructor; eauto. reflexivity.
                          - intros Hinm. apply fst_InMembers in Hinm; simpl_In; simpl_Forall.
                            repeat (take (CA.fresh_ident _ = _) and eapply fresh_ident_prefixed in it as (?&?&?); subst).
                            destruct Hin as [|[|[|[|]]]]; subst; try eapply contradict_AtomOrGensym in H25; eauto using auto_not_in_last_prefs.
                        }
                        repeat constructor; subst; [rewrite stres_proj1_fselect|rewrite stres_proj2_fselect].
                        1,2:sem_new_vars; simpl in *; auto.
                    + simpl_Forall; eauto.
                    + eapply sc_vars_restrict; eauto.
                      * intros ??; simpl; eauto with datatypes.
                      * simpl_app. apply Forall_app; split; simpl_Forall.
                        -- edestruct H16 as (?&Hbase); eauto with senv. rewrite Hbase; constructor.
                        -- eapply wc_clock_incl; [|eauto]. repeat apply incl_tl. reflexivity.
                      * eapply sc_vars_refines; [eauto|reflexivity|subst;eauto].
                   }
                 *{ auto_block_simpl_Forall.
                    eapply sem_block_refines, H with (Hi:=(Env.restrict _ _,_)) (Γck:=Γ'++_); eauto.
                    - etransitivity; [|eauto]. eapply Env.restrict_refines; eauto using EqStrel_Reflexive, EqStrel_Transitive.
                    - intros * Hv. inv Hv. apply InMembers_app in H58 as [Hin|Hin]; apply fst_InMembers in Hin; simpl_In.
                      + apply Hat. edestruct H16; eauto with senv.
                      + simpl_Forall; auto.
                    - eapply NoDupLocals_incl; [|eauto]. rewrite map_app, map_fst_senv_of_locs.
                      eapply incl_appl'.
                      intros ? Hin. simpl_In.
                      edestruct H16 as (Hck&_); eauto with senv. inv Hck; solve_In.
                    - apply Env.restrict_dom_ub.
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
            eapply H12; eauto.
          * eapply sc_vars_refines; [| |eauto]; eauto.
            eapply local_hist_dom_ub_refines; eauto.
    Qed.

    Lemma auto_node_sem : forall f n ins outs,
        wt_global (Global G1.(enums) (n::G1.(nodes))) ->
        wc_global (Global G1.(enums) (n::G1.(nodes))) ->
        Ordered_nodes (Global G1.(enums) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(enums) ((fst (auto_node n))::G2.(nodes))) ->
        sem_node_ck (Global G1.(enums) (n::G1.(nodes))) f ins outs ->
        sem_node_ck (Global G2.(enums) ((fst (auto_node n))::G2.(nodes))) f ins outs.
    Proof with eauto.
      intros * (_&Hwt) Hwc Hord1 Hord2 Hsem.

      inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
      - erewrite find_node_now in Hfind; eauto. inv Hfind.
        (*The semantics of equations can be given according to G only *)
        eapply sem_block_ck_cons in H3; eauto. rename H3 into Hblksem.
        2:{ inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }

        replace {| enums := enums G1; nodes := nodes G1 |} with G1 in Hblksem by (destruct G1; auto).
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
        + apply Env.dom_dom_ub; auto.
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
    intros (enms&nds) (Henums&Hwt). unfold auto_global; simpl.
    generalize (enms ++ flat_map snd (List.map auto_node nds)). revert enms Henums Hwt.
    induction nds; intros * Henums Hwt * Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      eapply Clocking.auto_global_wc, wc_global_Ordered_nodes in Hwc'.
      assert (global_sem_refines {| enums := enms; nodes := nds |} {| enums := l; nodes := List.map fst (List.map auto_node nds) |}) as Hind.
      { inv Hwt. inv Hwc. eapply IHnds... }
      apply global_sem_ref_cons with (f:=n_name a)...
      + eapply Ordered_nodes_change_enums; eauto.
      + intros ins outs Hsem; simpl in *.
        change l with ((Global l (List.map fst (List.map auto_node nds))).(enums)).
        eapply auto_node_sem with (G1:=Global enms nds)...
        1-3:inv Hwt; inv Hwc...
        * destruct H1. constructor... constructor...
        * eapply Ordered_nodes_change_enums; eauto.
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
       (LCA : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Ty : LTYPING Ids Op OpAux Cks Senv Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Lord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
       (LClockSem : LCLOCKSEMANTICS Ids Op OpAux Cks Senv Syn Ty Clo LCA Lord CStr Sem)
       (CA : COMPAUTO Ids Op OpAux Cks Senv Syn)
       <: CACORRECTNESS Ids Op OpAux Cks CStr Senv Syn LCA Ty Clo Lord Sem LClockSem CA.
  Include CACORRECTNESS Ids Op OpAux Cks CStr Senv Syn LCA Ty Clo Lord Sem LClockSem CA.
End CACorrectnessFun.
