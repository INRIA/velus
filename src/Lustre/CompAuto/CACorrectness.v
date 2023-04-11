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
    setoid_rewrite Str_nth_map. rewrite 2 mask_nth, 2 fwhen_nth.
    repeat setoid_rewrite Str_nth_map.
    destruct (_ =? _), (stres # n) as [|(?&?)]; auto.
    destruct (_ ==b _); auto.
  Qed.

  Fact stres_proj2_fselect : forall e k stres xs,
      stres_proj2 (fselect absent e k stres xs) ≡ fselectv e k stres (stres_proj2 xs).
  Proof.
    intros *. unfold fselectv, fselect.
    apply ntheq_eqst; intros n.
    setoid_rewrite Str_nth_map. rewrite 2 mask_nth, 2 fwhen_nth.
    repeat setoid_rewrite Str_nth_map.
    destruct (_ =? _), (stres # n) as [|(?&?)]; auto.
    destruct (_ ==b _); auto.
  Qed.

  Import Permutation.

  Section sem_node.
    Variable G1 : @global nolast last_prefs.
    Variable G2 : @global noauto auto_prefs.

    Hypothesis HwcG : wc_global G1.
    Hypothesis Href : global_sem_refines G1 G2.

    Ltac auto_block_simpl_Forall :=
      repeat
        simpl_Forall;
        (match goal with
         | Hmap: mmap2 _ _ _ = (?blks', _, _), Hin:In _ ?blks' |- _ =>
           eapply mmap2_values, Forall3_ignore13 in Hmap;
           eauto; simpl_Forall
         | _ => idtac
         end; repeat inv_bind);
        eauto.

    Fact case_first_of1 : forall e r bs vs bs' stres,
        bools_of vs bs' ->
        abstract_clock vs ≡ bs ->
        abstract_clock stres ≡ bs ->
        case vs [(true_tag, enum bs e); (false_tag, stres_proj1 stres)] None (stres_proj1 (first_of (e, r) bs' stres)).
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
        + setoid_rewrite Str_nth_map. rewrite first_of_nth.
          rewrite Hb; auto.
      - do 2 esplit. repeat (split; eauto).
        + repeat constructor; simpl.
          * rewrite enum_nth', <-Hac1; congruence.
          * setoid_rewrite Str_nth_map. rewrite Hst; congruence.
        + right; left. split; auto.
          setoid_rewrite Str_nth_map. rewrite Hst; eauto.
        + setoid_rewrite Str_nth_map. rewrite first_of_nth.
          rewrite Hb, Hst; auto.
      - repeat split; auto.
        + repeat constructor; simpl.
          * rewrite enum_nth', <-Hac1; congruence.
          * setoid_rewrite Str_nth_map. rewrite Hst; congruence.
        + setoid_rewrite Str_nth_map. rewrite first_of_nth.
          rewrite Hb. rewrite Hst; auto.
    Qed.

    Fact case_first_of2 : forall e r bs vs bs' stres,
        bools_of vs bs' ->
        abstract_clock vs ≡ bs ->
        abstract_clock stres ≡ bs ->
        case vs [(true_tag, enum bs (if (r : bool) then true_tag else false_tag));
                (false_tag, stres_proj2 stres)] None (stres_proj2 (first_of (e, r) bs' stres)).
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
        + setoid_rewrite Str_nth_map. rewrite first_of_nth.
          rewrite Hb; auto.
      - do 2 esplit. repeat (split; eauto).
        + repeat constructor; simpl.
          * rewrite enum_nth', <-Hac1; congruence.
          * setoid_rewrite Str_nth_map. rewrite Hst; congruence.
        + right; left. split; auto.
          setoid_rewrite Str_nth_map. rewrite Hst; eauto.
        + setoid_rewrite Str_nth_map. rewrite first_of_nth.
          rewrite Hb, Hst; auto.
      - repeat split; auto.
        + repeat constructor; simpl.
          * rewrite enum_nth', <-Hac1; congruence.
          * setoid_rewrite Str_nth_map. rewrite Hst; congruence.
        + setoid_rewrite Str_nth_map. rewrite first_of_nth.
          rewrite Hb. rewrite Hst; auto.
    Qed.

    Lemma init_state_exp_sem Γ : forall Hi bs tx ck bs' trans oth stres0,
        Forall (fun '(e, _) => wc_exp G1 Γ e /\ clockof e = [Cbase]) trans ->
        sem_clock (var_history Hi) bs ck bs' ->
        sc_vars Γ Hi bs' ->
        sem_transitions_ck G1 Hi bs' (List.map (fun '(e, t) => (e, (t, false))) trans) (oth, false) stres0 ->
        sem_exp_ck G2 Hi bs (init_state_exp tx ck trans oth) [stres_proj1 stres0].
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
          rewrite H13. eapply case_first_of1; eauto.
          * eapply sc_exp in H8; eauto.
            take (clockof _ = _) and rewrite it in H8; simpl_Forall. inv H4.
            now symmetry.
          * eapply sc_transitions in H12; eauto. simpl_Forall; eauto.
    Qed.

    Lemma trans_exp_sem Γ : forall Hi bs tx (* ck *) (* bs' *) trans oth stres,
        Forall (fun '(e, _) => wc_exp G1 Γ e /\ clockof e = [Cbase]) trans ->
        sc_vars Γ Hi bs ->
        sem_transitions_ck G1 Hi bs trans (oth, false) stres ->
        exists vss, Forall2 (sem_exp_ck G2 Hi bs) (trans_exp tx trans oth) vss
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
        econstructor. 1:eauto using sem_ref_sem_exp.
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
          * rewrite H12. apply case_first_of1; eauto.
            now symmetry.
          * rewrite H12. apply case_first_of2; eauto.
            now symmetry.
    Qed.

    Lemma sem_transitions_init_noreset Γ : forall ck ini oth Hi bs bs' stres,
        Forall (fun '(e, _) => wc_exp G1 Γ e /\ clockof e = [Cbase]) ini ->
        sem_clock (var_history Hi) bs ck bs' ->
        sc_vars Γ Hi bs' ->
        sem_transitions_ck G1 Hi bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres ->
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
        setoid_rewrite Str_nth_map. rewrite H13, enum_nth', first_of_nth.
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

    Fact bools_of_fwhen e : forall sc xs bs,
        bools_of xs bs ->
        bools_of (fwhenv e xs sc) (fwhenb e bs sc).
    Proof.
      intros * Hbools. rewrite bools_of_nth in *.
      intros n. repeat rewrite fwhenv_nth. repeat rewrite fwhenb_nth.
      specialize (Hbools n) as [(Hx&Hb)|[(Hx&Hb)|(Hx&Hb)]];
        destruct (_ ==b _); auto.
    Qed.

    Lemma fselect_mask_fwhen_hist : forall (Hi: history) e k stres,
        FEnv.Equiv (EqSt (A:=svalue))
                  (fselect_hist e k stres Hi)
                  (CStr.mask_hist k (fwhenb e (stres_res stres) (stres_st stres))
                                  (fwhen_hist e Hi (stres_st stres))).
    Proof.
      intros.
      unfold fselect_hist, CStr.mask_hist, fwhen_hist.
      rewrite FEnv.map_map; auto using EqStrel_Reflexive.
      eapply FEnv.map_Equiv. 2:reflexivity.
      intros * Heq. now rewrite Heq.
    Qed.

    Definition default_ann : annotation :=
      Build_annotation OpAux.bool_velus_type Cbase xH None.

    Ltac inv_branch := (Syn.inv_branch || Ty.inv_branch || Cl.inv_branch || Sem.inv_branch || LCS.inv_branch).
    Ltac inv_scope := (Syn.inv_scope || Ty.inv_scope || Cl.inv_scope || Sem.inv_scope || LCS.inv_scope).

    Local Ltac sem_new_vars :=
      subst; eapply sem_var_union3', sem_var_of_list; eauto with datatypes;
      try rewrite fst_NoDupMembers; auto.

    Lemma sc_vars_fselect ck e k sc : forall Γ Γ' Hi bs,
        sem_clock (var_history Hi) bs ck (abstract_clock sc) ->
        (forall x ck', HasClock Γ' x ck' -> HasClock Γ x ck /\ ck' = Cbase) ->
        (forall x, IsLast Γ' x -> IsLast Γ x) ->
        sc_vars Γ Hi bs ->
        sc_vars Γ' (fselect_hist e k sc Hi) (fselectb e k sc bs).
    Proof.
      intros * Hsemck Hcks Hlasts (Hsc1&Hsc2).
      split.
      - intros * Hck Hv. apply sem_var_fselect_inv in Hv as (?&Hv&Hsel).
        rewrite Hsel, ac_fselect.
        edestruct Hcks as (?&?); eauto; subst.
        eapply Hsc1 in Hv as Hsck; eauto. eapply sem_clock_det in Hsck; [|eapply Hsemck]. rewrite <-Hsck.
        eapply sem_clock_select; eauto.
      - intros * Hck Hlast Hv. apply sem_var_fselect_inv in Hv as (?&Hv&Hsel).
        rewrite Hsel, ac_fselect.
        edestruct Hcks as (?&?); eauto; subst.
        eapply Hsc2 in Hv as Hsck; eauto. eapply sem_clock_det in Hsck; [|eapply Hsemck]. rewrite <-Hsck.
        eapply sem_clock_select; eauto.
    Qed.

    Lemma sem_transitions_wt_state {PSyn prefs A} (G : @global PSyn prefs) (states : list ((enumtag * ident) * A)) :
      forall Hi bs trans default stres,
        Permutation.Permutation (List.map fst (List.map fst states)) (seq 0 (Datatypes.length states)) ->
        Forall (fun '(_, (t, _)) => InMembers t (List.map fst states)) trans ->
        In (fst default) (seq 0 (Datatypes.length states)) ->
        sem_transitions_ck G Hi bs trans default stres ->
        SForall (fun v => match v with present (e, _) => e < length states | _ => True end) stres.
    Proof.
      induction trans; intros * Hperm Hwt1 Hwt2 Hsem; inv Hwt1; inv Hsem.
      - apply SForall_forall; intros.
        apply eqst_ntheq with (n:=n) in H0. setoid_rewrite Str_nth_map in H0.
        eapply eq_ind with (P:=fun x => match x with absent => True | present (e0, _) => _ end).
        2:symmetry; apply H0. destruct (bs # n); simpl; auto.
        destruct default0. apply in_seq in Hwt2; simpl in *. lia.
      - apply IHtrans in H8; auto.
        apply SForall_forall; intros.
        apply eqst_ntheq with (n:=n) in H11. rewrite first_of_nth in H11.
        apply SForall_forall with (n:=n) in H8.
        eapply eq_ind with (P:=fun x => match x with absent => True | present (e0, _) => _ end).
        2:symmetry; apply H11. destruct (bs' # n); simpl; auto.
        rewrite fst_InMembers, Hperm in H1. apply in_seq in H1. lia.
    Qed.

    Corollary sem_automaton_wt_state1 {PSyn prefs A} (G : @global PSyn prefs) (states : list ((enumtag * ident) * branch (list transition * scope (A * list transition)))) :
      forall Hi bs bs' ini oth stres0 stres1 stres,
        Permutation.Permutation (List.map fst (List.map fst states)) (seq 0 (Datatypes.length states)) ->
        Forall (fun '(_, t) => InMembers t (List.map fst states)) ini ->
        In oth (seq 0 (Datatypes.length states)) ->
        Forall (fun '(_, Branch _ (_, Scope _ (_, trans))) =>
                  Forall (fun '(e, (t, _)) => InMembers t (List.map fst states)) trans) states ->
        sem_transitions_ck G Hi bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
        fby stres0 stres1 stres ->
        Forall (fun '((sel, _), Branch _ (_, Scope _ (_, trans))) =>
                  forall k, exists Hik,
                    (let bik := fselectb sel k stres bs in
                     sem_transitions_ck G Hik bik trans
                       (sel, false) (fselect absent sel k stres stres1))) states ->
        SForall (fun v => match v with present (e, _) => e < length states | _ => True end) stres.
    Proof.
      intros * Hperm Hwtini Hwtoth Hwtst Hsemini Hfby Hsemst.
      eapply sem_transitions_wt_state in Hsemini as Hwt0; eauto.
      2:simpl_Forall; auto.
      assert (Forall (fun state => forall k, SForall (fun v => match v with present (e, _) => e < length states | _ => True end)
                                       (fselect absent (fst (fst state)) k stres stres1)) states) as Hwt1.
      { simpl_Forall. destruct b as [?(?&[?(?&?)])]. specialize (Hsemst k); destruct_conjs.
        eapply sem_transitions_wt_state in H0; eauto.
        rewrite <-Hperm; auto. solve_In. }
      clear - Hperm Hwt0 Hwt1 Hfby.
      apply SForall_forall; intros n.
      induction n using Wf_nat.lt_wf_ind.
      apply Wf_nat.lt_wf_ind with (n:=n).
      intros n' Hrec.
      eapply fby_SForall; eauto.
      intros * Hlt. specialize (Hrec _ Hlt).
      destruct (stres # m) as [|(?&?)] eqn:Hres.
      - apply ac_fby2, eqst_ntheq with (n:=m) in Hfby.
        rewrite 2 ac_nth in Hfby. rewrite Hres in Hfby.
        destruct (stres1 # m) eqn:Hres1; try congruence.
        eapply eq_ind with (P:=fun x => match x with absent => True | present (e0, _) => _ end).
        2:symmetry; apply Hres1. simpl; auto.
      - eapply eq_ind with (P:=fun x => match x with absent => True | present (e0, _) => _ end) in Hrec; [|eauto].
        simpl in *.
        assert (In e (List.map fst (List.map fst states))) as Hin.
        { rewrite Hperm. apply in_seq. lia. }
        simpl_In. simpl_Forall.
        specialize (Hwt1 ((count (fwhenb e (stres_res stres) (stres_st stres))) # m)).
        apply SForall_forall with (n:=m) in Hwt1.
        unfold fselect in Hwt1. rewrite mask_nth, Nat.eqb_refl, fwhen_nth in Hwt1.
        unfold stres_st in Hwt1. rewrite Str_nth_map, Hres, equiv_decb_refl in Hwt1.
        auto.
    Qed.

    Corollary sem_automaton_wt_state2 {PSyn prefs A} (G : @global PSyn prefs) (states : list ((enumtag * ident) * branch (list transition * scope (A * list transition)))) :
      forall bs bs' ini stres1 stres,
        Permutation.Permutation (List.map fst (List.map fst states)) (seq 0 (Datatypes.length states)) ->
        In ini (seq 0 (Datatypes.length states)) ->
        Forall (fun '(_, Branch _ (trans, _)) =>
                  Forall (fun '(e, (t, _)) => InMembers t (List.map fst states)) trans) states ->
        fby (const_stres bs' (ini, false)) stres1 stres ->
        Forall (fun '((sel, _), Branch _ (trans, _)) =>
                  forall k, exists Hik,
                    (let bik := fselectb sel k stres bs in
                     sem_transitions_ck G Hik bik trans
                       (sel, false) (fselect absent sel k stres stres1))) states ->
        SForall (fun v => match v with present (e, _) => e < length states | _ => True end) stres.
    Proof.
      intros * Hperm Hwtoth Hwtst Hfby Hsemst.
      assert (SForall (fun s : synchronous (nat * bool) => match s with
                                                   | absent => True
                                                   | present (e, _) => e < length states
                                                   end) (const_stres bs' (ini, false))) as Hwt0.
      { apply SForall_forall. intros.
        unfold const_stres.
        rewrite Str_nth_map. destruct (bs' # n); simpl; auto.
        apply in_seq in Hwtoth. lia. }
      assert (Forall (fun state => forall k, SForall (fun v => match v with present (e, _) => e < length states | _ => True end)
                                       (fselect absent (fst (fst state)) k stres stres1)) states) as Hwt1.
      { simpl_Forall. destruct b as [?(?&[?(?&?)])]. specialize (Hsemst k); destruct_conjs.
        eapply sem_transitions_wt_state in H0; eauto.
        rewrite <-Hperm; auto. solve_In. }
      clear - Hperm Hwt0 Hwt1 Hfby.
      apply SForall_forall; intros n.
      induction n using Wf_nat.lt_wf_ind.
      apply Wf_nat.lt_wf_ind with (n:=n).
      intros n' Hrec.
      eapply fby_SForall; eauto.
      intros * Hlt. specialize (Hrec _ Hlt).
      destruct (stres # m) as [|(?&?)] eqn:Hres.
      - apply ac_fby2, eqst_ntheq with (n:=m) in Hfby.
        rewrite 2 ac_nth in Hfby. rewrite Hres in Hfby.
        destruct (stres1 # m) eqn:Hres1; try congruence.
      - assert (In n0 (List.map fst (List.map fst states))) as Hin.
        { rewrite Hperm. apply in_seq. lia. }
        simpl_In. simpl_Forall.
        specialize (Hwt1 ((count (fwhenb n0 (stres_res stres) (stres_st stres))) # m)).
        apply SForall_forall with (n:=m) in Hwt1.
        unfold fselect in Hwt1. rewrite mask_nth, Nat.eqb_refl, fwhen_nth in Hwt1.
        eapply eq_ind with (P:=fun x => match x with absent => True | present (e0, _) => _ end) in Hwt1.
        2:{ unfold stres_st. rewrite Str_nth_map. setoid_rewrite Hres. rewrite equiv_decb_refl. reflexivity. }
        assumption.
    Qed.

    Corollary sem_automaton_wt_state3 {PSyn prefs A} (G : @global PSyn prefs) (states : list ((enumtag * ident) * branch (list transition * scope (A * list transition)))) :
      forall bs bs' ini stres1 stres,
        Permutation.Permutation (List.map fst (List.map fst states)) (seq 0 (Datatypes.length states)) ->
        In ini (seq 0 (Datatypes.length states)) ->
        Forall (fun '(_, Branch _ (trans, _)) =>
                  Forall (fun '(e, (t, _)) => InMembers t (List.map fst states)) trans) states ->
        fby (const_stres bs' (ini, false)) stres1 stres ->
        Forall (fun '((sel, _), Branch _ (trans, _)) =>
                  forall k, exists Hik,
                    (let bik := fselectb sel k stres bs in
                     sem_transitions_ck G Hik bik trans
                       (sel, false) (fselect absent sel k stres stres1))) states ->
        SForall (fun v => match v with present (e, _) => e < length states | _ => True end) stres1.
    Proof.
      intros * Hperm Hwtoth Hwtst Hfby Hsemst.
      assert (SForall (fun s : synchronous (nat * bool) => match s with
                                                   | absent => True
                                                   | present (e, _) => e < length states
                                                   end) (const_stres bs' (ini, false))) as Hwt0.
      { apply SForall_forall. intros.
        unfold const_stres.
        rewrite Str_nth_map. destruct (bs' # n); simpl; auto.
        apply in_seq in Hwtoth. lia. }
      assert (Forall (fun state => forall k, SForall (fun v => match v with present (e, _) => e < length states | _ => True end)
                                       (fselect absent (fst (fst state)) k stres stres1)) states) as Hwt1.
      { simpl_Forall. destruct b as [?(?&[?(?&?)])]; destruct_conjs. specialize (Hsemst k); destruct_conjs.
        eapply sem_transitions_wt_state in H0; eauto.
        rewrite <-Hperm; auto. solve_In. }
      eapply sem_automaton_wt_state2 in Hfby as Hwt2; eauto.
      apply SForall_forall; intros n. eapply SForall_forall with (n:=n) in Hwt2.
      apply ac_fby2, eqst_ntheq with (n:=n) in Hfby. rewrite 2 ac_nth in Hfby.
      destruct (stres1 # n) eqn:Hstres1, (stres # n) eqn:Hstres; auto; try congruence.
      destruct v0, v.
      assert (In n0 (List.map fst (List.map fst states))) as Hin.
      { rewrite Hperm. apply in_seq. lia. }
      simpl_In. simpl_Forall.
      specialize (Hwt1 ((count (fwhenb n0 (stres_res stres) (stres_st stres))) # n)).
      apply SForall_forall with (n:=n) in Hwt1.
      unfold fselect in Hwt1. rewrite mask_nth, Nat.eqb_refl, fwhen_nth in Hwt1.
      eapply eq_ind with (P:=fun x => match x with absent => True | present (e0, _) => _ end) in Hwt1.
      2:{ unfold stres_st. rewrite Str_nth_map. setoid_rewrite Hstres. rewrite equiv_decb_refl. reflexivity. }
      rewrite Hstres1 in Hwt1.
      assumption.
    Qed.

    Lemma auto_block_sem : forall blk Γty Γck Hi bs blk' tys st st',
        (forall x, IsVar Γty x -> AtomOrGensym last_prefs x) ->
        (forall x, ~IsLast Γty x) ->
        (forall x, ~IsLast Γck x) ->
        (forall x, IsVar Γck x -> IsVar Γty x) ->
        NoDupLocals (List.map fst Γty) blk ->
        GoodLocals last_prefs blk ->
        nolast_block blk ->
        wt_block G1 Γty blk ->
        wc_block G1 Γck blk ->
        dom_ub Hi Γty ->
        sc_vars Γck Hi bs ->
        sem_block_ck G1 Hi bs blk ->
        auto_block blk st = (blk', tys, st') ->
        sem_block_ck G2 Hi bs blk'.
    Proof.
      induction blk using block_ind2; intros * Hat Hnl1 Hnl2 Hincl Hnd Hgood Hnl Hwt Hwc Hdom Hsc Hsem Haut;
        inv Hnd; inv Hgood; inv Hnl; inv Hwt; inv Hwc; inv Hsem; repeat inv_bind.

      - (* equation *)
        constructor; eauto using sem_ref_sem_equation.

      - (* reset *)
        econstructor; eauto using sem_ref_sem_exp.
        intros k. specialize (H16 k).
        auto_block_simpl_Forall.
        eapply H; eauto using sc_vars_mask.
        + now apply dom_ub_map.

      - (* switch *)
        econstructor; eauto using sem_ref_sem_exp.
        auto_block_simpl_Forall.
        repeat inv_branch. repeat inv_bind.
        assert (sem_clock (var_history Hi) bs ck (abstract_clock sc)) as Hsemck.
        { eapply sc_exp in H15; eauto.
          take (clockof _ = _) and rewrite it in H15; simpl_Forall; auto. }
        do 2 esplit; eauto. constructor.
        auto_block_simpl_Forall.
        eapply H with (Γck:=Γ'); eauto.
        + intros * ?. eapply Hnl2; eauto.
        + intros ? Hin. inv Hin. simpl_In. edestruct H14 as (Hck&_); eauto with senv.
        + eapply dom_ub_refines; eauto.
        + eapply sc_vars_when; eauto.

      - (* automaton (weak) *)
        assert (Forall (fun id => ~IsVar Γty id) [x1;x3;x5;x7]) as Hnin1.
        { simpl_Forall; simpl in *. intros Hv.
          apply Hat in Hv.
          repeat (take (CA.fresh_ident _ = _) and eapply fresh_ident_prefixed in it as (?&?&?); subst).
          take (_ \/ _ \/ _) and destruct it as [|[|[|[|]]]]; subst; try eapply contradict_AtomOrGensym in Hv; eauto using auto_not_in_last_prefs.
        }
        assert (Forall (fun id => ~ FEnv.In (Var id) Hi) [x1;x3;x5;x7]) as Hnin2.
        { simpl_Forall; simpl in *. intros Henvin. eapply Hdom in Henvin; eauto.
          take (_ \/ _ \/ _) and destruct it as [|[|[|[|]]]]; subst; eauto.
        }
        assert (NoDup [x1;x3;x5;x7]) as Hnd.
        { eapply fresh_idents_NoDup; eauto 7 with fresh. }
        assert (NoDup [Var x1;Var x3;Var x5;Var x7]) as Hndv.
        { apply FinFun.Injective_map_NoDup with (f:=Var) in Hnd; auto. intros ?? Eq; now inv Eq. }
        remember (FEnv.of_list [(Var x1, stres_proj1 stres); (Var x3, stres_proj1 stres1);
                                (Var x5, stres_proj2 stres); (Var x7, stres_proj2 stres1)]) as Hi'.
        assert (FEnv.refines (@EqSt _) Hi (Hi + Hi')) as Href'.
        { subst. intros ?? Hfind. do 2 esplit; [reflexivity|].
          apply FEnv.union2; auto. destruct (FEnv.of_list _ _) eqn:contra; auto.
          apply FEnv.of_list_find_In in contra; simpl_Forall.
          assert (FEnv.In x11 Hi) as Hin by (econstructor; eauto).
          destruct contra as [Heq|[Heq|[Heq|[Heq|[]]]]]; inv Heq; congruence. }

        assert (abstract_clock stres ≡ bs') as Hac.
        { take (sem_transitions_ck _ _ _ _ _ _) and eapply sc_transitions in it; eauto. 3:simpl_Forall; eauto.
          - take (fby _ _ _) and apply ac_fby1 in it; now rewrite <-it.
          - eapply sc_vars_subclock; eauto. }

        assert (forall x, IsVar Γ' x -> IsVar Γck x) as Hincl2.
        { take (forall x ck, HasClock Γ' _ _ -> _) and clear - it.
          intros ? Hv. inv Hv. simpl_In. edestruct it; eauto with senv.  }
        assert (incl (List.map fst Γ') (List.map fst Γck)) as Hinclfst by (auto using IsVar_incl_fst).

        constructor. eapply Sscope with (Hi':=Hi').
        + subst. split; intros *; rewrite FEnv.of_list_In.
          * rewrite IsVar_senv_of_decls, 2 fst_InMembers; simpl.
            split; intros [Eq|[Eq|[Eq|[Eq|Eq]]]]; inv Eq; auto.
          * split; [intros Hin|intros Hlast; inv Hlast]; simpl in *.
            destruct Hin as [Eq|[Eq|[Eq|[Eq|Eq]]]]; inv Eq.
            destruct H22 as [Eq|[Eq|[Eq|[Eq|Eq]]]]; inv Eq; simpl in *; congruence.
        + split; intros * Hcka.
          2:{ intros Hla. inv Hla; simpl_In.
              take (_ \/ _ \/ _) and destruct it as [He|[He|[He|[He|He]]]]; inv He; simpl in *; congruence. }
          simpl in *. intros Hv.
          apply sem_var_union' in Hv as [(Hnin&_)|Hv].
          1:{ exfalso. apply Hnin. subst.
              apply FEnv.of_list_In, fst_InMembers; simpl.
              inv Hcka; simpl in *. take (_ \/ _ \/ _) and destruct it as [He|[He|[He|[He|He]]]]; inv He; eauto.
          }
          assert (ck0 = ck); [|subst].
          { inv Hcka.
            take (_ \/ _ \/ _) and destruct it as [He|[He|[He|[He|He]]]]; inv He; auto. }
          subst. apply sem_var_of_list' in Hv as (?&Heq&Hin). rewrite Heq. simpl_In.
          take (_ \/ _ \/ _) and destruct it as [He|[He|[He|[He|He]]]]; inv He.

          1-4:(eapply sem_clock_refines; eauto using var_history_refines;
               try rewrite ac_stres_proj1; try rewrite ac_stres_proj2;
               try rewrite Hac; auto; simpl).
          1,2:take (fby _ _ _) and apply ac_fby2 in it; rewrite it, Hac; auto.
        + repeat constructor.
          *{ econstructor. repeat constructor. 2:simpl; rewrite app_nil_r; repeat constructor.
             econstructor; repeat constructor.
             3,4,6,7:sem_new_vars.
             - eapply sem_exp_refines; [eauto|].
               eapply init_state_exp_sem; eauto using sc_vars_subclock.
             - eapply add_whens_enum_sem, sem_clock_refines; eauto using var_history_refines.
             - repeat constructor.
               + apply fby_stres_proj1; auto.
               + take (sem_transitions_ck _ _ _ _ _ _) and eapply sem_transitions_init_noreset in it; eauto using sc_vars_subclock.
                 rewrite <-it.
                 apply fby_stres_proj2; auto.
           }
          *{ econstructor; simpl.
             - repeat constructor. sem_new_vars.
             - repeat constructor.
               take (sem_transitions_ck _ _ _ _ _ _) and eapply sem_automaton_wt_state1 in it; eauto.
               + apply SForall_forall; intros n. apply SForall_forall with (n:=n) in it.
                 setoid_rewrite Str_nth_map. destruct (stres # n) as [|(?&?)] eqn:Hst; simpl in *; auto.
                 constructor; simpl.
                 eapply eq_ind with (P:=fun x => match x with absent => True | present (e, _) => e < length states end) in it; [|eauto].
                 rewrite 2 map_length. congruence.
               + simpl_Forall; eauto.
               + rewrite <-H11. apply fst_InMembers; auto.
               + simpl_Forall. repeat inv_branch. repeat inv_scope. simpl_Forall; eauto.
               + simpl_Forall. repeat inv_branch. repeat inv_scope. intros. specialize (H26 k); destruct_conjs.
                 repeat inv_branch. repeat inv_scope.
                 esplit; eauto.
             - auto_block_simpl_Forall.
               do 2 esplit.
               1:{ simpl. apply when_hist_restrict_ac with (xs:=Var x1::Var x3::Var x5::Var x7::List.map (fun '(x, _) => Var x) Γ').
                   1:{ unfold stres_proj1, stres_st. apply SForall_forall. intros n.
                       rewrite Str_nth_map. cases_eqn Heq; auto. }
                   intros * Hin Hsem.
                   eapply sem_var_union in Hsem.
                   simpl in *. repeat rewrite <-or_assoc in Hin.
                   destruct Hin as [Hin|Hin], Hsem as [Hsem|Hsem].
                   - exfalso. eapply sem_var_In in Hsem; eauto.
                     destruct Hin as [[[|]|]|]; subst; eauto.
                   - apply sem_var_of_list' in Hsem as (?&Heq1&[Heq|[Heq|[Heq|[Heq|Heq]]]]); inv Heq;
                       rewrite Heq1; repeat rewrite ac_stres_proj1; repeat rewrite ac_stres_proj2.
                     + reflexivity.
                     + take (fby _ _ _) and apply ac_fby2 in it; auto.
                     + reflexivity.
                     + take (fby _ _ _) and apply ac_fby2 in it; auto.
                   - rewrite ac_stres_proj1, Hac. eapply sem_clock_det; eauto.
                     simpl_In. edestruct H18; eauto with senv.
                     eapply Hsc in Hsem; eauto.
                   - exfalso. simpl_In.
                     assert (IsVar Γty i0) as Hv.
                     { eapply Hincl, IsVar_fst, Hinclfst, in_map_iff; solve_In. }
                     apply sem_var_of_list' in Hsem as (?&_&[Heq|[Heq|[Heq|[Heq|Heq]]]]); inv Heq; eauto.
               }
               repeat inv_branch. repeat inv_bind.
               repeat constructor. econstructor.
               + econstructor; simpl. apply sem_var_restrict; eauto with datatypes.
                 apply sem_var_fwhen. sem_new_vars.
               + apply bools_of_fwhen, bools_of_stres_proj2.
               + intros k. specialize (H26 k); destruct_conjs.
                 take (select_hist _ _ _ _ _) and rename it into Hsel.
                 assert (Hsel':=Hsel). apply select_hist_fselect_hist in Hsel'. simpl in *.
                 repeat inv_branch. destruct s.
                 take (sem_scope_ck _ _ _ _) and eapply sem_scope_refines2, sem_scope_restrict2 in it. 3,4:eauto.
                 2:{ apply Forall_forall; intros; simpl_In.
                     edestruct H18 as (?&Hbase); eauto with senv. rewrite Hbase; constructor. }
                 repeat inv_scope. repeat inv_bind. subst Γ'0 Γ'1.
                 repeat constructor.

                 assert (forall x, ~ IsLast (senv_of_decls l) x) as Hnolast2.
                 { intros * Hlast. inv Hlast. simpl_In. simpl_Forall.
                   subst; simpl in *; congruence. }

                 assert (forall x, ~ IsLast Γ' x) as Hnl2' by (intros ??; eapply Hnl2; eauto).

                 remember ((CStr.mask_hist k (fwhenb e (stres_res stres) (stres_proj1 stres))
                              (FEnv.restrict
                                 (fwhen_hist e
                                    (Hi +
                                       FEnv.of_list
                                         [(Var x1, stres_proj1 stres); (Var x3, stres_proj1 stres1); (Var x5, stres_proj2 stres); (Var x7, stres_proj2 stres1)])
                                    (stres_proj1 stres))
                                 (Var x1 :: Var x3 :: Var x5 :: Var x7 :: List.map (fun '(x, _) => Var x) Γ')) + Hi')) as Hi''.
                 remember (maskb _ _ _) as bs''.

                 assert (FEnv.refines (@EqSt _) (restrict (fselect_hist e k stres Hi) Γ' + Hi') Hi'') as Href1.
                 { intros ?? Hf. subst. apply FEnv.union4' in Hf as [Hf|(Hf&Hnf)].
                   - do 2 esplit; eauto using FEnv.union3'. reflexivity.
                   - apply FEnv.restrict_find_inv in Hf as (Hin&Hf).
                     destruct x12; [apply vars_of_senv_Var in Hin|apply vars_of_senv_Last, Hnl2' in Hin as []].
                     simpl_fenv.
                     do 2 esplit; try reflexivity; simpl.
                     apply FEnv.union2; auto.
                     erewrite FEnv.restrict_find; eauto with datatypes. reflexivity.
                     + clear - Hin. do 4 right. inv Hin. solve_In.
                     + erewrite FEnv.union2; eauto. reflexivity.
                       apply FEnv.of_list_None. intros Him. simpl in *.
                       take (_ \/ _ \/ _) and destruct it as [He|[He|[He|[He|He]]]]; inv He.
                       all:take (_ = Some _) and apply FEnv.find_In in it; eauto.
                 }

                 assert (sc_vars (senv_of_decls l) Hi'' bs'') as Hsc1'.
                 { subst. intros. eapply sc_vars_refines; simpl. 1,4:eauto.
                   - intros * Hinm _. take (dom Hi' _) and now apply FEnv.union_In, or_intror, it.
                   - intros * Hl. clear - Hl H39. inv Hl. simpl_In. simpl_Forall. subst. simpl in *. congruence. }

                 assert (sc_vars (Γ' ++ senv_of_decls l) (restrict (fselect_hist e k stres Hi) Γ' + Hi') bs'') as Hsc2.
                 { eapply local_hist_sc_vars with (Γ:=Γ'); subst; eauto using List.incl_refl, restrict_dom_ub.
                   - intros * Hinm Hin. take (forall x, InMembers x _ -> ~_) and eapply it; eauto.
                     eapply IsVar_incl_fst, IsVar_fst; eauto.
                   - eapply sc_vars_restrict, sc_vars_refines, sc_vars_fselect; eauto; try reflexivity.
                     + simpl_Forall. simpl_In. take (forall x ck, HasClock Γ' _ _ -> _) and edestruct it as (?&Hck); eauto with senv.
                       rewrite Hck. constructor.
                     + now rewrite Hac.
                 }

                 assert (forall x, In x [x1; x3; x5; x7] -> ~InMembers x l) as Hdisj.
                 { intros * Hin1 Hin2. apply InMembers_In in Hin2; destruct_conjs. simpl_Forall.
                   repeat (take (CA.fresh_ident _ = _) and eapply fresh_ident_prefixed in it as (?&?&?); subst).
                   destruct Hin1 as [|[|[|[|]]]]; eauto; subst; eapply contradict_AtomOrGensym; eauto using auto_not_in_last_prefs.
                 }

                 assert (sc_vars (Γ' ++ senv_of_decls l) Hi'' bs'') as Hsc2'.
                 { subst. intros. eapply sc_vars_refines; simpl. 1,4:eauto.
                   - intros * Hinm Hin.
                     assert (~In x12 [x1;x3;x5;x7]) as Hnin.
                     { intros contra. apply IsVar_app in Hinm as [Hinm|Hinm].
                       - destruct contra as [|[|[|[|]]]]; subst; eauto.
                       - eapply Hdisj, IsVar_senv_of_decls; eauto.
                     }
                     unfold restrict. rewrite FEnv.union_In, FEnv.restrict_In, vars_of_senv_Var. setoid_rewrite FEnv.map_in_iff.
                     apply FEnv.union_In in Hin as [Hin|]; auto. setoid_rewrite FEnv.map_in_iff in Hin.
                     rewrite FEnv.restrict_In in Hin. setoid_rewrite FEnv.map_in_iff in Hin.
                     rewrite FEnv.union_In, FEnv.of_list_In in Hin.
                     destruct Hin as ([|Hin2]&Hin).
                     + destruct Hin as [In|[In|[In|[In|In]]]]; try inv In; auto.
                       1-4:exfalso; eauto with datatypes.
                       left; split; auto. clear - In. econstructor. solve_In.
                     + exfalso. rewrite fst_InMembers in Hin2; simpl in Hin2.
                       destruct Hin2 as [In|[In|[In|[In|In]]]]; try inv In; eauto with datatypes.
                   - intros * L. exfalso. apply IsLast_app in L as [L|L]; [eapply Hnl2'; eauto|].
                     clear - L H39. inv L. simpl_In. simpl_Forall. subst. simpl in *. congruence.
                 }

                 eapply Sscope with (Hi':=Hi'). 3:constructor. all:eauto.
                 * subst; eauto.
                 *{ take (sem_transitions_ck _ _ _ _ _ _) and eapply sem_transitions_refines, sem_transitions_restrict
                      with (Γ:=((x1, default_ann)::(x3, default_ann)::(x5, default_ann)::(x7, default_ann)::Γ' ++ senv_of_decls l)) in it; eauto.
                    2:{ simpl_Forall. eapply wx_exp_incl. 3:eauto with lclocking.
                        1,2:intros * Hv; inv Hv; econstructor; eauto using InMembers_cons with datatypes. }
                    eapply trans_exp_sem in it as (ss&Htranssem&Hconcat); eauto.
                    + repeat constructor. econstructor. 2:rewrite Hconcat; simpl.
                      * eapply Forall2_impl_In; [|eauto]; intros.
                        subst. eapply sem_exp_refines; [|eauto].
                        eapply FEnv.restrict_refines; eauto using EqStrel_Reflexive, EqStrel_Transitive.
                      * assert (forall x, In x [x1;x3;x5;x7] -> ~FEnv.In (Var x) Hi') as Hdisj'.
                        { intros * Hin Hinenv.
                          eapply Hdisj; eauto. take (dom Hi' _) and apply IsVar_senv_of_decls, it; auto. }
                        repeat constructor; subst; [rewrite stres_proj1_fselect|rewrite stres_proj2_fselect].
                        1,2:(eapply sem_var_union2; eauto with datatypes;
                             eapply sem_var_mask, sem_var_restrict, sem_var_fwhen;
                             eauto with datatypes; sem_new_vars).
                    + simpl_Forall; eauto.
                    + eapply sc_vars_restrict; eauto; simpl.
                      * intros ??; simpl; eauto with datatypes.
                      * simpl_app. apply Forall_app; split; simpl_Forall.
                        -- edestruct H18 as (?&Hbase); eauto with senv. rewrite Hbase; constructor.
                        -- eapply wc_clock_incl; [|eauto]. repeat apply incl_tl. reflexivity.
                      * subst; eauto.
                   }
                 *{ auto_block_simpl_Forall.
                    eapply sem_block_refines, H
                      with (Γck:=Γ'++_) (Γty:=Γty++_) (Hi:=(FEnv.restrict _ _)); eauto.
                    9:{ eapply sem_block_restrict. 3:eauto. all:eauto.
                        unfold wc_env. simpl_Forall; simpl_In.
                        apply in_app_iff in Hin as [Hin|Hin]; simpl_In; simpl_Forall; eauto.
                        edestruct H18 as (_&Hbase); eauto with senv. rewrite Hbase; constructor.
                    } all:simpl.
                    - etransitivity; eauto. eapply FEnv.restrict_refines; eauto using EqStrel_Reflexive.
                    - intros * Hv. inv Hv. take (InMembers _ _) and apply InMembers_app in it as [Hin|Hin]; apply InMembers_In in Hin as (?&?).
                      + apply Hat; eauto with senv.
                      + simpl_In. simpl_Forall; auto.
                    - apply NoLast_app; auto.
                    - apply NoLast_app; auto.
                    - intros * Hv. rewrite IsVar_app in *. destruct Hv as [Hv|]; auto.
                    - now rewrite map_app, map_fst_senv_of_decls.
                    - eapply dom_ub_incl', restrict_dom_ub.
                      + intros *; rewrite 2 IsVar_app; intros [|]; eauto.
                      + intros *; rewrite 2 IsLast_app; intros [|]; eauto.
                        exfalso; eapply Hnl2'; eauto.
                    - eapply sc_vars_restrict; eauto.
                      + reflexivity.
                      + simpl_Forall; simpl_In.
                        apply in_app_iff in Hin as [Hin|Hin]; simpl_In; simpl_Forall; eauto.
                        edestruct H18 as (_&Hbase); eauto with senv. rewrite Hbase; constructor.
                   }
            }

      - (* automaton (strong) *)
        assert (Forall (fun id => ~IsVar Γty id) [x1;x3;x5;x7]) as Hnin1.
        { simpl_Forall; simpl in *. intros Hv.
          apply Hat in Hv.
          repeat (take (CA.fresh_ident _ = _) and eapply fresh_ident_prefixed in it as (?&?&?); subst).
          take (_ \/ _ \/ _) and destruct it as [|[|[|[|]]]]; subst; try eapply contradict_AtomOrGensym in Hv; eauto using auto_not_in_last_prefs.
        }
        assert (Forall (fun id => ~ FEnv.In (Var id) Hi) [x1;x3;x5;x7]) as Hnin2.
        { simpl_Forall; simpl in *. intros Henvin. eapply Hdom in Henvin; eauto.
          take (_ \/ _ \/ _) and destruct it as [|[|[|[|]]]]; subst; eauto.
        }
        assert (NoDup [x1;x3;x5;x7]) as Hnd.
        { eapply fresh_idents_NoDup; eauto. }
        assert (NoDup [Var x1;Var x3;Var x5;Var x7]) as Hndv.
        { apply FinFun.Injective_map_NoDup with (f:=Var) in Hnd; auto. intros ?? Eq; now inv Eq. }
        remember (FEnv.of_list [(Var x1, stres_proj1 stres); (Var x3, stres_proj1 stres1);
                                (Var x5, stres_proj2 stres); (Var x7, stres_proj2 stres1)]) as Hi'.
        assert (FEnv.refines (@EqSt _) Hi (Hi + Hi')) as Href'.
        { subst. intros ?? Hfind. do 2 esplit; [reflexivity|].
          apply FEnv.union2; auto. destruct (FEnv.of_list _ _) eqn:contra; auto.
          apply FEnv.of_list_find_In in contra; simpl_Forall.
          assert (FEnv.In x11 Hi) as Hin by (econstructor; eauto).
          destruct contra as [Heq|[Heq|[Heq|[Heq|[]]]]]; inv Heq; congruence. }

        assert (abstract_clock stres ≡ bs') as Hac.
        { take (fby _ _ _) and apply ac_fby1 in it. rewrite <-it. apply const_stres_ac. }
        assert (abstract_clock stres1 ≡ bs') as Hac1.
        { take (fby _ _ _) and apply ac_fby2 in it. now rewrite it. }

        assert (forall x, IsVar Γ' x -> IsVar Γck x) as Hincl2.
        { take (forall x ck, HasClock Γ' _ _ -> _) and clear - it.
          intros ? Hv. inv Hv. simpl_In. edestruct it; eauto with senv.  }
        assert (incl (List.map fst Γ') (List.map fst Γck)) as Hinclfst by (auto using IsVar_incl_fst).

        assert (forall x, ~ IsLast Γ' x) as Hnl2' by (intros ??; eapply Hnl2; eauto).

        constructor. eapply Sscope with (Hi':=Hi').
        + subst. split; intros *; rewrite FEnv.of_list_In.
          * rewrite IsVar_senv_of_decls, 2 fst_InMembers; simpl.
            split; intros [Eq|[Eq|[Eq|[Eq|Eq]]]]; inv Eq; auto.
          * split; [intros Hin|intros Hlast; inv Hlast]; simpl in *.
            destruct Hin as [Eq|[Eq|[Eq|[Eq|Eq]]]]; inv Eq.
            destruct H25 as [Eq|[Eq|[Eq|[Eq|Eq]]]]; inv Eq; simpl in *; congruence.
        + split; intros * Hcka.
          2:{ intros Hla. inv Hla; simpl_In.
              take (_ \/ _ \/ _) and destruct it as [He|[He|[He|[He|He]]]]; inv He; simpl in *; congruence. }
          simpl in *. intros Hv.
          apply sem_var_union' in Hv as [(Hnin&_)|Hv].
          1:{ exfalso. apply Hnin. subst.
              apply FEnv.of_list_In, fst_InMembers; simpl.
              inv Hcka; simpl in *. take (_ \/ _ \/ _) and destruct it as [He|[He|[He|[He|He]]]]; inv He; eauto.
          }
          assert (ck0 = ck); [|subst].
          { inv Hcka.
            take (_ \/ _ \/ _) and destruct it as [He|[He|[He|[He|He]]]]; inv He; auto. }
          subst. apply sem_var_of_list' in Hv as (?&Heq&Hin). rewrite Heq. simpl_In.
          take (_ \/ _ \/ _) and destruct it as [He|[He|[He|[He|He]]]]; inv He.

          1-4:(eapply sem_clock_refines; eauto using var_history_refines;
               try rewrite ac_stres_proj1; try rewrite ac_stres_proj2;
               try rewrite Hac; auto; simpl).
          1,2:take (fby _ _ _) and apply ac_fby2 in it; rewrite it, Hac; auto.
        + repeat constructor.
          *{ econstructor. repeat constructor. 2:simpl; rewrite app_nil_r; repeat constructor.
             econstructor; repeat constructor.
             3,4,6,7:sem_new_vars.
             - eapply add_whens_enum_sem, sem_clock_refines; eauto using var_history_refines.
             - eapply add_whens_enum_sem, sem_clock_refines; eauto using var_history_refines.
             - repeat constructor.
               + take (fby _ _ _) and apply fby_stres_proj1 in it; auto.
                 rewrite stres_proj1_const in it; auto.
               + take (fby _ _ _) and apply fby_stres_proj2 in it. rewrite stres_proj2_const in it; auto.
           }
          *{ econstructor; simpl.
             - repeat constructor. sem_new_vars.
             - repeat constructor.
               take (fby _ _ _) and eapply sem_automaton_wt_state2 in it; eauto.
               + apply SForall_forall; intros n. apply SForall_forall with (n:=n) in it.
                 setoid_rewrite Str_nth_map. destruct (stres # n) as [|(?&?)] eqn:Hst; simpl in *; auto.
                 constructor; simpl.
                 eapply eq_ind with (P:=fun x => match x with absent => True | present (e, _) => e < length states end) in it; [|eauto].
                 simpl in *; auto. now rewrite 2 map_length.
               + rewrite <-H10. apply fst_InMembers; auto.
               + simpl_Forall; repeat inv_branch. simpl_Forall; auto.
               + simpl_Forall; repeat inv_branch. intros. specialize (H23 k); destruct_conjs.
                 repeat inv_branch.
                 esplit; eauto.
             - simpl_Forall.
               do 2 esplit.
               1:{ simpl. apply when_hist_restrict_ac with (xs:=Var x1::Var x3::Var x5::Var x7::List.map (fun '(x, _) => Var x) Γ').
                   1:{ unfold stres_proj1, stres_st. apply SForall_forall. intros n.
                       rewrite Str_nth_map. cases_eqn Heq; auto. }
                   intros * Hin Hsem.
                   eapply sem_var_union in Hsem; eauto.
                   simpl in *. repeat rewrite <-or_assoc in Hin.
                   destruct Hin as [Hin|Hin], Hsem as [Hsem|Hsem].
                   - exfalso. eapply sem_var_In in Hsem; eauto.
                     destruct Hin as [[[|]|]|]; subst; eauto.
                   - apply sem_var_of_list' in Hsem as (?&Heq1&[Heq|[Heq|[Heq|[Heq|Heq]]]]); inv Heq;
                       rewrite Heq1; repeat rewrite ac_stres_proj1; repeat rewrite ac_stres_proj2.
                     + reflexivity.
                     + take (fby _ _ _) and apply ac_fby2 in it; auto.
                     + reflexivity.
                     + take (fby _ _ _) and apply ac_fby2 in it; auto.
                   - rewrite ac_stres_proj1, Hac. eapply sem_clock_det; eauto.
                     simpl_In. edestruct H17; eauto with senv.
                     eapply Hsc in Hsem; eauto.
                   - exfalso. simpl_In.
                     assert (IsVar Γty i0) as Hv.
                     { eapply Hincl, IsVar_fst, Hinclfst, in_map_iff; solve_In. }
                     apply sem_var_of_list' in Hsem as (?&_&[Heq|[Heq|[Heq|[Heq|Heq]]]]); inv Heq; eauto.
               }
               repeat inv_branch. repeat inv_bind.
               repeat constructor. econstructor.
               + econstructor; simpl. apply sem_var_restrict; eauto with datatypes.
                 apply sem_var_fwhen. sem_new_vars.
               + apply bools_of_fwhen, bools_of_stres_proj2.
               + intros k. specialize (H23 k); destruct_conjs.
                 take (select_hist _ _ _ _ _) and rename it into Hsel.
                 assert (Hsel':=Hsel). apply select_hist_fselect_hist in Hsel'. simpl in *.
                 repeat inv_branch. destruct s.
                 repeat constructor.
                 *{ take (sem_transitions_ck _ _ _ _ _ _) and
                      eapply sem_transitions_refines, sem_transitions_restrict with (Γ:=((x1, default_ann)::(x3, default_ann)::(x5, default_ann)::(x7, default_ann)::Γ')) in it; eauto.
                    2:{ simpl_Forall. eapply wx_exp_incl. 3:eauto with lclocking.
                        1,2:intros * Hv; inv Hv; econstructor; eauto using InMembers_cons with datatypes. }
                    eapply sem_equation_ck_morph. 2,3:reflexivity.
                    1:{ instantiate (1:=(FEnv.restrict _ _)).
                        - setoid_rewrite <-FEnv.restrict_map; auto using EqStrel_Reflexive. apply FEnv.restrict_Equiv.
                          setoid_rewrite <-fselect_mask_fwhen_hist. reflexivity. }
                    eapply trans_exp_sem in it as (ss&Htranssem&Hconcat); eauto.
                    - repeat constructor. econstructor. 2:rewrite Hconcat; simpl.
                      + eapply Forall2_impl_In; [|eauto]; intros.
                        subst. eapply sem_exp_refines; eauto. simpl.
                        unfold restrict. rewrite vars_of_senv_NoLast.
                        2:{ intros * contra. inv contra. simpl in *.
                            destruct H38 as [Eq|[Eq|[Eq|[Eq|]]]]; try inv Eq; simpl in *; try congruence.
                            eapply Hnl2'; eauto with senv. }
                        eapply FEnv.restrict_refines', FEnv.refines_map; [|eauto].
                        intros * Heq; now rewrite Heq.
                      + repeat constructor; subst; [rewrite stres_proj1_fselect|rewrite stres_proj2_fselect].
                        1,2:eapply sem_var_restrict, sem_var_fselect; eauto with datatypes.
                        1,2:sem_new_vars; simpl in *; auto.
                    - simpl_Forall; eauto.
                    - eapply sc_vars_restrict; eauto.
                      + intros ??; simpl; eauto with datatypes.
                      + simpl_Forall; simpl_In; simpl_Forall.
                        edestruct H17 as (?&Hbase); eauto with senv. rewrite Hbase; constructor.
                      + eapply sc_vars_morph, sc_vars_fselect; eauto. 2:reflexivity.
                        simpl; now symmetry.
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
                 simpl in *; auto. now rewrite 2 map_length.
               + rewrite <-H10. apply fst_InMembers; auto.
               + simpl_Forall. repeat inv_branch. simpl_Forall; auto.
               + simpl_Forall. repeat inv_branch. intros. specialize (H23 k); destruct_conjs.
                 repeat inv_branch; repeat inv_scope. subst Γ'0 Γ'1.
                 esplit; eauto.
             - auto_block_simpl_Forall.
               do 2 esplit.
               1:{ simpl. apply when_hist_restrict_ac with (xs:=Var x1::Var x3::Var x5::Var x7::List.map (fun '(x, _) => Var x) Γ').
                   1:{ unfold stres_proj1, stres_st. apply SForall_forall. intros n.
                       rewrite Str_nth_map. cases_eqn Heq; auto. }
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
                     simpl_In. edestruct H17; eauto with senv.
                     eapply Hsc in Hsem; eauto.
                   - exfalso. simpl_In.
                     assert (IsVar Γty i0) as Hv.
                     { eapply Hincl, IsVar_fst, Hinclfst, in_map_iff; solve_In. }
                     apply sem_var_of_list' in Hsem as (?&_&[Heq|[Heq|[Heq|[Heq|Heq]]]]); inv Heq; eauto.
               }
               repeat inv_branch. repeat inv_bind.
               repeat constructor. econstructor.
               + econstructor; simpl. apply sem_var_restrict; eauto with datatypes.
                 apply sem_var_fwhen. sem_new_vars.
               + apply bools_of_fwhen, bools_of_stres_proj2.
               + intros k. specialize (H24 k); destruct_conjs.
                 take (select_hist _ _ _ _ _) and rename it into Hsel.
                 assert (Hsel':=Hsel). apply select_hist_fselect_hist in Hsel'. simpl in *.
                 repeat inv_branch. destruct s.
                 take (sem_scope_ck _ _ _ _) and eapply sem_scope_refines3, sem_scope_restrict3 in it. 3,4:eauto.
                 2:{ apply Forall_forall; intros; simpl_In.
                     edestruct H17 as (?&Hbase); eauto with senv. rewrite Hbase; constructor. }
                 repeat inv_scope. repeat inv_bind. subst Γ'0 Γ'1.
                 repeat constructor.

                 assert (forall x, ~ IsLast (senv_of_decls l0) x) as Hnolast2.
                 { intros * Hlast. inv Hlast. simpl_In. simpl_Forall.
                   subst; simpl in *; congruence. }

                 remember ((CStr.mask_hist k (fwhenb e (stres_res stres1) (stres_proj1 stres1))
                              (FEnv.restrict
                                 (fwhen_hist e
                                    (Hi +
                                       FEnv.of_list
                                         [(Var x1, stres_proj1 stres); (Var x3, stres_proj1 stres1); (Var x5, stres_proj2 stres); (Var x7, stres_proj2 stres1)])
                                    (stres_proj1 stres1))
                                 (Var x1 :: Var x3 :: Var x5 :: Var x7 :: List.map (fun '(x, _) => Var x) Γ')) + Hi')) as Hi''.
                 remember (maskb _ _ _) as bs''.

                 assert (FEnv.refines (@EqSt _) (restrict (fselect_hist e k stres1 Hi) Γ' + Hi') Hi'') as Href1.
                 { intros ?? Hf. subst. apply FEnv.union4' in Hf as [Hf|(Hf&Hnf)].
                   - do 2 esplit; eauto using FEnv.union3'. reflexivity.
                   - apply FEnv.restrict_find_inv in Hf as (Hin&Hf).
                     destruct x11; [apply vars_of_senv_Var in Hin|apply vars_of_senv_Last, Hnl2' in Hin as []].
                     simpl_fenv.
                     do 2 esplit; try reflexivity; simpl.
                     apply FEnv.union2; auto.
                     erewrite FEnv.restrict_find; eauto with datatypes. reflexivity.
                     + clear - Hin. do 4 right. inv Hin. solve_In.
                     + erewrite FEnv.union2; eauto. reflexivity.
                       apply FEnv.of_list_None. intros Him. simpl in *.
                       take (_ \/ _ \/ _) and destruct it as [He|[He|[He|[He|He]]]]; inv He.
                       all:take (_ = Some _) and apply FEnv.find_In in it; eauto.
                 }

                 assert (sc_vars (senv_of_decls l0) Hi'' bs'') as Hsc1'.
                 { subst. intros. eapply sc_vars_refines; simpl. 1,4:eauto.
                   - intros * Hinm _. take (dom Hi' _) and now apply FEnv.union_In, or_intror, it.
                   - intros * Hl. clear - Hl H37. inv Hl. simpl_In. simpl_Forall. subst. simpl in *. congruence. }

                 assert (sc_vars (Γ' ++ senv_of_decls l0) (restrict (fselect_hist e k stres1 Hi) Γ' + Hi') bs'') as Hsc2.
                 { eapply local_hist_sc_vars with (Γ:=Γ'); subst; eauto using List.incl_refl, restrict_dom_ub.
                   - intros * Hinm Hin. take (forall x, InMembers x _ -> ~_) and eapply it; eauto.
                     eapply IsVar_incl_fst, IsVar_fst; eauto.
                   - eapply sc_vars_restrict, sc_vars_refines, sc_vars_fselect; eauto; try reflexivity.
                     + simpl_Forall. simpl_In. take (forall x ck, HasClock Γ' _ _ -> _) and edestruct it as (?&Hck); eauto with senv.
                       rewrite Hck. constructor.
                     + now rewrite Hac1.
                 }

                 assert (forall x, In x [x1; x3; x5; x7] -> ~InMembers x l0) as Hdisj.
                 { intros * Hin1 Hin2. apply InMembers_In in Hin2; destruct_conjs. simpl_Forall.
                   repeat (take (CA.fresh_ident _ = _) and eapply fresh_ident_prefixed in it as (?&?&?); subst).
                   destruct Hin1 as [|[|[|[|]]]]; eauto; subst; eapply contradict_AtomOrGensym; eauto using auto_not_in_last_prefs.
                 }

                 assert (sc_vars (Γ' ++ senv_of_decls l0) Hi'' bs'') as Hsc2'.
                 { subst. intros. eapply sc_vars_refines; simpl. 1,4:eauto.
                   - intros * Hinm Hin.
                     assert (~In x11 [x1;x3;x5;x7]) as Hnin.
                     { intros contra. apply IsVar_app in Hinm as [Hinm|Hinm].
                       - destruct contra as [|[|[|[|]]]]; subst; eauto.
                       - eapply Hdisj, IsVar_senv_of_decls; eauto.
                     }
                     unfold restrict. rewrite FEnv.union_In, FEnv.restrict_In, vars_of_senv_Var. setoid_rewrite FEnv.map_in_iff.
                     apply FEnv.union_In in Hin as [Hin|]; auto. setoid_rewrite FEnv.map_in_iff in Hin.
                     rewrite FEnv.restrict_In in Hin. setoid_rewrite FEnv.map_in_iff in Hin.
                     rewrite FEnv.union_In, FEnv.of_list_In in Hin.
                     destruct Hin as ([|Hin2]&Hin).
                     + destruct Hin as [In|[In|[In|[In|In]]]]; try inv In; auto.
                       1-4:exfalso; eauto with datatypes.
                       left; split; auto. clear - In. econstructor. solve_In.
                     + exfalso. rewrite fst_InMembers in Hin2; simpl in Hin2.
                       destruct Hin2 as [In|[In|[In|[In|In]]]]; try inv In; eauto with datatypes.
                   - intros * L. exfalso. apply IsLast_app in L as [L|L]; [eapply Hnl2'; eauto|].
                     clear - L H37. inv L. simpl_In. simpl_Forall. subst. simpl in *. congruence.
                 }

                 eapply Sscope with (Hi':=Hi'); eauto.
                 * subst. eauto.
                 *{ auto_block_simpl_Forall.
                    eapply sem_block_refines, H
                      with (Γck:=Γ'++_) (Γty:=Γty++_) (Hi:=(FEnv.restrict _ _)); eauto.
                    9:{ eapply sem_block_restrict; eauto.
                        unfold wc_env. simpl_Forall; simpl_In.
                        apply in_app_iff in Hin as [Hin|Hin]; simpl_In; simpl_Forall; eauto.
                        edestruct H17 as (_&Hbase); eauto with senv. rewrite Hbase; constructor.
                    } all:simpl.
                    - etransitivity; eauto. eapply FEnv.restrict_refines; eauto using EqStrel_Reflexive.
                    - intros * Hv. inv Hv. take (InMembers _ _) and apply InMembers_app in it as [Hin|Hin]; apply InMembers_In in Hin as (?&?).
                      + apply Hat; eauto with senv.
                      + simpl_In. simpl_Forall; auto.
                    - apply NoLast_app; auto.
                    - apply NoLast_app; auto.
                    - intros * Hv. rewrite IsVar_app in *. destruct Hv as [Hv|]; auto.
                    - now rewrite map_app, map_fst_senv_of_decls.
                    - eapply dom_ub_incl', restrict_dom_ub.
                      + intros *; rewrite 2 IsVar_app; intros [|]; eauto.
                      + intros *; rewrite 2 IsLast_app; intros [|]; eauto.
                        exfalso; eapply Hnl2'; eauto.
                    - eapply sc_vars_restrict; eauto.
                      + reflexivity.
                      + simpl_Forall; simpl_In.
                        apply in_app_iff in Hin as [Hin|Hin]; simpl_In; simpl_Forall; eauto.
                        edestruct H17 as (_&Hbase); eauto with senv. rewrite Hbase; constructor.
                  }
           }

      - (* local *)
        repeat inv_scope.
        do 2 econstructor; eauto.
        auto_block_simpl_Forall.
        assert (forall x, ~ IsLast (senv_of_decls locs) x) as Hnl'.
        { intros * Hlast. inv Hlast. simpl_In; simpl_Forall. subst; simpl in *; congruence. }
        eapply H with (Γty:=Γty++senv_of_decls locs) (Γck:=Γck++senv_of_decls locs); eauto.
        + intros * Hv. apply IsVar_app in Hv as [Hv|Hv]; auto.
          inv Hv. simpl_In. simpl_Forall; auto.
        + apply NoLast_app; auto.
        + apply NoLast_app; auto.
        + intros * Hv. apply IsVar_app. apply IsVar_app in Hv as [Hv|Hv]; auto.
        + rewrite map_app, map_fst_senv_of_decls; auto.
        + eapply local_hist_dom_ub; eauto.
        + eapply local_hist_sc_vars with (Γ:=Γty); eauto using IsVar_incl_fst.
          intros *. rewrite IsVar_fst; eauto.
    Qed.

    Lemma auto_node_sem : forall f n ins outs,
        wt_global (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        wc_global (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        Ordered_nodes (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(types) G2.(externs) ((fst (auto_node n))::G2.(nodes))) ->
        sem_node_ck (Global G1.(types) G1.(externs) (n::G1.(nodes))) f ins outs ->
        sem_node_ck (Global G2.(types) G2.(externs) ((fst (auto_node n))::G2.(nodes))) f ins outs.
    Proof with eauto.
      intros * (_&Hwt) Hwc Hord1 Hord2 Hsem.

      inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
      - erewrite find_node_now in Hfind; eauto. inv Hfind.
        (*The semantics of equations can be given according to G only *)
        assert (~Is_node_in_block (n_name n0) (n_block n0)) as Blk.
        { inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }
        eapply sem_block_ck_cons1 in Blk; eauto. clear H3.

        pose proof (n_syn n0) as Hsyn. inversion_clear Hsyn as [?? Syn1 Syn2 _].
        pose proof (n_nodup n0) as (Hnd1&Hnd2).
        pose proof (n_good n0) as (Hgood1&Hgood2&_).
        inv Hwc. take (_ /\ _) and destruct it as (Hwc&_); simpl in Hwc.
        inv Hwt. take (_ /\ _) and destruct it as (Hwt&_); simpl in Hwt.
        destruct H4 as (Hdom1&Hsc1).
        econstructor; eauto.
        + erewrite find_node_now; eauto.
        + eauto.
        + eauto.
        + eapply sem_block_ck_cons2; eauto.
          2:{ eapply find_node_not_Is_node_in in Hord2. 2:erewrite find_node_now; eauto. auto. }
          simpl. replace (Global (types G1) (externs G1) (nodes G1)) with G1 in Blk by (destruct G1; auto).
          eapply auto_block_sem in Blk; eauto using dom_dom_ub, node_NoDupLocals.
          7:rewrite surjective_pairing with (p:=auto_block _ _), surjective_pairing with (p:=fst _); reflexivity.
          * destruct G2; eauto.
          * intros * Hv. inv Hv. rewrite fst_InMembers, map_app, map_fst_senv_of_ins, map_fst_senv_of_decls in H0.
            now simpl_Forall.
          * apply NoLast_app; split; auto using senv_of_ins_NoLast.
            intros ? L; inv L; simpl_In. simpl_Forall. subst; simpl in *; congruence.
          * apply NoLast_app; split; auto using senv_of_ins_NoLast.
            intros ? L; inv L; simpl_In. simpl_Forall. subst; simpl in *; congruence.
          * inv Hwt; subst Γ; destruct G1; auto.
          * inv Hwc; destruct G1; auto.
        + constructor; auto.
      - erewrite find_node_other in Hfind; eauto.
        eapply sem_node_ck_cons2...
        destruct G2; apply Href.
        destruct G1; econstructor...
        eapply sem_block_ck_cons1; eauto using find_node_later_not_Is_node_in.
    Qed.

  End sem_node.

  Module Clocking := CAClockingFun Ids Op OpAux Cks Senv Syn Cl CA.

  Lemma auto_global_refines : forall G,
      wt_global G ->
      wc_global G ->
      global_sem_refines G (auto_global G).
  Proof with eauto using wc_global_Ordered_nodes.
    intros [] (Htypes&Hwt). unfold auto_global; simpl.
    generalize (types0 ++ flat_map snd (List.map auto_node nodes0)). revert types0 Htypes Hwt.
    induction nodes0; intros * Htypes Hwt * Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      eapply Clocking.auto_global_wc, wc_global_Ordered_nodes in Hwc'.
      assert (global_sem_refines {| types := types0; externs := externs0; nodes := nodes0|}
                                 {| types := l; externs := externs0; nodes := List.map fst (List.map auto_node nodes0) |}) as Hind.
      { inv Hwt. inv Hwc. eapply IHnodes0... }
      apply global_sem_ref_cons with (f:=n_name a)...
      + eapply Ordered_nodes_change_types; eauto.
      + intros ins outs Hsem; simpl in *.
        change l with ((Global l externs0 (List.map fst (List.map auto_node nodes0))).(types)).
        eapply auto_node_sem with (G1:=Global types0 externs0 nodes0)...
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
