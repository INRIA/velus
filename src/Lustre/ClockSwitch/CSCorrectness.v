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
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LCausality Lustre.LSemantics Lustre.LClockSemantics.
From Velus Require Import Lustre.ClockSwitch.ClockSwitch.
From Velus Require Import Lustre.ClockSwitch.CSClocking.

Module Type CSCORRECTNESS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS Ids Op OpAux)
       (Import CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX Ids Op OpAux Cks)
       (Import Ty    : LTYPING Ids Op OpAux Cks Syn)
       (Import Cl    : LCLOCKING Ids Op OpAux Cks Syn)
       (LCA          : LCAUSALITY Ids Op OpAux Cks Syn)
       (Import Ord   : LORDERED Ids Op OpAux Cks Syn)
       (Sem          : LSEMANTICS Ids Op OpAux Cks Syn Ord CStr)
       (Import LCS   : LCLOCKSEMANTICS Ids Op OpAux Cks Syn Ty Cl LCA Ord CStr Sem)
       (Import CS    : CLOCKSWITCH Ids Op OpAux Cks Syn).

  Module Clocking := CSClockingFun Ids Op OpAux Cks Syn Cl CS.
  Module Import CIStr := CoindIndexedFun Ids Op OpAux Cks CStr IStr.

  Section subclock.
    Context {PSyn1 PSyn2 : block -> Prop} {prefs1 prefs2 : PS.t}.
    Variable G1 : @global PSyn1 prefs1.
    Variable G2 : @global PSyn2 prefs2.

    Hypothesis HGref : global_sem_refines G1 G2.

    Variable bck : clock.
    Variable sub : Env.t ident.
    Variable bs bs' : Stream bool.
    Variable H H' : history.

    Hypothesis Hbck : sem_clock H' bs' bck bs.

    Corollary add_whens_const_sem : forall c ty,
        sem_exp_ck G2 H' bs' (add_whens (Econst c) ty bck) [const bs c].
    Proof.
      revert bs bs' H' Hbck.
      induction bck as [|??? (?&?)]; intros * Hbck *; simpl.
      - inv Hbck. rewrite H1. constructor; auto.
        reflexivity.
      - assert (Hbck':=Hbck). inv Hbck'; simpl.
        1,2,3:(eapply Swhen; eauto; simpl;
               repeat constructor; try eapply IHc; eauto;
               repeat constructor; eauto using sem_clock_when_const).
    Qed.

    Corollary add_whens_enum_sem : forall ty k,
        sem_exp_ck G2 H' bs' (add_whens (Eenum k ty) ty bck) [enum bs k].
    Proof.
      revert bs bs' H' Hbck.
      induction bck as [|??? (?&?)]; intros * Hbck *; simpl.
      - inv Hbck. rewrite H1. constructor; auto.
        reflexivity.
      - assert (Hbck':=Hbck). inv Hbck'; simpl.
        1,2,3:(eapply Swhen; eauto; simpl;
               repeat constructor; try eapply IHc; eauto;
               repeat constructor; eauto using sem_clock_when_enum).
    Qed.

    Hypothesis Hsub : forall x y vs,
        Env.find x sub = Some y ->
        sem_var H x vs ->
        sem_var H' y vs.

    Hypothesis Hnsub : forall x vs,
        Env.find x sub = None ->
        sem_var H x vs ->
        sem_var H' x vs.

    Lemma rename_var_sem : forall x vs,
        sem_var H x vs ->
        sem_var H' (rename_var sub x) vs.
    Proof.
      unfold rename_var; intros * Hsem.
      destruct (Env.find _ _) eqn:Hfind; eauto.
    Qed.

    Lemma subclock_exp_sem : forall e vs,
        sem_exp_ck G1 H bs e vs ->
        sem_exp_ck G2 H' bs' (subclock_exp bck sub e) vs.
    Proof.
      induction e using exp_ind2; intros * Hsem; inv Hsem; simpl.
      - (* const *)
        rewrite H4. apply add_whens_const_sem.
      - (* enum *)
        rewrite H6. apply add_whens_enum_sem.
      - (* var *)
        constructor.
        eapply rename_var_sem; eauto.
      - (* unop *)
        econstructor; eauto.
        now rewrite subclock_exp_typeof.
      - (* binop *)
        econstructor; eauto.
        1,2:now rewrite subclock_exp_typeof.
      - (* fby *)
        econstructor; eauto.
        1,2:rewrite Forall2_map_1; eapply Forall2_impl_In; [|eauto]; intros.
        1,2:rewrite Forall_forall in *; eauto.
      - (* arrow *)
        econstructor; eauto.
        1,2:rewrite Forall2_map_1; eapply Forall2_impl_In; [|eauto]; intros.
        1,2:rewrite Forall_forall in *; eauto.
      - (* when *)
        econstructor; eauto using rename_var_sem.
        rewrite Forall2_map_1; eapply Forall2_impl_In; [|eauto]; intros.
        rewrite Forall_forall in *; eauto.
      - (* merge *)
        econstructor; eauto using rename_var_sem.
        rewrite <-Sem.Forall2Brs_map_1.
        eapply Sem.Forall2Brs_impl_In; [|eauto]; intros ?? Hex Hsem.
        eapply Exists_exists in Hex as (?&?&?).
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      - (* case (total) *)
        econstructor; eauto.
        rewrite <-Sem.Forall2Brs_map_1.
        eapply Sem.Forall2Brs_impl_In; [|eauto]; intros ?? Hex Hsem.
        eapply Exists_exists in Hex as (?&?&?).
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      - (* case (default) *)
        econstructor; eauto; simpl in *.
        + now rewrite subclock_exp_typeof.
        + rewrite <-Sem.Forall2Brs_map_1.
          eapply Sem.Forall2Brs_impl_In; [|eauto]; intros ?? Hex Hsem.
          eapply Exists_exists in Hex as (?&?&?).
          take (Forall _ es) and eapply Forall_forall in it; eauto.
          take (Forall _ (snd _)) and eapply Forall_forall in it; eauto.
        + rewrite Forall2_map_1; eapply Forall2_impl_In; [|eauto]; intros.
          rewrite Forall_forall in *; eauto.
      - (* app *)
        econstructor; eauto.
        1,2:rewrite Forall2_map_1; eapply Forall2_impl_In; [|eauto]; intros.
        1,2:rewrite Forall_forall in *; eauto.
        intros. eapply HGref; eauto.
    Qed.

    Lemma subclock_equation_sem : forall equ,
        sem_equation_ck G1 H bs equ ->
        sem_equation_ck G2 H' bs' (subclock_equation bck sub equ).
    Proof.
      intros * Hsem. inv Hsem.
      econstructor; rewrite Forall2_map_1.
      - eapply Forall2_impl_In; eauto using subclock_exp_sem.
      - eapply Forall2_impl_In; eauto using rename_var_sem.
    Qed.

  End subclock.

  Lemma subclock_clock_sem : forall bck sub Hi Hi' bs bs' ck bs1,
      (forall x y vs, Env.find x sub = Some y -> sem_var Hi x vs -> sem_var Hi' y vs) ->
      (forall x vs, Env.find x sub = None -> sem_var Hi x vs -> sem_var Hi' x vs) ->
      sem_clock Hi' bs' bck bs ->
      sem_clock Hi bs ck bs1 ->
      sem_clock Hi' bs' (subclock_clock bck sub ck) bs1.
  Proof.
    cofix CoFix; intros * Hsub Hnsub Hbck * Hsemck;
      destruct bs, bs'; inv Hsemck; simpl.
    - rewrite <-H0. assumption.
    - econstructor; eauto using rename_var_sem.
      eapply CoFix in H2; eauto using sc_step.
      + intros * Hfind Hv.
        eapply sem_var_step_inv in Hv as (?&?). eapply sem_var_step; eauto.
      + intros * Hfind Hv.
        eapply sem_var_step_inv in Hv as (?&?). eapply sem_var_step; eauto.
    - econstructor; eauto using rename_var_sem.
      eapply CoFix in H2; eauto using sc_step.
      + intros * Hfind Hv.
        eapply sem_var_step_inv in Hv as (?&?). eapply sem_var_step; eauto.
      + intros * Hfind Hv.
        eapply sem_var_step_inv in Hv as (?&?). eapply sem_var_step; eauto.
    - eapply Son_abs2; eauto using rename_var_sem.
      eapply CoFix in H3; eauto using sc_step.
      + intros * Hfind Hv.
        eapply sem_var_step_inv in Hv as (?&?). eapply sem_var_step; eauto.
      + intros * Hfind Hv.
        eapply sem_var_step_inv in Hv as (?&?). eapply sem_var_step; eauto.
  Qed.

  Import Fresh Facts Tactics List.

  Section switch_block.
    Variable G1 : @global (fun _ => True) elab_prefs.
    Variable G2 : @global noswitch_block switch_prefs.

    Hypothesis HwcG1 : wc_global G1.
    Hypothesis HGref : global_sem_refines G1 G2.

    Import Permutation.
    Import Fresh Facts Tactics List.

    Lemma cond_eq_sem envty : forall Hi bs e ty ck vs x xcs eqs' st st' aft,
        Forall (AtomOrGensym elab_prefs) envty ->
        st_valid_after st switch aft ->
        Env.dom_ub Hi (envty ++ st_ids st) ->
        sem_exp_ck G2 Hi bs e [vs] ->
        sem_clock Hi bs ck (abstract_clock vs) ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        exists Hi',
          Env.refines (@EqSt _) Hi Hi' /\
          sem_var Hi' x vs /\
          Forall (sem_equation_ck G2 Hi' bs) eqs' /\
          Env.dom Hi' (map fst (Env.elements Hi) ++ map fst xcs) /\
          Env.dom_ub Hi' (envty ++ st_ids st') /\
          sc_vars (idck xcs) Hi' bs.
    Proof.
      intros * Hat Hst Hdom Hsem Hsemck Hcond.
      destruct e; simpl in *; repeat (take ann and destruct it); repeat inv_bind.
      3:{ inv Hsem. exists Hi; repeat split; simpl; eauto with env.
          + rewrite app_nil_r. apply Env.dom_elements.
          + constructor. }
      1-10:(assert (Env.refines (@EqSt _) Hi (Env.add x vs Hi)) as Href;
            [eapply Env.refines_add; intros Henvin; try reflexivity;
             eapply Env.dom_ub_use, in_app_iff in Henvin as [Hin|Hin]; eauto;
             [eapply fresh_ident_prefixed in H as (?&?&?); subst;
              eapply Forall_forall in Hat; eauto; eapply contradict_AtomOrGensym in Hat; eauto using switch_not_in_elab_prefs
             |eapply fresh_ident_nIn; eauto]
            |]).
      1-10:(assert (sem_var (Env.add x vs Hi) x vs) as Hv;
            [econstructor; try reflexivity; apply Env.add_1; reflexivity|]).
      1-10:
        (exists (Env.add x vs Hi); repeat split; auto;
              [do 2 (econstructor; eauto);
               [econstructor; eauto using sem_exp_refines|
                simpl; constructor; auto]
              |rewrite <-Permutation_app_comm; simpl; apply Env.dom_add_cons, Env.dom_elements
              |erewrite <-fresh_ident_vars_perm, <-Permutation_middle; eauto using Env.dom_ub_add
              |constructor; auto; do 2 esplit; eauto using sem_clock_refines
        ]).
    Qed.

    Lemma sem_clock_Con_filter Hi bs' bs : forall ck xc tn e sc,
        wt_stream sc (Tenum tn) ->
        slower sc bs ->
        sem_var Hi xc sc ->
        sem_clock Hi bs' ck (abstract_clock sc) ->
        sem_clock Hi bs' (Con ck xc (Tenum tn, e)) (filterb e sc bs).
    Proof.
      intros * Hwt Hslow Hv Hck.
      rewrite sem_clock_equiv in *. rewrite sem_var_equiv in *.
      intros n. specialize (Hv n). specialize (Hck n).
      rewrite tr_Stream_nth in Hv.
      repeat rewrite tr_Stream_nth in *. rewrite ac_nth in Hck. rewrite filterb_nth.
      setoid_rewrite SForall_forall in Hwt. specialize (Hwt n).
      rewrite slower_nth in Hslow. specialize (Hslow n).
      destruct (sc # n) eqn:Hsc; simpl.
      - constructor; auto.
      - destruct (bs # n); [|specialize (Hslow eq_refl); congruence].
        destruct (_ ==b _) eqn:Heq.
        + rewrite equiv_decb_equiv in Heq; inv Heq.
          constructor; auto.
        + inv Hwt.
          eapply IStr.Son_abs2; [eauto|eauto|].
          intro contra; subst. rewrite equiv_decb_refl in Heq. congruence.
    Qed.

    Lemma when_filter : forall tn e vs sc,
        wt_stream sc (Tenum tn) ->
        abstract_clock vs ≡ abstract_clock sc ->
        when e vs sc (filterv e sc vs).
    Proof.
      intros * Hwt Hac.
      apply when_spec; intros n.
      setoid_rewrite SForall_forall in Hwt. specialize (Hwt n).
      eapply eqst_ntheq with (n:=n) in Hac. repeat rewrite ac_nth in Hac.
      rewrite filterv_nth.
      destruct (vs # n), (sc # n); try congruence; simpl; auto.
      right. inv Hwt.
      destruct (_ ==b _) eqn:Heq.
      - rewrite equiv_decb_equiv in Heq; inv Heq.
        eauto.
      - left. repeat esplit; eauto.
        intro contra; subst.
        rewrite equiv_decb_refl in Heq. congruence.
    Qed.

    Lemma when_free_sem Hi' bs' : forall x y ty ck cx tn e sc vs,
        sem_var Hi' cx sc ->
        wt_stream sc (Tenum tn) ->
        sem_var Hi' x vs ->
        abstract_clock vs ≡ abstract_clock sc ->
        sem_var Hi' y (filterv e sc vs) ->
        sem_block_ck G2 Hi' bs' (when_free x y ty ck cx (Tenum tn) e).
    Proof.
      intros * Hcx Hwt Hx Hac Hy.
      constructor. econstructor. repeat constructor.
      2:{ simpl. rewrite app_nil_r; repeat constructor. eauto. }
      econstructor; eauto. repeat constructor; eauto.
      simpl. repeat constructor.
      eapply when_filter; eauto.
    Qed.

    Lemma merge_filter {A} : forall c vs (brs : list (enumtag * A)) tn,
        wt_stream c (Tenum tn) ->
        abstract_clock vs ≡ abstract_clock c ->
        Permutation (map fst brs) (seq 0 (snd tn)) ->
        merge c (map (fun '(k, _) => (k, filterv k c vs)) brs) vs.
    Proof.
      intros * Hwt Hac Hperm.
      apply merge_spec. intros n.
      eapply SForall_forall in Hwt. instantiate (1:=n) in Hwt.
      eapply eqst_ntheq with (n:=n) in Hac. repeat rewrite ac_nth in Hac.
      destruct (c # n) eqn:Hc, (vs # n) eqn:Hvs; simpl in *; try congruence; [left|right].
      - repeat split; auto.
        apply Forall_map, Forall_forall; intros (?&?) ?; simpl.
        rewrite filterv_nth, Hc; simpl; auto.
      - inv Hwt. repeat esplit; eauto.
        + rewrite CommonList.Exists_map.
          assert (In v1 (map fst brs)) as Hin.
          { rewrite Hperm. apply in_seq; lia. }
          apply in_map_iff in Hin as ((?&?)&?&Hin); subst.
          eapply Exists_exists. do 2 esplit; eauto; simpl.
          split; auto. rewrite filterv_nth, Hc, equiv_decb_refl; auto.
        + rewrite Forall_map. apply Forall_forall; intros (?&?) ? Hneq.
          rewrite filterv_nth, Hc; simpl. destruct (_ ==b _) eqn:Heq; auto.
          rewrite equiv_decb_equiv in Heq. inv Heq; congruence.
    Qed.

    Lemma merge_defs_sem Hi Hi' bs' : forall sub x ty ck xc tn subs c vs,
        Permutation (map fst subs) (seq 0 (snd tn)) ->
        (forall x0 y vs, Env.find x0 sub = Some y -> sem_var Hi x0 vs -> sem_var Hi' y vs) ->
        (forall x0 vs, Env.find x0 sub = None -> sem_var Hi x0 vs -> sem_var Hi' x0 vs) ->
        sem_var Hi' xc c ->
        wt_stream c (Tenum tn) ->
        sem_var Hi x vs ->
        abstract_clock vs ≡ abstract_clock c ->
        Forall (fun '(k, sub) => sem_var Hi' (rename_var sub x) (filterv k c vs)) subs ->
        sem_block_ck G2 Hi' bs' (merge_defs sub x ty ck xc (Tenum tn) subs).
    Proof.
      intros * Hperm Hsub Hnsub Hxc Hwt Hx Hac Hx'.
      constructor. econstructor. repeat constructor.
      2:{ simpl; rewrite app_nil_r; repeat constructor.
          eapply rename_var_sem, Hx; eauto. }
      eapply Smerge with (vs0:=[List.map (fun '(k, _) => (k, filterv k c vs)) subs]); eauto.
      - clear Hperm.
        induction subs as [|(?&?)]; simpl; inv Hx'; repeat constructor.
        econstructor; eauto.
        1,2:repeat constructor; eauto.
      - repeat constructor. eapply merge_filter; eauto.
    Qed.

    Lemma new_idents_sem {A} envty frees defs bck tn xc : forall Hi Hi' bs' (branches : list (enumtag * A)) xs sc st st' aft,
        st_valid_after st switch aft ->
        Forall (AtomOrGensym elab_prefs) envty ->
        Env.dom_ub Hi' (envty ++ st_ids st) ->
        sem_var Hi' xc sc ->
        sem_clock Hi' bs' bck (abstract_clock sc) ->
        wt_stream sc (Tenum tn) ->
        Forall (fun '(x, _) => exists vs, sem_var Hi x vs /\ abstract_clock vs ≡ abstract_clock sc) (frees++defs) ->
        mmap
          (fun '(k, _) =>
             bind (new_idents bck xc (Tenum tn) k frees)
                  (fun nfrees =>
                     bind (new_idents bck xc (Tenum tn) k defs)
                          (fun ndefs => ret (k, Env.from_list (map (fun '(x, y2, _) => (x, y2)) (nfrees ++ ndefs)), nfrees, ndefs)))) branches st = (xs, st') ->
        exists Hi'',
          Env.refines (@EqSt _) Hi' Hi'' /\
          Env.dom Hi'' (map fst (Env.elements Hi') ++ map fst (flat_map (fun '(_, _, nfrees, ndefs) => (map (fun '(_, x, (ty, ck)) => (x, (ty, ck, xH))) (nfrees++ndefs))) xs)) /\
          Env.dom_ub Hi'' (envty ++ st_ids st') /\
          Forall (fun '(k, sub, _, _) => (forall x y vs, Env.find x sub = Some y -> sem_var Hi x vs -> sem_var Hi'' y (filterv k sc vs))) xs /\
          sc_vars (flat_map (fun '(_, _, nfrees, ndefs) => (map (fun '(_, x, (_, ck)) => (x, ck)) (nfrees++ndefs))) xs) Hi'' bs'.
    Proof.
      intros * Hst Hat Hdomub Hx Hck Hwt Hsc Hmmap.
      exists (Env.adds' (flat_map (fun '(k, _, nfrees, ndefs) =>
                                map (fun '(x, nx, _) => (nx, filterv k sc (or_default (Streams.const absent) (Env.find x Hi))))
                                    (nfrees++ndefs)) xs) Hi').
      assert (st_valid_after st' switch aft) as Hvalid'.
      { eapply mmap_st_valid; eauto.
        eapply Forall_forall; intros (?&?) ? (((?&?)&?)&?) ????; repeat inv_bind.
        do 2 (eapply new_idents_st_valid; [|eauto]; auto). }
      assert (Env.refines (EqSt (A:=svalue)) Hi' (Env.adds' (flat_map (fun '(k, _, nfrees, ndefs) => map (fun '(x, nx, _) => (nx, filterv k sc (or_default (Streams.const absent) (Env.find x Hi)))) (nfrees ++ ndefs)) xs) Hi')) as Href.
      { apply Env.refines_adds'; auto using EqStrel_Reflexive, EqStrel_Transitive.
        eapply new_idents_st_ids' in Hmmap.
        eapply Forall_forall; intros * Hin1 Hin2. eapply Env.dom_ub_use in Hin2; eauto.
        apply in_app_iff in Hin2 as [Hin2|Hin2].
        - eapply Forall_forall in Hat; eauto.
          eapply st_valid_after_AtomOrGensym_nIn in Hvalid'; eauto using switch_not_in_elab_prefs.
          eapply Hvalid'. rewrite Hmmap.
          erewrite flat_map_concat_map, concat_map, map_map in *. erewrite map_ext; eauto using in_or_app.
          intros (((?&?)&?)&?). erewrite 2 map_map, map_ext; eauto. intros ((?&?)&?&?); auto.
        - eapply st_valid_NoDup, NoDup_app_l in Hvalid'. rewrite Hmmap in Hvalid'.
          eapply NoDup_app_In in Hvalid'; eauto.
          eapply Hvalid'.
          erewrite flat_map_concat_map, concat_map, map_map in *. erewrite map_ext; eauto using in_or_app.
          intros (((?&?)&?)&?). erewrite 2 map_map, map_ext; eauto. intros ((?&?)&?&?); auto.
      }
      assert (NoDupMembers
                (flat_map
                   (fun '(k, _, nfrees, ndefs) =>
                      map (fun '(x2, nx, _) => (nx, filterv k sc (or_default (Streams.const absent) (Env.find x2 Hi))))
                          (nfrees ++ ndefs)) xs)) as Hnd'.
      { eapply st_valid_NoDup, NoDup_app_l in Hvalid'.
        erewrite new_idents_st_ids' in Hvalid'; eauto. apply NoDup_app_r in Hvalid'.
        erewrite fst_NoDupMembers.
        rewrite flat_map_concat_map, concat_map, map_map in *. erewrite map_ext; eauto.
        intros (((?&?)&?)&?). erewrite 2 map_map, map_ext; eauto. intros ((?&?)&?&?); auto.
      }

      repeat split; auto.
      - rewrite Permutation_app_comm.
        erewrite 2 flat_map_concat_map, concat_map, map_map, map_ext with (f:=fun _ => map _ _), <-map_map, <-concat_map.
        eapply Env.dom_adds', Env.dom_elements. intros (((?&?)&?)&?); auto.
        erewrite 2 map_map. apply map_ext. intros ((?&?)&?&?); auto.
      - erewrite new_idents_st_ids'; eauto. rewrite app_assoc.
        rewrite 2 flat_map_concat_map, concat_map, map_map.
        erewrite map_ext with (f:=fun x => map fst _), <-map_map, <-concat_map.
        eapply Env.adds'_dom_ub; eauto.
        intros (((?&?)&?)&?). erewrite 2 map_map, map_ext; eauto. intros ((?&?)&?&?); auto.
      - eapply mmap_values, Forall2_ignore1 in Hmmap.
        eapply Forall_impl_In; [|eauto]; intros (((?&?)&?)&?) Hin ((?&?)&?&?&?&?) ??? Hfind Hv; repeat inv_bind.
        inv Hv.
        econstructor. 2:rewrite H4; reflexivity.
        unfold Env.MapsTo in *.
        erewrite Env.In_find_adds'; auto.
        eapply in_flat_map; do 2 esplit; eauto; simpl.
        apply Env.from_list_find_In in Hfind. eapply in_map_iff in Hfind as (((?&?)&?&?)&Heq&Hfind); inv Heq.
        eapply in_map_iff; do 2 esplit; eauto. simpl.
        rewrite H3; simpl; auto.
      - eapply Forall_forall; intros (?&?) Hin.
        assert (Hin':=Hin). eapply in_flat_map in Hin' as ((((?&?)&?)&?)&?&Hin').
        eapply in_map_iff in Hin' as (((?&?)&?&?)&Heq&Hin'); inv Heq.
        eapply mmap_values, Forall2_ignore1, Forall_forall in Hmmap as ((?&?)&?&?&?&?); eauto; repeat inv_bind.
        assert (InMembers i0 (frees++defs)) as Hin2. 2:eapply InMembers_In in Hin2 as ((?&?)&Hin2).
        { erewrite fst_InMembers, map_app, <-2 new_idents_old; eauto.
          rewrite <-map_app. apply in_map_iff; do 2 esplit; eauto. auto. }
        assert (c = Con bck xc (Tenum tn, e)); subst.
        { apply in_app_iff in Hin' as [Hin'|Hin'];
            eapply Clocking.new_idents_In_inv_ck in Hin'; eauto. }
        eapply Forall_forall in Hsc; eauto; simpl in *. destruct Hsc as (vs&Hv&Hac).
        exists (filterv e sc vs). split; auto.
        + inv Hv. unfold Env.MapsTo in *. econstructor. 2:rewrite H5; reflexivity.
          eapply Env.In_find_adds'; auto.
          eapply in_flat_map; do 2 esplit; eauto; simpl.
          eapply in_map_iff; do 2 esplit; eauto. simpl.
          rewrite H4; simpl; auto.
        + eapply sem_clock_refines; eauto. rewrite ac_filter.
          apply sem_clock_Con_filter; eauto.
          rewrite Hac. apply ac_slower.
    Qed.

    Fact switch_blocks_sem' aft : forall bck sub envty envck Hi Hi' bs bs' blks blks' st st',
        Forall
          (fun blk => forall bck sub envty envck Hi Hi' bs bs' blk' st st',
               (forall x, Env.In x sub -> InMembers x envck) ->
               (forall x y vs, Env.find x sub = Some y -> sem_var Hi x vs -> sem_var Hi' y vs) ->
               (forall x vs, Env.find x sub = None -> sem_var Hi x vs -> sem_var Hi' x vs) ->
               st_valid_after st switch aft ->
               incl (map fst envck) (map fst envty) ->
               NoDupMembers envty ->
               NoDupMembers envck ->
               Forall (AtomOrGensym elab_prefs) (map fst envty) ->
               Env.dom_ub Hi (map fst envty) ->
               sc_vars (idck envck) Hi bs ->
               Env.dom_ub Hi' (map fst envty ++ st_ids st) ->
               sem_clock Hi' bs' bck bs ->
               NoDupLocals (map fst envty) blk ->
               GoodLocals elab_prefs blk ->
               wt_block G1 envty blk ->
               wc_block G1 (idck envck) blk ->
               sem_block_ck G1 Hi bs blk ->
               switch_block envck bck sub blk st = (blk', st') ->
               sem_block_ck G2 Hi' bs' blk') blks ->
        (forall x, Env.In x sub -> InMembers x envck) ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi x vs -> sem_var Hi' y vs) ->
        (forall x vs, Env.find x sub = None -> sem_var Hi x vs -> sem_var Hi' x vs) ->
        st_valid_after st switch aft ->
        incl (map fst envck) (map fst envty) ->
        NoDupMembers envty ->
        NoDupMembers envck ->
        Forall (AtomOrGensym elab_prefs) (map fst envty) ->
        Env.dom_ub Hi (map fst envty) ->
        sc_vars (idck envck) Hi bs ->
        Env.dom_ub Hi' (map fst envty ++ st_ids st) ->
        sem_clock Hi' bs' bck bs ->
        Forall (NoDupLocals (map fst envty)) blks ->
        Forall (GoodLocals elab_prefs) blks ->
        Forall (wt_block G1 envty) blks ->
        Forall (wc_block G1 (idck envck)) blks ->
        Forall (sem_block_ck G1 Hi bs) blks ->
        mmap (switch_block envck bck sub) blks st = (blks', st') ->
        Forall (sem_block_ck G2 Hi' bs') blks'.
    Proof.
      induction blks; intros * Hf Hsubin Hsub Hnsub Hvalid Hincl Hnd1 Hnd2 Hat Hdom1 Hsc Hdom2 Hbck Hnd3 Hgood Hwt Hwc Hsem Hmmap;
        inv Hf; inv Hnd3; inv Hgood; inv Hwt; inv Hwc; inv Hsem; repeat inv_bind; econstructor; eauto.
      eapply IHblks in H0; eauto using switch_block_st_valid.
      eapply Env.dom_ub_incl; eauto.
      apply incl_app; [solve_incl_app|apply incl_appr, incl_map].
      eapply st_follows_incl; eauto using switch_block_st_follows.
    Qed.

    Lemma switch_block_sem aft : forall blk bck sub envty envck Hi Hi' bs bs' blk' st st',
        (forall x, Env.In x sub -> InMembers x envck) ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi x vs -> sem_var Hi' y vs) ->
        (forall x vs, Env.find x sub = None -> sem_var Hi x vs -> sem_var Hi' x vs) ->
        st_valid_after st switch aft ->
        incl (map fst envck) (map fst envty) ->
        NoDupMembers envty ->
        NoDupMembers envck ->
        Forall (AtomOrGensym elab_prefs) (map fst envty) ->
        Env.dom_ub Hi (map fst envty) ->
        sc_vars (idck envck) Hi bs ->
        Env.dom_ub Hi' (map fst envty ++ st_ids st) ->
        sem_clock Hi' bs' bck bs ->
        NoDupLocals (map fst envty) blk ->
        GoodLocals elab_prefs blk ->
        wt_block G1 envty blk ->
        wc_block G1 (idck envck) blk ->
        sem_block_ck G1 Hi bs blk ->
        switch_block envck bck sub blk st = (blk', st') ->
        sem_block_ck G2 Hi' bs' blk'.
    Proof.
      induction blk using block_ind2;
        intros * Hsubin Hsub Hnsub Hvalid Hincl Hnd1 Hnd2 Hat Hdom Hsc Hdomub Hbck Hnd3 Hgood Hwt Hwc Hsem Hmmap;
        inv Hnd3; inv Hgood; inv Hwt; inv Hwc; inv Hsem; simpl in *; repeat inv_bind.
      - (* equation *)
        constructor; eauto using subclock_equation_sem.

      - (* reset *)
        econstructor; eauto using subclock_exp_sem.
        intros k. eapply switch_blocks_sem' with (Hi:=mask_hist k r Hi) in H0; eauto.
        + intros ??? Hfind Hv.
          eapply sem_var_mask_inv in Hv as (?&Hv&Heq). rewrite Heq.
          eapply sem_var_mask; eauto.
        + intros ?? Hfind Hv.
          eapply sem_var_mask_inv in Hv as (?&Hv&Heq). rewrite Heq.
          eapply sem_var_mask; eauto.
        + apply Env.dom_ub_map; auto.
        + apply sc_vars_mask; auto.
        + apply Env.dom_ub_map; auto.
        + eapply sem_clock_mask; eauto.

      - (* switch *)
        destruct (partition _ _) eqn:Hpart. apply partition_Partition in Hpart.
        repeat inv_bind. destruct x. repeat inv_bind.
        rename x into subs.

        assert (sem_clock Hi bs ck (abstract_clock sc)) as Hsemck.
        { eapply sc_exp in H16; eauto.
          rewrite H11 in H16; simpl in H16. now inv H16. }
        repeat rewrite subclock_exp_typeof, H5 in *; simpl in *.
        repeat rewrite subclock_exp_clockof, H11 in *; simpl in *.
        assert (sem_clock Hi' bs' (subclock_clock bck sub ck) (abstract_clock sc)) as Hsemck'.
        { eapply subclock_clock_sem; eauto. }

        assert (incl (l ++ filter (fun '(_, (_, ck')) => ck' ==b ck) l0) envck) as Hincl1.
        { apply Partition_Permutation in Hpart. rewrite Hpart.
          apply incl_app; [solve_incl_app|apply incl_appr, incl_filter', incl_refl]. }

        assert (NoDupMembers (l ++ filter (fun '(_, (_, ck')) => ck' ==b ck) l0)) as Hnd'.
        {  apply Partition_Permutation in Hpart. rewrite Hpart in Hnd2.
           apply NoDupMembers_app; eauto using NoDupMembers_app_l, NoDupMembers_app_r, nodupmembers_filter.
           intros ? Hinm1 Hinm2.
           eapply NoDupMembers_app_InMembers in Hnd2; eauto. eapply Hnd2, filter_InMembers'; eauto. }

        assert ( Forall (fun '(x, _) => exists vs : Stream svalue, sem_var Hi x vs /\ abstract_clock vs ≡ abstract_clock sc)
                        (filter (fun '(_, (_, ck')) => ck' ==b ck) l0 ++ l)) as Hsc'.
        { eapply Forall_forall; intros (?&?&?) Hin.
          rewrite Permutation_app_comm in Hincl1.
          eapply Forall_forall in Hsc; eauto. 2:eapply incl_map; eauto; eapply in_map_iff; eauto.
          simpl in *. destruct Hsc as (?&Hv&Hck).
          do 2 esplit; eauto.
          assert (c = ck); subst. 2:eapply sem_clock_det; eauto.
          apply in_app_iff in Hin as [Hin|Hin].
          - apply filter_In in Hin as (?&Hin'). rewrite equiv_decb_equiv in Hin'; inv Hin'; auto.
          - assert (Is_defined_in i0 (Bswitch ec branches)) as Hdef.
            { eapply vars_defined_Is_defined_in.
              eapply Partition_Forall1, Forall_forall in Hpart; eauto; simpl in *.
              apply PSF.mem_2; auto. }
            inv Hdef. rename H19 into Hex. do 2 (eapply Exists_exists in Hex as (?&?&Hex)).
            eapply Is_defined_in_wx_In in Hex; [|eapply wc_block_wx_block; repeat (eapply Forall_forall in H15; eauto)].
            eapply in_map_iff in Hex as ((?&?)&?&Henv); subst. eapply H14 in Henv as (Hin'&?); subst.
            eapply NoDupMembers_det in Hin'; eauto. apply NoDupMembers_idck; auto.
            eapply in_map_iff; do 2 esplit; eauto using in_or_app. reflexivity.
        }

        assert (Hcond:=H0). eapply cond_eq_sem in H0 as (Hi1&Href1&Hv1&Hsem1&Hdom1&Hdomub1&Hsc1); eauto using subclock_exp_sem.
        assert (Hni:=H3). eapply new_idents_sem with (bs'0:=bs') in H3 as (Hi2&Href2&Hdom2&Hdomub2&Hv2&Hsc2); eauto with fresh.
        2:eapply sem_clock_refines; eauto.
        2:take (wt_streams [_] [_]) and inv it; auto.

        assert (forall x, InMembers x (l ++ filter (fun '(_, (_, ck')) => ck' ==b ck) l0) ->
                     Forall (fun '(_, sub, _, _) => Env.In x sub) subs) as Hinsubs.
        { intros ? Hinm. eapply mmap_values, Forall2_ignore1 in Hni; eauto.
          eapply Forall_impl; [|eapply Hni]; intros (((?&?)&?)&?) ((?&?)&?&?&?&?); repeat inv_bind.
          apply Env.In_from_list, fst_InMembers.
          erewrite map_map, map_ext, map_app, 2 new_idents_old, <-map_app; eauto. 2:intros ((?&?)&(?&?)); auto.
          now rewrite <-fst_InMembers, Permutation_app_comm. }

        eapply Slocal with (H':=Hi2); eauto. 4:repeat rewrite Forall_app; repeat split.
        + intros ?? Hsemv Hnin. rewrite fst_InMembers, map_app, in_app_iff, not_or' in Hnin. destruct Hnin as (Hnin1&Hnin2).
          eapply Sem.sem_var_refines'. 3:eauto. 2:etransitivity; eauto.
          eapply Env.dom_use; eauto using Env.dom_elements.
          eapply Sem.sem_var_In, Env.dom_use in Hsemv; [|eauto]. apply in_app_iff in Hsemv as [Hsemv|]; try contradiction.
          eapply Env.dom_use in Hsemv; [|eauto using Env.dom_elements]; eapply Env.dom_use in Hsemv; [|eauto].
          apply in_app_iff in Hsemv as [|]; auto.
          exfalso. eapply Hnin1. erewrite map_map, map_ext; eauto. intros (?&?&?); auto.
        + clear - Hdom1 Hdom2. rewrite map_app.
          apply Env.dom_intro; intros. erewrite Env.dom_use; eauto.
          repeat rewrite in_app_iff. rewrite <-or_assoc. apply or_iff_compat_r.
          symmetry. erewrite map_map, map_ext with (g:=fst) (l:=l1). 2:intros (?&?&?); auto.
          erewrite <-in_app_iff, <-Env.dom_use; eauto. erewrite Env.dom_use; try reflexivity.
          apply Env.dom_elements.
        + rewrite idty_app, idck_app. apply Forall_app; split.
          * eapply sc_vars_refines; eauto.
            unfold idck, idty. repeat rewrite map_map. erewrite map_ext; eauto. intros (?&?&?); auto.
          * clear - Hsc2. unfold sc_vars in *.
            do 2 apply Forall_map. rewrite flat_map_concat_map in *. rewrite Forall_concat, Forall_map in Hsc2.
            eapply Forall_concat, Forall_map, Forall_impl; [|eauto]; intros (((?&?)&?)&?) Hf.
            rewrite Forall_map in Hf. eapply Forall_map, Forall_impl; [|eauto]; intros ((?&?)&(?&?)) ?; auto.
        + apply Forall_map, Forall_forall; intros (?&?&?) Hin.
          assert (Is_defined_in i0 (Bswitch ec branches)) as Hdef.
          { eapply vars_defined_Is_defined_in.
            eapply Partition_Forall1, Forall_forall in Hpart; eauto; simpl in *.
            apply PSF.mem_2; auto. }
          inv Hdef. rename H3 into Hex. do 2 (eapply Exists_exists in Hex as (?&?&Hex)).
          eapply Is_defined_in_wx_In in Hex; [|eapply wc_block_wx_block; repeat (eapply Forall_forall in H15; eauto)].
          eapply in_map_iff in Hex as ((?&?)&?&Henv); subst. eapply H14 in Henv as (Hin'&?); subst.
          eapply Forall_forall in Hsc; eauto; simpl in *. destruct Hsc as (?&Hv&Hck).
          eapply merge_defs_sem; eauto using Sem.sem_var_refines.
          * rewrite <-H7.
            replace (map fst (map _ subs)) with (map fst branches). reflexivity.
            clear - Hni. apply mmap_values in Hni.
            induction Hni as [|(?&?) (((?&?)&?)&?)]; simpl; auto.
            destruct H as (?&?&?); repeat inv_bind.
            f_equal; auto.
          * take (wt_streams [_] [_]) and inv it; auto.
          * eapply sem_clock_det in Hsemck; eauto.
          * rewrite Forall_map. eapply Forall_impl_In; [|eapply Hv2]; intros (((?&?)&?)&?) Hinxs Hsub'.
            eapply Hsub'; eauto.
            assert (Env.In i1 t0) as Henvin.
            { eapply Forall_forall in Hinsubs; eauto. 2:eapply InMembers_app; left; eauto using In_InMembers.
              simpl in *; auto. }
            inv Henvin. unfold rename_var, Env.MapsTo in *.
            rewrite H18 in *; auto.
        + eapply CS.mmap2_values' in H13. eapply mmap_values, Forall3_ignore3' with (zs:=x3) in Hni.
          2:{ eapply Forall3_length in H13 as (?&?); congruence. }
          2:eapply mmap_length in Hni; eauto.
          2:{ eapply mmap_st_valid, cond_eq_st_valid; eauto.
              eapply Forall_forall; intros (?&?) ? (((?&?)&?)&?) ????; repeat inv_bind.
              do 2 (eapply new_idents_st_valid; [|eauto]); eauto. }
          2:{ intros (?&?) (((?&?)&?)&?) ?????; repeat inv_bind.
              eapply mmap_st_valid; eauto.
              eapply Forall_forall; intros. eapply switch_block_st_valid; eauto. }
          2:{ intros (?&?) (((?&?)&?)&?) ????; repeat inv_bind.
              eapply mmap_st_follows; eauto.
              eapply Forall_forall; intros. eapply switch_block_st_follows; eauto. }
          eapply Forall3_Forall3 in Hni; eauto. clear H13.
          eapply Forall_concat, Forall_forall; intros ? Hin1.
          eapply Forall3_ignore12, Forall_forall in Hni as ((?&?)&?&Hin2&Hin3&(?&?&Hvalid'&Hfollows'&?)&?&?&?); eauto; repeat inv_bind.
          apply Forall_app; split.
          *{ repeat (take (Forall _ branches) and eapply Forall_forall in it; eauto).
             assert (Forall (wc_block G1 (idck (map (fun '(x, (ty, _)) => (x, (ty, Cbase))) (l ++ filter (fun '(_, (_, ck')) => ck' ==b ck) l0)))) l2) as Hwc'.
             { eapply Forall_impl; [|eapply it1]; intros.
               eapply wc_block_incl; eauto. intros (?&?) Hin.
               apply H14 in Hin as (Hin&?); subst.
               eapply in_map_iff in Hin as ((?&?&?)&Heq&Hin); inv Heq.
               apply Partition_Permutation in Hpart. rewrite Hpart in Hin.
               repeat (apply in_map_iff; do 2 esplit; eauto).
               2:apply in_app_iff in Hin as [|]; eauto using in_or_app. simpl; auto.
               apply in_or_app, or_intror, filter_In. split; auto.
               apply equiv_decb_refl. }

             eapply switch_blocks_sem' with (Hi:=Env.restrict (filter_hist e sc Hi) (map fst (l ++ filter (fun '(_, (_, ck')) => ck' ==b ck) l0)))
                                            (bs:=filterb e sc bs) in H0; eauto; clear it.
             - intros ? Hin. apply Env.In_from_list in Hin.
               rewrite fst_InMembers in Hin. rewrite fst_InMembers.
               erewrite map_map, map_ext, map_app, <-2 new_idents_old, <-map_app, Permutation_app_comm; eauto.
               erewrite map_map, map_ext in Hin; eauto. intros ((?&?)&(?&?)); auto. intros (?&?&?); auto.
             - intros ??? Hfind Hv. eapply Sem.sem_var_restrict_inv in Hv as (?&Hv).
               eapply Forall_forall in Hv2; eauto. simpl in *.
               eapply sem_var_filter_inv in Hv as (?&Hv&Heq).
               rewrite Heq; eauto.
             - intros ?? Hfind Hv. eapply Sem.sem_var_restrict_inv in Hv as (Hin&_). exfalso.
               apply Env.Props.P.F.not_find_in_iff in Hfind. apply Hfind, Env.In_from_list.
               rewrite fst_InMembers.
               erewrite map_app, <-2 new_idents_old, <-map_app, Permutation_app_comm in Hin; eauto.
               erewrite map_map, map_ext; eauto. intros ((?&?)&(?&?)); auto.
             - etransitivity; [|eauto].
               erewrite map_map, map_ext. apply incl_map; auto. intros (?&?&?); auto.
             - clear - Hnd'.
               erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; auto. intros (?&?&?); auto.
             - eapply Env.restrict_dom_ub', Env.dom_ub_map; eauto.
             - eapply Forall_forall. intros (?&?) Hin.
               do 2 (eapply in_map_iff in Hin as ((?&?&?)&Heq&Hin); inv Heq).
               eapply Forall_forall in Hsc'; [|rewrite Permutation_app_comm; eauto]. destruct Hsc' as (vs&Hv&Hck).
               exists (filterv e sc vs). split.
               + eapply Sem.sem_var_restrict, sem_var_filter; eauto.
                 apply in_map_iff. do 2 esplit; eauto. auto.
               + constructor. rewrite ac_filter, Hck.
                 apply filterb_both_slower; eauto using ac_slower, sc_slower, ac_aligned.
             - eapply Env.dom_ub_incl; eauto. apply incl_app; [solve_incl_app|apply incl_appr].
               apply incl_map, st_follows_incl; auto.
             - eapply sem_clock_Con_filter; eauto.
               + take (wt_streams [_] [_]) and inv it; auto.
               + eapply sc_slower; eauto using ac_aligned.
               + eapply Sem.sem_var_refines; eauto.
               + eapply sem_clock_refines; [|eauto]. etransitivity; eauto.
             - eapply Forall_impl_In; [|eapply it0]; intros.
               erewrite <-map_ext, <-map_map, <-map_fst_idck. eapply sem_block_restrict; eauto.
               2:eapply Forall_forall in Hwc'; eauto.
               2:intros (?&?&?); auto.
               eapply Forall_map, Forall_map, Forall_forall; intros (?&?&?) _; simpl; auto with clocks.
           }
          *{ rewrite Forall_map. eapply Forall_forall; intros ((?&?)&?&?) Hin4.
             assert (InMembers i0 (filter (fun '(_, (_, ck')) => ck' ==b ck) l0)) as Hin.
             { eapply new_idents_In_inv in Hin4 as (?&?); eauto.
               eapply In_InMembers; eauto. }
             apply InMembers_In in Hin as (?&Hin).
             eapply Forall_forall in Hsc'; eauto using in_or_app; simpl in *. destruct Hsc' as (?&Hv&Heq).
             eapply when_free_sem; eauto.
             - eapply Sem.sem_var_refines; eauto.
             - take (wt_streams [_] [_]) and inv it; auto.
             - eapply Sem.sem_var_refines; [|eapply rename_var_sem; eauto].
               etransitivity; eauto.
             - eapply Forall_forall in Hv2; eauto. simpl in Hv2.
               eapply Hv2; eauto.
               apply Env.find_In_from_list.
               + apply in_map_iff; do 2 esplit; eauto using in_or_app. auto.
               + erewrite fst_NoDupMembers, map_map, map_ext, map_app, 2 new_idents_old, <-map_app, <-fst_NoDupMembers. 2,3:eauto.
                 now rewrite Permutation_app_comm.
                 intros ((?&?)&(?&?)); auto.
           }
        + rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
          constructor. eapply sem_equation_refines; eauto.

      - (* local *)
        assert (forall x, InMembers x locs -> ~Env.In x Hi') as Hnin.
        { intros ? Hinm Hin.
          eapply Env.dom_ub_use, in_app_iff in Hin as [|]; eauto.
          - eapply H5; eauto.
          - eapply st_valid_after_AtomOrGensym_nIn; eauto using switch_not_in_elab_prefs.
            eapply fst_InMembers, Forall_forall in Hinm; eauto.
        }

        assert (forall x y vs,
                   Env.find x sub = Some y -> sem_var H' x vs ->
                   sem_var (Env.union (Env.restrict H' (map fst locs)) Hi') y vs) as Hsub'.
        { intros ??? Hfind Hv.
          destruct (InMembers_dec x0 locs ident_eq_dec).
          - exfalso. apply Env.find_In, Hsubin, fst_InMembers, Hincl in Hfind.
            eapply H5; eauto.
          - eapply Sem.sem_var_refines; [|eapply Hsub]; eauto. eauto using Env.union_refines4', EqStrel. }
        assert (forall x vs,
                   Env.find x sub = None -> sem_var H' x vs ->
                   sem_var (Env.union (Env.restrict H' (map fst locs)) Hi') x vs) as Hnsub'.
        {  intros ?? Hfind Hv.
           destruct (InMembers_dec x0 locs ident_eq_dec).
           - inv Hv. econstructor; eauto.
             eapply Env.union_find2. eapply Env.restrict_find; eauto.
             + now rewrite <-fst_InMembers.
             + apply Env.Props.P.F.not_find_in_iff; eauto.
           - eapply Sem.sem_var_refines; [|eapply Hnsub]; eauto using Env.union_refines4', EqStrel. }

        eapply Slocal with (H'0:=Env.union (Env.restrict H' (map fst locs)) Hi'); eauto.
        + intros ?? Hv1 Hnim.
          erewrite fst_InMembers, map_map, map_ext with (g:=fst) in Hnim. 2:intros (?&(?&?)&?); auto.
          inv Hv1. econstructor; eauto.
          apply Env.union_find4 in H8 as [Hfind|]; eauto.
          apply Env.restrict_find_inv in Hfind as (?&?). contradiction.
        + rewrite Permutation_app_comm. apply Env.union_dom; auto using Env.dom_elements.
          erewrite map_map. erewrite (map_ext (fun x => fst (let '(x, (ty, ck, cx)) := x in (_, _)))).
          apply Env.dom_lb_restrict_dom. 2:intros (?&(?&?)&?); auto.
          eapply Env.dom_lb_incl, Env.dom_dom_lb; eauto. solve_incl_app.
        + unfold sc_vars, idck, idty in *. repeat rewrite map_map in *.
          rewrite Forall_map in *.
          eapply Forall_impl_In; [|eauto]. intros (?&(?&?)&?) Hin (?&Hv&Hck); simpl in *.
          do 2 esplit.
          *{ inv Hv. econstructor; eauto.
             eapply Env.union_find2. eapply Env.restrict_find; eauto.
             - eapply in_map_iff. do 2 esplit; eauto. auto.
             - apply Env.Props.P.F.not_find_in_iff; eauto using In_InMembers.
           }
          *{ eapply subclock_clock_sem. 1,2,4:eauto.
             eapply sem_clock_refines; [|eauto]; eauto using Env.union_refines4', EqStrel.
           }
        + eapply switch_blocks_sem' with (envty:=envty++idty (idty locs)) (Hi:=H') in H0; eauto.
          * intros ? Hin. apply InMembers_app; auto.
          * rewrite 2 map_app, 3 map_fst_idty, Permutation_app_comm.
            eapply incl_app; [|solve_incl_app]. apply incl_appl; auto.
          * eapply NoDupMembers_app; eauto. now rewrite 2 NoDupMembers_idty.
            intros ? Hin1 Hin2. rewrite 2 InMembers_idty in Hin2. apply fst_InMembers in Hin1.
            eapply H5; eauto.
          * eapply NoDupMembers_app; eauto. now rewrite NoDupMembers_idty.
            intros ? Hinm1 Hinm2. rewrite InMembers_idty in Hinm1. rewrite fst_InMembers in Hinm2.
            eapply H5; eauto.
          * rewrite map_app, 2 map_fst_idty. apply Forall_app; auto.
          * rewrite map_app, 2 map_fst_idty. eapply local_hist_dom_ub; eauto.
          * rewrite idck_app. apply Forall_app; split; auto.
            eapply sc_vars_refines; [|eauto]; eauto using local_hist_dom_ub_refines.
          * rewrite map_app, 2 map_fst_idty, (Permutation_app_comm (map fst envty)), <-app_assoc.
            apply Env.union_dom_ub; auto using Env.restrict_dom_ub.
          * eapply sem_clock_refines; [|eauto]; eauto using Env.union_refines4', EqStrel.
          * now rewrite map_app, 2 map_fst_idty.
          * now rewrite Permutation_app_comm, idck_app.
    Qed.

  End switch_block.

  Lemma switch_node_sem G1 G2 : forall f n ins outs,
      global_sem_refines G1 G2 ->
      CommonTyping.wt_program wt_node {| enums := enums G1; nodes := n :: nodes G1 |} ->
      wc_global (Global G1.(enums) (n::G1.(nodes))) ->
      Ordered_nodes (Global G1.(enums) (n::G1.(nodes))) ->
      Ordered_nodes (Global G2.(enums) ((switch_node n)::G2.(nodes))) ->
      sem_node_ck (Global G1.(enums) (n::G1.(nodes))) f ins outs ->
      sem_node_ck (Global G2.(enums) ((switch_node n)::G2.(nodes))) f ins outs.
  Proof with eauto.
    intros * HGref Hwt Hwc Hord1 Hord2 Hsem.

    inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
    - erewrite find_node_now in Hfind; eauto. inv Hfind.
      (* The semantics of the block can be given according to G only *)
      eapply sem_block_ck_cons in H3; eauto. rename H3 into Hblksem.
      2:{ inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }

      replace {| enums := enums G1; nodes := nodes G1 |} with G1 in Hblksem by (destruct G1; auto).
      pose proof (n_nodup n0) as (Hnd1&Hnd2).
      pose proof (n_good n0) as (Hgood1&Hgood2&_).
      inv Hwc. destruct H4 as (Hwc&_); simpl in Hwc.
      destruct H5 as (Hdom1&Hsc1).
      inv Hwt. destruct H4 as (Hwt&_); simpl in Hwt.
      eapply switch_block_sem with (envty:=idty (idty (n_in n0 ++ n_out n0))) (st:=init_st) in Hblksem...
      15:eapply surjective_pairing.
      eapply Snode with (H0:=H); simpl... 1-18:repeat rewrite map_fst_idty in *; auto.
      + erewrite find_node_now...
      + eauto.
      + eauto.
      + apply sem_block_ck_cons'; simpl; auto.
        2:{ eapply find_node_not_Is_node_in in Hord2.
            2:erewrite find_node_now; eauto. eauto. }
        destruct (switch_block _ _ _ _ _) as (?&?) eqn:Hil. destruct G2; rewrite Hil...
      + simpl. constructor; simpl; auto.
      + intros ? Hin. apply Env.Props.P.F.empty_in_iff in Hin. inv Hin.
      + intros * Hfind. rewrite Env.gempty in Hfind. congruence.
      + eapply init_st_valid; eauto using switch_not_in_elab_prefs, PS_For_all_empty.
      + reflexivity.
      + now rewrite 2 NoDupMembers_idty.
      + now rewrite NoDupMembers_idty.
      + eapply Env.dom_ub_incl; eauto using Env.dom_dom_ub. solve_incl_app.
      + eapply Env.dom_ub_incl; eauto using Env.dom_dom_ub. solve_incl_app.
      + constructor. reflexivity.
      + destruct Hwt as (?&?&?&?), G1; auto.
      + destruct Hwc as (?&?&?), G1; auto.
    - erewrite find_node_other in Hfind...
      eapply sem_node_ck_cons'...
      destruct G2; apply HGref.
      econstructor...
      destruct G1; eapply sem_block_ck_cons...
      eapply find_node_later_not_Is_node_in in Hord1...
  Qed.

  Fact wc_global_Ordered_nodes {PSyn prefs} : forall (G: @global PSyn prefs),
      wc_global G ->
      Ordered_nodes G.
  Proof.
    intros G Hwt.
    apply wl_global_Ordered_nodes; auto using wc_global_wl_global.
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
        change enms with ((Global enms (map switch_node nds)).(enums)).
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
       (Syn   : LSYNTAX Ids Op OpAux Cks)
       (Ty    : LTYPING Ids Op OpAux Cks Syn)
       (Clo   : LCLOCKING Ids Op OpAux Cks Syn)
       (LCA   : LCAUSALITY Ids Op OpAux Cks Syn)
       (Lord  : LORDERED Ids Op OpAux Cks Syn)
       (Sem   : LSEMANTICS Ids Op OpAux Cks Syn Lord CStr)
       (LCS   : LCLOCKSEMANTICS Ids Op OpAux Cks Syn Ty Clo LCA Lord CStr Sem)
       (CS    : CLOCKSWITCH Ids Op OpAux Cks Syn)
       <: CSCORRECTNESS Ids Op OpAux Cks CStr Syn Ty Clo LCA Lord Sem LCS CS.
  Include CSCORRECTNESS Ids Op OpAux Cks CStr Syn Ty Clo LCA Lord Sem LCS CS.
End CSCorrectnessFun.
