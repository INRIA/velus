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
       (Import Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (Import LCS   : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Cl Ord CStr Sem)
       (Import CS    : CLOCKSWITCH Ids Op OpAux Cks Senv Syn).

  Module Import SCT := SCCorrectnessFun Ids Op OpAux Cks CStr Senv Syn Cl Ord Sem LCS SC. Import SC.

  Module Clocking := CSClockingFun Ids Op OpAux Cks Senv Syn Cl CS.
  Module Import CIStr := CoindIndexedFun Ids Op OpAux Cks CStr IStr.

  Import Fresh Facts Tactics List.
  Local Open Scope fresh_monad_scope.

  Section switch_block.
    Variable G1 : @global noauto auto_prefs.
    Variable G2 : @global noswitch switch_prefs.

    Hypothesis HwcG1 : wc_global G1.
    Hypothesis HGref : global_sem_refines G1 G2.

    Import Permutation.
    Import Fresh Facts Tactics List Notations.

    Lemma sem_clock_Con_when Hi bs' bs : forall ck xc tx tn e sc,
        wt_stream sc (Tenum tx tn) ->
        slower sc bs ->
        sem_var Hi xc sc ->
        sem_clock Hi bs' ck (abstract_clock sc) ->
        sem_clock Hi bs' (Con ck xc (Tenum tx tn, e)) (fwhenb e bs sc).
    Proof.
      intros * Hwt Hslow Hv Hck.
      rewrite sem_clock_equiv in *. rewrite sem_var_equiv in Hv.
      intros n. specialize (Hv n). specialize (Hck n).
      rewrite tr_Stream_nth in Hv.
      repeat rewrite tr_Stream_nth in *. rewrite ac_nth in Hck. rewrite fwhenb_nth.
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

    Lemma when_free_sem Hi' bs' : forall x y ty ck cx tx tn e sc vs,
        sem_var Hi' (Var cx) sc ->
        wt_stream sc (Tenum tx tn) ->
        sem_var Hi' (Var x) vs ->
        abstract_clock vs ≡ abstract_clock sc ->
        sem_var Hi' (Var y) (fwhenv e vs sc) ->
        sem_block_ck G2 Hi' bs' (when_free x y ty ck cx (Tenum tx tn) e).
    Proof.
      intros * Hcx Hwt Hx Hac Hy.
      constructor. econstructor. repeat constructor.
      2:{ simpl. rewrite app_nil_r; repeat constructor. eauto. }
      econstructor; eauto. repeat constructor; eauto.
      simpl. repeat constructor.
      eapply fwhenv_whenv; eauto using wt_stream_enum.
    Qed.

    Lemma when_freel_sem subl Hi' bs' : forall x y ty ck cx tx tn e sc vs,
        sem_var Hi' (Var cx) sc ->
        wt_stream sc (Tenum tx tn) ->
        (Env.find x subl = None -> sem_var Hi' (Last x) vs) ->
        (forall y, Env.find x subl = Some y -> sem_var Hi' (Var y) vs) ->
        abstract_clock vs ≡ abstract_clock sc ->
        sem_var Hi' (Var y) (fwhenv e vs sc) ->
        sem_block_ck G2 Hi' bs' (when_freel subl x y ty ck cx (Tenum tx tn) e).
    Proof.
      intros * Hcx Hwt Hx Hac Hy.
      constructor. econstructor. repeat constructor.
      2:{ simpl. rewrite app_nil_r; repeat constructor. eauto. }
      econstructor; eauto. repeat constructor; eauto.
      2:{ simpl. instantiate (1:=[_]). simpl. repeat constructor.
          eapply fwhenv_whenv; eauto using wt_stream_enum. }
      - unfold rename_last. cases_eqn Eq; econstructor; eauto.
    Qed.

    Lemma merge_when {A} : forall c vs (brs : list (enumtag * A)) tx tn,
        wt_stream c (Tenum tx tn) ->
        abstract_clock vs ≡ abstract_clock c ->
        Permutation (map fst brs) (seq 0 (length tn)) ->
        merge c (map (fun '(k, _) => (k, fwhenv k vs c)) brs) vs.
    Proof.
      intros * Hwt Hac Hperm.
      apply merge_spec. intros n.
      eapply SForall_forall in Hwt. instantiate (1:=n) in Hwt.
      eapply eqst_ntheq with (n:=n) in Hac. repeat rewrite ac_nth in Hac.
      destruct (c # n) eqn:Hc, (vs # n) eqn:Hvs; setoid_rewrite Hc in Hac; simpl in *; try congruence; [left|right].
      - repeat split; auto.
        apply Forall_map, Forall_forall; intros (?&?) ?; simpl.
        rewrite fwhenv_nth, Hc; simpl; auto.
      - inv Hwt. repeat esplit; eauto.
        + rewrite CommonList.Exists_map.
          assert (In v1 (map fst brs)) as Hin.
          { rewrite Hperm. apply in_seq; lia. }
          apply in_map_iff in Hin as ((?&?)&?&Hin); subst.
          eapply Exists_exists. do 2 esplit; eauto; simpl.
          split; auto. rewrite fwhenv_nth, Hc, equiv_decb_refl; auto.
        + rewrite Forall_map. apply Forall_forall; intros (?&?) ? Hneq.
          rewrite fwhenv_nth, Hc; simpl. destruct (_ ==b _) eqn:Heq; auto.
          rewrite equiv_decb_equiv in Heq. inv Heq; congruence.
    Qed.

    Lemma merge_defs_sem Hi Hi' bs' : forall sub x ty ck xc tx tn subs c vs,
        Permutation (map fst subs) (seq 0 (length tn)) ->
        (forall x0 y vs, Env.find x0 sub = Some y -> sem_var Hi (Var x0) vs -> sem_var Hi' (Var y) vs) ->
        (forall x0 vs, Env.find x0 sub = None -> sem_var Hi (Var x0) vs -> sem_var Hi' (Var x0) vs) ->
        sem_var Hi' (Var xc) c ->
        wt_stream c (Tenum tx tn) ->
        sem_var Hi (Var x) vs ->
        abstract_clock vs ≡ abstract_clock c ->
        Forall (fun '(k, sub) => sem_var Hi' (Var (rename_var sub x)) (fwhenv k vs c)) subs ->
        sem_block_ck G2 Hi' bs' (merge_defs sub x ty ck xc (Tenum tx tn) subs).
    Proof.
      intros * Hperm Hsub Hnsub Hxc Hwt Hx Hac Hx'.
      constructor. econstructor. repeat constructor.
      2:{ simpl; rewrite app_nil_r; repeat constructor.
          eapply rename_var_sem, Hx; eauto. }
      eapply Smerge with (vs:=[List.map (fun '(k, _) => (k, fwhenv k vs c)) subs]); eauto.
      - clear Hperm.
        induction subs as [|(?&?)]; simpl; inv Hx'; repeat constructor.
        econstructor; eauto.
        1,2:repeat constructor; eauto.
      - repeat constructor. eapply merge_when; eauto.
    Qed.

    Definition st_senv {pref} (st: fresh_st pref _) := senv_of_tyck (st_anns st).

    Lemma cond_eq_sem envty : forall Hi bs e ty ck vs x xcs eqs' st st',
        Forall (AtomOrGensym auto_prefs) (map fst envty) ->
        dom_ub Hi (envty ++ st_senv st) ->
        sem_exp_ck G2 Hi bs e [vs] ->
        sem_clock (var_history Hi) bs ck (abstract_clock vs) ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        exists Hi',
          sem_var (Hi + Hi') (Var x) vs
          /\ Forall (sem_equation_ck G2 (Hi + Hi') bs) eqs'
          /\ Hi ⊑ Hi + Hi'
          /\ (forall x, FEnv.In (Var x) Hi' <-> In x (map fst xcs))
          /\ (forall x, ~FEnv.In (Last x) Hi')
          /\ sc_vars (senv_of_tyck xcs) (Hi + Hi') bs.
    Proof.
      intros * Hat Hdom Hsem Hsemck Hcond.
      assert (sem_var (fun y => if y ==b Var x then Some vs else None) (Var x) vs) as Hv.
      { econstructor; [|reflexivity]. now rewrite equiv_decb_refl. }
      assert (forall ann st', fresh_ident None ann st = (x, st') ->
                         Hi ⊑ Hi + (fun y => if y ==b (Var x) then Some vs else None)) as Href.
      { intros * Hfresh ?? Hfind.
        do 2 esplit; [reflexivity|]. apply FEnv.union2; auto.
        cases_eqn Heq; auto. exfalso.
        rewrite equiv_decb_equiv in Heq; inv Heq.
        assert (FEnv.In (Var x) Hi) as Hin by (econstructor; eauto).
        eapply Hdom, IsVar_app in Hin as [Hin|Hin].
        - eapply fresh_ident_prefixed in Hfresh. apply IsVar_fst in Hin. simpl_Forall; subst.
          eapply contradict_AtomOrGensym; eauto using switch_not_in_auto_prefs.
        - inv Hin. simpl_In. eapply fresh_ident_nIn in Hfresh; eauto.
          eapply Hfresh. solve_In.
      }
      destruct e; simpl in *; repeat (take ann and destruct it); repeat inv_bind.
      3:{ inv Hsem. exists (FEnv.empty _); split; [|split; [constructor|split; [|split; [|split]]]].
          + take (sem_var _ _ _) and apply it.
          + unfold FEnv.union, FEnv.empty; reflexivity.
          + split; [intros [? Hemp]|intros []]; inv Hemp.
          + intros ? [? Hemp]; inv Hemp.
          + split; intros * Hck; inv Hck; inv H. }
      all:(exists (fun y => if y ==b Var x then Some vs else None)).
      all:split; [|split; [|split; [|split; [|split; [|split]]]]]; eauto using sem_var_union3'.
      all:match goal with
          | |- Forall _ [_] =>
              repeat constructor; econstructor;
              [constructor; auto; eapply sem_exp_refines; [|eauto]; eauto
              |simpl; repeat constructor; eauto using sem_var_union3']
          | |- forall x, FEnv.In (Var x) _ <-> _ =>
              intros; unfold FEnv.In; simpl; split;
              [intros (?&Hsome); cases_eqn Heq; inv Hsome; rewrite equiv_decb_equiv in Heq; inv Heq; auto
              |intros [|[]]; subst; rewrite equiv_decb_refl; eauto]
          | |- forall x, ~FEnv.In (Last x) _ => intros ? [? L]; cases_eqn Eq; rewrite equiv_decb_equiv in Eq; inv Eq
          | |- forall x ck xs, HasClock _ _ _ -> IsLast _ _ -> _ =>
              intros * _ IsLast; exfalso; eapply senv_of_tyck_NoLast; eauto
          | |- forall x ck xs, HasClock _ _ _ -> sem_var _ _ _ -> _ =>
              intros * Hck Hvar; inv Hck; take (In _ [_]) and apply In_singleton in it; inv it; simpl in *;
              take (sem_var (_ + _) _ _) and eapply sem_var_det in it; [|eapply sem_var_union3', Hv]; rewrite <-it;
              eauto using Sem.sem_clock_refines, var_history_refines
          end.
    Qed.

    Lemma new_idents_sem {A} Γty frees defs freesl bck tx tn xc :
      forall Hi1 Hi2 bs' (branches : list (enumtag * A)) xs sc st st',
        Forall (AtomOrGensym auto_prefs) (map fst Γty) ->
        dom_ub Hi2 (Γty ++ st_senv st) ->
        sem_var Hi2 (Var xc) sc ->
        sem_clock (var_history Hi2) bs' bck (abstract_clock sc) ->
        wt_stream sc (Tenum tx tn) ->
        Forall (fun '(x, _) => forall vs, sem_var Hi1 (Var x) vs -> abstract_clock vs ≡ abstract_clock sc) (frees++defs) ->
        Forall (fun '(x, _) => forall vs, sem_var Hi1 (Last x) vs -> abstract_clock vs ≡ abstract_clock sc) freesl ->
        mmap (fun '(k, _) =>
                       do nfrees <- new_idents bck xc (Tenum tx tn) k frees;
                       do ndefs <- new_idents bck xc (Tenum tx tn) k defs;
                       let sub' := Env.from_list (map (fun '(x, y, _) => (x, y)) (nfrees++ndefs)) in
                       do nfreesl <- new_idents bck xc (Tenum tx tn) k freesl;
                       let subl' := Env.from_list (map (fun '(x, y, _) => (x, y)) nfreesl) in
                       ret (k, sub', subl', nfrees, ndefs, nfreesl)
                    ) branches st = (xs, st') ->
        exists Hi',
          Hi2 ⊑ Hi2 + Hi'
          /\ (forall x, FEnv.In (Var x) Hi' <-> InMembers x (flat_map (fun '(_, _, nfrees, ndefs, nfreesl) => (map (fun '(_, x, (ty, ck)) => (x, (ty, ck, xH, @None ident))) (nfrees++ndefs++nfreesl))) xs))
          /\ (forall x, ~FEnv.In (Last x) Hi')
          /\ Forall (fun '(k, sub, _, _, _, _) => (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 (Var x) vs -> sem_var (Hi2 + Hi') (Var y) (fwhenv k vs sc))) xs
          /\ Forall (fun '(k, _, subl, _, _, _) => (forall x y vs, Env.find x subl = Some y -> sem_var Hi1 (Last x) vs -> sem_var (Hi2 + Hi') (Var y) (fwhenv k vs sc))) xs
          /\ sc_vars (flat_map (fun '(_, _, nfrees, ndefs, nfreesl) => (map (fun '(_, x, (ty, ck)) => (x, Build_annotation ty ck xH None)) (nfrees++ndefs++nfreesl))) xs) (Hi2 + Hi') bs'.
    Proof.
      intros * Hat Hdomub Hx Hsemck Hwt Hsc Hscl Hmmap.

      assert (NoDupMembers
                (flat_map
                   (fun '(k, _, _, nfrees, ndefs, nfreesl) =>
                      map
                        (fun '(x3, nx, _) => (Var nx, fwhenv k (or_default (Streams.const (present (Venum 0))) (Hi1 (Var x3))) sc))
                        (nfrees ++ ndefs) ++
                        map
                        (fun '(x3, nx, _) =>
                           (Var nx, fwhenv k (or_default (Streams.const (present (Venum 0))) (Hi1 (Last x3))) sc)) nfreesl) xs)
             ) as Hnd'.
      { specialize (st_valid_NoDup st') as Hvalid'.
        erewrite new_idents_st_ids' in Hvalid'; eauto.
        eapply NoDup_app_r, FinFun.Injective_map_NoDup with (f:=Var) in Hvalid'. 2:intros ?? Eq; now inv Eq.
        erewrite map_map, flat_map_concat_map, concat_map, map_map in Hvalid'.
        erewrite fst_NoDupMembers, flat_map_concat_map, concat_map, map_map. erewrite map_ext; eauto.
        intros; destruct_conjs. simpl_app.
        erewrite ? map_map, map_ext with (l:=l1), map_ext with (l:=l0), map_ext with (l:=l); eauto. all:intros ((?&?)&?&?); auto.
      }

      remember (FEnv.of_list
                  (flat_map (fun '(k, _, _, nfrees, ndefs, nfreesl) =>
                               map (fun '(x, nx, _) => (Var nx, fwhenv k (or_default (Streams.const (present (Venum 0))) (Hi1 (Var x))) sc)) (nfrees++ndefs)
                                 ++ map (fun '(x, nx, _) => (Var nx, fwhenv k (or_default (Streams.const (present (Venum 0))) (Hi1 (Last x))) sc)) nfreesl) xs)) as Hi'.
      exists Hi'.
      assert (Hi2 ⊑ Hi2 + Hi') as Href.
      { subst. intros ?? Hfind. do 2 esplit; try reflexivity. apply FEnv.union2; auto.
        apply FEnv.of_list_None; intros Hinm; apply fst_InMembers in Hinm.
        eapply new_idents_st_ids' in Hmmap.
        assert (FEnv.In x Hi2) as Hin2 by (econstructor; eauto).
        destruct x; apply Hdomub in Hin2; [apply IsVar_app in Hin2 as [Hin2|Hin2]|apply IsLast_app in Hin2 as [Hin2|Hin2]].
        - inv Hin2. simpl_In. simpl_Forall.
          eapply st_valid_AtomOrGensym_nIn; eauto using switch_not_in_auto_prefs.
          rewrite Hmmap. apply in_or_app, or_intror.
          apply in_app_iff in Hinf as [|]; solve_In.
          2,4:rewrite app_assoc, in_app_iff; eauto. 1,2:simpl; auto.
        - inv Hin2. simpl_In. specialize (st_valid_NoDup st') as Hvalid'. rewrite Hmmap in Hvalid'.
          eapply NoDup_app_In in Hvalid'; [|eapply in_map_iff; eauto].
          eapply Hvalid'.
          apply in_app_iff in Hinf as [|]; solve_In.
          2,4:rewrite app_assoc, in_app_iff; eauto. 1,2:simpl; auto.
        - simpl_In. apply in_app_iff in Hinf as [|]; simpl_In.
        - simpl_In. apply in_app_iff in Hinf as [|]; simpl_In.
      }
      split; [|split; [|split; [|split; [|repeat split]]]]; auto.
      - intros. subst.
        erewrite FEnv.of_list_In; split; intros In.
        + simpl_In. apply in_app_iff in Hinf as [|]; solve_In.
          2,4:rewrite app_assoc, in_app_iff; eauto. 1,2:auto.
        + simpl_In.
          rewrite app_assoc in Hin; rewrite in_app_iff in *. destruct Hin; solve_In.
          2:rewrite in_app_iff; left; solve_In. 3:rewrite in_app_iff; right; solve_In. 1,2:auto.
      - intros ? In; subst. apply FEnv.of_list_In in In. simpl_In.
        apply in_app_iff in Hinf as [|]; simpl_In.
      - eapply mmap_values, Forall2_ignore1 in Hmmap. simpl_Forall. repeat inv_bind.
        intros * Hfind Hv. inv Hv.
        econstructor. 2:rewrite H6; reflexivity.
        apply FEnv.union3', FEnv.of_list_In_find; auto.
        apply Env.from_list_find_In in Hfind. repeat (solve_In; simpl).
        apply in_app_iff. left. solve_In.
        rewrite H5; simpl; auto.
      - eapply mmap_values, Forall2_ignore1 in Hmmap. simpl_Forall. repeat inv_bind.
        intros * Hfind Hv. inv Hv.
        econstructor. 2:rewrite H6; reflexivity.
        apply FEnv.union3', FEnv.of_list_In_find; auto.
        apply Env.from_list_find_In in Hfind. repeat (solve_In; simpl).
        apply in_app_iff. right. solve_In.
        rewrite H5; simpl; auto.
      - intros * Hck Hv. inv Hck. simpl_In.
        eapply mmap_values, Forall2_ignore1 in Hmmap. simpl_Forall. repeat inv_bind.
        assert (c = Con bck xc (Tenum tx tn, e0)); subst.
        { rewrite ? in_app_iff in Hin0.
          destruct Hin0 as [Hin'|[Hin'|Hin']];
            eapply Clocking.new_idents_In_inv_ck in Hin'; eauto. }
        eapply sem_var_union' in Hv as [(Hnin&Hv)|Hv].
        1:{ exfalso.
            eapply Hnin, FEnv.of_list_In, fst_InMembers. simpl_In.
            rewrite app_assoc, in_app_iff in Hin0. destruct Hin0; solve_In.
               2,4:rewrite in_app_iff. 2:left; solve_In. 2:right; solve_In. 1,2:auto. }
        rewrite app_assoc in Hin0. apply in_app_iff in Hin0 as [Hin0|Hin0].
        + assert (InMembers i (frees++defs)) as Hin3. 2:eapply InMembers_In in Hin3 as (?&Hin3).
           { erewrite fst_InMembers, ? map_app, <- ? new_idents_old; eauto.
             rewrite <- ? map_app. apply in_map_iff; do 2 esplit; eauto. auto. }
           simpl_Forall.
           eapply sem_var_of_list in Hnd'.
           2:{ solve_In; simpl; solve_In.
               apply in_app_iff. left. solve_In. }
           eapply sem_var_det in Hnd'; [|eapply Hv].
           eapply Sem.sem_clock_refines; eauto using var_history_refines. rewrite Hnd', ac_fwhen.
           eapply sem_clock_Con_when; eauto. 2:now apply sem_var_history.
           destruct (Hi1 (Var i)) eqn:Hhi1; simpl.
          * erewrite Hsc; eauto using ac_slower. econstructor; eauto. reflexivity.
          * apply slower_nth. intros * Hac. rewrite ac_nth, const_nth in Hac; simpl in Hac.
            congruence.
        + assert (InMembers i freesl) as Hin3. 2:eapply InMembers_In in Hin3 as (?&Hin3).
          { erewrite fst_InMembers, ? map_app, <- ? new_idents_old; eauto.
            rewrite <- ? map_app. apply in_map_iff; do 2 esplit; eauto. auto. }
          simpl_Forall.
          eapply sem_var_of_list in Hnd'.
          2:{ solve_In; simpl; solve_In.
              apply in_app_iff. right. solve_In. }
          eapply sem_var_det in Hnd'; [|eapply Hv].
          eapply Sem.sem_clock_refines; eauto using var_history_refines. rewrite Hnd', ac_fwhen.
          eapply sem_clock_Con_when; eauto. 2:now apply sem_var_history.
          destruct (Hi1 (Last i)) eqn:Hhi1; simpl.
          * erewrite Hscl; eauto using ac_slower. econstructor; eauto. reflexivity.
          * apply slower_nth. intros * Hac. rewrite ac_nth, const_nth in Hac; simpl in Hac.
            congruence.
      - intros * Hck Hca. exfalso. inv Hca. simpl_In. congruence.
    Qed.

    Fact switch_blocks_sem' : forall bck sub subl ls Γty Γck Hi Hi' bs bs' blks blks' st st',
        Forall
          (fun blk => forall bck sub subl ls Γty Γck Hi Hi' bs bs' blk' st st',
               (forall x, Env.In x sub \/ Env.In x subl -> InMembers x Γck) ->
               (forall x, Env.In x sub \/ Env.In x subl -> ~In x ls) ->
               (forall x y, Env.find x sub = Some y \/ Env.find x subl = Some y -> exists (n : ident) (hint : option ident), y = gensym switch hint n) ->
               (forall x vs, Env.find x sub = None -> sem_var Hi (Var x) vs -> sem_var Hi' (Var x) vs) ->
               (forall x vs, Env.find x subl = None -> sem_var Hi (Last x) vs -> sem_var Hi' (Last x) vs) ->
               (forall x y vs, Env.find x sub = Some y -> sem_var Hi (Var x) vs -> sem_var Hi' (Var y) vs) ->
               (forall x y vs, Env.find x subl = Some y -> sem_var Hi (Last x) vs -> sem_var Hi' (Var y) vs) ->
               incl (map fst Γck) (map fst Γty) ->
               NoDupMembers Γty ->
               NoDupMembers Γck ->
               Forall (AtomOrGensym auto_prefs) (map fst Γty) ->
               dom_ub Hi Γty ->
               dom_lb Hi Γck ->
               sc_vars Γck Hi bs ->
               dom_ub Hi' (Γty ++ st_senv st) ->
               sem_clock (var_history Hi') bs' bck bs ->
               noauto_block blk ->
               LastsDefined blk ls ->
               NoDupLocals (map fst Γty) blk ->
               GoodLocals auto_prefs blk ->
               wt_block G1 Γty blk ->
               wc_block G1 Γck blk ->
               sem_block_ck G1 Hi bs blk ->
               switch_block Γck bck sub subl blk st = (blk', st') ->
               sem_block_ck G2 Hi' bs' blk') blks ->
        (forall x, Env.In x sub \/ Env.In x subl -> InMembers x Γck) ->
        (forall x, Env.In x sub \/ Env.In x subl -> ~In x (concat ls)) ->
        (forall x y, Env.find x sub = Some y \/ Env.find x subl = Some y -> exists (n : ident) (hint : option ident), y = gensym switch hint n) ->
        (forall x vs, Env.find x sub = None -> sem_var Hi (Var x) vs -> sem_var Hi' (Var x) vs) ->
        (forall x vs, Env.find x subl = None -> sem_var Hi (Last x) vs -> sem_var Hi' (Last x) vs) ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi (Var x) vs -> sem_var Hi' (Var y) vs) ->
        (forall x y vs, Env.find x subl = Some y -> sem_var Hi (Last x) vs -> sem_var Hi' (Var y) vs) ->
        incl (map fst Γck) (map fst Γty) ->
        NoDupMembers Γty ->
        NoDupMembers Γck ->
        Forall (AtomOrGensym auto_prefs) (map fst Γty) ->
        dom_ub Hi Γty ->
        dom_lb Hi Γck ->
        sc_vars Γck Hi bs ->
        dom_ub Hi' (Γty ++ st_senv st) ->
        sem_clock (var_history Hi') bs' bck bs ->
        Forall noauto_block blks ->
        Forall2 LastsDefined blks ls ->
        Forall (NoDupLocals (map fst Γty)) blks ->
        Forall (GoodLocals auto_prefs) blks ->
        Forall (wt_block G1 Γty) blks ->
        Forall (wc_block G1 Γck) blks ->
        Forall (sem_block_ck G1 Hi bs) blks ->
        mmap (switch_block Γck bck sub subl) blks st = (blks', st') ->
        Forall (sem_block_ck G2 Hi' bs') blks'.
    Proof.
      intros * Hf Hsubin Hnsubin Hsubat Hnsub Hnsubl Hsub Hsubl Hincl Hnd1 Hnd2 Hat Hdom1 Hdom2 Hsc Hdom3 Hbck Hnl3 LD Hnd3 Hgood Hwt Hwc Hsem Hmmap.
      eapply mmap_values_follows, Forall2_ignore1 in Hmmap;
        eauto using switch_block_st_follows.
      simpl_Forall. inv_VarsDefined.
      eapply Hf with (ls:=xs) (Γty:=Γty) in H2; eauto.
      - intros * SubIn In.
        eapply Hnsubin; eauto using in_concat'.
      - simpl_Forall; auto.
      - eapply dom_ub_incl; eauto.
        apply incl_app; [solve_incl_app|apply incl_appr, incl_map, st_follows_incl]; auto.
    Qed.

    Lemma switch_scope_sem {A} P_na P_ld P_nd P_good P_wt P_wc P_sem1 f_switch (P_sem2: _ -> _ -> Prop) :
      forall locs (blk: A) bck sub subl ls Γty Γck Hi Hi' bs bs' s' st st',
        (forall x, Env.In x sub \/ Env.In x subl -> InMembers x Γck) ->
        (forall x, Env.In x sub \/ Env.In x subl -> ~In x ls) ->
        (forall x y, Env.find x sub = Some y \/ Env.find x subl = Some y -> exists (n : ident) (hint : option ident), y = gensym switch hint n) ->
        (forall x vs, Env.find x sub = None -> sem_var Hi (Var x) vs -> sem_var Hi' (Var x) vs) ->
        (forall x vs, Env.find x subl = None -> sem_var Hi (Last x) vs -> sem_var Hi' (Last x) vs) ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi (Var x) vs -> sem_var Hi' (Var y) vs) ->
        (forall x y vs, Env.find x subl = Some y -> sem_var Hi (Last x) vs -> sem_var Hi' (Var y) vs) ->
        incl (map fst Γck) (map fst Γty) ->
        NoDupMembers Γty ->
        NoDupMembers Γck ->
        Forall (AtomOrGensym auto_prefs) (map fst Γty) ->
        dom_ub Hi Γty ->
        dom_lb Hi Γck ->
        sc_vars Γck Hi bs ->
        dom_ub Hi' (Γty ++ st_senv st) ->
        sem_clock (var_history Hi') bs' bck bs ->
        noauto_scope P_na (Scope locs blk) ->
        LastsDefinedScope P_ld (Scope locs blk) ls ->
        NoDupScope P_nd (map fst Γty) (Scope locs blk) ->
        GoodLocalsScope P_good auto_prefs (Scope locs blk) ->
        wt_scope P_wt G1 Γty (Scope locs blk) ->
        wc_scope P_wc G1 Γck (Scope locs blk) ->
        sem_scope_ck P_sem1 Hi bs (Scope locs blk) ->
        switch_scope f_switch Γck bck sub (Scope locs blk) st = (s', st') ->
        (forall ls Γty Γck Hi Hi' blk' st st',
            (forall x, Env.In x sub \/ Env.In x subl -> InMembers x Γck) ->
            (forall x, Env.In x sub \/ Env.In x subl -> ~In x ls) ->
            (forall x y, Env.find x sub = Some y -> exists (n : ident) (hint : option ident), y = gensym switch hint n) ->
            (forall x vs, Env.find x sub = None -> sem_var Hi (Var x) vs -> sem_var Hi' (Var x) vs) ->
            (forall x vs, Env.find x subl = None -> sem_var Hi (Last x) vs -> sem_var Hi' (Last x) vs) ->
            (forall x y vs, Env.find x sub = Some y -> sem_var Hi (Var x) vs -> sem_var Hi' (Var y) vs) ->
            (forall x y vs, Env.find x subl = Some y -> sem_var Hi (Last x) vs -> sem_var Hi' (Var y) vs) ->
            incl (map fst Γck) (map fst Γty) ->
            NoDupMembers Γty ->
            NoDupMembers Γck ->
            Forall (AtomOrGensym auto_prefs) (map fst Γty) ->
            dom_ub Hi Γty ->
            dom_lb Hi Γck ->
            sc_vars Γck Hi bs ->
            dom_ub Hi' (Γty ++ st_senv st) ->
            sem_clock (var_history Hi') bs' bck bs ->
            P_na blk ->
            P_ld blk ls ->
            P_nd (map fst Γty) blk ->
            P_good blk ->
            P_wt Γty blk ->
            P_wc Γck blk ->
            P_sem1 Hi blk ->
            f_switch Γck blk st = (blk', st') ->
            P_sem2 Hi' blk') ->
        sem_scope_ck P_sem2 Hi' bs' s'.
    Proof.
      intros * Hsubin Hnsubin Hsubat Hnsub Hnsubl Hsub Hsubl Hincl Hnd1 Hnd2 Hat Hdomub Hdomlb Hsc Hdomub1 Hbck Hnl3 LD Hnd3 Hgood Hwt Hwc Hsem Hmmap Hind;
        inv Hnl3; inv LD; inv Hnd3; inv Hgood; inv Hwt; inv Hwc; inv Hsem; simpl in *; repeat inv_bind. subst Γ' Γ'0.
      assert (forall x, InMembers x locs -> ~FEnv.In (Var x) Hi') as Hnin.
      { intros ? Hinm Hin.
        eapply Hdomub1, IsVar_app in Hin as [Hin|Hin]; eauto.
        - apply IsVar_fst in Hin. take (forall x, InMembers x locs -> ~_) and eapply it; eauto.
        - apply IsVar_fst in Hin. simpl_In.
          eapply st_valid_AtomOrGensym_nIn; eauto using switch_not_in_auto_prefs.
          2:solve_In. simpl_Forall; eauto.
      }
      assert (forall x, InMembers x locs -> ~FEnv.In (Last x) Hi') as Hninl.
      { intros ? Hinm Hin.
        eapply Hdomub1, IsLast_IsVar, IsVar_app in Hin as [Hin|Hin]; eauto.
        - apply IsVar_fst in Hin. take (forall x, InMembers x locs -> ~In _ _) and eapply it; eauto.
        - apply IsVar_fst in Hin. simpl_In.
          eapply st_valid_AtomOrGensym_nIn; eauto using switch_not_in_auto_prefs.
          2:solve_In. simpl_Forall; eauto.
      }

      assert (Hi' ⊑ Hi' + Hi'0) as Href.
      { intros ?? Hfind.
        do 2 esplit; [reflexivity|]. apply FEnv.union2; auto.
        apply FEnv.not_find_In. intros contra. destruct x0; take (dom Hi'0 _) and eapply it in contra.
        + apply IsVar_senv_of_decls in contra. eapply Hnin; eauto. econstructor; eauto.
        + apply IsLast_senv_of_decls in contra. eapply Hninl; eauto. econstructor; eauto.
      }

      assert (forall x vs,
                 Env.find x sub = None -> sem_var (Hi + Hi'0) (Var x) vs -> sem_var (Hi' + Hi'0) (Var x) vs) as Hnsub'.
      { intros ?? Hfind Hv.
        apply sem_var_union' in Hv as [(Hnin'&Hv)|Hv]; eauto using sem_var_union2, sem_var_union3'. }
      assert (forall x vs,
                 Env.find x subl = None -> sem_var (Hi + Hi'0) (Last x) vs -> sem_var (Hi' + Hi'0) (Last x) vs) as Hnsubl'.
      { intros ?? Hfind Hv.
        apply sem_var_union' in Hv as [(Hnin'&Hv)|Hv]; eauto using sem_var_union2, sem_var_union3'. }

      assert (forall x y vs,
                 Env.find x sub = Some y -> sem_var (Hi + Hi'0) (Var x) vs -> sem_var (Hi' + Hi'0) (Var y) vs) as Hsub'.
      { intros ??? Hfind Hv.
        apply sem_var_union in Hv as [Hv|Hv].
        - eapply sem_var_union2; eauto.
          intros contra. take (dom Hi'0 _) and apply it, IsVar_senv_of_decls in contra. simpl_In. simpl_Forall.
          eapply or_introl, Hsubat in Hfind; destruct_conjs; subst.
          eapply contradict_AtomOrGensym; eauto using switch_not_in_auto_prefs.
        - exfalso.
          take (dom Hi'0 _) and apply Sem.sem_var_In, it, IsVar_senv_of_decls in Hv.
          take (forall x, InMembers x locs -> ~In _ _) and eapply it; eauto.
          apply Hincl, fst_InMembers, Hsubin. left. econstructor; eauto.
      }
      assert (forall x y vs,
                 Env.find x subl = Some y -> sem_var (Hi + Hi'0) (Last x) vs -> sem_var (Hi' + Hi'0) (Var y) vs) as Hsubl'.
      { intros ??? Hfind Hv.
        apply sem_var_union in Hv as [Hv|Hv].
        - eapply sem_var_union2; eauto.
          intros contra. take (dom Hi'0 _) and apply it, IsVar_senv_of_decls in contra. simpl_In. simpl_Forall.
          eapply or_intror, Hsubat in Hfind; destruct_conjs; subst.
          eapply contradict_AtomOrGensym; eauto using switch_not_in_auto_prefs.
        - exfalso.
          take (dom Hi'0 _) and apply Sem.sem_var_In, it, IsLast_senv_of_decls in Hv.
          take (forall x, InMembers x locs -> ~In _ _) and eapply it; eauto.
          apply Hincl, fst_InMembers, Hsubin. right. econstructor; eauto.
      }

      eapply Sscope with (Hi':=Hi'0); eauto.
      - take (dom Hi'0 _) and destruct it as (D1&D2). split; intros ?; [rewrite D1|rewrite D2].
        1,2:clear - x0; split; intros In; inv In; simpl_In; econstructor; solve_In; simpl; auto.
      - split; intros * Hck.
        + intros Hv.
          inv Hck; simpl_In. take (sc_vars (senv_of_decls locs) _ _) and destruct it as (Hsc1&_); simpl in *.
          apply sem_var_union' in Hv as [(Hnin'&Hv)|Hv].
          1:{ exfalso. take (dom Hi'0 _) and eapply Hnin', it, IsVar_senv_of_decls; eauto using In_InMembers. }
          eapply sem_var_union3', Hsc1 in Hv. 2:econstructor; solve_In; reflexivity. simpl in *.
          eapply subclock_clock_sem with (Hi:=var_history (Hi + _)); eauto using sem_clock_refines, var_history_refines.
          1,2:intros *; rewrite 2 sem_var_history; eauto using sem_var_refines.
        + intros L Hv.
          inv Hck; inv L; simpl_In. eapply NoDupMembers_det in Hin1; eauto; inv Hin1.
          take (sc_vars (senv_of_decls locs) _ _) and destruct it as (_&Hsc1); simpl in *.
          apply sem_var_union' in Hv as [(Hnin'&Hv)|Hv].
          1:{ exfalso. take (dom Hi'0 _) and eapply Hnin', it. econstructor; solve_In. auto. }
          eapply sem_var_union3', Hsc1 in Hv. 2,3:econstructor; solve_In; eauto; reflexivity. simpl in *.
          eapply subclock_clock_sem with (Hi:=var_history (Hi + _)); eauto using sem_clock_refines, var_history_refines.
          1,2:intros *; rewrite 2 sem_var_history; eauto using sem_var_refines.
      - eapply Hind with (ls:=ls ++ lasts_of_decls locs) (Γty:=Γty++_) (Γck:=Γck++_) in H; eauto.
        + intros ? Hin. apply InMembers_app; auto.
        + intros * In1 In2. apply in_app_iff in In2 as [In2|In2].
          * eapply Hnsubin; eauto.
          * eapply Hsubin in In1.
            unfold lasts_of_decls in *.
            eapply H6, Hincl, fst_InMembers; eauto. solve_In.
        + rewrite 2 map_app; eauto using incl_appl'.
        + eapply NoDupMembers_app; eauto. rewrite NoDupMembers_senv_of_decls; auto.
          intros ? Hin1 Hin2. rewrite InMembers_senv_of_decls in Hin2.
          take (forall x, InMembers _ _ -> ~In _ _) and eapply it; eauto. apply fst_InMembers; auto.
        + eapply NoDupMembers_app; eauto. rewrite NoDupMembers_senv_of_decls; auto.
          intros ? Hinm1 Hinm2. rewrite InMembers_senv_of_decls in Hinm2.
          take (forall x, InMembers _ _ -> ~In _ _) and eapply it; eauto. apply Hincl, fst_InMembers; auto.
        + rewrite map_app, map_fst_senv_of_decls. apply Forall_app; auto.
        + eapply local_hist_dom_ub; eauto.
        + eapply local_hist_dom_lb; eauto.
        + eapply local_hist_sc_vars; eauto. intros ?. rewrite IsVar_fst; eauto.
        + unfold dom_ub. rewrite <-app_assoc. setoid_rewrite (Permutation_app_comm (senv_of_decls _)). rewrite app_assoc.
          eapply local_hist_dom_ub; eauto.
        + eauto using sem_clock_refines, var_history_refines.
        + now rewrite map_app, map_fst_senv_of_decls.
    Qed.

    Ltac inv_branch :=
      match goal with
      | _ => (Syn.inv_branch || Ty.inv_branch || Cl.inv_branch || Sem.inv_branch || LCS.inv_branch)
      end.

    Lemma change_last : forall Γ Hi Hi',
        (forall x, ~IsLast Γ x) ->
        dom_ub Hi Γ ->
        (forall x vs, sem_var Hi (Last x) vs -> sem_var Hi' (Last x) vs).
    Proof.
      intros * NoLast Dom * V.
      apply sem_var_In, Dom, NoLast in V as [].
    Qed.

    Lemma switch_block_sem : forall blk bck sub subl ls Γty Γck Hi Hi' bs bs' blk' st st',
        (forall x, Env.In x sub \/ Env.In x subl -> InMembers x Γck) ->
        (forall x, Env.In x sub \/ Env.In x subl -> ~In x ls) ->
        (forall x y, Env.find x sub = Some y \/ Env.find x subl = Some y -> exists (n : ident) (hint : option ident), y = gensym switch hint n) ->
        (forall x vs, Env.find x sub = None -> sem_var Hi (Var x) vs -> sem_var Hi' (Var x) vs) ->
        (forall x vs, Env.find x subl = None -> sem_var Hi (Last x) vs -> sem_var Hi' (Last x) vs) ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi (Var x) vs -> sem_var Hi' (Var y) vs) ->
        (forall x y vs, Env.find x subl = Some y -> sem_var Hi (Last x) vs -> sem_var Hi' (Var y) vs) ->
        incl (map fst Γck) (map fst Γty) ->
        NoDupMembers Γty ->
        NoDupMembers Γck ->
        Forall (AtomOrGensym auto_prefs) (map fst Γty) ->
        dom_ub Hi Γty ->
        dom_lb Hi Γck ->
        sc_vars Γck Hi bs ->
        dom_ub Hi' (Γty ++ st_senv st) ->
        sem_clock (var_history Hi') bs' bck bs ->
        noauto_block blk ->
        LastsDefined blk ls ->
        NoDupLocals (map fst Γty) blk ->
        GoodLocals auto_prefs blk ->
        wt_block G1 Γty blk ->
        wc_block G1 Γck blk ->
        sem_block_ck G1 Hi bs blk ->
        switch_block Γck bck sub subl blk st = (blk', st') ->
        sem_block_ck G2 Hi' bs' blk'.
    Proof.
      Opaque switch_scope.
      induction blk using block_ind2;
        intros * Hsubin Hsubnin Hsubat Hnsub Hnsubl Hsub Hsubl Hincl Hnd1 Hnd2 Hat Hdomub Hdomlb Hsc Hdomub1 Hbck Hnl3 LD Hnd3 Hgood Hwt Hwc Hsem Hmmap;
        inv LD; inv Hnl3; inv Hnd3; inv Hgood; inv Hwt; inv Hwc; inv Hsem; simpl in *; repeat inv_bind.
      - (* equation *)
        constructor. eapply subclock_equation_sem with (H:=Hi); eauto.

      - (* last *)
        econstructor; eauto.
        + eapply subclock_exp_sem with (H:=Hi); eauto.
        + eapply Hnsub; eauto.
          apply Env.Props.P.F.not_find_in_iff. intros contra. eapply Hsubnin; eauto.
        + eapply Hnsubl; eauto.
          apply Env.Props.P.F.not_find_in_iff. intros contra. eapply Hsubnin; eauto.

      - (* reset *)
        econstructor; eauto.
        1:{ eapply subclock_exp_sem with (H:=Hi); eauto using change_last, sem_var_refines. }
        intros k. eapply switch_blocks_sem' with (Γty:=Γty) (Hi:=mask_hist k r Hi) in H0; eauto.
        1-4:(intros * Hfind Hv;
             eapply sem_var_mask_inv in Hv as (?&Hv&Heq); rewrite Heq;
             eapply sem_var_mask; eauto).
        + apply dom_ub_map; auto.
        + apply dom_lb_map; auto.
        + eapply sc_vars_mask in Hsc; eauto.
        + apply dom_ub_map; auto.
        + eapply sem_clock_mask; eauto.

      - (* switch *)
        destruct (partition _ _) eqn:Hpart. apply partition_Partition in Hpart.
        repeat inv_bind. destruct x. repeat inv_bind.
        rename x into subs.

        assert (sem_clock (var_history Hi) bs ck (abstract_clock sc)) as Hsemck.
        { take (sem_exp_ck _ _ _ _ _) and eapply sc_exp in it; eauto.
          rewrite H14 in it; simpl in *. now inv it. }
        repeat rewrite subclock_exp_typeof, H8 in *; simpl in *.
        repeat rewrite subclock_exp_clockof, H14 in *; simpl in *.
        assert (sem_clock (var_history Hi') bs' (subclock_clock bck sub ck) (abstract_clock sc)) as Hsemck'.
        { eapply subclock_clock_sem. 3,4:eauto. 1,2:intros *; rewrite 2 sem_var_history; eauto using sem_var_refines. }

        assert (incl (l ++ filter (fun '(_, ann) => ann.(clo) ==b ck) l0) Γck) as Hincl1.
        { apply Partition_Permutation in Hpart. rewrite Hpart.
          apply incl_app; [solve_incl_app|apply incl_appr, incl_filter', incl_refl]. }

        assert (NoDupMembers (l ++ filter (fun '(_, ann) => ann.(clo) ==b ck) l0)) as Hnd'.
        {  apply Partition_Permutation in Hpart. rewrite Hpart in Hnd2.
           apply NoDupMembers_app; eauto using NoDupMembers_app_l, NoDupMembers_app_r, NoDupMembers_filter.
           intros ? Hinm1 Hinm2.
           eapply NoDupMembers_app_InMembers in Hnd2; eauto. eapply Hnd2, filter_InMembers'; eauto. }

        assert ( Forall (fun '(x, _) => forall vs, sem_var Hi (Var x) vs -> abstract_clock vs ≡ abstract_clock sc)
                        (filter (fun '(_, ann) => ann.(clo) ==b ck) l0 ++ l)) as Hsc'.
        { eapply Forall_forall; intros (?&?) Hin * Hv.
          rewrite Permutation_app_comm in Hincl1.
          eapply Hsc in Hv. 2:apply Hincl1 in Hin; eauto with senv.
          assert (clo a = ck); subst. 2:eapply sem_clock_det; eauto.
          apply in_app_iff in Hin as [Hin|Hin].
          - apply filter_In in Hin as (?&Hin'). rewrite equiv_decb_equiv in Hin'; inv Hin'; auto.
          - assert (Is_defined_in (Var i0) (Bswitch ec branches)) as Hdef.
            { eapply vars_defined_Is_defined_in.
              eapply Partition_Forall1, Forall_forall in Hpart; eauto; simpl in *.
              apply PSF.mem_2; auto. }
            inv Hdef. simpl_Exists. simpl_Forall.
            repeat inv_branch. simpl_Exists. simpl_Forall.
            take (Syn.Is_defined_in _ _) and eapply wc_block_Is_defined_in in it; eauto.
            eapply InMembers_In in it as (?&Hin').
            take (forall x ck, HasClock _ _ _ -> _) and edestruct it as (Hck&_); eauto with senv.
            inv Hck. eapply NoDupMembers_det with (t:=a) in H1; eauto. congruence.
            eapply Hincl1; auto using in_or_app.
        }

        assert ( Forall (fun '(x, _) => forall vs, sem_var Hi (Last x) vs -> abstract_clock vs ≡ abstract_clock sc)
                        (filter (fun '(_, ann) => isSome (causl_last ann)) (filter (fun '(_, ann) => ann.(clo) ==b ck) l0 ++ l))) as Hscl'.
        { eapply Forall_forall; intros (?&?) Hin * Hv. simpl_In.
          rewrite Permutation_app_comm in Hincl1.
          eapply Hsc in Hv.
          2:{ apply Hincl1 in Hin0; eauto with senv. }
          2:{ apply Partition_Permutation in Hpart. rewrite Hpart. econstructor.
              rewrite in_app_iff in *. destruct Hin0; simpl_In; eauto.
              destruct a, causl_last0; simpl in *; congruence. }
          assert (clo a = ck); subst. 2:eapply sem_clock_det; eauto.
          apply in_app_iff in Hin0 as [Hin|Hin].
          - apply filter_In in Hin as (?&Hin'). rewrite equiv_decb_equiv in Hin'; inv Hin'; auto.
          - assert (Is_defined_in (Var i0) (Bswitch ec branches)) as Hdef.
            { eapply vars_defined_Is_defined_in.
              eapply Partition_Forall1, Forall_forall in Hpart; eauto; simpl in *.
              apply PSF.mem_2; auto. }
            inv Hdef. simpl_Exists. simpl_Forall.
            repeat inv_branch. simpl_Exists. simpl_Forall.
            take (Syn.Is_defined_in _ _) and eapply wc_block_Is_defined_in in it; eauto.
            eapply InMembers_In in it as (?&Hin').
            take (forall x ck, HasClock _ _ _ -> _) and edestruct it as (Hck&_); eauto with senv.
            inv Hck. eapply NoDupMembers_det with (t:=a) in H1; eauto. congruence.
            eapply Hincl1; auto using in_or_app.
        }

        assert (forall x, InMembers x (l ++ filter (fun '(_, ann) => ann.(clo) ==b ck) l0) ->
                     Forall (fun '(_, sub, _, _, _, _) => Env.In x sub) subs) as Hinsubs.
        { intros ? Hinm. eapply mmap_values, Forall2_ignore1 in H6; eauto.
          eapply Forall_impl; [|eapply H6]; intros (((?&?)&?)&?) ((?&?)&?&?&?&?); repeat inv_bind.
          apply Env.In_from_list, fst_InMembers.
          erewrite map_map, map_ext, map_app, ? new_idents_old, <-map_app; eauto. 2:intros ((?&?)&(?&?)); auto.
          now rewrite <-fst_InMembers, Permutation_app_comm. }

        assert (sem_exp_ck G2 Hi' bs' (subclock_exp bck sub subl ec) [sc]) as Hsem.
        { eapply subclock_exp_sem with (H:=Hi); eauto using change_last, sem_var_refines. }
        assert (Hcond:=H0). eapply cond_eq_sem in H0 as (Hi1&Hv1&Hsem1&Href1&Hdom1&Hdoml1&Hsc1); eauto.
        assert (dom_ub (Hi' + Hi1) (Γty ++ st_senv x1)) as Hdomub1'.
        { split; intros ? Hin; apply FEnv.union_In in Hin as [Hin|Hin]; try apply Hdomub1 in Hin.
          - eapply IsVar_incl; [|eauto].
            eapply incl_appr', incl_map, st_follows_incl; eauto using cond_eq_st_follows.
          - eapply Hdom1, cond_eq_incl in Hin; [|eauto]. apply IsVar_app, or_intror, IsVar_fst. unfold st_senv, senv_of_tyck. solve_In.
          - eapply IsLast_incl; [|eauto].
            eapply incl_appr', incl_map, st_follows_incl; eauto using cond_eq_st_follows.
          - eapply Hdoml1 in Hin as [].
        }
        assert (Hni:=H6). eapply new_idents_sem with (bs':=bs') in H6 as (Hi2&Href2&Hdom2&Hdoml2&Hv2&Hl2&Hsc2); eauto with fresh.
        2:{ eapply Sem.sem_clock_refines; eauto using var_history_refines. }
        2:take (wt_streams [_] [_]) and inv it; auto.

        constructor. eapply Sscope with (Hi':=Hi1 + Hi2); eauto. 3:rewrite ? Forall_app; repeat split. split.
        + intros. rewrite FEnv.union_In, Hdom1, Hdom2, IsVar_senv_of_decls, InMembers_app.
          apply or_iff_compat_r. erewrite fst_InMembers, map_map, map_ext. reflexivity.
          intros; destruct_conjs; auto.
        + intros. rewrite FEnv.union_In, senv_of_decls_app, IsLast_app.
          split; [intros [In|In]|intros [In|In]]. 3,4:clear - In; inv In; simpl_In; congruence.
          1,2:exfalso. eapply Hdoml1; eauto. eapply Hdoml2; eauto.
        + simpl_app. apply sc_vars_app.
          * intros * Hinm1 Hinm2. rewrite fst_InMembers in Hinm1, Hinm2.
            specialize (st_valid_NoDup x2) as Hvalid'.
            apply new_idents_st_ids' in Hni. apply cond_eq_st_ids in Hcond.
            rewrite Hni, Hcond in Hvalid'. simpl_app. simpl_In.
            eapply NoDup_app_r, NoDup_app_In in Hvalid'. 2:solve_In.
            eapply Hvalid'. solve_In. auto.
          * eapply sc_vars_refines.
            1:{ rewrite FEnv.union_assoc; eauto using EqStrel_Reflexive. }
            3:{ erewrite map_map, map_ext; eauto. intros (?&?&?); auto. }
            -- intros * Hin1 Hin2.
               erewrite IsVar_fst, 2 map_map, map_ext, <-fst_InMembers in Hin1.
               2:intros; destruct_conjs; auto.
               apply fst_InMembers, Hdom1 in Hin1.
               apply FEnv.union_In; auto.
            -- intros * L. clear - L. inv L. simpl_In. congruence.
          * clear - Hsc2. eapply sc_vars_morph. 4:eauto. 3:reflexivity.
            2:symmetry; apply FEnv.union_assoc; auto using EqStrel_Reflexive.
            erewrite 2 flat_map_concat_map, concat_map, map_map, map_ext; eauto.
            intros; destruct_conjs; auto. erewrite map_map, map_ext; eauto.
            intros; destruct_conjs; auto.
        + simpl_Forall.
          assert (Is_defined_in (Var i0) (Bswitch ec branches)) as Hdef.
          { eapply vars_defined_Is_defined_in.
            eapply Partition_Forall1, Forall_forall in Hpart; eauto; simpl in *.
            apply PSF.mem_2; auto. }
          assert (exists vs, sem_var Hi (Var i0) vs) as (vs&Hi0).
          { eapply sem_block_defined in Hdef; eauto.
            - inv Hdef. esplit; econstructor; eauto. reflexivity.
            - econstructor; eauto.  take (typeof ec = _) and now rewrite it. }
          inv Hdef. simpl_Exists. simpl_Forall. repeat inv_branch. simpl_Exists. simpl_Forall.
          take (Is_defined_in _ _) and eapply wc_block_Is_defined_in, InMembers_In in it as (?&Hin1); eauto.
          assert (HasClock Γ' i0 x5.(clo)) as Hck by eauto with senv.
          eapply H16 in Hck as (Hin'&?); subst. inv Hin'.
          eapply sem_block_ck_morph; [symmetry; eapply FEnv.union_assoc, EqStrel_Reflexive| | |]; simpl; try reflexivity.
          eapply merge_defs_sem with (Hi:=Hi); eauto using Sem.sem_var_refines.
          * rewrite <-H10.
            replace (map fst (map _ subs)) with (map fst branches). reflexivity.
            clear - Hni. apply mmap_values in Hni.
            induction Hni as [|(?&?) (((?&?)&?)&?)]; simpl; auto.
            destruct H as (?&?&?); repeat inv_bind.
            f_equal; auto.
          * take (wt_streams [_] [_]) and inv it; auto.
          * eapply sem_clock_det in Hsemck; eauto.
            destruct Hsc as (Hsc&_). eapply Hsc; eauto with senv.
          * simpl_Forall. eapply Hv2; eauto.
            assert (Env.In i0 t0) as Henvin.
            { eapply Forall_forall in Hinsubs; eauto. 2:eapply InMembers_app; left; eauto using In_InMembers.
              simpl in *; auto. }
            inv Henvin. unfold rename_var, Env.MapsTo in *.
            rewrite H24 in *; auto.
        + eapply CS.mmap2_values' in H20.
          assert (st_follows x1 x2) as Hfollows2.
          { eapply mmap_st_follows; eauto. simpl_Forall; destruct_conjs; repeat inv_bind.
            repeat (etransitivity; eauto using new_idents_st_follows). }
          assert (Hf:=Hni). eapply mmap_values, Forall3_ignore3' with (zs:=x3) in Hf.
          2:{ eapply Forall3_length in H20 as (?&?); congruence. }
          2:eapply mlength_map in Hni; eauto.
          2:{ intros; destruct_conjs. take (branch _) and destruct it. repeat inv_bind.
              eapply mmap_st_follows; eauto.
              simpl_Forall; eauto using switch_block_st_follows. }
          eapply Forall3_Forall3 in Hf; [|eapply H20]. clear H20.
          eapply Forall_concat, Forall_forall; intros ? Hin1.
          eapply Forall3_ignore12, Forall_forall in Hf as ((?&?)&?&Hin2&Hin3&(?&?&Hfollows&?)&?&?&?); eauto; repeat inv_bind.
          simpl_Forall. repeat inv_branch. repeat inv_bind.
          take (In _ (_ ++ _)) and rewrite ? in_app_iff in it. destruct it as [|[Hin|Hin]]; simpl_Forall.
          *{ eapply sem_block_ck_morph; [symmetry; eapply FEnv.union_assoc, EqStrel_Reflexive| | |]; simpl; try reflexivity.
             assert (Forall (wc_block G1 (map (fun '(x, ann0) => (x, ann_with_clock ann0 Cbase)) (l ++ filter (fun '(_, ann0) => clo ann0 ==b ck) l0))) blks) as Hwc'.
             { simpl_Forall.
               eapply wc_block_incl; [| |eauto].
               + intros * Hin. apply H16 in Hin as (Hin&?); subst.
                 inv Hin; econstructor; solve_In.
                 2:{ apply Partition_Permutation in Hpart. rewrite Hpart in H25.
                     rewrite in_app_iff in *. destruct H25; eauto; right; solve_In.
                     apply equiv_decb_refl. }
                 simpl; eauto. auto.
               + intros * Hin.
                 assert (HasClock Γck x16 ck) as Ck.
                 { inv Hin. edestruct H16; eauto with senv. } eapply H18 in Hin.
                 inv Hin. inv Ck. eapply NoDupMembers_det in H25; eauto; subst.
                 apply Partition_Permutation in Hpart. rewrite Hpart, in_app_iff in H30.
                 rewrite map_app, IsLast_app.
                 destruct H30 as [Hin|Hin]; [left|right]; econstructor; solve_In.
                 2:apply equiv_decb_refl.
                 1,2:destruct e0; simpl in *; auto.
             }
             eapply switch_blocks_sem'
               with (ls:=map (fun _ => []) blks) (Γty:=Γty) (bs:=fwhenb e bs sc)
                    (Hi:=restrict (fwhen_hist e Hi sc) (map (fun '(x, ann0) => (x, ann_with_clock ann0 Cbase)) (l ++ filter (fun '(_, ann) => ann.(clo) ==b ck) l0))) in H0.
             simpl_Forall; eauto. all:eauto.
             - intros ? Hin. rewrite ? Env.In_from_list, ? fst_InMembers in Hin. rewrite fst_InMembers.
               destruct Hin.
               + erewrite map_map, map_ext, map_app, <-2 new_idents_old, <-map_app, Permutation_app_comm; eauto.
                 solve_In. intros; destruct_conjs; auto.
               + simpl_In. eapply new_idents_In_inv in H21 as (?&In&_); eauto.
                 setoid_rewrite Permutation_app_comm. solve_In.
             - intros * _ In. apply in_concat in In as (?&?&In). simpl_In. inv In.
             - repeat (take (new_idents _ _ _ _ _ _ = _) and apply new_idents_prefixed in it).
               intros * [Hfind|Hfind]; apply Env.from_list_find_In in Hfind; simpl_In.
               + apply in_app_iff in Hin as [|]; simpl_Forall; eauto.
               + simpl_Forall. eauto.
             - intros ?? Hfind Hv. eapply Sem.sem_var_restrict_inv in Hv as (Hin&_). exfalso.
               apply Env.Props.P.F.not_find_in_iff in Hfind. apply Hfind, Env.In_from_list.
               rewrite fst_InMembers.
               erewrite vars_of_senv_Var, IsVar_fst, map_map, map_ext, map_app, <-2 new_idents_old, <-map_app, Permutation_app_comm in Hin; eauto.
               erewrite map_map, map_ext; eauto. 1,2:intros; destruct_conjs; auto.
             - intros ?? Hfind Hv. eapply Sem.sem_var_restrict_inv in Hv as (Hin&_). exfalso.
               apply Env.Props.P.F.not_find_in_iff in Hfind. apply Hfind, Env.In_from_list.
               rewrite fst_InMembers.
               erewrite vars_of_senv_Last in Hin. erewrite map_map, map_ext, new_idents_old; eauto.
               2:intros; destruct_conjs; auto.
               inv Hin. rewrite Permutation_app_comm. solve_In.
               destruct a; simpl in *. destruct causl_last0; simpl; auto; congruence.
             - intros ??? Hfind Hv. eapply Sem.sem_var_restrict_inv in Hv as (_&Hv).
               eapply sem_var_fwhen_inv in Hv as (?&Hv&Heq).
               rewrite Heq; eauto.
             - intros ??? Hfind Hv. eapply Sem.sem_var_restrict_inv in Hv as (_&Hv).
               eapply sem_var_fwhen_inv in Hv as (?&Hv&Heq).
               rewrite Heq; eauto.
             - etransitivity; [|eauto].
               erewrite map_map, map_ext. apply incl_map; eauto. intros (?&?); auto.
             - clear - Hnd'.
               erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; auto. intros (?&?); auto.
             - simpl_Forall; auto.
             - split; intros ? In; eapply dom_ub_map; eauto.
               1,2:eapply FEnv.restrict_In in In as (?&?); eauto.
             - split; intros ? In; apply FEnv.restrict_In;
                 (split; [apply FEnv.map_in_iff, Hdomlb|try apply vars_of_senv_Var; try apply vars_of_senv_Last]).
               1:eapply IsVar_incl; eauto. 3:eapply IsLast_incl; eauto.
               1,2:clear - In; inv In; econstructor; solve_In.
               1,2:clear - In; inv In; eapply in_map_iff in H as ((?&?)&?&?); inv_equalities; econstructor; eauto; solve_In.
             - split.
               + intros * Hck Hv.
                 inv Hck. simpl_In. eapply Forall_forall in Hsc'. 2:rewrite Permutation_app_comm; eauto. simpl in *.
                 apply Sem.sem_var_restrict_inv in Hv as (_&Hv). apply sem_var_fwhen_inv in Hv as (?&Hv&Hwhen).
                 constructor. rewrite Hwhen, ac_fwhen, Hsc'; eauto.
                 apply fwhenb_both_slower; eauto using ac_slower, sc_slower, ac_aligned.
               + intros * Hck Hl Hv.
                 inv Hck. inv Hl. simpl_In. eapply NoDupMembers_det in Hin0; eauto; subst.
                 eapply Forall_forall in Hscl'.
                 2:{ rewrite Permutation_app_comm. solve_In. simpl.
                     destruct causl_last; simpl; auto. } simpl in *.
                 apply Sem.sem_var_restrict_inv in Hv as (_&Hv). apply sem_var_fwhen_inv in Hv as (?&Hv&Hwhen).
                 constructor. rewrite Hwhen, ac_fwhen, Hscl'; eauto.
                 apply fwhenb_both_slower; eauto using ac_slower, sc_slower, ac_aligned.
             - split; intros ? Hin; apply FEnv.union_In in Hin as [Hin|Hin].
               + eapply Hdomub1' in Hin. eapply IsVar_incl; eauto.
                 eapply incl_appr', incl_map, st_follows_incl. etransitivity; eauto.
               + apply Hdom2 in Hin.
                 eapply IsVar_app, or_intror, IsVar_incl; [eapply incl_map, st_follows_incl; eauto|].
                 eapply new_idents_st_ids' in Hni. erewrite IsVar_fst, map_map, map_ext. setoid_rewrite Hni. 2:intros; destruct_conjs; auto.
                 apply in_app_iff, or_intror; auto.
                 apply fst_InMembers in Hin. clear - Hin. solve_In. auto.
               + eapply Hdomub1' in Hin. eapply IsLast_incl; eauto.
                 eapply incl_appr', incl_map, st_follows_incl. etransitivity; eauto.
               + exfalso. eapply Hdoml2; eauto.
             - eapply sem_clock_Con_when; eauto using Sem.sem_clock_refines, var_history_refines.
               + take (wt_streams [_] [_]) and inv it; auto.
               + eapply sc_slower; eauto using ac_aligned.
               + eapply sem_var_history, sem_var_refines; eauto.
             - simpl_Forall. auto.
             - simpl_Forall. eapply sem_block_restrict; eauto.
               + unfold wc_env. simpl_Forall. take (In _ (idck _)) and clear - it. simpl_In. constructor.
               + take (when_hist _ _ _ _) and apply when_hist_fwhen_hist in it; eauto using sem_block_refines.
           }
          *{ simpl_In. simpl_Forall.
             assert (InMembers i0 (filter (fun '(_, ann) => ann.(clo) ==b ck) l0)) as Hin.
             { eapply new_idents_In_inv in H6 as (?&?&?); eauto using In_InMembers. }
             apply InMembers_In in Hin as (?&Hin).
             assert (exists vs, sem_var Hi (Var i0) vs) as (vs&Hv).
             { assert (FEnv.In (Var i0) Hi) as (?&?). 2:do 2 econstructor; eauto; reflexivity.
               eapply Hdomlb, IsVar_incl, IsVar_app, or_intror; eauto.
               clear - Hin. econstructor. solve_In. }
             eapply Forall_forall in Hsc'; eauto using in_or_app; simpl in *.
             eapply sem_block_ck_morph; [symmetry; eapply FEnv.union_assoc, EqStrel_Reflexive| | |]; simpl; try reflexivity.
             eapply when_free_sem; eauto using Sem.sem_var_refines.
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
          *{ simpl_In.
             assert (InMembers i0  (filter (fun '(_, ann) => isSome (causl_last ann)) (filter (fun '(_, ann) => clo ann ==b ck) l0 ++ l))) as Hin.
             { eapply new_idents_In_inv in H21 as (?&?&?); eauto using In_InMembers. }
             apply InMembers_In in Hin as (?&Hin).
             assert (exists vs, sem_var Hi (Last i0) vs) as (vs&Hv).
             { assert (FEnv.In (Last i0) Hi) as (?&?). 2:do 2 econstructor; eauto; reflexivity.
               eapply Hdomlb, IsLast_incl; eauto. rewrite Permutation_app_comm.
               econstructor; simpl_In. eauto. edestruct causl_last; simpl in *; congruence. }
             eapply Forall_forall in Hscl'; eauto using in_or_app; simpl in *.
             eapply sem_block_ck_morph; [symmetry; eapply FEnv.union_assoc, EqStrel_Reflexive| | |]; simpl; try reflexivity.
             eapply when_freel_sem; eauto using Sem.sem_var_refines.
             - take (wt_streams [_] [_]) and inv it; auto.
             - eapply Hl2; eauto.
               apply Env.find_In_from_list.
               + apply in_map_iff; do 2 esplit; eauto using in_or_app. auto.
               + erewrite fst_NoDupMembers, map_map, map_ext, new_idents_old, <-fst_NoDupMembers. 2:eauto.
                 apply NoDupMembers_filter. now rewrite Permutation_app_comm.
                 intros ((?&?)&(?&?)); auto.
           }

        + simpl_Forall.
          constructor. eapply sem_equation_refines; eauto.
          rewrite FEnv.union_assoc; eauto using EqStrel_Reflexive.

      - (* local *)
        constructor.
        eapply switch_scope_sem with (Γty:=Γty); eauto.
        intros. simpl in *. inv_VarsDefined. eapply switch_blocks_sem' with (Γty:=Γty0); eauto.
        + intros * In1. rewrite Hperm; eauto.
        Transparent switch_scope.
    Qed.

  End switch_block.

  Lemma switch_node_sem G1 G2 : forall f n ins outs,
      global_sem_refines G1 G2 ->
      CommonTyping.wt_program wt_node {| types := G1.(types); externs := G1.(externs); nodes := n :: G1.(nodes) |} ->
      wc_global (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
      Ordered_nodes (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
      Ordered_nodes (Global G2.(types) G2.(externs) ((switch_node n)::G2.(nodes))) ->
      sem_node_ck (Global G1.(types) G1.(externs) (n::G1.(nodes))) f ins outs ->
      sem_node_ck (Global G2.(types) G2.(externs) ((switch_node n)::G2.(nodes))) f ins outs.
  Proof with eauto.
    intros * HGref Hwt Hwc Hord1 Hord2 Hsem.

    inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
    - erewrite find_node_now in Hfind; eauto. inv Hfind.
      (* The semantics of the block can be given according to G only *)
      assert (~Is_node_in_block (n_name n0) (n_block n0)) as Blk.
      { inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }
      eapply sem_block_ck_cons1 in Blk; eauto. clear H3.

      replace {| types := types G1; nodes := nodes G1 |} with G1 in Blk by (destruct G1; auto).
      pose proof (n_nodup n0) as (Hnd1&Hnd2).
      pose proof (n_good n0) as (Hgood1&Hgood2&_).
      pose proof (n_syn n0) as Hsyn. inversion_clear Hsyn as [?? Hsyn2 _].
      pose proof (n_lastd n0) as (?&Last&_).
      inv Hwc. take (_ /\ _) and destruct it as (Hwc&_); simpl in Hwc.
      inv Hwt. take (_ /\ _) and destruct it as (Hwt&_); simpl in Hwt.
      take (clocked_node _ _ _) and destruct it as (Hdom1&Hsc1).
      econstructor.
      + erewrite find_node_now; eauto.
      + eauto.
      + eauto.
      + eapply sem_block_ck_cons2; auto.
        2:{ eapply find_node_not_Is_node_in in Hord2; eauto.
            erewrite find_node_now; eauto. }
        eapply switch_block_sem in Blk; eauto using node_NoDupMembers, node_NoDupLocals, dom_dom_ub, dom_dom_lb.
        13:eapply surjective_pairing.
        * destruct G2; auto.
        * intros ? [Hin|Hin]; apply Env.Props.P.F.empty_in_iff in Hin; inv Hin.
        * intros ? [Hin|Hin]; apply Env.Props.P.F.empty_in_iff in Hin; inv Hin.
        * intros * [Hfind|Hfind]; rewrite Env.gempty in Hfind; congruence.
        * intros * Hfind. rewrite Env.gempty in Hfind. congruence.
        * intros * Hfind. rewrite Env.gempty in Hfind. congruence.
        * reflexivity.
        * now rewrite map_app, map_fst_senv_of_ins, map_fst_senv_of_decls.
        * unfold st_senv. rewrite init_st_anns, app_nil_r.
          eauto using dom_dom_ub.
        * constructor. reflexivity.
        * destruct G1. now inv Hwt.
        * destruct G1. now inv Hwc.
      + constructor; auto.
    - erewrite find_node_other in Hfind; eauto.
      eapply sem_node_ck_cons2...
      destruct G2; apply HGref.
      destruct G1; econstructor...
      eapply sem_block_ck_cons1; eauto using find_node_later_not_Is_node_in.
  Qed.

  Lemma switch_global_refines : forall G,
      wt_global G ->
      wc_global G ->
      global_sem_refines G (switch_global G).
  Proof with eauto using wc_global_Ordered_nodes.
    intros [] (_&Hwt). revert Hwt.
    induction nodes0; intros * Hwt Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      eapply Clocking.switch_global_wc, wc_global_Ordered_nodes in Hwc' ;
        unfold switch_global in Hwc'; simpl in Hwc'.
      apply global_sem_ref_cons with (f:=n_name a)...
      + inv Hwc. inv Hwt. eapply IHnodes0...
      + intros ins outs Hsem; simpl in *.
        change types0 with ((Global types0 externs0 (map switch_node nodes0)).(types)).
        eapply switch_node_sem with (G1:=Global types0 externs0 nodes0)...
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
