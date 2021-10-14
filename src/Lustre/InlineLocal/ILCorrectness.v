From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LCausality Lustre.LSemantics Lustre.LClockSemantics.
From Velus Require Import Lustre.InlineLocal.InlineLocal Lustre.InlineLocal.ILTyping Lustre.InlineLocal.ILClocking.

Module Type ILCORRECTNESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (LCA        : LCAUSALITY Ids Op OpAux Cks Syn)
       (Import Ty : LTYPING Ids Op OpAux Cks Syn)
       (Import Cl : LCLOCKING Ids Op OpAux Cks Syn)
       (Import Ord : LORDERED Ids Op OpAux Cks Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Cks Syn Ord CStr)
       (Import LCS : LCLOCKSEMANTICS Ids Op OpAux Cks Syn Ty Cl LCA Ord CStr Sem)
       (Import IL  : INLINELOCAL Ids Op OpAux Cks Syn).

  Module Typing := ILTypingFun Ids Op OpAux Cks Syn Ty IL.
  Module Clocking := ILClockingFun Ids Op OpAux Cks Syn Cl IL.

  Section rename.
    Variable sub : Env.t ident.

    Lemma rename_in_var_sem : forall H H' x vs,
        (forall y vs, Env.find x sub = Some y -> sem_var H x vs -> sem_var H' y vs) ->
        (forall vs, Env.find x sub = None -> sem_var H x vs -> sem_var H' x vs) ->
        sem_var H x vs ->
        sem_var H' (rename_in_var sub x) vs.
    Proof.
      intros * Hsub Hnsub Hv. unfold rename_in_var.
      destruct (Env.find x sub) eqn:Hfind; eauto.
    Qed.

    Fact history_tl_sub : forall H H' x,
      (forall y vs, Env.find x sub = Some y -> sem_var H x vs -> sem_var H' y vs) ->
      forall y vs, Env.find x sub = Some y -> sem_var (history_tl H) x vs -> sem_var (history_tl H') y vs.
    Proof.
      intros * Hsub * Hfind Hv.
      eapply sem_var_step_inv in Hv as (?&Hv).
      eapply Hsub, sem_var_step in Hv; eauto.
    Qed.

    Fact history_tl_nsub : forall H H' x,
      (forall vs, Env.find x sub = None -> sem_var H x vs -> sem_var H' x vs) ->
      forall vs, Env.find x sub = None -> sem_var (history_tl H) x vs -> sem_var (history_tl H') x vs.
    Proof.
      intros * Hsub * Hfind Hv.
      eapply sem_var_step_inv in Hv as (?&Hv).
      eapply Hsub, sem_var_step in Hv; eauto.
    Qed.

    Lemma rename_in_clock_sem : forall H H' ck bs bs',
        (forall x y vs, Is_free_in_clock x ck -> Env.find x sub = Some y -> sem_var H x vs -> sem_var H' y vs) ->
        (forall x vs, Is_free_in_clock x ck -> Env.find x sub = None -> sem_var H x vs -> sem_var H' x vs) ->
        sem_clock H bs ck bs' ->
        sem_clock H' bs (rename_in_clock sub ck) bs'.
    Proof.
      cofix CoFix; destruct ck; intros * Hsub Hnsub Hsem.
      - inv Hsem; constructor; auto.
      - inv Hsem.
        + econstructor; eauto using rename_in_var_sem.
          eapply CoFix in H6; eauto.
          eapply CoFix in H9; intros; eauto using history_tl_sub, history_tl_nsub.
        + econstructor; eauto using rename_in_var_sem.
          eapply CoFix in H6; eauto.
          eapply CoFix in H9; eauto using history_tl_sub, history_tl_nsub.
        + eapply Son_abs2; eauto using rename_in_var_sem.
          eapply CoFix in H4; eauto.
          eapply CoFix in H10; eauto using history_tl_sub, history_tl_nsub.
    Qed.

    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Section rename_in_exp.

      Variable H H' : history.

      Hypothesis Hsub : forall x y vs,
          Env.find x sub = Some y ->
          sem_var H x vs ->
          sem_var H' y vs.

      Hypothesis Hnsub : forall x vs,
          Env.find x sub = None ->
          sem_var H x vs ->
          sem_var H' x vs.

      Lemma rename_in_exp_sem : forall bs e vss,
          sem_exp_ck G H bs e vss ->
          sem_exp_ck G H' bs (rename_in_exp sub e) vss.
      Proof.
        induction e using exp_ind2; intros * Hsem; inv Hsem; simpl.
        1-12:econstructor; eauto using rename_in_var_sem.
        1-3:rewrite Typing.rename_in_exp_typeof; auto.
        1-5,10-12:(simpl in *;
                   rewrite Forall2_map_1; eapply Forall2_impl_In; [|eauto]; intros; eauto;
                   rewrite Forall_forall in *; eauto).
        - rewrite <-Forall2Brs_map_1. eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hs.
          eapply Exists_exists in Hin as (?&Hin1&Hin2).
          repeat (eapply Forall_forall in H0; eauto).
        - rewrite <-Forall2Brs_map_1. eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hs.
          eapply Exists_exists in Hin as (?&Hin1&Hin2).
          repeat (eapply Forall_forall in H0; eauto).
        - rewrite Typing.rename_in_exp_typeof; auto.
        - rewrite <-Forall2Brs_map_1. eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hs.
          eapply Exists_exists in Hin as (?&Hin1&Hin2).
          repeat (eapply Forall_forall in H0; eauto).
      Qed.

      Corollary rename_in_equation_sem : forall bs eq,
          sem_equation_ck G H bs eq ->
          sem_equation_ck G H' bs (rename_in_equation sub eq).
      Proof.
        intros * Hsem. inv Hsem. simpl in *.
        econstructor; rewrite Forall2_map_1;
          (eapply Forall2_impl_In; [|eauto]; intros);
          eauto using rename_in_var_sem, rename_in_exp_sem.
      Qed.

      Lemma rename_in_sc_vars {B} : forall bs (xs : list (ident * (B * clock))),
          sc_vars (idck xs) H bs ->
          sc_vars (idck (List.map (fun '(x, (ty, ck)) => (rename_in_var sub x, (ty, rename_in_clock sub ck))) xs)) H' bs.
      Proof.
        intros * Hsc.
        unfold sc_vars, idck in *.
        repeat rewrite Forall_map in *.
        eapply Forall_impl; [|eauto]; intros (?&?&?) (?&Hv&Hck); simpl.
        exists x. split; eauto using rename_in_var_sem, rename_in_clock_sem.
      Qed.

    End rename_in_exp.

    Fact mask_hist_sub : forall k r H H',
      (forall x y vs, Env.find x sub = Some y -> sem_var H x vs -> sem_var H' y vs) ->
      forall x y vs, Env.find x sub = Some y -> sem_var (mask_hist k r H) x vs -> sem_var (mask_hist k r H') y vs.
    Proof.
      intros * Hsub * Hfind Hv.
      eapply sem_var_mask_inv in Hv as (?&Hv&Heq).
      eapply Hsub, sem_var_mask in Hv; eauto. rewrite Heq; eauto.
    Qed.

    Fact mask_hist_nsub : forall k r H H',
      (forall x vs, Env.find x sub = None -> sem_var H x vs -> sem_var H' x vs) ->
      forall x vs, Env.find x sub = None -> sem_var (mask_hist k r H) x vs -> sem_var (mask_hist k r H') x vs.
    Proof.
      intros * Hsub * Hfind Hv.
      eapply sem_var_mask_inv in Hv as (?&Hv&Heq).
      eapply Hsub, sem_var_mask in Hv; eauto. rewrite Heq; eauto.
    Qed.

  End rename.

  Import Fresh Facts Tactics.
  Import List.

  Section inlinelocal_node_sem.
    Context {PSyn : block -> Prop}.
    Variable G1 : @global PSyn elab_prefs.
    Variable G2 : @global nolocal_top_block local_prefs.

    Hypothesis HGref : global_sem_refines G1 G2.
    Hypothesis HwG1 : wc_global G1.

    Hint Constructors sem_var.

    Fact sem_var_adds' : forall H xs x vs,
        sem_var (Env.adds' xs H) x vs ->
        (exists vs', vs ≡ vs' /\ In (x, vs') xs) \/ sem_var H x vs.
    Proof.
      intros * Hv. inv Hv.
      eapply Env.find_adds'_In in H1 as [Hin|Hfind]; eauto.
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

    Lemma sem_var_union : forall Hi1 Hi2 x vs,
        sem_var (Env.union Hi1 Hi2) x vs ->
        sem_var Hi1 x vs \/ sem_var Hi2 x vs.
    Proof.
      intros * Hv. inv Hv.
      eapply Env.union_find4 in H0 as [Hfind|Hfind]; eauto.
    Qed.

    Lemma sem_var_disj_union : forall Hi1 Hi2 x vs,
        (forall x, Env.In x Hi1 -> ~Env.In x Hi2) ->
        sem_var (Env.union Hi1 Hi2) x vs <-> sem_var Hi1 x vs \/ sem_var Hi2 x vs.
    Proof.
      intros * Hdisj; split.
      - eapply sem_var_union.
      - intros [Hv|Hv]; inv Hv; econstructor; eauto; unfold Env.MapsTo in *.
        + erewrite Env.union_find2; eauto.
          eapply Env.Props.P.F.not_find_in_iff, Hdisj.
          econstructor; eauto.
        + erewrite Env.union_find3; eauto.
          eapply Env.Props.P.F.not_find_in_iff; intros ?.
          eapply Hdisj; eauto. econstructor; eauto.
    Qed.

    Lemma local_hist_dom_ub : forall xs ys (H H' : Env.t (Stream svalue)),
        Env.dom_ub H xs ->
        Env.dom H' (map fst (Env.elements H) ++ ys) ->
        Env.dom_ub H' (xs ++ ys).
    Proof.
      intros * Hdom1 Hdom2.
      eapply Env.dom_ub_intro; intros ? Hin.
      eapply Env.dom_use in Hin; [|eauto].
      rewrite in_app_iff in *. destruct Hin as [?|?]; auto.
      left. eapply Env.dom_ub_use; eauto.
      eapply in_map_iff in H0 as ((?&?)&?&?); subst.
      eapply Env.elements_In; eauto.
    Qed.

    Lemma local_hist_dom_ub_refines {B C} : forall xs (ys : list (ident * B)) (zs : list (ident * C)) H H',
        (forall x, InMembers x ys \/ InMembers x zs -> ~In x xs) ->
        (forall x vs, sem_var H' x vs -> ~InMembers x ys -> ~InMembers x zs -> sem_var H x vs) ->
        Env.dom_ub H xs ->
        Env.dom H' (map fst (Env.elements H) ++ map fst ys ++ map fst zs) ->
        Env.refines (@EqSt _) H H'.
    Proof.
      intros * Hnd Hinv Hdom1 Hdom2 ?? Hfind.
      assert (In x xs) as Hin.
      { eapply Env.find_In, Env.dom_ub_use in Hfind; eauto. }
      assert (Env.In x H') as (vs'&HfindH').
      { eapply Env.dom_use; eauto. apply in_or_app; left.
        eapply fst_InMembers, Env.In_Members. econstructor; eauto. }
      assert (sem_var H' x vs') as Hv' by (econstructor; eauto; reflexivity).
      eapply Hinv in Hv'. 2,3:intros ?; eapply Hnd; eauto.
      inv Hv'. rewrite H1 in Hfind; inv Hfind.
      do 2 esplit; eauto. now symmetry.
    Qed.

    Hint Constructors NoDupMembers.

    Fact InMembers_sub {A} : forall (sub : Env.t ident) (xs : list (ident * A)) x,
        InMembers x (map_filter (fun '(x, vs) => option_map (fun y : ident => (y, vs)) (Env.find x sub)) xs) ->
        exists y, Env.MapsTo y x sub.
    Proof.
      intros * Hinm.
      eapply InMembers_In in Hinm as (?&Hin).
      eapply map_filter_In' in Hin as ((?&?)&Hin&Hopt).
      eapply option_map_inv in Hopt as (?&Hfind'&Heq); inv Heq.
      eauto.
    Qed.

    Fact InMembers_sub_iff {A} : forall (sub : Env.t ident) (xs : list (ident * A)) x,
        InMembers x (map_filter (fun '(x, vs) => option_map (fun y : ident => (y, vs)) (Env.find x sub)) xs) <->
        exists y, InMembers y xs /\ Env.MapsTo y x sub.
    Proof.
      intros *; split; [intros Hinm|intros (?&Hinm&Hfind)].
      - eapply InMembers_In in Hinm as (?&Hin).
        eapply map_filter_In' in Hin as ((?&?)&Hin&Hopt).
        eapply option_map_inv in Hopt as (?&Hfind'&Heq); inv Heq.
        eauto using In_InMembers.
      - eapply InMembers_In in Hinm as (?&Hin).
        eapply In_InMembers, map_filter_In; eauto.
        simpl. rewrite Hfind; simpl; eauto.
    Qed.

    Fact NoDupMembers_sub {A} : forall (sub : Env.t ident) (xs : list (ident * A)),
        NoDupMembers xs ->
        NoDup (map snd (Env.elements sub)) ->
        NoDupMembers (map_filter (fun '(x, vs) => option_map (fun y => (y, vs)) (Env.find x sub)) xs).
    Proof.
      intros * Hnd1 Hnd2.
      induction xs as [|(?&?)]; inv Hnd1; simpl; auto.
      destruct (option_map _ _) as [(?&?)|] eqn:Hopt; auto.
      econstructor; auto.
      intros Hinm.
      eapply option_map_inv in Hopt as (?&Hfind&Heq); inv Heq.
      apply InMembers_In in Hinm as (?&Hin).
      eapply map_filter_In' in Hin as ((?&?)&Hin&Hopt).
      eapply option_map_inv in Hopt as (?&Hfind'&Heq); inv Heq.
      eapply Env.NoDup_snd_elements in Hnd2; [|eapply Hfind|eapply Hfind']; subst.
      eapply H1, In_InMembers; eauto.
    Qed.

    (** Induction on blocks *)

    Import Permutation.

    Hint Resolve sem_block_refines.
    Hint Resolve InMembers_incl.
    Hint Resolve local_anon_in_block_incl local_anons_in_block_incl.
    Hint Resolve <- fst_InMembers InMembers_idck InMembers_idty.
    Hint Resolve -> fst_InMembers InMembers_idck InMembers_idty.
    Hint Resolve in_or_app In_InMembers.

    Fact mmap_inlinelocal_block_sem : forall vars blks sub vars' blks' st st' bs Hi1 Hi2,
        Forall
          (fun blk => forall sub vars' blks' st st' bs Hi1 Hi2,
               (forall x, InMembers x vars -> ~InMembers x vars') ->
               (forall x, Env.In x sub <-> InMembers x vars') ->
               (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 x vs -> sem_var Hi2 y vs) ->
               (forall x vs, InMembers x vars -> sem_var Hi1 x vs -> sem_var Hi2 x vs) ->
               (forall x y, Env.MapsTo x y sub -> exists n : ident, y = gensym local (Some x) n) ->
               NoDupMembers (vars++vars') ->
               NoDupLocals (map fst (vars++vars')) blk ->
               Forall (AtomOrGensym elab_prefs) (map fst vars) ->
               GoodLocals elab_prefs blk ->
               wc_env (idck (vars++vars')) ->
               wc_block G1 (idck (vars++vars')) blk ->
               Env.dom_ub Hi1 (map fst (vars++vars')) ->
               sem_block_ck G1 Hi1 bs blk ->
               Env.dom Hi2 (map fst vars++st_ids st) ->
               sc_vars (idck (vars++st_anns st)) Hi2 bs ->
               st_valid_after st local PS.empty ->
               inlinelocal_block sub blk st = (blks', st') ->
               exists Hi3,
                 Env.refines (EqSt (A:=svalue)) Hi2 Hi3 /\
                 Env.dom Hi3 (map fst vars++st_ids st') /\
                 sc_vars (idck (vars++st_anns st')) Hi3 bs /\
                 Forall (sem_block_ck G2 Hi3 bs) blks')
          blks ->
        (forall x, InMembers x vars -> ~InMembers x vars') ->
        (forall x, Env.In x sub <-> InMembers x vars') ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 x vs -> sem_var Hi2 y vs) ->
        (forall x vs, InMembers x vars -> sem_var Hi1 x vs -> sem_var Hi2 x vs) ->
        (forall x y, Env.MapsTo x y sub -> exists n : ident, y = gensym local (Some x) n) ->
        NoDupMembers (vars++vars') ->
        Forall (NoDupLocals (map fst (vars++vars'))) blks ->
        Forall (AtomOrGensym elab_prefs) (map fst vars) ->
        Forall (GoodLocals elab_prefs) blks ->
        wc_env (idck (vars++vars')) ->
        Forall (wc_block G1 (idck (vars++vars'))) blks ->
        Env.dom_ub Hi1 (map fst (vars++vars')) ->
        Forall (sem_block_ck G1 Hi1 bs) blks ->
        Env.dom Hi2 (map fst vars++st_ids st) ->
        sc_vars (idck (vars++st_anns st)) Hi2 bs ->
        st_valid_after st local PS.empty ->
        mmap (inlinelocal_block sub) blks st = (blks', st') ->
        exists Hi3,
          Env.refines (EqSt (A:=svalue)) Hi2 Hi3 /\
          Env.dom Hi3 (map fst vars++st_ids st') /\
          sc_vars (idck (vars++st_anns st')) Hi3 bs /\
          Forall (sem_block_ck G2 Hi3 bs) (concat blks').
    Proof with eauto.
      induction blks;
        intros * Hf Hdisj Hsubin Hsub Hnsub Hsubgensym Hnd1 Hnd2 Hatgen Hgood Hwenv Hwc Hub Hsem Hdom Hsc Hvalid Hmmap;
        inv Hf; inv Hnd2; inv Hgood; inv Hwc; inv Hsem; repeat inv_bind; simpl in *.
      - exists Hi2. repeat (split; auto).
      - assert (Hdl:=H).
        eapply H1 with (Hi1:=Hi1) (Hi2:=Hi2)
          in H as (Hi3&Href1&Hdom1&Hsc1&Hsem1)... clear H1.
        eapply IHblks with (Hi1:=Hi1) (Hi2:=Hi3)
          in H0 as (Hi4&Href3&Hdom3&Hsc3&Hsem3)... clear IHblks H2.
        2,3:intros; eauto using sem_var_refines.
        2:{ eapply inlinelocal_block_st_valid_after; eauto. }
        exists Hi4. repeat (split; auto).
        + etransitivity...
        + apply Forall_app; split; auto.
          eapply Forall_impl; [|eauto]; intros...
    Qed.

    (** Central correctness lemma                                              *)
    (* - vars : not renamed (in + out of the node)
       - vars' : renamed (local vars already encountered)
       - Hi1 : history before renaming
       - Hi2 : history after renaming of the enclosing blocks
       - Hi3 : refines Hi2 by adding the renamed variables of the subblocks
     *)
    Lemma inlinelocal_block_sem vars : forall blk sub vars' blks' st st' bs Hi1 Hi2,
        (forall x, InMembers x vars -> ~InMembers x vars') ->
        (forall x, Env.In x sub <-> InMembers x vars') ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 x vs -> sem_var Hi2 y vs) ->
        (forall x vs, InMembers x vars -> sem_var Hi1 x vs -> sem_var Hi2 x vs) ->
        (forall x y, Env.MapsTo x y sub -> exists n, y = gensym local (Some x) n) ->
        NoDupMembers (vars++vars') ->
        NoDupLocals (map fst (vars++vars')) blk ->
        Forall (AtomOrGensym elab_prefs) (map fst vars) ->
        GoodLocals elab_prefs blk ->
        wc_env (idck (vars++vars')) ->
        wc_block G1 (idck (vars++vars')) blk ->
        Env.dom_ub Hi1 (map fst (vars++vars')) ->
        sem_block_ck G1 Hi1 bs blk ->
        Env.dom Hi2 (map fst vars ++ st_ids st) ->
        sc_vars (idck (vars++st_anns st)) Hi2 bs ->
        st_valid_after st local PS.empty ->
        inlinelocal_block sub blk st = (blks', st') ->
        exists Hi3,
          Env.refines (@EqSt _) Hi2 Hi3 /\
          Env.dom Hi3 (map fst vars++st_ids st') /\
          sc_vars (idck (vars++st_anns st')) Hi3 bs /\
          Forall (sem_block_ck G2 Hi3 bs) blks'.
    Proof with eauto.
      induction blk using block_ind2;
        intros * Hdisj Hsubin Hsub Hnsub Hsubgensym Hnd1 Hnd2 Hgenat Hgood Hwenv Hwc Hub Hsem Hdom Hsc Hvalid Hdl;
        inv Hnd2; inv Hgood; inv Hwc; inv Hsem; repeat inv_bind; simpl.
      - (* equation *)
        exists Hi2. repeat split; auto.
        constructor; auto. constructor.
        eapply rename_in_equation_sem; eauto using sem_ref_sem_equation.
        { intros * Hnone Hv.
          assert (Hin:=Hv). eapply sem_var_In, Env.dom_ub_use in Hin; [|eauto].
          repeat rewrite map_app, in_app_iff in Hin.
          destruct Hin as [|]; eauto.
          exfalso. eapply Env.Props.P.F.not_find_in_iff in Hnone. eapply Hnone, Hsubin; eauto.
        }
      - (* reset *)
        rename x into blks'.
        assert (forall k, exists Hi4, Env.refines (@EqSt _) (mask_hist k r Hi2) (mask_hist k r Hi4) /\
                            Env.dom (mask_hist k r Hi4) (map fst vars++st_ids st') /\
                            sc_vars (idck (vars++st_anns st')) (mask_hist k r Hi4) (maskb k r bs) /\
                            Forall (sem_block_ck G2 (mask_hist k r Hi4) (maskb k r bs)) (concat blks')) as Hblks.
        { intros k. specialize (H12 k).
          eapply mmap_inlinelocal_block_sem with (Hi2:=mask_hist k r Hi2) in H12
            as (Hi4&Href1&Hdom1&Hsc1&Hsem1); eauto.
          2:{ intros ??? Hfind Hv.
              eapply sem_var_mask_inv in Hv as (?&Hv&Hmask).
              rewrite Hmask. eapply sem_var_mask... }
          2:{ intros ?? Hin Hv.
              eapply sem_var_mask_inv in Hv as (?&Hv&Hmask).
              rewrite Hmask. eapply sem_var_mask...
          }
          2:{ setoid_rewrite Env.dom_ub_map; eauto. }
          2:{ eapply Env.dom_map; eauto. }
          2:{ eapply sc_vars_mask; eauto; subst. }
          assert (Env.Equiv (@EqSt _) Hi4 (mask_hist k r Hi4)) as Heqmask.
          { unfold st_ids in Hdom1.
            rewrite <-map_app, <-map_fst_idck in Hdom1.
            eapply slower_mask_hist, sc_vars_slower_hist; [|eauto].
            repeat rewrite idck_app in *. simpl_app. eauto. }
          exists Hi4. repeat split; auto.
          + rewrite <-Heqmask; auto.
          + rewrite <-Heqmask.
            eapply Env.dom_Permutation; [|eauto]. solve_Permutation_app.
          + rewrite Heqmask in Hsc1. eapply Permutation_Forall; [|eauto].
            repeat rewrite idck_app. solve_Permutation_app.
          + eapply Forall_impl; [|eauto]; intros. rewrite <-Heqmask...
        }
        eapply consolidate_mask_hist
          with (P := fun k H'k =>
                       Env.refines (@EqSt _) (mask_hist k r Hi2) H'k /\
                       Env.dom H'k (map fst vars++st_ids st') /\
                       sc_vars (idck (vars++st_anns st')) H'k (maskb k r bs) /\
                       Forall (sem_block_ck G2 H'k (maskb k r bs)) (concat blks'))
        in Hblks as (Hi4&HHi4).
        2:{ intros ????? Heq (?&?&?&?); subst. repeat (split; auto).
            1-3:intros; rewrite <-Heq; auto.
            eapply Forall_impl; [|eauto]; intros.
            rewrite <-Heq...
        }
        2:{ intros ????? (_&Hdom1&_) (_&Hdom2&_) Hdom'.
            eapply Env.dom_intro; intros.
            eapply Env.dom_use in Hdom1. eapply Env.dom_use in Hdom2. eapply Env.dom_use in Hdom'.
            rewrite Hdom2, <-Hdom1...
        }
        assert (Env.refines (@EqSt _) Hi2 Hi4) as Href1.
        { eapply refines_unmask; intros. eapply HHi4. }
        exists Hi4. repeat split; try rewrite app_nil_r; repeat rewrite <-app_assoc...
        + erewrite <-Env.dom_map. eapply (HHi4 0)...
        + eapply sc_vars_unmask. intros k. eapply (HHi4 k)...
        + do 2 (econstructor; eauto).
          * eapply sem_exp_refines; [eauto|].
            eapply rename_in_exp_sem; eauto using sem_ref_sem_exp.
            { intros * Hnone Hv.
              assert (Hin:=Hv). eapply sem_var_In, Env.dom_ub_use in Hin; [|eauto].
              repeat rewrite map_app, in_app_iff in Hin.
              destruct Hin as [|]; eauto.
              exfalso. eapply Env.Props.P.F.not_find_in_iff in Hnone. eapply Hnone, Hsubin; eauto.
            }
          * intros. eapply HHi4...
      - (* local *)
        assert (forall x, Env.In x x0 <-> InMembers x locs) as Hsubin'.
        { intros. split; intros * Hin.
          - eapply fresh_idents_rename_sub1 in Hin; [|eauto].
            unfold idty in *. erewrite fst_InMembers, 2 map_map, map_ext, <-fst_InMembers in Hin...
            intros (?&(?&?)&?)...
          - eapply fresh_idents_rename_sub2 in H0.
            unfold idty in *. erewrite fst_InMembers, 2 map_map, map_ext, <-fst_InMembers in H0...
            2:intros (?&(?&?)&?); auto.
            apply H0 in Hin as (?&?&?&_); eauto. econstructor...
        }
        assert (forall x, InMembers x (map_filter (fun '(x, vs) => option_map (fun y => (y, vs)) (Env.find x x0)) (Env.elements H')) ->
                     ~ Env.In x Hi2) as Hdisj2.
        { intros ? Hinm Henvin. eapply InMembers_sub in Hinm as (?&Hfind).
          assert (Hfind':=Hfind). eapply fresh_idents_rename_sub_gensym in Hfind as (?&?); eauto; subst.
          eapply Env.dom_use in Henvin; eauto. rewrite in_app_iff in Henvin.
          destruct Henvin as [Hin1|Hin1].
          - eapply Forall_incl, Forall_forall in Hgenat; eauto. 2:solve_incl_app.
            eapply contradict_AtomOrGensym in Hgenat; eauto using local_not_in_elab_prefs.
          - eapply fresh_idents_rename_sub_nIn in Hin1; eauto.
        }
        assert (forall x : Env.key, Env.In x sub -> ~Env.In x x0) as Hsub1.
        { intros ?. rewrite Hsubin, Hsubin'. intros Hin1 Hin2.
          eapply H5... repeat rewrite map_app, in_app_iff... }
        assert (NoDupMembers (map_filter (fun '(x4, vs0) => option_map (fun y0 : ident => (y0, vs0)) (Env.find x4 x0)) (Env.elements H'))) as HndH'.
        { eapply NoDupMembers_sub; eauto using Env.NoDupMembers_elements.
          eapply fresh_idents_rename_sub_NoDup; [|eauto].
          erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers, NoDupMembers_idty; auto.
          intros (?&?&?); auto. }
        eapply mmap_inlinelocal_block_sem with
            (vars':=vars'++idty locs) (Hi1:=H') (Hi2:=Env.adds' (map_filter (fun '(x, vs) => option_map (fun y => (y, vs)) (Env.find x x0)) (Env.elements H')) Hi2)
          in H1 as (Hi3&Href1&Hdom1&Hsc1&Hsem1); eauto. clear H.
        + exists Hi3. repeat (split; eauto).
          etransitivity...
          intros ?? Hfind. eexists; split; try reflexivity.
          erewrite Env.gsso'; eauto. intros contra.
          eapply Hdisj2... econstructor...
        + intros ?. rewrite InMembers_app. intros Hinm1 [Hinm2|Hinm2].
          * eapply Hdisj; eauto.
          * eapply H5... repeat rewrite map_app, in_app_iff...
        + intros ?. rewrite Env.union_In, Hsubin, Hsubin', InMembers_app.
          split; intros [?|?]...
        + intros ??? Hfind Hv.
          erewrite sem_var_disj_adds'; eauto.
          eapply Env.union_find4 in Hfind as [Hfind|Hfind].
          * right. eapply Hsub; eauto.
            eapply H10; eauto; eapply Env.find_In in Hfind; rewrite Hsubin in Hfind.
            intros contra. eapply H5... repeat rewrite map_app, in_app_iff...
          * left. inv Hv. do 2 esplit; eauto.
            eapply map_filter_In. eapply Env.elements_correct; eauto.
            simpl. rewrite Hfind; auto.
        + intros ?? Hfind Hv.
          erewrite sem_var_disj_adds'; eauto. right.
          eapply Hnsub, H10; eauto; intro Hinm2.
          eapply H5... repeat rewrite map_app, in_app_iff...
        + intros ?? Hfind.
          eapply Env.union_find4 in Hfind as [Hfind|Hfind]...
          eapply fresh_idents_rename_sub_gensym...
        + clear - Hnd1 H5 H4. rewrite app_assoc.
          eapply NoDupMembers_app; eauto.
          * rewrite NoDupMembers_idty; auto.
          * intros ? Hinm Hinm2. rewrite InMembers_idty in Hinm2.
            eapply H5...
        + clear - H2.
          repeat rewrite map_app in *. repeat rewrite <- app_assoc in *.
          rewrite map_fst_idty.
          eapply Forall_impl; [|eauto]; intros.
          eapply NoDupLocals_Permutation_Proper. 2,3:eauto. solve_Permutation_app.
        + clear - Hwenv H9.
          rewrite app_assoc, idck_app. apply Forall_app; split.
          * eapply Forall_impl; [|eauto]; intros (?&?) ?.
            eapply wc_clock_incl; [|eauto]. solve_incl_app.
          * rewrite Forall_map in H9. eapply Forall_impl; [|eauto]; intros (?&?) ?; eauto.
        + clear - H8. repeat rewrite idck_app in *. now rewrite <-app_assoc in H8.
        + eapply local_hist_dom_ub in H11; eauto.
          eapply Env.dom_ub_incl; [|eauto].
          simpl_app. rewrite map_fst_idty; simpl.
          eapply Permutation_incl1; [|reflexivity]. solve_Permutation_app.
        +{ eapply Env.dom_intro. intros.
           rewrite Env.In_adds_spec', InMembers_sub_iff.
           unfold st_ids. erewrite fresh_idents_rename_anns; eauto. setoid_rewrite <-Env.In_Members.
           repeat setoid_rewrite Env.dom_use; eauto. simpl_app.
           repeat rewrite in_app_iff.
           split; [intros [(?&Hin&Hmaps)|[|]]|intros [|[Hin|Hin]]]...
           - repeat rewrite in_app_iff in Hin. destruct Hin as [Hin|Hin].
             + exfalso. eapply fst_InMembers, Env.In_Members, Env.dom_ub_use in Hin...
               eapply Env.find_In, Hsubin' in Hmaps.
               eapply H5...
             + right; left.
               eapply fresh_idents_rename_ids in H0; eauto; subst.
               2:erewrite fst_NoDupMembers, map_map, map_ext, map_fst_idty, <-fst_NoDupMembers; simpl; auto; intros (?&?&?); auto.
               eapply fst_InMembers, InMembers_In in Hin as (((?&?)&?)&Hin).
               unfold idty. repeat rewrite map_map.
               eapply in_map_iff. do 2 esplit; eauto. simpl. now rewrite Hmaps.
           - eapply fresh_idents_rename_ids in H0; eauto.
             2:erewrite fst_NoDupMembers, map_map, map_ext, map_fst_idty, <-fst_NoDupMembers; simpl; auto; intros (?&?&?); auto.
             rewrite H0, map_map, map_map in Hin.
             unfold idty in Hin. repeat rewrite map_map in Hin.
             eapply in_map_iff in Hin as ((?&(?&?)&?)&?&?); simpl in *.
             left. do 2 esplit; eauto. repeat rewrite in_app_iff; eauto using in_map_iff.
             destruct (Env.find i x0) eqn:Hfind; simpl in *; subst; auto.
             exfalso. eapply Env.Props.P.F.not_find_in_iff in Hfind. rewrite Hsubin' in Hfind.
             eapply Hfind; eauto.
         }
        +{ assert (Env.refines (@EqSt _) Hi2 (Env.adds' (map_filter (fun '(x3, vs) => option_map (fun y : ident => (y, vs)) (Env.find x3 x0)) (Env.elements H')) Hi2)) as Href.
           { intros ?? Hfind. do 2 esplit; try reflexivity.
             erewrite Env.gsso'... intro contra.
             eapply Hdisj2... econstructor... }
           erewrite fresh_idents_rename_anns; eauto. repeat rewrite idck_app in *.
           simpl in Hsc.
           unfold sc_vars in *. repeat rewrite Forall_app in Hsc. destruct Hsc as (Hsc1&Hsc2).
           repeat rewrite Forall_app. repeat split; eauto.
           1,3:eapply sc_vars_refines...
           eapply fresh_idents_rename_ids in H0.
           2:erewrite fst_NoDupMembers, map_map, map_ext, map_fst_idty, <-fst_NoDupMembers; auto;
             intros (?&?&?); auto.
           eapply sc_vars_restrict in H14; eauto. 2:solve_incl_app.
           unfold idty, idck, sc_vars in *. rewrite H0, 3 map_map, Forall_map; simpl.
           repeat rewrite map_app in H14. repeat rewrite map_map in H14. simpl in H14. rewrite Forall_map in H14.
           eapply Forall_impl_In; [|eapply H14]; intros (?&(?&?)&?) Hin (xs&?&Hck); simpl in *.
           exists xs; split.
           - eapply rename_in_var_sem; [| |eauto]...
             + intros * Hfind Hv. eapply sem_var_restrict_inv in Hv as (Hin'&Hv). eapply sem_var_disj_adds'...
               left. inv Hv. do 2 esplit; eauto.
               eapply map_filter_In; eauto using Env.elements_correct; simpl. now rewrite Hfind.
             + intros * Hfind Hv. eapply sem_var_restrict_inv in Hv as (Hin'&Hv). eapply sem_var_disj_adds'...
               repeat rewrite in_app_iff in Hin'.
               exfalso. rewrite <-Env.Props.P.F.not_find_in_iff, Hsubin' in Hfind; eauto.
           - assert (forall x, InMembers x locs -> ~ Env.In x Hi2) as Hdisj3.
             { intros ? Hinm Henv. eapply Env.dom_use in Henv; [|eauto].
               apply in_app_iff in Henv as [Hin'|Hin'].
               - eapply H5... eapply incl_map; [|eauto]; solve_incl_app.
               - eapply st_valid_after_AtomOrGensym_nIn in Hin'; eauto using local_not_in_elab_prefs.
                 eapply Forall_forall in H3... }
             eapply rename_in_clock_sem, rename_in_clock_sem
               with (H':=Env.union (Env.restrict H' (map fst locs)) Hi2). 5:eauto.
             + intros * Hfree Hfind Hv. eapply sem_var_union in Hv as [Hv|Hv]; eapply sem_var_disj_adds'...
               * eapply sem_var_restrict_inv in Hv as (Hin'&Hv).
                 left. inv Hv. do 2 esplit...
                 eapply map_filter_In; eauto using Env.elements_correct; simpl. now rewrite Hfind.
               * exfalso. eapply sem_var_In, Hdisj3 in Hv...
                 eapply Hsubin', Env.find_In...
             + intros * Hfree Hfind Hv. eapply sem_var_union in Hv as [Hv|Hv]; eapply sem_var_disj_adds'...
               exfalso. eapply sem_var_restrict_inv in Hv as (Hin'&Hv).
               eapply Env.Props.P.F.not_find_in_iff... rewrite Hsubin'...
             + intros * Hfree Hfind Hv. eapply sem_var_restrict_inv in Hv as (Hin'&Hv). eapply sem_var_disj_union...
               1:intros * Henv; eapply Env.restrict_In in Henv...
               right. eapply Hsub; eauto. eapply H10; eauto; eapply Env.find_In in Hfind; rewrite Hsubin in Hfind.
               intros contra. eapply H5... repeat rewrite map_app, in_app_iff...
             + intros * Hfree Hfind Hv. eapply sem_var_restrict_inv in Hv as (Hin'&Hv). eapply sem_var_disj_union...
               1:intros * Henv; eapply Env.restrict_In in Henv...
               repeat rewrite in_app_iff in Hin'. destruct Hin' as [[Hin'|Hin']|Hin']; rewrite <-fst_InMembers in Hin'.
               * right. eapply Hnsub, H10...
                 intros contra. eapply H5... repeat rewrite map_app, in_app_iff...
               * exfalso. eapply Env.Props.P.F.not_find_in_iff... rewrite Hsubin...
               * left. eapply sem_var_restrict; eauto.
         }
        + eapply fresh_idents_rename_st_valid; eauto.
    Qed.

    Lemma inlinelocal_topblock_sem vars : forall blk blks' locs' st st' bs Hi1 Hi2,
        (forall x vs, InMembers x vars -> sem_var Hi1 x vs -> sem_var Hi2 x vs) ->
        NoDupMembers vars ->
        NoDupLocals (map fst vars) blk ->
        Forall (AtomOrGensym elab_prefs) (map fst vars) ->
        GoodLocals elab_prefs blk ->
        wc_env (idck (vars)) ->
        wc_block G1 (idck vars) blk ->
        Env.dom Hi1 (map fst vars) ->
        sem_block_ck G1 Hi1 bs blk ->
        Env.dom Hi2 (map fst vars ++ st_ids st) ->
        sc_vars (idck (vars++st_anns st)) Hi2 bs ->
        st_valid_after st local PS.empty ->
        inlinelocal_topblock blk st = (blks', locs', st') ->
        exists Hi3,
          Env.refines (@EqSt _) Hi2 Hi3 /\
          Env.dom Hi3 (map fst (vars++idty locs')++st_ids st') /\
          sc_vars (idck (vars++idty locs'++st_anns st')) Hi3 bs /\
          Forall (sem_block_ck G2 Hi3 bs) blks'.
    Proof with eauto.
      Opaque inlinelocal_block.
      destruct blk; intros * Hinm Hnd1 Hnd2 Hatgen  Hgood Hwenv Hwc Hdom1 Hsem Hdom2 Hsc Hvalid Hil;
        repeat inv_bind; simpl in *.
      1,2:eapply inlinelocal_block_sem with (Hi1:=Hi1) in H as (Hi3&?&Hdom3&Hsc3&?);
        repeat rewrite app_nil_r in *; eauto; simpl in *.
      9:inv Hnd2; inv Hgood; inv Hwc; inv Hsem.
      9:assert (forall x, Env.In x (Env.restrict H' (map fst locs')) -> ~ Env.In x Hi2) as Hdisj2.
      9:{ intros * Hin1 Hin2. eapply Env.restrict_In in Hin1.
          eapply Env.dom_use, in_app_iff in Hin2 as [Hin2|Hin2]...
          - eapply H5...
          - eapply st_valid_after_AtomOrGensym_nIn in Hin2; eauto using local_not_in_elab_prefs.
            eapply Forall_forall in H3... }
      9:assert (Env.refines (EqSt (A:=svalue)) (Env.restrict H' (map fst (vars ++ (idty locs')))) (Env.union (Env.restrict H' (map fst locs')) Hi2)) as Href.
      9:{ intros ?? Hfind. eapply Env.restrict_find_inv in Hfind as (Hin&Hfind).
          rewrite map_app, map_fst_idty, in_app_iff in Hin. destruct Hin as [Hin|Hin].
          - assert (sem_var H' x0 v) as Hv by (econstructor; eauto; reflexivity).
            eapply H10, Hinm in Hv; eauto. inv Hv.
            + do 2 esplit; eauto. eapply Env.union_find3'; eauto.
            + intros contra. eapply H5; eauto.
          - do 2 esplit; try reflexivity.
            eapply Env.union_find2. eapply Env.restrict_find; eauto.
            eapply Env.Props.P.F.not_find_in_iff, Hdisj2, Env.restrict_In_iff; eauto.
            split; auto. econstructor; eauto. }
      9:eapply mmap_inlinelocal_block_sem
        with (vars:=vars++idty locs')
             (Hi1:=H')
             (Hi2:=Env.union (Env.restrict H' (map fst locs')) Hi2)
        in H as (Hi3&?&Hdom3&Hsc3&?);
        repeat rewrite app_nil_r in *; eauto; simpl in *.
      10:eapply Forall_forall; intros; eauto using inlinelocal_block_sem.
      1,5,10:intros *; rewrite Env.Props.P.F.empty_in_iff; split; intros [].
      1,2,4,5,8,10:intros * Hfind; eapply Env.Props.P.F.empty_mapsto_iff in Hfind as [].
      1,2:eapply Env.dom_dom_ub...
      - exists Hi3. repeat split...
        + etransitivity; eauto using Env.union_refines4'.
        + clear - Hsc3. repeat rewrite idck_app in *.
          eapply Permutation_Forall; [|eauto]. solve_Permutation_app.
      - intros * Hinm1 Hv.
        eapply sem_var_refines... eapply sem_var_restrict...
      - apply NoDupMembers_app; auto.
        + apply NoDupMembers_idty; auto.
        + intros ? Hinm1 Hinm2. rewrite InMembers_idty in Hinm2.
          eapply H5...
      - eapply Forall_impl; [|eapply H2]; intros.
        now rewrite map_app, map_fst_idty.
      - rewrite map_app, map_fst_idty.
        apply Forall_app; auto.
      - rewrite idck_app.
        apply Forall_app; split.
        + eapply Forall_impl; [|eapply Hwenv]; intros (?&?) ?.
          eapply wc_clock_incl; eauto; solve_incl_app.
        + rewrite Forall_map in H9.
          eapply Forall_impl; [|eapply H9]; intros (?&?) ?; eauto.
      - now rewrite idck_app.
      - rewrite map_app, map_fst_idty.
        eapply Env.dom_dom_ub, local_hist_dom; eauto.
      - rewrite (Permutation_app_comm vars), map_app, <-app_assoc, map_fst_idty.
        eapply Env.union_dom; eauto.
        eapply Env.dom_lb_restrict_dom, Env.dom_lb_incl, Env.dom_dom_lb; eauto. solve_incl_app.
      - unfold sc_vars. rewrite (Permutation_app_comm vars), 2 idck_app, <-app_assoc.
        apply Forall_app; split; try rewrite <-idck_app.
        + eapply sc_vars_restrict in H14. 3:eauto. 2:solve_incl_app.
          eapply sc_vars_refines; [|eauto]. rewrite <-idck_app, map_fst_idck...
        + eapply sc_vars_refines; [|eauto]. eapply Env.union_refines4'; eauto.
      Transparent inlinelocal_block.
    Qed.

    Lemma inlinelocal_node_sem : forall f n ins outs,
        wc_global (Global G1.(enums) (n::G1.(nodes))) ->
        Ordered_nodes (Global G1.(enums) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(enums) ((inlinelocal_node n)::G2.(nodes))) ->
        sem_node_ck (Global G1.(enums) (n::G1.(nodes))) f ins outs ->
        sem_node_ck (Global G2.(enums) ((inlinelocal_node n)::G2.(nodes))) f ins outs.
    Proof with eauto.
      intros * Hwc Hord1 Hord2 Hsem.

      inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
      - erewrite find_node_now in Hfind; eauto. inv Hfind.
        (*The semantics of equations can be given according to G only *)
        eapply sem_block_ck_cons in H3; eauto. rename H3 into Hblksem.
        2:{ inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }

        replace {| enums := enums G1; nodes := nodes G1 |} with G1 in Hblksem by (destruct G1; auto).
        pose proof (n_nodup n0) as (Hnd1&Hnd2).
        pose proof (n_good n0) as (Hgood1&Hgood2&_).
        inv Hwc. destruct H4 as (Hwc&_); simpl in Hwc.
        destruct H5 as (Hdom1&Hsc1).
        eapply inlinelocal_topblock_sem
          with (vars:=idty (n_in n0 ++ n_out n0))
               (st:=init_st)
               (Hi2:=H)
               (blks':=fst (fst (inlinelocal_topblock (n_block n0) init_st)))
               (locs':=snd (fst (inlinelocal_topblock (n_block n0) init_st)))
               (st':=snd (inlinelocal_topblock (n_block n0) init_st))
          in Hblksem as (Hf&Href&Hdom&Hsc&Hsem); eauto. 10:destruct inlinelocal_topblock as ((?&?)&?); reflexivity.
        eapply Snode with (H0:=H); simpl; eauto.
        + erewrite find_node_now; eauto.
        + eauto.
        + eauto.
        + apply sem_block_ck_cons'; simpl...
          2:{ eapply find_node_not_Is_node_in in Hord2.
            2:erewrite find_node_now; eauto. eauto. }
          destruct (inlinelocal_topblock _ _) as ((?&?)&?) eqn:Hil.
          econstructor. 4:destruct G2; eauto.
          * intros ?? Hv Hnin1.
            eapply sem_var_refines_iff. 1,4:eauto.
            eapply Env.dom_dom_lb...
            eapply sem_var_In, Env.dom_use in Hv; [|eauto].
            rewrite map_app in Hv; simpl in Hv. repeat rewrite in_app_iff in Hv.
            destruct Hv as [[Hin|Hin]|Hin]; auto. 1-2:exfalso.
            -- eapply Hnin1. rewrite InMembers_app; auto.
            -- eapply Hnin1. rewrite InMembers_app, 2 fst_InMembers, map_map; auto.
          * eapply local_hist_dom; eauto; simpl.
            repeat rewrite map_app in *. repeat rewrite map_fst_idty in Hdom. repeat rewrite map_fst_idty.
            simpl in *. rewrite <-app_assoc in Hdom.
            rewrite map_map.  auto.
          * eapply Forall_incl; [eauto|].
            unfold idck, idty. repeat rewrite map_app. repeat rewrite map_map. repeat rewrite <-app_assoc. simpl.
            solve_incl_app.
        + simpl. constructor; simpl; auto.
        + eapply NoDupMembers_app_l; eauto.
        + rewrite map_fst_idty. eapply NoDupLocals_incl; eauto. solve_incl_app.
        + rewrite map_fst_idty. eapply Forall_incl; eauto. solve_incl_app.
        + destruct Hwc as (?&?&?); auto.
        + destruct Hwc as (?&?&?), G1; auto.
        + unfold st_ids; rewrite init_st_anns, app_nil_r...
        + rewrite init_st_anns; simpl. rewrite app_nil_r...
        + eapply init_st_valid; eauto using local_not_in_elab_prefs, PS_For_all_empty.
      - erewrite find_node_other in Hfind; eauto.
        eapply sem_node_ck_cons'...
        destruct G2; apply HGref.
        econstructor...
        destruct G1; eapply sem_block_ck_cons...
        eapply find_node_later_not_Is_node_in in Hord1...
    Qed.

  End inlinelocal_node_sem.

  Fact wc_global_Ordered_nodes {PSyn prefs} : forall (G: @global PSyn prefs),
      wc_global G ->
      Ordered_nodes G.
  Proof.
    intros G Hwt.
    apply wl_global_Ordered_nodes; auto.
  Qed.
  Hint Resolve wc_global_Ordered_nodes.

  Lemma inlinelocal_global_refines : forall G,
      wc_global G ->
      global_sem_refines G (inlinelocal_global G).
  Proof with eauto.
    intros (enms&nds).
    induction nds; intros * Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      eapply Clocking.inlinelocal_global_wc, wc_global_Ordered_nodes in Hwc' ;
        unfold inlinelocal_global in Hwc'; simpl in Hwc'.
      apply global_sem_ref_cons with (f:=n_name a)...
      + inv Hwc. eapply IHnds...
      + intros ins outs Hsem; simpl in *.
        change enms with ((Global enms (map inlinelocal_node nds)).(enums)).
        eapply inlinelocal_node_sem with (G1:=Global enms nds)...
        1,2:inv Hwc...
  Qed.

  Theorem inlinelocal_global_sem : forall G f ins outs,
      wc_global G ->
      sem_node_ck G f ins outs ->
      sem_node_ck (inlinelocal_global G) f ins outs.
  Proof.
    intros.
    eapply inlinelocal_global_refines in H; eauto.
    specialize (H f ins outs); auto.
  Qed.

End ILCORRECTNESS.

Module ILCorrectnessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (LCA : LCAUSALITY Ids Op OpAux Cks Syn)
       (Ty : LTYPING Ids Op OpAux Cks Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (Lord : LORDERED Ids Op OpAux Cks Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Syn Lord CStr)
       (LClockSem : LCLOCKSEMANTICS Ids Op OpAux Cks Syn Ty Clo LCA Lord CStr Sem)
       (IL  : INLINELOCAL Ids Op OpAux Cks Syn)
       <: ILCORRECTNESS Ids Op OpAux Cks CStr Syn LCA Ty Clo Lord Sem LClockSem IL.
  Include ILCORRECTNESS Ids Op OpAux Cks CStr Syn LCA Ty Clo Lord Sem LClockSem IL.
End ILCorrectnessFun.
