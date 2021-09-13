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
       (Import LCS : LCLOCKSEMANTICS Ids Op OpAux Cks Syn Cl LCA Ord CStr Sem)
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
        1-11:econstructor; eauto using rename_in_var_sem.
        1-3:rewrite Typing.rename_in_exp_typeof; auto.
        1-6,9-11:(rewrite Forall2_map_1; eapply Forall2_impl_In; [|eauto]; intros; eauto;
                  rewrite Forall_forall in *; eauto).
        - (* merge *)
          rewrite Forall2_map_1. eapply Forall2_impl_In; [|eauto]; intros.
          specialize (H0 _ H1). rewrite Forall_forall in *; eauto.
        - (* case *)
          rewrite Forall2_map_1. eapply Forall2_impl_In; [|eapply H10]; intros.
          destruct a0; simpl in *; inv H5.
          specialize (H4 _ eq_refl).
          rewrite Forall2_map_1. eapply Forall2_impl_In; [|eauto]; intros.
          eapply Forall_forall in H0; eauto; simpl in *.
          rewrite Forall_forall in *; eauto.
        - rewrite Forall2_map_1. eapply Forall2_impl_In; [|eapply H12]; intros.
          destruct a0; simpl in *; inv H5; eauto.
        - (* app *)
          unfold clocked_app in *.
          rewrite Forall2_map_1. eapply Forall2_impl_In; [|eauto]; intros (?&(?&[|])) ??? Hck; simpl in *; auto.
          destruct Hck. split; eauto using rename_in_var_sem, rename_in_clock_sem.
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

    (* Lemma rename_in_block_sem : forall blk bs H H', *)
    (*     (forall x y vs, Env.find x sub = Some y -> sem_var H x vs -> sem_var H' y vs) -> *)
    (*     (forall x vs, Env.find x sub = None -> sem_var H x vs -> sem_var H' x vs) -> *)
    (*     nolocal_block blk -> *)
    (*     sem_block_ck G H bs blk -> *)
    (*     sem_block_ck G H' bs (rename_in_block sub blk). *)
    (* Proof. *)
    (*   induction blk using block_ind2; intros * Hsub Hnsub Hnl Hsem; inv Hnl; inv Hsem; simpl. *)
    (*   - (* equation *) *)
    (*     constructor. eapply rename_in_equation_sem; eauto. *)
    (*   - (* reset *) *)
    (*     econstructor; eauto using rename_in_exp_sem. *)
    (*     intros k. specialize (H9 k). *)
    (*     rewrite Forall_map. rewrite Forall_forall in *; intros. *)
    (*     eapply H; [eauto| | |eauto|eauto]; eauto using mask_hist_sub, mask_hist_nsub. *)
    (* Qed. *)

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

    (* Fact sem_var_gsso' : forall H xs x vs, *)
    (*     ~InMembers x xs -> *)
    (*     sem_var H x vs -> *)
    (*     sem_var (Env.adds' xs H) x vs. *)
    (* Proof. *)
    (*   intros * Hnin Hv. inv Hv. *)
    (*   econstructor; [|eauto]. *)
    (*   unfold Env.MapsTo in *. erewrite Env.gsso'; eauto. *)
    (* Qed. *)

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

    Fact mmap_inlinelocal_block_sem : forall vars blks sub vars' panons blks' st st' bs Hi1 Hi2,
        Forall
          (fun blk => forall sub vars' panons blks' st st' bs Hi1 Hi2,
               (forall x, InMembers x vars \/ InMembers x (anon_in_block blk) -> ~InMembers x vars') ->
               (forall x, Env.In x sub <-> InMembers x vars') ->
               (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 x vs -> sem_var Hi2 y vs) ->
               (forall x vs, InMembers x vars \/ InMembers x panons -> sem_var Hi1 x vs -> sem_var Hi2 x vs) ->
               (forall x y, Env.MapsTo x y sub -> exists n : ident, y = gensym local (Some x) n) ->
               NoDupMembers (vars++vars'++panons++anon_in_block blk) ->
               NoDupLocals (map fst (vars++vars'++panons++anon_in_block blk)) blk ->
               Forall (AtomOrGensym elab_prefs) (map fst (vars++panons++anon_in_block blk)) ->
               GoodLocals elab_prefs blk ->
               wc_env (idck (vars++vars')) ->
               wc_block G1 (idck (vars++vars')) blk ->
               Env.dom_lb Hi1 (map fst (local_anon_in_block blk)) ->
               Env.dom_ub Hi1 (map fst (vars++vars'++panons++local_anon_in_block blk)) ->
               sem_block_ck G1 Hi1 bs blk ->
               Env.dom Hi2 (map fst (vars++panons)++st_ids st) ->
               sc_vars (idck (vars++panons++st_anns st)) Hi2 bs ->
               st_valid_after st local PS.empty ->
               inlinelocal_block sub blk st = (blks', st') ->
               exists Hi3,
                 Env.refines (EqSt (A:=svalue)) Hi2 Hi3 /\
                 Env.dom Hi3 (map fst (vars++panons++flat_map anon_in_block blks')++st_ids st') /\
                 sc_vars (idck (vars++panons++flat_map anon_in_block blks'++st_anns st')) Hi3 bs /\
                 (forall x vs, InMembers x (flat_map anon_in_block blks') -> sem_var Hi1 x vs -> sem_var Hi3 x vs) /\
                 Forall (sem_block_ck G2 Hi3 bs) blks')
          blks ->
        (forall x, InMembers x vars \/ InMembers x (flat_map anon_in_block blks) -> ~InMembers x vars') ->
        (forall x, Env.In x sub <-> InMembers x vars') ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 x vs -> sem_var Hi2 y vs) ->
        (forall x vs, InMembers x vars \/ InMembers x panons -> sem_var Hi1 x vs -> sem_var Hi2 x vs) ->
        (forall x y, Env.MapsTo x y sub -> exists n : ident, y = gensym local (Some x) n) ->
        NoDupMembers (vars++vars'++panons++flat_map anon_in_block blks) ->
        Forall (NoDupLocals (map fst (vars++vars'++panons++flat_map anon_in_block blks))) blks ->
        Forall (AtomOrGensym elab_prefs) (map fst (vars++panons++flat_map anon_in_block blks)) ->
        Forall (GoodLocals elab_prefs) blks ->
        wc_env (idck (vars++vars')) ->
        Forall (wc_block G1 (idck (vars++vars'))) blks ->
        Env.dom_lb Hi1 (map fst (flat_map local_anon_in_block blks)) ->
        Env.dom_ub Hi1 (map fst (vars++vars'++panons++flat_map local_anon_in_block blks)) ->
        Forall (sem_block_ck G1 Hi1 bs) blks ->
        Env.dom Hi2 (map fst (vars++panons)++st_ids st) ->
        sc_vars (idck (vars++panons++st_anns st)) Hi2 bs ->
        st_valid_after st local PS.empty ->
        mmap (inlinelocal_block sub) blks st = (blks', st') ->
        exists Hi3,
          Env.refines (EqSt (A:=svalue)) Hi2 Hi3 /\
          Env.dom Hi3 (map fst (vars++panons++flat_map anon_in_block (concat blks'))++st_ids st') /\
          sc_vars (idck (vars++panons++flat_map anon_in_block (concat blks')++st_anns st')) Hi3 bs /\
          (forall x vs, InMembers x (flat_map anon_in_block (concat blks')) -> sem_var Hi1 x vs -> sem_var Hi3 x vs) /\
          Forall (sem_block_ck G2 Hi3 bs) (concat blks').
    Proof with eauto.
      induction blks;
        intros * Hf Hdisj Hsubin Hsub Hnsub Hsubgensym Hnd1 Hnd2 Hatgen Hgood Hwenv Hwc Hlb Hub Hsem Hdom Hsc Hvalid Hmmap;
        inv Hf; inv Hnd2; inv Hgood; inv Hwc; inv Hsem; repeat inv_bind; simpl in *.
      - exists Hi2. repeat (split; auto). now rewrite app_nil_r.
        intros ?? [].
      - assert (Hdl:=H).
        eapply H1 with (panons:=panons) (Hi1:=Env.restrict Hi1 (map fst (vars++vars'++panons++local_anon_in_block a))) (Hi2:=Hi2)
          in H as (Hi3&Href1&Hdom1&Hsc1&Hnsub1&Hsem1)... clear H1.
        2:{ intros ? Hinm. eapply Hdisj.
            rewrite InMembers_app in *. destruct Hinm as [|]; eauto. }
        2:{ intros ??? Hfind Hv. eapply sem_var_restrict_inv in Hv as (?&?).
            eapply Hsub... }
        2:{ intros ?? Hnin Hv. eapply sem_var_restrict_inv in Hv as (?&?).
            eapply Hnsub... }
        2:{ clear - Hnd1. solve_NoDupMembers_app. }
        2:{ clear - H3. eapply NoDupLocals_incl; [|eauto]. solve_incl_app. }
        2:{ clear - Hatgen. eapply Forall_incl; [eauto|]. solve_incl_app. }
        2:{ eapply Env.dom_lb_restrict_dom_lb, Env.dom_lb_incl; eauto. 2:solve_incl_app.
            eapply incl_map, incl_appr, incl_appr, incl_appr, incl_refl. }
        2:{ eapply Env.restrict_dom_ub. }
        2:{ rewrite app_assoc, map_app, <-map_fst_idck. eapply sem_block_restrict...
            solve_incl_app. }
        assert (map fst (flat_map anon_in_block x) = map fst (anon_in_block a)) as Hanon.
        { eapply inlinelocal_block_anon; eauto.
          - intros ? Hanon. rewrite Hsubin. eapply Hdisj.
            rewrite InMembers_app; auto.
          - eapply NoDupLocals_incl; [|eauto]. solve_incl_app.
        }
        eapply IHblks with (panons:=panons++flat_map anon_in_block x) (Hi1:=Hi1) (Hi2:=Hi3)
          in H0 as (Hi4&Href3&Hdom3&Hsc3&Hnsub3&Hsem3)... clear IHblks H2.
        3:intros; eauto using sem_var_refines.
        10:{ eapply inlinelocal_block_st_valid_after; eauto. }
        3-9:repeat rewrite <-app_assoc in *; auto.
        2:{ intros ? Hinm. eapply Hdisj.
            rewrite InMembers_app in *. destruct Hinm; eauto. }
        2:{ intros ??. rewrite InMembers_app. intros [|[|Hinm]] ?.
            1,2:eapply sem_var_refines; eauto.
            eapply Hnsub1; eauto. eapply sem_var_restrict; [|eauto].
            rewrite fst_InMembers, Hanon in Hinm. repeat rewrite map_app, in_app_iff...
            repeat right. eapply sem_var_In, Env.dom_ub_use in H; [|eauto].
            rewrite (Permutation_app_comm (anon_in_block _)) in Hnd1. repeat rewrite app_assoc in Hnd1.
            repeat rewrite map_app, in_app_iff in H.
            eapply NoDupMembers_app_InMembers_l in Hnd1; eauto. repeat rewrite InMembers_app in Hnd1.
            destruct H as [|[|[|[|]]]]; auto; exfalso; eapply Hnd1...
        }
        2:{ clear - Hanon Hnd1. rewrite fst_NoDupMembers, 4 map_app, Hanon, <-4 map_app, <-fst_NoDupMembers.
            assumption. }
        2:{ clear - Hanon H4.
            repeat rewrite map_app in *. repeat rewrite <-app_assoc in *. rewrite Hanon.
            assumption. }
        2:{ simpl_app. rewrite Hanon. assumption. }
        2:{ eapply Env.dom_lb_incl; eauto. solve_incl_app. }
        2:{ clear - Hub Hanon.
            repeat rewrite map_app in *.  rewrite Hanon.
            eapply Env.dom_ub_incl; eauto.
            apply incl_appr', incl_appr', incl_appr', incl_appl', incl_map; auto. }
        exists Hi4. repeat (split; auto).
        + etransitivity...
        + rewrite <-flat_map_app. rewrite <-app_assoc in *...
        + rewrite <-flat_map_app. rewrite <-app_assoc in *...
        + intros ??. rewrite <-flat_map_app, InMembers_app. intros [Hinm|?] ?; auto.
          eapply sem_var_refines; [eauto|]. eapply Hnsub1; eauto.
          eapply sem_var_restrict; [|eauto].
          rewrite fst_InMembers, Hanon in Hinm. repeat rewrite map_app, in_app_iff...
            repeat right. eapply sem_var_In, Env.dom_ub_use in H; [|eauto].
            rewrite (Permutation_app_comm (anon_in_block _)) in Hnd1. repeat rewrite app_assoc in Hnd1.
            repeat rewrite map_app, in_app_iff in H.
            eapply NoDupMembers_app_InMembers_l in Hnd1; eauto. repeat rewrite InMembers_app in Hnd1.
            destruct H as [|[|[|[|]]]]; auto; exfalso; eapply Hnd1...
        + apply Forall_app; split; auto.
          eapply Forall_impl; [|eauto]; intros...
    Qed.

    Lemma inlinelocal_block_sem vars : forall blk sub vars' panons blks' st st' bs Hi1 Hi2,
        (forall x, InMembers x vars \/ InMembers x (anon_in_block blk) -> ~InMembers x vars') ->
        (forall x, Env.In x sub <-> InMembers x vars') ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 x vs -> sem_var Hi2 y vs) ->
        (forall x vs, InMembers x vars \/ InMembers x panons -> sem_var Hi1 x vs -> sem_var Hi2 x vs) ->
        (forall x y, Env.MapsTo x y sub -> exists n, y = gensym local (Some x) n) ->
        NoDupMembers (vars++vars'++panons++anon_in_block blk) ->
        NoDupLocals (map fst (vars++vars'++panons++anon_in_block blk)) blk ->
        Forall (AtomOrGensym elab_prefs) (map fst (vars++panons++anon_in_block blk)) ->
        GoodLocals elab_prefs blk ->
        wc_env (idck (vars++vars')) ->
        wc_block G1 (idck (vars++vars')) blk ->
        Env.dom_lb Hi1 (map fst (local_anon_in_block blk)) ->
        Env.dom_ub Hi1 (map fst (vars++vars'++panons++local_anon_in_block blk)) ->
        sem_block_ck G1 Hi1 bs blk ->
        (* sc_vars (idck (local_anon_in_block blk)) Hi1 bs -> *)
        Env.dom Hi2 (map fst (vars++panons) ++ st_ids st) ->
        sc_vars (idck (vars++panons++st_anns st)) Hi2 bs ->
        (* hist_st (idck (vars++local_anon_in_block blk)) bs Hi2 st -> *)
        st_valid_after st local PS.empty ->
        inlinelocal_block sub blk st = (blks', st') ->
        exists Hi3,
          Env.refines (@EqSt _) Hi2 Hi3 /\
          Env.dom Hi3 (map fst (vars++panons++flat_map anon_in_block blks')++st_ids st') /\
          sc_vars (idck (vars++panons++flat_map anon_in_block blks'++st_anns st')) Hi3 bs /\
          (forall x vs, InMembers x (flat_map anon_in_block blks') -> sem_var Hi1 x vs -> sem_var Hi3 x vs) /\
          Forall (sem_block_ck G2 Hi3 bs) blks'.
    Proof with eauto.
      induction blk using block_ind2;
        intros * Hdisj Hsubin Hsub Hnsub Hsubgensym Hnd1 Hnd2 Hgenat Hgood Hwenv Hwc Hlb Hub Hsem Hdom Hsc Hvalid Hdl;
        inv Hnd2; inv Hgood; inv Hwc; inv Hsem; repeat inv_bind; simpl.
      - (* equation *)
        assert (forall x, Env.In x (Env.restrict Hi1 (map fst (anon_in_eq eq))) -> ~ Env.In x Hi2) as Hdisj2.
        { intros * Hin1. erewrite Env.dom_use; [|eauto]. intros Hin2.
          eapply Env.restrict_In in Hin1. apply in_app_iff in Hin2 as [Hin2|Hin2].
          - repeat rewrite app_assoc in Hnd1. eapply NoDupMembers_app_InMembers_l in Hnd1; eauto.
            eapply Hnd1. eapply InMembers_incl; [|eauto]. solve_incl_app.
          - eapply st_valid_after_AtomOrGensym_nIn in Hin2; eauto using local_not_in_elab_prefs.
            eapply Forall_forall in Hgenat; eauto. repeat rewrite map_app, in_app_iff; auto. }
        assert (forall x vs, Env.find x sub = None -> sem_var Hi1 x vs ->
                        sem_var (Env.union (Env.restrict Hi1 (map fst (anon_in_eq eq))) Hi2) x vs) as Hsubin'.
        { intros * Hnone Hv. eapply sem_var_disj_union; eauto.
          assert (Hin:=Hv). eapply sem_var_In, Env.dom_ub_use in Hin; [|eauto].
          repeat rewrite map_app, in_app_iff in Hin.
          destruct Hin as [|[|[|]]]; eauto.
          - exfalso. eapply Env.Props.P.F.not_find_in_iff in Hnone. eapply Hnone, Hsubin; eauto.
          - left. eapply sem_var_restrict; eauto. }
        assert (map fst (anon_in_eq (rename_in_equation sub eq)) = map fst (anon_in_eq eq)) as Hanon.
        { rewrite rename_in_equation_anon_in, not_in_sub_same; auto.
          intros; rewrite Hsubin... }
        exists (Env.union (Env.restrict Hi1 (map fst (anon_in_eq eq))) Hi2).
        repeat split; auto; try rewrite app_nil_r.
        + eapply Env.union_refines4'; eauto.
        + rewrite app_assoc, (Permutation_app_comm _ (anon_in_eq _)), map_app, <-app_assoc.
          eapply Env.union_dom; eauto. rewrite Hanon.
          eapply Env.dom_lb_restrict_dom, Env.dom_lb_incl; eauto. reflexivity.
        + unfold sc_vars in *. repeat rewrite idck_app, Forall_app in *.
          destruct Hsc as (Hsc1&Hsc2&Hsc3).
          repeat split; eauto.
          1,2,4:eapply sc_vars_refines; [|eauto]; eauto using Env.union_refines4'.
          rewrite rename_in_equation_anon_in.
          eapply rename_in_sc_vars, sc_vars_anon_in_eq; [| |eauto]...
          * intros * Hfind Hv. eapply sem_var_refines; [|eauto]; eauto using Env.union_refines4'.
        + intros * Hinm Hv. eapply sem_var_disj_union; eauto.
          left. eapply sem_var_restrict; eauto.
          rewrite fst_InMembers, Hanon in Hinm...
        + repeat constructor.
          eapply rename_in_equation_sem; [| |eauto using sem_ref_sem_equation]...
          intros. eapply sem_var_refines; [|eauto]; eauto using Env.union_refines4'.
      - (* reset *)
        rename x into blks'.
        assert (forall x1, Env.In x1 (Env.restrict Hi1 (map fst (fresh_in er))) -> ~ Env.In x1 Hi2) as Hdisj2.
        { intros * Hin1. erewrite Env.dom_use; [|eauto]. intros Hin2.
          eapply Env.restrict_In in Hin1. apply in_app_iff in Hin2 as [Hin2|Hin2].
          - repeat rewrite app_assoc in Hnd1. eapply NoDupMembers_app_InMembers_l in Hnd1; eauto.
            eapply Hnd1. eapply InMembers_incl; [|eauto]. solve_incl_app.
          - eapply st_valid_after_AtomOrGensym_nIn in Hin2; eauto using local_not_in_elab_prefs.
            eapply Forall_forall in Hgenat; eauto. repeat rewrite map_app, in_app_iff; auto. }
        assert (map fst (fresh_in (rename_in_exp sub er)) = map fst (fresh_in er)) as Hanon1.
        { rewrite rename_in_exp_fresh_in, not_in_sub_same; auto.
          intros; rewrite Hsubin... eapply Hdisj. rewrite InMembers_app... }
        remember (Env.union (Env.restrict Hi1 (map fst (fresh_in er))) Hi2) as Hi3.
        assert (forall k, exists Hi4, Env.refines (@EqSt _) (mask_hist k r Hi3) (mask_hist k r Hi4) /\
                            Env.dom (mask_hist k r Hi4) (map fst (vars++panons++flat_map anon_in_block (concat blks')++fresh_in (rename_in_exp sub er))++st_ids st') /\
                            sc_vars (idck (vars++panons++flat_map anon_in_block (concat blks')++fresh_in (rename_in_exp sub er)++st_anns st')) (mask_hist k r Hi4) (maskb k r bs) /\
                            (forall x vs, InMembers x (flat_map anon_in_block (concat blks')++fresh_in (rename_in_exp sub er)) -> sem_var (mask_hist k r Hi1) x vs -> sem_var (mask_hist k r Hi4) x vs) /\
                            Forall (sem_block_ck G2 (mask_hist k r Hi4) (maskb k r bs)) (concat blks')) as Hblks.
        { intros k. specialize (H12 k).
          eapply mmap_inlinelocal_block_sem
            with (panons:=panons++fresh_in (rename_in_exp sub er)) (Hi2:=mask_hist k r Hi3) in H12
            as (Hi4&Href1&Hdom1&Hsc1&Hnsub1&Hsem1); eauto.
          2:{ intros ? Hinm. eapply Hdisj.
              rewrite InMembers_app in *. destruct Hinm; auto. }
          2:{ intros ??? Hfind Hv.
              eapply sem_var_mask_inv in Hv as (?&Hv&Hmask).
              rewrite Hmask. eapply sem_var_mask... subst.
              eapply sem_var_refines; [|eauto]. eapply Env.union_refines4'; eauto. }
          2:{ intros ??. rewrite InMembers_app. intros Hin Hv.
              eapply sem_var_mask_inv in Hv as (?&Hv&Hmask).
              rewrite Hmask. eapply sem_var_mask...
              destruct Hin as [|[|Hin]]; auto. 1,2:eapply sem_var_refines; subst; [eapply Env.union_refines4'; eauto|eauto].
              subst. eapply sem_var_disj_union...
              left. eapply sem_var_restrict... rewrite fst_InMembers, Hanon1 in Hin...
          }
          2:{ rewrite fst_NoDupMembers. simpl_app. rewrite Hanon1.
              repeat rewrite <-map_app. now rewrite <-fst_NoDupMembers, (Permutation_app_comm (fresh_in er)). }
          2:{ simpl_app. rewrite Hanon1.
              eapply Forall_impl; [|eapply H2]; intros. eapply NoDupLocals_Permutation_Proper. 2,3:eauto.
              solve_Permutation_app. }
          2:{ simpl_app. rewrite Hanon1.
              eapply Permutation_Forall; [|eauto]. solve_Permutation_app. }
          2:{ setoid_rewrite <-Env.dom_lb_map; eauto. eapply Env.dom_lb_incl; [|eauto]. solve_incl_app. }
          2:{ setoid_rewrite Env.dom_ub_map; eauto. simpl_app. rewrite Hanon1.
              eapply Env.dom_ub_incl; [|eauto]. eapply Permutation_incl1; [|reflexivity]. solve_Permutation_app. }
          2:{ eapply Env.dom_map. simpl_app. rewrite Hanon1. subst.
              rewrite 2 app_assoc, (Permutation_app_comm _ (map fst (fresh_in _))), <-2 app_assoc.
              eapply Env.union_dom; eauto.
              eapply Env.dom_lb_restrict_dom, Env.dom_lb_incl; [|eauto]. solve_incl_app.
          }
          2:{ eapply sc_vars_mask; eauto; subst.
              unfold sc_vars in *. repeat rewrite idck_app, Forall_app in *.
              destruct Hsc as (Hsc1&Hsc2&Hsc3).
              repeat split; eauto.
              1,2,4:eapply sc_vars_refines; [|eauto]; eauto using Env.union_refines4'.
              rewrite rename_in_exp_fresh_in.
              eapply rename_in_sc_vars, sc_vars_fresh_in with (H3:=Env.restrict Hi1 (map fst (vars++vars'++fresh_in er))).
              - intros * Hfind Hv. eapply sem_var_restrict_inv in Hv as (?&Hv).
                eapply sem_var_refines; [|eauto]; eauto using Env.union_refines4'.
              - intros * Hfind Hv. eapply sem_var_restrict_inv in Hv as (Hin&Hv).
                eapply sem_var_disj_union; eauto.
                repeat rewrite map_app, in_app_iff in Hin. destruct Hin as [Hin|[Hin|Hin]]...
                + exfalso. eapply Env.Props.P.F.not_find_in_iff...
                  rewrite Hsubin...
                + left. eapply sem_var_restrict...
              - rewrite app_assoc, map_app, <-map_fst_idck, idck_app. eapply sem_exp_restrict...
                reflexivity.
          }
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
          + intros * Hinm Hv. rewrite <-Heqmask. apply InMembers_app in Hinm as [Hinm|Hinm]...
            eapply sem_var_refines; [eauto|].
            eapply sem_var_mask_inv in Hv as (?&Hv&Hmask).
            rewrite Hmask. eapply sem_var_mask...
            subst. eapply sem_var_disj_union...
            left. eapply sem_var_restrict... rewrite fst_InMembers, Hanon1 in Hinm...
          + eapply Forall_impl; [|eauto]; intros. rewrite <-Heqmask...
        }
        eapply consolidate_mask_hist
          with (P := fun k H'k =>
                       Env.refines (@EqSt _) (mask_hist k r Hi3) H'k /\
                       Env.dom H'k (map fst (vars++panons++flat_map anon_in_block (concat blks')++fresh_in (rename_in_exp sub er))++st_ids st') /\
                       sc_vars (idck (vars++panons++flat_map anon_in_block (concat blks')++fresh_in (rename_in_exp sub er)++st_anns st')) H'k (maskb k r bs) /\
                       (forall x vs, InMembers x (flat_map anon_in_block (concat blks')++fresh_in (rename_in_exp sub er)) -> sem_var (mask_hist k r Hi1) x vs -> sem_var H'k x vs) /\
                       Forall (sem_block_ck G2 H'k (maskb k r bs)) (concat blks'))
        in Hblks as (Hi4&HHi4).
        2:{ intros ????? Heq (?&?&?&?&?); subst. repeat (split; auto).
            1-4:intros; rewrite <-Heq; auto.
            eapply Forall_impl; [|eauto]; intros.
            rewrite <-Heq...
        }
        2:{ intros ????? (_&Hdom1&_) (_&Hdom2&_) Hdom'.
            eapply Env.dom_intro; intros.
            eapply Env.dom_use in Hdom1. eapply Env.dom_use in Hdom2. eapply Env.dom_use in Hdom'.
            rewrite Hdom2, <-Hdom1...
        }
        assert (Env.refines (@EqSt _) Hi3 Hi4) as Href1.
        { eapply refines_unmask; intros. eapply HHi4. }
        assert (Env.refines (@EqSt _) Hi2 Hi4) as Href2.
        { etransitivity... subst. eapply Env.union_refines4'... }
        exists Hi4. repeat split; try rewrite app_nil_r; repeat rewrite <-app_assoc...
        + erewrite <-Env.dom_map. eapply (HHi4 0)...
        + eapply sc_vars_unmask. intros k. eapply (HHi4 k)...
        + intros * Hinm Hv. eapply sem_var_unmask; intros.
          eapply HHi4, sem_var_mask...
        + do 2 (econstructor; eauto using sem_exp_refines).
          *{ subst. eapply rename_in_exp_sem; [| |eauto using sem_ref_sem_exp].
             - intros. eapply sem_var_refines...
             - intros * Hnone Hv.
               assert (Hin:=Hv). eapply sem_var_In, Env.dom_ub_use in Hin; [|eauto].
               repeat rewrite map_app, in_app_iff in Hin.
               destruct Hin as [|[|[|Hin]]]; eauto.
               + eapply sem_var_refines...
               + exfalso. eapply Env.Props.P.F.not_find_in_iff in Hnone. eapply Hnone, Hsubin; eauto.
               + eapply sem_var_refines...
               + eapply sem_var_unmask; intros. eapply sem_var_mask in Hv.
                 eapply HHi4... rewrite InMembers_app, 2 fst_InMembers, Hanon1. destruct Hin...
                 erewrite mmap_inlinelocal_block_anon; eauto.
                 * intros. rewrite Hsubin. eapply Hdisj. rewrite InMembers_app...
                 * eapply Forall_impl; [|eapply H2]; intros.
                   eapply NoDupLocals_incl; [|eauto]. solve_incl_app.
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
        assert (forall x : Env.key, Env.In x sub -> ~Env.In x x0) as Hsub1.
        { intros ?. rewrite Hsubin, Hsubin'. intros Hin1 Hin2.
          eapply H5... repeat rewrite map_app, in_app_iff... }
        assert (NoDupMembers (map_filter (fun '(x4, vs0) => option_map (fun y0 : ident => (y0, vs0)) (Env.find x4 x0)) (Env.elements H'))) as HndH'.
        { eapply NoDupMembers_sub; eauto using Env.NoDupMembers_elements.
          eapply fresh_idents_rename_sub_NoDup; [|eauto].
          erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers, NoDupMembers_idty; auto.
          intros (?&?&?); auto. }
        assert (forall x, InMembers x (map_filter (fun '(x, vs) => option_map (fun y => (y, vs)) (Env.find x x0)) (Env.elements H')) ->
                     ~ Env.In x Hi2) as Hdisj2.
        { intros ? Hinm Henvin. eapply InMembers_sub in Hinm as (?&Hfind).
          assert (Hfind':=Hfind). eapply fresh_idents_rename_sub_gensym in Hfind as (?&?); eauto; subst.
          eapply Env.dom_use in Henvin; eauto. repeat rewrite map_app, in_app_iff in Henvin.
          destruct Henvin as [Hin1|Hin1].
          - eapply Forall_incl, Forall_forall in Hgenat; eauto. 2:solve_incl_app.
            eapply contradict_AtomOrGensym in Hgenat; eauto using local_not_in_elab_prefs.
          - eapply fresh_idents_rename_sub_nIn in Hin1; eauto.
        }
        eapply mmap_inlinelocal_block_sem
          with (vars:=vars) (vars':=vars'++idty locs) (sub:=Env.union _ _) (st:=x1)
               (Hi1:=H')
               (Hi2:=
                  (Env.adds'
                     (map_filter (fun '(x, vs) => option_map (fun y => (y, vs)) (Env.find x x0)) (Env.elements H'))
                     Hi2)) in H
          as (Hi3&Href1&Hdom1&Hsc1&Hnsub1&Hsem1)...
        + exists Hi3. repeat (split; auto).
          * etransitivity...
            intros ?? Hfind. eexists; split; try reflexivity.
            erewrite Env.gsso'; eauto. intros contra.
            eapply Hdisj2... econstructor...
          * intros * Hin Hv. eapply Hnsub1...
            eapply sem_var_refines; [|eauto]. eapply local_hist_dom_ub_refines...
            intros ?. rewrite app_nil_r.
            intros [Hinm1|Hinm1] Hin2...
            -- eapply H5... eapply incl_map... solve_incl_app.
            -- repeat rewrite app_assoc in Hnd1. eapply NoDupMembers_app_InMembers_l in Hnd1...
               eapply Hnd1. rewrite <-app_assoc...
        + intros ?. rewrite InMembers_app. intros Hinm1 [Hinm2|Hinm2].
          * eapply Hdisj; eauto.
          * eapply H5... repeat rewrite map_app, in_app_iff...
            destruct Hinm1...
        + intros ?. rewrite Env.union_In, Hsubin, Hsubin', InMembers_app.
          split; intros [?|?]...
        + intros ??? Hfind Hv.
          erewrite sem_var_disj_adds'; eauto.
          eapply Env.union_find4 in Hfind as [Hfind|Hfind].
          * right. eapply Hsub; eauto.
            eapply H10; eauto; eapply Env.find_In in Hfind; rewrite Hsubin in Hfind.
            -- intros contra. eapply H5... repeat rewrite map_app, in_app_iff...
            -- intros contra. repeat rewrite app_assoc in Hnd1. eapply NoDupMembers_app_InMembers in Hnd1.
               eapply Hnd1; eauto. repeat rewrite InMembers_app...
          * left. inv Hv. do 2 esplit; eauto.
            eapply map_filter_In. eapply Env.elements_correct; eauto.
            simpl. rewrite Hfind; auto.
        + intros ?? Hfind Hv.
          erewrite sem_var_disj_adds'; eauto. right.
          eapply Hnsub, H10; eauto; intro Hinm2.
          * eapply H5... repeat rewrite map_app, in_app_iff. destruct Hfind...
          * repeat rewrite app_assoc in Hnd1. eapply NoDupMembers_app_InMembers in Hnd1.
            eapply Hnd1; eauto. repeat rewrite InMembers_app. destruct Hfind...
        + intros ?? Hfind.
          eapply Env.union_find4 in Hfind as [Hfind|Hfind]...
          eapply fresh_idents_rename_sub_gensym...
        + clear - Hnd1 H5 H4. rewrite <-app_assoc, (Permutation_app_comm (idty locs)).
          repeat rewrite app_assoc in *. eapply NoDupMembers_app; eauto.
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
        + eapply Env.dom_lb_incl, Env.dom_dom_lb; [|eauto]. solve_incl_app.
        + eapply local_hist_dom_ub in H11; eauto.
          eapply Env.dom_ub_incl; [|eauto].
          simpl_app. rewrite map_fst_idty; simpl.
          eapply Permutation_incl1; [|reflexivity]. solve_Permutation_app.
        +{ eapply Env.dom_intro. intros.
           rewrite Env.In_adds_spec', InMembers_sub_iff.
           unfold st_ids. erewrite fresh_idents_rename_anns; eauto. setoid_rewrite <-Env.In_Members.
           repeat setoid_rewrite Env.dom_use; eauto. simpl_app.
           repeat rewrite in_app_iff.
           split; [intros [(?&Hin&Hmaps)|[|[|]]]|intros [|[|[Hin|Hin]]]]...
           - repeat rewrite in_app_iff in Hin. destruct Hin as [Hin|[Hin|Hin]].
             + exfalso. eapply fst_InMembers, Env.In_Members, Env.dom_ub_use in Hin...
               eapply Env.find_In, Hsubin' in Hmaps.
               eapply H5... rewrite app_nil_r in Hin. repeat rewrite in_app_iff in *. destruct Hin as [|[|]]...
             + do 2 right; left.
               eapply fresh_idents_rename_ids in H0; eauto; subst.
               2:erewrite fst_NoDupMembers, map_map, map_ext, map_fst_idty, <-fst_NoDupMembers; simpl; auto; intros (?&?&?); auto.
               eapply fst_InMembers, InMembers_In in Hin as (((?&?)&?)&Hin).
               unfold idty. repeat rewrite map_map.
               eapply in_map_iff. do 2 esplit; eauto. simpl. now rewrite Hmaps.
             + exfalso. eapply Env.find_In, Hsubin' in Hmaps.
               eapply H5... repeat rewrite in_app_iff. repeat right.
               eapply incl_map...
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
           unfold sc_vars in *. repeat rewrite Forall_app in Hsc. destruct Hsc as (Hsc1&Hsc2&Hsc3).
           repeat rewrite Forall_app. repeat split; eauto.
           1,2,4:eapply sc_vars_refines...
           eapply fresh_idents_rename_ids in H0.
           2:erewrite fst_NoDupMembers, map_map, map_ext, map_fst_idty, <-fst_NoDupMembers; auto;
             intros (?&?&?); auto.
           eapply sc_vars_restrict in H14; eauto. 2:solve_incl_app.
           unfold idty, idck in *. rewrite H0, 3 map_map, Forall_map; simpl.
           unfold sc_vars in H14. repeat rewrite map_app in H14. repeat rewrite map_map in H14. simpl in H14. rewrite Forall_map in H14.
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
               * intros contra. eapply H5... repeat rewrite map_app, in_app_iff...
               * intros contra. repeat rewrite app_assoc in Hnd1. eapply NoDupMembers_app_InMembers in Hnd1.
                 eapply Hnd1; eauto. repeat rewrite InMembers_app...
             + intros * Hfree Hfind Hv. eapply sem_var_restrict_inv in Hv as (Hin'&Hv). eapply sem_var_disj_union...
               1:intros * Henv; eapply Env.restrict_In in Henv...
               repeat rewrite in_app_iff in Hin'. destruct Hin' as [[Hin'|Hin']|Hin']; rewrite <-fst_InMembers in Hin'.
               * right. eapply Hnsub, H10...
                 -- intros contra. eapply H5... repeat rewrite map_app, in_app_iff...
                 -- intros contra. repeat rewrite app_assoc in Hnd1. eapply NoDupMembers_app_InMembers in Hnd1.
                    eapply Hnd1; eauto. repeat rewrite InMembers_app...
               * exfalso. eapply Env.Props.P.F.not_find_in_iff... rewrite Hsubin...
               * left. eapply sem_var_restrict; eauto.
         }
        + eapply fresh_idents_rename_st_valid; eauto.
    Qed.

    Lemma inlinelocal_topblock_sem vars : forall blk blks' locs' st st' bs Hi1 Hi2,
        (forall x vs, InMembers x vars -> sem_var Hi1 x vs -> sem_var Hi2 x vs) ->
        NoDupMembers (vars++anon_in_block blk) ->
        NoDupLocals (map fst (vars++anon_in_block blk)) blk ->
        Forall (AtomOrGensym elab_prefs) (map fst (vars++anon_in_block blk)) ->
        GoodLocals elab_prefs blk ->
        wc_env (idck (vars)) ->
        wc_block G1 (idck vars) blk ->
        Env.dom Hi1 (map fst (vars++local_anon_in_block blk)) ->
        sem_block_ck G1 Hi1 bs blk ->
        Env.dom Hi2 (map fst vars ++ st_ids st) ->
        sc_vars (idck (vars++st_anns st)) Hi2 bs ->
        st_valid_after st local PS.empty ->
        inlinelocal_topblock blk st = (blks', locs', st') ->
        exists Hi3,
          Env.refines (@EqSt _) Hi2 Hi3 /\
          Env.dom Hi3 (map fst (vars++flat_map anon_in_block blks'++idty locs')++st_ids st') /\
          sc_vars (idck (vars++flat_map anon_in_block blks'++idty locs'++st_anns st')) Hi3 bs /\
          Forall (sem_block_ck G2 Hi3 bs) blks'.
    Proof with eauto.
      Opaque inlinelocal_block.
      destruct blk; intros * Hinm Hnd1 Hnd2 Hatgen  Hgood Hwenv Hwc Hdom1 Hsem Hdom2 Hsc Hvalid Hil;
        repeat inv_bind; simpl in *.
      1,2:eapply inlinelocal_block_sem with (panons:=[]) (Hi1:=Hi1) in H as (Hi3&?&Hdom3&Hsc3&_&?);
        repeat rewrite app_nil_r in *; eauto; simpl in *.
      13:inv Hnd2; inv Hgood; inv Hwc; inv Hsem.
      13:assert (forall x, Env.In x (Env.restrict H' (map fst locs')) -> ~ Env.In x Hi2) as Hdisj2.
      13:{ intros * Hin1 Hin2. eapply Env.restrict_In in Hin1.
           eapply Env.dom_use, in_app_iff in Hin2 as [Hin2|Hin2]...
           - eapply H5... rewrite map_app, in_app_iff...
           - eapply st_valid_after_AtomOrGensym_nIn in Hin2; eauto using local_not_in_elab_prefs.
             eapply Forall_forall in H3... }
      13:assert (Env.refines (EqSt (A:=svalue)) (Env.restrict H' (map fst (vars ++ (idty locs')))) (Env.union (Env.restrict H' (map fst locs')) Hi2)) as Href.
      13:{ intros ?? Hfind. eapply Env.restrict_find_inv in Hfind as (Hin&Hfind).
           rewrite map_app, map_fst_idty, in_app_iff in Hin. destruct Hin as [Hin|Hin].
           - assert (sem_var H' x0 v) as Hv by (econstructor; eauto; reflexivity).
             eapply H10, Hinm in Hv; eauto. inv Hv.
             + do 2 esplit; eauto. eapply Env.union_find3'; eauto.
             + intros contra. eapply H5; eauto. rewrite map_app, in_app_iff...
             + intros contra. eapply NoDupMembers_app_InMembers in Hnd1...
           - do 2 esplit; try reflexivity.
             eapply Env.union_find2. eapply Env.restrict_find; eauto.
             eapply Env.Props.P.F.not_find_in_iff, Hdisj2, Env.restrict_In_iff; eauto.
             split; auto. econstructor; eauto. }
      13:eapply mmap_inlinelocal_block_sem
        with (panons:=[]) (vars:=vars++idty locs')
             (Hi1:=H')
             (Hi2:=Env.union (Env.restrict H' (map fst locs')) Hi2)
        in H as (Hi3&?&Hdom3&Hsc3&_&?);
        repeat rewrite app_nil_r in *; eauto; simpl in *.
      14:eapply Forall_forall; intros; eauto using inlinelocal_block_sem.
      1,7,14:intros *; rewrite Env.Props.P.F.empty_in_iff; split; intros [].
      1,3,6,8,12,14:intros * Hfind; eapply Env.Props.P.F.empty_mapsto_iff in Hfind as [].
      1,4:intros * [|[]]; auto.
      2,4:eapply Env.dom_dom_ub...
      1,2:eapply Env.dom_lb_incl, Env.dom_dom_lb; eauto; solve_incl_app.
      - exists Hi3. repeat split...
        + etransitivity; eauto using Env.union_refines4'.
        + clear - Hdom3. repeat rewrite map_app in *. repeat rewrite map_fst_idty in *.
          eapply Env.dom_Permutation; [|eauto]. solve_Permutation_app.
        + clear - Hsc3. repeat rewrite idck_app in *.
          eapply Permutation_Forall; [|eauto]. solve_Permutation_app.
      - intros * [Hinm1|[]] Hv.
        eapply sem_var_refines... eapply sem_var_restrict...
      - rewrite (Permutation_app_comm vars), <-app_assoc.
        apply NoDupMembers_app; auto.
        + apply NoDupMembers_idty; auto.
        + intros ? Hinm1 Hinm2. rewrite InMembers_idty in Hinm1.
          eapply H5...
      - eapply Forall_impl; [|eapply H2]; intros.
        eapply NoDupLocals_Permutation. 2,3:eauto.
        simpl_app. rewrite map_fst_idty. solve_Permutation_app.
      - rewrite (Permutation_app_comm vars), <-app_assoc, map_app, map_fst_idty.
        apply Forall_app; auto.
      - rewrite idck_app.
        apply Forall_app; split.
        + eapply Forall_impl; [|eapply Hwenv]; intros (?&?) ?.
          eapply wc_clock_incl; eauto; solve_incl_app.
        + rewrite Forall_map in H9.
          eapply Forall_impl; [|eapply H9]; intros (?&?) ?; eauto.
      - now rewrite idck_app.
      - eapply Env.dom_lb_incl, Env.dom_dom_lb; eauto. solve_incl_app.
      - rewrite 2 map_app, map_fst_idty, <-app_assoc.
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
               (Hi2:=Env.restrict H (map fst (n_in n0 ++ n_out n0)))
               (blks':=fst (fst (inlinelocal_topblock (n_block n0) init_st)))
               (locs':=snd (fst (inlinelocal_topblock (n_block n0) init_st)))
               (st':=snd (inlinelocal_topblock (n_block n0) init_st))
          in Hblksem as (Hf&Href&Hdom&Hsc&Hsem); eauto. 10:destruct inlinelocal_topblock as ((?&?)&?); reflexivity.
        eapply Snode with (H0:=Env.restrict H (map fst (n_in n0 ++ n_out n0))); simpl; eauto.
        + erewrite find_node_now; eauto.
        + simpl. eapply Forall2_impl_In; [|eauto]; intros.
          eapply sem_var_restrict... rewrite map_app...
        + simpl. eapply Forall2_impl_In; [|eauto]; intros.
          eapply sem_var_restrict... rewrite map_app...
        + apply sem_block_ck_cons'; simpl...
          2:{ eapply find_node_not_Is_node_in in Hord2.
            2:erewrite find_node_now; eauto. eauto. }
          destruct (inlinelocal_topblock _ _) as ((?&?)&?) eqn:Hil.
          econstructor. 4:destruct G2; eauto.
          * intros ?? Hv Hnin1 Hnin2.
            eapply sem_var_refines_iff. 1,4:eauto.
            eapply Env.dom_dom_lb, Env.dom_lb_restrict_dom, Env.dom_lb_incl, Env.dom_dom_lb...
            rewrite 2 map_app, map_fst_idty; solve_incl_app.
            eapply sem_var_In, Env.dom_use in Hv; [|eauto].
            rewrite map_app, map_fst_idty in Hv; simpl in Hv. rewrite (map_app _ _ (idty l0)) in Hv. repeat rewrite in_app_iff in Hv.
            destruct Hv as [[|[Hin|Hin]]|Hin]; auto. 1-3:exfalso.
            -- eapply Hnin2. rewrite nolocal_block_local_anons_idem; eauto using inlinelocal_topblock_nolocal.
            -- eapply Hnin1. rewrite InMembers_app; auto.
            -- eapply Hnin1. rewrite InMembers_app, 2 fst_InMembers, map_map; auto.
          * eapply local_hist_dom; eauto; simpl.
            eapply Env.dom_lb_restrict_dom, Env.dom_lb_incl, Env.dom_dom_lb...
            rewrite 2 map_app, map_fst_idty; solve_incl_app.
            rewrite 2 map_app, 2 map_fst_idty, <- app_assoc in Hdom. rewrite (map_app _ l0), map_map, <-app_assoc; simpl in *.
            rewrite nolocal_block_local_anons_idem; eauto using inlinelocal_topblock_nolocal.
            eapply Env.dom_Permutation; [|eauto]. apply Permutation_app_head.
            rewrite (Permutation_app_comm _ (map fst l0)), <-app_assoc. apply Permutation_app_head, Permutation_app_comm.
          * eapply Forall_incl; [eauto|].
            unfold idck, idty. repeat rewrite map_app. repeat rewrite map_map. repeat rewrite <-app_assoc. simpl.
            solve_incl_app.
        + simpl. constructor; simpl.
          * rewrite app_nil_r, map_fst_idty.
            eapply Env.dom_lb_restrict_dom, Env.dom_lb_incl, Env.dom_dom_lb; eauto.
            rewrite 2 map_app, map_fst_idty. solve_incl_app.
          * rewrite <-map_fst_idty, <-map_fst_idck. eapply sc_vars_restrict; eauto.
            -- reflexivity.
            -- destruct Hwc as (_&Hwc&_).
               eapply Forall_map, Forall_impl; [|eapply Hwc]; intros (?&?); auto.
        + intros * Hin Hv. rewrite InMembers_idty in Hin. eapply sem_var_restrict; eauto.
        + now rewrite map_app, map_fst_idty.
        + now rewrite map_app, map_fst_idty.
        + destruct Hwc as (?&?&?); auto.
        + destruct Hwc as (?&?&?), G1; auto.
        + unfold st_ids; rewrite init_st_anns, app_nil_r, map_fst_idty.
          eapply Env.dom_lb_restrict_dom, Env.dom_lb_incl, Env.dom_dom_lb; eauto.
          rewrite 2 map_app, map_fst_idty. solve_incl_app.
        + rewrite init_st_anns; simpl. rewrite app_nil_r.
          rewrite <-map_fst_idty, <-map_fst_idck. eapply sc_vars_restrict...
          * reflexivity.
          * destruct Hwc as (_&Hwc&_).
            eapply Forall_map, Forall_impl; [|eapply Hwc]; intros (?&?); auto.
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
       (LClockSem : LCLOCKSEMANTICS Ids Op OpAux Cks Syn Clo LCA Lord CStr Sem)
       (IL  : INLINELOCAL Ids Op OpAux Cks Syn)
       <: ILCORRECTNESS Ids Op OpAux Cks CStr Syn LCA Ty Clo Lord Sem LClockSem IL.
  Include ILCORRECTNESS Ids Op OpAux Cks CStr Syn LCA Ty Clo Lord Sem LClockSem IL.
End ILCorrectnessFun.
