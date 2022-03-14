From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LCausality Lustre.LSemantics Lustre.LClockSemantics.
From Velus Require Import Lustre.InlineLocal.InlineLocal Lustre.InlineLocal.ILTyping Lustre.InlineLocal.ILClocking.
From Velus Require Import Lustre.SubClock.SCCorrectness.

Module Type ILCORRECTNESS
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
       (Import IL  : INLINELOCAL Ids Op OpAux Cks Senv Syn).

  Module Import SCT := SCCorrectnessFun Ids Op OpAux Cks CStr Senv Syn Ty Cl LCA Ord Sem LCS SC. Import SC.

  Module Typing := ILTypingFun Ids Op OpAux Cks Senv Syn Ty IL.
  Module Clocking := ILClockingFun Ids Op OpAux Cks Senv Syn Cl IL.

  Fact mask_hist_sub sub : forall k r H H',
      (forall x y vs, Env.find x sub = Some y -> sem_var H x vs -> sem_var H' y vs) ->
      forall x y vs, Env.find x sub = Some y -> sem_var (CStr.mask_hist k r H) x vs -> sem_var (CStr.mask_hist k r H') y vs.
  Proof.
    intros * Hsub * Hfind Hv.
    eapply sem_var_mask_inv in Hv as (?&Hv&Heq).
    eapply Hsub, sem_var_mask in Hv; eauto. rewrite Heq; eauto.
  Qed.

  Fact mask_hist_nsub (sub : Env.t ident) : forall k r H H',
      (forall x vs, Env.find x sub = None -> sem_var H x vs -> sem_var H' x vs) ->
      forall x vs, Env.find x sub = None -> sem_var (CStr.mask_hist k r H) x vs -> sem_var (CStr.mask_hist k r H') x vs.
  Proof.
    intros * Hsub * Hfind Hv.
    eapply sem_var_mask_inv in Hv as (?&Hv&Heq).
    eapply Hsub, sem_var_mask in Hv; eauto. rewrite Heq; eauto.
  Qed.

  Import Fresh Facts Tactics.
  Import List.

  Section inlinelocal_node_sem.
    Variable G1 : @global noswitch_block switch_prefs.
    Variable G2 : @global nolocal_top_block local_prefs.

    Hypothesis HGref : global_sem_refines G1 G2.
    Hypothesis HwG1 : wc_global G1.

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
      induction xs as [|(?&?)]; inv Hnd1; simpl; auto with datatypes.
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

    Local Hint Resolve InMembers_incl : datatypes.
    Local Hint Resolve <- fst_InMembers InMembers_idck InMembers_idty : datatypes.
    Local Hint Resolve -> fst_InMembers InMembers_idck InMembers_idty : datatypes.

    Definition st_senv st := senv_of_tyck (st_anns st).

    Fact mmap_inlinelocal_block_sem : forall Γ blks sub Γ' blks' st st' bs Hi1 Hi2 Hl,
        Forall
          (fun blk => forall sub Γ' blks' st st' bs Hi1 Hi2 Hl,
               (forall x, ~IsLast (Γ++Γ') x) ->
               (forall x, InMembers x Γ -> ~InMembers x Γ') ->
               (forall x, Env.In x sub <-> InMembers x Γ') ->
               (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 x vs -> sem_var Hi2 y vs) ->
               (forall x vs, InMembers x Γ -> sem_var Hi1 x vs -> sem_var Hi2 x vs) ->
               (forall x y, Env.MapsTo x y sub -> exists n : ident, y = gensym local (Some x) n) ->
               NoDupMembers (Γ++Γ') ->
               noswitch_block blk ->
               NoDupLocals (map fst (Γ++Γ')) blk ->
               Forall (AtomOrGensym switch_prefs) (map fst Γ) ->
               GoodLocals switch_prefs blk ->
               wc_env (idck (Γ++Γ')) ->
               wc_block G1 (Γ++Γ') blk ->
               Env.dom_ub Hi1 (map fst (Γ++Γ')) ->
               sem_block_ck G1 (Hi1, Hl) bs blk ->
               Env.dom Hi2 (map fst Γ++st_ids st) ->
               sc_vars (Γ++st_senv st) (Hi2, Hl) bs ->
               st_valid_after st local PS.empty ->
               inlinelocal_block sub blk st = (blks', st') ->
               exists Hi3,
                 Env.refines (EqSt (A:=svalue)) Hi2 Hi3 /\
                 Env.dom Hi3 (map fst Γ++st_ids st') /\
                 sc_vars (Γ++st_senv st') (Hi3, Hl) bs /\
                 Forall (sem_block_ck G2 (Hi3, Hl) bs) blks')
          blks ->
        (forall x, ~IsLast (Γ++Γ') x) ->
        (forall x, InMembers x Γ -> ~InMembers x Γ') ->
        (forall x, Env.In x sub <-> InMembers x Γ') ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 x vs -> sem_var Hi2 y vs) ->
        (forall x vs, InMembers x Γ -> sem_var Hi1 x vs -> sem_var Hi2 x vs) ->
        (forall x y, Env.MapsTo x y sub -> exists n : ident, y = gensym local (Some x) n) ->
        NoDupMembers (Γ++Γ') ->
        Forall noswitch_block blks ->
        Forall (NoDupLocals (map fst (Γ++Γ'))) blks ->
        Forall (AtomOrGensym switch_prefs) (map fst Γ) ->
        Forall (GoodLocals switch_prefs) blks ->
        wc_env (idck (Γ++Γ')) ->
        Forall (wc_block G1 (Γ++Γ')) blks ->
        Env.dom_ub Hi1 (map fst (Γ++Γ')) ->
        Forall (sem_block_ck G1 (Hi1, Hl) bs) blks ->
        Env.dom Hi2 (map fst Γ++st_ids st) ->
        sc_vars (Γ++st_senv st) (Hi2, Hl) bs ->
        st_valid_after st local PS.empty ->
        mmap (inlinelocal_block sub) blks st = (blks', st') ->
        exists Hi3,
          Env.refines (EqSt (A:=svalue)) Hi2 Hi3 /\
          Env.dom Hi3 (map fst Γ++st_ids st') /\
          sc_vars (Γ++st_senv st') (Hi3, Hl) bs /\
          Forall (sem_block_ck G2 (Hi3, Hl) bs) (concat blks').
    Proof with eauto.
      induction blks;
        intros * Hf Hnl Hdisj Hsubin Hsub Hnsub Hsubgensym Hnd1 Hns Hnd2 Hatgen Hgood Hwenv Hwc Hub Hsem Hdom Hsc Hvalid Hmmap;
        inv Hf; inv Hns; inv Hnd2; inv Hgood; inv Hwc; inv Hsem; repeat inv_bind; simpl in *.
      - exists Hi2. repeat (split; auto with env).
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
          eapply Forall_impl; [|eauto]; intros; eauto using sem_block_refines.
    Qed.

    (** Central correctness lemma                                              *)
    (* - vars : not renamed (in + out of the node)
       - vars' : renamed (local vars already encountered)
       - Hi1 : history before renaming
       - Hi2 : history after renaming of the enclosing blocks
       - Hi3 : refines Hi2 by adding the renamed variables of the subblocks
     *)
    Lemma inlinelocal_block_sem Γ : forall blk sub Γ' blks' st st' bs Hi1 Hi2 Hl,
        (forall x, ~IsLast (Γ++Γ') x) ->
        (forall x, InMembers x Γ -> ~InMembers x Γ') ->
        (forall x, Env.In x sub <-> InMembers x Γ') ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 x vs -> sem_var Hi2 y vs) ->
        (forall x vs, InMembers x Γ -> sem_var Hi1 x vs -> sem_var Hi2 x vs) ->
        (forall x y, Env.MapsTo x y sub -> exists n, y = gensym local (Some x) n) ->
        NoDupMembers (Γ++Γ') ->
        noswitch_block blk ->
        NoDupLocals (map fst (Γ++Γ')) blk ->
        Forall (AtomOrGensym switch_prefs) (map fst Γ) ->
        GoodLocals switch_prefs blk ->
        wc_env (idck (Γ++Γ')) ->
        wc_block G1 (Γ++Γ') blk ->
        Env.dom_ub Hi1 (map fst (Γ++Γ')) ->
        sem_block_ck G1 (Hi1, Hl) bs blk ->
        Env.dom Hi2 (map fst Γ ++ st_ids st) ->
        sc_vars (Γ++st_senv st) (Hi2, Hl) bs ->
        st_valid_after st local PS.empty ->
        inlinelocal_block sub blk st = (blks', st') ->
        exists Hi3,
          Env.refines (@EqSt _) Hi2 Hi3 /\
          Env.dom Hi3 (map fst Γ++st_ids st') /\
          sc_vars (Γ++st_senv st') (Hi3, Hl) bs /\
          Forall (sem_block_ck G2 (Hi3, Hl) bs) blks'.
    Proof with eauto with datatypes.
      induction blk using block_ind2;
        intros * Hnl Hdisj Hsubin Hsub Hnsub Hsubgensym Hnd1 Hns Hnd2 Hgenat Hgood Hwenv Hwc Hub Hsem Hdom Hsc Hvalid Hdl;
        inv Hns; inv Hnd2; inv Hgood; inv Hwc; inv Hsem; repeat inv_bind; simpl.

      - (* equation *)
        exists Hi2. repeat (split; auto with env).
        constructor; auto. constructor.
        eapply subclock_equation_sem; eauto using sem_ref_sem_equation.
        + constructor; reflexivity.
        + intros * Hnone Hv.
          assert (Hin:=Hv). eapply sem_var_In, Env.dom_ub_use in Hin; [|eauto].
          repeat rewrite map_app, in_app_iff in Hin.
          destruct Hin as [|]...
          exfalso. eapply Env.Props.P.F.not_find_in_iff in Hnone. eapply Hnone, Hsubin...

      - (* reset *)
        rename x into blks'.
        assert (forall k, exists Hi4, Env.refines (@EqSt _) (CStr.mask_hist k r Hi2) (CStr.mask_hist k r Hi4) /\
                            Env.dom (CStr.mask_hist k r Hi4) (map fst Γ++st_ids st') /\
                            sc_vars (Γ++st_senv st') (mask_hist k r (Hi4, Hl)) (maskb k r bs) /\
                            Forall (sem_block_ck G2 (mask_hist k r (Hi4, Hl)) (maskb k r bs)) (concat blks')) as Hblks.
        { intros k. specialize (H13 k).
          eapply mmap_inlinelocal_block_sem with (Hi2:=CStr.mask_hist k r Hi2) in H13
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
          2:{ eapply sc_vars_mask in Hsc; eauto; subst. }
          assert (Env.Equiv (@EqSt _) Hi4 (CStr.mask_hist k r Hi4)) as Heqmask.
          { unfold st_ids in Hdom1.
            eapply slower_mask_hist. eapply sc_vars_slower_hist in Hsc1; eauto.
            simpl_app. setoid_rewrite map_fst_senv_of_tyck. auto.
          }
          exists Hi4. repeat split; auto.
          + rewrite <-Heqmask; auto.
          + rewrite <-Heqmask.
            eapply Env.dom_Permutation; [|eauto]. solve_Permutation_app.
          + intros. edestruct Hsc1 as ((?&Hv&Hck)&_); simpl in *; eauto.
            rewrite Heqmask in Hv, Hck; eauto.
          + intros * _ Hca. exfalso. apply IsLast_app in Hca as [Hca|Hca].
            * eapply Hnl, IsLast_app; eauto.
            * eapply senv_of_tyck_NoLast; eauto.
          + eapply Forall_impl; [|eauto]; intros. unfold mask_hist.
            eapply sem_block_ck_morph; eauto. 2:reflexivity.
            split; eauto. reflexivity.
        }
        unfold mask_hist.
        eapply consolidate_mask_hist
          with (P := fun k H'k =>
                       Env.refines (@EqSt _) (CStr.mask_hist k r Hi2) H'k /\
                       Env.dom H'k (map fst Γ++st_ids st') /\
                       sc_vars (Γ++st_senv st') (H'k, CStr.mask_hist k r Hl) (maskb k r bs) /\
                       Forall (sem_block_ck G2 (H'k, CStr.mask_hist k r Hl) (maskb k r bs)) (concat blks'))
        in Hblks as (Hi4&HHi4).
        2:{ intros ????? Heq (?&?&(?&?)&?); subst. repeat (split; auto).
            1-2:intros; rewrite <-Heq; auto.
            1,2:intros.
            - repeat setoid_rewrite Heq in H11; eauto.
            - repeat setoid_rewrite Heq in H14; eauto.
            - simpl_Forall.
              eapply sem_block_ck_morph; eauto. 2:reflexivity.
              split; eauto. reflexivity.
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
        + eapply sc_vars_unmask. intros k. eapply (HHi4 k)...
        + do 2 (econstructor; eauto).
          * eapply sem_exp_refines; [eauto|].
            eapply subclock_exp_sem; eauto using sem_ref_sem_exp.
            1:{ constructor; reflexivity. }
            { intros * Hnone Hv.
              assert (Hin:=Hv). eapply sem_var_In, Env.dom_ub_use in Hin; [|eauto].
              repeat rewrite map_app, in_app_iff in Hin.
              destruct Hin as [|]...
              exfalso. eapply Env.Props.P.F.not_find_in_iff in Hnone. eapply Hnone, Hsubin...
            }
          * intros. eapply HHi4...

      - (* local *)
        assert (forall x, Env.In x x0 <-> InMembers x locs) as Hsubin'.
        { intros. split; intros * Hin.
          - eapply fresh_idents_rename_sub1 in Hin; [|eauto].
            unfold idty in *. erewrite fst_InMembers, map_map, map_ext, <-fst_InMembers in Hin...
            intros; destruct_conjs...
          - eapply fresh_idents_rename_sub2 in H0.
            unfold idty in *. erewrite fst_InMembers, map_map, map_ext, <-fst_InMembers in H0...
            2:intros; destruct_conjs; auto.
            apply H0 in Hin as (?&?&?&_); eauto. econstructor...
        }
        assert (forall x, InMembers x (map_filter (fun '(x, vs) => option_map (fun y => (y, vs)) (Env.find x x0)) (Env.elements H')) ->
                     ~ Env.In x Hi2) as Hdisj2.
        { intros ? Hinm Henvin. eapply InMembers_sub in Hinm as (?&Hfind).
          assert (Hfind':=Hfind). eapply fresh_idents_rename_sub_gensym in Hfind as (?&?); eauto; subst.
          eapply Env.dom_use in Henvin; eauto. rewrite in_app_iff in Henvin.
          destruct Henvin as [Hin1|Hin1].
          - eapply Forall_incl, Forall_forall in Hgenat; eauto. 2:solve_incl_app.
            eapply contradict_AtomOrGensym in Hgenat; eauto using local_not_in_switch_prefs.
          - eapply fresh_idents_rename_sub_nIn in Hin1; eauto.
        }
        assert (forall x : Env.key, Env.In x sub -> ~Env.In x x0) as Hsub1.
        { intros ?. rewrite Hsubin, Hsubin'. intros Hin1 Hin2.
          eapply H7... }
        assert (NoDupMembers (map_filter (fun '(x4, vs0) => option_map (fun y0 : ident => (y0, vs0)) (Env.find x4 x0)) (Env.elements H'))) as HndH'.
        { eapply NoDupMembers_sub; eauto using Env.NoDupMembers_elements.
          eapply fresh_idents_rename_sub_NoDup; [|eauto].
          erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; auto.
          intros; destruct_conjs; auto. }
        assert (Forall nolocal_block (concat x2)) as Hnlo.
        { apply Forall_concat.
          apply mmap_values, Forall2_ignore1 in H1. simpl_Forall.
          apply inlinelocal_block_nolocal in H11; auto; simpl_Forall; auto. }
        assert (Forall (sem_block_ck G1 (H', Hl) bs) blocks) as Hsem.
        { simpl_Forall. eapply sem_block_change_lasts.
          1,3,4:eauto using noswitch_noauto, noauto_nolast with lclocking.
          rewrite NoLast_app; split; auto.
          intros * Hla; inv Hla; simpl_In; simpl_Forall. subst; simpl in *; congruence. }
        eapply mmap_inlinelocal_block_sem with
            (Γ':=Γ'++senv_of_locs locs) (Hi1:=H') (Hl:=Hl) (Hi2:=Env.adds' (map_filter (fun '(x, vs) => option_map (fun y => (y, vs)) (Env.find x x0)) (Env.elements H')) Hi2)
            (sub:=Env.union sub x0) (st:=x1)
          in H1 as (Hi3&Href1&Hdom1&(Hsc11&Hsc12)&Hsem1); eauto. clear H.
        + exists Hi3. repeat (split; eauto).
          etransitivity...
          intros ?? Hfind. eexists; split; try reflexivity.
          erewrite Env.gsso'; eauto. intros contra.
          eapply Hdisj2... econstructor...
        + rewrite app_assoc, NoLast_app; split; auto.
          intros * Hla; inv Hla; simpl_In; simpl_Forall. subst; simpl in *; congruence.
        + intros ?. rewrite InMembers_app. intros Hinm1 [Hinm2|Hinm2].
          * eapply Hdisj; eauto.
          * apply InMembers_senv_of_locs in Hinm2. eapply H7...
        + intros ?. rewrite Env.union_In, Hsubin, Hsubin', InMembers_app, InMembers_senv_of_locs.
          split; intros [?|?]...
        + intros ??? Hfind Hv.
          erewrite sem_var_disj_adds'; eauto.
          eapply Env.union_find4 in Hfind as [Hfind|Hfind].
          * right. eapply Hsub; eauto.
            eapply H15; eauto; eapply Env.find_In in Hfind; rewrite Hsubin in Hfind.
            intros contra. eapply H7...
          * left. inv Hv. do 2 esplit; eauto.
            eapply map_filter_In. eapply Env.elements_correct; eauto.
            simpl. rewrite Hfind; auto.
        + intros ?? Hfind Hv.
          erewrite sem_var_disj_adds'; eauto. right.
          eapply Hnsub, H15; eauto; intro Hinm2.
          eapply H7...
        + intros ?? Hfind.
          eapply Env.union_find4 in Hfind as [Hfind|Hfind]...
          eapply fresh_idents_rename_sub_gensym...
        + clear - Hnd1 H7 H6. rewrite app_assoc.
          eapply NoDupMembers_app; eauto.
          * rewrite NoDupMembers_senv_of_locs; auto.
          * intros ? Hinm Hinm2. rewrite InMembers_senv_of_locs in Hinm2.
            eapply H7...
        + clear - H4.
          rewrite app_assoc, map_app, map_fst_senv_of_locs; auto.
        + clear - Hwenv H12.
          unfold wc_env in *. simpl_app. rewrite app_assoc, Forall_app; split; simpl_Forall.
          * eapply wc_clock_incl; [|eauto]. solve_incl_app.
          * simpl_app; auto.
        + rewrite app_assoc; auto.
        + eapply local_hist_dom_ub in H16; eauto.
          rewrite app_assoc, map_app, map_fst_senv_of_locs; auto.
        +{ eapply Env.dom_intro. intros.
           rewrite Env.In_adds_spec', InMembers_sub_iff.
           unfold st_ids. erewrite fresh_idents_rename_anns; eauto. setoid_rewrite <-Env.In_Members.
           repeat setoid_rewrite Env.dom_use; eauto. simpl_app.
           repeat rewrite in_app_iff.
           split; [intros [(?&Hin&Hmaps)|[|]]|intros [|[Hin|Hin]]]...
           - repeat rewrite in_app_iff in Hin. destruct Hin as [Hin|Hin].
             + exfalso. eapply fst_InMembers, Env.In_Members, Env.dom_ub_use in Hin...
               eapply Env.find_In, Hsubin' in Hmaps.
               eapply H7...
             + right; left.
               eapply fresh_idents_rename_ids in H0; eauto; subst.
               2:erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; simpl; auto; intros; destruct_conjs; auto.
               solve_In. now rewrite Hmaps.
           - eapply fresh_idents_rename_ids in H0; eauto.
             2:erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; simpl; auto; intros; destruct_conjs; auto.
             rewrite H0, map_map, map_map in Hin. simpl_In.
             left. do 2 esplit...
             destruct (Env.find i x0) eqn:Hfind; simpl in *; subst; auto.
             exfalso. eapply Env.Props.P.F.not_find_in_iff in Hfind. rewrite Hsubin' in Hfind.
             eapply Hfind...
         }
        +{ assert (Env.refines (@EqSt _) Hi2 (Env.adds' (map_filter (fun '(x3, vs) => option_map (fun y : ident => (y, vs)) (Env.find x3 x0)) (Env.elements H')) Hi2)) as Href.
           { intros ?? Hfind. do 2 esplit; try reflexivity.
             erewrite Env.gsso'... intro contra.
             eapply Hdisj2... econstructor... }
           unfold st_senv. erewrite fresh_idents_rename_anns; eauto. split.
           2:{ intros * _ Hla. exfalso. apply IsLast_app in Hla as [Hla|Hla].
               - eapply Hnl, IsLast_app; eauto.
               - apply senv_of_tyck_NoLast in Hla; auto.
           }
           intros * Hck. eapply sc_vars_refines in Hsc. 2:eauto. 2:reflexivity. destruct Hsc as (Hsc1&_).
           unfold senv_of_tyck in Hck. simpl_app. rewrite Permutation_swap, HasClock_app in Hck.
           destruct Hck as [Hck|Hck]. 2:edestruct Hsc1 as (?&?&?); eauto.
           inv Hck. simpl_In.
           eapply fresh_idents_rename_ids in H0.
           2:(erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; auto;
              intros; destruct_conjs; auto).
           eapply sc_vars_restrict with (Γ:=Γ++Γ'++senv_of_locs locs) in H20 as (Hsc4&_); eauto.
           3:{ simpl_Forall. simpl_In. simpl_Forall. simpl_app. auto. }
           2:{ simpl_app. erewrite map_map, map_ext with (g:=fst) (l:=locs); eauto.
               apply incl_appr, incl_appr, incl_refl. intros; destruct_conjs; auto. }
           subst. simpl_In. edestruct Hsc4 as (vs&Hsv&Hsemck).
           1:{ econstructor; solve_In. auto. } simpl in *.
           exists vs; split.
           - eapply rename_var_sem; [| |eauto]...
             + intros * Hfind Hv. eapply sem_var_restrict_inv in Hv as (Hin'&Hv). eapply sem_var_disj_adds'...
               left. inv Hv. do 2 esplit; eauto.
               eapply map_filter_In; eauto using Env.elements_correct; simpl. now rewrite Hfind.
             + intros * Hfind Hv. eapply sem_var_restrict_inv in Hv as (Hin'&Hv). eapply sem_var_disj_adds'...
               repeat rewrite in_app_iff in Hin'.
               exfalso. rewrite <-Env.Props.P.F.not_find_in_iff, Hsubin' in Hfind...
           - assert (forall x, InMembers x locs -> ~ Env.In x Hi2) as Hdisj3.
             { intros ? Hinm Henv. eapply Env.dom_use in Henv; [|eauto].
               apply in_app_iff in Henv as [Hin'|Hin'].
               - eapply H7...
               - eapply st_valid_after_AtomOrGensym_nIn in Hin'; eauto using local_not_in_switch_prefs.
                 eapply Forall_forall in H5... }
             eapply subclock_clock_sem, subclock_clock_sem
               with (Hi':=Env.union (Env.restrict H' (map fst locs)) Hi2). 3,6:constructor; reflexivity. 5:eauto.
             + intros * Hfind Hv. eapply sem_var_union in Hv as [Hv|Hv]; eapply sem_var_disj_adds'...
               * eapply sem_var_restrict_inv in Hv as (Hin'&Hv).
                 left. inv Hv. do 2 esplit...
                 eapply map_filter_In; eauto using Env.elements_correct; simpl. now rewrite Hfind.
               * exfalso. eapply sem_var_In, Hdisj3 in Hv; auto.
                 eapply Hsubin', Env.find_In...
             + intros * Hfind Hv. eapply sem_var_union in Hv as [Hv|Hv]; eapply sem_var_disj_adds'...
               exfalso. eapply sem_var_restrict_inv in Hv as (Hin'&Hv).
               eapply Env.Props.P.F.not_find_in_iff... rewrite Hsubin'...
             + intros * Hfind Hv. eapply sem_var_restrict_inv in Hv as (Hin'&Hv). eapply sem_var_disj_union...
               1:intros * Henv; eapply Env.restrict_In in Henv...
               right. eapply Hsub; eauto. eapply H15; eauto; eapply Env.find_In in Hfind; rewrite Hsubin in Hfind.
               intros contra. eapply H7...
             + intros * Hfind Hv. eapply sem_var_restrict_inv in Hv as (Hin'&Hv). eapply sem_var_disj_union...
               1:intros * Henv; eapply Env.restrict_In in Henv...
               simpl_app. repeat rewrite in_app_iff in Hin'. destruct Hin' as [Hin'|[Hin'|Hin']]; rewrite <-fst_InMembers in Hin'.
               * right. eapply Hnsub, H15...
                 intros contra. eapply H7...
               * exfalso. eapply Env.Props.P.F.not_find_in_iff... rewrite Hsubin...
               * left. apply fst_InMembers in Hin'. eapply sem_var_restrict...
                 solve_In.
         }
        + eapply fresh_idents_rename_st_valid; eauto.
    Qed.

    Lemma inlinelocal_topblock_sem Γ : forall blk blks' locs' st st' bs Hi1 Hi2 Hl,
        (forall x, ~IsLast Γ x) ->
        (forall x vs, InMembers x Γ -> sem_var Hi1 x vs -> sem_var Hi2 x vs) ->
        NoDupMembers Γ ->
        noswitch_block blk ->
        NoDupLocals (map fst Γ) blk ->
        Forall (AtomOrGensym switch_prefs) (map fst Γ) ->
        GoodLocals switch_prefs blk ->
        wc_env (idck Γ) ->
        wc_block G1 Γ blk ->
        Env.dom Hi1 (map fst Γ) ->
        sem_block_ck G1 (Hi1, Hl) bs blk ->
        Env.dom Hi2 (map fst Γ ++ st_ids st) ->
        sc_vars (Γ++st_senv st) (Hi2, Hl) bs ->
        st_valid_after st local PS.empty ->
        inlinelocal_topblock blk st = (blks', locs', st') ->
        exists Hi3,
          Env.refines (@EqSt _) Hi2 Hi3 /\
          Env.dom Hi3 (map fst (Γ++senv_of_locs locs')++st_ids st') /\
          sc_vars (Γ++senv_of_locs locs'++st_senv st') (Hi3, Hl) bs /\
          Forall (sem_block_ck G2 (Hi3, Hl) bs) blks'.
    Proof with eauto with datatypes.
      Opaque inlinelocal_block.
      destruct blk; intros * Hnl Hinm Hnd1 Hns Hnd2 Hatgen Hgood Hwenv Hwc Hdom1 Hsem Hdom2 Hsc Hvalid Hil;
        repeat inv_bind; simpl in *.
      3:inv Hns.
      1-3:eapply inlinelocal_block_sem with (Hi1:=Hi1) in H as (Hi3&?&Hdom3&Hsc3&?);
        repeat rewrite app_nil_r in *; eauto; simpl in *.
      13:inv Hns; inv Hnd2; inv Hgood; inv Hwc; inv Hsem.
      13:assert (forall x, Env.In x (Env.restrict H' (map fst locs')) -> ~ Env.In x Hi2) as Hdisj2.
      13:{ intros * Hin1 Hin2. eapply Env.restrict_In in Hin1.
           eapply Env.dom_use, in_app_iff in Hin2 as [Hin2|Hin2]...
           - eapply H7...
           - eapply st_valid_after_AtomOrGensym_nIn in Hin2; eauto using local_not_in_switch_prefs.
             eapply Forall_forall in H5... }
      13:assert (Env.refines (EqSt (A:=svalue)) (Env.restrict H' (map fst (Γ ++ senv_of_locs locs'))) (Env.union (Env.restrict H' (map fst locs')) Hi2)) as Href.
      13:{ intros ?? Hfind. eapply Env.restrict_find_inv in Hfind as (Hin&Hfind).
           rewrite map_app, map_fst_senv_of_locs, in_app_iff in Hin. destruct Hin as [Hin|Hin].
           - assert (sem_var H' x0 v) as Hv by (econstructor; eauto; reflexivity).
             eapply H15, Hinm in Hv... inv Hv.
             + do 2 esplit; eauto. eapply Env.union_find3'; eauto.
             + intros contra. eapply H7; eauto.
           - do 2 esplit; try reflexivity.
             eapply Env.union_find2. eapply Env.restrict_find; eauto.
             eapply Env.Props.P.F.not_find_in_iff, Hdisj2, Env.restrict_In_iff; eauto.
             split; auto. econstructor; eauto. }
      13:eapply mmap_inlinelocal_block_sem
        with (Γ:=Γ++senv_of_locs locs')
             (Hi1:=H') (Hl:=Hl)
             (Hi2:=Env.union (Env.restrict H' (map fst locs')) Hi2)
        in H as (Hi3&?&Hdom3&Hsc3&?);
        repeat rewrite app_nil_r in *; eauto; simpl in *.
      14:eapply Forall_forall; intros; eauto using inlinelocal_block_sem.
      1,5,9,15:intros *; rewrite Env.Props.P.F.empty_in_iff; split; intros [].
      1,2,4,5,7,8,12,14:intros * Hfind; eapply Env.Props.P.F.empty_mapsto_iff in Hfind as [].
      1-3:eapply Env.dom_dom_ub...
      - exists Hi3. repeat split...
        + etransitivity; eauto using Env.union_refines4', EqStrel.
        + clear - Hsc3. destruct Hsc3 as (Hsc3&_). simpl_app; eauto.
        + clear - Hsc3. destruct Hsc3 as (_&Hsc3). simpl_app; eauto.
      - rewrite NoLast_app; split; auto.
        intros * Hla. inv Hla. simpl_In. simpl_Forall. subst; simpl in *; congruence.
      - intros * Hinm1 Hv.
        eapply sem_var_refines... eapply sem_var_restrict...
      - apply NoDupMembers_app; auto.
        + apply NoDupMembers_senv_of_locs; auto.
        + intros ? Hinm1 Hinm2. rewrite InMembers_senv_of_locs in Hinm2.
          eapply H7...
      - now rewrite map_app, map_fst_senv_of_locs.
      - rewrite map_app, map_fst_senv_of_locs.
        apply Forall_app; auto.
      - unfold wc_env in *. simpl_app.
        apply Forall_app; split; simpl_Forall; eauto.
        eapply wc_clock_incl; eauto; solve_incl_app.
      - rewrite map_app, map_fst_senv_of_locs.
        eapply Env.dom_dom_ub, local_hist_dom; eauto.
      - simpl_Forall. eapply sem_block_change_lasts.
        1,3,4:eauto using noswitch_noauto, noauto_nolast with lclocking.
        rewrite NoLast_app; split; auto.
        intros * Hla. inv Hla. simpl_In. simpl_Forall. subst; simpl in *; congruence.
      - rewrite (Permutation_app_comm Γ), map_app, map_fst_senv_of_locs, <-app_assoc.
        eapply Env.union_dom; eauto.
        eapply Env.dom_lb_restrict_dom, Env.dom_lb_incl, Env.dom_dom_lb; eauto. solve_incl_app.
      - split.
        2:{ intros * _ Hla. exfalso. repeat rewrite IsLast_app in Hla. destruct Hla as [[Hla|Hla]|Hla].
            - eapply Hnl; eauto.
            - inv Hla. simpl_In. simpl_Forall. subst; simpl in *; congruence.
            - eapply senv_of_tyck_NoLast; eauto.
        }
        intros * Hck. rewrite (Permutation_app_comm Γ), <-app_assoc, HasClock_app in Hck. destruct Hck as [Hck|Hck].
        + eapply sc_vars_restrict with (Γ:=Γ++senv_of_locs locs') in H20.
          3:{ simpl_Forall. simpl_app. simpl_In. simpl_Forall. eauto. }
          2:{ simpl_app. solve_incl_app. }
          edestruct H20 as ((?&?&?)&_); eauto using sem_var_refines, sem_clock_refines.
        + eapply sc_vars_refines in Hsc as (Hsc1&_); [eauto| |reflexivity].
          eapply Env.union_refines4'; eauto using EqStrel.
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
          with (Γ:=senv_of_inout (n_in n0 ++ n_out n0))
               (st:=init_st)
               (Hi2:=H)
               (blks':=fst (fst (inlinelocal_topblock (n_block n0) init_st)))
               (locs':=snd (fst (inlinelocal_topblock (n_block n0) init_st)))
               (st':=snd (inlinelocal_topblock (n_block n0) init_st))
          in Hblksem as (Hf&Href&Hdom&Hsc&Hsem); eauto. 12:destruct inlinelocal_topblock as ((?&?)&?); reflexivity.
        eapply Snode with (H:=H); simpl; eauto.
        + erewrite find_node_now; eauto.
        + eauto.
        + eauto.
        + apply sem_block_ck_cons'; simpl...
          2:{ eapply find_node_not_Is_node_in in Hord2.
            2:erewrite find_node_now; eauto. eauto. }
          destruct (inlinelocal_topblock _ _) as ((?&?)&?) eqn:Hil.
          econstructor. 6:destruct G2; eauto.
          * intros ?? Hv Hnin1.
            eapply sem_var_refines_iff. 1,4:eauto.
            eapply Env.dom_dom_lb...
            eapply sem_var_In, Env.dom_use in Hv; [|eauto].
            rewrite map_app in Hv; simpl in Hv. repeat rewrite in_app_iff in Hv.
            destruct Hv as [[Hin|Hin]|Hin]; auto. 1-2:exfalso.
            -- eapply Hnin1. simpl_In. rewrite InMembers_app; eauto using In_InMembers.
            -- eapply Hnin1. simpl_In. rewrite InMembers_app, 2 fst_InMembers; auto.
               right; solve_In.
          * eapply local_hist_dom; eauto; simpl. unfold st_ids in Hdom. simpl_app.
            repeat rewrite map_map in *. erewrite map_ext with (l:=l0), map_ext with (l:=st_anns _); eauto.
            intros; destruct_conjs; auto.
          * reflexivity.
          * intros * Hin. apply in_app_iff in Hin as [Hin|]; simpl_In.
            apply inlinelocal_topblock_nolast in Hil; auto. 2:apply n_syn. simpl_Forall; congruence.
          * split; auto.
            2:{ intros * _ Hla. inv Hla. simpl_app. apply in_app_iff in H0 as [|]; simpl_In.
                - apply inlinelocal_topblock_nolast in Hil; auto. 2:apply n_syn. simpl_Forall; subst; simpl in *; congruence.
                - congruence.
            }
            intros * Hck.
            edestruct Hsc as ((?&?&?)&_); eauto.
            simpl_app. repeat rewrite HasClock_app in *. right; right. unfold st_senv, senv_of_tyck.
            destruct Hck as [Hck|Hck]; [left|right]; inv Hck; simpl_In; econstructor; solve_In; auto.
        + simpl. constructor; simpl; auto.
        + apply senv_of_inout_NoLast.
        + apply nodupmembers_map; auto. intros; destruct_conjs; auto.
        + apply n_syn.
        + now rewrite map_fst_senv_of_inout.
        + now rewrite map_fst_senv_of_inout.
        + destruct Hwc as (?&?&?); auto. simpl_app; auto.
          erewrite 2 map_map, map_ext, map_ext with (l:=n_out _); eauto. 1,2:intros; destruct_conjs; auto.
        + destruct Hwc as (?&?&?), G1; auto.
        + unfold st_ids; rewrite init_st_anns, app_nil_r...
        + unfold st_senv. rewrite init_st_anns, app_nil_r...
        + eapply init_st_valid; eauto using local_not_in_switch_prefs, PS_For_all_empty.
      - erewrite find_node_other in Hfind; eauto.
        eapply sem_node_ck_cons'...
        destruct G2; apply HGref.
        econstructor...
        destruct G1; eapply sem_block_ck_cons...
        eapply find_node_later_not_Is_node_in in Hord1...
    Qed.

  End inlinelocal_node_sem.

  Lemma inlinelocal_global_refines : forall G,
      wc_global G ->
      global_sem_refines G (inlinelocal_global G).
  Proof with eauto using wc_global_Ordered_nodes.
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
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (LCA : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Ty : LTYPING Ids Op OpAux Cks Senv Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Lord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
       (LClockSem : LCLOCKSEMANTICS Ids Op OpAux Cks Senv Syn Ty Clo LCA Lord CStr Sem)
       (IL  : INLINELOCAL Ids Op OpAux Cks Senv Syn)
       <: ILCORRECTNESS Ids Op OpAux Cks CStr Senv Syn LCA Ty Clo Lord Sem LClockSem IL.
  Include ILCORRECTNESS Ids Op OpAux Cks CStr Senv Syn LCA Ty Clo Lord Sem LClockSem IL.
End ILCorrectnessFun.
