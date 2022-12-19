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
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LSemantics Lustre.LClockedSemantics.
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
       (Import Ty : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import Cl : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import Ord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (Import LCS : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Cl Ord CStr Sem)
       (Import IL  : INLINELOCAL Ids Op OpAux Cks Senv Syn).

  Module Import SCT := SCCorrectnessFun Ids Op OpAux Cks CStr Senv Syn Cl Ord Sem LCS SC. Import SC.

  Module Typing := ILTypingFun Ids Op OpAux Cks Senv Syn Ty IL.
  Module Clocking := ILClockingFun Ids Op OpAux Cks Senv Syn Cl IL.

  Fact mask_hist_sub sub : forall k r H H',
      (forall x y vs, Env.find x sub = Some y -> sem_var H (Var x) vs -> sem_var H' (Var y) vs) ->
      forall x y vs, Env.find x sub = Some y -> sem_var (mask_hist k r H) (Var x) vs -> sem_var (mask_hist k r H') (Var y) vs.
  Proof.
    intros * Hsub * Hfind Hv.
    eapply sem_var_mask_inv in Hv as (?&Hv&Heq).
    eapply Hsub, sem_var_mask in Hv; eauto. rewrite Heq; eauto.
  Qed.

  Fact mask_hist_nsub (sub : Env.t ident) : forall k r H H',
      (forall x vs, Env.find x sub = None -> sem_var H (Var x) vs -> sem_var H' (Var x) vs) ->
      forall x vs, Env.find x sub = None -> sem_var (mask_hist k r H) (Var x) vs -> sem_var (mask_hist k r H') (Var x) vs.
  Proof.
    intros * Hsub * Hfind Hv.
    eapply sem_var_mask_inv in Hv as (?&Hv&Heq).
    eapply Hsub, sem_var_mask in Hv; eauto. rewrite Heq; eauto.
  Qed.

  Import Fresh Facts Tactics.
  Import List.

  Fact find_pred_snd_nNone : forall (sub: Env.t ident) x y,
      Env.find x sub = Some y ->
      Env.find_pred (fun _ y' => Var y' ==b Var y) sub <> None.
  Proof.
    unfold Env.find_pred. intros *.
    apply Env.Props.P.fold_rec.
    - intros * Hempty Hfind.
      apply Hempty in Hfind as [].
    - intros * _ _ Hadd Hrec Hfind.
      unfold Env.Props.P.Add in Hadd. rewrite Hadd in Hfind.
      destruct (ident_eq_dec x k); subst.
      * rewrite Env.gss in Hfind. inv Hfind.
        rewrite equiv_decb_refl. congruence.
      * rewrite Env.gso in Hfind; auto.
        destruct (_ ==b _); auto. congruence.
  Qed.

  Fact find_pred_snd_spec : forall (sub: Env.t ident) x y,
      NoDup (map snd (Env.elements sub)) ->
      Env.find x sub = Some y ->
      Env.find_pred (fun _ y' => Var y' ==b Var y) sub = Some (x, y).
  Proof.
    intros * Hnd Hfind.
    destruct (Env.find_pred _ _) as [(?&?)|] eqn:Hfind'.
    - apply Env.find_pred_spec in Hfind' as (Hfind'&Heq).
      rewrite equiv_decb_equiv in Heq; inv Heq.
      eapply Env.NoDup_snd_elements in Hfind; eauto; subst.
      reflexivity.
    - exfalso.
      eapply find_pred_snd_nNone; eauto.
  Qed.

  Section inlinelocal_node_sem.
    Variable G1 : @global noswitch_block switch_prefs.
    Variable G2 : @global nolocal_top_block local_prefs.

    Hypothesis HGref : global_sem_refines G1 G2.
    Hypothesis HwG1 : wc_global G1.

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

    Definition st_senv (st: fresh_st local _) := senv_of_tyck (st_anns st).

    Fact mmap_inlinelocal_block_sem : forall Γ blks sub Γ' blks' st st' bs Hi1 Hi2,
        Forall
          (fun blk => forall sub Γ' blks' st st' bs Hi1 Hi2,
               (forall x, ~IsLast (Γ++Γ') x) ->
               (forall x, IsVar Γ x -> ~IsVar Γ' x) ->
               (forall x, Env.In x sub <-> IsVar Γ' x) ->
               (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 (Var x) vs -> sem_var Hi2 (Var y) vs) ->
               (forall x vs, IsVar Γ x -> sem_var Hi1 (Var x) vs -> sem_var Hi2 (Var x) vs) ->
               (forall x y, Env.MapsTo x y sub -> exists n : ident, y = gensym local (Some x) n) ->
               NoDupMembers (Γ++Γ') ->
               noswitch_block blk ->
               NoDupLocals (map fst (Γ++Γ')) blk ->
               Forall (AtomOrGensym switch_prefs) (map fst Γ) ->
               GoodLocals switch_prefs blk ->
               wc_env (idck (Γ++Γ')) ->
               wc_block G1 (Γ++Γ') blk ->
               dom_ub Hi1 (Γ++Γ') ->
               sem_block_ck G1 Hi1 bs blk ->
               dom Hi2 (Γ++st_senv st) ->
               sc_vars (Γ++st_senv st) Hi2 bs ->
               inlinelocal_block sub blk st = (blks', st') ->
               exists Hi3,
                 Hi2 ⊑ Hi3 /\
                 dom Hi3 (Γ++st_senv st') /\
                 sc_vars (Γ++st_senv st') Hi3 bs /\
                 Forall (sem_block_ck G2 Hi3 bs) blks')
          blks ->
        (forall x, ~IsLast (Γ++Γ') x) ->
        (forall x, IsVar Γ x -> ~IsVar Γ' x) ->
        (forall x, Env.In x sub <-> IsVar Γ' x) ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 (Var x) vs -> sem_var Hi2 (Var y) vs) ->
        (forall x vs, IsVar Γ x -> sem_var Hi1 (Var x) vs -> sem_var Hi2 (Var x) vs) ->
        (forall x y, Env.MapsTo x y sub -> exists n : ident, y = gensym local (Some x) n) ->
        NoDupMembers (Γ++Γ') ->
        Forall noswitch_block blks ->
        Forall (NoDupLocals (map fst (Γ++Γ'))) blks ->
        Forall (AtomOrGensym switch_prefs) (map fst Γ) ->
        Forall (GoodLocals switch_prefs) blks ->
        wc_env (idck (Γ++Γ')) ->
        Forall (wc_block G1 (Γ++Γ')) blks ->
        dom_ub Hi1 (Γ++Γ') ->
        Forall (sem_block_ck G1 Hi1 bs) blks ->
        dom Hi2 (Γ++st_senv st) ->
        sc_vars (Γ++st_senv st) Hi2 bs ->
        mmap (inlinelocal_block sub) blks st = (blks', st') ->
        exists Hi3,
          Hi2 ⊑ Hi3 /\
          dom Hi3 (Γ++st_senv st') /\
          sc_vars (Γ++st_senv st') Hi3 bs /\
          Forall (sem_block_ck G2 Hi3 bs) (concat blks').
    Proof with eauto.
      induction blks;
        intros * Hf Hnl Hdisj Hsubin Hsub Hnsub Hsubgensym Hnd1 Hns Hnd2 Hatgen Hgood Hwenv Hwc Hub Hsem Hdom Hsc Hmmap;
        inv Hf; inv Hns; inv Hnd2; inv Hgood; inv Hwc; inv Hsem; repeat inv_bind; simpl in *.
      - exists Hi2. repeat (split; auto with env). reflexivity.
      - assert (Hdl:=H).
        eapply H1 with (Hi1:=Hi1) (Hi2:=Hi2)
          in H as (Hi3&Href1&Hdom1&Hsc1&Hsem1)... clear H1.
        eapply IHblks with (Hi1:=Hi1) (Hi2:=Hi3)
          in H0 as (Hi4&Href3&Hdom3&Hsc3&Hsem3)... clear IHblks H2.
        2,3:intros; eauto using sem_var_refines.
        exists Hi4. repeat (split; auto).
        + etransitivity...
        + apply Forall_app; split; auto.
          eapply Forall_impl; [|eauto]; intros; eauto using sem_block_refines.
    Qed.

    Ltac inv_scope :=
      (Syn.inv_scope || Ty.inv_scope || Cl.inv_scope || Sem.inv_scope || LCS.inv_scope).

    (** Central correctness lemma                                              *)
    (* - vars : not renamed (in + out of the node)
       - vars' : renamed (local vars already encountered)
       - Hi1 : history before renaming
       - Hi2 : history after renaming of the enclosing blocks
       - Hi3 : refines Hi2 by adding the renamed variables of the subblocks
     *)
    Lemma inlinelocal_block_sem Γ : forall blk sub Γ' blks' st st' bs Hi1 Hi2,
        (forall x, ~IsLast (Γ++Γ') x) ->
        (forall x, IsVar Γ x -> ~IsVar Γ' x) ->
        (forall x, Env.In x sub <-> IsVar Γ' x) ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 (Var x) vs -> sem_var Hi2 (Var y) vs) ->
        (forall x vs, IsVar Γ x -> sem_var Hi1 (Var x) vs -> sem_var Hi2 (Var x) vs) ->
        (forall x y, Env.MapsTo x y sub -> exists n, y = gensym local (Some x) n) ->
        NoDupMembers (Γ++Γ') ->
        noswitch_block blk ->
        NoDupLocals (map fst (Γ++Γ')) blk ->
        Forall (AtomOrGensym switch_prefs) (map fst Γ) ->
        GoodLocals switch_prefs blk ->
        wc_env (idck (Γ++Γ')) ->
        wc_block G1 (Γ++Γ') blk ->
        dom_ub Hi1 (Γ++Γ') ->
        sem_block_ck G1 Hi1 bs blk ->
        dom Hi2 (Γ ++ st_senv st) ->
        sc_vars (Γ++st_senv st) Hi2 bs ->
        inlinelocal_block sub blk st = (blks', st') ->
        exists Hi3,
          Hi2 ⊑ Hi3 /\
          dom Hi3 (Γ++st_senv st') /\
          sc_vars (Γ++st_senv st') Hi3 bs /\
          Forall (sem_block_ck G2 Hi3 bs) blks'.
    Proof with eauto with datatypes.
      induction blk using block_ind2;
        intros * Hnl Hdisj Hsubin Hsub Hnsub Hsubgensym Hnd1 Hns Hnd2 Hgenat Hgood Hwenv Hwc Hub Hsem Hdom Hsc Hdl;
        inv Hns; inv Hnd2; inv Hgood; inv Hwc; inv Hsem; repeat inv_bind; simpl.

      - (* equation *)
        exists Hi2. repeat (split; auto with env). reflexivity.
        constructor; auto. constructor.
        eapply subclock_equation_sem with (H:=Hi1); eauto using sem_ref_sem_equation.
        + constructor; reflexivity.
        + intros * Hl. exfalso. apply sem_var_In, Hub in Hl. eapply Hnl; eauto.
        + intros * Hnone Hv.
          assert (Hin:=Hv). eapply sem_var_In, Hub in Hin.
          repeat rewrite map_app, in_app_iff in Hin.
          apply IsVar_app in Hin as [|]; eauto.
          * exfalso. eapply Env.Props.P.F.not_find_in_iff in Hnone. eapply Hnone, Hsubin...

      - (* reset *)
        rename x into blks'.
        assert (forall k, exists Hi4, (CStr.mask_hist k r Hi2) ⊑ (CStr.mask_hist k r Hi4) /\
                            dom (CStr.mask_hist k r Hi4) (Γ++st_senv st') /\
                            sc_vars (Γ++st_senv st') (mask_hist k r Hi4) (maskb k r bs) /\
                            Forall (sem_block_ck G2 (mask_hist k r Hi4) (maskb k r bs)) (concat blks')) as Hblks.
        { intros k. specialize (H13 k).
          eapply mmap_inlinelocal_block_sem with (Hi2:=CStr.mask_hist k r Hi2) in H13
            as (Hi4&Href1&Hdom1&Hsc1&Hsem1); eauto.
          2:{ intros ??? Hfind Hv.
              eapply sem_var_mask_inv in Hv as (?&Hv&Hmask).
              rewrite Hmask. eapply sem_var_mask... }
          2:{ intros ?? Hin Hv.
              eapply sem_var_mask_inv in Hv as (?&Hv&Hmask).
              rewrite Hmask. eapply sem_var_mask... }
          2:{ eapply dom_ub_map; eauto. }
          2:{ eapply dom_map; eauto. }
          2:{ eapply sc_vars_mask in Hsc; eauto; subst. }
          assert (FEnv.Equiv (@EqSt _) Hi4 (CStr.mask_hist k r Hi4)) as Heqmask.
          { unfold st_ids in Hdom1.
            eapply slower_mask_hist. eapply sc_vars_slower_hist in Hsc1; eauto.
            simpl_app. auto using dom_dom_ub.
          }
          exists Hi4. split; [|split; [|split]].
          + rewrite <-Heqmask; auto.
          + apply dom_map; auto.
          + unfold mask_hist. simpl. eapply sc_vars_morph. 1,3,4:eauto; reflexivity. auto.
          + eapply Forall_impl; [|eauto]; intros. unfold mask_hist.
            eapply sem_block_ck_morph; eauto. reflexivity.
        }
        unfold mask_hist.
        eapply consolidate_mask_hist
          with (P := fun k H'k =>
                       (CStr.mask_hist k r Hi2) ⊑ H'k /\
                       dom H'k (Γ++st_senv st') /\
                       sc_vars (Γ++st_senv st') H'k (maskb k r bs) /\
                       Forall (sem_block_ck G2 H'k (maskb k r bs)) (concat blks'))
        in Hblks as (Hi4&HHi4).
        2:{ intros ????? Heq (?&?&(?&?)&?); subst. split; [|split; [|repeat split]].
            - rewrite <-Heq; auto.
            - split; intros ?; rewrite <-Heq; apply H10.
            - intros. rewrite <-Heq. eapply H11; eauto. now rewrite Heq.
            - intros. rewrite <-Heq. eapply H14; eauto. now rewrite Heq.
            - simpl_Forall.
              eapply sem_block_ck_morph; eauto. reflexivity.
        }
        2:{ intros ?? (?&?&?). eapply dom_fenv_dom; eauto. }
        assert (Hi2 ⊑ Hi4) as Href1.
        { eapply refines_unmask; intros. eapply HHi4. }
        exists Hi4. split; [|split; [|repeat split]]; try rewrite app_nil_r; repeat rewrite <-app_assoc...
        + erewrite <-dom_map. eapply (HHi4 0)...
        + eapply sc_vars_unmask. intros k. eapply (HHi4 k)...
        + eapply sc_vars_unmask. intros k. eapply (HHi4 k)...
        + do 2 (econstructor; eauto).
          * eapply sem_exp_refines; [eauto|].
            eapply subclock_exp_sem with (H:=Hi1); eauto using sem_ref_sem_exp.
            1:{ constructor; reflexivity. }
            { intros * Hl. apply sem_var_In, Hub in Hl. exfalso; eapply Hnl; eauto. }
            { intros * Hnone Hv.
              assert (Hin:=Hv). eapply sem_var_In, Hub in Hin; eauto.
              repeat rewrite map_app, in_app_iff in Hin.
              apply IsVar_app in Hin as [|]...
              exfalso. eapply Env.Props.P.F.not_find_in_iff in Hnone. eapply Hnone, Hsubin...
            }
          * intros. eapply HHi4...

      - (* local *)
        repeat inv_scope.
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
        assert (forall x, FEnv.In x Hi2 ->
                     ~FEnv.In x (fun x => obind (Env.find_pred (fun _ y => Var y ==b x) x0) (fun '(x, _) => Hi' (Var x)))) as Hdisj2.
        { intros ? Hin2 (?&Hfind1).
          destruct x3.
          2:{ apply Hdom, IsLast_app in Hin2 as [Hin2|Hin2]. 2:inv Hin2; simpl_In; congruence.
              eapply Hnl, IsLast_app; eauto. }
          apply obind_inversion in Hfind1 as ((?&?)&Hfind1&Hfind2).
          apply Env.find_pred_spec in Hfind1 as (Hfind1&Heq). rewrite equiv_decb_equiv in Heq; inv Heq.
          assert (Hfind1':=Hfind1). eapply fresh_idents_rename_sub_gensym in Hfind1' as (?&?); eauto; subst.
          apply Hdom, IsVar_app in Hin2 as [Hin2|Hin2]; inv Hin2; simpl_In.
          - simpl_Forall.
            eapply contradict_AtomOrGensym in Hgenat; eauto using local_not_in_switch_prefs.
          - eapply fresh_idents_rename_sub_nIn in H0; eauto. eapply H0; solve_In.
        }
        assert (forall x, Env.In x sub -> ~Env.In x x0) as Hsub1.
        { intros ?. rewrite Hsubin, Hsubin'. intros Hin1 Hin2.
          eapply H13... inv Hin1; simpl_In; do 2 esplit; eauto with datatypes. auto. }
        assert (NoDup (map snd (Env.elements x0))) as Hnd2.
        {  eapply fresh_idents_rename_sub_NoDup in H0; eauto.
           apply NoDupMembers_map; auto. intros; destruct_conjs; auto. }
        assert (Forall nolocal_block (concat x2)) as Hnlo.
        { apply Forall_concat.
          apply mmap_values, Forall2_ignore1 in H5. simpl_Forall.
          apply inlinelocal_block_nolocal in H5; auto; simpl_Forall; auto. }
        assert (Hi2 ⊑ Hi2 + (fun x3 => obind (Env.find_pred (fun (_ : Env.key) (y : ident) => Var y ==b x3) x0) (fun '(x4, _) => Hi' (Var x4)))) as Href.
        { intros ?? Hfind. do 2 esplit; try reflexivity.
          apply FEnv.union2; auto.
          destruct (obind _ _) eqn:Hb; auto. apply obind_inversion in Hb; destruct_conjs.
          exfalso.
          eapply Hdisj2. 1,2:econstructor; eauto. rewrite H1; eauto. }
        eapply mmap_inlinelocal_block_sem with
            (Γ':=Γ'++senv_of_locs locs) (Hi1:=Hi1 + Hi') (Hi2:=Hi2 + fun x => obind (Env.find_pred (fun _ y => Var y ==b x) x0) (fun '(x, _) => Hi' (Var x)))
            (sub:=Env.union sub x0) (st:=x1)
          in H5 as (Hi3&Href1&Hdom1&(Hsc11&Hsc12)&Hsem1); eauto. clear H.
        + exists Hi3. repeat (split; eauto).
          etransitivity...
        + rewrite app_assoc, NoLast_app; split; auto.
          intros * Hla; inv Hla; simpl_In; simpl_Forall. subst; simpl in *; congruence.
        + intros ?. rewrite IsVar_app. intros Hinm1 [Hinm2|Hinm2].
          * eapply Hdisj; eauto.
          * apply IsVar_senv_of_locs in Hinm2. take (forall x, InMembers x locs -> ~_) and eapply it...
            rewrite <-IsVar_fst, IsVar_app; auto.
        + intros ?. rewrite Env.union_In, Hsubin, Hsubin', IsVar_app, IsVar_senv_of_locs.
          split; intros [?|?]...
        + intros ??? Hfind Hv.
          erewrite sem_var_disj_union; eauto.
          eapply Env.union_find4 in Hfind as [Hfind|Hfind]; eapply sem_var_union in Hv as [Hv|Hv]; eauto.
          * exfalso. apply Env.find_In, Hsubin in Hfind.
            apply sem_var_In, H6, IsVar_senv_of_locs in Hv.
            take (forall x, InMembers x locs -> ~_) and eapply it...
            rewrite <-IsVar_fst, IsVar_app; auto.
          * exfalso. apply Env.find_In, Hsubin' in Hfind.
            apply sem_var_In, Hub in Hv.
            take (forall x, InMembers x locs -> ~_) and eapply it...
            rewrite <-IsVar_fst; auto.
          * right. inv Hv. econstructor; eauto.
            erewrite find_pred_snd_spec; eauto.
        + intros ?? Hfind Hv.
          erewrite sem_var_disj_union; eauto.
          eapply sem_var_union in Hv as [Hv|Hv]; eauto.
          exfalso. apply sem_var_In, H6, IsVar_senv_of_locs in Hv.
          take (forall x, InMembers x locs -> ~_) and eapply it...
          rewrite <-IsVar_fst, IsVar_app; auto.
        + intros ?? Hfind.
          eapply Env.union_find4 in Hfind as [Hfind|Hfind]...
          eapply fresh_idents_rename_sub_gensym...
        + rewrite app_assoc.
          eapply NoDupMembers_app; eauto.
          * rewrite NoDupMembers_senv_of_locs; auto.
          * intros ? Hinm Hinm2. rewrite InMembers_senv_of_locs in Hinm2.
            take (forall x, InMembers x locs -> ~_) and eapply it...
        + rewrite app_assoc, map_app, map_fst_senv_of_locs; auto.
        + unfold wc_env in *. simpl_app. rewrite app_assoc, Forall_app; split; simpl_Forall.
          * eapply wc_clock_incl; [|eauto]. solve_incl_app.
          * simpl_app; auto.
        + rewrite app_assoc; auto.
        + eapply local_hist_dom_ub in H6; eauto. now rewrite app_assoc.
        + destruct Hdom as (Dom&DomL).
          eapply fresh_idents_rename_ids in H0 as ?; subst; eauto. 2:apply NoDupMembers_map; auto; intros; destruct_conjs; auto.
          split; intros ?; unfold st_senv, senv_of_tyck; erewrite FEnv.union_In, fresh_idents_rename_anns; eauto.
          1,2:erewrite map_app, (Permutation_app_comm (map _ _)), app_assoc.
          1:rewrite IsVar_app, Dom. 2:rewrite IsLast_app, DomL.
          1,2:apply or_iff_compat_l; split; intros In.
          * destruct In as (?&Find). apply obind_inversion in Find as ((?&?)&Find&?).
            apply Env.find_pred_spec in Find as (Find&Eq). rewrite equiv_decb_equiv in Eq. inv Eq.
            eapply fresh_idents_rename_sub1 in H0; [|econstructor; eauto].
            clear - Find H0. econstructor. solve_In.
            now rewrite Find.
          * inv In. simpl_In.
            eapply fresh_idents_rename_sub2 with (x:=k) in H0 as ((?&?&Find&_)&_). solve_In.
            setoid_rewrite Find; simpl.
            assert (FEnv.In (Var k) Hi') as (?&Hfind') by (apply H6, IsVar_senv_of_locs; eauto using In_InMembers).
            esplit.
            apply find_pred_snd_spec in Find; auto. rewrite Find; simpl; eauto.
          * clear - In. destruct In as (?&Find). apply obind_inversion in Find as ((?&?)&Find&?).
            apply Env.find_pred_spec in Find as (_&Eq). rewrite equiv_decb_equiv in Eq. inv Eq.
          * clear - In. inv In. simpl_In. congruence.
        +{ unfold st_senv. erewrite fresh_idents_rename_anns; eauto. split.
           2:{ intros * _ Hla. exfalso. apply IsLast_app in Hla as [Hla|Hla].
               - eapply Hnl, IsLast_app; eauto.
               - apply senv_of_tyck_NoLast in Hla; auto.
           }
           destruct Hsc as (Hsc&_).
           intros * Hck Hv; simpl in *.
           unfold senv_of_tyck in Hck. simpl_app. rewrite Permutation_swap, HasClock_app in Hck.
           apply sem_var_union in Hv.
           assert (Hfresh:=H0). eapply fresh_idents_rename_ids in Hfresh; subst.
           2:(erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; auto;
              intros; destruct_conjs; auto).
           assert (forall x, InMembers x locs -> ~ FEnv.In (Var x) Hi2) as Hdisj3.
           { intros ? Hinm Henv. eapply Hdom in Henv.
             apply IsVar_app in Henv as [Hin'|Hin'].
             - apply IsVar_fst in Hin'. take (forall x, InMembers x locs -> ~_) and eapply it...
             - eapply st_valid_AtomOrGensym_nIn with (st:=st); eauto using local_not_in_switch_prefs.
               + eapply Forall_forall in H9...
               + clear - Hin'. inv Hin'. solve_In. }
           assert (forall x3, FEnv.In x3 Hi2 -> ~ FEnv.In x3 Hi') as Hdisj4.
           { intros * In1 In2. destruct x4.
             - eapply Hdisj3 in In1; eauto. now apply IsVar_senv_of_locs, H6.
             - apply H6 in In2. clear - In2 H2. inv In2. simpl_In. simpl_Forall. subst; simpl in *; congruence. }
           destruct Hck as [Hck|Hck], Hv as [Hv|Hv].
           - exfalso. apply sem_var_In, Hdisj2 in Hv.
             eapply Hv. inv Hck. simpl_In.
             assert (FEnv.In (Var k) Hi') as [? Hfind'] by (eapply H6, IsVar_senv_of_locs; eauto using In_InMembers).
             apply In_InMembers, Hsubin' in Hin as [? Hfind].
             rewrite Hfind; simpl. econstructor; simpl.
             erewrite find_pred_snd_spec; eauto.
           - inv Hck. simpl_In.
             assert (FEnv.In (Var k) Hi') as [vs Hfind'] by (eapply H6, IsVar_senv_of_locs; eauto using In_InMembers).
             assert (sem_var Hi' (Var k) vs) as Hv' by (econstructor; eauto; reflexivity).
             take (sc_vars _ _ _) and destruct it as (Hsc2&_).
             eapply rename_var_sem in Hv' as Heq. eapply sem_var_det in Heq; [|apply Hv]. rewrite Heq.
             eapply sem_var_refines, Hsc2 in Hv'; eauto using FEnv.union_refines4', EqStrel_Reflexive.
             2:econstructor; solve_In; reflexivity.
             simpl in *.
             eapply subclock_clock_sem, subclock_clock_sem
               with (Hi':= var_history (Hi2 + Hi')). 3,6:constructor; reflexivity. 5:eauto.
             + intros * Hs Hvar. rewrite sem_var_history in *.
               apply sem_var_union in Hvar as [Hvar|Hvar].
               * exfalso. eapply Hdisj3; eauto using sem_var_In.
                 apply Hsubin'. econstructor; eauto.
               * inv Hvar. econstructor; eauto.
                 eapply FEnv.union3'. erewrite find_pred_snd_spec; eauto.
             + intros * Hs Hvar. rewrite sem_var_history in *.
               apply sem_var_union in Hvar as [Hvar|Hvar].
               * apply sem_var_disj_union; eauto.
               * exfalso.
                 eapply Env.Props.P.F.not_find_in_iff; eauto.
                 eapply Hsubin', IsVar_senv_of_locs, H6; eauto using sem_var_In.
             + intros * Hs Hvar. rewrite sem_var_history in *.
               apply sem_var_union in Hvar as [Hvar|Hvar].
               * eapply sem_var_disj_union; eauto.
               * exfalso. apply sem_var_In, H6, IsVar_senv_of_locs, H13 in Hvar.
                 eapply Hvar, in_app_iff, or_intror, IsVar_fst, Hsubin. econstructor; eauto.
             + intros * Hs Hvar. rewrite sem_var_history in *.
               apply sem_var_union in Hvar as [Hvar|Hvar].
               * eapply sem_var_disj_union; eauto.
                 left. eapply Hnsub; eauto.
                 apply sem_var_In, Hub, IsVar_app in Hvar as [|Hvar]; auto with datatypes.
                 apply Hsubin, Env.Props.P.F.in_find_iff in Hvar. contradiction.
               * eapply sem_var_disj_union; eauto.
             + intros * Hfind Hvar. inv Hvar. econstructor; eauto.
               erewrite find_pred_snd_spec; eauto.
             + intros * Hfind Hvar. exfalso.
               eapply Env.Props.P.F.not_find_in_iff; eauto.
               eapply Hsubin', IsVar_senv_of_locs, H6, sem_var_In; eauto.
           - eapply sem_clock_refines; eauto using var_history_refines.
           - exfalso.
             eapply Hdisj2, sem_var_In, Hv.
             apply Hdom. eauto with senv.
         }
    Qed.

    Lemma inlinelocal_topblock_sem Γ : forall blk blks' locs' st st' bs Hi1 Hi2,
        (forall x, ~IsLast Γ x) ->
        (forall x vs, IsVar Γ x -> sem_var Hi1 (Var x) vs -> sem_var Hi2 (Var x) vs) ->
        NoDupMembers Γ ->
        noswitch_block blk ->
        NoDupLocals (map fst Γ) blk ->
        Forall (AtomOrGensym switch_prefs) (map fst Γ) ->
        GoodLocals switch_prefs blk ->
        wc_env (idck Γ) ->
        wc_block G1 Γ blk ->
        dom Hi1 Γ ->
        sem_block_ck G1 Hi1 bs blk ->
        dom Hi2 (Γ ++ st_senv st) ->
        sc_vars (Γ++st_senv st) Hi2 bs ->
        inlinelocal_topblock blk st = (blks', locs', st') ->
        exists Hi3,
          Hi2 ⊑ Hi3 /\
          dom Hi3 ((Γ++senv_of_locs locs')++st_senv st') /\
          sc_vars (Γ++senv_of_locs locs'++st_senv st') Hi3 bs /\
          Forall (sem_block_ck G2 Hi3 bs) blks'.
    Proof with eauto with datatypes.
      Opaque inlinelocal_block.
      destruct blk; intros * Hnl Hinm Hnd1 Hns Hnd2 Hatgen Hgood Hwenv Hwc Hdom1 Hsem Hdom2 Hsc Hil;
        try destruct s; repeat inv_bind; simpl in *.
      3:inv Hns.
      1-3:eapply inlinelocal_block_sem with (Hi1:=Hi1) in H as (Hi3&?&Hdom3&Hsc3&?);
        repeat rewrite app_nil_r in *; eauto; simpl in *.
      16:inv Hns; inv Hnd2; inv Hgood; inv Hwc; inv Hsem; repeat inv_scope.
      16:assert (forall x, FEnv.In x Hi2 -> ~FEnv.In x Hi') as Hdisj2.
      16:{ intros * Hin2 Hin1. destruct x0; apply H4 in Hin1; apply Hdom2 in Hin2.
           2:{ clear - Hin1 H2. inv Hin1. simpl_In. simpl_Forall. subst; simpl in *; congruence. }
           apply IsVar_senv_of_locs in Hin1.
           apply IsVar_app in Hin2 as [Hin2|Hin2]...
           - apply IsVar_fst in Hin2. take (forall x, InMembers x _ -> ~In _ _) and eapply it; eauto.
           - eapply st_valid_AtomOrGensym_nIn; eauto using local_not_in_switch_prefs.
             eapply Forall_forall in H5...
             clear - Hin2. inv Hin2; solve_In. }
      16:assert (Hi1 + Hi' ⊑ Hi2 + Hi') as Href.
      16:{ intros ?? Hv. apply FEnv.union4 in Hv as [Hv|Hv].
           - destruct x0. 2:{ eapply FEnv.find_In, Hdom1, Hnl in Hv as []. }
             assert (IsVar Γ x0) as Hin by (eapply Hdom1; econstructor; eauto).
             assert (sem_var Hi2 (Var x0) v) as Hv2.
             { eapply Hinm; [|econstructor; eauto; reflexivity]. now inv Hin. }
             inv Hv2. do 2 esplit; eauto. apply FEnv.union2; auto.
             apply FEnv.not_find_In. intros contra. apply H4, IsVar_senv_of_locs in contra.
             take (forall x, InMembers x _ -> ~In _ _) and eapply it; eauto. now apply IsVar_fst.
           - do 2 esplit; [reflexivity|auto using FEnv.union3'].
      }
      16:assert (Hi2 ⊑ Hi2 + Hi') as Href2.
      16:{ intros ?? Hfind. do 2 esplit; try reflexivity.
           apply FEnv.union2; auto.
           apply FEnv.not_find_In, Hdisj2. econstructor; eauto. }
      16:eapply mmap_inlinelocal_block_sem
        with (Γ:=Γ++senv_of_locs locs')
             (Hi1:=Hi1 + Hi')
             (Hi2:=Hi2 + Hi')
        in H as (Hi3&?&Hdom3&Hsc3&?);
        repeat rewrite app_nil_r in *; eauto; simpl in *.
      17:eapply Forall_forall; intros; eauto using inlinelocal_block_sem.
      all:match goal with
          | |- forall x, _ -> ~ IsVar [] x =>
              intros * _ In; inv In; take (InMembers _ []) and inv it
          | |- forall x, Env.In x (Env.empty ident) <-> _ =>
              intros ?; rewrite Env.Props.P.F.empty_in_iff; split; [intros []|intros In]; inv In; take (InMembers _ []) and inv it
          | |- forall x y vs, Env.find _ (Env.empty ident) = Some _ -> _ =>
              intros * Hfind; eapply Env.Props.P.F.empty_mapsto_iff in Hfind as []
          | |- forall x y, Env.MapsTo _ _ (Env.empty ident) -> _ =>
              intros * Hfind; eapply Env.Props.P.F.empty_mapsto_iff in Hfind as []
          | _ => idtac
          end; auto using dom_dom_ub.
      - exists Hi3. repeat (split; eauto).
        + etransitivity; eauto using FEnv.union_refines4', EqStrel.
        + clear - Hsc3. destruct Hsc3 as (Hsc3&_). simpl_app; eauto.
        + clear - Hsc3. destruct Hsc3 as (_&Hsc3). simpl_app; eauto.
      - rewrite NoLast_app; split; auto.
        intros * Hla. inv Hla. simpl_In. simpl_Forall. subst; simpl in *; congruence.
      - intros * Hinm1 Hv.
        eapply sem_var_refines; [eapply Href|eauto].
      - apply NoDupMembers_app; auto.
        + apply NoDupMembers_senv_of_locs; auto.
        + intros ? Hinm1 Hinm2. rewrite InMembers_senv_of_locs in Hinm2.
          take (forall x, InMembers x _ -> ~In _ _) and eapply it...
      - now rewrite map_app, map_fst_senv_of_locs.
      - rewrite map_app, map_fst_senv_of_locs.
        apply Forall_app; auto.
      - unfold wc_env in *. simpl_app.
        apply Forall_app; split; simpl_Forall; eauto.
        eapply wc_clock_incl; eauto; solve_incl_app.
      - eapply dom_dom_ub, local_hist_dom; eauto.
      - unfold dom. rewrite <-app_assoc. setoid_rewrite (Permutation_app_comm (senv_of_locs _)). rewrite app_assoc.
        eapply local_hist_dom; eauto.
      - split.
        2:{ intros * _ Hla. exfalso. repeat rewrite IsLast_app in Hla. destruct Hla as [[Hla|Hla]|Hla].
            - eapply Hnl; eauto.
            - inv Hla. simpl_In. simpl_Forall. subst; simpl in *; congruence.
            - eapply senv_of_tyck_NoLast; eauto.
        }
        intros * Hck Hv. rewrite (Permutation_app_comm Γ), <-app_assoc, HasClock_app in Hck. destruct Hck as [Hck|Hck].
        + edestruct H17 as (Hsc1&_).
          eapply sem_clock_refines, Hsc1, sem_var_refines'; eauto using var_history_refines. simpl.
          apply FEnv.union_In, or_intror, H4. inv Hck. econstructor. solve_In.
        + destruct Hsc as (Hsc1&_).
          eapply sem_clock_refines, Hsc1, sem_var_refines'; eauto using var_history_refines.
          apply Hdom2. inv Hck. unfold st_ids, st_senv in *.
          apply IsVar_app. apply in_app_iff in H0 as [|]; [left|right]; econstructor; eauto using In_InMembers.
      Transparent inlinelocal_block.
    Qed.

    Lemma inlinelocal_node_sem : forall f n ins outs,
        wc_global (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        Ordered_nodes (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(types) G2.(externs) ((inlinelocal_node n)::G2.(nodes))) ->
        sem_node_ck (Global G1.(types) G1.(externs) (n::G1.(nodes))) f ins outs ->
        sem_node_ck (Global G2.(types) G2.(externs) ((inlinelocal_node n)::G2.(nodes))) f ins outs.
    Proof with eauto.
      intros * Hwc Hord1 Hord2 Hsem.

      inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
      - erewrite find_node_now in Hfind; eauto. inv Hfind.
        (*The semantics of equations can be given according to G only *)
        eapply sem_block_ck_cons in H3; eauto. rename H3 into Hblksem.
        2:{ inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }

        replace {| types := types G1; nodes := nodes G1 |} with G1 in Hblksem by (destruct G1; auto).
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
          in Hblksem as (Hf&Href&Hdom&Hsc&Hsem); eauto. 11:destruct inlinelocal_topblock as ((?&?)&?); reflexivity.
        eapply Snode with (H:=H); simpl; eauto.
        + erewrite find_node_now; eauto.
        + eauto.
        + eauto.
        + apply sem_block_ck_cons'; simpl...
          2:{ eapply find_node_not_Is_node_in in Hord2.
            2:erewrite find_node_now; eauto. eauto. }
          destruct (inlinelocal_topblock _ _) as ((?&?)&?) eqn:Hil.
          assert (FEnv.Equiv (@EqSt _) Hf (H + restrict Hf (senv_of_locs l0 ++ st_senv f))) as Heq.
          { intros ?. destruct (Hf x) eqn:Hfind.
            - unfold restrict, FEnv.restrict. destruct (existsb (fun y : lustre_var => y ==b x) (vars_of_senv (senv_of_locs l0 ++ st_senv f))) eqn:Ex.
              + erewrite FEnv.union3'; eauto using FEnv.restrict_find. 2:setoid_rewrite Ex; eauto.
                reflexivity.
              + assert (FEnv.In x H) as (?&Hfind').
                { destruct Hdom as (D2&DL2). apply FEnv.find_In in Hfind.
                  apply existsb_Forall, forallb_Forall, Forall_flat_map in Ex.
                  destruct x; apply Hdom1; [apply D2 in Hfind|apply DL2 in Hfind].
                  1,2:rewrite <-app_assoc in Hfind. 1:apply IsVar_app in Hfind as [|Hfind]; auto. 2:apply IsLast_app in Hfind as [|Hfind]; auto.
                  - inv Hfind. simpl_In. simpl_Forall.
                    rewrite equiv_decb_refl in H4. inv H4.
                  - inv Hfind. simpl_Forall. destruct (causl_last _); try congruence. simpl in *; simpl_Forall.
                    rewrite equiv_decb_refl in H9. inv H9.
                }
                assert (Hfind'':=Hfind'). apply Href in Hfind'' as (?&?&Hfind''). rewrite Hfind in Hfind''; inv Hfind''.
                erewrite FEnv.union2; eauto using FEnv.restrict_find_None1.
                2:setoid_rewrite Ex; auto.
                constructor. now symmetry.
            - replace ((_ + _) x) with (@None (Stream svalue)); [constructor|].
              symmetry. apply FEnv.union_None; split; eauto using FEnv.restrict_find_None2, FEnv.refines_None.
          }
          econstructor. eapply Sscope with (Hi':=restrict Hf (senv_of_locs l0 ++ st_senv f)).
          *{ destruct Hdom as (D&DL). split; intros *; unfold restrict.
             1,2:rewrite FEnv.restrict_In, senv_of_locs_app.
             - rewrite D, vars_of_senv_Var, 4 IsVar_app.
               split; intros; repeat (progress destruct_conjs || take (_ \/ _) and destruct it); auto.
               1,2:right; clear - H3; inv H3; econstructor; solve_In.
               clear - H0. split; right; inv H0; econstructor; unfold st_senv, senv_of_tyck; solve_In.
             - rewrite DL, vars_of_senv_Last, 4 IsLast_app.
               split; intros; repeat (progress destruct_conjs || take (_ \/ _) and destruct it); auto.
               1,2:right; clear - H3; inv H3; econstructor; solve_In; auto.
               clear - H0. split; right; inv H0; econstructor; unfold st_senv, senv_of_tyck; solve_In; auto.
           }
          * intros * Hin. apply in_app_iff in Hin as [Hin|]; simpl_In.
            apply inlinelocal_topblock_nolast in Hil; auto. 2:apply n_syn. simpl_Forall; congruence.
          * eapply sc_vars_morph. 1,3:reflexivity. eauto.
            eapply sc_vars_incl; [|eauto]. unfold st_senv, senv_of_locs, senv_of_tyck. repeat solve_incl_app.
            erewrite map_map, map_ext; [reflexivity|]. intros; destruct_conjs; auto.
          * destruct G2; simpl in *. simpl_Forall.
            eapply sem_block_ck_morph; eauto. reflexivity.
        + simpl. constructor; simpl; auto.
        + apply senv_of_inout_NoLast.
        + apply NoDupMembers_map; auto. intros; destruct_conjs; auto.
        + apply n_syn.
        + now rewrite map_fst_senv_of_inout.
        + now rewrite map_fst_senv_of_inout.
        + destruct Hwc as (?&?&?); auto. simpl_app; auto.
          erewrite 2 map_map, map_ext, map_ext with (l:=n_out _); eauto. 1,2:intros; destruct_conjs; auto.
        + destruct Hwc as (?&?&?), G1; auto.
        + unfold st_senv; rewrite init_st_anns, app_nil_r...
        + unfold st_senv. rewrite init_st_anns, app_nil_r...
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
    intros [].
    induction nodes0; intros * Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      eapply Clocking.inlinelocal_global_wc, wc_global_Ordered_nodes in Hwc' ;
        unfold inlinelocal_global in Hwc'; simpl in Hwc'.
      apply global_sem_ref_cons with (f:=n_name a)...
      + inv Hwc. eapply IHnodes0...
      + intros ins outs Hsem; simpl in *.
        change types0 with ((Global types0 externs0 (map inlinelocal_node nodes0)).(types)).
        eapply inlinelocal_node_sem with (G1:=Global types0 externs0 nodes0)...
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
       (Ty : LTYPING Ids Op OpAux Cks Senv Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Lord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
       (LClockSem : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Clo Lord CStr Sem)
       (IL  : INLINELOCAL Ids Op OpAux Cks Senv Syn)
       <: ILCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Ty Clo Lord Sem LClockSem IL.
  Include ILCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Ty Clo Lord Sem LClockSem IL.
End ILCorrectnessFun.
