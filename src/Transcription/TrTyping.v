From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.

From Velus Require Import Lustre.LTyping.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLTyping.

From Coq Require Import String.
From Coq Require Import Permutation.

From Coq Require Import List.
Import List.ListNotations.

From compcert Require Import common.Errors.
Open Scope error_monad_scope.

(** * Typing Preservation for Transcription *)

Module Type TRTYPING
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX Ids Op)
       (Import Cks  : CLOCKS Ids Op OpAux)
       (Senv        : STATICENV Ids Op OpAux Cks)
       (L           : LSYNTAX  Ids Op OpAux Cks Senv)
       (LT          : LTYPING  Ids Op OpAux Cks Senv L)
       (Import CE   : CESYNTAX Ids Op OpAux Cks)
       (CET         : CETYPING Ids Op OpAux Cks CE)
       (NL          : NLSYNTAX Ids Op OpAux Cks CE)
       (Ord         : NLORDERED Ids Op OpAux Cks CE     NL)
       (NLT         : NLTYPING  Ids Op OpAux Cks CE NL Ord CET)
       (Import TR   : TR Ids Op OpAux Cks Senv L CE NL).

  Lemma wt_clock_l_ce :
    forall enums vars ck,
      LT.wt_clock enums vars ck -> CET.wt_clock enums (Senv.idty vars) ck.
  Proof.
    induction ck; intros * H; inv H; constructor; eauto.
    inv H3. solve_In. congruence.
  Qed.

  Lemma typeof_lexp {PSyn prefs} :
    forall (G: @L.global PSyn prefs) vars e e' ty,
      to_lexp e = OK e' ->
      LT.wt_exp G vars e ->
      L.typeof e = [ty] ->
      typeof e' = ty.
  Proof.
    intros * Htr Hwt Hty. revert dependent e'. revert dependent ty.
    induction e using L.exp_ind2; intros; inv Htr; inv Hty; simpl; auto.
    - cases.
    - cases. now monadInv H0.
    - cases. now monadInv H0.
    - cases. inv H. monadInv H1. simpl in *. inv Hwt. simpl_Foralls.
      take (L.typesof _ = _) and inversion it as [Ht].
      rewrite app_nil_r in Ht.
      take ([_] = [_]) and inv it.
      eauto.
  Qed.

  Fact add_whens_typeof : forall ty ck,
      typeof (add_whens (init_type ty) ty ck) = ty.
  Proof.
    induction ck as [|??? (?&?)]; simpl; auto.
    destruct ty; simpl; auto.
    f_equal. apply ctype_init_ctype.
  Qed.

  Lemma typeofc_cexp {PSyn prefs} :
    forall (G: @L.global PSyn prefs) vars e e' ty,
      to_cexp e = OK e' ->
      LT.wt_exp G vars e ->
      L.typeof e = [ty] ->
      CE.typeofc e' = ty.
  Proof.
    intros * Htr Hwt Hty. revert dependent e'. revert dependent ty.
    induction e using L.exp_ind2; intros; inv Htr; inv Hty; simpl; auto.
    - cases.
    - cases. monadInv H0. monadInv EQ. now simpl.
    - cases. monadInv H0. monadInv EQ. now simpl.
    - cases. monadInv H1. monadInv EQ. simpl in *. inv Hwt.
      take (L.typesof _ = _) and inversion it as [Ht].
      rewrite app_nil_r in Ht.
      take ([_] = [_]) and inv it.
      simpl_Foralls. eauto using typeof_lexp.
    - cases. monadInv H1. inv H2; auto.
    - cases; monadInv H2; inv H3; simpl in *; auto.
      + inv H0. inv Hwt; simpl in *. rewrite app_nil_r in *.
        inv H15; eauto.
      + simpl. apply add_whens_typeof.
  Qed.

  Lemma wt_constant {PSyn prefs} :
    forall (G: @L.global PSyn prefs) vars e ty c,
      to_constant e = OK c ->
      LT.wt_exp G vars e ->
      L.typeof e = [ty] ->
      wt_const G.(L.enums) c ty.
  Proof.
    intros * Htr Hwt Hty.
    induction e using L.exp_ind2; intros; inv Htr; inv Hwt;
      simpl in *.
    - inv Hty. constructor.
    - inv Hty. constructor; auto.
    - cases_eqn H1; subst.
      simpl in Hty. rewrite app_nil_r in Hty.
      apply Forall_singl in H8. apply Forall_singl in H; auto.
  Qed.

  Section wt_node.
    Variable (G : @L.global L.nolocal_top_block norm2_prefs).
    Hypothesis HwtG : LT.wt_global G.

    Lemma wt_lexp :
      forall vars e e',
        to_lexp e = OK e' ->
        LT.wt_exp G vars e ->
        CET.wt_exp G.(L.enums) (Senv.idty vars) e'.
    Proof.
      intros * Htr Hwt. revert dependent e'.
      induction e using L.exp_ind2; intros; try (now inv Htr); inv Hwt; eauto with clocks nltyping.
      - inv Htr. now constructor.
      - inv Htr. now constructor.
      - monadInv Htr. constructor; eauto. inv H1. solve_In.
      - monadInv Htr. constructor; eauto. eapply typeof_lexp in EQ as ->; eauto.
      - monadInv Htr. constructor; eauto.
        eapply typeof_lexp in EQ as ->; eauto.
        eapply typeof_lexp in EQ1 as ->; eauto.
      - inv Htr. cases. monadInv H1. inv H. inv H7. econstructor; eauto.
        inv H4. solve_In. congruence.
    Qed.

    Lemma wt_add_whens vars : forall ty ck,
        LT.wt_enum G ty ->
        CET.wt_clock (L.enums G) vars ck ->
        CET.wt_exp (L.enums G) vars (add_whens (init_type ty) ty ck).
    Proof.
      induction ck as [|??? (?&?)]; intros Henum Hck; inv Hck; simpl.
      - destruct ty; simpl; constructor.
        1,2:inv Henum; auto.
      - econstructor; eauto.
    Qed.

    Lemma wt_cexp :
      forall vars e e',
        to_cexp e = OK e' ->
        Forall (LT.wt_enum G) (map (fun '(_, a) => a.(Senv.typ)) vars) ->
        LT.wt_exp G vars e ->
        CET.wt_cexp G.(L.enums) (Senv.idty vars) e'.
    Proof.
      intros * Htr Hwvars Hwt. revert dependent e'.
      Opaque to_lexp.
      induction e using L.exp_ind2; intros; try (now inv Htr); inv Hwt; simpl in *; try monadInv Htr.
      1-6:eapply wt_lexp in EQ; eauto with nltyping. 1-6:econstructor; eauto.
      Transparent to_lexp.
      - inv Htr. cases_eqn Hb. monadInv H1.
        constructor; eauto.
        + inv H3. solve_In. congruence.
        + erewrite map_length, <-Permutation_length; eauto using BranchesSort.Permuted_sort.
          erewrite mmap_length; eauto.
          erewrite <-map_length, H5, seq_length; auto.
        + clear - H7 H8 EQ.
          rewrite Forall_map, <-BranchesSort.Permuted_sort. revert dependent x.
          induction es; intros; simpl in *; monadInv EQ; inv H7; inv H8; constructor; auto.
          cases_eqn EQ0; subst. inv H1. simpl in H3; rewrite app_nil_r in H3.
          monadInv EQ0. eapply typeofc_cexp in EQ1; eauto.
        + clear - H H7 EQ.
          rewrite Forall_map, <-BranchesSort.Permuted_sort. revert dependent x.
          induction es; intros; simpl in *; monadInv EQ; inv H; inv H7; constructor; auto.
          cases_eqn EQ0; inv H1; inv H2; monadInv EQ0; auto.
      - inv Htr. cases_eqn H2; simpl in *; subst. monadInv H2.
        econstructor; eauto.
        + eapply wt_lexp in EQ; eauto.
        + eapply typeof_lexp in EQ; eauto.
        + erewrite map_length, <-Permutation_length; eauto using BranchesSort.Permuted_sort.
          erewrite mmap_length; eauto.
          erewrite <-map_length, H8, seq_length; auto.
        + intros ? Hin.
          eapply in_map_iff in Hin as ((?&?)&Heq&Hin); simpl in *; inv Heq.
          rewrite <-BranchesSort.Permuted_sort in Hin.
          eapply mmap_inversion, Coqlib.list_forall2_in_right in EQ1 as ((?&?)&?&Hl); eauto.
          cases_eqn EQ; subst; monadInv Hl.
          rewrite add_whens_typeof.
          eapply typeofc_cexp in EQ0; eauto.
          eapply Forall_forall in H10; eauto; inv H10; eauto.
          eapply Forall_forall in H11; eauto. simpl in H11; rewrite app_nil_r in H11; auto.
        + econstructor. eapply wt_add_whens; eauto using wt_clock_l_ce.
          inv H11; try congruence. inv H10.
          eapply LT.wt_exps_wt_enum in H11; eauto.
          rewrite H1 in H11; inv H11; auto.
        + intros ? Hin.
          eapply in_map_iff in Hin as ((?&?)&Heq&Hin); simpl in *; inv Heq.
          rewrite<-BranchesSort.Permuted_sort in Hin.
          eapply mmap_inversion, Coqlib.list_forall2_in_right in EQ1 as ((?&?)&?&Hl); eauto.
          cases_eqn EQ; subst; monadInv Hl.
          eapply Forall_forall in H; eauto; simpl in *. apply Forall_singl in H.
          eapply H; eauto. eapply Forall_forall in H10; eauto; inv H10; auto.
      - inv Htr. cases_eqn H2; simpl in *; subst; monadInv H2. inv H6.
        econstructor; eauto.
        + eapply wt_lexp in EQ; eauto.
        + eapply typeof_lexp in EQ; eauto.
        + erewrite map_length, <-map_length.
          rewrite complete_branches_fst, seq_length; auto.
          * rewrite <-BranchesSort.Permuted_sort.
            erewrite fst_NoDupMembers, to_controls_fst, <-fst_NoDupMembers; eauto.
          * eapply Sorted.Sorted_StronglySorted, Sorted_impl, BranchesSort.Sorted_sort.
            intros (?&?) (?&?) (?&?) ??. lia.
            intros (?&?) (?&?) Ht; simpl in *. inv Ht.
            apply Nat.leb_le; auto.
          * rewrite <-BranchesSort.Permuted_sort.
            erewrite to_controls_fst; eauto.
        + intros ? Hin.
          eapply in_map_iff in Hin as ((?&?)&Heq&Hin); simpl in *; inv Heq.
          eapply complete_branches_In in Hin.
          rewrite <-BranchesSort.Permuted_sort in Hin.
          eapply mmap_inversion, Coqlib.list_forall2_in_right in EQ1 as ((?&?)&?&Hl); eauto.
          cases_eqn EQ; subst; monadInv Hl.
          eapply typeofc_cexp in EQ0; eauto. inv H13; eauto.
          eapply typeofc_cexp in EQ1; eauto.
          2:(eapply Forall_forall in H11; eauto; inv H11; eauto).
          2:(eapply Forall_forall in H12; eauto; simpl in H12; rewrite app_nil_r in H12; eauto).
          rewrite app_nil_r in *; subst; auto.
        + inv H13. inv H0. eauto.
        + intros ? Hin.
          eapply in_map_iff in Hin as ((?&?)&Heq&Hin); simpl in *; inv Heq.
          eapply complete_branches_In in Hin.
          rewrite <-BranchesSort.Permuted_sort in Hin.
          eapply mmap_inversion, Coqlib.list_forall2_in_right in EQ1 as ((?&?)&?&Hl); eauto.
          cases_eqn EQ; subst; monadInv Hl.
          eapply Forall_forall in H; eauto; simpl in *. apply Forall_singl in H.
          eapply H; eauto. eapply Forall_forall in H11; eauto; inv H11; auto.
    Qed.

    Lemma ty_lexp : forall env e e',
        LT.wt_exp G env e ->
        to_lexp e = OK e' ->
        L.typeof e = [CE.typeof e'].
    Proof.
      induction e using L.exp_ind2; intros * Hwt Htr; inv Htr.
      - now simpl.
      - now simpl.
      - destruct a. inv H0. now simpl.
      - destruct a. simpl. monadInv H0. now simpl.
      - destruct a. monadInv H0. now simpl.
      - cases. inv H. simpl. inv Hwt. inv H10. inv H5. monadInv H1.
        unfold L.typesof. unfold flat_map. simpl in *. rewrite app_nil_r in H11.
        eapply H3 in H2; eauto. congruence.
    Qed.

    Lemma wt_clock_of_suffix : forall enums vars lck cbase,
        LT.wt_clock enums vars cbase ->
        Forall (fun '(x, (ty, n)) => exists tn, ty = Tenum tn /\ In tn enums /\ Senv.HasType vars x ty /\ n < snd tn) lck ->
        LT.wt_clock enums vars (clock_of_suffix lck cbase).
    Proof.
      induction lck as [|(?&?&?)]; intros * Hbase Hlck; simpl; auto.
      inversion_clear Hlck as [|(?&?) ? Htn]; destruct Htn as ((?&?)&?&Henums&Hvars&Hinf); subst.
      eapply IHlck; eauto. constructor; auto.
    Qed.

    Lemma wt_suffix_of_clock : forall enums vars ck,
        LT.wt_clock enums vars ck ->
        Forall
          (fun '(x, (ty, n)) => exists tn, ty = Tenum tn /\ In tn enums /\ Senv.HasType vars x ty /\ n < snd tn)
          (suffix_of_clock ck []).
    Proof.
      intros *.
      assert (Forall (fun '(x, (ty, n)) => exists tn , ty = Tenum tn /\ In tn enums /\ Senv.HasType vars x ty /\ n < snd tn)
                     (@nil (ident * (type * enumtag))))
        as Hsuf by auto.
      revert Hsuf. generalize (@nil (ident * (type * enumtag))).
      induction ck; intros * Hsuf Hwt; inv Hwt; simpl.
      - assumption.
      - apply IHck; auto. constructor; eauto.
    Qed.

    Lemma incl_common_suffix :
      forall sfx1 sfx2,
        incl (common_suffix sfx1 sfx2) sfx1.
    Proof.
      intros * ? Hmem.
      revert dependent sfx2. induction sfx1 as [|[]]; simpl; intros; auto.
      cases. inv Hmem; eauto.
    Qed.

    Lemma wt_find_base_clock :
      forall enums vars lck,
        Forall (LT.wt_clock enums vars) lck ->
        LT.wt_clock enums vars (find_base_clock lck).
    Proof.
      unfold find_base_clock.
      destruct lck; intros * Hwt; inv Hwt; simpl. constructor.
      eapply wt_clock_of_suffix. constructor.
      specialize (wt_suffix_of_clock _ _ _ H1).
      generalize (suffix_of_clock c []).
      induction lck; intros * Hsuff; simpl; auto.
      inv H2. eapply IHlck; eauto.
      specialize (wt_suffix_of_clock _ _ _ H3) as Hsuff'.
      eapply Forall_incl; [|eapply incl_common_suffix; eauto]; eauto.
    Qed.

    Lemma wt_equation :
      forall P env envo xr vars e e',
        to_global G = OK P ->
        to_equation env envo xr e = OK e' ->
        (forall i ck, find_clock env i = OK ck -> LT.wt_clock P.(NL.enums) vars ck) ->
        Forall (fun xr0 => Senv.HasType vars xr0 bool_velus_type) (map fst xr) ->
        Forall (LT.wt_clock (L.enums G) vars) (map snd xr) ->
        Forall (LT.wt_enum G) (map (fun '(_, a) => a.(Senv.typ)) vars) ->
        NoDup (fst e) ->
        LT.wt_equation G vars e ->
        NLT.wt_equation P (Senv.idty vars) e'.
    Proof.
      Opaque to_cexp.
      intros ????? [xs [|? []]] e' Hg Htr Henvs Hxr Hckr Hen Hdup (Hwt & Hf2);
        try (inv Htr; cases; discriminate).
      apply Forall_singl in Hwt.
      destruct e; simpl in *; cases_eqn Eq; monadInv Htr.
      1-8,10-15:(simpl_Forall;
                 take (Senv.HasType _ _ _) and inv it;
                 econstructor;
                 [erewrite typeofc_cexp; eauto; solve_In|
                 eauto using wt_clock_l_ce|
                   erewrite to_global_enums; eauto; eapply wt_cexp; eauto];
                 take (In _ _) and clear it; simpl_Forall; eauto).
      1-9:simpl; try rewrite app_nil_r in *; try congruence.
      - simpl_Foralls. take (LT.wt_exp _ _ _) and inv it. simpl_Foralls.
        simpl in *. rewrite app_nil_r in *.
        constructor; eauto.
        + inv H2. erewrite typeof_lexp; eauto. solve_In.
          congruence.
        + rewrite <-H1 in H6. erewrite typeof_lexp; eauto.
          rewrite <-H1 in H7.
          erewrite to_global_enums; eauto. eapply wt_constant; eauto.
        + eapply Henvs in EQ0. eapply wt_clock_l_ce; eauto.
        + erewrite to_global_enums; eauto. eapply wt_lexp; eauto.
        + simpl_Forall. inv Hxr. split; solve_In; try congruence.
          erewrite to_global_enums; eauto. inv HwtG; eauto.
        + erewrite to_global_enums; eauto.
          eapply Forall_impl; [|eauto]. intros; eauto using wt_clock_l_ce.
      - rewrite app_nil_r in Hf2.
        simpl_Foralls.
        take (LT.wt_exp _ _ _) and inv it;
          assert (Hg':=Hg); eapply find_node_global in Hg' as (?&?&?); eauto.
        eapply vars_of_spec in Eq.
        apply mmap_inversion in EQ.
        econstructor; simpl; eauto; try erewrite to_global_enums; eauto.
        + erewrite <- (to_node_out n); eauto. rewrite Forall2_map_2 in Hf2. setoid_rewrite Forall2_map_2.
          apply Forall2_forall. split.
          2:{ repeat take (Forall2 _ _ _) and apply Forall2_length in it.
              rewrite it2; auto. }
          intros * Hin; destruct_conjs.
          eapply Forall2_chain_In in Hin; eauto.
          destruct Hin as (?&?& <-). inv H1. solve_In.
        + erewrite <- (to_node_in n); eauto.
          clear - HwtG H3 H6 EQ. setoid_rewrite Forall2_map_2.
          remember (L.n_in n). clear Heql0. revert dependent l0.
          revert dependent x.
          induction l; intros; inv EQ; auto.
          inv H6; auto.
          simpl_Foralls. eapply ty_lexp in H2; eauto. simpl in *.
          rewrite H2 in H6. inv H6. destruct y as (?&((?&?)&?)).
          constructor; eauto.
        + apply wt_clock_l_ce, wt_find_base_clock.
          clear H5 H6 H9 EQ.
          induction l; simpl; auto.
          inv H3. apply Forall_app.
          split; auto.
          apply LT.wt_exp_clockof in H5; auto.
        + clear H5 H6 H9. revert dependent l. induction x; intros; auto.
          inv EQ. simpl_Foralls.
          constructor; eauto using wt_lexp.
        + rewrite map_app, Forall_app; split.
          * simpl_Forall. inv Hxr. split; solve_In; try congruence.
            inv HwtG; auto.
          * eapply Forall2_ignore1 in Eq. simpl_Forall; subst.
            simpl in *. inv H8. inv H4; inv H11; split; auto; solve_In; try congruence.
            inv HwtG; auto.
        + rewrite map_app, Forall_app; split; auto.
          * simpl_Forall; eauto using wt_clock_l_ce.
          * eapply Forall2_ignore1 in Eq. simpl_Forall; subst.
            simpl in *. inv H4; auto using wt_clock_l_ce with clocks.
    Qed.

    Lemma wt_block_to_equation :
      forall P env envo d xr vars e' xs,
        to_global G = OK P ->
        block_to_equation env envo xr d = OK e' ->
        (forall i ck, find_clock env i = OK ck -> LT.wt_clock P.(NL.enums) vars ck) ->
        Forall (fun xr0 => Senv.HasType vars xr0 bool_velus_type) (map fst xr) ->
        Forall (LT.wt_clock (L.enums G) vars) (map snd xr) ->
        Forall (LT.wt_enum G) (map (fun '(_, a) => a.(Senv.typ)) vars) ->
        L.VarsDefined d xs ->
        NoDup xs ->
        LT.wt_block G vars d ->
        NLT.wt_equation P (Senv.idty vars) e'.
    Proof.
      induction d using L.block_ind2; intros * Hg Htr Henvs Hxr Hckr Hen Hvars Hdup Hwt;
        inv Hvars; inv Hwt; simpl in *; try congruence.
      - eapply wt_equation in Htr; eauto.
      - cases. apply Forall_singl in H. apply Forall_singl in H2.
        inv H6. inv H5; inv H4. inv H3; inv H9.
        simpl in Hdup; rewrite app_nil_r in Hdup.
        eapply H in Htr; eauto.
        1,2:constructor; eauto with senv.
    Qed.

    Lemma wt_clock_app :
      forall enums ck l l',
        LT.wt_clock enums l ck -> LT.wt_clock enums (l ++ l') ck.
    Proof.
      intros * Hwt.
      eapply LT.wt_clock_incl; [|eauto].
      intros. apply Senv.HasType_app; auto.
    Qed.

    Lemma wt_node :
      forall P n n',
        to_node n = OK n' ->
        to_global G = OK P ->
        LT.wt_node G n ->
        NLT.wt_node P n'.
    Proof.
      intros * Htr Hg (Wti& Wto & Wte & Hwt).
      tonodeInv Htr. unfold NLT.wt_node. simpl.
      pose proof (L.n_defd n) as (?&Hvars&Hperm). pose proof (L.n_nodup n) as (Hnd1&Hnd2).
      pose proof (L.n_syn n) as Hsyn. inv Hsyn. rename H into Hblk. rewrite <-Hblk in *. symmetry in Hblk.
      assert (Forall (fun blk => exists xs, L.VarsDefined blk xs /\ NoDup xs) blks) as Hvars'. 2:clear Hnd1 Hnd2 Hvars Hperm.
      { clear - Hnd1 Hnd2 Hvars Hperm.
        inv Hvars; inv H0; L.inv_VarsDefined.
        inv Hnd2; inv H1. apply Forall2_ignore2 in Hvars. simpl_Forall.
        do 2 esplit; eauto.
        eapply NoDup_concat; eauto. rewrite Hperm0, Hperm.
        apply NoDup_app'.
        - apply NoDupMembers_app_r in Hnd1. apply fst_NoDupMembers; eauto.
        - apply fst_NoDupMembers; auto.
        - eapply Forall_forall; intros * Hinm1 Hinm2. eapply fst_InMembers, H5 in Hinm2.
          apply Hinm2. rewrite map_app, in_app_iff; auto.
      }
      monadInv Hmmap.
      split.
      - inv Hwt. inv H3.
        eapply mmap_inversion in EQ.
        eapply envs_eq_node in Hblk.
        induction EQ; inv H1; inv H9; inv Hvars'; constructor; auto.
        destruct H9 as (?&?&?).
        eapply wt_block_to_equation in H3; eauto; simpl; auto.
        + simpl_app. repeat rewrite map_map in *; simpl in *.
          erewrite map_ext, map_ext with (l:=l), map_ext with (l:=L.n_out _), Permutation_app_comm with (l:=map _ l); eauto.
          1-3:intros; destruct_conjs; auto.
        + intros ?? Hfind.
          eapply envs_eq_find' in Hfind; eauto.
          erewrite to_global_enums; eauto.
          clear - Wti Wto H5 Hfind. unfold LT.wt_clocks, idty in *.
          simpl_In. repeat rewrite in_app_iff in Hin0. destruct Hin0 as [|[|]]; simpl_In; simpl_Forall; eauto.
          1,2:eapply LT.wt_clock_incl; [|eauto].
          1,2:intros; simpl_app; repeat rewrite Senv.HasType_app in *; intuition.
        + rewrite map_app. apply Forall_app; split; simpl_Forall; simpl_In; simpl_Forall; auto.
      - erewrite to_global_enums; eauto.
        clear - Wte Hwt. inv Hwt; inv H1. intros * Hin.
        simpl_app. repeat rewrite map_map in *; simpl in *.
        rewrite Forall_app in Wte. destruct Wte.
        repeat rewrite in_app_iff in Hin. destruct Hin as [|[|]]; simpl_In; simpl_Forall; eauto.
    Qed.

  End wt_node.

  Lemma wt_transcription :
    forall G P,
      LT.wt_global G ->
      to_global G = OK P ->
      NLT.wt_global P.
  Proof.
    intros (?&nds) ? (Hbool&Hwt). revert P.
    induction nds as [| n]. inversion 1. constructor.
    intros * Htr; simpl in *. monadInv Htr. simpl in *. monadInv EQ.
    inversion_clear Hwt as [|?? (Hwt'&Hnames) Hf ].
    constructor; simpl in *.
    - split.
      + eapply wt_node; eauto. constructor; auto.
        unfold to_global; simpl; rewrite EQ; simpl; auto.
      + erewrite to_node_name in Hnames; eauto.
        replace x1 with (NL.Global enums x1).(NL.nodes) by auto.
        eapply to_global_names with (G:=L.Global enums nds); eauto.
        unfold to_global; simpl; rewrite EQ; simpl; auto.
    - eapply IHnds in Hf; eauto.
      2:unfold to_global; simpl; erewrite EQ; simpl; auto.
      auto.
  Qed.

End TRTYPING.

Module TrTypingFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (OpAux: OPERATORS_AUX Ids Op)
       (Cks  : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (L    : LSYNTAX  Ids Op OpAux Cks Senv)
       (LT   : LTYPING  Ids Op OpAux Cks Senv L)
       (CE   : CESYNTAX Ids Op OpAux Cks)
       (CET  : CETYPING Ids Op OpAux Cks CE)
       (NL   : NLSYNTAX Ids Op OpAux Cks CE)
       (Ord  : NLORDERED Ids Op OpAux Cks CE     NL)
       (NLT  : NLTYPING  Ids Op OpAux Cks CE NL Ord CET)
       (TR   : TR Ids Op OpAux Cks Senv L CE NL)
<: TRTYPING Ids Op OpAux Cks Senv L LT CE CET NL Ord NLT TR.
  Include TRTYPING Ids Op OpAux Cks Senv L LT CE CET NL Ord NLT TR.
End TrTypingFun.
