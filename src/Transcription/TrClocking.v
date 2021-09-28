From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LTyping.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Lustre.Normalization.Normalization.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.
From Velus Require Import Transcription.Completeness.

From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLClocking.

From Coq Require Import String.
From Coq Require Import Permutation.

From Coq Require Import List.
Import List.ListNotations.

From compcert Require Import common.Errors.
Open Scope error_monad_scope.

(** * Clocking Preservation for Transcription *)


Module Type TRCLOCKING
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX  Ids Op)
       (Import Cks  : CLOCKS     Ids Op OpAux)
       (L           : LSYNTAX    Ids Op OpAux Cks)
       (LT          : LTYPING    Ids Op OpAux Cks L)
       (LC          : LCLOCKING  Ids Op OpAux Cks L)
       (Import CE   : CESYNTAX   Ids Op OpAux Cks)
       (NL          : NLSYNTAX   Ids Op OpAux Cks CE)
       (Import Ord  : NLORDERED  Ids Op OpAux Cks CE NL)
       (Import Mem  : MEMORIES   Ids Op OpAux Cks CE NL)
       (Import IsD  : ISDEFINED  Ids Op OpAux Cks CE NL Mem)
       (Import CEClo: CECLOCKING Ids Op OpAux Cks CE)
       (NLC         : NLCLOCKING Ids Op OpAux Cks CE NL Ord Mem IsD CEClo)
       (Import TR   : TR         Ids Op OpAux Cks L CE NL).

  Module Norm := NormalizationFun Ids Op OpAux Cks L.
  Module Completeness := CompletenessFun Ids Op OpAux Cks L LT Norm CE NL TR.

  Lemma envs_eq_in :
    forall env cenv x ck,
      envs_eq env cenv ->
      find_clock env x = OK ck ->
      In (x, ck) cenv.
  Proof.
    unfold find_clock, envs_eq. intros * Heq Hin.
    cases_eqn HH. inv Hin. apply Heq; eauto.
  Qed.

  Lemma find_clock_det :
    forall env x ck ck',
      find_clock env x = OK ck ->
      find_clock env x = OK ck' ->
      ck = ck'.
  Proof.
    unfold find_clock. intros. cases. congruence.
  Qed.

  Section wc_node.
    Variable (G : @L.global L.nolocal_top_block norm2_prefs).
    Hypothesis HwcG : LC.wc_global G.

    Lemma wc_lexp :
      forall vars e e',
        to_lexp e = OK e' ->
        LC.wc_exp G vars e ->
        (exists ck,
            L.clockof e = [ck]
            /\ wc_exp vars e' ck).
    Proof.
      intros * Hto Hwc. revert dependent e'.
      induction e using L.exp_ind2; intros; inv Hto; inv Hwc.
      - exists Cbase. split; constructor.
      - exists Cbase. split; constructor.
      - simpl. unfold L.clock_of_nclock, stripname. simpl. esplit; split; eauto.
        monadInv H0. now constructor.
      - simpl. unfold L.clock_of_nclock, stripname. simpl. esplit; split; eauto.
        monadInv H0. now constructor.
      - simpl. unfold L.clock_of_nclock, stripname. simpl. esplit; split; eauto.
        monadInv H0. constructor. apply IHe in EQ as (?&?&?); eauto.
        congruence.
      - simpl. unfold L.clock_of_nclock, stripname. simpl. esplit; split; eauto.
        monadInv H0. constructor.
        + apply IHe1 in EQ as (?&?&?); eauto. congruence.
        + apply IHe2 in EQ1 as (?&?&?); eauto. congruence.
      - cases.
        simpl. unfold L.clock_of_nclock, stripname. simpl. esplit; split; eauto.
        take (_ = OK e') and monadInv it. simpl_Foralls.
        constructor; auto.
        take (_ -> _) and apply it in EQ as (?& Heq &?); auto.
        unfold L.clocksof in *. simpl in *. rewrite app_nil_r in *.
        rewrite Heq in *. simpl_Foralls. congruence.
    Qed.

    Lemma wc_exp_cexp :
      forall vars e ck,
        wc_exp vars e ck ->
        wc_cexp vars (Eexp e) ck.
    Proof.
      now constructor.
    Qed.

    Lemma wc_add_whens vars : forall ty ck,
        wc_clock vars ck ->
        wc_exp vars (add_whens (init_type ty) ty ck) ck.
    Proof.
      induction ck as [|??? (?&?)]; intros * Hwc; inv Hwc; simpl.
      - destruct ty; simpl; constructor.
      - constructor; auto.
    Qed.

    Fact complete_branches_eq_nil : forall s es,
        complete_branches s es = [] ->
        es = [].
    Proof.
      induction s; intros * Hcomp; simpl in *; auto.
      - apply map_eq_nil in Hcomp; auto.
      - destruct es as [|(?&?)]; simpl in *; auto.
        destruct (e =? a); inv Hcomp.
    Qed.

    Lemma wc_cexp : forall vars e e',
        to_cexp e = OK e' ->
        LT.wt_exp G (idty vars) e ->
        wc_env (idck vars) ->
        LC.wc_exp G (idck vars) e ->
        (exists ck,
            L.clockof e = [ck]
            /\ wc_cexp (idck vars) e' ck).
    Proof.
      intros * Hto Hwt Hwenv Hwc. revert dependent e'.
      Opaque to_lexp.
      induction e using L.exp_ind2; intros;
        simpl in *; try monadInv Hto;
          try (take (to_lexp _ = _) and eapply wc_lexp in it as (?&?&?);
               eauto); eauto using wc_exp_cexp.
      Transparent to_lexp.
      1-2:cases; monadInv Hto.
      - simpl. unfold L.clock_of_nclock, stripname. simpl. esplit; split; eauto.
        inv Hwc. inv Hwt. simpl_Foralls. constructor; simpl; auto.
        + intro contra.
          assert (map snd x0 = nil) as Hnil.
          { eapply Permutation_nil. rewrite <-contra.
            apply Permutation_map, Permutation_sym, BranchesSort.Permuted_sort. }
          destruct es, x0; simpl in *; try congruence.
          apply H5; auto. monadInv EQ.
        + erewrite map_length, <-Permutation_length, <-map_length, to_controls_fst, map_length; eauto using BranchesSort.Permuted_sort.
          assert (Forall (fun '(i, e) => wc_cexp (idck vars) e (Con ck x1 (Tenum tn, i))) x0) as Hwc'.
          { eapply Forall_forall; intros (?&?) Hin.
            eapply mmap_inversion, Coqlib.list_forall2_in_right in EQ as ((?&?)&Hin2&Htr); eauto.
            cases; monadInv Htr.
            rewrite Forall_forall in *.
            specialize (H _ Hin2); simpl in H. apply Forall_singl in H.
            eapply H in EQ as (?&Hck&Hwc); eauto.
            2:(eapply H14 in Hin2; simpl in Hin2; inv Hin2; auto).
            2:(eapply H6 in Hin2; simpl in Hin2; inv Hin2; auto).
            eapply H7 in Hin2; simpl in Hin2; rewrite app_nil_r in Hin2.
            rewrite Hck in Hin2. apply Forall_singl in Hin2; subst; auto.
          }
          replace (seq 0 (Datatypes.length es)) with (map fst (BranchesSort.sort x0)).
          2:{ eapply Permutation_seq_eq.
              - erewrite <-BranchesSort.Permuted_sort, to_controls_fst; eauto.
                erewrite H12. replace (Datatypes.length es) with (snd tn); auto.
                erewrite <-map_length, H12, seq_length; auto.
              - apply Sorted.Sorted_StronglySorted. intros ?????; lia.
                eapply Sorted_map, Sorted_impl, BranchesSort.LocallySorted_sort.
                intros * Hleb. apply Nat.leb_le in Hleb; auto.
          }
          apply Forall2_combine''. 1:now rewrite 2 map_length.
          rewrite <-combine_fst_snd, <-BranchesSort.Permuted_sort; auto.
      - simpl in *. unfold L.clock_of_nclock, stripname. simpl. esplit; split; eauto.
        inv Hwc. inv Hwt. simpl_Foralls. constructor; simpl; auto.
        + eapply wc_lexp in EQ as (?&?&?); eauto.
          rewrite H0 in H8. now inv H8.
        + eapply to_controls_fst in EQ1.
          assert (x0 <> []) as Hnnil.
          { intro; subst; simpl in *. destruct es; simpl in *; congruence. }
          contradict Hnnil. apply map_eq_nil, complete_branches_eq_nil in Hnnil.
          eapply Permutation_nil. rewrite <-Hnnil. apply Permutation_sym, BranchesSort.Permuted_sort.
        + eapply Forall_singl, H4 in H13 as (?&?&?); eauto.
          specialize (H14 _ eq_refl); simpl in H14; rewrite app_nil_r in H14.
          rewrite H0 in H14; inv H14; auto.
        + intros ? Hin.
          eapply in_map_iff in Hin as ((?&?)&Heq&Hin); simpl in *; inv Heq.
          eapply complete_branches_In in Hin.
          rewrite <-BranchesSort.Permuted_sort in Hin.
          eapply mmap_inversion, Coqlib.list_forall2_in_right in EQ1 as ((?&?)&Hin2&Hl); eauto.
          cases_eqn EQ; subst; monadInv Hl.
          rewrite Forall_forall in *.
          specialize (H _ Hin2); simpl in H. apply Forall_singl in H.
          eapply H in EQ1 as (?&Hck&Hwc); eauto.
          2:(eapply H21 in Hin2; simpl in Hin2; inv Hin2; auto).
          2:(eapply H10 in Hin2; simpl in Hin2; inv Hin2; auto).
          eapply H11 in Hin2; eauto; simpl in Hin2; rewrite app_nil_r, Hck in Hin2. inv Hin2; auto.
      - simpl in *. unfold L.clock_of_nclock, stripname. simpl. esplit; split; eauto.
        inv Hwc. inv Hwt. simpl_Foralls. constructor; simpl; auto.
        + eapply wc_lexp in EQ as (?&?&?); eauto.
          rewrite H1 in H8. now inv H8.
        + eapply to_controls_fst in EQ1.
          assert (x0 <> []) as Hnnil.
          { intro; subst; simpl in *. destruct es; simpl in *; congruence. }
          contradict Hnnil. apply map_eq_nil in Hnnil.
          eapply Permutation_nil. rewrite <-Hnnil. apply Permutation_sym, BranchesSort.Permuted_sort.
        + constructor. eapply wc_add_whens.
          eapply LC.wc_exp_clockof in H7; eauto.
          rewrite H8 in H7. apply Forall_singl in H7.
          eapply Completeness.to_lexp_normalized, Norm.Unnesting.normalized_lexp_no_fresh in EQ.
          rewrite EQ in H7; simpl in H7. now rewrite app_nil_r in H7.
        + intros ? Hin.
          eapply in_map_iff in Hin as ((?&?)&Heq&Hin); simpl in *; inv Heq.
          rewrite <-BranchesSort.Permuted_sort in Hin.
          eapply mmap_inversion, Coqlib.list_forall2_in_right in EQ1 as ((?&?)&Hin2&Hl); eauto.
          cases_eqn EQ; subst; monadInv Hl.
          rewrite Forall_forall in *.
          specialize (H _ Hin2); simpl in H. apply Forall_singl in H.
          eapply H in EQ0 as (?&Hck&Hwc); eauto.
          2:(eapply H19 in Hin2; simpl in Hin2; inv Hin2; auto).
          2:(eapply H10 in Hin2; simpl in Hin2; inv Hin2; auto).
          eapply H11 in Hin2; eauto; simpl in Hin2; rewrite app_nil_r, Hck in Hin2. inv Hin2; auto.
    Qed.

    (* correctness of substition extension *)
    Lemma instck_sub_ext :
      forall bck sub ck ck' P,
        instck bck sub ck = Some ck' ->
        instck bck (fun x => match sub x with
                          | None => P x
                          | s => s
                          end) ck = Some ck'.
    Proof.
      intros * Hinst.
      revert dependent ck'. induction ck; intros; auto.
      inv Hinst.
      destruct (instck bck sub ck) eqn:?; try discriminate.
      destruct (sub i) eqn:Hs; try discriminate.
      specialize (IHck c eq_refl).
      simpl. now rewrite IHck, Hs.
    Qed.

    Lemma wc_equation :
      forall P env envo xr vars e e',
        to_global G = OK P ->
        to_equation env envo xr e = OK e' ->
        envs_eq env (idck vars) ->
        Forall (fun xr => In xr (idck vars)) xr ->
        LT.wt_equation G (idty vars) e ->
        wc_env (idck vars) ->
        LC.wc_equation G (idck vars) e ->
        NLC.wc_equation P (idck vars) e'.
    Proof.
      intros ????? [xs [|? []]] e' Hg Htr Henvs Hxr Hwt Hwcenv (Hwc & Hlift & Hf2);
        try (inv Htr; cases; discriminate).
      Opaque to_cexp.
      destruct e; inv Hwt; simpl in *; simpl_Foralls; cases_eqn Eq; try monadInv Htr.
      1-7,9-14:(constructor; eauto using envs_eq_in;
                assert (Hwce:=EQ1); eapply wc_cexp in Hwce as (?&?&?); eauto).
      Transparent to_cexp.
      1-13:try (solve [monadInv EQ1]).
      1-8:simpl in *.
      1-5:(eapply envs_eq_find in Henvs; eauto;
           pose proof (find_clock_det _ _ _ _ EQ Henvs) as ->; congruence).
      1-3:(cases; monadInv EQ1; simpl in *;
           inv H; inv Hf2;
           (eapply envs_eq_find in Henvs; eauto;
            pose proof (find_clock_det _ _ _ _ EQ Henvs) as ->; congruence)).
      - cases; try monadInv Htr.
        constructor; eauto using envs_eq_in.
        take (LC.wc_exp _ _ _) and inv it. simpl_Foralls.
        eapply wc_lexp in EQ2 as (?& Heq &?); eauto.
        take (Forall2 eq _ _) and rewrite Forall2_eq in it.
        unfold L.clocksof in it. simpl in *. rewrite app_nil_r in *.
        rewrite Heq in it. rewrite it in *.
        eapply envs_eq_find in Henvs; eauto.
        pose proof (find_clock_det _ _ _ _ EQ0 Henvs) as ->.
        congruence.
      - rename Eq into Vars. eapply vars_of_spec in Vars.
        clear H0 H3.
        take (LC.wc_exp _ _ _) and inversion_clear it
          as [| | | | | | | | | | |????? bck sub Wce Wcer ? WIi WIo].
        eapply find_node_global in Hg as (n' & Hfind & Hton); eauto;
          assert (find_base_clock (L.clocksof l) = bck) as ->
            by (take (L.find_node _ _ = Some n) and
                     pose proof (LC.wc_find_node _ _ n HwcG it) as (?& (Wcin &?));
                apply find_base_clock_bck;
                [rewrite L.clocksof_nclocksof; eapply LC.WellInstantiated_bck; eauto;
                 unfold idck; rewrite map_length, length_idty; exact (L.n_ingt0 n)
                | apply LC.WellInstantiated_parent in WIi;
                  rewrite L.clocksof_nclocksof, Forall_map;
                  eapply Forall_impl; eauto; now simpl]).
        econstructor; eauto; try discriminate;
          rewrite app_nil_r in *.
        (* We can't use [sub] directly because some variables
           in the left side of the equation may have no image bu [sub].
           -> see LClocking.wc_equation *)
        + instantiate (1 := fun x => match sub x with
                                  | None => assoc_ident x (combine (L.idents (L.n_out n)) xs)
                                  | s => s
                                  end).
          (* inputs *)
          erewrite <- (to_node_in n n'); eauto.
          apply mmap_inversion in EQ.
          pose proof (L.n_nodup n) as (Hdup&_).
          remember (L.n_in n) as ins. clear Heqins.
          revert dependent ins.
          revert dependent x.
          induction l as [| e].
          { intros. inv EQ. simpl in WIi. inv WIi.
            take ([] = _) and apply symmetry, map_eq_nil, map_eq_nil in it.
            subst; simpl; auto. }
          intros le Htr ins WIi.
          inv Htr. simpl in WIi.
          take (Forall _ (e::_)) and inv it.
          take (to_lexp e = _) and pose proof it as Tolexp; eapply wc_lexp in it as (ck & Hck & Wce);
            eauto.
          rewrite L.clockof_nclockof in Hck.
          destruct (L.nclockof e) as [|nc []] eqn:Hcke; simpl in *; inv Hck.
          inversion WIi as [|???? Wi ? Hmap]. subst.
          unfold idck in Hmap.
          apply symmetry, map_cons'' in Hmap as ((?&(?&?))&?&?&?&?). subst.
          unfold LC.WellInstantiated in Wi. destruct Wi; simpl in *.
          destruct ins as [|(?&?&?)]; simpl in *; inv H2.
          constructor; eauto.
          2:{ eapply IHl; eauto. now apply nodupmembers_cons in Hdup. }
          split; simpl; eauto.
          2:{ exists (stripname nc). split. apply Wce. auto using instck_sub_ext. }
          simpl in *. take (sub _ = _) and rewrite it. destruct nc as (ck & []).
          2:{ simpl.
              rewrite assoc_ident_false. constructor.
              apply nodupmembers_cons in Hdup as [Hin].
              rewrite <- In_InMembers_combine. unfold L.idents. intro Hin'.
              apply in_map_iff in Hin' as ((?&?)&?&?). simpl in *. subst.
              eapply Hin, In_InMembers.
              rewrite idty_app. repeat rewrite in_app_iff. left; right. eapply in_map_iff; do 2 esplit; eauto; auto.
              apply Forall2_length in Hf2. apply Forall2_length in WIo.
              unfold L.idents, idck in *. repeat rewrite map_length in *. rewrite length_idty in WIo.
              congruence.
          }
          simpl. destruct e; take (LC.wc_exp G (idck vars) _) and inv it;
                   inv Hcke; inv Tolexp.
          * constructor.
          * destruct tys; take (map _ _ = [_]) and inv it.
        + (* outputs *)
          unfold idck in *.
          erewrite <- (to_node_out n n'); eauto.
          clear - Hlift Hf2 WIo.
          apply Forall2_forall. split.
          2:{ apply Forall2_length in Hlift. apply Forall2_length in WIo.
              repeat rewrite map_length in *. congruence. }
          intros (?&(?&?)) ? Hin. split.
          * destruct (sub i) eqn:Hsub.
            apply Forall2_swap_args in Hlift.
            pose proof (Forall2_trans_ex _ _ _ _ _ WIo Hlift) as Ho.
            rewrite Forall2_map_1 in Ho.
            eapply Forall2_In in Hin; eauto.
            destruct Hin as (?&?&(Heq&?)&Hl). simpl in *.
            rewrite Hsub in Heq. rewrite <- Heq in Hl. simpl in Hl.
            now subst.
            unfold L.idents. apply assoc_ident_true.
            2:{ rewrite <-map_fst_idty, combine_map_fst, in_map_iff.
                esplit; split; eauto. now simpl. }
            apply NoDup_NoDupMembers_combine.
            pose proof (L.n_nodup n) as (Hdup&_).
            rewrite fst_NoDupMembers, map_app, map_fst_idty in Hdup. repeat rewrite map_app in Hdup.
            eauto using NoDup_app_l, NoDup_app_r.
          * rewrite Forall2_map_2 in Hf2. rewrite Forall2_map_2 in WIo.
            apply Forall2_swap_args in Hf2.
            pose proof (Forall2_trans_ex _ _ _ _ _ WIo Hf2) as Ho.
            rewrite Forall2_map_1 in Ho.
            eapply Forall2_In in Hin; eauto.
            destruct Hin as (?&?&(Heq&?)&Hl). simpl in *.
            esplit; split; eauto.
            eauto using instck_sub_ext.
        + eapply Forall_app; split; eauto.
          eapply Forall2_ignore1 in Vars.
          eapply Forall_impl; [|eauto]. intros (?&?) (?&?&?&?&?); subst.
          eapply Forall_forall in Wcer; eauto. inv Wcer; auto.
    Qed.

    Lemma wc_block_to_equation :
      forall P env envo d xr vars e',
        to_global G = OK P ->
        block_to_equation env envo xr d = OK e' ->
        envs_eq env (idck vars) ->
        Forall (fun xr => In xr (idck vars)) xr ->
        LT.wt_block G (idty vars) d ->
        wc_env (idck vars) ->
        LC.wc_block G (idck vars) d ->
        NLC.wc_equation P (idck vars) e'.
    Proof.
      induction d using L.block_ind2; intros * Hg Htr Henvs Hxr Hwt Hwenv Hwc;
        inv Hwt; inv Hwc; simpl in *.
      - eapply wc_equation in Htr; eauto.
      - cases. apply Forall_singl in H. apply Forall_singl in H2. apply Forall_singl in H3.
        eapply H; eauto.
        constructor; auto.
        inv H7; auto.
      - inv Htr.
    Qed.

    Lemma wc_node :
      forall P n n',
        to_node n = OK n' ->
        to_global G = OK P ->
        LT.wt_node G n ->
        LC.wc_node G n ->
        NLC.wc_node P n'.
    Proof.
      intros * Htn Htg Hwt Hwc.
      tonodeInv Htn. unfold NLC.wc_node. simpl.
      inversion Hwc as (WCi&WCo&WCeq). rewrite idty_app in WCo.
      inversion_clear Hwt as (_&_&_&WT).
      cases_eqn Hblk. eapply envs_eq_node in Hblk.
      monadInv Hmmap.
      repeat (split; try tauto).
      - inv WCeq. rewrite Forall_map in H3.
        rewrite (Permutation_app_comm (idty l)), app_assoc, idck_app. apply Forall_app; split; auto.
        1,2:(eapply Forall_impl; [|eauto]; simpl in *; intros;
             eapply LC.wc_clock_incl; [|eauto]; unfold idty, idck;
             repeat rewrite map_app; repeat rewrite map_map; solve_incl_app).
      - inv WCeq. inv WT.
        eapply mmap_inversion in EQ.
        induction EQ; inv H1; inv H2; constructor; eauto.
        eapply wc_block_to_equation; eauto.
        + repeat rewrite <-idty_app; eauto.
        + eapply LT.wt_block_incl; [|eauto]. rewrite (Permutation_app_comm (idty l)).
          unfold idty. solve_incl_app.
        + unfold wc_env. rewrite (Permutation_app_comm (idty l)), 2 app_assoc, 3 idck_app.
          apply Forall_app; split.
          * eapply Forall_impl; [|eauto]. intros (?&?) ?.
            eapply LC.wc_clock_incl; [|eauto]. unfold idty, idck; solve_incl_app.
          * rewrite Forall_map in H3. eapply Forall_impl; [|eauto]. intros (?&?) ?.
            eapply LC.wc_clock_incl; [|eauto].
            rewrite <-app_assoc, (Permutation_app_comm (idck (idty l))). unfold idty, idck. simpl_app. reflexivity.
        + rewrite (Permutation_app_comm (idty l)).
          now rewrite app_assoc, idck_app, <-idty_app.
    Qed.

  End wc_node.

  Lemma wc_transcription :
    forall G P,
      LT.wt_global G ->
      LC.wc_global G ->
      to_global G = OK P ->
      NLC.wc_global P.
  Proof.
    intros (?&nds) ? (_&Hwt). revert P Hwt.
    induction nds as [| n]. inversion 3. constructor.
    intros * Hwt Hwc Htr. monadInv Htr; simpl in *; monadInv EQ.
    inversion_clear Hwt as [|?? (?&?) Wt ].
    inversion_clear Hwc as [|?? (?&?) Wc ].
    constructor; simpl.
    - eapply wc_node; eauto; simpl; auto.
      unfold to_global; simpl; rewrite EQ; simpl; auto.
    - eapply IHnds in Wc; eauto.
      2:(unfold to_global; simpl; rewrite EQ; simpl; auto).
      apply Wc.
  Qed.

End TRCLOCKING.

Module TrClockingFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (OpAux: OPERATORS_AUX  Ids Op)
       (Cks  : CLOCKS     Ids Op OpAux)
       (L    : LSYNTAX    Ids Op OpAux Cks)
       (LT   : LTYPING    Ids Op OpAux Cks L)
       (LC   : LCLOCKING  Ids Op OpAux Cks L)
       (CE   : CESYNTAX   Ids Op OpAux Cks)
       (NL   : NLSYNTAX   Ids Op OpAux Cks CE)
       (Ord  : NLORDERED  Ids Op OpAux Cks CE NL)
       (Mem  : MEMORIES   Ids Op OpAux Cks CE NL)
       (IsD  : ISDEFINED  Ids Op OpAux Cks CE NL Mem)
       (CEClo: CECLOCKING Ids Op OpAux Cks CE)
       (NLC  : NLCLOCKING Ids Op OpAux Cks CE NL Ord Mem IsD CEClo)
       (TR   : TR         Ids Op OpAux Cks L CE NL)
<: TRCLOCKING Ids Op OpAux Cks L LT LC CE NL Ord Mem IsD CEClo NLC TR.
  Include TRCLOCKING Ids Op OpAux Cks L LT LC CE NL Ord Mem IsD CEClo NLC TR.
End TrClockingFun.
