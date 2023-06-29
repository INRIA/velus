From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LTyping.
From Velus Require Import Lustre.LClocking.
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
       (Senv        : STATICENV  Ids Op OpAux Cks)
       (L           : LSYNTAX    Ids Op OpAux Cks Senv)
       (LT          : LTYPING    Ids Op OpAux Cks Senv L)
       (LC          : LCLOCKING  Ids Op OpAux Cks Senv L)
       (Import CE   : CESYNTAX   Ids Op OpAux Cks)
       (NL          : NLSYNTAX   Ids Op OpAux Cks CE)
       (Import Ord  : NLORDERED  Ids Op OpAux Cks CE NL)
       (Import Mem  : MEMORIES   Ids Op OpAux Cks CE NL)
       (Import IsD  : ISDEFINED  Ids Op OpAux Cks CE NL Mem)
       (Import CEClo: CECLOCKING Ids Op OpAux Cks CE)
       (NLC         : NLCLOCKING Ids Op OpAux Cks CE NL Ord Mem IsD CEClo)
       (Import TR   : TR         Ids Op OpAux Cks Senv L CE NL).

  Module Completeness := CompletenessFun Ids Op OpAux Cks Senv L LT CE NL TR.

  (* Lemma envs_eq_in : *)
  (*   forall env cenv x ck, *)
  (*     envs_eq env cenv -> *)
  (*     find_clock env x = OK ck -> *)
  (*     In (x, ck) (Senv.idck cenv). *)
  (* Proof. *)
  (*   unfold find_clock, envs_eq. intros * Heq Hin. *)
  (*   cases_eqn HH. inv Hin. apply Heq; eauto. *)
  (* Qed. *)

  Lemma find_clock_det :
    forall env x ck ck',
      find_clock env x = OK ck ->
      find_clock env x = OK ck' ->
      ck = ck'.
  Proof.
    unfold find_clock. intros. cases. congruence.
  Qed.

  Definition idck (env : Senv.static_env) : list (ident * (clock * bool)) :=
    map (fun '(x, entry) => (x, (Senv.clo entry, isSome (Senv.causl_last entry)))) env.
  Global Hint Unfold idck : list.

  Section wc_node.
    Variable (G : @L.global L.normalized fby_prefs).
    Hypothesis HwcG : LC.wc_global G.

    Section wc_block.
      Variable vars : Senv.static_env.
      Hypothesis ND : NoDupMembers vars.

      Lemma wc_lexp :
        forall e e',
          to_lexp e = OK e' ->
          LC.wc_exp G vars e ->
          (exists ck,
              L.clockof e = [ck]
              /\ wc_exp (idck vars) e' ck).
      Proof.
        intros * Hto Hwc. revert dependent e'.
        induction e using L.exp_ind2; intros; inv Hto; inv Hwc.
        - exists Cbase. split; constructor.
        - exists Cbase. split; constructor.
        - simpl. esplit; split; eauto.
          monadInv H0. take (Senv.HasClock _ _ _) and inv it.
          econstructor. solve_In.
        - simpl. esplit; split; eauto.
          monadInv H0.
          take (Senv.HasClock _ _ _) and inv it. take (Senv.IsLast _ _) and inv it.
          eapply NoDupMembers_det in H; eauto; subst.
          econstructor. solve_In.
          destruct (Senv.causl_last _); try congruence; auto.
        - simpl. esplit; split; eauto.
          monadInv H0. constructor. apply IHe in EQ as (?&?&?); eauto.
          congruence.
        - simpl. esplit; split; eauto.
          monadInv H0. constructor.
          + apply IHe1 in EQ as (?&?&?); eauto. congruence.
          + apply IHe2 in EQ1 as (?&?&?); eauto. congruence.
        - cases.
          simpl. esplit; split; eauto.
          take (_ = OK e') and monadInv it. simpl_Foralls.
          take (Senv.HasClock _ _ _) and inv it.
          econstructor; eauto. 2:solve_In.
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

      Lemma wc_add_whens : forall ty ck,
          wc_clock (Senv.idck vars) ck ->
          wc_exp (idck vars) (add_whens (init_type ty) ty ck) ck.
      Proof.
        induction ck as [|??? (?&?)]; intros * Hwc; inv Hwc; simpl.
        - destruct ty; simpl; constructor.
        - simpl_In. econstructor; eauto. solve_In.
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

      Lemma wc_cexp : forall e e',
          to_cexp e = OK e' ->
          LT.wt_exp G vars e ->
          wc_env (Senv.idck vars) ->
          LC.wc_exp G vars e ->
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
        - simpl. esplit; split; eauto.
          inv Hwc. inv Hwt. simpl_Foralls. take (Senv.HasClock _ _ _) and inv it.
          econstructor; simpl; auto.
          + solve_In.
          + intro contra.
            assert (map snd x0 = nil) as Hnil.
            { eapply Permutation_nil. rewrite <-contra.
              apply Permutation_map, Permutation_sym, BranchesSort.Permuted_sort. }
            destruct es, x0; simpl in *; try congruence.
            apply H5; auto. monadInv EQ.
          + take Senv.annotation and destruct it. simpl in *.
            erewrite map_length, <-Permutation_length, <-map_length, to_controls_fst, map_length; eauto using BranchesSort.Permuted_sort.
            assert (Forall (fun '(i, e) => wc_cexp (idck vars) e (Con clo x1 (Tenum tx0 tn, i))) x0) as Hwc'.
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
                  erewrite H12. replace (Datatypes.length es) with (length tn); auto.
                  symmetry. erewrite <-map_length, H12, seq_length; auto.
                - apply Sorted.Sorted_StronglySorted. intros ?????; lia.
                  eapply Sorted_map, Sorted_impl, BranchesSort.Sorted_sort.
                  intros * Hleb. apply Nat.leb_le in Hleb; auto.
            }
            apply Forall2_combine''. 1:now rewrite 2 map_length.
            rewrite <-combine_fst_snd, <-BranchesSort.Permuted_sort; auto.
        - simpl in *. esplit; split; eauto.
          inv Hwc. inv Hwt. simpl_Foralls. constructor; simpl; auto.
          + eapply wc_lexp in EQ as (?&?&?); eauto.
            rewrite H0 in H7. now inv H7.
          + eapply to_controls_fst in EQ1.
            assert (x0 <> []) as Hnnil.
            { intro; subst; simpl in *. destruct es; simpl in *; congruence. }
            contradict Hnnil. apply map_eq_nil, complete_branches_eq_nil in Hnnil.
            eapply Permutation_nil. rewrite <-Hnnil. apply Permutation_sym, BranchesSort.Permuted_sort.
          + eapply Forall_singl, H4 in H12 as (?&?&?); eauto.
            specialize (H13 _ eq_refl); simpl in H13; rewrite app_nil_r in H13.
            rewrite H0 in H13; inv H13; auto.
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
            2:(eapply H9 in Hin2; simpl in Hin2; inv Hin2; auto).
            eapply H10 in Hin2; eauto; simpl in Hin2; rewrite app_nil_r, Hck in Hin2. inv Hin2; auto.
        - simpl in *. esplit; split; eauto.
          inv Hwc. inv Hwt. simpl_Foralls. constructor; simpl; auto.
          + eapply wc_lexp in EQ as (?&?&?); eauto.
            rewrite H1 in H7. now inv H7.
          + eapply to_controls_fst in EQ1.
            assert (x0 <> []) as Hnnil.
            { intro; subst; simpl in *. destruct es; simpl in *; congruence. }
            contradict Hnnil. apply map_eq_nil in Hnnil.
            eapply Permutation_nil. rewrite <-Hnnil. apply Permutation_sym, BranchesSort.Permuted_sort.
          + constructor. eapply wc_add_whens.
            eapply LC.wc_exp_clockof in H6; eauto.
            rewrite H7 in H6. apply Forall_singl in H6. auto.
          + intros ? Hin.
            eapply in_map_iff in Hin as ((?&?)&Heq&Hin); simpl in *; inv Heq.
            rewrite <-BranchesSort.Permuted_sort in Hin.
            eapply mmap_inversion, Coqlib.list_forall2_in_right in EQ1 as ((?&?)&Hin2&Hl); eauto.
            cases_eqn EQ; subst; monadInv Hl.
            rewrite Forall_forall in *.
            specialize (H _ Hin2); simpl in H. apply Forall_singl in H.
            eapply H in EQ0 as (?&Hck&Hwc); eauto.
            2:(eapply H19 in Hin2; simpl in Hin2; inv Hin2; auto).
            2:(eapply H9 in Hin2; simpl in Hin2; inv Hin2; auto).
            eapply H10 in Hin2; eauto; simpl in Hin2; rewrite app_nil_r, Hck in Hin2. inv Hin2; auto.
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

      (* We can't use [sub] directly because some variables
       in the left side of the equation may have no image bu [sub].
       -> see LClocking.wc_equation *)
      Lemma wc_equation_app_inputs (n : @L.node L.normalized fby_prefs) : forall n' bck sub xs es es',
          length (L.n_out n) = length xs ->
          Forall (LC.wc_exp G vars) es ->
          Forall2 (LC.WellInstantiated bck sub) (idsnd (idfst (L.n_in n))) (L.nclocksof es) ->
          to_node n = OK n' ->
          mmap to_lexp es = OK es' ->
          let sub' := fun x => match sub x with
                               | None => assoc_ident x (combine (map fst (L.n_out n)) xs)
                               | s => s
                               end in
          Forall2 (fun '(x0, (_, xck)) le => SameVar (sub' x0) le /\ (exists lck, wc_exp (idck vars) le lck /\ instck bck sub' xck = Some lck)) (NL.n_in n') es'.
      Proof.
        intros * Hlen Wce WIi Hton EQ.
        erewrite <-to_node_in; eauto.
        pose proof (L.n_nodup n) as (Hdup&_).
        remember (L.n_in n) as ins. clear Heqins.
        revert dependent ins.
        revert dependent es'.
        induction es as [| e].
        { intros. inv EQ. simpl in WIi. inv WIi.
          take ([] = _) and apply symmetry, map_eq_nil, map_eq_nil in it.
          subst; simpl; auto. }
        intros le Htr ins WIi.
        inv Htr. simpl in WIi. monadInv H0.
        take (Forall _ (e::_)) and inv it.
        take (to_lexp e = _) and pose proof it as Tolexp; eapply wc_lexp in it as (ck & Hck & Wce);
          eauto.
        rewrite L.clockof_nclockof in Hck.
        destruct (L.nclockof e) as [|nc []] eqn:Hcke; simpl in *; inv Hck.
        inversion WIi as [|???? Wi ? Hmap]. subst.
        unfold idsnd in Hmap.
        apply symmetry, map_cons'' in Hmap as ((?&(?&?))&?&?&?&?). subst.
        unfold LC.WellInstantiated in Wi. destruct Wi; simpl in *.
        destruct ins as [|(?&?&?)]; simpl in *; inv H0.
        constructor; eauto.
        2:{ eapply IHes; eauto. now inv Hdup. }
        split; simpl; eauto.
        2:{ exists (fst nc). split. apply Wce. auto using instck_sub_ext. }
        simpl in *. take (sub _ = _) and rewrite it. destruct nc as (ck & []).
        2:{ simpl.
            assert (assoc_ident i (combine (map fst (L.n_out n)) xs) = None) as Hassc.
            { apply assoc_ident_false.
              inv Hdup. contradict H5.
              apply InMembers_In_combine in H5.
              apply in_app_iff, or_intror; auto. }
            rewrite Hassc. constructor.
        }
        simpl. destruct e; take (LC.wc_exp G vars _) and inv it;
          inv Hcke; inv Tolexp.
        - constructor.
        - destruct tys; take (map _ _ = [_]) and inv it.
      Qed.

      Lemma wc_equation :
        forall P outs lasts env envo xr e e',
          to_global G = OK P ->
          to_equation env envo xr e = OK e' ->
          (forall x, Senv.IsLast vars x -> In x lasts) ->
          envs_eq env vars ->
          Forall (fun xr => In xr (Senv.idck vars)) xr ->
          L.normalized_equation outs lasts e ->
          LT.wt_equation G vars e ->
          wc_env (Senv.idck vars) ->
          LC.wc_equation G vars e ->
          NLC.wc_equation P (idck vars) e'.
      Proof.
        intros ?????? [xs [|? []]] e' Hg Htr Hlasts Henvs Hxr Hnorm Hwt Hwcenv Hwc;
          try (inv Htr; cases; discriminate).
        Opaque to_cexp.
        destruct e; inv Hwt; simpl in *; simpl_Foralls; cases_eqn Eq; try monadInv Htr.
        all:try (inv Hwc; simpl_Foralls;
                 eapply envs_eq_find in Henvs; eauto; rewrite Henvs in EQ; inv EQ; try rewrite app_nil_r in *;
                 take (Senv.HasClock _ _ _) and inv it;
                 econstructor; eauto; [eapply in_map_iff; do 2 esplit; eauto; simpl; auto; take (Senv.clo _ = _) and rewrite it; eauto|];
                 assert (Hwce:=EQ1); eapply wc_cexp in Hwce as (?&?&?); eauto;
                 simpl in *; econstructor; eauto; congruence).
        Transparent to_cexp.
        3:inv Hwc.
        - (* extcall *)
          inv Hwc. simpl_Forall.
          take (LC.wc_exp _ _ _) and inv it.
          take (Senv.HasClock _ _ _) and inv it. solve_In.
          repeat econstructor.
          + solve_In.
          + simpl_Forall.
            eapply mmap_inversion, Coqlib.list_forall2_in_right in EQ; eauto; destruct_conjs; simpl_Forall.
            eapply wc_lexp in H5 as (?&?&?); eauto.
            apply Forall_flat_map in H7. simpl_Forall. rewrite H5 in H7. simpl_Forall; auto.
        - (* fby *)
          inv Hnorm; [|inv H1; inv H]. inv Hwc. simpl_Forall.
          erewrite envs_eq_find in EQ0; eauto. inv EQ0.
          take (Senv.HasClock _ _ _) and inv it.
          assert (Senv.causl_last e1 = None) as Nlast.
          { destruct (Senv.causl_last e1) eqn:Causl; auto. exfalso.
            take (~In _ lasts) and apply it, Hlasts. econstructor; eauto. congruence. }
          constructor; eauto.
          + solve_In. rewrite Nlast. auto.
          + take (LC.wc_exp _ _ _) and inv it. simpl_Forall.
            eapply wc_lexp in EQ2 as (?& Heq &?); eauto.
            rewrite app_nil_r in *. congruence.
          + simpl_Forall. simpl_In. esplit. solve_In.
        - (* app (equation) *)
          rename Eq into Vars. eapply vars_of_spec in Vars.
          clear H0 H3.
          rename H9 into WIi. rename H10 into WIo. rename H12 into Hf2.
          eapply find_node_global in Hg as (n' & Hfind & Hton); eauto.
          assert (find_base_clock (L.clocksof l) = bck) as ->.
          { take (L.find_node _ _ = Some n) and apply LC.wc_find_node in it as (?&Wcn); eauto.
            inversion_clear Wcn as [? Wcin _ _].
            apply find_base_clock_bck.
            - rewrite L.clocksof_nclocksof; eapply LC.WellInstantiated_bck; eauto.
              rewrite map_length; exact (L.n_ingt0 n).
            - apply LC.WellInstantiated_parent in WIi.
              rewrite L.clocksof_nclocksof. simpl_Forall; eauto. }
          eapply NLC.CEqApp; eauto; try discriminate.
          + eapply wc_equation_app_inputs with (es:=l) (xs:=xs); eauto.
            apply Forall2_length in Hf2. apply Forall3_length in WIo as (WIo&?).
            unfold idfst, idsnd in *. repeat rewrite map_length in *. setoid_rewrite WIo; auto.
            unfold idsnd, idfst. simpl_Forall. eauto.
          + (* outputs *)
            unfold idsnd in *.
            erewrite <- (to_node_out n n'); eauto.
            unfold idfst in *. simpl_Forall. rewrite Forall3_map_1, Forall3_map_2 in WIo.
            eapply Forall2_swap_args, Forall3_ignore1', Forall3_Forall3 in Hf2. 2:eapply WIo.
            2:apply Forall3_length in WIo as (?&?); auto.
            eapply Forall3_ignore2 in Hf2. simpl_Forall.
            inversion_clear H1 as [Sub Inst]. simpl in *. rewrite Sub. split; auto.
            inv H2. do 2 esplit. split. solve_In.
            erewrite instck_sub_ext; eauto.
          + eapply Forall_app; split; eauto.
            2:eapply Forall2_ignore1 in Vars. 1,2:simpl_Forall.
            * simpl_In. esplit. solve_In.
            * subst. inv H7. take (Senv.HasClock _ _ _) and inv it. esplit. solve_In.
        - (* app (exp) *)
          rename Eq into Vars. eapply vars_of_spec in Vars.
          clear H0 H3.
          rename H4 into Hf2. simpl in Hf2; rewrite app_nil_r in Hf2. simpl_Forall.
          take (LC.wc_exp _ _ _) and inversion_clear it
            as [| | | | | | | | | | | |????? bck sub Wce Wcer ? WIi WIo Ckr].
          eapply find_node_global in Hg as (n' & Hfind & Hton); eauto.
          assert (find_base_clock (L.clocksof l) = bck) as ->.
          { take (L.find_node _ _ = Some n) and apply LC.wc_find_node in it as (?&Wcn); eauto.
            inversion_clear Wcn as [? Wcin _ _].
            apply find_base_clock_bck.
            - rewrite L.clocksof_nclocksof; eapply LC.WellInstantiated_bck; eauto.
              rewrite map_length; exact (L.n_ingt0 n).
            - apply LC.WellInstantiated_parent in WIi.
              rewrite L.clocksof_nclocksof. simpl_Forall; eauto. }
          eapply NLC.CEqApp; eauto; try discriminate.
          + eapply wc_equation_app_inputs with (es:=l) (xs:=xs); eauto.
            apply Forall2_length in Hf2. apply Forall2_length in WIo.
            1,2:unfold idfst, idsnd in *. repeat rewrite map_length in *. setoid_rewrite WIo; auto.
            simpl_Forall. eauto.
          + (* outputs *)
            unfold idsnd in *.
            erewrite <- (to_node_out n n'); eauto.
            clear - Hf2 WIo.
            replace (map _ (L.n_out n)) with (idsnd (idfst (idfst (L.n_out n)))) in WIo.
            2:{ unfold idfst, idsnd. erewrite 2 map_map, map_ext; eauto. intros; destruct_conjs; auto. }
            rewrite Forall2_map_2 in WIo.
            eapply Forall3_ignore1' in Hf2. eapply Forall3_ignore2' in WIo. eapply Forall3_Forall3 in WIo; eauto. clear Hf2.
            2:{ apply Forall3_length in Hf2 as (?&?). repeat rewrite map_length in *; auto. }
            2:{ apply Forall2_length in Hf2. apply Forall2_length in WIo. congruence. }
            apply Forall2_forall. split.
            2:{ apply Forall3_length in WIo as (?&?).
                unfold idsnd, idfst in *. repeat rewrite map_length in *. congruence. }
            intros (?&(?&?)) ? Hin. split.
            * destruct (sub i) eqn:Hsub.
              -- eapply Forall3_ignore3, Forall2_map_1, Forall2_combine, Forall_forall in WIo; eauto; simpl in *. destruct WIo as ((?&?)&?&Hsub'&?); simpl in *.
                 rewrite Hsub in Hsub'; auto. inv Hsub'.
              -- unfold L.idents. apply assoc_ident_true.
                 2:{ rewrite <-2 map_fst_idfst, combine_map_fst, in_map_iff.
                     esplit; split; eauto. now simpl. }
                 apply NoDup_NoDupMembers_combine.
                 pose proof (L.n_nodup n) as (Hdup&_); eauto using NoDup_app_r.
            * eapply Forall3_ignore3, Forall2_map_1, Forall2_combine, Forall_forall in WIo; eauto.
              destruct WIo as ((?&?)&?&?&?); simpl in *.
              take (Senv.HasClock _ _ _) and inv it.
              do 2 esplit; split; eauto using instck_sub_ext. solve_In.
          + eapply Forall_app; split; eauto.
            2:eapply Forall2_ignore1 in Vars. 1,2:simpl_Forall.
            * simpl_In. esplit. solve_In.
            * subst. inv Wcer. take (Senv.HasClock _ _ _) and inv it. esplit. solve_In.
      Qed.

      Lemma wc_block_to_equation :
        forall P outs lasts env envo d xr e',
          to_global G = OK P ->
          block_to_equation env envo xr d = OK e' ->
          (forall x, Senv.IsLast vars x -> In x lasts) ->
          envs_eq env vars ->
          Forall (fun xr => In xr (Senv.idck vars)) xr ->
          L.normalized_block outs lasts d ->
          LT.wt_block G vars d ->
          wc_env (Senv.idck vars) ->
          LC.wc_block G vars d ->
          NLC.wc_equation P (idck vars) e'.
      Proof.
        induction d using L.block_ind2; intros * Hg Htr Hlasts Henvs Hxr Hnorm Hwt Hwenv Hwc;
          inv Hnorm; inv Hwt; inv Hwc; simpl in *; try now inv Htr.
        - eapply wc_equation in Htr; eauto.
        - monadInv Htr.
          erewrite envs_eq_find in EQ; eauto. inv EQ.
          take (Senv.HasClock _ _ _) and inv it. take (Senv.IsLast _ _) and inv it.
          eapply NoDupMembers_det in H; eauto; subst.
          econstructor.
          + solve_In. destruct (Senv.causl_last _); try congruence; auto.
          + simpl_Forall. simpl_In.
            esplit. solve_In.
        - cases. simpl_Forall.
          repeat take ([_] = [_]) and inv it.
          eapply H3; eauto.
          constructor; auto.
          inv H8. take (Senv.HasClock _ _ _) and inv it. solve_In.
      Qed.

    End wc_block.

    Fact idsnd_idfst : forall (xs : list (_ * (type * clock * ident))),
        idsnd (idfst xs) = map (fun '(x, (_, ck, _)) => (x, ck)) xs.
    Proof.
      intros. unfold idsnd, idfst. rewrite map_map.
      eapply map_ext. intros; destruct_conjs; auto.
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
      inversion_clear Hwc as [? WCi WCo WCeq].
      inversion_clear Hwt as [????? WT]; subst Γ.
      pose proof (L.n_nodup n) as (Hnd1&Hnd2).
      pose proof (L.n_syn n) as Hsyn. inversion Hsyn as [??? Hsyn1 Hsyn2 _]; clear Hsyn. subst. rewrite <-H3 in *. symmetry in H3.
      eapply envs_eq_node in H3.
      monadInv Hmmap. inv WCeq; inv H5. inv WT; inv H5. subst Γ' Γ'0. inv Hnd2; inv H5.
      repeat split.
      - unfold idsnd, idfst. erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
      - unfold idsnd, idfst. erewrite map_app, 3 map_map, map_ext, map_ext with (l:=L.n_out _); eauto. 1,2:unfold L.decl; intros; destruct_conjs; auto.
      - rewrite (Permutation_app_comm (idfst (map _ l))), app_assoc. rewrite idsnd_app. apply Forall_app; split; auto.
        + unfold idsnd, idfst. erewrite map_app, 3 map_map, map_ext, map_ext with (l:=L.n_out _); eauto.
          simpl_Forall. eapply Forall_forall in WCo; [|eauto]. eapply Cks.wc_clock_incl; [|eauto]. apply incl_appl, incl_refl.
          1,2:unfold L.decl; intros; destruct_conjs; auto.
        + unfold L.decl. unfold idsnd, idfst. simpl_Forall. eapply Cks.wc_clock_incl; [|eauto].
          simpl_app. repeat rewrite map_map.
          erewrite map_ext, map_ext with (l:=L.n_out _), map_ext with (l:=l); try reflexivity.
          1-3:unfold L.decl; intros; destruct_conjs; auto.
      - eapply mmap_inversion in EQ.
        induction EQ; repeat (take (Forall _ (_::_)) and inv it); constructor; eauto.
        eapply wc_block_to_equation in H2; eauto.
        + clear - H2 Hsyn1. simpl_app.
          repeat rewrite map_map in *.
          erewrite map_ext, map_ext with (l:=l), map_ext_in with (l:=L.n_out _); eauto.
          1-3:unfold L.decl; intros; destruct_conjs; auto.
          simpl_Forall. subst. auto.
        + rewrite app_assoc. apply NoDupMembers_app; auto using L.node_NoDupMembers.
          * now apply Senv.NoDupMembers_senv_of_decls.
          * intros * InM1 InM2. apply Senv.InMembers_senv_of_decls in InM2. eapply H14; eauto.
            rewrite fst_InMembers, map_app, Senv.map_fst_senv_of_ins, Senv.map_fst_senv_of_decls in InM1; auto.
        + intros * Il. rewrite 2 Senv.IsLast_app in Il. destruct Il as [Il|[Il|Il]]; inv Il; simpl_In.
          * congruence.
          * simpl_Forall. contradiction.
          * unfold L.lasts_of_decls. solve_In. simpl. destruct o; try congruence. auto.
        + take (LT.wt_block _ _ _) and rewrite <-app_assoc in it; auto.
        + clear - WCo H7. repeat simpl_app. repeat erewrite map_map in *.
          erewrite map_ext, map_ext with (l:=L.n_out n), app_assoc.
          apply Forall_app; split; simpl_Forall; simpl_In; simpl_Forall.
          * eapply Forall_forall in WCo; [|eauto].
            eapply Cks.wc_clock_incl; [|eauto]. apply incl_appl, incl_refl.
          * eapply Cks.wc_clock_incl; [|eauto].
            simpl_app. erewrite map_ext, map_ext with (l:=L.n_out n). reflexivity.
            1,2:unfold L.decl; intros; destruct_conjs; auto.
          * unfold L.decl; intros; destruct_conjs; auto.
          * unfold L.decl; intros; destruct_conjs; auto.
        + take (LC.wc_block _ _ _) and rewrite <-app_assoc in it; auto.
    Qed.

  End wc_node.

  Lemma wc_transcription :
    forall G P,
      LT.wt_global G ->
      LC.wc_global G ->
      to_global G = OK P ->
      NLC.wc_global P.
  Proof.
    intros [] ? (_&Hwt). revert P Hwt.
    induction nodes as [| n]. inversion 3. constructor.
    intros * Hwt Hwc Htr. monadInv Htr; simpl in *; monadInv EQ.
    inversion_clear Hwt as [|?? (?&?) Wt ].
    inversion_clear Hwc as [|?? (?&?) Wc ].
    constructor; simpl.
    - eapply wc_node; eauto; simpl; auto.
      unfold to_global; simpl; rewrite EQ; simpl; auto.
    - eapply IHnodes in Wc; eauto.
      2:(unfold to_global; simpl; rewrite EQ; simpl; auto).
      apply Wc.
  Qed.

End TRCLOCKING.

Module TrClockingFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (OpAux: OPERATORS_AUX  Ids Op)
       (Cks  : CLOCKS     Ids Op OpAux)
       (Senv : STATICENV  Ids Op OpAux Cks)
       (L    : LSYNTAX    Ids Op OpAux Cks Senv)
       (LT   : LTYPING    Ids Op OpAux Cks Senv L)
       (LC   : LCLOCKING  Ids Op OpAux Cks Senv L)
       (CE   : CESYNTAX   Ids Op OpAux Cks)
       (NL   : NLSYNTAX   Ids Op OpAux Cks CE)
       (Ord  : NLORDERED  Ids Op OpAux Cks CE NL)
       (Mem  : MEMORIES   Ids Op OpAux Cks CE NL)
       (IsD  : ISDEFINED  Ids Op OpAux Cks CE NL Mem)
       (CEClo: CECLOCKING Ids Op OpAux Cks CE)
       (NLC  : NLCLOCKING Ids Op OpAux Cks CE NL Ord Mem IsD CEClo)
       (TR   : TR         Ids Op OpAux Cks Senv L CE NL)
<: TRCLOCKING Ids Op OpAux Cks Senv L LT LC CE NL Ord Mem IsD CEClo NLC TR.
  Include TRCLOCKING Ids Op OpAux Cks Senv L LT LC CE NL Ord Mem IsD CEClo NLC TR.
End TrClockingFun.
