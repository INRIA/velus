From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Lustre.SubClock.SubClock.

Module Type SCCLOCKING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import SC : SUBCLOCK Ids Op OpAux Cks Senv Syn).

  Section subclock_nclockof.

    Variable bck : clock.
    Variable sub subl : Env.t ident.

    Lemma add_whens_nclockof : forall e ty ck,
        nclockof e = [(Cbase, None)] ->
        nclockof (add_whens e ty ck) = [(ck, None)].
    Proof.
      intros * Hck.
      destruct ck as [|?? (?&?)]; simpl in *; auto.
    Qed.

    Lemma subclock_exp_nclockof : forall e,
        Forall2
          (fun '(ck1, o1) '(ck2, o2) => ck2 = subclock_clock bck sub ck1 /\ LiftO True (fun x1 => o2 = Some (rename_var sub x1)) o1)
          (nclockof e) (nclockof (subclock_exp bck sub subl e)).
    Proof.
      destruct e; simpl in *; destruct_conjs; simpl_Forall; auto.
      1,2:rewrite add_whens_nclockof; auto; repeat constructor.
      unfold rename_last.
      cases_eqn Eq; simpl; simpl_Forall; auto.
    Qed.

    Corollary subclock_exp_nclocksof : forall es,
        Forall2
          (fun '(ck1, o1) '(ck2, o2) => ck2 = subclock_clock bck sub ck1 /\ LiftO True (fun x1 => o2 = Some (rename_var sub x1)) o1)
          (nclocksof es) (nclocksof (map (subclock_exp bck sub subl) es)).
    Proof.
      intros es.
      unfold nclocksof. rewrite 2 flat_map_concat_map. apply Forall2_concat.
      simpl_Forall. eapply subclock_exp_nclockof.
    Qed.

  End subclock_nclockof.

  Section subclock.
    Variable bck : clock.
    Variable sub subl : Env.t ident.
    Variable Γ Γ' : static_env.

    Hypothesis Hclock : forall x ck,
        Env.find x sub = None ->
        HasClock Γ x ck ->
        HasClock Γ' x (subclock_clock bck sub ck).

    Hypothesis Hlast : forall x ck,
        Env.find x subl = None ->
        HasClock Γ x ck ->
        IsLast Γ x ->
        HasClock Γ' x (subclock_clock bck sub ck) /\ IsLast Γ' x.

    Hypothesis Hsub : forall x y ck,
        Env.find x sub = Some y ->
        HasClock Γ x ck ->
        HasClock Γ' y (subclock_clock bck sub ck).

    Hypothesis Hsubl : forall x y ck,
        Env.find x subl = Some y ->
        HasClock Γ x ck ->
        IsLast Γ x ->
        HasClock Γ' y (subclock_clock bck sub ck).

    Lemma rename_var_wc : forall x ck,
        HasClock Γ x ck ->
        HasClock Γ' (rename_var sub x) (subclock_clock bck sub ck).
    Proof.
      unfold rename_var.
      intros * Hin.
      destruct (Env.find _ _) eqn:Hfind; simpl in *; eauto.
    Qed.

    Context {PSyn : list decl -> block -> Prop} {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Hypothesis Hwbck : wc_clock (idck Γ') bck.

    Lemma subclock_clock_wc : forall ck,
        wc_clock (idck Γ) ck ->
        wc_clock (idck Γ') (subclock_clock bck sub ck).
    Proof.
      induction ck; intros * Hwc; inv Hwc; simpl; auto.
      constructor; eauto.
      simpl_In. assert (HasClock Γ i a.(clo)) as Hck by eauto with senv.
      eapply rename_var_wc in Hck. inv Hck. solve_In. congruence.
    Qed.

    Lemma add_whens_wc : forall e ty,
        clockof e = [Cbase] ->
        wc_exp G Γ' e ->
        wc_exp G Γ' (add_whens e ty bck).
    Proof.
      clear Hsub Hsubl Hclock Hlast.
      induction bck as [|??? (?&?)]; intros * Hbase Hwc; inv Hwbck;
        simpl in *; auto. simpl_In.
      eapply wc_Ewhen; eauto; simpl; try rewrite app_nil_r.
      - econstructor; solve_In; eauto.
      - rewrite add_whens_clockof; auto.
      - rewrite add_whens_clockof; auto.
    Qed.

    Lemma subclock_clock_instck : forall sub1 sub0 sub2 bck' ck ck',
        instck bck' sub0 ck = Some ck' ->
        instck (subclock_clock bck sub1 bck')
          (fun x0 => (match option_map (rename_var sub1) (sub0 x0) with
                   | Some y => Some y
                   | None => Env.find x0 sub2
                   end)) ck = Some (subclock_clock bck sub1 ck').
    Proof.
      induction ck; intros * Hinst; simpl in *.
      - inv Hinst; auto.
      - cases_eqn Heq; inv Hinst; simpl in *.
        + inv Heq2; simpl. inv Heq3; simpl.
          specialize (IHck _ eq_refl). now inv IHck.
        + congruence.
        + specialize (IHck _ eq_refl). congruence.
        + specialize (IHck _ eq_refl). congruence.
    Qed.

    (* Lemma subclock_nclock_WellInstantiated1 : forall bck' sub0 sub xck nck, *)
    (*     WellInstantiated bck' sub0 xck nck -> *)
    (*     WellInstantiated (subclock_clock bck sub bck') (fun x => option_map (rename_var sub) (sub0 x)) xck (subclock_nclock bck sub nck). *)
    (* Proof. *)
    (*   intros ??? (x&ck) (ck'&name) (Hw1&Hw2). split; simpl in *. *)
    (*   - rewrite Hw1. destruct name; simpl; auto. *)
    (*   - apply subclock_clock_instck; auto. *)
    (* Qed. *)

    (* Lemma subclock_nclock_WellInstantiated2 : forall bck' sub0 sub xck ck, *)
    (*     WellInstantiated bck' sub0 xck (ck, None) -> *)
    (*     WellInstantiated (subclock_clock bck sub bck') (fun x => option_map (rename_var sub) (sub0 x)) xck (subclock_clock bck sub ck, None). *)
    (* Proof. *)
    (*   intros ??? (x&ck) ck' (Hw1&Hw2). split; simpl in *. *)
    (*   - rewrite Hw1. reflexivity. *)
    (*   - apply subclock_clock_instck; auto. *)
    (* Qed. *)

    Lemma subclock_exp_wc : forall e,
        wc_exp G Γ e ->
        wc_exp G Γ' (subclock_exp bck sub subl e).
    Proof with eauto with lclocking.
      induction e using exp_ind2; intros * Hwc; inv Hwc; simpl in *.
      1-12:try econstructor; simpl in *; eauto using rename_var_wc with lclocking.
      all:try solve [rewrite Forall_map, Forall_forall in *; intros; eauto].
      all:try (erewrite subclock_exp_clockof; eauto).
      all:try rewrite subclock_exp_clocksof.
      all:try (rewrite map_subclock_ann_clock; rewrite Forall2_eq in *; congruence).
      - apply add_whens_wc...
      - apply add_whens_wc...
      - unfold rename_last. cases_eqn Eq; [econstructor; eauto|].
        edestruct Hlast; eauto. econstructor; eauto.
      - take (clockof e = [_]) and rewrite it; auto.
      - take (clockof e1 = [_]) and rewrite it; auto.
      - take (clockof e2 = [_]) and rewrite it; auto.
      - simpl_Forall; subst; auto.
      - contradict H5. eapply map_eq_nil; eauto.
      - simpl_Forall; subst; auto.
      - rewrite length_map; auto.
      - contradict H4. apply map_eq_nil in H4; auto.
      - simpl_Forall. auto.
      - rewrite Forall_map. rewrite Forall_forall; intros (?&?) Hin; simpl.
        rewrite subclock_exp_clocksof, Forall_map.
        eapply Forall_forall in H6; eauto; simpl in H6.
        eapply Forall_impl; [|eauto]; intros; subst; auto.
      - simpl_Forall.
        now rewrite subclock_exp_clocksof, length_map.
      - now rewrite H6.
      - contradict H7. apply map_eq_nil in H7; auto.
      - simpl_Forall; auto.
      - rewrite Forall_map. rewrite Forall_forall; intros (?&?) Hin; simpl.
        rewrite subclock_exp_clocksof, Forall_map.
        eapply Forall_forall in H9; eauto; simpl in H9.
        eapply Forall_impl; [|eauto]; intros; subst; auto.
      - simpl_Forall.
        now rewrite subclock_exp_clocksof, length_map.
      - intros ? Hopt. eapply option_map_inv in Hopt as (?&?&?); subst; simpl in *.
        specialize (H11 _ eq_refl).
        rewrite Forall_map. rewrite Forall_forall in *; eauto.
      - intros ? Hopt. eapply option_map_inv in Hopt as (?&?&?); subst; simpl in *.
        specialize (H12 _ eq_refl).
        rewrite subclock_exp_clocksof, Forall_map. eapply Forall_impl; [|eauto]; intros; subst; auto.
      - intros ? Hopt. eapply option_map_inv in Hopt as (?&?&?); subst; simpl in *.
        specialize (H13 _ eq_refl).
        now rewrite subclock_exp_clocksof, length_map.
      - (* app *)
        remember (Env.from_list (map_filter (fun '(x, (_, ox)) => option_map (fun xc => (x, xc)) ox)
                                            (combine (map fst (n_in n)) (nclocksof (map (subclock_exp bck sub subl) es))))) as sub2.
        assert (length (n_in n) = length (nclocksof (map (subclock_exp bck sub subl) es))) as Len.
        { apply Forall2_length in H8.
          rewrite ? length_map, ? length_nclocksof_annots, <-? length_clocksof_annots, ? subclock_exp_clocksof, ? length_map in *.
          auto. }
        assert (Forall2 (fun '(x, _) '(ck, ox) => LiftO (Env.find x sub2 = None) (fun x' => Env.MapsTo x x' sub2) ox)
                  (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof (map (subclock_exp bck sub subl) es))) as Hsub2.
        { apply Forall2_forall; split; [|now rewrite length_map].
          intros (?&?) (?&?) Hin'.
          assert (In (k, (c0, o)) (combine (map fst (n_in n)) (nclocksof (map (subclock_exp bck sub subl) es)))) as Hin2.
          { repeat setoid_rewrite combine_map_fst in Hin'.
            eapply in_map_iff in Hin' as (((?&(?&?)&?)&?&?)&Heq&?); inv Heq.
            rewrite combine_map_fst. eapply in_map_iff. do 2 esplit; eauto. simpl; auto. }
          assert (NoDupMembers (combine (map fst (n_in n)) (nclocksof (map (subclock_exp bck sub subl) es)))) as Hnd1.
          { rewrite fst_NoDupMembers, combine_map_fst', <-fst_NoDupMembers; [|now rewrite length_map].
            pose proof (n_nodup n) as (Hnd1&_). apply fst_NoDupMembers; eauto using NoDup_app_l. }
          destruct o; simpl; subst.
          - eapply Env.find_In_from_list.
            2:{ clear - Hnd1. remember (combine _ _) as comb. clear - Hnd1.
                induction comb as [|(?&?&?)]; simpl in *; inv Hnd1. constructor.
                destruct (option_map _ _) as [(?&?)|] eqn:Hopt; simpl; auto.
                eapply option_map_inv in Hopt as (?&?&Heq); inv Heq.
                econstructor; auto. intro contra. apply H1.
                apply fst_InMembers, in_map_iff in contra as ((?&?)&?&Hin); subst.
                apply map_filter_In' in Hin as ((?&?&?)&Hin&Hopt). apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
                apply In_InMembers in Hin; auto.
            }
            eapply map_filter_In; eauto.
          - destruct (Env.find _ _) eqn:Hfind; auto. exfalso.
            eapply Env.from_list_find_In, map_filter_In' in Hfind as ((?&?&?)&Hin3&Hopt).
            apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
            eapply NoDupMembers_det in Hin2; eauto. inv Hin2.
        }

        econstructor; eauto. 1,2,5:simpl_Forall; eauto.
        + erewrite subclock_exp_clockof, H2; simpl; eauto.
        + instantiate (1:=fun x => (match option_map (rename_var sub) (sub0 x) with
                                 | Some y => Some y
                                 | _ => Env.find x sub2
                                 end)).
          instantiate (1:=subclock_clock bck sub bck0).
          specialize (subclock_exp_nclocksof bck sub subl es) as Hncks.
          eapply Forall2_trans_ex in Hncks; eauto.
          simpl_Forall. destruct b; destruct_conjs. subst.
          take (WellInstantiated _ _ _ _) and inv it; simpl in *.
          destruct o; simpl in *; subst.
          * econstructor; simpl; eauto using subclock_clock_instck.
            now take (sub0 _ = _) and rewrite it.
          * destruct o0; constructor; simpl in *; try take (sub0 _ = _) and rewrite it; simpl; eauto.
            1,2:eapply subclock_clock_instck; eauto.
        + simpl_Forall.
          take (WellInstantiated _ _ _ _) and inv it; simpl in *.
          constructor; simpl; eauto using subclock_clock_instck.
          take (sub0 _ = _) and rewrite it; simpl; eauto.
          apply Env.Props.P.F.not_find_in_iff. rewrite Env.In_from_list.
          intros ?. simpl_In. eapply in_combine_l in Hin0.
          pose proof (n_nodup n) as (ND&_).
          eapply NoDup_app_In in ND; eauto. eapply ND. solve_In.
    Qed.

    Lemma subclock_equation_wc : forall eq,
        wc_equation G Γ eq ->
        wc_equation G Γ' (subclock_equation bck sub subl eq).
    Proof.
      intros (?&?) Hwc. inv Hwc; simpl.
      - (* app *)
        remember (Env.from_list (map_filter (fun '(x, (_, ox)) => option_map (fun xc => (x, xc)) ox)
                                            (combine (map fst (n_in n)) (nclocksof (map (subclock_exp bck sub subl) es))))) as sub2.
        assert (length (n_in n) = length (nclocksof (map (subclock_exp bck sub subl) es))) as Len.
        { apply Forall2_length in H4.
          rewrite ? length_map, ? length_nclocksof_annots, <-? length_clocksof_annots, ? subclock_exp_clocksof, ? length_map in *.
          auto. }
        assert (Forall2 (fun '(x, _) '(ck, ox) => LiftO (Env.find x sub2 = None) (fun x' => Env.MapsTo x x' sub2) ox)
                  (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof (map (subclock_exp bck sub subl) es))) as Hsub2.
        { apply Forall2_forall; split; [|now rewrite length_map].
          intros (?&?) (?&?) Hin'.
          assert (In (k, (c0, o)) (combine (map fst (n_in n)) (nclocksof (map (subclock_exp bck sub subl) es)))) as Hin2.
          { repeat setoid_rewrite combine_map_fst in Hin'.
            eapply in_map_iff in Hin' as (((?&(?&?)&?)&?&?)&Heq&?); inv Heq.
            rewrite combine_map_fst. eapply in_map_iff. do 2 esplit; eauto. simpl; auto. }
          assert (NoDupMembers (combine (map fst (n_in n)) (nclocksof (map (subclock_exp bck sub subl) es)))) as Hnd1.
          { rewrite fst_NoDupMembers, combine_map_fst', <-fst_NoDupMembers; [|now rewrite length_map].
            pose proof (n_nodup n) as (Hnd1&_). apply fst_NoDupMembers; eauto using NoDup_app_l. }
          destruct o; simpl; subst.
          - eapply Env.find_In_from_list.
            2:{ clear - Hnd1. remember (combine _ _) as comb. clear - Hnd1.
                induction comb as [|(?&?&?)]; simpl in *; inv Hnd1. constructor.
                destruct (option_map _ _) as [(?&?)|] eqn:Hopt; simpl; auto.
                eapply option_map_inv in Hopt as (?&?&Heq); inv Heq.
                econstructor; auto. intro contra. apply H1.
                apply fst_InMembers, in_map_iff in contra as ((?&?)&?&Hin); subst.
                apply map_filter_In' in Hin as ((?&?&?)&Hin&Hopt). apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
                apply In_InMembers in Hin; auto.
            }
            eapply map_filter_In; eauto.
          - destruct (Env.find _ _) eqn:Hfind; auto. exfalso.
            eapply Env.from_list_find_In, map_filter_In' in Hfind as ((?&?&?)&Hin3&Hopt).
            apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
            eapply NoDupMembers_det in Hin2; eauto. inv Hin2.
        }

        econstructor; eauto.
        1,2,5:simpl_Forall; eauto using subclock_exp_wc.
        + erewrite subclock_exp_clockof, H0; simpl; eauto.
        + instantiate (1:=fun x => (match option_map (rename_var sub) (sub0 x) with
                                 | Some y => Some y
                                 | _ => Env.find x sub2
                                 end)).
          instantiate (1:=subclock_clock bck sub bck0).
          specialize (subclock_exp_nclocksof bck sub subl es) as Hncks.
          eapply Forall2_trans_ex in Hncks; eauto.
          simpl_Forall. destruct b; destruct_conjs. subst.
          take (WellInstantiated _ _ _ _) and inv it; simpl in *.
          destruct o; simpl in *; subst.
          * econstructor; simpl; eauto using subclock_clock_instck.
            now take (sub0 _ = _) and rewrite it.
          * destruct o0; constructor; simpl in *; try take (sub0 _ = _) and rewrite it; simpl; eauto.
            1,2:eapply subclock_clock_instck; eauto.
        + rewrite ? Forall3_map_2, ? Forall3_map_3 in *.
          eapply Forall3_impl_In; [|eauto]; intros; simpl_In.
          take (WellInstantiated _ _ _ _) and inv it; simpl in *.
          constructor; simpl; eauto using subclock_clock_instck.
          take (sub0 _ = _) and rewrite it; simpl; eauto.
        + simpl_Forall. eapply rename_var_wc; eauto.
      - (* general case *)
        econstructor; eauto.
        + simpl_Forall; eauto using subclock_exp_wc.
        + rewrite subclock_exp_clocksof. simpl_Forall; eauto using rename_var_wc.
    Qed.

  End subclock.

End SCCLOCKING.

Module SCClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (SC  : SUBCLOCK Ids Op OpAux Cks Senv Syn)
       <: SCCLOCKING Ids Op OpAux Cks Senv Syn Clo SC.
  Include SCCLOCKING Ids Op OpAux Cks Senv Syn Clo SC.
End SCClockingFun.
