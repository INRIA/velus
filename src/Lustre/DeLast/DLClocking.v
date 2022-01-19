From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax Lustre.LClocking.
From Velus Require Import Lustre.DeLast.DeLast.

Module Type DLCLOCKING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (Import DL  : DELAST Ids Op OpAux Cks Syn).

  Lemma rename_in_sub : forall x y (ck : clock) sub xs,
      Env.find x sub = Some y ->
      In (x, ck) xs ->
      In (y, ck) (map (fun '(x, ty) => (rename_in_var sub x, ty)) xs).
  Proof.
    intros * Hfind Hin.
    solve_In.
    unfold rename_in_var. now rewrite Hfind.
  Qed.

  Lemma rename_in_nsub : forall x (ck : clock) sub xs,
      Env.find x sub = None ->
      In (x, ck) xs ->
      In (x, ck) (map (fun '(x, ty) => (rename_in_var sub x, ty)) xs).
  Proof.
    intros * Hfind Hin.
    solve_In.
    unfold rename_in_var. now rewrite Hfind.
  Qed.

  Section rename.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Variable sub : Env.t ident.

    Section rename_in_exp.
      Variable Γ Γl : list (ident * clock).

      Lemma rename_in_last_wc : forall x ck,
          In (x, ck) Γl ->
          In (rename_in_var sub x, ck) (map (fun '(x, ck) => (rename_in_var sub x, ck)) Γl).
      Proof.
        intros * Hin.
        unfold rename_in_var.
        destruct (Env.find _ _) eqn:Hfind; eauto using rename_in_sub, rename_in_nsub.
      Qed.

      Lemma rename_in_exp_clockof : forall e,
          clockof (rename_in_exp sub e) = clockof e.
      Proof.
        destruct e; destruct_conjs; simpl; auto.
      Qed.

      Corollary rename_in_exp_clocksof : forall es,
          clocksof (map (rename_in_exp sub) es) = clocksof es.
      Proof.
        induction es; simpl; auto.
        f_equal; auto using rename_in_exp_clockof.
      Qed.

      Lemma rename_in_exp_nclockof : forall sub e,
          Forall2 (fun '(ck1, o1) '(ck2, o2) => ck1 = ck2 /\ LiftO True (fun id1 => o2 = Some id1) o1)
                  (nclockof e) (nclockof (rename_in_exp sub e)).
      Proof.
        destruct e; destruct_conjs; simpl_Forall; auto.
      Qed.

      Corollary rename_in_exp_nclocksof : forall sub es,
          Forall2 (fun '(ck1, o1) '(ck2, o2) => ck1 = ck2 /\ LiftO True (fun id1 => o2 = Some id1) o1)
                  (nclocksof es) (nclocksof (map (rename_in_exp sub) es)).
      Proof.
        intros.
        unfold nclocksof. rewrite 2 flat_map_concat_map.
        apply Forall2_concat. simpl_Forall.
        apply rename_in_exp_nclockof.
      Qed.

      Lemma rename_in_exp_wc : forall e,
          wc_exp G Γ Γl e ->
          wc_exp G (Γ++map (fun '(x, ty) => (rename_in_var sub x, ty)) Γl) [] (rename_in_exp sub e).
      Proof.
        intros * Hwc; induction e using exp_ind2; inv Hwc; simpl.
        12:remember (Env.from_list (map_filter (fun '(x, (_, ox)) => option_map (fun xc => (x, xc)) ox)
                                            (combine (map fst (n_in n)) (nclocksof (map (rename_in_exp sub) es))))) as sub2.
        12:assert (length (n_in n) = length (nclocksof (map (rename_in_exp sub) es))) as Hlen2.
        12:{ apply Forall2_length in H8. repeat setoid_rewrite map_length in H8. rewrite H8.
             pose proof (rename_in_exp_nclocksof sub es) as Hncks. apply Forall2_length in Hncks; auto. }
        12:assert (Forall2 (fun '(x, _) '(ck, ox) => LiftO (Env.find x sub2 = None) (fun x' => Env.MapsTo x x' sub2) ox) (idck (idty (n_in n))) (nclocksof (map (rename_in_exp sub) es))) as Hsub2.
        12:{ apply Forall2_forall; split. 2:repeat setoid_rewrite map_length; auto.
             intros (?&?) (?&?) Hin'.
             assert (In (k, (c0, o)) (combine (map fst (n_in n)) (nclocksof (map (rename_in_exp sub) es)))) as Hin2.
             { repeat setoid_rewrite combine_map_fst in Hin'. rewrite map_map in Hin'.
               eapply in_map_iff in Hin' as (((?&(?&?)&?)&?&?)&Heq&?); inv Heq.
               rewrite combine_map_fst. eapply in_map_iff. do 2 esplit; eauto. simpl; auto. }
             assert (NoDupMembers (combine (map fst (n_in n)) (nclocksof (map (rename_in_exp sub) es)))) as Hnd1.
             { rewrite fst_NoDupMembers, combine_map_fst', <-fst_NoDupMembers. 2:now rewrite map_length.
               pose proof (n_nodup n) as (Hnd1&_). apply NoDupMembers_app_l in Hnd1; auto. }
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
        12:(pose proof (rename_in_exp_nclocksof sub es) as Hncks; eapply Forall2_trans_ex in Hncks; eauto).

        12:eapply wc_Eapp with
          (bck0:=bck)
          (sub1:=fun x => match (sub0 x) with
                       | Some y => Some y
                       | _ => Env.find x sub2
                       end).
        1-11:econstructor.
        1-40:eauto using in_or_app; simpl_Forall; eauto;
          match goal with
          | |- clockof _ = _ => rewrite rename_in_exp_clockof; auto
          | |- context [clocksof _] => rewrite rename_in_exp_clocksof; auto
          | H: context [clocksof _] |- _ => rewrite rename_in_exp_clocksof in H; auto
          | _ => idtac
          end.
        - apply in_or_app, or_intror. apply rename_in_last_wc; auto.
        - simpl_Forall; auto.
        - intros contra. apply map_eq_nil in contra; subst. contradiction.
        - simpl_Forall; auto.
        - intros contra. apply map_eq_nil in contra; subst. contradiction.
        - simpl_Forall; auto.
        - intros. inv_equalities; subst. specialize (H11 _ eq_refl). simpl_Forall; eauto.
        - intros. inv_equalities; subst. rewrite rename_in_exp_clocksof; eauto.
        - intros. inv_equalities; subst. rewrite rename_in_exp_clocksof; eauto.
        - destruct b; inv_equalities. destruct o; simpl in *; subst.
          + eapply WellInstantiated_refines2; eauto. intros ?? Hsub. rewrite Hsub; auto.
          + eapply WellInstantiated_refines1; eauto.
            * intros ?? Hsub. rewrite Hsub; auto.
            * destruct H11 as (Hsub&_); simpl in *. rewrite Hsub.
              destruct o0; simpl in *; auto.
        - eapply WellInstantiated_refines1; eauto.
          + intros ?? Hsub. rewrite Hsub; auto.
          + destruct H3 as (Hsub&_); simpl in *. rewrite Hsub. subst.
            destruct (Env.find i _) eqn:Hfind; auto. exfalso.
            eapply Env.from_list_find_In, map_filter_In' in Hfind as ((?&?&?)&?&Hopt).
            apply option_map_inv in Hopt as (?&?&Heq); inv Heq.
            pose proof (n_nodup n) as (Hnd&_). eapply NoDupMembers_app_InMembers in Hnd. eapply Hnd.
            rewrite fst_InMembers, <-map_fst_idty, <-map_fst_idck. eapply in_map_iff; do 2 esplit; eauto.
            apply In_InMembers, fst_InMembers in H3. erewrite combine_map_fst', <-fst_InMembers in H3; eauto.
            now rewrite map_length.
        - erewrite rename_in_exp_clockof; eauto.
      Qed.

      Lemma rename_in_equation_wc : forall eq,
          wc_equation G Γ Γl eq ->
          wc_equation G (Γ++map (fun '(x, ty) => (rename_in_var sub x, ty)) Γl) [] (rename_in_equation sub eq).
      Proof.
        intros * Hwc. inv Hwc.
        - (* app *)
          remember (Env.from_list (map_filter (fun '(x, (_, ox)) => option_map (fun xc => (x, xc)) ox)
                                              (combine (map fst (n_in n)) (nclocksof (map (rename_in_exp sub) es))))) as sub2.
          assert (length (n_in n) = length (nclocksof (map (rename_in_exp sub) es))) as Hlen2.
          { apply Forall2_length in H2. repeat setoid_rewrite map_length in H2. rewrite H2.
            pose proof (rename_in_exp_nclocksof sub es) as Hncks. apply Forall2_length in Hncks; auto. }
          assert (Forall2 (fun '(x, _) '(ck, ox) => LiftO (Env.find x sub2 = None) (fun x' => Env.MapsTo x x' sub2) ox) (idck (idty (n_in n))) (nclocksof (map (rename_in_exp sub) es))) as Hsub2.
          { apply Forall2_forall; split. 2:repeat setoid_rewrite map_length; auto.
            intros (?&?) (?&?) Hin'.
            assert (In (k, (c0, o)) (combine (map fst (n_in n)) (nclocksof (map (rename_in_exp sub) es)))) as Hin2.
            { repeat setoid_rewrite combine_map_fst in Hin'. rewrite map_map in Hin'.
              eapply in_map_iff in Hin' as (((?&(?&?)&?)&?&?)&Heq&?); inv Heq.
              rewrite combine_map_fst. eapply in_map_iff. do 2 esplit; eauto. simpl; auto. }
            assert (NoDupMembers (combine (map fst (n_in n)) (nclocksof (map (rename_in_exp sub) es)))) as Hnd1.
            { rewrite fst_NoDupMembers, combine_map_fst', <-fst_NoDupMembers. 2:now rewrite map_length.
              pose proof (n_nodup n) as (Hnd1&_). apply NoDupMembers_app_l in Hnd1; auto. }
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
          pose proof (rename_in_exp_nclocksof sub es) as Hncks; eapply Forall2_trans_ex in Hncks; eauto.
          eapply wc_EqApp with
          (bck0:=bck)
          (sub1:=fun x => match (sub0 x) with
                       | Some y => Some y
                       | _ => Env.find x sub2
                       end); simpl_Forall; eauto using in_or_app, rename_in_exp_wc.
          3:erewrite rename_in_exp_clockof; eauto.
          + simpl_Forall. destruct b; inv_equalities.
            destruct o; simpl in *; subst.
            * eapply WellInstantiated_refines2; eauto. intros ?? Hsub. rewrite Hsub; auto.
            * eapply WellInstantiated_refines1; eauto.
            -- intros ?? Hsub. rewrite Hsub; auto.
            -- destruct H10 as (Hsub&_); simpl in *. rewrite Hsub.
               destruct o0; simpl in *; auto.
          + eapply Forall3_impl_In; [|eauto]; intros; simpl in *.
            eapply WellInstantiated_refines2; eauto.
            intros * Hsub; rewrite Hsub; auto.

        - (* general case *)
          constructor; simpl_Forall; eauto using rename_in_exp_wc.
          rewrite rename_in_exp_clocksof; simpl_Forall; auto using in_or_app.
      Qed.

    End rename_in_exp.

  End rename.

  Import Fresh Facts Tactics.

  Lemma delast_block_wc {PSyn prefs} (G: @global PSyn prefs) : forall blk sub Γ Γl Γtyl blk' st st',
      incl (map fst Γl) Γtyl ->
      (forall x, Env.In x sub -> In x Γtyl) ->
      NoDupLocals Γtyl blk ->
      wc_block G Γ Γl blk ->
      delast_block sub blk st = (blk', st') ->
      wc_block G (Γ++map (fun '(x, ck) => (rename_in_var sub x, ck)) Γl) [] blk'.
  Proof.
    induction blk using block_ind2; intros * Hincl Hsubin Hnd Hwc Hdl;
      inv Hnd; inv Hwc; repeat inv_bind.
    - (* equation *)
      constructor.
      eapply rename_in_equation_wc; eauto.
    - (* reset *)
      econstructor.
      + eapply mmap_values, Forall2_ignore1 in H0; eauto.
        simpl_Forall; eauto.
      + eapply rename_in_exp_wc; eauto.
      + rewrite rename_in_exp_clockof; eauto.
    - (* switch *)
      eapply wc_Bswitch with (Γl'0:=[]); eauto.
      6:{ eapply mmap_values, Forall2_ignore1 in H0; eauto.
          simpl_Forall; eauto. repeat inv_bind.
          eapply mmap_values, Forall2_ignore1 in H7; eauto.
          simpl_Forall. eapply H in H10; eauto.
          intros ? Hin. simpl_In. apply H9 in Hin0 as (?&?); subst.
          apply Hincl; solve_In.
      }
      + eapply rename_in_exp_wc; eauto.
      + rewrite rename_in_exp_clockof; eauto.
      + apply mmap_values in H0. inv H0; auto. congruence.
      + intros * Hin. rewrite in_app_iff in *. destruct Hin as [Hin|]; simpl_In.
        * apply H6 in Hin as (?&?). auto.
        * apply H9 in Hin as (?&?). split; auto.
          right. solve_In.
      + intros * [].
    - (* local *)
      assert (forall y, Env.In y (Env.from_list (map fst x)) <->
                   InMembers y (map_filter (fun '(x, (ty, ck, _, o)) => option_map (fun '(e, _) => (x, (ty, ck, e))) o) locs)) as Hsubin'.
      { intros. rewrite Env.In_from_list.
        eapply fresh_idents_InMembers in H0. erewrite H0, 2 fst_InMembers.
        split; intros; solve_In. }
      assert (incl
                ((Γ ++ map (fun '(x6, (_, ck, _, _)) => (x6, ck)) locs)
                   ++ map (fun '(x6, ck) => (rename_in_var (Env.union sub (Env.from_list (map fst x))) x6, ck)) (Γl ++ map_filter (fun '(x6, (_, ck, _, o)) => option_map (fun _ : exp * ident => (x6, ck)) o) locs))
                ((Γ ++ map (fun '(x6, ck) => (rename_in_var sub x6, ck)) Γl)
                   ++ map (fun '(x6, (_, ck, _, _)) => (x6, ck)) (map (fun '(x6, (ty, ck, cx, _)) => (x6, (ty, ck, cx, @None (exp * ident)))) locs ++ map (fun '(_, lx, (ty, ck, _)) => (lx, (ty, ck, 1%positive, None))) x))
             ) as Hincl'.
      { simpl_app.
        apply incl_appr', incl_app;
          [apply incl_appr, incl_appl; erewrite map_map, map_ext; try reflexivity;
           intros; destruct_conjs; auto|].
        apply incl_app; [apply incl_appl|apply incl_appr, incl_appr].
        - intros ? Hin; solve_In. rewrite not_in_union_rename2; auto.
          erewrite Hsubin'. intros contra. apply fst_InMembers in contra. simpl_In.
          eapply H5; eauto using In_InMembers. solve_In.
          apply Hincl. solve_In.
        - intros ? Hin; simpl_In.
          assert (Hfresh:=H0). eapply fresh_idents_In in H0 as (?&Hin'). 2:solve_In; simpl; eauto.
          solve_In.
          rewrite not_in_union_rename1.
          2:{ intros Hsub. apply Hsubin in Hsub. eapply H5; eauto using In_InMembers. }
          unfold rename_in_var. erewrite fresh_idents_sub; eauto. 3:solve_In. auto.
          apply nodupmembers_map_filter; auto. intros; destruct_conjs; destruct o as [(?&?)|]; simpl; auto.
      }
      econstructor; eauto. rewrite Forall_app; split.
      + rewrite map_filter_nil; simpl.
        2:{ apply Forall_app; split; simpl_Forall; auto. }
        simpl_Forall. repeat constructor; simpl.
        * eapply fresh_idents_In' in H3; eauto. simpl_In. simpl_Forall.
          eapply rename_in_exp_wc in H3. eapply wc_exp_incl; [|reflexivity|eauto]. eauto.
        * eapply fresh_idents_In' in H3; eauto. simpl_In.
          simpl_app. repeat rewrite in_app_iff. right; right; left; solve_In.
        * eapply fresh_idents_In' in H3; eauto. simpl_In.
          simpl_Forall.
          rewrite rename_in_exp_clockof, app_nil_r, H6; auto.
        * simpl_app. repeat rewrite in_app_iff.
          right; right; right; solve_In.
      + eapply mmap_values(* _valid *), Forall2_ignore1 in H1; eauto.
        simpl_Forall.
        rewrite map_filter_nil.
        2:{ apply Forall_app; split; simpl_Forall; auto. }
        eapply H with (sub:=Env.union _ _) in H7; eauto.
        * eapply wc_block_incl; [|reflexivity|eauto]. eauto.
        * simpl_app. apply incl_app; [apply incl_appl; auto|apply incl_appr].
          intros ??. solve_In.
        * intros * Hin. rewrite in_app_iff. apply Env.union_In in Hin as [|Hin]; eauto.
          right.
          rewrite Hsubin' in Hin. rewrite fst_InMembers in Hin. solve_In.
      + simpl_app. apply Forall_app; split; auto.
        * simpl_Forall. eapply wc_clock_incl; [|eauto].
          apply incl_appr', incl_appr, incl_appl.
          erewrite map_map, map_ext; try reflexivity. intros; destruct_conjs; auto.
        * eapply mmap_values, Forall2_ignore1 in H0; simpl_Forall.
          repeat inv_bind. simpl_In.
          simpl_Forall. eapply wc_clock_incl; [|eauto].
          apply incl_appr', incl_appr, incl_appl.
          erewrite map_map, map_ext; try reflexivity. intros; destruct_conjs; auto.
      + simpl_app. apply Forall_app; split; auto.
        * simpl_Forall; auto.
        * eapply mmap_values, Forall2_ignore1 in H0; simpl_Forall.
          repeat inv_bind. simpl_In.
          simpl_Forall; eauto.
  Qed.

  (** Typing of the node *)

  Lemma delast_node_wc : forall G1 G2 (n : @node _ _),
      global_iface_eq G1 G2 ->
      wc_node G1 n ->
      wc_node G2 (delast_node n).
  Proof.
    intros * Hiface (Hwc1&Hwc2&Hwc3).
    pose proof (n_nodup n) as (_&Hnd2).
    pose proof (n_good n) as (_&Hgood&_).
    pose proof (n_syn n) as Hsyn.
    repeat econstructor; simpl; eauto.
    eapply delast_block_wc in Hwc3. 5:apply surjective_pairing.
    - rewrite app_nil_r in Hwc3. eapply iface_eq_wc_block, Hwc3; eauto.
    - reflexivity.
    - intros. rewrite Env.Props.P.F.empty_in_iff in H. inv H.
    - eapply NoDupLocals_incl; eauto. apply incl_nil'.
  Qed.

  Theorem delast_global_wc : forall G,
      wc_global G ->
      wc_global (delast_global G).
  Proof.
    unfold wc_global, delast_global.
    intros * Hwc.
    eapply CommonTyping.transform_units_wt_program; eauto.
    intros ?? Hwc'.
    eapply delast_node_wc; eauto. eapply delast_global_iface_eq.
  Qed.

End DLCLOCKING.

Module DLClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (Clo : LCLOCKING Ids Op OpAux Cks Syn)
       (DL  : DELAST Ids Op OpAux Cks Syn)
       <: DLCLOCKING Ids Op OpAux Cks Syn Clo DL.
  Include DLCLOCKING Ids Op OpAux Cks Syn Clo DL.
End DLClockingFun.
