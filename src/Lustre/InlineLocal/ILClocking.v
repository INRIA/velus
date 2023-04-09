From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LClocking.
From Velus Require Import Lustre.InlineLocal.InlineLocal.
From Velus Require Import Lustre.SubClock.SCClocking.

Module Type ILCLOCKING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import DL  : INLINELOCAL Ids Op OpAux Cks Senv Syn).

  Module Import SCC := SCClockingFun Ids Op OpAux Cks Senv Syn Clo SC. Import SC.

  Ltac inv_scope := (Syn.inv_scope || Clo.inv_scope).
  Ltac inv_block := (Syn.inv_block || Clo.inv_block).

  Fact In_sub1 : forall vars1 vars2 vars3 sub,
      (forall x, InMembers x vars1 -> ~InMembers x vars2) ->
      (forall x, Env.In x sub <-> InMembers x vars2) ->
      (forall x y ck, Env.find x sub = Some y -> HasClock vars2 x ck -> HasClock vars3 y (rename_in_clock sub ck)) ->
      forall x y ck, Env.find x sub = Some y -> HasClock (vars1 ++ vars2) x ck -> HasClock (vars1 ++ vars3) y (rename_in_clock sub ck) .
  Proof.
    intros * Hnd Hsubin Hsub * Hfind Hin.
    rewrite HasClock_app in *. destruct Hin as [Hin|Hin]; eauto.
    exfalso. inv Hin. eapply Hnd; eauto using In_InMembers.
    eapply Hsubin. econstructor; eauto.
  Qed.

  Fact rename_in_clock_idem vars sub : forall ck,
      (forall x, InMembers x vars -> ~Env.In x sub) ->
      wc_clock vars ck ->
      rename_in_clock sub ck = ck.
  Proof.
    induction ck; intros * Hnin Hwc; inv Hwc; simpl; auto.
    rewrite IHck; eauto. f_equal; auto.
    unfold rename_var.
    destruct (Env.find i sub) eqn:Hfind; auto.
    exfalso.
    eapply Hnin; eauto using In_InMembers.
    econstructor; eauto.
  Qed.

  Fact In_sub2 : forall vars1 vars2 vars3 sub,
      wc_env (idck vars1) ->
      (forall x, InMembers x vars1 -> ~InMembers x vars2) ->
      (forall x, Env.In x sub <-> InMembers x vars2) ->
      (forall x y ck, Env.find x sub = Some y -> HasClock vars2 x ck -> HasClock vars3 y (rename_in_clock sub ck)) ->
      forall x ck, Env.find x sub = None -> HasClock (vars1 ++ vars2) x ck -> HasClock (vars1 ++ vars3) x (rename_in_clock sub ck).
  Proof.
    intros * Hwenv Hnin Hsubin Hsub * Hfind Hin.
    rewrite HasClock_app in *. destruct Hin as [Hin|Hin]; eauto.
    - erewrite rename_in_clock_idem with (vars:=idck vars1); eauto.
      + intros. rewrite Hsubin; eauto. eapply Hnin.
        erewrite fst_InMembers in H. rewrite fst_InMembers. solve_In.
      + inv Hin. eapply Forall_forall in Hwenv; eauto. 2:solve_In. auto.
    - exfalso. inv Hin. eapply In_InMembers, Hsubin in H as (?&?).
      congruence.
  Qed.

  Local Hint Resolve In_sub1 In_sub2 : lclocking.

  Global Hint Resolve -> fst_InMembers : datatypes.
  Global Hint Resolve <- fst_InMembers : datatypes.
  Global Hint Resolve in_or_app In_InMembers : datatypes.

  Fact mmap_inlinelocal_block_wc {PSyn prefs} (G: @global PSyn prefs) sub Γ Γ' Γ'' : forall blks locs' blks' st st',
      Forall (fun blk => forall sub Γ' Γ'' locs' blks' st st',
                  (forall x, ~IsLast (Γ++Γ') x) ->
                  (forall x, InMembers x Γ -> ~InMembers x Γ') ->
                  (forall x, Env.In x sub <-> InMembers x Γ') ->
                  (forall x y, Env.find x sub = Some y -> InMembers y Γ' \/ exists n hint, y = gensym local hint n) ->
                  (forall x y ck, Env.find x sub = Some y -> HasClock Γ' x ck -> HasClock Γ'' y (rename_in_clock sub ck)) ->
                  noswitch_block blk ->
                  NoDupLocals (map fst Γ++map fst Γ'++map fst Γ'') blk ->
                  GoodLocals switch_prefs blk ->
                  wc_env (idck Γ) ->
                  wc_env (idck (Γ++Γ')) ->
                  wc_env (idck (Γ++Γ'')) ->
                  wc_block G (Γ++Γ') blk ->
                  inlinelocal_block sub blk st = (locs', blks', st') ->
                  Forall (wc_block G (Γ++Γ''++senv_of_anns locs')) blks'
                  /\ Forall (fun '(_, (_, ck)) => wc_clock (idck (Γ++Γ''++senv_of_anns locs')) ck) locs') blks ->
      (forall x, ~IsLast (Γ++Γ') x) ->
      (forall x, InMembers x Γ -> ~InMembers x Γ') ->
      (forall x, Env.In x sub <-> InMembers x Γ') ->
      (forall x y, Env.find x sub = Some y -> InMembers y Γ' \/ exists n hint, y = gensym local hint n) ->
      (forall x y ck, Env.find x sub = Some y -> HasClock Γ' x ck -> HasClock Γ'' y (rename_in_clock sub ck)) ->
      Forall noswitch_block blks ->
      Forall (NoDupLocals (map fst Γ++map fst Γ'++map fst Γ'')) blks ->
      Forall (GoodLocals switch_prefs) blks ->
      wc_env (idck Γ) ->
      wc_env (idck (Γ++Γ')) ->
      wc_env (idck (Γ++Γ'')) ->
      Forall (wc_block G (Γ++Γ')) blks ->
      mmap2 (inlinelocal_block sub) blks st = (locs', blks', st') ->
      Forall (wc_block G (Γ++Γ''++senv_of_anns (concat locs'))) (concat blks')
      /\ Forall (fun '(_, (_, ck)) => wc_clock (idck (Γ++Γ''++senv_of_anns (concat locs'))) ck) (concat locs').
  Proof.
    intros * F Nl Hnin Hsubin Hsub Hsubgen Hns Hnd Hgood Hwenv1 Hwenv2 Hwenv3 Hwc Hmmap.
    split; apply Forall_concat.
    - eapply mmap2_values, Forall3_ignore12 in Hmmap. simpl_Forall.
      take (inlinelocal_block _ _ _ = _) and eapply F in it as (?&?); eauto.
      simpl_Forall.
      eapply wc_block_incl; [| |eauto].
      1,2:intros * In; rewrite app_assoc in *; eauto with senv.
    - eapply mmap2_values, Forall3_ignore13 in Hmmap. simpl_Forall.
      take (inlinelocal_block _ _ _ = _) and eapply F in it as (?&?); eauto.
      simpl_Forall.
      eapply wc_clock_incl; [|eauto].
      apply incl_map; rewrite 2 app_assoc in *; eauto with senv.
  Qed.

  Lemma inlinelocal_block_wc {PSyn prefs} (G: @global PSyn prefs) Γ : forall blk sub Γ' Γ'' locs' blks' st st',
      (forall x, ~IsLast (Γ++Γ') x) ->
      (forall x, InMembers x Γ -> ~InMembers x Γ') ->
      (forall x, Env.In x sub <-> InMembers x Γ') ->
      (forall x y, Env.find x sub = Some y -> InMembers y Γ' \/ exists n hint, y = gensym local hint n) ->
      (forall x y ck, Env.find x sub = Some y -> HasClock Γ' x ck -> HasClock Γ'' y (rename_in_clock sub ck)) ->
      noswitch_block blk ->
      NoDupLocals (map fst Γ++map fst Γ'++map fst Γ'') blk ->
      GoodLocals switch_prefs blk ->
      wc_env (idck Γ) ->
      wc_env (idck (Γ++Γ')) ->
      wc_env (idck (Γ++Γ'')) ->
      wc_block G (Γ++Γ') blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall (wc_block G (Γ++Γ''++senv_of_anns locs')) blks'
      /\ Forall (fun '(_, (_, ck)) => wc_clock (idck (Γ++Γ''++senv_of_anns locs')) ck) locs'.
  Proof.
    induction blk using block_ind2; intros * Hnl Hnin Hsubin Hsubgen Hsub Hns Hgood Hnd Hwenv1 Hwenv2 Hwenv3 Hwc Hdl;
      inv Hns; inv Hnd; inv Hgood; inv Hwc; repeat monadInv.

    - (* equation *)
      simpl. split; auto. rewrite app_nil_r.
      do 2 constructor; auto.
      eapply subclock_equation_wc; eauto with lclocking.

    - (* reset *)
      eapply mmap_inlinelocal_block_wc in H0 as (Wc&Wcc); eauto.
      repeat econstructor; eauto.
      + eapply subclock_exp_wc; eauto using in_or_app with lclocking.
        1,2:intros * ??; rewrite app_assoc; apply HasClock_app; eauto with lclocking.
      + setoid_rewrite subclock_exp_clockof. rewrite H8; simpl; eauto.

    - (* local *)
      repeat inv_scope. subst Γ'0.

      assert (forall y, Env.In y (Env.from_list (combine (map fst locs) x)) <-> InMembers y locs) as Hsubin'.
      { intros.
        rewrite Env.In_from_list, <-In_InMembers_combine, fst_InMembers; try reflexivity.
        now apply mmap_values, Forall2_length in H0. }

      assert (forall y, Env.In y sub -> ~In y (map fst locs)) as Hsub1.
      { intros ?. rewrite Hsubin. intros Hin1 Hin2.
        eapply H12; eauto with datatypes. rewrite 2 in_app_iff; eauto with datatypes. }
     assert (forall x1 x2, Env.MapsTo x1 x2 sub -> ~In x2 (map fst locs)) as Hsub2.
      { intros ??. intros Hin1 Hin2.
        eapply Hsubgen in Hin1 as [Hin|(?&?&Hgen)]; subst.
        - simpl_In. eapply H12; eauto using In_InMembers. rewrite 2 in_app_iff; eauto with datatypes.
        - simpl_In. simpl_Forall.
          eapply Fresh.Facts.contradict_AtomOrGensym; eauto using local_not_in_switch_prefs. }

      rewrite senv_of_anns_app, 2 app_assoc, <-app_assoc with (m:=Γ''). rewrite Forall_app.

      assert (Forall
                (fun '(_, (_, ck)) =>
                   wc_clock
                     (idck
                        ((Γ ++ Γ'' ++
                            senv_of_anns
                            (map
                               (fun '(x3, (ty, ck0, _, _)) =>
                                  (rename_var (Env.adds (map fst locs) x sub) x3,
                                    (ty, rename_in_clock (Env.adds (map fst locs) x sub) ck0))) locs)))) ck)
                (map
                   (fun '(x3, (ty, ck, _, _)) =>
                      (rename_var (Env.adds (map fst locs) x sub) x3,
                        (ty, rename_in_clock (Env.adds (map fst locs) x sub) ck))) locs)) as Cks.
      { simpl_Forall.
        erewrite <-disjoint_union_rename_in_clock; eauto.
        eapply subclock_clock_wc, subclock_clock_wc
          with (Γ':=(Γ++Γ'')++senv_of_anns (map (fun '(x, (ty, ck, _, _)) => (x, (ty, rename_in_clock sub ck))) locs)).
        3,6,7:eauto with lclocking.
        3:{ intros * Hfind In. repeat rewrite HasClock_app in *. destruct In as [[In|In]|In]; eauto.
            1,2:exfalso.
            - eapply Hnin, Hsubin. 2:econstructor; eauto.
              clear - In. inv In. solve_In.
            - eapply H12.
              2:{ repeat rewrite in_app_iff. right. left. eapply fst_InMembers, Hsubin. econstructor; eauto. }
              clear - In. inv In. solve_In.
        }
        3:{ intros * Hfind In. repeat rewrite HasClock_app in *. destruct In as [[In|In]|In]; eauto.
            - left. left. erewrite rename_in_clock_idem with (vars:=idck Γ); eauto.
              2:{ inv In. eapply wc_env_var; eauto. solve_In. }
              intros ? InM InE. eapply Hnin, Hsubin; eauto.
              clear - InM. solve_In.
            - exfalso. inv In. eapply In_InMembers, Hsubin in H5 as (?&?). congruence.
            - right. clear - In. inv In. simpl_In. econstructor. solve_In. auto.
        }
        1:{ intros * Find In.
            repeat rewrite HasClock_app in *. destruct In as [[In|In]|In]; eauto.
            1,2:exfalso; apply Env.from_list_find_In, in_combine_l, fst_InMembers in Find.
            - exfalso. eapply H12; eauto.
              clear - In. inv In. repeat rewrite in_app_iff. left. solve_In.
            - exfalso. eapply H12; eauto.
              clear - In. inv In. repeat rewrite in_app_iff. right. right. solve_In.
            - right. right.
              inv In. simpl_In. eapply reuse_idents_find in H0 as (?&?&?&Reu&Find'); eauto using In_InMembers.
              erewrite disjoint_union_rename_in_clock; eauto.
              unfold Env.adds, Env.from_list in *. rewrite Find' in Find. inv Find.
              econstructor. solve_In. unfold rename_var. erewrite Env.find_gsss'_irrelevant; simpl; eauto. 2:auto.
              apply Env.find_adds'_In in Find' as [|Find]; eauto using In_InMembers.
              rewrite Env.gempty in Find. congruence.
        }
        1:{ intros * Find In.
            repeat rewrite HasClock_app in *. destruct In as [[In|In]|In]; eauto.
            - left. erewrite rename_in_clock_idem with (vars:=idck Γ); eauto.
              2:{ inv In. eapply wc_env_var; eauto. solve_In. }
              intros ? Hinm. rewrite Hsubin'. intros contra. rewrite fst_InMembers in Hinm.
              eapply H12; eauto.
              clear - Hinm. repeat rewrite in_app_iff. left. solve_In.
            - right. left. erewrite rename_in_clock_idem; eauto.
              2:{ inv In. eapply wc_env_var; eauto. simpl_app. apply in_app_iff, or_intror. solve_In. }
              intros * Inm In2. simpl_app.
              eapply Env.In_from_list, InMembers_In_combine, fst_InMembers in In2.
              eapply H12; eauto.
              clear - Inm. repeat rewrite in_app_iff.
              apply InMembers_app in Inm as [|]; [left|right; right]; solve_In.
            - exfalso. inv In. simpl_In.
              eapply In_InMembers, Hsubin' in Hin0 as (?&Find'). unfold Env.MapsTo in *.
              setoid_rewrite Find in Find'. congruence.
        }
      }
      eapply mmap_inlinelocal_block_wc with (Γ':=Γ'++senv_of_decls locs) (Γ'':=Γ''++_) in H4 as (Wc&Wcc); eauto.
      1:rewrite app_assoc in Wc, Wcc; repeat split; eauto.
      * simpl_Forall. eapply wc_clock_incl; eauto. solve_incl_app.
      * rewrite app_assoc, NoLast_app. split; auto.
        intros * Hl. inv Hl; simpl_In. simpl_Forall. subst; simpl in *; congruence.
      * intros ? Hin. rewrite InMembers_app, not_or', InMembers_senv_of_decls.
        split; auto. intro contra.
        eapply H12; eauto with datatypes.
      * intros. rewrite Env.In_adds_spec, InMembers_app, InMembers_senv_of_decls, Hsubin, <-fst_InMembers; eauto using mmap_values, Forall2_length.
        apply or_comm.
      *{ intros ?? Hfind. rewrite InMembers_app, InMembers_senv_of_decls.
         eapply Env.find_adds'_In in Hfind as [Hfind|Hfind]; eauto.
         - eapply in_combine_r in Hfind.
           eapply reuse_idents_gensym in H0. simpl_Forall. destruct H0; eauto.
         - eapply Hsubgen in Hfind as [|]; eauto. }
      *{ intros * Hfind Hin. apply HasClock_app.
         eapply HasClock_app in Hin as [Hin|Hin]; [left|right].
         - assert (Env.find x3 (Env.from_list (combine (map fst locs) x)) = None) as Hnone.
           { inv Hin.
             destruct (Env.find x3 (Env.from_list (combine (map fst locs) x))) eqn:Hfind'; eauto.
             exfalso. apply Env.from_list_find_In, in_combine_l in Hfind'.
             eapply H12; eauto with datatypes. rewrite 2 in_app_iff; eauto with datatypes. }
           apply Env.adds_from_list in Hfind as [Hfind|Hfind]; eauto.
           1:{ setoid_rewrite Hfind in Hnone. inv Hnone. }
           erewrite <-disjoint_union_rename_in_clock, rename_in_clock_idem; eauto.
           2:eapply subclock_clock_wc with (Γ:=Γ++Γ'), wc_env_var; eauto with lclocking; eauto with datatypes.
           4:{ inv Hin. simpl_app. apply in_app_iff, or_intror. solve_In. }
           2:eapply In_sub1; eauto. 2:eapply In_sub2; eauto.
           1:{ intros * In1 In2. rewrite Hsubin' in In2. setoid_rewrite map_app in In1.
               eapply H12; eauto. rewrite 2 in_app_iff.
               clear - In1. apply InMembers_app in In1 as [In1|In1]; [left|right;right]; solve_In.
           }
         - inv Hin. simpl_In. eapply reuse_idents_find in H0 as (?&?&?&Reu&Find); eauto using In_InMembers.
           rewrite Hfind in Find. inv Find.
           econstructor. unfold senv_of_anns. solve_In.
           unfold rename_var. rewrite Hfind. eauto. reflexivity.
       }
      *{ simpl_app. simpl_Forall.
         eapply NoDupLocals_incl'. 4:eauto. all:eauto using local_not_in_switch_prefs.
         intros *. repeat rewrite in_app_iff.
         intros [|[|[In|[In|In]]]]; auto.
         * clear - In. simpl_In. left. right. right. right. solve_In.
         * clear - H0 H11 In. simpl_In.
           eapply reuse_idents_find in H0 as (?&?&?&Reu&Find); eauto using In_InMembers.
           unfold rename_var. rewrite Find.
           eapply reuse_ident_gensym in Reu as [|]; subst; eauto.
           left. right. right. right. solve_In.
       }
      *{ simpl_app. rewrite app_assoc.
         eapply Forall_app; split.
         * eapply Forall_impl; [|eauto]; intros (?&?) ?.
           eapply wc_clock_incl; [|eauto]. solve_incl_app.
         * simpl_Forall. simpl_app. auto. }
      * rewrite app_assoc. setoid_rewrite map_app. eapply wc_env_app; eauto.
        clear - Cks. simpl_app. simpl_Forall.
        eapply wc_clock_incl; [|eauto]. solve_incl_app.
      * now rewrite app_assoc.
  Qed.

  Lemma inlinelocal_node_wc : forall G1 G2 n,
      global_iface_incl G1 G2 ->
      wc_node G1 n ->
      wc_node G2 (inlinelocal_node n).
  Proof.
    unfold inlinelocal_node; simpl.
    intros * Hiface Hwc. inversion_clear Hwc as [?? Wc1 Wc2 Wc3].
    pose proof (n_nodup n) as (_&Hnd2).
    pose proof (n_good n) as (_&Hgood&_).
    pose proof (n_syn n) as Hsyn. inversion_clear Hsyn as [?? Syn1 Syn2].
    econstructor; simpl; eauto.
    destruct (inlinelocal_block _ _ _) as ((?&?)&?) eqn:Hdl.
    repeat split; auto.
    assert (Hinl:=Hdl). eapply inlinelocal_block_wc
                          with (Γ:=senv_of_ins (n_in n) ++ senv_of_decls (n_out n)) in Hdl as (?&?); try rewrite app_nil_r in *; eauto.
    - repeat econstructor; simpl; eauto.
      + simpl_Forall. simpl_app. repeat rewrite map_map in *.
        erewrite map_ext with (l:=l); eauto. intros; destruct_conjs; auto.
      + simpl_Forall. simpl_app. repeat rewrite map_map in *.
        erewrite map_ext with (l:=l); eauto using iface_incl_wc_block. intros; destruct_conjs; auto.
    - apply NoLast_app; split; auto using senv_of_ins_NoLast.
      intros * L. inv L. simpl_In. simpl_Forall. subst; simpl in *; congruence.
    - intros. rewrite Env.Props.P.F.empty_in_iff.
      split; intros [].
    - intros * EQ. rewrite Env.gempty in EQ. congruence.
    - intros * EQ. rewrite Env.gempty in EQ. congruence.
    - rewrite app_nil_r. apply node_NoDupLocals.
    - unfold idck, senv_of_ins, senv_of_decls.
      erewrite map_app, 2 map_map, map_ext, map_ext with (l:=n_out _); eauto.
      1,2:unfold decl; intros; destruct_conjs; auto.
    - unfold idck, senv_of_ins, senv_of_decls.
      erewrite map_app, 2 map_map, map_ext, map_ext with (l:=n_out _); eauto.
      1,2:unfold decl; intros; destruct_conjs; auto.
    - unfold idck, senv_of_ins, senv_of_decls.
      erewrite map_app, 2 map_map, map_ext, map_ext with (l:=n_out _); eauto.
      1,2:unfold decl; intros; destruct_conjs; auto.
  Qed.

  Theorem inlinelocal_global_wc : forall G,
      wc_global G ->
      wc_global (inlinelocal_global G).
  Proof.
    unfold wc_global, inlinelocal_global.
    intros * Hwc.
    eapply CommonTyping.transform_units_wt_program; eauto.
    intros ?? Hwc'.
    eapply inlinelocal_node_wc; eauto. eapply iface_eq_iface_incl, inlinelocal_global_iface_eq.
  Qed.

End ILCLOCKING.

Module ILClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (IL  : INLINELOCAL Ids Op OpAux Cks Senv Syn)
       <: ILCLOCKING Ids Op OpAux Cks Senv Syn Clo IL.
  Include ILCLOCKING Ids Op OpAux Cks Senv Syn Clo IL.
End ILClockingFun.
