From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping.
From Velus Require Import Lustre.InlineLocal.InlineLocal.

Module Type ILTYPING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import IL  : INLINELOCAL Ids Op OpAux Cks Senv Syn).

  Section rename.
    Variable sub : Env.t ident.

    Variable Γ Γ' : static_env.

    Hypothesis Hsub : forall x y ty,
        Env.find x sub = Some y ->
        HasType Γ x ty ->
        HasType Γ' y ty.

    Hypothesis Hnsub : forall x ty,
        Env.find x sub = None ->
        HasType Γ x ty ->
        HasType Γ' x ty.

    Hypothesis Hlsub : forall x y,
        Env.find x sub = Some y ->
        IsLast Γ x ->
        IsLast Γ' y.

    Hypothesis Hlnsub : forall x,
        Env.find x sub = None ->
        IsLast Γ x ->
        IsLast Γ' x.

    Lemma rename_var_wt : forall x ty,
        HasType Γ x ty ->
        HasType Γ' (rename_var sub x) ty.
    Proof.
      unfold rename_var.
      intros * Hin.
      destruct (Env.find _ _) eqn:Hfind; simpl in *; eauto.
    Qed.

    Context {PSyn : list decl -> block -> Prop} {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Lemma rename_clock_wt : forall ck,
        wt_clock G.(types) Γ ck ->
        wt_clock G.(types) Γ' (rename_clock sub ck).
    Proof.
      induction ck; intros * Hwt; inv Hwt; simpl.
      all:constructor; eauto using rename_var_wt.
    Qed.
    Local Hint Resolve rename_clock_wt : ltyping.

    Lemma rename_exp_wt : forall e,
        wt_exp G Γ e ->
        wt_exp G Γ' (rename_exp sub e).
    Proof with auto with ltyping.
      induction e using exp_ind2; intros * Hwt; inv Hwt; simpl in *.
      3-14:econstructor; simpl in *; eauto using rename_var_wt, rename_clock_wt.
      all:try solve [rewrite Forall_map, Forall_forall in *; intros; eauto].
      all:try rewrite rename_exp_typeof.
      all:try rewrite rename_exp_typesof.
      all:try (rewrite map_rename_ann_clock; auto). all:try (rewrite map_rename_ann_type; auto); auto.
      - constructor.
      - constructor...
      - eapply rename_var_IsLast; eauto.
      - simpl_Forall...
      - simpl_Forall...
      - erewrite map_map, map_ext; eauto. intros (?&?); auto.
      - contradict H6. apply map_eq_nil in H6; auto.
      - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite Forall_map.
        specialize (H _ Hin). specialize (H7 _ Hin).
        rewrite Forall_forall in *; eauto.
      - rewrite Forall_map. rewrite Forall_forall; intros (?&?) Hin; simpl.
        rewrite rename_exp_typesof.
        eapply Forall_forall in H8; eauto; auto.
      - erewrite map_map, map_ext; eauto. intros (?&?); auto.
      - contradict H9. apply map_eq_nil in H9; auto.
      - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite Forall_map.
        specialize (H _ Hin). specialize (H10 _ Hin).
        rewrite Forall_forall in *; eauto.
      - simpl_Forall. now rewrite rename_exp_typesof.
      - erewrite map_map, map_ext; eauto. intros (?&?); auto.
      - erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; eauto. intros (?&?); auto.
      - contradict H10. apply map_eq_nil in H10; auto.
      - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite Forall_map.
        specialize (H _ Hin). specialize (H11 _ Hin).
        rewrite Forall_forall in *; eauto.
      - rewrite Forall_map. rewrite Forall_forall; intros (?&?) Hin; simpl.
        rewrite rename_exp_typesof.
        eapply Forall_forall in H12; eauto; auto.
      - rewrite Forall2_map_1. eapply Forall2_impl_In; [|eauto]; intros (?&?) (?&((?&?)&?)) _ _ ?; auto.
      - rewrite Forall_map. eapply Forall_impl; [|eapply H10]; eauto; intros.
        now rewrite rename_exp_typeof.
      - rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
        eapply rename_clock_wt; eauto.
    Qed.

    Lemma rename_equation_wt : forall eq,
        wt_equation G Γ eq ->
        wt_equation G Γ' (rename_equation sub eq).
    Proof.
      intros (?&?) (Hwt1&Hwt2). constructor.
      - rewrite Forall_map.
        eapply Forall_impl; [|eauto]; eauto using rename_exp_wt.
      - rewrite Forall2_map_1, rename_exp_typesof.
        eapply Forall2_impl_In; [|eauto]; intros; eauto using rename_var_wt.
    Qed.

  End rename.

  Ltac inv_scope := (Syn.inv_scope || Typ.inv_scope).

  Fact HasType_sub1 : forall vars1 vars2 vars3 sub,
      (forall x, InMembers x vars1 -> ~InMembers x vars2) ->
      (forall x, Env.In x sub <-> InMembers x vars2) ->
      (forall x y ty, Env.find x sub = Some y -> HasType vars2 x ty -> HasType vars3 y ty) ->
      forall x y ty, Env.find x sub = Some y -> HasType (vars1 ++ vars2) x ty -> HasType (vars1 ++ vars3) y ty.
  Proof.
    intros * Hnd Hsubin Hsub * Hfind Hin.
    rewrite HasType_app in *. destruct Hin as [Hin|Hin]; eauto.
    exfalso. inv Hin. eapply Hnd; eauto using In_InMembers.
    eapply Hsubin. econstructor; eauto.
  Qed.

  Fact HasType_sub2 : forall vars1 vars2 vars3 sub,
      (forall x, Env.In x sub <-> InMembers x vars2) ->
      (forall x y ty, Env.find x sub = Some y -> HasType vars2 x ty -> HasType vars3 y ty) ->
      forall x ty, Env.find x sub = None -> HasType (vars1 ++ vars2) x ty -> HasType (vars1 ++ vars3) x ty.
  Proof.
    intros * Hsubin Hsub * Hfind Hin.
    rewrite HasType_app in *. destruct Hin as [Hin|Hin]; eauto.
    exfalso. inv Hin. eapply In_InMembers, Hsubin in H as (?&?).
    congruence.
  Qed.

  Global Hint Resolve HasType_sub1 HasType_sub2 IsLast_sub1 IsLast_sub2 : ltyping.

  Global Hint Resolve -> fst_InMembers : datatypes.
  Global Hint Resolve <- fst_InMembers : datatypes.
  Global Hint Resolve in_or_app In_InMembers : datatypes.

  Fact mmap_inlinelocal_block_wt {PSyn prefs} (G: @global PSyn prefs) sub Γ Γ' Γ'' : forall blks locs' blks' st st',
      Forall (fun blk => forall sub Γ' Γ'' locs' blks' st st',
                  (forall x, InMembers x Γ -> ~InMembers x Γ') ->
                  (forall x, Env.In x sub <-> InMembers x Γ') ->
                  (forall x y, Env.find x sub = Some y -> InMembers y Γ' \/ exists n hint, y = gensym local hint n) ->
                  (forall x y ty, Env.find x sub = Some y -> HasType Γ' x ty -> HasType Γ'' y ty) ->
                  (forall x y, Env.find x sub = Some y -> IsLast Γ' x -> IsLast Γ'' y) ->
                  noswitch_block blk ->
                  NoDupLocals (map fst Γ++map fst Γ'++map fst Γ'') blk ->
                  GoodLocals switch_prefs blk ->
                  wt_block G (Γ++Γ') blk ->
                  inlinelocal_block sub blk st = (locs', blks', st') ->
                  Forall (wt_block G (Γ ++ Γ''++senv_of_decls locs')) blks' /\
                  Forall (fun '(_, (_, ck, _, _)) => wt_clock G.(types) (Γ++Γ''++senv_of_decls locs') ck) locs') blks ->
      (forall x, InMembers x Γ -> ~InMembers x Γ') ->
      (forall x, Env.In x sub <-> InMembers x Γ') ->
      (forall x y, Env.find x sub = Some y -> InMembers y Γ' \/ exists n hint, y = gensym local hint n) ->
      (forall x y ty, Env.find x sub = Some y -> HasType Γ' x ty -> HasType Γ'' y ty) ->
      (forall x y, Env.find x sub = Some y -> IsLast Γ' x -> IsLast Γ'' y) ->
      Forall noswitch_block blks ->
      Forall (NoDupLocals (map fst Γ++map fst Γ'++map fst Γ'')) blks ->
      Forall (GoodLocals switch_prefs) blks ->
      Forall (wt_block G (Γ++Γ')) blks ->
      mmap2 (inlinelocal_block sub) blks st = (locs', blks', st') ->
      Forall (wt_block G (Γ ++ Γ''++senv_of_decls (concat locs'))) (concat blks') /\
      Forall (fun '(_, (_, ck, _, _)) => wt_clock G.(types) (Γ++Γ''++senv_of_decls (concat locs')) ck) (concat locs').
  Proof.
    intros * F Hnin Hsubin Hsubgen Hty Hlast Hns Hnd Hgood Hwc Hmmap.
    split; apply Forall_concat.
    - eapply mmap2_values, Forall3_ignore12 in Hmmap. simpl_Forall.
      take (inlinelocal_block _ _ _ = _) and eapply F in it as (?&?); eauto.
      simpl_Forall.
      eapply wt_block_incl; [| |eauto].
      1,2:intros * In; rewrite app_assoc in *; eauto with senv.
    - eapply mmap2_values, Forall3_ignore13 in Hmmap. simpl_Forall.
      take (inlinelocal_block _ _ _ = _) and eapply F in it as (?&?); eauto.
      simpl_Forall.
      eapply wt_clock_incl; [|eauto].
      intros * In; rewrite app_assoc in *; eauto with senv.
  Qed.

  Lemma inlinelocal_block_wt {PSyn prefs} (G: @global PSyn prefs) Γ : forall blk sub Γ' Γ'' locs' blks' st st',
      (forall x, InMembers x Γ -> ~InMembers x Γ') ->
      (forall x, Env.In x sub <-> InMembers x Γ') ->
      (forall x y, Env.find x sub = Some y -> InMembers y Γ' \/ exists n hint, y = gensym local hint n) ->
      (forall x y ty, Env.find x sub = Some y -> HasType Γ' x ty -> HasType Γ'' y ty) ->
      (forall x y, Env.find x sub = Some y -> IsLast Γ' x -> IsLast Γ'' y) ->
      noswitch_block blk ->
      NoDupLocals (map fst Γ++map fst Γ'++map fst Γ'') blk ->
      GoodLocals switch_prefs blk ->
      wt_block G (Γ++Γ') blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall (wt_block G (Γ++Γ''++senv_of_decls locs')) blks' /\
      Forall (fun '(_, (_, ck, _, _)) => wt_clock G.(types) (Γ++Γ''++senv_of_decls locs') ck) locs'.
  Proof.
    induction blk using block_ind2; intros * Hnin Hsubin Hsubgen Hty Hlast Hns Hnd Hgood Hwt Hdl;
      inv Hns; inv Hnd; inv Hgood; inv Hwt; repeat monadInv.

    - (* equation *)
      split; auto. rewrite app_nil_r.
      do 2 constructor; auto.
      eapply rename_equation_wt; eauto with ltyping.

    - (* last *)
      split; auto. rewrite app_nil_r.
      do 2 econstructor; eauto 6 using rename_var_wt, rename_var_IsLast, rename_exp_wt with ltyping.
      setoid_rewrite rename_exp_typeof; auto.

    - (* reset *)
      eapply mmap_inlinelocal_block_wt in H0 as (Wt&Wtc); eauto.
      repeat constructor; auto.
      + eapply rename_exp_wt in H7; eauto using in_or_app with ltyping.
        1:eapply HasType_sub1; eauto. 2:eapply HasType_sub2; eauto.
        1,2:(intros; eapply HasType_app; left; eauto).
        1:eapply IsLast_sub1; eauto. 2:eapply IsLast_sub2; eauto.
        1,2:(intros; eapply IsLast_app; left; eauto).
      + now setoid_rewrite rename_exp_typeof.

    - (* local *)
      repeat inv_scope. subst Γ'0.

      assert (forall y, Env.In y (Env.from_list (combine (map fst locs) x)) <-> InMembers y locs) as Hsubin'.
      { intros.
        rewrite Env.In_from_list, <-In_InMembers_combine, fst_InMembers; try reflexivity.
        now apply mmap_values, Forall2_length in H0. }

      take (forall x, InMembers x locs -> ~_) and rename it into Hnd'; eauto.

      assert (forall y, Env.In y sub -> ~In y (map fst locs)) as Hsub1.
      { intros ?. rewrite Hsubin. intros In1 In2.
        eapply Hnd'; eauto with datatypes. rewrite 2 in_app_iff; eauto with datatypes. }
      assert (forall x1 x2, Env.MapsTo x1 x2 sub -> ~In x2 (map fst locs)) as Hsub2.
      { intros ?? Hin1 Hin2.
        eapply Hsubgen in Hin1 as [Hin|(?&?&Hgen)]; subst.
        - simpl_In. eapply Hnd'; eauto using In_InMembers. rewrite 2 in_app_iff; eauto with datatypes.
        - simpl_In. simpl_Forall.
          eapply Fresh.Facts.contradict_AtomOrGensym; eauto using local_not_in_switch_prefs. }

      rewrite senv_of_decls_app, 2 app_assoc, <-app_assoc with (m:=Γ''). rewrite Forall_app.

      eapply mmap_inlinelocal_block_wt with (Γ':=Γ'++senv_of_decls locs) in H as (Wt&Wtc). 11:eauto. all:eauto.
      + rewrite app_assoc in Wt, Wtc. repeat split; eauto.
        unfold wt_clocks, idfst, senv_of_decls in *. simpl_Forall.
        erewrite <-disjoint_union_rename_in_clock; eauto.
        eapply rename_clock_wt, rename_clock_wt
          with (Γ':=(Γ++Γ'')++senv_of_decls (map (fun '(x, (ty, ck, cx, clx)) => (x, (ty, rename_clock sub ck, cx, clx))) locs)).
        5:eauto with ltyping.
        3:{ intros * Hfind In. repeat rewrite HasType_app in *. destruct In as [[In|In]|In]; eauto.
            1,2:exfalso.
            - eapply Hnin, Hsubin. 2:econstructor; eauto.
              clear - In. inv In. solve_In.
            - eapply Hnd'.
              2:{ repeat rewrite in_app_iff. right. left. eapply fst_InMembers, Hsubin. econstructor; eauto. }
              clear - In. inv In. solve_In.
        }
        3:{ intros * Hfind In. repeat rewrite HasType_app in *. destruct In as [[In|In]|In]; eauto.
            - exfalso. inv In. eapply In_InMembers, Hsubin in H2 as (?&Find').
              rewrite Find' in Hfind. congruence.
            - right. clear - In. inv In. simpl_In. econstructor. solve_In. auto.
        }
        1:{ intros * Find In.
            repeat rewrite HasType_app in *. destruct In as [[In|In]|In]; eauto.
            1,2:exfalso; apply Env.from_list_find_In, in_combine_l, fst_InMembers in Find.
            - exfalso. eapply Hnd'; eauto.
              clear - In. inv In. repeat rewrite in_app_iff. left. solve_In.
            - exfalso. eapply Hnd'; eauto.
              clear - In. inv In. repeat rewrite in_app_iff. right. right. solve_In.
            - left. right. right.
              inv In. simpl_In. eapply reuse_idents_find in H0 as (?&?&?&Reu&Find'); eauto using In_InMembers.
              unfold Env.adds, Env.from_list in *. rewrite Find' in Find. inv Find.
              econstructor. solve_In. unfold rename_var. erewrite Env.find_gsss'_irrelevant; simpl; eauto. 2:auto.
              apply Env.find_adds'_In in Find' as [|Find]; eauto using In_InMembers.
              rewrite Env.gempty in Find. congruence.
        }
        1:{ intros * Find In.
            repeat rewrite HasType_app in *. destruct In as [[In|In]|In]; eauto.
            - exfalso. inv In. simpl_In.
              eapply In_InMembers, Hsubin' in Hin0 as (?&Find'). unfold Env.MapsTo in *.
              setoid_rewrite Find in Find'. inv Find'.
        }
      + intros ? Hin. rewrite InMembers_app, not_or', InMembers_senv_of_decls.
        split; auto. intro contra.
        eapply Hnd'; eauto.
        apply in_or_app, or_introl, fst_InMembers; auto.
      + intros. rewrite Env.In_adds_spec, InMembers_app, Hsubin, InMembers_senv_of_decls, <-fst_InMembers; eauto using mmap_values, Forall2_length.
        apply or_comm.
      + intros ?? Hfind. rewrite InMembers_app, InMembers_senv_of_decls.
         eapply Env.find_adds'_In in Hfind as [Hfind|Hfind]; eauto.
         * eapply in_combine_r in Hfind.
           eapply reuse_idents_gensym in H0. simpl_Forall. destruct H0; eauto.
         * eapply Hsubgen in Hfind as [|]; eauto.
      + intros * Hfind Hin. apply HasType_app.
        eapply HasType_app in Hin as [Hin|Hin].
        * assert (Env.find x3 (Env.from_list (combine (map fst locs) x)) = None) as Hnone.
          { inv Hin.
            destruct (Env.find x3 (Env.from_list (combine (map fst locs) x))) eqn:Hfind'; eauto.
            exfalso. apply Env.from_list_find_In, in_combine_l in Hfind'.
            eapply Hnd'; eauto with datatypes. rewrite 2 in_app_iff; eauto with datatypes. }
          apply Env.adds_from_list in Hfind as [Hfind|Hfind]; eauto.
          setoid_rewrite Hfind in Hnone. congruence.
        * right. inv Hin. simpl_In. eapply reuse_idents_find in H0 as (?&?&?&Reu&Find); eauto using In_InMembers.
          setoid_rewrite Hfind in Find. inv Find.
          econstructor. unfold senv_of_decls. solve_In.
          unfold rename_var. setoid_rewrite Hfind. simpl. eauto. reflexivity.
      + intros * Hfind Hin. apply IsLast_app.
        eapply IsLast_app in Hin as [Hin|Hin].
        * assert (Env.find x3 (Env.from_list (combine (map fst locs) x)) = None) as Hnone.
          { inv Hin.
            destruct (Env.find x3 (Env.from_list (combine (map fst locs) x))) eqn:Hfind'; eauto.
            exfalso. apply Env.from_list_find_In, in_combine_l in Hfind'.
            eapply Hnd'; eauto with datatypes. rewrite 2 in_app_iff; eauto with datatypes. }
          apply Env.adds_from_list in Hfind as [Hfind|Hfind]; eauto.
          setoid_rewrite Hfind in Hnone. congruence.
        * right. inv Hin. simpl_In. eapply reuse_idents_find in H0 as (?&?&?&Reu&Find); eauto using In_InMembers.
          setoid_rewrite Hfind in Find. inv Find.
          econstructor. unfold senv_of_decls. solve_In.
          unfold rename_var. setoid_rewrite Hfind. simpl. eauto. simpl. auto.
      + simpl_app. simpl_Forall.
        eapply NoDupLocals_incl'. 4:eauto. all:eauto using local_not_in_switch_prefs.
        intros *. repeat rewrite in_app_iff.
        intros [|[|[In|[In|In]]]]; auto.
        * clear - In. simpl_In. left. right. right. right. solve_In.
        * clear - H0 H10 In. simpl_In.
          eapply reuse_idents_find in H0 as (?&?&?&Reu&Find); eauto using In_InMembers.
          unfold rename_var. rewrite Find.
          eapply reuse_ident_gensym in Reu as [|]; subst; eauto.
          left. right. right. right. solve_In.
      + take (Forall (wt_block _ _) _) and rewrite <-app_assoc in it; auto.
  Qed.

  (** Used enum types are correct *)

  Lemma inlinelocal_block_wt_type {PSyn prefs} (G: @global PSyn prefs) : forall blk sub Γ locs' blks' st st',
      noswitch_block blk ->
      wt_block G Γ blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall (fun '(_, (ty, _, _, _)) => wt_type G.(types) ty) locs'.
  Proof.
    induction blk using block_ind2; intros * Hns Hwt Hdl;
      inv Hns; inv Hwt; repeat monadInv; auto.

    - (* reset *)
      apply Forall_concat.
      eapply mmap2_values, Forall3_ignore13 in H0. simpl_Forall.
      take (inlinelocal_block _ _ _ = _) and eapply H in it; eauto. now simpl_Forall.

    - (* local *)
      repeat inv_scope.
      apply Forall_app; split.
      + now simpl_Forall.
      + apply Forall_concat.
        eapply mmap2_values, Forall3_ignore13 in H2. simpl_Forall.
        take (inlinelocal_block _ _ _ = _) and eapply H in it; eauto. now simpl_Forall.
  Qed.

  (** Typing of the node *)

  Lemma inlinelocal_node_wt : forall G1 G2 (n : @node _ _),
      global_iface_incl G1 G2 ->
      wt_node G1 n ->
      wt_node G2 (inlinelocal_node n).
  Proof.
    intros * Hiface Hwt. inversion_clear Hwt as [?? Wt1 Wt2 Wt3 Wt4 Wt5]; subst Γ.
    pose proof (n_nodup n) as (_&Hnd2).
    pose proof (n_good n) as (_&Hgood&_).
    pose proof (n_syn n) as Hsyn. inversion_clear Hsyn as [?? Syn1 Syn2].
    econstructor.
    1-2:unfold wt_clocks in *; simpl_Forall; eauto with ltyping.
    1,2:simpl_Forall; subst; eauto using iface_incl_wt_type.
    simpl. destruct (inlinelocal_block _ _ _) as ((?&?)&?) eqn:Il. assert (Il':=Il).
    eapply inlinelocal_block_wt with (Γ':=[]) (Γ'':=[]) in Il' as (Wt&Wtc); repeat rewrite app_nil_r; eauto using node_NoDupLocals.
    (* 2:(apply NoLast_app; split; eauto using senv_of_ins_NoLast; *)
    (*    intros ? L; inv L; simpl_In; simpl_Forall; subst; simpl in *; congruence). *)
    2:intros; rewrite Env.Props.P.F.empty_in_iff; split; intros [].
    2,3,4:intros * Find; rewrite Env.gempty in Find; inv Find.
    simpl. repeat econstructor; eauto.
    - (* clocks *)
      unfold wt_clocks, idfst. simpl_Forall. simpl_In. simpl_Forall. eauto with ltyping.
    - eapply inlinelocal_block_wt_type in Il; eauto. simpl_Forall. eauto with ltyping.
    - simpl_Forall. eauto with ltyping.
  Qed.

  Theorem inlinelocal_global_wt : forall G,
      wt_global G ->
      wt_global (inlinelocal_global G).
  Proof.
    unfold wt_global, inlinelocal_global.
    intros * (?&Hwt).
    split; auto.
    eapply CommonTyping.transform_units_wt_program; eauto.
    intros ?? Hwt'.
    eapply inlinelocal_node_wt; eauto. eapply iface_eq_iface_incl, inlinelocal_global_iface_eq.
  Qed.

End ILTYPING.

Module ILTypingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LTYPING Ids Op OpAux Cks Senv Syn)
       (IL  : INLINELOCAL Ids Op OpAux Cks Senv Syn)
       <: ILTYPING Ids Op OpAux Cks Senv Syn Clo IL.
  Include ILTYPING Ids Op OpAux Cks Senv Syn Clo IL.
End ILTypingFun.
