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
From Velus Require Import Lustre.SubClock.SCTyping.

Module Type ILTYPING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import IL  : INLINELOCAL Ids Op OpAux Cks Senv Syn).

  Module Import SCT := SCTypingFun Ids Op OpAux Cks Senv Syn Typ SC. Import SC.

  Import Fresh Facts Tactics.

  Fact In_sub1 : forall vars1 vars2 vars3 sub,
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

  Fact In_sub2 : forall vars1 vars2 vars3 sub,
      (forall x, Env.In x sub <-> InMembers x vars2) ->
      (forall x y ty, Env.find x sub = Some y -> HasType vars2 x ty -> HasType vars3 y ty) ->
      forall x ty, Env.find x sub = None -> HasType (vars1 ++ vars2) x ty -> HasType (vars1 ++ vars3) x ty.
  Proof.
    intros * Hsubin Hsub * Hfind Hin.
    rewrite HasType_app in *. destruct Hin as [Hin|Hin]; eauto.
    exfalso. inv Hin. eapply In_InMembers, Hsubin in H as (?&?).
    congruence.
  Qed.

  Global Hint Resolve In_sub1 In_sub2 : ltyping.

  Definition st_senv st := senv_of_tyck (st_anns st).

  Fact mmap_inlinelocal_block_wt {PSyn prefs} (G: @global PSyn prefs) sub Γ Γ' : forall blks blks' st st',
      Forall (fun blk => forall sub Γ' blks' st st',
                  (forall x, ~IsLast (Γ ++ Γ') x) ->
                  (forall x, InMembers x Γ -> ~InMembers x Γ') ->
                  (forall x, Env.In x sub <-> InMembers x Γ') ->
                  (forall x y ty, Env.find x sub = Some y -> HasType Γ' x ty -> HasType (st_senv st) y ty) ->
                  noswitch_block blk ->
                  NoDupLocals (map fst Γ++map fst Γ') blk ->
                  GoodLocals switch_prefs blk ->
                  wt_block G (Γ++Γ') blk ->
                  Forall (wt_clock (enums G) (Γ ++ st_senv st)) (map (fun '(_, (_, ck)) => ck) (st_anns st)) ->
                  st_valid_after st local PS.empty ->
                  inlinelocal_block sub blk st = (blks', st') ->
                  Forall (wt_block G (Γ ++ st_senv st')) blks' /\
                  Forall (wt_clock (enums G) (Γ ++ st_senv st')) (map (fun '(_, (_, ck)) => ck) (st_anns st'))) blks ->
      (forall x, ~IsLast (Γ ++ Γ') x) ->
      (forall x, InMembers x Γ -> ~InMembers x Γ') ->
      (forall x, Env.In x sub <-> InMembers x Γ') ->
      (forall x y ty, Env.find x sub = Some y -> HasType Γ' x ty -> HasType (st_senv st) y ty) ->
      Forall noswitch_block blks ->
      Forall (NoDupLocals (map fst Γ++map fst Γ')) blks ->
      Forall (GoodLocals switch_prefs) blks ->
      Forall (wt_block G (Γ++Γ')) blks ->
      Forall (wt_clock (enums G) (Γ ++ st_senv st)) (map (fun '(_, (_, ck)) => ck) (st_anns st)) ->
      st_valid_after st local PS.empty ->
      mmap (inlinelocal_block sub) blks st = (blks', st') ->
      Forall (wt_block G (Γ ++ st_senv st')) (concat blks') /\
      Forall (wt_clock (enums G) (Γ ++ st_senv st')) (map (fun '(_, (_, ck)) => ck) (st_anns st')).
  Proof.
    induction blks; intros * Hf Hnl Hnin Hsubin Hsub Hns Hnd Hgood Hwt Hwtc Hvalid Hmmap;
      inv Hf; inv Hns; inv Hnd; inv Hgood; inv Hwt; repeat inv_bind; simpl; auto.
    assert (Hdl:=H). eapply H1 in H as (?&?); eauto.
    assert (Hmap:=H0). eapply IHblks in H0 as (?&?); eauto.
    2:{ intros * Hfind Hin.
        eapply HasType_incl; eauto. eapply incl_map, st_follows_incl; eauto with fresh. }
    2:eapply inlinelocal_block_st_valid_after; eauto.
    constructor; auto.
    apply Forall_app. split; eauto.
    eapply Forall_impl; [|eauto]; intros.
    assert (st_follows x0 st') as Hfollows.
    { eapply mmap_st_follows; eauto. simpl_Forall; eauto with fresh. }
    eapply wt_block_incl; [| |eauto].
    - intros * Hty. rewrite HasType_app in *. destruct Hty; auto; right.
      eapply HasType_incl; eauto. eapply incl_map, st_follows_incl; eauto.
    - intros * Hty. rewrite IsLast_app in *. destruct Hty; auto; right.
      eapply IsLast_incl; eauto. eapply incl_map, st_follows_incl; eauto.
  Qed.

  Lemma inlinelocal_block_wt {PSyn prefs} (G: @global PSyn prefs) Γ : forall blk sub Γ' blks' st st',
      (forall x, ~IsLast (Γ ++ Γ') x) ->
      (forall x, InMembers x Γ -> ~InMembers x Γ') ->
      (forall x, Env.In x sub <-> InMembers x Γ') ->
      (forall x y ty, Env.find x sub = Some y -> HasType Γ' x ty -> HasType (st_senv st) y ty) ->
      noswitch_block blk ->
      NoDupLocals (map fst Γ++map fst Γ') blk ->
      GoodLocals switch_prefs blk ->
      wt_block G (Γ++Γ') blk ->
      Forall (wt_clock G.(enums) (Γ++st_senv st)) (map (fun '(_, (_, ck)) => ck) (st_anns st)) ->
      st_valid_after st local PS.empty ->
      inlinelocal_block sub blk st = (blks', st') ->
      Forall (wt_block G (Γ++st_senv st')) blks' /\
      Forall (wt_clock G.(enums) (Γ++st_senv st')) (map (fun '(_, (_, ck)) => ck) (st_anns st')).
  Proof.
    induction blk using block_ind2; intros * Hnl Hnin Hsubin Hsub Hns Hnd Hgood Hwt Hwtc Hvalid Hdl;
      inv Hns; inv Hnd; inv Hgood; inv Hwt; repeat inv_bind.

    - (* equation *)
      split; auto.
      do 2 constructor; auto.
      eapply subclock_equation_wt; eauto with ltyping.

    - (* reset *)
      repeat constructor; auto.
      + eapply mmap_inlinelocal_block_wt; eauto.
      + eapply subclock_exp_wt; eauto using in_or_app with ltyping.
        eapply In_sub1; eauto. 2:eapply In_sub2; eauto.
        1,2:(intros; eapply HasType_incl; [|eauto];
             eapply incl_map, st_follows_incl, mmap_st_follows; eauto;
             eapply Forall_forall; eauto with fresh).
      + now setoid_rewrite subclock_exp_typeof.
      + eapply mmap_inlinelocal_block_wt; eauto.

    - (* local *)
      assert (forall x, Env.In x x0 <-> InMembers x locs) as Hsubin'.
      { split; intros * Hin.
        * eapply fresh_idents_rename_sub1 in Hin; [|eauto].
          unfold idty in *. erewrite fst_InMembers, map_map, map_ext, <-fst_InMembers in Hin; eauto.
          intros; destruct_conjs; auto.
        * eapply fresh_idents_rename_sub2 in H0.
          unfold idty in *. erewrite fst_InMembers, map_map, map_ext, <-fst_InMembers in H0; eauto.
          2:intros; destruct_conjs; auto.
          apply H0 in Hin as (?&?&?&_); eauto. econstructor; eauto.
      }
      inv H3. inv H1. inv H6.
      eapply mmap_inlinelocal_block_wt with (Γ':=Γ'++senv_of_locs locs) in H. 1,12:eauto. 1-10:eauto.
      + rewrite app_assoc, NoLast_app. split; auto.
        intros * Hl. inv Hl; simpl_In. simpl_Forall. subst; simpl in *; congruence.
      + intros ? Hin. rewrite InMembers_app, not_or', InMembers_senv_of_locs.
        split; auto. intro contra.
        eapply H13; eauto. apply in_or_app, or_introl, fst_InMembers; auto.
      + intros. rewrite Env.union_In, InMembers_app, Hsubin.
        apply or_iff_compat_l.
        now rewrite InMembers_senv_of_locs.
      + intros * Hfind Hin.
        eapply HasType_app in Hin as [Hin|Hin].
        * assert (Env.find x3 x0 = None) as Hone.
          { inv Hin. eapply In_InMembers, fst_InMembers in H1.
            destruct (Env.find x3 x0) eqn:Hfind'; eauto.
            exfalso. eapply H13; eauto using in_or_app. eapply fst_InMembers.
            eapply fresh_idents_rename_sub1 in H0. 2:econstructor; eauto.
            erewrite fst_InMembers, map_map, map_ext in H0; eauto.
            intros; destruct_conjs; auto. }
          eapply Env.union_find4 in Hfind as [Hfind|Hfind]; try congruence.
          eapply HasType_incl; eauto using incl_map, st_follows_incl, fresh_idents_rename_st_follows.
        * unfold st_senv. erewrite fresh_idents_rename_anns; [|eauto].
          unfold senv_of_tyck. simpl_app. apply HasType_app, or_introl.
          assert (Hfresh:=H0). eapply fresh_idents_rename_sub2 in H0 as ((?&?&Hmap&_)&_).
          { inv Hin. simpl_In. eapply In_InMembers. solve_In. }
          unfold Env.MapsTo in *. erewrite Env.union_find3' in Hfind; [|eauto]. inv Hfind.
          eapply fresh_idents_rename_ids in Hfresh. rewrite Hfresh.
          2:{ apply nodupmembers_map; auto. intros; destruct_conjs; auto. }
          inv Hin. simpl_In. econstructor; solve_In. rewrite Hmap; simpl; eauto. reflexivity.
      + rewrite map_app, map_fst_senv_of_locs, app_assoc; auto.
      + rewrite <-app_assoc in H19; auto.
      + erewrite fresh_idents_rename_anns; [|eauto].
        simpl_app. apply Forall_app; split.
        * assert (Hfresh:=H0). eapply fresh_idents_rename_ids in H0. rewrite H0.
          2:{ apply nodupmembers_map; auto. intros; destruct_conjs; auto. }
          unfold wt_clocks in H15. rewrite Forall_forall in H8. simpl_Forall.
          eapply subclock_clock_wt, subclock_clock_wt with (Γ':=Γ++senv_of_locs locs++st_senv st). 3,6,7:eauto with ltyping.
          4:{ intros ?? Hfind Hin. repeat rewrite HasType_app in *. destruct Hin as [|[Hin|]]; eauto.
              exfalso. inv Hin. eapply In_InMembers, Hsubin in H3. inv H3; congruence.
          }
          3:{ intros ??? Hfind Hin. repeat rewrite HasType_app in *. destruct Hin as [Hin|[|Hin]]; eauto.
              - exfalso. inv Hin. eapply In_InMembers, Hnin in H3.
                eapply H3, Hsubin. econstructor; eauto.
              - exfalso. inv Hin. simpl_In.
                eapply H13; eauto using In_InMembers.
                eapply in_or_app, or_intror, fst_InMembers.
                eapply Hsubin. econstructor; eauto. }
          2:{ intros ?? Hfind Hin. repeat rewrite HasType_app in *. destruct Hin as [|[Hin|]]; eauto.
              - exfalso. inv Hin. simpl_In.
                apply In_InMembers, Hsubin' in Hin. inv Hin. congruence.
              - right. eapply HasType_incl; eauto. apply incl_map, st_follows_incl; eauto.
                eapply fresh_idents_rename_st_follows; eauto. }
          { intros ??? Hfind Hin.
            unfold st_senv. erewrite fresh_idents_rename_anns; eauto.
            unfold senv_of_tyck. simpl_app.
            eapply fresh_idents_rename_sub1 in Hfresh. 2:econstructor; eauto.
            erewrite fst_InMembers, map_map, map_ext, <-fst_InMembers in Hfresh.
            2:intros; destruct_conjs; auto.
            repeat rewrite HasType_app in *. destruct Hin as [Hin|[Hin|Hin]]; auto.
            - exfalso. inv Hin. eapply In_InMembers, fst_InMembers in H3.
              eapply H13, in_or_app, or_introl; eauto.
            - inv Hin. simpl_In. right; left.
              econstructor. solve_In. rewrite Hfind. 1,2:reflexivity.
            - exfalso. inv Hin. unfold st_senv. simpl_In.
              apply In_InMembers, fst_InMembers in Hin.
              eapply st_valid_after_AtomOrGensym_nIn in Hin; eauto using local_not_in_switch_prefs.
              apply H8, fst_InMembers; auto.
          }
        * simpl_Forall.
          eapply wt_clock_incl; [|eauto].
          intros *. rewrite 2 HasType_app. intros [|]; auto; right.
          eapply HasType_incl; eauto. eapply incl_map, st_follows_incl, fresh_idents_rename_st_follows; eauto.
      + eapply fresh_idents_rename_st_valid; eauto.
  Qed.

  Lemma inlinelocal_topblock_wt {PSyn prefs} (G: @global PSyn prefs) Γ : forall blk blks' locs' st st',
      (forall x, ~IsLast Γ x) ->
      noswitch_block blk ->
      NoDupLocals (map fst Γ) blk ->
      GoodLocals switch_prefs blk ->
      wt_block G Γ blk ->
      Forall (wt_clock G.(enums) (Γ++st_senv st)) (map (fun '(_, (_, ck)) => ck) (st_anns st)) ->
      st_valid_after st local PS.empty ->
      inlinelocal_topblock blk st = (blks', locs', st') ->
      Forall (wt_block G (Γ++senv_of_locs locs'++st_senv st')) blks' /\
      Forall (wt_clock G.(enums) (Γ++senv_of_locs locs'++st_senv st'))
             (map (fun '(_, (_, ck, _, _)) => ck) locs'++map (fun '(_, (_, ck)) => ck) (st_anns st')).
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hnl Hns Hnd Hgood Hwt Hwtc Hvalid Hil; try destruct s; repeat inv_bind; simpl. 3:inv Hns.
    1-3:eapply inlinelocal_block_wt with (Γ':=[]); try rewrite app_nil_r; eauto.
    7:inv Hnd; inv Hgood; inv Hwt; inv H1; inv H2; inv H4; inv_VarsDefined;
      eapply mmap_inlinelocal_block_wt with (Γ:=Γ++senv_of_locs locs') (Γ':=[]) in H as (Hwt1&Hwt2); try rewrite app_nil_r; eauto.
    2,4,6,11:intros * Hfind _; rewrite Env.gempty in Hfind; try congruence.
    1,2,3,7:intros *; rewrite Env.Props.P.F.empty_in_iff; split; intros [].
    - rewrite <-app_assoc in Hwt1, Hwt2. split; eauto.
      apply Forall_app. unfold wt_clocks, Common.idty in H8. split; auto; simpl_Forall.
      eapply wt_clock_incl; [|eauto]. intros *. repeat rewrite HasType_app. intros [|]; auto.
    - eapply Forall_forall; intros; eauto using inlinelocal_block_wt.
    - apply NoLast_app; split; auto.
      intros * Hl. inv Hl. simpl_In. inv Hns. simpl_Forall; subst; simpl in *; congruence.
    - inv Hns; auto.
    - rewrite map_app, map_fst_senv_of_locs; auto.
    - eapply Forall_impl; [|eauto]; intros.
      eapply wt_clock_incl; [|eauto]. intros *. repeat rewrite HasType_app. intros [|]; auto.
    Transparent inlinelocal_block.
  Qed.

  (** Used enum types are correct *)

  Fact mmap_inlinelocal_block_wt_enum {PSyn prefs} (G: @global PSyn prefs) : forall blks sub xs Γ blks' st st',
      Forall
        (fun blk => forall sub xs Γ blks' st st',
             noswitch_block blk ->
             NoDupLocals xs blk ->
             wt_block G Γ blk ->
             Forall (wt_enum G) (map (fun '(_, (ty, _)) => ty) (st_anns st)) ->
             inlinelocal_block sub blk st = (blks', st') ->
             Forall (wt_enum G) (map (fun '(_, (ty, _)) => ty) (st_anns st'))) blks ->
      Forall noswitch_block blks ->
      Forall (NoDupLocals xs) blks ->
      Forall (wt_block G Γ) blks ->
      Forall (wt_enum G) (map (fun '(_, (ty, _)) => ty) (st_anns st)) ->
      mmap (inlinelocal_block sub) blks st = (blks', st') ->
      Forall (wt_enum G) (map (fun '(_, (ty, _)) => ty) (st_anns st')).
  Proof.
    induction blks; intros * Hnd Hf Hns Hwt Henums Hmap;
      inv Hnd; inv Hf; inv Hns; inv Hwt; repeat inv_bind; eauto.
  Qed.

  Lemma inlinelocal_block_wt_enum {PSyn prefs} (G: @global PSyn prefs) : forall blk sub xs Γ blks' st st',
      noswitch_block blk ->
      NoDupLocals xs blk ->
      wt_block G Γ blk ->
      Forall (wt_enum G) (map (fun '(_, (ty, _)) => ty) (st_anns st)) ->
      inlinelocal_block sub blk st = (blks', st') ->
      Forall (wt_enum G) (map (fun '(_, (ty, _)) => ty) (st_anns st')).
  Proof.
    induction blk using block_ind2; intros * Hns Hnd Hwt Hf Hdl;
      inv Hns; inv Hnd; inv Hwt; repeat inv_bind; auto.

    - (* reset *)
      eapply mmap_inlinelocal_block_wt_enum in H0; eauto.

    - (* local *)
      inv H3. inv H5.
      eapply mmap_inlinelocal_block_wt_enum in H1; eauto.
      erewrite fresh_idents_rename_anns; [|eauto].
      rewrite map_app. apply Forall_app; split; auto.
      eapply fresh_idents_rename_ids in H0.
      2:{ apply nodupmembers_map; auto. intros; destruct_conjs; auto. }
      rewrite H0. simpl_Forall. auto.
  Qed.

  Lemma inlinelocal_topblock_wt_enum {PSyn prefs} (G: @global PSyn prefs) : forall blk xs Γ blks' locs' st st',
      noswitch_block blk ->
      NoDupLocals xs blk ->
      wt_block G Γ blk ->
      Forall (wt_enum G) (map (fun '(_, (ty, _)) => ty) (st_anns st)) ->
      inlinelocal_topblock blk st = (blks', locs', st') ->
      Forall (wt_enum G) (map (fun '(_, (ty, _, _, _)) => ty) locs'++map (fun '(_, (ty, _)) => ty) (st_anns st')).
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hns Hnd Hwt Hwte Hil; try destruct s; repeat inv_bind; simpl.
    1-4:eapply inlinelocal_block_wt_enum; eauto.
    inv Hns. inv Hwt; inv H3. inv Hnd; inv H3.
    repeat setoid_rewrite map_app. apply Forall_app; split; auto.
    eapply mmap_inlinelocal_block_wt_enum in H; eauto.
    eapply Forall_forall; intros; eauto using inlinelocal_block_wt_enum.
    Transparent inlinelocal_block.
  Qed.

  (** Typing of the node *)

  Lemma inlinelocal_node_wt : forall G1 G2 (n : @node _ _),
      global_iface_incl G1 G2 ->
      wt_node G1 n ->
      wt_node G2 (inlinelocal_node n).
  Proof.
    intros * Hiface (Hwt1&Hwt2&Hwt3&Hwt4).
    pose proof (n_nodup n) as (_&Hnd2).
    pose proof (n_good n) as (_&Hgood&_).
    pose proof (n_syn n) as Hsyn.
    repeat econstructor; simpl; eauto.
    1-2:unfold wt_clocks in *; simpl_Forall; eauto with ltyping.
    simpl_Forall; eauto using iface_incl_wt_enum.
    1-4:destruct (inlinelocal_topblock _ _) as ((?&?)&?) eqn:Hdl.
    - (* clocks *)
      eapply inlinelocal_topblock_wt with (Γ:=senv_of_inout (n_in n ++ n_out n)) in Hdl as (?&?); try rewrite app_nil_r; simpl; eauto.
      + simpl_app. unfold wt_clocks in *. apply Forall_app in H0 as (?&?).
        rewrite Forall_app; split; simpl_Forall.
        * erewrite map_ext with (l:=l0), map_map, map_ext with (l:=st_anns f); eauto using iface_incl_wt_clock.
          intros; destruct_conjs; auto.
        * erewrite map_ext with (l:=l0), map_map, map_ext with (l:=st_anns f); eauto using iface_incl_wt_clock.
          intros; destruct_conjs; auto.
      + apply senv_of_inout_NoLast.
      + rewrite map_fst_senv_of_inout. apply n_nodup.
      + rewrite init_st_anns; simpl; auto.
      + eapply init_st_valid; eauto using local_not_in_switch_prefs, PS_For_all_empty.
    - (* enums *)
      eapply inlinelocal_topblock_wt_enum, Forall_app in Hdl as (?&?); eauto.
      2:{ rewrite init_st_anns; simpl; auto. }
      simpl_app. apply Forall_app; split; simpl_Forall; eauto using iface_incl_wt_enum.
    - simpl_Forall. apply in_app_iff in H as [|]; simpl_In; auto.
      eapply inlinelocal_topblock_nolast in Hdl; eauto.
      simpl_Forall; subst; simpl; auto.
    - (* blocks *)
      eapply inlinelocal_topblock_wt with (Γ:=senv_of_inout (n_in n ++ n_out n)) in Hdl as (?&?); try rewrite app_nil_r; simpl; eauto.
      + eapply Forall_impl; [|eauto]; intros ? Hwt.
        eapply iface_incl_wt_block; eauto. clear - Hwt.
        simpl_app. repeat rewrite map_map in *; simpl in *.
        erewrite map_ext with (l:=l0), map_ext with (l:=st_anns f).
        eapply wt_block_incl; eauto.
        1,2:intros; destruct_conjs; auto.
      + apply senv_of_inout_NoLast.
      + rewrite map_fst_senv_of_inout. apply n_nodup.
      + rewrite init_st_anns; simpl; auto.
      + eapply init_st_valid; eauto using local_not_in_switch_prefs, PS_For_all_empty.
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
