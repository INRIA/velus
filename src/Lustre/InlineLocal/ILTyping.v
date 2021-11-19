From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Omega.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.LSyntax Lustre.LTyping.
From Velus Require Import Lustre.InlineLocal.InlineLocal.

Module Type ILTYPING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (Import Clo : LTYPING Ids Op OpAux Cks Syn)
       (Import IL  : INLINELOCAL Ids Op OpAux Cks Syn).

  Section rename_in_clock.
    Variable sub : Env.t ident.
    Variable vars vars' : list (ident * Op.type).

    Hypothesis Hsub : forall x y ty,
        Env.find x sub = Some y ->
        In (x, ty) vars ->
        In (y, ty) vars'.

    Hypothesis Hnsub : forall x ty,
        Env.find x sub = None ->
        In (x, ty) vars ->
        In (x, ty) vars'.

    Lemma rename_in_var_wt : forall x ty,
        In (x, ty) vars ->
        In (rename_in_var sub x, ty) vars'.
    Proof.
      intros * Hin.
      unfold rename_in_var.
      destruct (Env.find _ _) eqn:Hfind; eauto.
    Qed.

    Lemma rename_in_clock_wt : forall enums ck,
        wt_clock enums vars ck ->
        wt_clock enums vars' (rename_in_clock sub ck).
    Proof.
      induction ck; intros * Hwc; inv Hwc; simpl; auto.
      - constructor.
      - constructor; eauto using rename_in_var_wt.
    Qed.

  End rename_in_clock.

  Lemma rename_in_sub : forall x y (ty : Op.type) sub xs,
      Env.find x sub = Some y ->
      In (x, ty) (idty xs) ->
      In (y, ty) (idty (map (fun '(x0, (ty0, ck)) => (rename_in_var sub x0, (ty0, rename_in_clock sub ck))) xs)).
  Proof.
    intros * Hfind Hin.
    eapply In_idty_exists in Hin as (ck&Hin).
    unfold idty. rewrite map_map, in_map_iff; simpl.
    exists (x, (ty, ck)). split; simpl; auto.
    f_equal.
    unfold rename_in_var. now rewrite Hfind.
  Qed.

  Lemma rename_in_nsub : forall x (ty : Op.type) sub xs,
      Env.find x sub = None ->
      In (x, ty) (idty xs) ->
      In (x, ty) (idty (map (fun '(x0, (ty0, ck)) => (rename_in_var sub x0, (ty0, rename_in_clock sub ck))) xs)).
  Proof.
    intros * Hfind Hin.
    eapply In_idty_exists in Hin as (ck&Hin).
    unfold idty. rewrite map_map, in_map_iff; simpl.
    exists (x, (ty, ck)). split; simpl; auto.
    f_equal.
    unfold rename_in_var. now rewrite Hfind.
  Qed.

  Lemma rename_in_nsub' : forall x (ty : Op.type) sub xs,
      Env.find x sub = None ->
      In (x, ty) (idty xs) ->
      In (x, ty) (idty (map (fun '(x0, (ty0, ck)) => (x0, (ty0, rename_in_clock sub ck))) xs)).
  Proof.
    intros * Hfind Hin.
    eapply In_idty_exists in Hin as (ck&Hin).
    unfold idty. rewrite map_map, in_map_iff; simpl.
    exists (x, (ty, ck)). split; simpl; auto.
  Qed.

  Section rename.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Variable sub : Env.t ident.

    Section rename_in_exp.
      Variable vars vars' : list (ident * Op.type).

      Hypothesis Hsub : forall x y ty,
          Env.find x sub = Some y ->
          In (x, ty) vars ->
          In (y, ty) vars'.

      Hypothesis Hnsub : forall x ty,
          Env.find x sub = None ->
          In (x, ty) vars ->
          In (x, ty) vars'.

      Lemma rename_in_exp_typeof : forall e,
          typeof (rename_in_exp sub e) = typeof e.
      Proof.
        induction e using exp_ind2; simpl; auto. 3:destruct x; simpl; auto.
        1-3:repeat rewrite map_map; simpl; auto.
      Qed.

      Corollary rename_in_exp_typesof : forall es,
          typesof (map (rename_in_exp sub) es) = typesof es.
      Proof.
        induction es; simpl; auto.
        f_equal; auto using rename_in_exp_typeof.
      Qed.

      Lemma rename_in_exp_wt : forall e,
          wt_exp G vars e ->
          wt_exp G vars' (rename_in_exp sub e).
      Proof.
        intros * Hwc; induction e using exp_ind2; inv Hwc; simpl;
          econstructor; eauto using rename_in_var_wt, rename_in_clock_wt.
        1-38:try solve [rewrite Forall_map, Forall_forall in *; intros; eauto].
        1-31:try rewrite rename_in_exp_typeof; simpl; auto.
        1-26:try rewrite rename_in_exp_typesof; simpl; auto.
        1-23:try rewrite map_map; eauto.
        - rewrite Forall_map in *.
          eapply Forall_impl; [|eauto]; intros; simpl in *; eauto using rename_in_clock_wt.
        - rewrite Forall_map in *.
          eapply Forall_impl; [|eauto]; intros; simpl in *; eauto using rename_in_clock_wt.
        - erewrite map_ext; eauto. intros (?&?); auto.
        - contradict H6. apply map_eq_nil in H6; auto.
        - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite Forall_map.
          specialize (H _ Hin). specialize (H7 _ Hin).
          rewrite Forall_forall in *; eauto.
        - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl.
          rewrite rename_in_exp_typesof. eapply H8 in Hin; eauto.
        - erewrite map_ext; eauto. intros (?&?); auto.
        - contradict H9. apply map_eq_nil in H9; auto.
        - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite Forall_map.
          specialize (H _ Hin). specialize (H10 _ Hin).
          rewrite Forall_forall in *; eauto.
        - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl.
          rewrite rename_in_exp_typesof. eapply H11 in Hin; eauto.
        - erewrite map_ext; eauto. intros (?&?); auto.
        - erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; auto.
          intros (?&?); auto.
        - contradict H9. apply map_eq_nil in H9; auto.
        - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite Forall_map.
          specialize (H _ Hin). specialize (H11 _ Hin).
          rewrite Forall_forall in *; eauto.
        - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl.
          rewrite rename_in_exp_typesof. eapply H12 in Hin; eauto.
        - simpl in *. rewrite Forall_map, Forall_forall in *; eauto.
        - rewrite Forall2_map_1. eapply Forall2_impl_In; [|eauto]; intros (?&?) (?&(?&?)&?) ???; subst; auto.
        - rewrite Forall_map. eapply Forall_impl; [|eauto]; intros ??; simpl in *.
          rewrite rename_in_exp_typeof; auto.
        - rewrite Forall_map. eapply Forall_impl; [|eauto]; intros ??; simpl in *.
          eapply rename_in_clock_wt; eauto.
      Qed.

      Lemma rename_in_equation_wt : forall eq,
          wt_equation G vars eq ->
          wt_equation G vars' (rename_in_equation sub eq).
      Proof.
        intros (?&?) (Hwt1&Hwt2).
        simpl. constructor.
        - rewrite Forall_map. eapply Forall_impl; eauto using rename_in_exp_wt.
        - rewrite rename_in_exp_typesof, Forall2_map_1.
          eapply Forall2_impl_In; [|eauto]; eauto using rename_in_var_wt.
      Qed.

    End rename_in_exp.

  End rename.

  Import Fresh Facts Tactics.

  Fact In_sub1 {B} : forall (vars1 vars2 vars3 : list (ident * B)) sub,
      (forall x, InMembers x vars1 -> ~InMembers x vars2) ->
      (forall x, Env.In x sub <-> InMembers x vars2) ->
      (forall x y ty, Env.find x sub = Some y -> In (x, ty) vars2 -> In (y, ty) vars3) ->
      forall x y ty, Env.find x sub = Some y -> In (x, ty) (vars1 ++ vars2) -> In (y, ty) (vars1 ++ vars3).
  Proof.
    intros * Hnd Hsubin Hsub * Hfind Hin.
    rewrite in_app_iff in *. destruct Hin as [Hin|Hin]; eauto.
    exfalso. eapply In_InMembers, Hnd in Hin.
    eapply Hin, Hsubin. econstructor; eauto.
  Qed.

  Fact In_sub2 {B} : forall (vars1 vars2 vars3 : list (ident * B)) sub,
      (forall x, Env.In x sub <-> InMembers x vars2) ->
      (forall x y ty, Env.find x sub = Some y -> In (x, ty) vars2 -> In (y, ty) vars3) ->
      forall x ty, Env.find x sub = None -> In (x, ty) (vars1 ++ vars2) -> In (x, ty) (vars1 ++ vars3).
  Proof.
    intros * Hsubin Hsub * Hfind Hin.
    rewrite in_app_iff in *. destruct Hin as [Hin|Hin]; eauto.
    exfalso. eapply In_InMembers, Hsubin in Hin as (?&?).
    congruence.
  Qed.

  Hint Resolve In_sub1 In_sub2.

  Fact mmap_inlinelocal_block_wt {PSyn prefs} (G: @global PSyn prefs) sub vars vars' : forall blks blks' st st',
      Forall (fun blk => forall sub vars' blks' st st',
                  (forall x, InMembers x vars -> ~InMembers x vars') ->
                  (forall x, Env.In x sub <-> InMembers x vars') ->
                  (forall x y ty, Env.find x sub = Some y -> In (x, ty) vars' -> In (y, ty) (idty (st_anns st))) ->
                  noswitch_block blk ->
                  NoDupLocals (map fst vars++map fst vars') blk ->
                  GoodLocals switch_prefs blk ->
                  wt_block G (vars++vars') blk ->
                  Forall (wt_clock (enums G) (vars ++ idty (st_anns st))) (map snd (idck (st_anns st))) ->
                  st_valid_after st local PS.empty ->
                  inlinelocal_block sub blk st = (blks', st') ->
                  Forall (wt_block G (vars ++ idty (st_anns st'))) blks' /\
                  Forall (wt_clock (enums G) (vars ++ idty (st_anns st'))) (map snd (idck (st_anns st')))) blks ->
      (forall x, InMembers x vars -> ~InMembers x vars') ->
      (forall x, Env.In x sub <-> InMembers x vars') ->
      (forall x y ty, Env.find x sub = Some y -> In (x, ty) vars' -> In (y, ty) (idty (st_anns st))) ->
      Forall noswitch_block blks ->
      Forall (NoDupLocals (map fst vars++map fst vars')) blks ->
      Forall (GoodLocals switch_prefs) blks ->
      Forall (wt_block G (vars++vars')) blks ->
      Forall (wt_clock (enums G) (vars ++ idty (st_anns st))) (map snd (idck (st_anns st))) ->
      st_valid_after st local PS.empty ->
      mmap (inlinelocal_block sub) blks st = (blks', st') ->
      Forall (wt_block G (vars ++ idty (st_anns st'))) (concat blks') /\
      Forall (wt_clock (enums G) (vars ++ idty (st_anns st'))) (map snd (idck (st_anns st'))).
  Proof.
    induction blks; intros * Hf Hnin Hsubin Hsub Hns Hnd Hgood Hwt Hwtc Hvalid Hmmap;
      inv Hf; inv Hns; inv Hnd; inv Hgood; inv Hwt; repeat inv_bind; simpl; auto.
    assert (Hdl:=H). eapply H1 in H as (?&?); eauto.
    assert (Hmap:=H0). eapply IHblks in H0 as (?&?); eauto.
    2:{ intros * Hfind Hin.
        eapply incl_map; [|eauto]. eapply st_follows_incl; eauto. }
    2:eapply inlinelocal_block_st_valid_after; eauto.
    constructor; auto.
    apply Forall_app. split; eauto.
    eapply Forall_impl; [|eauto]; intros.
    eapply wt_block_incl; [|eauto]. eapply incl_appr', incl_map, st_follows_incl, mmap_st_follows; eauto.
    eapply Forall_forall; eauto.
  Qed.

  Lemma inlinelocal_block_wt {PSyn prefs} (G: @global PSyn prefs) vars : forall blk sub vars' blks' st st',
      (forall x, InMembers x vars -> ~InMembers x vars') ->
      (forall x, Env.In x sub <-> InMembers x vars') ->
      (forall x y ty, Env.find x sub = Some y -> In (x, ty) vars' -> In (y, ty) (idty (st_anns st))) ->
      noswitch_block blk ->
      NoDupLocals (map fst vars++map fst vars') blk ->
      GoodLocals switch_prefs blk ->
      wt_block G (vars++vars') blk ->
      Forall (wt_clock G.(enums) (vars++idty (st_anns st))) (map snd (idck (st_anns st))) ->
      st_valid_after st local PS.empty ->
      inlinelocal_block sub blk st = (blks', st') ->
      Forall (wt_block G (vars++idty (st_anns st'))) blks' /\
      Forall (wt_clock G.(enums) (vars++idty (st_anns st'))) (map snd (idck (st_anns st'))).
  Proof.
    induction blk using block_ind2; intros * Hnin Hsubin Hsub Hns Hnd Hgood Hwt Hwtc Hvalid Hdl;
      inv Hns; inv Hnd; inv Hgood; inv Hwt; repeat inv_bind.
    - (* equation *)
      split; auto.
      do 2 constructor; auto.
      eapply rename_in_equation_wt; [| |eauto]; eauto using in_or_app.
    - (* reset *)
      repeat constructor; auto.
      + eapply mmap_inlinelocal_block_wt; eauto.
      + eapply rename_in_exp_wt; [| |eauto]; eauto using in_or_app.
        eapply In_sub1; eauto. 2:eapply In_sub2; eauto.
        1,2:(intros; eapply incl_map; [|eauto];
             eapply st_follows_incl, mmap_st_follows; eauto;
             eapply Forall_forall; eauto).
      + now rewrite rename_in_exp_typeof.
      + eapply mmap_inlinelocal_block_wt; eauto.
    - (* local *)
      eapply mmap_inlinelocal_block_wt with (vars'0:=vars'++idty (idty locs)) in H. 1,11:eauto. 4-9:eauto.
      + intros ? Hin. rewrite InMembers_app, not_or', 2 InMembers_idty.
        split; auto. intro contra.
        eapply H6; eauto. apply in_or_app, or_introl, fst_InMembers; auto.
      + intros. rewrite Env.union_In, InMembers_app, Hsubin.
        apply or_iff_compat_l.
        rewrite 2 InMembers_idty.
        split; intros * Hin.
        * eapply fresh_idents_rename_sub1 in Hin; [|eauto].
          unfold idty in *. erewrite fst_InMembers, 2 map_map, map_ext, <-fst_InMembers in Hin; eauto.
          intros (?&(?&?)&?); auto.
        * eapply fresh_idents_rename_sub2 in H0.
          unfold idty in *. erewrite fst_InMembers, 2 map_map, map_ext, <-fst_InMembers in H0; eauto.
          2:intros (?&(?&?)&?); auto.
          apply H0 in Hin as (?&?&?&_); eauto. econstructor; eauto.
      + intros * Hfind Hin.
        eapply in_app_or in Hin as [Hin|Hin].
        * assert (Env.find x3 x0 = None) as Hone.
          { eapply In_InMembers in Hin. rewrite fst_InMembers in Hin.
            destruct (Env.find x3 x0) eqn:Hfind'; eauto.
            exfalso. eapply H6; eauto using in_or_app. eapply fst_InMembers.
            eapply fresh_idents_rename_sub1 in H0. 2:econstructor; eauto.
            erewrite fst_InMembers, map_map, map_ext, map_fst_idty in H0; eauto.
            intros (?&?&?); auto. }
          eapply Env.union_find4 in Hfind as [Hfind|Hfind]; try congruence.
          eapply incl_map; eauto using st_follows_incl, fresh_idents_rename_st_follows.
        * erewrite fresh_idents_rename_anns; [|eauto].
          rewrite idty_app. apply in_or_app, or_introl.
          assert (Hfresh:=H0). eapply fresh_idents_rename_sub2 in H0 as ((?&?&Hmap&_)&_).
          { eapply In_InMembers in Hin. rewrite 2 InMembers_idty, fst_InMembers in Hin.
            unfold idty. erewrite fst_InMembers, 2 map_map, map_ext; eauto.
            intros (?&(?&?)&?); auto. }
          unfold Env.MapsTo in *. erewrite Env.union_find3' in Hfind; [|eauto]. inv Hfind.
          eapply fresh_idents_rename_ids in Hfresh. rewrite Hfresh.
          2:{ unfold idty. erewrite fst_NoDupMembers, 2 map_map, map_ext, <-fst_NoDupMembers; auto.
              intros (?&(?&?)&?); auto. }
          repeat eapply In_idty_exists in Hin as (?&Hin).
          unfold idty. rewrite 3 map_map. eapply in_map_iff.
          do 2 esplit; eauto. simpl.
          rewrite Hmap; auto.
      + rewrite map_app, 2 map_fst_idty, app_assoc; auto.
      + rewrite <-app_assoc in H8; auto.
      + erewrite fresh_idents_rename_anns; [|eauto].
        rewrite idty_app, idck_app, map_app.
        apply Forall_app; split.
        * assert (Hfresh:=H0). eapply fresh_idents_rename_ids in H0. rewrite H0.
          2:{ unfold idty. erewrite fst_NoDupMembers, 2 map_map, map_ext, <-fst_NoDupMembers; auto.
              intros (?&(?&?)&?); auto. }
          unfold wt_clocks in H10.
          unfold idck at 1, idty at 4. repeat rewrite map_map; rewrite Forall_map.
          eapply Forall_impl; [|eauto]. intros (?&(?&?)&?) Hwt; simpl.
          eapply rename_in_clock_wt, rename_in_clock_wt with (vars':=vars++idty (idty locs)++idty (st_anns st)). 5:eauto.
          4:{ intros ?? Hfind Hin. repeat rewrite in_app_iff in *. destruct Hin as [[|Hin]|]; auto.
              eapply In_InMembers, Hsubin in Hin as (?&?). congruence. }
          3:{ intros ??? Hfind Hin. repeat rewrite in_app_iff in *. destruct Hin as [[Hin|]|Hin]; eauto.
              - exfalso. eapply In_InMembers, Hnin in Hin.
                eapply Hin, Hsubin. econstructor; eauto.
              - exfalso. eapply In_InMembers in Hin. rewrite 2 InMembers_idty in Hin.
                eapply H6; eauto.
                eapply in_or_app, or_intror, fst_InMembers.
                eapply Hsubin. econstructor; eauto. }
          2:{ intros ?? Hfind Hin. repeat rewrite in_app_iff in *. destruct Hin as [|[Hin|]]; auto.
              right; left. unfold idty at 1.
              do 2 eapply In_idty_exists in Hin as (?&Hin).
              unfold idty. repeat rewrite map_map. eapply in_map_iff. do 2 esplit; [|eauto].
              simpl. rewrite Hfind; auto. }
          { intros ??? Hfind Hin.
            eapply fresh_idents_rename_sub1 in Hfresh. 2:econstructor; eauto.
            erewrite fst_InMembers, map_map, map_ext, map_fst_idty, <-fst_InMembers in Hfresh.
            2:intros (?&?&?); auto.
            repeat rewrite in_app_iff in *. destruct Hin as [Hin|[Hin|Hin]]; auto.
            - exfalso. eapply In_InMembers, fst_InMembers in Hin.
              eapply H6, in_or_app, or_introl; eauto.
            - right; left.
              do 2 eapply In_idty_exists in Hin as (?&Hin).
              unfold idty. repeat rewrite map_map. eapply in_map_iff. do 2 esplit; [|eauto].
              simpl. rewrite Hfind; auto.
            - exfalso. eapply In_InMembers in Hin. rewrite InMembers_idty, fst_InMembers in Hin.
              rewrite fst_InMembers in Hfresh.
              eapply st_valid_after_AtomOrGensym_nIn in Hin; eauto using local_not_in_switch_prefs.
              eapply Forall_forall in H4; eauto.
          }
        * eapply Forall_impl; [|eauto]; intros.
          eapply wt_clock_incl; [|eauto]; solve_incl_app.
      + eapply fresh_idents_rename_st_valid; eauto.
  Qed.

  Lemma inlinelocal_topblock_wt {PSyn prefs} (G: @global PSyn prefs) vars : forall blk blks' locs' st st',
      noswitch_block blk ->
      NoDupLocals (map fst vars) blk ->
      GoodLocals switch_prefs blk ->
      wt_block G vars blk ->
      Forall (wt_clock G.(enums) (vars++idty (st_anns st))) (map snd (idck (st_anns st))) ->
      st_valid_after st local PS.empty ->
      inlinelocal_topblock blk st = (blks', locs', st') ->
      Forall (wt_block G (vars++idty (idty locs')++idty (st_anns st'))) blks' /\
      Forall (wt_clock G.(enums) (vars++idty (idty locs')++idty (st_anns st'))) (map snd (idck (idty locs'++st_anns st'))).
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hns Hnd Hgood Hwt Hwtc Hvalid Hil; repeat inv_bind; simpl. 3:inv Hns.
    1,2:eapply inlinelocal_block_wt with (vars':=[]); try rewrite app_nil_r; eauto.
    5:inv Hnd; inv Hgood; inv Hwt;
      eapply mmap_inlinelocal_block_wt with (vars':=[]) in H as (Hwt1&Hwt2); try rewrite app_nil_r; eauto.
    2,4,8:intros * Hfind [].
    1,2,5:intros *; rewrite Env.Props.P.F.empty_in_iff; split; intros [].
    - rewrite <-app_assoc in Hwt1, Hwt2. split; auto.
      rewrite idck_app, map_app, Forall_app. split; auto.
      unfold wt_clocks in H9. do 3 setoid_rewrite Forall_map.
      eapply Forall_impl; [|eauto]; intros (?&(?&?)&?) ?.
      eapply wt_clock_incl; [|eauto]. solve_incl_app.
    - eapply Forall_forall; intros; eauto using inlinelocal_block_wt.
    - inv Hns; auto.
    - rewrite map_app, 2 map_fst_idty; auto.
    - eapply Forall_impl; [|eauto]; intros.
      eapply wt_clock_incl; [|eauto]. solve_incl_app.
    Transparent inlinelocal_block.
  Qed.

  (** Used enum types are correct *)

  Fact mmap_inlinelocal_block_wt_enum {PSyn prefs} (G: @global PSyn prefs) : forall blks sub xs vars blks' st st',
      Forall
        (fun blk => forall sub xs vars blks' st st',
             NoDupLocals xs blk ->
             wt_block G vars blk ->
             Forall (wt_enum G) (map snd (idty (st_anns st))) ->
             inlinelocal_block sub blk st = (blks', st') ->
             Forall (wt_enum G) (map snd (idty (st_anns st')))) blks ->
      Forall (NoDupLocals xs) blks ->
      Forall (wt_block G vars) blks ->
      Forall (wt_enum G) (map snd (idty (st_anns st))) ->
      mmap (inlinelocal_block sub) blks st = (blks', st') ->
      Forall (wt_enum G) (map snd (idty (st_anns st'))).
  Proof.
    induction blks; intros * Hnd Hf Hwt Henums Hmap;
      inv Hnd; inv Hf; inv Hwt; repeat inv_bind; eauto.
  Qed.

  Lemma inlinelocal_block_wt_enum {PSyn prefs} (G: @global PSyn prefs) : forall blk sub xs vars blks' st st',
      NoDupLocals xs blk ->
      wt_block G vars blk ->
      Forall (wt_enum G) (map snd (idty (st_anns st))) ->
      inlinelocal_block sub blk st = (blks', st') ->
      Forall (wt_enum G) (map snd (idty (st_anns st'))).
  Proof.
    induction blk using block_ind2; intros * Hnd Hwt Hf Hdl;
      inv Hnd; inv Hwt; repeat inv_bind; auto.
    - (* reset *)
      eapply mmap_inlinelocal_block_wt_enum in H0; eauto.
    - (* local *)
      eapply mmap_inlinelocal_block_wt_enum in H1; eauto.
      erewrite fresh_idents_rename_anns; [|eauto].
      rewrite idty_app, map_app. apply Forall_app; split; auto.
      eapply fresh_idents_rename_ids in H0.
      2:{ erewrite fst_NoDupMembers, map_map, map_ext, map_fst_idty, <-fst_NoDupMembers; eauto.
          intros (?&?&?); auto. }
      rewrite H0.
      unfold idty in *.
      repeat rewrite map_map in *; simpl. erewrite map_ext; [eauto|]. intros (?&(?&?)&?); auto.
  Qed.

  Lemma inlinelocal_topblock_wt_enum {PSyn prefs} (G: @global PSyn prefs) : forall blk xs vars blks' locs' st st',
      NoDupLocals xs blk ->
      wt_block G vars blk ->
      Forall (wt_enum G) (map snd (idty (st_anns st))) ->
      inlinelocal_topblock blk st = (blks', locs', st') ->
      Forall (wt_enum G) (map snd (idty (idty locs'++st_anns st'))).
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hnd Hwt Hwte Hil; repeat inv_bind; simpl.
    1,2,3:eapply inlinelocal_block_wt_enum; eauto.
    inv Hwt. inv Hnd.
    repeat setoid_rewrite map_app. rewrite Forall_app. split; auto.
    eapply mmap_inlinelocal_block_wt_enum in H; eauto.
    eapply Forall_forall; intros; eauto using inlinelocal_block_wt_enum.
    Transparent inlinelocal_block.
  Qed.

  (** Typing of the node *)

  Lemma inlinelocal_node_wt : forall G1 G2 (n : @node _ _),
      global_iface_eq G1 G2 ->
      wt_node G1 n ->
      wt_node G2 (inlinelocal_node n).
  Proof.
    intros * Hiface (Hwt1&Hwt2&Hwt3&Hwt4).
    pose proof (n_nodup n) as (_&Hnd2).
    pose proof (n_good n) as (_&Hgood&_).
    pose proof (n_syn n) as Hsyn.
    repeat constructor; simpl; eauto.
    1,2:destruct Hiface as (Heq&_); rewrite <-Heq; auto.
    eapply Forall_impl; [|eauto]; intros; eauto using iface_eq_wt_enum.
    1-3:destruct (inlinelocal_topblock _ _) as ((?&?)&?) eqn:Hdl.
    - (* blocks *)
      eapply inlinelocal_topblock_wt with (vars:=idty (idty (n_in n ++ n_out n))) in Hdl as (?&?); try rewrite app_nil_r; simpl; eauto.
      + eapply Forall_impl; [|eauto]; intros ? Hwt.
        eapply iface_eq_wt_block; eauto. clear - Hwt.
        rewrite (idty_app l0), (idty_app (idty l0)). unfold idty at 5, idty at 5. repeat rewrite map_map; simpl.
        eapply Hwt.
      + rewrite 2 map_fst_idty.
        eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
      + rewrite init_st_anns; simpl; auto.
      + eapply init_st_valid; eauto using local_not_in_switch_prefs, PS_For_all_empty.
    - (* clocks *)
      eapply inlinelocal_topblock_wt with (vars:=idty (idty (n_in n ++ n_out n))) in Hdl as (?&?); try rewrite app_nil_r; simpl; eauto.
      + repeat rewrite idty_app in *. rewrite idck_app, map_app, Forall_app in H0. repeat setoid_rewrite Forall_map in H0. destruct H0 as (Hck1&Hck2).
        setoid_rewrite Forall_app. rewrite Forall_map.
        split; (eapply Forall_impl; [|eauto]); intros (?&(?&?)) Hwtc. destruct p. 1,2:simpl in *; eauto.
        * unfold idty at 7, idty at 7. repeat rewrite map_map; simpl; eauto using iface_eq_wt_clock.
        * unfold idty at 7, idty at 7. repeat rewrite map_map; simpl; eauto using iface_eq_wt_clock.
      + rewrite 2 map_fst_idty.
        eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
      + rewrite init_st_anns; simpl; auto.
      + eapply init_st_valid; eauto using local_not_in_switch_prefs, PS_For_all_empty.
    - (* enums *)
      eapply inlinelocal_topblock_wt_enum in Hdl; eauto.
      2:{ rewrite init_st_anns; simpl; auto. }
      unfold idty in *. repeat rewrite map_map in *; simpl in *.
      rewrite map_app, Forall_app, 3 Forall_map in Hdl. destruct Hdl.
      rewrite map_app, Forall_app, 3 Forall_map; split; auto.
      1,2:eapply Forall_impl; [|eauto]; eauto using iface_eq_wt_enum.
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
    eapply inlinelocal_node_wt; eauto. eapply inlinelocal_global_iface_eq.
  Qed.

End ILTYPING.

Module ILTypingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (Clo : LTYPING Ids Op OpAux Cks Syn)
       (IL  : INLINELOCAL Ids Op OpAux Cks Syn)
       <: ILTYPING Ids Op OpAux Cks Syn Clo IL.
  Include ILTYPING Ids Op OpAux Cks Syn Clo IL.
End ILTypingFun.
