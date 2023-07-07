From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Coq Require Import List. Import List.ListNotations. Open Scope list_scope.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping.
From Velus Require Import Lustre.NormFby.NormFby.
From Velus Require Import Lustre.SubClock.SCTyping.

Module Type NFTYPING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import NF  : NORMFBY Ids Op OpAux Cks Senv Syn).

  Import Fresh Facts Tactics.

  Module Import SCT := SCTypingFun Ids Op OpAux Cks Senv Syn Typ SC. Import SC.

  Ltac solve_incl :=
    match goal with
    | Hiface : global_iface_incl ?G1 ?G2, H : wt_clock (types ?G1) _ ?ck |- wt_clock (types ?G2) _ ?ck =>
        eapply iface_incl_wt_clock; eauto
    | H : wt_clock _ ?l1 ?cl |- wt_clock _ ?l2 ?cl =>
        eapply wt_clock_incl; [|eauto]; intros
    | Hiface : global_iface_incl ?G1 ?G2, H : wt_exp ?G1 _ ?e |- wt_exp ?G2 _ ?e =>
        eapply iface_incl_wt_exp; eauto
    | H : wt_exp ?G ?l1 ?e |- wt_exp ?G ?l2 ?e =>
        eapply wt_exp_incl; [| |eauto]; intros
    | H : wt_equation ?G ?l1 ?eq |- wt_equation ?G ?l2 ?eq =>
        eapply wt_equation_incl; [| |eauto]; intros
    | Hiface : global_iface_incl ?G1 ?G2, H : wt_block ?G1 _ ?e |- wt_block ?G2 _ ?e =>
        eapply iface_incl_wt_block; eauto
    | H : wt_block ?G ?l1 ?eq |- wt_block ?G ?l2 ?eq =>
        eapply wt_block_incl; [| |eauto]; intros
    | |- incl ?l1 ?l1 => reflexivity
    | |- incl ?l1 (?l1 ++ ?l2) =>
        eapply incl_appl; reflexivity
    | |- incl (?l1 ++ ?l2) (?l1 ++ ?l3) =>
        eapply incl_app
    | |- incl ?l1 (?l2 ++ ?l3) =>
        eapply incl_appr
    | |- incl ?l1 (?a::?l2) =>
        eapply incl_tl
    | |- incl (st_anns ?st1) (st_anns _) =>
        eapply st_follows_incl; repeat solve_st_follows
    | |- incl (st_senv ?st1) (st_senv _) =>
        apply incl_map; repeat solve_st_follows
    | H : In ?x ?l1 |- In ?x ?l2 =>
        assert (incl l1 l2); eauto
    | H : HasType ?l1 ?x ?ty |- HasType ?l2 ?x ?ty =>
        eapply HasType_incl; [|eauto]
    | H : IsLast ?l1 ?x |- IsLast ?l2 ?x =>
        eapply IsLast_incl; [|eauto]
    end; auto with datatypes.

  Fact fby_iteexp_typeof : forall e0 e ann e' eqs' st st',
      fby_iteexp e0 e ann st = (e', eqs', st') ->
      typeof e' = [fst ann].
  Proof.
    intros ?? [ty ck] e' eqs' st st' Hfby.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind; try reflexivity.
  Qed.

  Section normfby_node_wt.
    Variable G1 : @global normlast last_prefs.
    Variable G2 : @global normalized fby_prefs.

    Hypothesis Hiface : global_iface_incl G1 G2.
    Hypothesis Hbool : wt_type G1.(types) bool_velus_type.
    Hint Resolve iface_incl_wt_clock iface_incl_wt_exp : norm.

    Fact init_var_for_clock_wt_eq : forall vars ck id eqs' st st' ,
        wt_clock G1.(types) (vars++st_senv st) ck ->
        init_var_for_clock ck st = (id, eqs', st') ->
        Forall (wt_equation G2 (vars++st_senv st')) eqs'.
    Proof with eauto.
      intros * Hck Hinit.
      unfold init_var_for_clock in Hinit.
      destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
        repeat constructor; simpl; repeat rewrite app_nil_r; auto.
        1,2:eapply add_whens_wt; eauto.
        2,4:constructor; simpl; auto.
        5,6:eapply add_whens_typeof; simpl; auto.
        1-6:repeat solve_incl. 1,2:eapply iface_incl_wt_type; eauto.
        eapply fresh_ident_In in Hfresh.
        eapply HasType_app; right; unfold st_senv, idty; econstructor; solve_In. auto.
    Qed.

    Fact fby_iteexp_wt_exp : forall vars e0 e ty ck e' eqs' st st' ,
        wt_clock G1.(types) (vars++st_senv st) ck ->
        wt_exp G1 (vars++st_senv st) e0 ->
        wt_exp G1 (vars++st_senv st) e ->
        typeof e0 = [ty] ->
        typeof e = [ty] ->
        fby_iteexp e0 e (ty, ck) st = (e', eqs', st') ->
        wt_exp G2 (vars++st_senv st') e'.
    Proof.
      intros * Hwtc Hwt1 Hwt2 Hty1 Hty2 Hfby.
      unfold fby_iteexp in Hfby; repeat inv_bind.
      econstructor; repeat constructor; simpl in *; try rewrite app_nil_r; eauto.
      2,5,6,7,8:repeat solve_incl; eapply init_var_for_clock_st_follows in H; repeat solve_st_follows.
      - apply init_var_for_clock_In in H as In.
        eapply HasType_incl with (senv1:=st_senv x1). repeat solve_incl.
        econstructor; solve_In. auto.
      - apply fresh_ident_In in H0.
        apply HasType_app, or_intror; econstructor; solve_In; auto.
      - apply Hiface; auto. now inv Hbool.
      - congruence.
    Qed.

    Fact arrow_iteexp_wt_exp : forall vars e0 e ty ck e' eqs' st st' ,
        wt_clock G1.(types) (vars++st_senv st) ck ->
        wt_exp G1 (vars++st_senv st) e0 ->
        wt_exp G1 (vars++st_senv st) e ->
        typeof e0 = [ty] ->
        typeof e = [ty] ->
        arrow_iteexp e0 e (ty, ck) st = (e', eqs', st') ->
        wt_exp G2 (vars++st_senv st') e'.
    Proof.
      intros * Hwtc Hwt1 Hwt2 Hty1 Hty2 Hfby.
      unfold arrow_iteexp in Hfby; repeat inv_bind.
      econstructor; repeat constructor; simpl in *; try rewrite app_nil_r; auto.
      2,5,6,7:repeat solve_incl; eapply init_var_for_clock_st_follows in H; repeat solve_st_follows.
      - apply init_var_for_clock_In in H as In.
        apply HasType_app, or_intror; econstructor; solve_In; auto.
      - apply Hiface; auto. now inv Hbool.
      - congruence.
    Qed.

    Hypothesis HwtG1 : wt_global G1.

    Fact fby_iteexp_wt_eq : forall vars e0 e ty ck e' eqs' st st' ,
        Forall (wt_type G1.(types)) (map (fun '(_, a) => a.(typ)) vars) ->
        wt_clock G1.(types) (vars++st_senv st) ck ->
        wt_exp G1 vars e0 ->
        wt_exp G1 vars e ->
        typeof e0 = [ty] ->
        typeof e = [ty] ->
        fby_iteexp e0 e (ty, ck) st = (e', eqs', st') ->
        Forall (wt_equation G2 (vars++st_senv st')) eqs'.
    Proof.
      intros * Htypes Hwtc Hwt1 Hwt2 Hty1 Hty2 Hfby.
      unfold fby_iteexp in Hfby; repeat inv_bind; auto.
      assert (wt_clock G1.(types) (vars ++ st_senv st') ck) as Hwtck'.
      { repeat solve_incl; eapply init_var_for_clock_st_follows in H; repeat solve_st_follows. }
      constructor.
      - repeat constructor; simpl; try rewrite app_nil_r; eauto with norm.
        + eapply add_whens_wt; eauto.
          * repeat solve_incl.
          * destruct ty; simpl; auto.
            now rewrite Op.ctype_init_ctype.
          * destruct ty; simpl; [constructor|]; auto.
            eapply wt_exp_wt_type in Hwt1; eauto.
            rewrite Hty1 in Hwt1. apply Forall_singl in Hwt1.
            constructor; eauto with ltyping. now inv Hwt1.
        + repeat solve_incl; eapply init_var_for_clock_st_follows in H; repeat solve_st_follows.
        + eapply add_whens_typeof.
          destruct ty; simpl; auto. now rewrite Op.ctype_init_ctype.
        + apply fresh_ident_In in H0.
          apply HasType_app, or_intror. econstructor; solve_In. auto.
      - eapply init_var_for_clock_wt_eq with (vars:=vars) in H; eauto.
        eapply Forall_impl; [|eauto]; intros; repeat solve_incl.
    Qed.

    Fact arrow_iteexp_wt_eq : forall vars e0 e ty ck e' eqs' st st' ,
        wt_clock G1.(types) (vars++st_senv st) ck ->
        arrow_iteexp e0 e (ty, ck) st = (e', eqs', st') ->
        Forall (wt_equation G2 (vars++st_senv st')) eqs'.
    Proof.
      intros * Hwtc Hfby.
      unfold arrow_iteexp in Hfby. repeat inv_bind.
      eapply init_var_for_clock_wt_eq in H; eauto.
    Qed.

    Fact normfby_equation_wt_eq : forall vars to_cut eq eqs' st st' ,
        Forall (wt_type G1.(types)) (map (fun '(_, a) => a.(typ)) vars) ->
        wt_equation G1 vars eq ->
        normfby_equation to_cut eq st = (eqs', st') ->
        Forall (wt_equation G2 (vars++st_senv st')) eqs'.
    Proof.
      intros * Htypes Hwt Hfby.
      inv_normfby_equation Hfby to_cut eq.
      - (* constant fby *)
        destruct x2 as (?&?). destruct (PS.mem x to_cut); repeat inv_bind; auto.
        destruct Hwt as [Hwt Hin]. apply Forall_singl in Hwt. apply Forall2_singl in Hin.
        inv Hwt. apply Forall_singl in H4. apply Forall_singl in H3.
        apply Forall_singl in H7.
        repeat (constructor; auto).
        1-8:repeat solve_incl.
        + apply fresh_ident_In in H. apply HasType_app, or_intror. econstructor; solve_In. auto.
        + apply fresh_ident_In in H. apply HasType_app, or_intror. econstructor; solve_In. auto.
        + destruct Hwt. constructor; eauto.
          eapply iface_incl_wt_equation; eauto.
          constructor; auto. 1,2:simpl_Forall; repeat solve_incl.
      - (* fby *)
        destruct x2 as (ty&ck).
        assert (st_follows st st') as Hfollows by (eapply fby_iteexp_st_follows with (ann:=(ty, ck)) in H; eauto).
        destruct Hwt as [Hwt Hins]. apply Forall_singl in Hwt. apply Forall2_singl in Hins.
        inv Hwt.
        simpl in *; rewrite app_nil_r in *.
        apply Forall_singl in H3; apply Forall_singl in H4.
        apply Forall_singl in H7.
        assert (Hwte:=H). eapply fby_iteexp_wt_exp with (vars:=vars) in Hwte; eauto.
        assert (Hty:=H). eapply (fby_iteexp_typeof _ _ (ty, ck)) in Hty; eauto.
        assert (Hwteq:=H). eapply fby_iteexp_wt_eq in Hwteq; eauto.
        repeat constructor; auto.
        simpl; rewrite app_nil_r, Hty. repeat constructor. 1-5:repeat solve_incl.
      - (* arrow *)
        destruct x2 as [ty ck].
        destruct Hwt as [Hwt Hins]. apply Forall_singl in Hwt. apply Forall2_singl in Hins.
        inv Hwt.
        simpl in *; rewrite app_nil_r in *.
        apply Forall_singl in H3; apply Forall_singl in H4.
        apply Forall_singl in H7.
        assert (Hwte:=H). eapply arrow_iteexp_wt_exp with (vars:=vars) in Hwte; eauto. 2-4:repeat solve_incl.
        assert (Hwteq:=H). eapply arrow_iteexp_wt_eq with (vars:=vars) in Hwteq; eauto. 2:repeat solve_incl.
        assert (st_follows st st') as Hfollows.
        { repeat inv_bind. eapply init_var_for_clock_st_follows; eauto. }
        repeat inv_bind.
        econstructor; auto. econstructor; repeat constructor; auto.
        apply HasType_app; auto.
      - destruct Hwt. constructor; auto. constructor; auto.
        1,2:simpl_Forall; repeat solve_incl.
    Qed.

    Fact normfby_block_wt : forall vars to_cut d blocks' st st' ,
        Forall (wt_type G1.(types)) (map (fun '(_, a) => a.(typ)) vars) ->
        wt_block G1 vars d ->
        normfby_block to_cut d st = (blocks', st') ->
        Forall (wt_block G2 (vars++st_senv st')) blocks'.
    Proof.
      induction d using block_ind2; intros * Htypes Hwt Hnorm.
      - (* equation *)
        inv Hwt; repeat inv_bind.
        eapply normfby_equation_wt_eq in H; eauto.
        rewrite Forall_map. eapply Forall_impl; [|eauto].
        intros; constructor; auto.
      - repeat inv_bind. constructor; auto. repeat solve_incl.
      - (* reset *)
        simpl in Hnorm.
        cases; repeat inv_bind;
          try (constructor; auto; repeat solve_incl).
        inv Hwt; simpl in *. inv H6. apply Forall_singl in H3.
        apply Forall_singl in H. apply H in H0; eauto.
        simpl_Forall. constructor; auto. repeat solve_incl.
      - repeat inv_bind. constructor; auto. repeat solve_incl.
      - repeat inv_bind. constructor; auto. repeat solve_incl.
      - repeat inv_bind. constructor; auto. repeat solve_incl.
    Qed.

    Corollary normfby_blocks_wt : forall vars to_cut blocks blocks' st st' ,
        Forall (wt_type G1.(types)) (map (fun '(_, a) => a.(typ)) vars) ->
        Forall (wt_block G1 vars) blocks ->
        normfby_blocks to_cut blocks st = (blocks', st') ->
        Forall (wt_block G2 (vars++st_senv st')) blocks'.
    Proof.
      induction blocks; intros * Htypes Hwt Hfby;
        unfold normfby_blocks in *; repeat inv_bind; simpl; auto.
      inv Hwt.
      apply Forall_app; split.
      - eapply normfby_block_wt in H; eauto. simpl_Forall. repeat solve_incl.
      - assert (normfby_blocks to_cut blocks x1 = (concat x2, st')) as Hnorm.
        { unfold normfby_blocks. repeat inv_bind; eauto. }
        eapply IHblocks in Hnorm; eauto.
    Qed.

    (** wt_clock *)

    Definition st_clocks {pref} (st : fresh_st pref (Op.type * clock)) : list clock :=
      map (fun '(_, (_, cl)) => cl) (st_anns st).

    Fact fresh_ident_wt_clock : forall types pref hint vars ty cl id (st st' : fresh_st pref _),
        Forall (wt_clock types vars) (st_clocks st) ->
        wt_clock types vars cl ->
        fresh_ident hint (ty, cl) st = (id, st') ->
        Forall (wt_clock types vars) (st_clocks st').
    Proof.
      intros * Hclocks Hwt Hfresh.
      apply fresh_ident_anns in Hfresh.
      unfold st_clocks in *. setoid_rewrite Hfresh; simpl.
      constructor; auto.
    Qed.

    Fact init_var_for_clock_wt_clock : forall types vars ck x eqs' st st' ,
        wt_clock types (vars++st_senv st) ck ->
        Forall (wt_clock types (vars ++ st_senv st)) (st_clocks st) ->
        init_var_for_clock ck st = (x, eqs', st') ->
        Forall (wt_clock types (vars ++ st_senv st')) (st_clocks st').
    Proof.
      intros * Hwtc1 Hwtc2 Hfby.
      unfold init_var_for_clock in Hfby.
      destruct (fresh_ident _ _) eqn:Hfresh.
      inv Hfby.
      eapply fresh_ident_wt_clock in Hfresh; eauto. simpl_Forall. 1,2:repeat solve_incl.
    Qed.

    Fact fby_iteexp_wt_clock : forall types vars e0 e ty ck e' eqs' st st' ,
        wt_clock types (vars++st_senv st) ck ->
        Forall (wt_clock types (vars ++ st_senv st)) (st_clocks st) ->
        fby_iteexp e0 e (ty, ck) st = (e', eqs', st') ->
        Forall (wt_clock types (vars ++ st_senv st')) (st_clocks st').
    Proof.
      intros * Hwtc1 Hwtc2 Hfby.
      unfold fby_iteexp in Hfby; repeat inv_bind; auto.
      assert (st_follows st x1) as Hfollows1 by (eapply init_var_for_clock_st_follows in H; eauto).
      assert (st_follows x1 st') as Hfollows2 by eauto with fresh.
      eapply fresh_ident_wt_clock in H0; eauto. 2:repeat solve_incl.
      eapply init_var_for_clock_wt_clock in H; eauto.
      simpl_Forall; repeat solve_incl.
    Qed.

    Fact arrow_iteexp_wt_clock : forall types vars e0 e ty ck e' eqs' st st' ,
        wt_clock types (vars++st_senv st) ck ->
        Forall (wt_clock types (vars ++ st_senv st)) (st_clocks st) ->
        arrow_iteexp e0 e (ty, ck) st = (e', eqs', st') ->
        Forall (wt_clock types (vars ++ st_senv st')) (st_clocks st').
    Proof.
      intros * Hwtc1 Hwtc2 Hfby.
      unfold arrow_iteexp in Hfby. repeat inv_bind.
      eapply init_var_for_clock_wt_clock in H; eauto.
    Qed.

    Fact normfby_equation_wt_clock : forall vars to_cut eq eqs' st st' ,
        wt_equation G1 (vars++st_senv st) eq ->
        Forall (wt_clock G2.(types) (vars ++ st_senv st)) (st_clocks st) ->
        normfby_equation to_cut eq st = (eqs', st') ->
        Forall (wt_clock G2.(types) (vars ++ st_senv st')) (st_clocks st').
    Proof.
      intros * Hwt Hwtck Hfby.
      inv_normfby_equation Hfby to_cut eq; destruct x2 as (ty&ck).
      - (* fby (constant) *)
        destruct PS.mem; repeat inv_bind; auto.
        destruct Hwt as [Hwt _]. apply Forall_singl in Hwt.
        inv Hwt. apply Forall_singl in H7.
        eapply fresh_ident_wt_clock in H; eauto.
        1:simpl_Forall. 1,2:repeat solve_incl.
      - (* fby *)
        eapply fby_iteexp_wt_clock in H; eauto.
        destruct Hwt as [Hwt _]. apply Forall_singl in Hwt.
        inv Hwt. apply Forall_singl in H7; auto.
        solve_incl.
      - (* arrow *)
        destruct Hwt as [Hwt _]. apply Forall_singl in Hwt.
        inv Hwt. apply Forall_singl in H7; auto.
        eapply arrow_iteexp_wt_clock in H; eauto with norm.
    Qed.

    Fact normfby_block_wt_clock : forall vars to_cut d blocks' st st' ,
        wt_block G1 (vars++st_senv st) d ->
        Forall (wt_clock G2.(types) (vars ++ st_senv st)) (st_clocks st) ->
        normfby_block to_cut d st = (blocks', st') ->
        Forall (wt_clock G2.(types) (vars ++ st_senv st')) (st_clocks st').
    Proof.
      induction d using block_ind2; intros * Hwt Hwtck Hnorm;
        repeat inv_bind; auto.
      - (* equation *)
        inv Hwt; repeat inv_bind.
        eapply normfby_equation_wt_clock; eauto.
      - (* reset *)
        simpl in Hnorm.
        cases; repeat inv_bind; auto.
        inv Hwt. apply Forall_singl in H3.
        apply Forall_singl in H; eauto.
    Qed.

    Corollary normfby_blocks_wt_clock : forall vars to_cut blocks blocks' st st' ,
        Forall (wt_block G1 (vars++st_senv st)) blocks ->
        Forall (wt_clock G2.(types) (vars ++ st_senv st)) (st_clocks st) ->
        normfby_blocks to_cut blocks st = (blocks', st') ->
        Forall (wt_clock G2.(types) (vars ++ st_senv st')) (st_clocks st').
    Proof.
      induction blocks; intros * Hwt Hwtck Hfby;
        unfold normfby_blocks in *; repeat inv_bind; simpl; auto.
      inv Hwt.
      assert (H':=H). eapply normfby_block_wt_clock in H; eauto.
      assert (normfby_blocks to_cut blocks x1 = (concat x2, st')) as Hnorm.
      { unfold normfby_blocks. repeat inv_bind; eauto. }
      eapply IHblocks in Hnorm; eauto. simpl_Forall; repeat solve_incl; eauto with norm.
    Qed.

    (** wt_type *)

    Lemma fresh_ident_wt_type' : forall vars pref hint ty ck id (st st': fresh_st pref _),
        wt_type G2.(types) ty ->
        Forall (wt_type G2.(types)) (map (fun '(_, a) => a.(typ)) (vars++st_senv st)) ->
        fresh_ident hint (ty, ck) st = (id, st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, a) => a.(typ)) (vars++st_senv st')).
    Proof.
      unfold st_senv.
      intros * Hty Htypes Hfresh.
      apply Ker.fresh_ident_anns in Hfresh. rewrite Hfresh; simpl.
      rewrite <-Permutation.Permutation_middle; simpl; eauto.
    Qed.

    Fact init_var_for_clock_wt_type : forall vars ck x eqs' st st' ,
        Forall (wt_type G2.(types)) (map (fun '(_, a) => a.(typ)) (vars ++ st_senv st)) ->
        init_var_for_clock ck st = (x, eqs', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, a) => a.(typ)) (vars ++ st_senv st')).
    Proof.
      intros * Hwtc2 Hfby.
      unfold init_var_for_clock in Hfby.
      destruct (fresh_ident _ _) eqn:Hfresh.
      inv Hfby.
      eapply fresh_ident_wt_type' in Hfresh; eauto.
      eapply iface_incl_wt_type; eauto.
    Qed.

    Fact fby_iteexp_wt_type : forall vars e0 e ty ck e' eqs' st st' ,
        wt_type G2.(types) ty ->
        Forall (wt_type G2.(types)) (map (fun '(_, a) => a.(typ)) (vars ++ st_senv st)) ->
        fby_iteexp e0 e (ty, ck) st = (e', eqs', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, a) => a.(typ)) (vars ++ st_senv st')).
    Proof.
      intros * Hwt1 Hwt2 Hfby.
      unfold fby_iteexp in Hfby; repeat inv_bind; auto.
      assert (st_follows st x1) as Hfollows1 by (eapply init_var_for_clock_st_follows in H; eauto).
      assert (st_follows x1 st') as Hfollows2 by eauto with fresh.
      eapply fresh_ident_wt_type' in H0; eauto.
      eapply init_var_for_clock_wt_type in H; eauto.
    Qed.

    Fact arrow_iteexp_wt_type : forall vars e0 e ty ck e' eqs' st st' ,
        wt_type G2.(types) ty ->
        Forall (wt_type G2.(types)) (map (fun '(_, a) => a.(typ)) (vars ++ st_senv st)) ->
        arrow_iteexp e0 e (ty, ck) st = (e', eqs', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, a) => a.(typ)) (vars ++ st_senv st')).
    Proof.
      intros * Hwtc1 Hwtc2 Hfby.
      unfold arrow_iteexp in Hfby. repeat inv_bind.
      eapply init_var_for_clock_wt_type in H; eauto.
    Qed.

    Hypothesis HwtG2 : wt_global G2.

    Fact normfby_equation_wt_type : forall vars to_cut eq eqs' st st' ,
        wt_equation G1 (vars++st_senv st) eq ->
        Forall (wt_type G2.(types)) (map (fun '(_, a) => a.(typ)) (vars ++ st_senv st)) ->
        normfby_equation to_cut eq st = (eqs', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, a) => a.(typ)) (vars ++ st_senv st')).
    Proof.
      intros * Hwt Hwtck Hfby.
      inv_normfby_equation Hfby to_cut eq; destruct x2 as (ty&ck).
      - (* fby (constant) *)
        destruct PS.mem; repeat inv_bind; auto.
        destruct Hwt as [Hwt _]. apply Forall_singl in Hwt.
        inv Hwt. apply Forall_singl in H7.
        eapply fresh_ident_wt_type' in H; eauto. simpl in *.
        eapply Forall_singl, iface_incl_wt_exp in H4; eauto. eapply wt_exp_wt_type in H4; eauto.
        rewrite app_nil_r in H5. rewrite H5 in H4. apply Forall_singl in H4; eauto.
      - (* fby *)
        eapply fby_iteexp_wt_type in H; eauto.
        destruct Hwt as [Hwt _]. apply Forall_singl in Hwt.
        inv Hwt. apply Forall_singl in H7; auto. simpl in *.
        eapply Forall_singl, iface_incl_wt_exp in H4; eauto. eapply wt_exp_wt_type in H4; eauto.
        rewrite app_nil_r in H5. rewrite H5 in H4. apply Forall_singl in H4; eauto.
      - (* arrow *)
        destruct Hwt as [Hwt _]. apply Forall_singl in Hwt.
        inv Hwt. apply Forall_singl in H7; auto. simpl in *.
        eapply arrow_iteexp_wt_type in H; eauto.
        eapply Forall_singl, iface_incl_wt_exp in H4; eauto. eapply wt_exp_wt_type in H4; eauto.
        rewrite app_nil_r in H5. rewrite H5 in H4. apply Forall_singl in H4; eauto.
    Qed.

    Fact normfby_block_wt_type : forall vars to_cut d blocks' st st' ,
        wt_block G1 (vars++st_senv st) d ->
        Forall (wt_type G2.(types)) (map (fun '(_, a) => a.(typ)) (vars ++ st_senv st)) ->
        normfby_block to_cut d st = (blocks', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, a) => a.(typ)) (vars ++ st_senv st')).
    Proof.
      induction d using block_ind2; intros * Hwt Htypes Hnorm;
        repeat inv_bind; auto.
      - (* equation *)
        inv Hwt. repeat inv_bind.
        eapply normfby_equation_wt_type in H; eauto.
      - (* reset *)
        simpl in Hnorm. cases; repeat inv_bind; auto.
        inv Hwt. apply Forall_singl in H3.
        apply Forall_singl in H; eauto.
    Qed.

    Corollary normfby_blocks_wt_type : forall vars to_cut blocks blocks' st st' ,
        Forall (wt_block G1 (vars++st_senv st)) blocks ->
        Forall (wt_type G2.(types)) (map (fun '(_, a) => a.(typ)) (vars ++ st_senv st)) ->
        normfby_blocks to_cut blocks st = (blocks', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, a) => a.(typ)) (vars ++ st_senv st')).
    Proof.
      induction blocks; intros * Hwt Hwtck Hfby;
        unfold normfby_blocks in *; repeat inv_bind; simpl; auto.
      inv Hwt.
      assert (H':=H). eapply normfby_block_wt_type in H; eauto.
      assert (normfby_blocks to_cut blocks x1 = (concat x2, st')) as Hnorm.
      { unfold normfby_blocks. repeat inv_bind; eauto. }
      eapply IHblocks in Hnorm; eauto. simpl_Forall; repeat solve_incl; eauto with norm.
    Qed.

    (** Finally, typing of a node *)

    Local Hint Resolve iface_incl_wt_type : norm.

    Lemma normfby_node_wt : forall n,
        wt_node G1 n ->
        wt_node G2 (normfby_node n).
    Proof.
      intros * Hwc. inversion_clear Hwc as [??? Hclin Hclout Heq]; subst Γ.
      unfold normfby_node.
      pose proof (n_syn n) as Hsyn. inversion Hsyn as [??? _ Hsyn2 _].
      destruct Hiface as (Htypes&_).
      econstructor; simpl; eauto.
      1-3:unfold wt_clocks in *; simpl_Forall; eauto with ltyping.
      rewrite <-H1 in *; simpl in *. inv Heq. inv_scope; subst Γ'.
      do 2 econstructor; eauto.
      - unfold wt_clocks in *. setoid_rewrite senv_of_decls_app. apply Forall_app; split; simpl_Forall.
        + eapply wt_clock_incl; [|eauto with ltyping].
          intros. eapply HasType_incl; [|eauto]. setoid_rewrite senv_of_decls_app. solve_incl_app.
        + destruct (normfby_blocks _ _ _) as (blocks&st') eqn:Heqres.
          eapply normfby_blocks_wt_clock with (vars:=senv_of_ins (n_in n) ++ senv_of_decls (n_out n) ++ senv_of_decls locs) in Heqres; eauto.
          * unfold st_clocks in *. simpl_In. simpl_Forall.
            simpl_app. erewrite map_map, map_ext with (l:=st_anns _); eauto. intros; destruct_conjs; auto.
          * unfold st_clocks, st_senv. rewrite init_st_anns, app_nil_r. simpl_app; auto.
          * unfold st_clocks. rewrite init_st_anns; simpl; constructor.
      - destruct (normfby_blocks _ _ _) as (blocks'&st') eqn:Heqres; simpl.
        eapply normfby_blocks_wt_type with (vars:=senv_of_ins (n_in n) ++ senv_of_decls (n_out n) ++ senv_of_decls locs) in Heqres; eauto.
        + rewrite 2 map_app, 2 Forall_app in Heqres. destruct Heqres as ((?&?)&?).
          unfold st_senv, idfst in *. simpl_app.
          apply Forall_app; auto; split; simpl_Forall; eauto with ltyping.
        + unfold st_senv. rewrite init_st_anns, app_nil_r. simpl_app; auto.
        + unfold st_senv. rewrite init_st_anns, app_nil_r.
          rewrite app_assoc, map_app, Forall_app; split; simpl_Forall; simpl_In; simpl_Forall; eauto with ltyping.
      - destruct (normfby_blocks _ _ _) as (blocks'&st') eqn:Heqres; simpl.
        eapply normfby_blocks_wt in Heqres; eauto.
        + simpl_Forall. simpl_app. erewrite map_map, map_ext with (l:=st_anns _); eauto. intros; destruct_conjs; auto.
        + rewrite map_app. apply Forall_app; split; simpl_Forall; simpl_In; simpl_Forall; eauto with ltyping.
    Qed.

  End normfby_node_wt.

  Lemma normfby_global_wt : forall G,
      wt_global G ->
      wt_global (normfby_global G).
  Proof.
    intros [] (?&Hwt). unfold CommonTyping.wt_program in Hwt; simpl.
    induction nodes0; simpl; inv Hwt; split; simpl; auto. constructor.
    destruct H2. constructor; [constructor|]; simpl in *.
    - eapply normfby_node_wt; eauto; simpl; auto.
      + eapply iface_eq_iface_incl, normfby_global_eq.
      + constructor; auto.
    - eapply normfby_nodes_names; eauto.
    - eapply IHnodes0; eauto.
  Qed.

End NFTYPING.

Module NFTypingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (NF  : NORMFBY Ids Op OpAux Cks Senv Syn)
       <: NFTYPING Ids Op OpAux Cks Senv Syn Typ NF.
  Include NFTYPING Ids Op OpAux Cks Senv Syn Typ NF.
End NFTypingFun.
