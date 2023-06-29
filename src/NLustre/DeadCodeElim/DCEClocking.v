From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Recdef.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Environment.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import NLustre.DeadCodeElim.DCE.

Module Type DCECLOCKING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Import CEF   : CEISFREE        Ids Op OpAux Cks CESyn)
       (Import CEClo : CECLOCKING      Ids Op OpAux Cks CESyn)
       (Import Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Import Free  : ISFREE          Ids Op OpAux Cks CESyn Syn CEF)
       (Import Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (Import Def   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Import Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Import Clo   : NLCLOCKING      Ids Op OpAux Cks CESyn Syn Ord Mem Def CEClo)
       (Import DCE   : DCE             Ids Op OpAux Cks CESyn CEF Syn Free Mem Def).

  Lemma wc_clock_free' : forall (vars : list (ident * clock)) ck x,
    wc_clock vars ck ->
    Is_free_in_clock x ck ->
    InMembers x vars.
  Proof.
    induction ck; intros * Hwc Hfree;
      inv Hwc; inv Hfree; eauto.
    solve_In.
  Qed.

  Lemma wc_clock_free : forall (vars : list (ident * (clock * bool))) ck x,
    wc_clock (idfst vars) ck ->
    Is_free_in_clock x ck ->
    InMembers x vars.
  Proof.
    induction ck; intros * Hwc Hfree;
      inv Hwc; inv Hfree; eauto.
    solve_In.
  Qed.

  Lemma wc_exp_free : forall vars e ck x,
      wc_exp vars e ck ->
      Is_free_in_exp x e ->
      InMembers (var_last_ident x) vars.
  Proof.
    induction e; intros * Hwc Hfree;
      inv Hwc; inv Hfree; eauto using In_InMembers.
    destruct H1; eauto.
  Qed.

  Lemma wc_cexp_free : forall vars e ck x,
      wc_cexp vars e ck ->
      Is_free_in_cexp x e ->
      InMembers (var_last_ident x) vars.
  Proof.
    induction e using cexp_ind2'; intros * Hwc Hfree;
      inv Hwc; inv Hfree; eauto using wc_exp_free, In_InMembers.
    - eapply Forall2_ignore1 in H6.
      simpl_Exists; simpl_Forall; eauto.
    - simpl_Exists; simpl_Forall; eauto.
      subst; simpl in *; eauto.
  Qed.

  Lemma wc_rhs_free : forall vars e x ck,
      wc_rhs vars e ck ->
      Is_free_in_rhs x e ->
      InMembers (var_last_ident x) vars.
  Proof.
    intros * Wt Free; inv Wt; inv Free; eauto using wc_cexp_free.
    simpl_Exists; simpl_Forall; eauto using wc_exp_free.
  Qed.

  Lemma wc_equation_def_free : forall G vars eq x,
      wc_env (idfst vars) ->
      wc_equation G vars eq ->
      Is_defined_in_eq x eq \/ Is_free_in_eq x eq ->
      InMembers (var_last_ident x) vars.
  Proof.
    induction eq; intros * Hwenv Hwc Hdeff; inv Hwc.
    - destruct Hdeff as [Hdef|Hfree].
      + inv Hdef; eauto using In_InMembers.
      + inv Hfree. inv H2; eauto using wc_rhs_free.
        eapply wc_clock_free; eauto. eapply wc_env_var; eauto. solve_In.
    - destruct Hdeff as [Hdef|Hfree].
      + inv Hdef; eauto using In_InMembers.
      + inv Hfree. destruct H2 as [Hex|Hex].
        * eapply wc_env_var, wc_clock_free in Hwenv; eauto. solve_In.
        * simpl_Exists; simpl_Forall.
          destruct Hex; subst; eauto. solve_In.
          eapply wc_env_var, wc_clock_free in Hwenv; eauto. solve_In.
    - destruct Hdeff as [Hdef|Hfree].
      + inv Hdef. eapply Forall2_ignore1, Forall_forall in H6; eauto.
        destruct H6 as ((?&?&?)&?&?&?&?&?&?); simpl; eauto using In_InMembers.
      + inv Hfree. destruct H1 as [Hfree|Hex].
        * inv Hfree; eauto.
          -- simpl_Exists.
             eapply Forall2_ignore1, Forall_forall in H5 as ((?&?&?)&?&?&?&?&?); eauto using wc_exp_free.
          -- pose proof (node_in_not_nil n) as Hnnil.
             inv H5; try congruence. clear H0 H2.
             destruct x as (?&?&?). destruct H1 as (?&?&Hwc&Hinst).
             apply wc_clock_exp in Hwc; eauto.
             apply instck_parent in Hinst as [|Hpar]; subst; eauto using wc_clock_free.
             eapply wc_clock_parent in Hpar; eauto using wc_clock_free.
        * simpl_Exists; simpl_Forall.
          destruct Hex; subst; eauto using In_InMembers. destruct_conjs; subst.
          eapply wc_clock_free; eauto. eapply wc_env_var; eauto. solve_In.
    - destruct Hdeff as [Hdef|Hfree].
      + inv Hdef; eauto using In_InMembers.
      + inv Hfree. destruct H1 as [Hfree|Hex].
        * inv Hfree; eauto using wc_exp_free.
          eapply wc_clock_exp in H5; eauto using wc_clock_free.
        * simpl_Exists; simpl_Forall.
          destruct Hex; subst; eauto using In_InMembers. destruct_conjs; subst.
          eapply wc_clock_free; eauto. eapply wc_env_var; eauto. solve_In.
  Qed.

  Section wc_node.
    Variable G1 G2 : global.
    Hypothesis HG : global_iface_eq G1 G2.
    Hypothesis HwG2 : wc_global G2.

    Lemma wc_clock_restrict : forall vars vars' ck,
        (forall x ty, In (x, ty) vars -> Is_free_in_clock x ck -> In (x, ty) vars') ->
        wc_clock vars ck ->
        wc_clock vars' ck.
    Proof.
      induction ck; intros * Hincl Hwc; inv Hwc; constructor; auto with nlfree.
    Qed.

    Lemma wc_exp_restrict : forall vars vars' e ck,
        (forall x ty islast, In (x, (ty, islast)) vars -> Is_free_in_exp (Var x) e -> In (x, (ty, islast)) vars') ->
        (forall x ty, In (x, (ty, true)) vars -> Is_free_in_exp (Last x) e -> In (x, (ty, true)) vars') ->
        wc_exp vars e ck ->
        wc_exp vars' e ck.
    Proof.
      induction e; intros * Vars Lasts Hwc; inv Hwc; econstructor; eauto 8 with nlclocking nlfree.
    Qed.
    Local Hint Resolve wc_exp_restrict : nlclocking.

    Lemma wc_cexp_restrict : forall vars vars' e ck,
        (forall x ty islast, In (x, (ty, islast)) vars -> Is_free_in_cexp (Var x) e -> In (x, (ty, islast)) vars') ->
        (forall x ty, In (x, (ty, true)) vars -> Is_free_in_cexp (Last x) e -> In (x, (ty, true)) vars') ->
        wc_cexp vars e ck ->
        wc_cexp vars' e ck.
    Proof with eauto 7 with nlclocking nlfree.
      induction e using cexp_ind2'; intros * Vars Lasts Hwc; inv Hwc...
      - econstructor...
        + simpl_Forall.
          eapply H; eauto; intros; [eapply Vars|eapply Lasts]; eauto; constructor; solve_Exists.
      - econstructor...
        intros ? Hin. eapply Forall_forall in H; eauto; simpl in *.
        eapply H; eauto; intros; [eapply Vars|eapply Lasts]; eauto; eapply FreeEcase_branches; solve_Exists.
    Qed.
    Local Hint Resolve wc_cexp_restrict : nlclocking.

    Lemma wc_rhs_restrict : forall vars vars' e ck,
        (forall x ty islast, In (x, (ty, islast)) vars -> Is_free_in_rhs (Var x) e -> In (x, (ty, islast)) vars') ->
        (forall x ty, In (x, (ty, true)) vars -> Is_free_in_rhs (Last x) e -> In (x, (ty, true)) vars') ->
        wc_rhs vars e ck ->
        wc_rhs vars' e ck.
    Proof with eauto 6 with nlclocking nlfree.
      intros * Vars Lasts Wt; inv Wt; econstructor; simpl_Forall...
      - eapply wc_exp_restrict in H; eauto;
          intros; [eapply Vars|eapply Lasts]; eauto; constructor; solve_Exists.
    Qed.

    Lemma wc_equation_restrict : forall vars vars' eq,
        (forall x ty islast, In (x, (ty, islast)) vars -> Is_defined_in_eq (Var x) eq \/ Is_free_in_eq (Var x) eq -> In (x, (ty, islast)) vars') ->
        (forall x ty, In (x, (ty, true)) vars -> Is_defined_in_eq (Last x) eq \/ Is_free_in_eq (Last x) eq -> In (x, (ty, true)) vars') ->
        wc_equation G1 vars eq ->
        wc_equation G2 vars' eq.
    Proof with eauto with nlclocking nlfree nldef.
      intros * Vars Lasts Hwc. inv Hwc.
      - econstructor...
        + eapply wc_rhs_restrict with (vars:=vars)...
      - econstructor...
        simpl_Forall. esplit. eapply Vars; eauto.
        right. constructor. right. solve_Exists.
      - destruct HG as (?&?&Hf). specialize (Hf f). rewrite H in Hf; inv Hf. destruct H7 as (Hname&Hin&Hout).
        econstructor...
        + rewrite <-Hin. simpl_Forall. repeat esplit; eauto.
          eapply wc_exp_restrict with (vars:=vars); eauto;
            intros; [eapply Vars|eapply Lasts]; eauto; right; constructor; left; econstructor; solve_Exists.
        + rewrite <-Hout. simpl_Forall. repeat esplit...
        + simpl_Forall. esplit. eapply Vars; eauto.
          right. constructor. right. solve_Exists.
      - econstructor...
        + eapply wc_exp_restrict with (vars:=vars); eauto 8 with nlfree.
        + simpl_Forall. esplit. eapply Vars; eauto.
          right. constructor. right. solve_Exists.
    Qed.

    Lemma wc_equations_has_def : forall vars eqs,
        Forall (wc_equation G1 vars) eqs ->
        Forall (fun eq : equation => exists x0, Is_defined_in_eq x0 eq) eqs.
    Proof.
      intros * Hwc.
      simpl_Forall.
      inv Hwc; eauto with nldef.
      esplit. eapply Is_defined_in_EqApp with (d:=xH).
      pose proof (n_outgt0 n) as Hgt.
      apply Forall2_length in H2. congruence.
    Qed.

    Lemma wc_equation_free_in_clock : forall vars eq x y ck islast,
        NoDupMembers vars ->
        wc_equation G2 vars eq ->
        Is_defined_in_eq x eq ->
        In (var_last_ident x, (ck, islast)) vars ->
        Is_free_in_clock y ck ->
        Is_defined_in_eq (Var y) eq \/ Is_free_in_eq (Var y) eq.
    Proof with eauto with nlfree nldef.
      intros * Hnd Hwc Hdef Hxck Hfree; inv Hwc; inv Hdef.
      - (* def *)
        eapply NoDupMembers_det in Hxck; eauto. inv Hxck...
      - (* last *)
        eapply NoDupMembers_det in Hxck; eauto. inv Hxck...
      - (* app *)
        assert (Hf2:=H1). eapply Forall2_ignore1, Forall_forall in H1 as ((?&?&?)&Hin&Hsub&?&?&Hvars&Hinst); eauto.
        eapply NoDupMembers_det in Hxck; eauto. inv Hxck.
        eapply instck_inv in Hinst as [|(?&Hsub'&Hfree')]...
        assert (wc_env (idsnd (n_in n ++ n_out n))) as Hwenv.
        { eapply wc_find_node in H as (?&?&_&?&?&?); eauto. }
        eapply wc_env_var in Hwenv; [|eapply in_map_iff; do 2 esplit; eauto with datatypes]. simpl in *.
        eapply wc_clock_free', InMembers_idsnd, InMembers_In in Hfree' as ((?&?)&Hin'); [|eauto].
        apply in_app_iff in Hin' as [Hin'|Hin'].
        + eapply Forall2_ignore2, Forall_forall in H0 as (?&?&Hv); eauto; simpl in *.
          destruct Hv as (Hv&_). rewrite Hsub' in Hv. inv Hv.
          right. constructor. do 2 left. solve_Exists...
        + eapply Forall2_ignore2, Forall_forall in Hf2 as (?&Hin1&Hv); eauto; simpl in *.
          destruct Hv as (Hsub1&_). rewrite Hsub1 in Hsub'; inv Hsub'...
      - (* fby *)
        eapply NoDupMembers_det in Hxck; eauto. inv Hxck...
    Qed.

    Import Permutation.

    Fact In_nolast : forall (ins outs : list (ident * (type * clock))) vars x ck islast,
        In (x, (ck, islast)) (map (fun '(x, (_, ck)) => (x, (ck, false))) (ins ++ outs)
                                ++ map (fun '(x, (_, ck, islast)) => (x, (ck, islast))) vars)
        <-> exists ty, In (x, (ty, ck, islast))
                  (map (fun '(x0, (ty0, ck0)) => (x0, (ty0, ck0, false))) ins
                     ++ vars ++ map (fun '(x0, (ty0, ck0)) => (x0, (ty0, ck0, false))) outs).
    Proof.
      intros. simpl_app. repeat setoid_rewrite in_app_iff.
      split; [intros [|[|]]; simpl_In; esplit|intros (?&[|[|]])].
      1,4:left; solve_In.
      1,3:right; right; solve_In.
      1,2:right; left; solve_In; eauto.
    Qed.

    Lemma dce_node_wc : forall n,
        wc_node G1 n ->
        wc_node G2 (dce_node n).
    Proof.
      intros ? (Hwc1&Hwc2&Hwc3&Hwc4).
      remember (fst (dce_eqs (PSP.of_list (map fst (n_out n))) (n_vars n) (n_eqs n))) as vars'.
      remember (snd (dce_eqs (PSP.of_list (map fst (n_out n))) (n_vars n) (n_eqs n))) as eqs'.

      assert (wc_env
                (idfst
                   (map (fun '(x2, (_, ck)) => (x2, (ck, false))) (n_in n ++ n_out n) ++
                      map (fun '(x2, (_, ck, islast)) => (x2, (ck, islast))) (n_vars n)))) as Wenv'.
      { clear - Hwc3. simpl_app. rewrite map_map in Hwc3.
        erewrite 3 map_map, Permutation_app_comm with (l:=map _ (n_out n)),
            map_ext with (l:=n_in _), map_ext with (l:=n_out _), map_ext with (l:=n_vars _); eauto.
        1-3:intros; destruct_conjs; auto. }

      eapply wc_equations_has_def in Hwc4 as Hdef.
      unshelve eassert (Hdef':=dce_eqs_stable (map _ (n_in n)) (n_vars n) (map _ (n_out n)) _ _ _ _ _ _ Hdef _ eq_refl).
      1,2:exact (fun '(x, (ty, ck)) => (x, (ty, ck, false))).
      5:replace (map fst (map (fun '(x1, (ty0, ck0)) => (x1, (ty0, ck0, false))) (n_out n)))
        with (map fst (n_out n)) in Hdef'
          by (symmetry; erewrite map_map, map_ext; eauto; intros; destruct_conjs; auto).
      1:{ intros * In1 In2. simpl_In.
          pose proof (n_nodup n) as Nd.
          eapply NoDup_app_r, NoDup_app_In in Nd. eapply Nd. 1,2:solve_In. }
      1:{ intros.
          erewrite Is_defined_in_vars_defined, n_defd, fst_InMembers, map_app, map_map, map_ext with (l:=n_out _);
            [reflexivity|].
          intros; destruct_conjs; auto. }
      1:{ intros * In. rewrite Is_defined_in_lasts_defined, n_lastd1 in In.
          solve_In. }
      1:{ intros. simpl_Exists. simpl_Forall.
          eapply wc_equation_def_free in Hwc4; eauto.
          simpl_app. rewrite 2 InMembers_app in Hwc4. rewrite 2 InMembers_app.
          destruct Hwc4 as [|[|]]; [left|right; right|right; left]; solve_In. }

        assert (Forall
                  (wc_equation G2
                     (map (fun '(x, (_, ck)) => (x, (ck, false))) (n_in (dce_node n) ++ n_out (dce_node n)) ++
                        map (fun '(x, (_, ck, islast)) => (x, (ck, islast))) (n_vars (dce_node n)))) (n_eqs (dce_node n))) as Hwc'.
      { simpl_Forall. simpl_In. simpl_Forall.
        eapply wc_equation_restrict. 3:eauto.
        1,2:intros * In Def; apply In_nolast in In as (?&In).
        1,2:apply In_nolast; esplit; eapply incl_NoDup_In; eauto.
        3:eapply Hdef' with (x:=Var x1); eauto; solve_Exists; solve_In.
        5:eapply Hdef' with (x:=Last x1); eauto; solve_Exists; solve_In.
        1,3:apply incl_appr', incl_appl', incl_filter', incl_refl.
        1,2:erewrite fst_NoDupMembers, 2 map_app, 2 map_map,
            map_ext with (l:=n_in _), map_ext with (l:=n_out _); try apply n_nodup.
        all:intros; destruct_conjs; auto.
      }
      repeat (split; auto).
      - (* env *)
        rewrite (Permutation_app_comm (idfst _)), app_assoc, idsnd_app.
        apply Forall_app; split.
        + eapply Forall_impl; [|eauto]; intros (?&?) ?.
          eapply Cks.wc_clock_incl; [|eauto]. solve_incl_app.
        + simpl_Forall. simpl_In.
          eapply wc_clock_restrict.
          2:{ unfold wc_env in Hwc3. rewrite 2 idsnd_app, 2 Forall_app in Hwc3.
              destruct Hwc3 as (_&Hwc3&_). eapply Forall_forall in Hwc3. 2:solve_In. eauto. }
          intros * In1 Inck.
          remember (filter _ (n_eqs n)) as eqs'. assert (Is_defined_in (Var i) eqs') as Def.
          { subst. apply Is_defined_in_vars_defined. erewrite dce_vars_defined. 4:reflexivity.
            - apply in_or_app, or_introl. solve_In.
            - eapply NoDup_app_r, n_nodup.
            - apply n_defd. }
          eapply Exists_exists in Def as (?&In&Def). simpl_Forall.
          eapply wc_equation_free_in_clock in Inck; eauto.
          eapply incl_NoDup_In. 4:eauto.
          * clear - n.
            simpl_app. apply incl_appr', incl_app; [apply incl_appr| apply incl_appl];
              intros ??; solve_In.
          * rewrite fst_NoDupMembers, 2 map_app, 3 map_fst_idsnd, map_fst_idfst.
            apply n_nodup.
          * clear - Hdef' In Inck. simpl_app.
            specialize (Hdef' (Var x)).
            rewrite 2 InMembers_app in Hdef'. rewrite 2 InMembers_app.
            edestruct Hdef' as [Hin|[Hin|Hin]]; [solve_Exists|left|right;right|right;left];
              clear - Hin; solve_In.
          * rewrite fst_NoDupMembers. simpl_app.
            erewrite 3 map_map, map_ext with (l:=n_in _), map_ext with (l:=n_out _), map_ext with (l:=filter _ (n_vars _)),
                    Permutation_app_comm with (l:=map _ (n_out _)).
            eapply dce_NoDupMembers_filter, n_nodup.
            1-3:intros; destruct_conjs; auto.
          * simpl. rewrite in_app_iff. right. solve_In.
    Qed.

  End wc_node.

  Theorem dce_wc : forall G,
    wc_global G ->
    wc_global (dce_global G).
  Proof.
    intros.
    unfold wc_global in *; simpl.
    induction H; simpl; constructor; auto.
    eapply dce_node_wc in H; eauto.
    apply dce_global_iface_eq.
  Qed.

End DCECLOCKING.

Module DCEClockingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CESyn : CESYNTAX        Ids Op OpAux Cks)
       (CEF   : CEISFREE        Ids Op OpAux Cks CESyn)
       (CEClo : CECLOCKING        Ids Op OpAux Cks CESyn)
       (Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Free  : ISFREE          Ids Op OpAux Cks CESyn Syn CEF)
       (Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (Def   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Clo   : NLCLOCKING        Ids Op OpAux Cks CESyn Syn Ord Mem Def CEClo)
       (DCE   : DCE             Ids Op OpAux Cks CESyn CEF Syn Free Mem Def)
<: DCECLOCKING Ids Op OpAux Cks CESyn CEF CEClo Syn Free Mem Def Ord Clo DCE.
  Include DCECLOCKING Ids Op OpAux Cks CESyn CEF CEClo Syn Free Mem Def Ord Clo DCE.
End DCEClockingFun.
