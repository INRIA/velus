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
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLTyping.
From Velus Require Import NLustre.DeadCodeElim.DCE.

Module Type DCETYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Import CEF   : CEISFREE        Ids Op OpAux Cks CESyn)
       (Import CETyp : CETYPING        Ids Op OpAux Cks CESyn)
       (Import Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Import Free  : ISFREE          Ids Op OpAux Cks CESyn Syn CEF)
       (Import Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (Import Def   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Import Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Import Typ   : NLTYPING        Ids Op OpAux Cks CESyn Syn Ord CETyp)
       (Import DCE   : DCE             Ids Op OpAux Cks CESyn CEF Syn Free Mem Def).

  Lemma wt_clock_free : forall types vars ck x,
    wt_clock types vars ck ->
    Is_free_in_clock x ck ->
    InMembers x vars.
  Proof.
    induction ck; intros * Hwt Hfree;
      inv Hwt; inv Hfree; eauto using In_InMembers.
  Qed.

  Lemma wt_exp_free : forall types vars e x,
      wt_exp types vars e ->
      Is_free_in_exp x e ->
      InMembers (var_last_ident x) vars.
  Proof.
    induction e; intros * Hwt Free; inv Hwt; inv Free; eauto using In_InMembers.
    take (_ \/ _) and destruct it; auto.
  Qed.

  Lemma wt_cexp_free : forall types vars e x,
      wt_cexp types vars e ->
      Is_free_in_cexp x e ->
      InMembers (var_last_ident x) vars.
  Proof.
    induction e using cexp_ind2'; intros * Hwt Hfree; inv Hwt; inv Hfree;
      eauto using wt_exp_free, In_InMembers.
    all:simpl_Exists; simpl_Forall; subst; eauto.
  Qed.

  Lemma wt_rhs_free : forall types externs vars e x,
      wt_rhs types externs vars e ->
      Is_free_in_rhs x e ->
      InMembers (var_last_ident x) vars.
  Proof.
    intros * Wt Free; inv Wt; inv Free; eauto using wt_cexp_free.
    all:simpl_Exists; simpl_Forall; eauto using wt_exp_free.
  Qed.

  Lemma wt_equation_def_free: forall G vars eq x,
      wt_equation G vars eq ->
      Is_defined_in_eq x eq \/ Is_free_in_eq x eq ->
      InMembers (var_last_ident x) vars.
  Proof.
    induction eq; intros * Hwt Hdeff; inv Hwt.
    - destruct Hdeff as [Hdef|Hfree].
      + inv Hdef; eauto using In_InMembers.
      + inv Hfree. inv H1; eauto using wt_clock_free, wt_rhs_free.
    - destruct Hdeff as [Hdef|Hfree].
      + inv Hdef; eauto using In_InMembers.
      + inv Hfree. destruct H1 as [Hex|Hex]; eauto using wt_clock_free.
        simpl_Exists; simpl_Forall.
        destruct Hex; subst; eauto using wt_clock_free. solve_In.
    - destruct Hdeff as [Hdef|Hfree].
      + inv Hdef. eapply Forall2_ignore2, Forall_forall in H5; eauto.
        destruct H5 as ((?&?&?)&?&?); simpl; eauto using In_InMembers.
      + inv Hfree. destruct H1 as [Hfree|Hex].
        * inv Hfree; eauto using wt_clock_free.
          simpl_Exists; simpl_Forall; eauto using wt_exp_free.
        * simpl_Exists; simpl_Forall.
          destruct Hex; destruct_conjs; subst; eauto using wt_clock_free. solve_In.
    - destruct Hdeff as [Hdef|Hfree].
      + inv Hdef; eauto using In_InMembers.
      + inv Hfree. destruct H1 as [Hfree|Hex].
        * inv Hfree; eauto using wt_clock_free, wt_exp_free.
        * simpl_Exists; simpl_Forall.
          destruct Hex; destruct_conjs; subst; eauto using wt_clock_free. solve_In.
  Qed.

  Section wt_node.
    Variable G1 G2 : global.
    Hypothesis HG : global_iface_eq G1 G2.

    Lemma wt_clock_restrict : forall vars vars' ck,
        (forall x ty, In (x, ty) vars -> Is_free_in_clock x ck -> In (x, ty) vars') ->
        wt_clock G1.(types) vars ck ->
        wt_clock G2.(types) vars' ck.
    Proof.
      induction ck; intros * Hincl Hwt; inv Hwt; econstructor; eauto with nlfree.
      destruct HG. congruence.
    Qed.

    Lemma wt_exp_restrict : forall vars vars' e,
        (forall x ty islast, In (x, (ty, islast)) vars -> Is_free_in_exp (Var x) e -> In (x, (ty, islast)) vars') ->
        (forall x ty, In (x, (ty, true)) vars -> Is_free_in_exp (Last x) e -> In (x, (ty, true)) vars') ->
        wt_exp G1.(types) vars e ->
        wt_exp G2.(types) vars' e.
    Proof with eauto 6 with nltyping nlfree.
      induction e; intros * Vars Lasts Hwt; inv Hwt...
      - constructor... destruct HG; congruence.
      - econstructor... destruct HG; congruence.
      - econstructor...
      - econstructor...
        + eapply IHe1...
        + eapply IHe2...
    Qed.
    Local Hint Resolve wt_clock_restrict wt_exp_restrict : nltyping.

    Lemma wt_cexp_restrict : forall vars vars' e,
        (forall x ty islast, In (x, (ty, islast)) vars -> Is_free_in_cexp (Var x) e -> In (x, (ty, islast)) vars') ->
        (forall x ty, In (x, (ty, true)) vars -> Is_free_in_cexp (Last x) e -> In (x, (ty, true)) vars') ->
        wt_cexp G1.(types) vars e ->
        wt_cexp G2.(types) vars' e.
    Proof with eauto 6 with nltyping nlfree.
      induction e using cexp_ind2'; intros * Vars Lasts Hwt; inv Hwt...
      - econstructor...
        + destruct HG; congruence.
        + rewrite Forall_forall in *; intros.
          eapply H; eauto; intros; [eapply Vars|eapply Lasts]; eauto; constructor; solve_Exists.
      - econstructor...
        + destruct HG; congruence.
        + intros ? Hin. simpl_Forall.
          eapply H; eauto; intros; [eapply Vars|eapply Lasts]; eauto; eapply FreeEcase_branches; solve_Exists.
      - econstructor...
    Qed.
    Local Hint Resolve wt_cexp_restrict : nltyping.

    Lemma wt_rhs_restrict : forall vars vars' e,
        (forall x ty islast, In (x, (ty, islast)) vars -> Is_free_in_rhs (Var x) e -> In (x, (ty, islast)) vars') ->
        (forall x ty, In (x, (ty, true)) vars -> Is_free_in_rhs (Last x) e -> In (x, (ty, true)) vars') ->
        wt_rhs G1.(types) G1.(externs) vars e ->
        wt_rhs G2.(types) G2.(externs) vars' e.
    Proof with eauto 6 with nltyping nlfree.
      intros * Vars Lasts Wt; inv Wt; econstructor; simpl_Forall...
      - eapply wt_exp_restrict; [| |eauto];
          intros; [eapply Vars|eapply Lasts]; eauto; constructor; solve_Exists.
      - destruct HG as (?&?&?). congruence.
    Qed.

    Lemma wt_equation_restrict : forall vars vars' eq,
        (forall x ty islast, In (x, (ty, islast)) vars -> Is_defined_in_eq (Var x) eq \/ Is_free_in_eq (Var x) eq -> In (x, (ty, islast)) vars') ->
        (forall x ty, In (x, (ty, true)) vars -> Is_defined_in_eq (Last x) eq \/ Is_free_in_eq (Last x) eq -> In (x, (ty, true)) vars') ->
        wt_equation G1 vars eq ->
        wt_equation G2 vars' eq.
    Proof with eauto 6 with nltyping nlfree nldef.
      intros * Vars Lasts Hwt. destruct HG as (Htys&Hexts&Hf). inv Hwt.
      - econstructor...
        + eapply wt_clock_restrict with (vars:=vars)...
          intros. destruct_conjs...
        + eapply wt_rhs_restrict with (vars:=vars)...
      - econstructor...
        + eapply wt_clock_restrict with (vars:=vars)...
          intros. destruct_conjs...
        + congruence.
        + simpl_Forall. repeat split; try congruence.
          * simpl_In. eapply Vars in Hin; [solve_In|]. right. constructor. right. solve_Exists.
          * eapply wt_clock_restrict; [|eauto].
            intros. destruct_conjs. eapply Vars... right. constructor. right. solve_Exists.
      - specialize (Hf f). rewrite H in Hf; inv Hf. destruct H8 as (Hname&Hin&Hout).
        econstructor...
        + rewrite <-Hout. eapply Forall2_impl_In; [|eauto].
          intros ? (?&?&?) Hin1 Hin2 ?; simpl in *...
        + rewrite <-Hin. eapply Forall2_impl_In; [|eauto].
          intros ? (?&?&?) Hin1 Hin2 ?; simpl in *...
        + eapply wt_clock_restrict with (vars:=vars)...
          intros. destruct_conjs...
        + rewrite Forall_forall in *; intros.
          eapply wt_exp_restrict with (vars:=vars); eauto; intros;
            [eapply Vars|eapply Lasts]; eauto;
            right; constructor; left; constructor; solve_Exists.
        + simpl_Forall.
          repeat split; try congruence.
          * simpl_In. eapply Vars in Hin0; [solve_In|]. right. constructor. right. solve_Exists.
          * eapply wt_clock_restrict; [|eauto].
            intros. destruct_conjs. eapply Vars... right. constructor. right. solve_Exists.
        + simpl_Forall. simpl_In.
          eapply wt_clock_restrict with (vars:=vars); eauto.
          intros; destruct_conjs.
          eapply Vars; eauto. right; constructor; right. solve_Exists.
      - destruct HG. econstructor...
        + eapply wt_clock_restrict with (vars:=vars)...
          intros. destruct_conjs...
        + congruence.
        + eapply wt_exp_restrict with (vars:=vars); eauto 8 with nlfree.
        + simpl_Forall.
          repeat split; try congruence.
          * simpl_In. eapply Vars in Hin; [solve_In|]. right. constructor. right. solve_Exists.
          * eapply wt_clock_restrict; [|eauto].
            intros. destruct_conjs. eapply Vars... right. constructor. right. solve_Exists.
    Qed.

    Lemma wt_equations_has_def : forall vars eqs,
        Forall (wt_equation G1 vars) eqs ->
        Forall (fun eq : equation => exists x, Is_defined_in_eq x eq) eqs.
    Proof.
      intros * Hwt.
      simpl_Forall. inv Hwt; eauto with nldef.
      esplit. eapply Is_defined_in_EqApp with (d:=xH).
      pose proof (n_outgt0 n) as Hgt.
      apply Forall2_length in H1. congruence.
    Qed.

    Fact In_nolast : forall (ins outs : list (ident * (type * clock))) vars x ty islast,
        In (x, (ty, islast)) (map (fun '(x, (ty, _)) => (x, (ty, false))) (ins ++ outs)
                                ++ map (fun '(x, (ty, _, islast)) => (x, (ty, islast))) vars)
        <-> exists ck, In (x, (ty, ck, islast))
                  (map (fun '(x0, (ty0, ck0)) => (x0, (ty0, ck0, false))) ins
                     ++ vars ++ map (fun '(x0, (ty0, ck0)) => (x0, (ty0, ck0, false))) outs).
    Proof.
      intros. simpl_app. repeat setoid_rewrite in_app_iff.
      split; [intros [|[|]]; simpl_In; esplit|intros (?&[|[|]])].
      1,4:left; solve_In.
      1,3:right; right; solve_In.
      1,2:right; left; solve_In; eauto.
    Qed.

    Lemma dce_node_wt : forall n,
        wt_node G1 n ->
        wt_node G2 (dce_node n).
    Proof.
      intros ? (Hwt1&Hwt2).
      constructor; simpl.
      - eapply wt_equations_has_def in Hwt1 as Hdef.
        unshelve eassert (Hdef':=dce_eqs_stable (map _ (n_in n)) (n_vars n) (map _ (n_out n)) _ _ _ _ _ _ Hdef _ eq_refl).
        1,2:exact (fun '(x, (ty, ck)) => (x, (ty, ck, false))).
        + intros * In1 In2. simpl_In.
          pose proof (n_nodup n) as Nd.
          eapply NoDup_app_r, NoDup_app_In in Nd. eapply Nd. 1,2:solve_In.
        + intros.
          erewrite Is_defined_in_vars_defined, n_defd, fst_InMembers, map_app, map_map, map_ext with (l:=n_out _);
            [reflexivity|].
          intros; destruct_conjs; auto.
        + intros * In. rewrite Is_defined_in_lasts_defined, n_lastd1 in In.
          solve_In.
        + intros. simpl_Exists. simpl_Forall.
          eapply wt_equation_def_free in Hwt1; eauto.
          simpl_app. rewrite 2 InMembers_app in Hwt1. rewrite 2 InMembers_app.
          destruct Hwt1 as [|[|]]; [left|right; right|right; left]; solve_In.
        + replace (map fst (map (fun '(x1, (ty0, ck0)) => (x1, (ty0, ck0, false))) (n_out n))) with (map fst (n_out n)) in Hdef'.
          2:{ symmetry. erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto. }
          simpl_Forall. simpl_In. simpl_Forall.
          eapply wt_equation_restrict. 3:eauto.
          1,2:intros * In Def; apply In_nolast in In as (?&In).
          1,2:apply In_nolast; esplit; eapply incl_NoDup_In; eauto.
          3:eapply Hdef' with (x:=Var x1); eauto; solve_Exists; solve_In.
          5:eapply Hdef' with (x:=Last x1); eauto; solve_Exists; solve_In.
          1,3:apply incl_appr', incl_appl', incl_filter', incl_refl.
          1,2:erewrite fst_NoDupMembers, 2 map_app, 2 map_map,
              map_ext with (l:=n_in _), map_ext with (l:=n_out _); try apply n_nodup.
          all:intros; destruct_conjs; auto.
      - intros x tn Hin. specialize (Hwt2 x tn).
        repeat rewrite idfst_app, in_app_iff in Hin, Hwt2.
        destruct HG as (Htypes&_). rewrite <-Htypes.
        destruct Hin as [|[Hin|]]; auto.
        apply Hwt2; right; left. solve_In.
    Qed.

  End wt_node.

  Theorem dce_wt : forall G,
    wt_global G ->
    wt_global (dce_global G).
  Proof.
    intros.
    eapply CommonTyping.transform_units_wt_program; eauto.
    intros. eapply dce_node_wt; eauto using dce_global_iface_eq.
  Qed.

End DCETYPING.

Module DCETypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CESyn : CESYNTAX        Ids Op OpAux Cks)
       (CEF   : CEISFREE        Ids Op OpAux Cks CESyn)
       (CETyp : CETYPING        Ids Op OpAux Cks CESyn)
       (Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Free  : ISFREE          Ids Op OpAux Cks CESyn Syn CEF)
       (Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (Def   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Typ   : NLTYPING        Ids Op OpAux Cks CESyn Syn Ord CETyp)
       (DCE   : DCE             Ids Op OpAux Cks CESyn CEF Syn Free Mem Def)
<: DCETYPING Ids Op OpAux Cks CESyn CEF CETyp Syn Free Mem Def Ord Typ DCE.
  Include DCETYPING Ids Op OpAux Cks CESyn CEF CETyp Syn Free Mem Def Ord Typ DCE.
End DCETypingFun.
