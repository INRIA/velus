From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.

From Velus Require Import Lustre.LTyping.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLTyping.
From Velus Require Import Lustre.Normalization.Unnesting.

From Coq Require Import String.
From Coq Require Import Permutation.

From Coq Require Import List.
Import List.ListNotations.

From compcert Require Import common.Errors.
Open Scope error_monad_scope.

(** * Typing Preservation for Transcription *)

Module Type TRTYPING
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX Ids Op)
       (Import Cks  : CLOCKS Ids Op OpAux)
       (L           : LSYNTAX  Ids Op OpAux Cks)
       (LT          : LTYPING  Ids Op OpAux Cks L)
       (FNS         : UNNESTING Ids Op OpAux Cks L)
       (Import CE   : CESYNTAX Ids Op OpAux Cks)
       (CET         : CETYPING Ids Op OpAux Cks CE)
       (NL          : NLSYNTAX Ids Op OpAux Cks CE)
       (Ord         : NLORDERED Ids Op OpAux Cks CE     NL)
       (NLT         : NLTYPING  Ids Op OpAux Cks CE NL Ord CET)
       (Import TR   : TR Ids Op OpAux Cks L CE NL).

  Lemma wt_clock_l_ce :
    forall enums vars ck,
      LT.wt_clock enums vars ck -> CET.wt_clock enums vars ck.
  Proof.
    induction ck; intros * H; inv H; constructor; eauto.
  Qed.

  Lemma typeof_lexp {prefs} :
    forall (G: @L.global prefs) vars e e' ty,
      to_lexp e = OK e' ->
      LT.wt_exp G vars e ->
      L.typeof e = [ty] ->
      typeof e' = ty.
  Proof.
    intros * Htr Hwt Hty. revert dependent e'. revert dependent ty.
    induction e using L.exp_ind2; intros; inv Htr; inv Hty; simpl; auto.
    - cases.
    - cases. now monadInv H0.
    - cases. now monadInv H0.
    - cases. inv H. monadInv H1. simpl in *. inv Hwt. simpl_Foralls.
      take (L.typesof _ = _) and inversion it as [Ht].
      rewrite app_nil_r in Ht.
      take ([_] = [_]) and inv it.
      eauto.
  Qed.

  Lemma typeofc_cexp {prefs} :
    forall (G: @L.global prefs) vars e e' ty,
      to_cexp e = OK e' ->
      LT.wt_exp G vars e ->
      L.typeof e = [ty] ->
      CE.typeofc e' = ty.
  Proof.
    intros * Htr Hwt Hty. revert dependent e'. revert dependent ty.
    induction e using L.exp_ind2; intros; inv Htr; inv Hty; simpl; auto.
    - cases.
    - cases. monadInv H0. monadInv EQ. now simpl.
    - cases. monadInv H0. monadInv EQ. now simpl.
    - cases. monadInv H1. monadInv EQ. simpl in *. inv Hwt.
      take (L.typesof _ = _) and inversion it as [Ht].
      rewrite app_nil_r in Ht.
      take ([_] = [_]) and inv it.
      simpl_Foralls. eauto using typeof_lexp.
    - cases. monadInv H1. inv H2; auto.
    - cases; monadInv H2. inv H3; simpl; auto.
      inv H0. inv Hwt; simpl in *. rewrite app_nil_r in *.
      inv H14; eauto.
  Qed.

  Lemma wt_constant {prefs} :
    forall (G: @L.global prefs) vars e ty c,
      to_constant e = OK c ->
      LT.wt_exp G vars e ->
      L.typeof e = [ty] ->
      wt_const G.(L.enums) c ty.
  Proof.
    intros * Htr Hwt Hty.
    induction e using L.exp_ind2; intros; inv Htr; inv Hwt;
      simpl in *.
    - inv Hty. constructor.
    - inv Hty. constructor; auto.
    - cases_eqn H1; subst.
      simpl in Hty. rewrite app_nil_r in Hty.
      apply Forall_singl in H8. apply Forall_singl in H; auto.
  Qed.

  Lemma wt_lexp {prefs} :
    forall (G: @L.global prefs) vars e e',
      to_lexp e = OK e' ->
      LT.wt_exp G vars e ->
      CET.wt_exp G.(L.enums) vars e'.
  Proof.
    intros * Htr Hwt. revert dependent e'.
    induction e using L.exp_ind2; intros; try (now inv Htr); inv Hwt.
    - inv Htr. now constructor.
    - inv Htr. now constructor.
    - monadInv Htr. constructor; eauto. eapply typeof_lexp in EQ as ->; eauto.
    - monadInv Htr. constructor; eauto.
      eapply typeof_lexp in EQ as ->; eauto.
      eapply typeof_lexp in EQ1 as ->; eauto.
    - inv Htr. cases. monadInv H1. inv H. inv H7. econstructor; eauto.
  Qed.

  Lemma wt_cexp {prefs} :
    forall (G: @L.global prefs) vars e e',
      to_cexp e = OK e' ->
      LT.wt_exp G vars e ->
      CET.wt_cexp G.(L.enums) vars e'.
  Proof.
    intros * Htr Hwt. revert dependent e'.
    induction e using L.exp_ind2; intros; try (now inv Htr); inv Hwt.
    - inv Htr. now constructor.
    - inv Htr. constructor; eauto.
    - monadInv Htr. constructor; eauto.
    - monadInv Htr. monadInv EQ. constructor.
      constructor; eauto using wt_lexp.
      eapply typeof_lexp in EQ0 as ->; eauto.
    - monadInv Htr. monadInv EQ. constructor.
      constructor; eauto using wt_lexp.
      eapply typeof_lexp in EQ0 as ->; eauto.
      eapply typeof_lexp in EQ as ->; eauto.
    - monadInv Htr. cases. monadInv EQ.
      constructor. simpl_Foralls. econstructor; eauto using wt_lexp.
    - inv Htr. cases_eqn Hb. monadInv H1.
      constructor; eauto.
      + erewrite mmap_length; eauto.
      + clear - H7 H8 EQ. revert dependent x.
        induction es; intros; simpl in *; monadInv EQ; inv H7; inv H8; constructor; auto.
        cases_eqn EQ0; subst. inv H1. simpl in H3; rewrite app_nil_r in H3.
        eapply typeofc_cexp in EQ0; eauto.
      + clear - H H7 EQ. revert dependent x.
        induction es; intros; simpl in *; monadInv EQ; inv H; inv H7; constructor; auto.
        cases_eqn EQ0; inv H1; inv H2; auto.
    - inv Htr. cases_eqn H2; simpl in *; rewrite app_nil_r in *; subst. monadInv H2.
      apply Forall_singl in H12. apply Forall_singl in H0.
      econstructor; eauto.
      + eapply wt_lexp in EQ; eauto.
      + eapply typeof_lexp in EQ; eauto.
      + erewrite mmap_length; eauto.
      + eapply typeofc_cexp in EQ0; eauto; subst.
        clear - H H4 H10 H11 EQ1. revert dependent x0.
        induction es; intros; simpl in *; monadInv EQ1; inv H; inv H0.
        * cases_eqn EQ; subst. monadInv EQ.
          eapply typeofc_cexp in EQ0; eauto.
          -- eapply Forall_forall in H10; eauto with datatypes.
          -- erewrite <- H11; eauto with datatypes.
             simpl; now rewrite app_nil_r.
        * eapply IHes in EQ1; eauto.
      + clear - H H10 EQ1. revert dependent x0.
        induction es; intros; simpl in *; monadInv EQ1; inv H; inv H0; auto.
        * cases_eqn EQ; subst. monadInv EQ.
          apply Forall_singl in H3. eapply H3; eauto.
          eapply Forall_forall in H10; eauto with datatypes.
        * eapply IHes; eauto.
  Qed.

  Lemma ty_lexp {prefs} :
    forall (G: @L.global prefs) env e e',
      LT.wt_exp G env e ->
      to_lexp e = OK e' ->
      L.typeof e = [CE.typeof e'].
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr; inv Htr.
    - now simpl.
    - now simpl.
    - destruct a. inv H0. now simpl.
    - destruct a. simpl. monadInv H0. now simpl.
    - destruct a. monadInv H0. now simpl.
    - cases. inv H. simpl. inv Hwt. inv H10. inv H5. monadInv H1.
      unfold L.typesof. unfold flat_map. simpl in *. rewrite app_nil_r in H11.
      eapply H3 in H2; eauto. congruence.
  Qed.

  Lemma wt_clock_of_suffix : forall enums vars lck cbase,
      LT.wt_clock enums vars cbase ->
      Forall (fun '(x, (ty, n)) => exists tn, ty = Tenum tn /\ In tn enums /\ In (x, ty) vars /\ n < snd tn) lck ->
      LT.wt_clock enums vars (clock_of_suffix lck cbase).
  Proof.
    induction lck as [|(?&?&?)]; intros * Hbase Hlck; simpl; auto.
    inversion_clear Hlck as [|(?&?) ? Htn]; destruct Htn as ((?&?)&?&Henums&Hvars&Hinf); subst.
    eapply IHlck; eauto. constructor; auto.
  Qed.

  Lemma wt_suffix_of_clock : forall enums vars ck,
      LT.wt_clock enums vars ck ->
      Forall
        (fun '(x, (ty, n)) => exists tn, ty = Tenum tn /\ In tn enums /\ In (x, ty) vars /\ n < snd tn)
        (suffix_of_clock ck []).
  Proof.
    intros *.
    assert (Forall (fun '(x, (ty, n)) => exists tn , ty = Tenum tn /\ In tn enums /\ In (x, ty) vars /\ n < snd tn)
                   (@nil (ident * (type * enumtag))))
      as Hsuf by auto.
    revert Hsuf. generalize (@nil (ident * (type * enumtag))).
    induction ck; intros * Hsuf Hwt; inv Hwt; simpl.
    - assumption.
    - apply IHck; auto. constructor; eauto.
  Qed.

  Lemma incl_common_suffix :
    forall sfx1 sfx2,
    incl (common_suffix sfx1 sfx2) sfx1.
  Proof.
    intros * ? Hmem.
    revert dependent sfx2. induction sfx1 as [|[]]; simpl; intros; auto.
    cases. inv Hmem; eauto.
  Qed.

  Lemma wt_find_base_clock :
    forall enums vars lck,
    Forall (LT.wt_clock enums vars) lck ->
    LT.wt_clock enums vars (find_base_clock lck).
  Proof.
    unfold find_base_clock.
    destruct lck; intros * Hwt; inv Hwt; simpl. constructor.
    eapply wt_clock_of_suffix. constructor.
    specialize (wt_suffix_of_clock _ _ _ H1).
    generalize (suffix_of_clock c []).
    induction lck; intros * Hsuff; simpl; auto.
    inv H2. eapply IHlck; eauto.
    specialize (wt_suffix_of_clock _ _ _ H3) as Hsuff'.
    eapply Forall_incl; [|eapply incl_common_suffix; eauto]; eauto.
  Qed.

  Lemma wt_clockof {prefs} :
    forall (G: @L.global prefs) vars e,
      FNS.normalized_cexp e ->
      LT.wt_exp G vars e ->
      Forall (LT.wt_clock G.(L.enums) vars) (L.clockof e).
  Proof.
    intros * Hnormed Hwt.
    eapply LT.wt_exp_clockof in Hwt.
    eapply FNS.normalized_cexp_no_fresh in Hnormed.
    rewrite Hnormed, app_nil_r in Hwt; auto.
  Qed.

  Lemma wt_equation :
    forall G P env envo vars e e',
      to_global G = OK P ->
      to_equation env envo e = OK e' ->
      LT.wt_global G ->
      (forall i ck, find_clock env i = OK ck -> LT.wt_clock P.(NL.enums) vars ck) ->
      NoDup (fst e) ->
      FNS.unnested_equation G e ->
      LT.wt_equation G vars e ->
      NLT.wt_equation P vars e'.
  Proof.
    intros ????? [xs [|? []]] e' Hg Htr HwtG Henvs Hdup Hnormed (Hwt & Hf2);
      try (inv Htr; cases; discriminate).
    destruct e; simpl in *.
    - cases. monadInv Htr. inv Hf2. constructor; eauto using wt_clock_l_ce.
    - cases. monadInv Htr. inv Hf2. apply Forall_singl in Hwt. inv Hwt.
      repeat constructor; eauto using wt_clock_l_ce.
      erewrite to_global_enums; eauto.
    - cases. monadInv Htr. monadInv EQ1. monadInv EQ0. inv Hf2.
      constructor; eauto using wt_clock_l_ce. inversion_clear Hwt as [|?? Wt].
      inv Wt. repeat constructor. assumption.
    - cases. monadInv Htr. inv Hf2. monadInv EQ1. monadInv EQ0.
      constructor; eauto using wt_clock_l_ce. inversion_clear Hwt as [|?? Wt].
      inv Wt. constructor. erewrite to_global_enums; eauto.
      constructor; eauto using wt_lexp.
      eapply typeof_lexp in EQ1 as ->; eauto.
    - cases. monadInv Htr. inv Hf2. monadInv EQ1. monadInv EQ0.
      constructor; eauto using wt_clock_l_ce. inversion_clear Hwt as [|?? Wt].
      inv Wt. constructor. erewrite to_global_enums; eauto.
      constructor; eauto using wt_lexp.
      eapply typeof_lexp in EQ1 as ->; eauto.
      eapply typeof_lexp in EQ0 as ->; eauto.
    - remember (vars_of l1) as varsl1.
      cases; monadInv Htr. symmetry in Heqvarsl1.
      eapply vars_of_spec in Heqvarsl1.
      simpl_Foralls. take (LT.wt_exp _ _ _) and inv it. simpl_Foralls.
      simpl in *. rewrite app_nil_r in *.
      constructor; eauto.
      + erewrite typeof_lexp with (ty:=y); eauto.
        congruence.
      + rewrite <-H2 in H8. erewrite typeof_lexp; eauto.
        rewrite <-H2 in H9.
        erewrite to_global_enums; eauto. eapply wt_constant; eauto.
      + eapply Henvs in EQ0. eapply wt_clock_l_ce; eauto.
      + erewrite to_global_enums; eauto. eapply wt_lexp; eauto.
      + eapply Forall_map. eapply Forall2_ignore1 in Heqvarsl1.
        eapply Forall_impl; [|eauto]. intros (?&?) (?&?&?&?&?); subst.
        eapply Forall_forall in H7; eauto. eapply Forall_forall in H10; eauto.
        simpl in *. inv H10. inv H7; split; auto.
        erewrite to_global_enums; eauto. inv HwtG; auto.
      + eapply Forall_map. eapply Forall2_ignore1 in Heqvarsl1.
        eapply Forall_impl; [|eauto]. intros (?&?) (?&?&?&?&?); subst.
        eapply Forall_forall in H7; eauto. eapply Forall_forall in H10; eauto.
        simpl in *. inv H10. inv H7; inv H12; erewrite to_global_enums; eauto using wt_clock_l_ce.
    - cases; monadInv Htr; monadInv EQ1; try discriminate.
    - cases; monadInv Htr; monadInv EQ1; try discriminate.
      monadInv EQ0.
      simpl_Foralls. take (LT.wt_exp _ _ _) and inv it. simpl_Foralls.
      take (L.typesof _ = _) and inversion it as [Ht].
      rewrite app_nil_r in Ht.
      constructor; eauto using wt_clock_l_ce; simpl in *.
      + eapply typeof_lexp in EQ1 as ->; eauto.
      + constructor. erewrite to_global_enums; eauto.
        econstructor; eauto using wt_lexp.
    - cases; monadInv Htr; monadInv EQ1; try discriminate.
      constructor; eauto using wt_clock_l_ce.
      + simpl_Foralls; auto.
      + simpl_Foralls. erewrite to_global_enums; eauto.
        eapply wt_cexp in H1; simpl; eauto.
        rewrite EQ0; simpl; auto.
    - cases; monadInv Htr. 1,2,4,5:monadInv EQ1. simpl_Foralls.
      constructor; eauto using wt_clock_l_ce; simpl in *.
      + simpl_Foralls. eapply typeofc_cexp in H1; eauto.
        2:simpl; eauto. congruence.
      + simpl_Foralls. erewrite to_global_enums; eauto.
        eapply wt_cexp in H1; simpl; eauto.
    - rewrite app_nil_r in Hf2.
      simpl_Foralls.
      take (LT.wt_exp _ _ _) and inv it;
        assert (Hg':=Hg); eapply find_node_global in Hg' as (?&?&?); eauto.
      monadInv Htr.
      destruct (vars_of l0) eqn:Vars; monadInv EQ0.
      eapply vars_of_spec in Vars.
      apply mmap_inversion in EQ.
      econstructor; simpl; eauto; try erewrite to_global_enums; eauto.
      + erewrite <- (to_node_out n); eauto. rewrite Forall2_map_2 in Hf2.
        apply Forall2_forall. split.
        2:{ repeat take (Forall2 _ _ _) and apply Forall2_length in it.
            rewrite it; auto. }
        intros ? (?&(?&?)) Hin.
        eapply Forall2_chain_In in Hin; eauto.
        now destruct Hin as (?&?& <-).
      + erewrite <- (to_node_in n); eauto.
        clear - H3 H6 EQ.
        remember (L.n_in n). clear Heql0. revert dependent l0.
        revert dependent x0.
        induction l; intros; inv EQ; auto.
        inv H6; auto.
        simpl_Foralls. eapply ty_lexp in H1; eauto. simpl in *.
        rewrite H1 in H6. inv H6.
        constructor; eauto.
      + apply wt_clock_l_ce, wt_find_base_clock.
        inv Hnormed; [|inv H2; inv H1].
        clear H5 H6 H9 H15 EQ.
        induction l; simpl; auto.
        inv H3. inv H12. apply Forall_app.
        split; auto.
        apply wt_clockof in H5; auto.
      + clear H5 H6 H9 Hnormed. revert dependent l. induction x0; intros; auto.
        inv EQ. simpl_Foralls.
        constructor; eauto using wt_lexp.
      + eapply Forall_map. eapply Forall2_ignore1 in Vars.
        eapply Forall_impl; [|eauto]. intros (?&?) (?&?&?&?&?); subst.
        eapply Forall_forall in H4; eauto. eapply Forall_forall in H8; eauto.
        simpl in *. inv H8. inv H4; split; auto.
        destruct HwtG as (?&_); auto.
      + eapply Forall_map. eapply Forall2_ignore1 in Vars.
        eapply Forall_impl; [|eauto]. intros (?&?) (?&?&?&?&?); subst.
        eapply Forall_forall in H4; eauto. eapply Forall_forall in H8; eauto.
        simpl in *. inv H4; inv H13; auto using wt_clock_l_ce.
  Qed.

  Lemma wt_clock_app :
    forall enums ck l l',
      LT.wt_clock enums l ck -> LT.wt_clock enums (l ++ l') ck.
  Proof.
    intros * Hwt.
    eapply LT.wt_clock_incl; eauto.
    apply incl_appl, incl_refl.
  Qed.

  Lemma wt_node :
    forall G P n n',
      to_node n = OK n' ->
      to_global G = OK P ->
      FNS.unnested_node G n ->
      LT.wt_global G ->
      LT.wt_node G n ->
      NLT.wt_node P n'.
  Proof.
    intros * Htr Hg Hnormed HwtG (Wti& Wto & Wtv & Wte & Hwt).
    tonodeInv Htr. unfold NLT.wt_node. simpl.
    split.
    - pose proof (L.NoDup_vars_defined_n_eqs n) as Hdup.
      revert dependent x.
      unfold FNS.unnested_node in Hnormed.
      induction (L.n_eqs n); intros; simpl in *; monadInv Hmmap; auto.
      inv Hwt. inv Hnormed.
      simpl in Hdup. apply NoDup_app'_iff in Hdup as (?&?&?).
      constructor; auto. eapply wt_equation; eauto.

      intros i ck Hfind.
      erewrite to_global_enums; eauto.
      unfold find_clock in Hfind.
      cases_eqn Hfind. inv Hfind.
      apply Env.find_env_from_list' in Hfind0 as [Hin|[? Hfind]].
      pose proof Hin as Wt; eapply Forall_forall in Wt; eauto.
      simpl in Wt. now setoid_rewrite Permutation_app_comm in Wt at 2.
      apply Env.find_env_from_list' in Hfind as [Hin|[? Hfind]].
      pose proof Hin as Wt; eapply Forall_forall in Wt; eauto.
      simpl in Wt. unfold idty. rewrite map_app.
      eapply wt_clock_app in Wt; eauto.
      apply Env.from_list_find_In in Hfind as Hin.
      pose proof Hin as Wt; eapply Forall_forall in Wt; eauto.
      simpl in Wt. setoid_rewrite Permutation_app_comm at 2.
      eapply wt_clock_app in Wt; eauto. unfold idty.
      rewrite app_assoc, map_app. eauto.
    - erewrite to_global_enums; eauto.
      clear - Wte. intros * Hin.
      rewrite Forall_map in Wte. eapply Forall_forall in Wte; eauto.
      destruct Wte; auto.
  Qed.

  Lemma wt_transcription :
    forall G P,
      FNS.unnested_global G ->
      LT.wt_global G ->
      to_global G = OK P ->
      NLT.wt_global P.
  Proof.
    intros (?&nds) ? Hnormed (Hbool&Hwt). revert P.
    induction nds as [| n]. inversion 1. constructor.
    intros * Htr; simpl in *. monadInv Htr. simpl in *. monadInv EQ.
    inversion_clear Hwt as [|?? (Hwt'&Hnames) Hf ].
    inversion_clear Hnormed as [|?? (Hnormed'&?) ].
    constructor; simpl in *.
    - split.
      + eapply wt_node; eauto. 2:constructor; auto.
        unfold to_global; simpl; rewrite EQ; simpl; auto.
      + erewrite to_node_name in Hnames; eauto.
        replace x1 with (NL.Global enums x1).(NL.nodes) by auto.
        eapply to_global_names with (G:=L.Global enums nds); eauto.
        unfold to_global; simpl; rewrite EQ; simpl; auto.
    - eapply IHnds in H0; eauto.
      2:unfold to_global; simpl; erewrite EQ; simpl; auto.
      auto.
  Qed.

End TRTYPING.

Module TrTypingFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (OpAux: OPERATORS_AUX Ids Op)
       (Cks  : CLOCKS Ids Op OpAux)
       (L    : LSYNTAX  Ids Op OpAux Cks)
       (LT   : LTYPING  Ids Op OpAux Cks L)
       (FNS  : UNNESTING Ids Op OpAux Cks L)
       (CE   : CESYNTAX Ids Op OpAux Cks)
       (CET  : CETYPING Ids Op OpAux Cks CE)
       (NL   : NLSYNTAX Ids Op OpAux Cks CE)
       (Ord  : NLORDERED Ids Op OpAux Cks CE     NL)
       (NLT  : NLTYPING  Ids Op OpAux Cks CE NL Ord CET)
       (TR   : TR Ids Op OpAux Cks L CE NL)
<: TRTYPING Ids Op OpAux Cks L LT FNS CE CET NL Ord NLT TR.
  Include TRTYPING Ids Op OpAux Cks L LT FNS CE CET NL Ord NLT TR.
End TrTypingFun.
