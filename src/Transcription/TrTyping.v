From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.

From Velus Require Import Lustre.LTyping.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLTyping.

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
       (Senv        : STATICENV Ids Op OpAux Cks)
       (L           : LSYNTAX  Ids Op OpAux Cks Senv)
       (LT          : LTYPING  Ids Op OpAux Cks Senv L)
       (Import CE   : CESYNTAX Ids Op OpAux Cks)
       (CET         : CETYPING Ids Op OpAux Cks CE)
       (NL          : NLSYNTAX Ids Op OpAux Cks CE)
       (Ord         : NLORDERED Ids Op OpAux Cks CE     NL)
       (NLT         : NLTYPING  Ids Op OpAux Cks CE NL Ord CET)
       (Import TR   : TR Ids Op OpAux Cks Senv L CE NL).

  Definition idty (env : Senv.static_env) : list (ident * (type * bool)) :=
    map (fun '(x, entry) => (x, (Senv.typ entry, isSome (Senv.causl_last entry)))) env.
  Global Hint Unfold idty : list.

  Lemma wt_clock_l_ce :
    forall types vars ck,
      LT.wt_clock types vars ck -> CET.wt_clock types (idty vars) ck.
  Proof.
    induction ck; intros * H; inv H.
    - constructor; eauto.
    - inv H3. econstructor; eauto.
      rewrite <-H0. solve_In.
  Qed.

  Lemma typeof_lexp {PSyn prefs} :
    forall (G: @L.global PSyn prefs) vars e e' ty,
      to_lexp e = OK e' ->
      LT.wt_exp G vars e ->
      L.typeof e = [ty] ->
      typeof e' = ty.
  Proof.
    intros * Htr Hwt Hty. generalize dependent e'. generalize dependent ty.
    induction e using L.exp_ind2; intros; inv Htr; inv Hty; simpl; auto.
    - cases.
    - cases.
    - cases. now monadInv H0.
    - cases. now monadInv H0.
    - cases. inv H. monadInv H1. simpl in *. inv Hwt. simpl_Foralls.
      take (L.typesof _ = _) and inversion it as [Ht].
      rewrite app_nil_r in Ht.
      take ([_] = [_]) and inv it.
      eauto.
  Qed.

  Fact add_whens_typeof : forall ty ck,
      typeof (add_whens (init_type ty) ty ck) = ty.
  Proof.
    induction ck as [|??? (?&?)]; simpl; auto.
    destruct ty; simpl; auto.
    f_equal. apply ctype_init_ctype.
  Qed.

  Lemma typeofc_cexp {PSyn prefs} :
    forall (G: @L.global PSyn prefs) vars e e' ty,
      to_cexp e = OK e' ->
      LT.wt_exp G vars e ->
      L.typeof e = [ty] ->
      CE.typeofc e' = ty.
  Proof.
    intros * Htr Hwt Hty. generalize dependent e'. generalize dependent ty.
    induction e using L.exp_ind2; intros; inv Htr; inv Hty; simpl; auto.
    - cases.
    - cases.
    - cases. monadInv H0. monadInv EQ. now simpl.
    - cases. monadInv H0. monadInv EQ. now simpl.
    - cases. monadInv H1. monadInv EQ. simpl in *. inv Hwt.
      take (L.typesof _ = _) and inversion it as [Ht].
      rewrite app_nil_r in Ht.
      take ([_] = [_]) and inv it.
      simpl_Foralls. eauto using typeof_lexp.
    - cases. monadInv H1. inv H2; auto.
    - cases; monadInv H2; inv H3; simpl in *; auto.
      + inv H0. inv Hwt; simpl in *. rewrite app_nil_r in *.
        inv H15; eauto.
      + simpl. apply add_whens_typeof.
  Qed.

  Lemma wt_constant {PSyn prefs} :
    forall (G: @L.global PSyn prefs) vars e ty c,
      to_constant e = OK c ->
      LT.wt_exp G vars e ->
      L.typeof e = [ty] ->
      wt_const G.(L.types) c ty.
  Proof.
    intros * Htr Hwt Hty.
    induction e using L.exp_ind2; intros; inv Htr; inv Hwt;
      simpl in *.
    - inv Hty. constructor.
    - inv Hty. inv H1. constructor; auto.
    - cases_eqn H1; subst.
      simpl in Hty. rewrite app_nil_r in Hty.
      apply Forall_singl in H8. apply Forall_singl in H; auto.
  Qed.

  Section wt_node.
    Variable (G : @L.global L.normalized fby_prefs).
    Hypothesis HwtG : LT.wt_global G.

    Lemma wt_add_whens vars : forall ty ck,
        wt_type (L.types G) ty ->
        CET.wt_clock (L.types G) vars ck ->
        CET.wt_exp (L.types G) vars (add_whens (init_type ty) ty ck).
    Proof.
      induction ck as [|??? (?&?)]; intros Henum Hck; inv Hck; simpl.
      - destruct ty; simpl; constructor.
        1,2:inv Henum; auto.
      - econstructor; eauto.
    Qed.

    Section wt_block.

      Variables vars : Senv.static_env.
      Hypothesis ND : NoDupMembers vars.

      Lemma wt_lexp :
        forall e e',
          to_lexp e = OK e' ->
          LT.wt_exp G vars e ->
          CET.wt_exp G.(L.types) (idty vars) e'.
      Proof.
        intros * Htr Hwt. generalize dependent e'.
        induction e using L.exp_ind2; intros; try (now inv Htr); inv Hwt; eauto with clocks nltyping.
        - inv Htr. now constructor.
        - inv Htr. inv H1. now constructor.
        - inv Htr. inv H1. econstructor. solve_In.
        - inv Htr. inv H1. inv H2.
          eapply NoDupMembers_det in H; eauto; subst. econstructor. solve_In.
          destruct Senv.causl_last; try congruence. auto.
        - monadInv Htr. constructor; eauto. eapply typeof_lexp in EQ as ->; eauto.
        - monadInv Htr. constructor; eauto.
          eapply typeof_lexp in EQ as ->; eauto.
          eapply typeof_lexp in EQ1 as ->; eauto.
        - inv Htr. cases. monadInv H1. inv H. inv H7. inv H4. econstructor; eauto.
          solve_In. rewrite H0. eauto.
      Qed.

      Lemma wt_cexp :
        forall e e',
          to_cexp e = OK e' ->
          Forall (wt_type (L.types G)) (map (fun '(_, a) => a.(Senv.typ)) vars) ->
          LT.wt_exp G vars e ->
          CET.wt_cexp G.(L.types) (idty vars) e'.
      Proof.
        intros * Htr Hwvars Hwt. generalize dependent e'.
        Opaque to_lexp.
        induction e using L.exp_ind2; intros; try (now inv Htr); inv Hwt; simpl in *; try monadInv Htr.
        1-7:eapply wt_lexp in EQ; eauto with nltyping. 1-7:econstructor; eauto.
        Transparent to_lexp.
        - cases_eqn Hb. monadInv Htr. take (Senv.HasType _ _ _) and inv it.
          econstructor; eauto.
          + solve_In. rewrite H1; eauto.
          + symmetry. erewrite length_map, <-Permutation_length; eauto using BranchesSort.Permuted_sort.
            erewrite mlength_map; [|eauto].
            erewrite <-length_map, H5, length_seq; auto.
          + clear - H7 H8 EQ.
            rewrite Forall_map, <-BranchesSort.Permuted_sort. generalize dependent x.
            induction es; intros; simpl in *; monadInv EQ; inv H7; inv H8; constructor; auto.
            cases_eqn EQ0; subst. inv H1. simpl in H3; rewrite app_nil_r in H3.
            monadInv EQ0. eapply typeofc_cexp in EQ1; eauto.
          + clear - H H7 EQ.
            rewrite Forall_map, <-BranchesSort.Permuted_sort. generalize dependent x.
            induction es; intros; simpl in *; monadInv EQ; inv H; inv H7; constructor; auto.
            cases_eqn EQ0; inv H1; inv H2; monadInv EQ0; auto.
        - cases_eqn Eq; simpl in *; subst. monadInv Htr.
          econstructor; eauto.
          + eapply wt_lexp in EQ; eauto.
          + eapply typeof_lexp in EQ; eauto.
          + symmetry. erewrite length_map, <-Permutation_length; eauto using BranchesSort.Permuted_sort.
            erewrite mlength_map; [|eauto].
            erewrite <-length_map, H8, length_seq; auto.
          + intros ? Hin.
            eapply in_map_iff in Hin as ((?&?)&Heq&Hin); simpl in *; inv Heq.
            rewrite <-BranchesSort.Permuted_sort in Hin.
            eapply mmap_inversion, Coqlib.list_forall2_in_right in EQ1 as ((?&?)&?&Hl); eauto.
            cases_eqn EQ; subst; monadInv Hl.
            rewrite add_whens_typeof.
            eapply typeofc_cexp in EQ0; eauto.
            eapply Forall_forall in H10; eauto; inv H10; eauto.
            eapply Forall_forall in H11; eauto. simpl in H11; rewrite app_nil_r in H11; auto.
          + econstructor. eapply wt_add_whens; eauto using wt_clock_l_ce.
            inv H11; try congruence. inv H10.
            eapply LT.wt_exps_wt_type in H11; eauto.
            rewrite H1 in H11; inv H11; auto.
          + intros ? Hin.
            eapply in_map_iff in Hin as ((?&?)&Heq&Hin); simpl in *; inv Heq.
            rewrite<-BranchesSort.Permuted_sort in Hin.
            eapply mmap_inversion, Coqlib.list_forall2_in_right in EQ1 as ((?&?)&?&Hl); eauto.
            cases_eqn EQ; subst; monadInv Hl.
            eapply Forall_forall in H; eauto; simpl in *. apply Forall_singl in H.
            eapply H; eauto. eapply Forall_forall in H10; eauto; inv H10; auto.
        - cases_eqn Eq; simpl in *; subst; monadInv Htr. inv H6.
          econstructor; eauto.
          + eapply wt_lexp in EQ; eauto.
          + eapply typeof_lexp in EQ; eauto.
          + symmetry. erewrite length_map, <-length_map.
            rewrite complete_branches_fst, length_seq; auto.
            * rewrite <-BranchesSort.Permuted_sort.
              erewrite fst_NoDupMembers, to_controls_fst, <-fst_NoDupMembers; eauto.
            * eapply Sorted.Sorted_StronglySorted, Sorted_impl, BranchesSort.Sorted_sort.
              intros (?&?) (?&?) (?&?) ??. lia.
              intros (?&?) (?&?) Ht; simpl in *. inv Ht.
              apply Nat.leb_le; auto.
            * rewrite <-BranchesSort.Permuted_sort.
              erewrite to_controls_fst; eauto.
          + intros ? Hin.
            eapply in_map_iff in Hin as ((?&?)&Heq&Hin); simpl in *; inv Heq.
            eapply complete_branches_In in Hin.
            rewrite <-BranchesSort.Permuted_sort in Hin.
            eapply mmap_inversion, Coqlib.list_forall2_in_right in EQ1 as ((?&?)&?&Hl); eauto.
            cases_eqn EQ; subst; monadInv Hl.
            eapply typeofc_cexp in EQ0; eauto. inv H13; eauto.
            eapply typeofc_cexp in EQ1; eauto.
            2:(eapply Forall_forall in H11; eauto; inv H11; eauto).
            2:(eapply Forall_forall in H12; eauto; simpl in H12; rewrite app_nil_r in H12; eauto).
            rewrite app_nil_r in *; subst; auto.
          + inv H13. inv H0. eauto.
          + intros ? Hin.
            eapply in_map_iff in Hin as ((?&?)&Heq&Hin); simpl in *; inv Heq.
            eapply complete_branches_In in Hin.
            rewrite <-BranchesSort.Permuted_sort in Hin.
            eapply mmap_inversion, Coqlib.list_forall2_in_right in EQ1 as ((?&?)&?&Hl); eauto.
            cases_eqn EQ; subst; monadInv Hl.
            eapply Forall_forall in H; eauto; simpl in *. apply Forall_singl in H.
            eapply H; eauto. eapply Forall_forall in H11; eauto; inv H11; auto.
      Qed.

      Lemma ty_lexp : forall env e e',
          LT.wt_exp G env e ->
          to_lexp e = OK e' ->
          L.typeof e = [CE.typeof e'].
      Proof.
        induction e using L.exp_ind2; intros * Hwt Htr; inv Htr.
        - now simpl.
        - now simpl.
        - destruct a. monadInv H0. now simpl.
        - destruct a. monadInv H0. now simpl.
        - destruct a. monadInv H0. now simpl.
        - destruct a. monadInv H0. now simpl.
        - cases. inv H. simpl. inv Hwt. inv H10. inv H5. monadInv H1.
          unfold L.typesof. unfold flat_map. simpl in *. rewrite app_nil_r in H11.
          eapply H3 in H2; eauto. congruence.
      Qed.

      Lemma wt_clock_of_suffix : forall types vars lck cbase,
          LT.wt_clock types vars cbase ->
          Forall (fun '(x, (ty, n)) => exists tx tn, ty = Tenum tx tn /\ In ty types /\ Senv.HasType vars x ty /\ n < length tn) lck ->
          LT.wt_clock types vars (clock_of_suffix lck cbase).
      Proof.
        induction lck as [|(?&?&?)]; intros * Hbase Hlck; simpl; auto.
        inversion_clear Hlck as [|(?&?) ? Htn]; destruct Htn as (?&?&?&Htypes&Hvars&Hinf); subst.
        eapply IHlck; eauto. constructor; auto.
      Qed.

      Lemma wt_suffix_of_clock : forall types ck,
          LT.wt_clock types vars ck ->
          Forall
            (fun '(x, (ty, n)) => exists tx tn, ty = Tenum tx tn /\ In ty types /\ Senv.HasType vars x ty /\ n < length tn)
            (suffix_of_clock ck []).
      Proof.
        intros *.
        assert (Forall (fun '(x, (ty, n)) => exists tx tn, ty = Tenum tx tn /\ In ty types /\ Senv.HasType vars x ty /\ n < length tn)
                  (@nil (ident * (type * enumtag))))
          as Hsuf by auto.
        revert Hsuf. generalize (@nil (ident * (type * enumtag))).
        induction ck; intros * Hsuf Hwt; inv Hwt; simpl.
        - assumption.
        - apply IHck; auto. constructor; eauto 6.
      Qed.

      Lemma incl_common_suffix :
        forall sfx1 sfx2,
          incl (common_suffix sfx1 sfx2) sfx1.
      Proof.
        intros * ? Hmem.
        generalize dependent sfx2. induction sfx1 as [|[]]; simpl; intros; auto.
        cases. inv Hmem; eauto.
      Qed.

      Lemma wt_find_base_clock :
        forall types lck,
          Forall (LT.wt_clock types vars) lck ->
          LT.wt_clock types vars (find_base_clock lck).
      Proof.
        unfold find_base_clock.
        destruct lck; intros * Hwt; inv Hwt; simpl. constructor.
        eapply wt_clock_of_suffix. constructor.
        specialize (wt_suffix_of_clock _ _ H1).
        generalize (suffix_of_clock c []).
        induction lck; intros * Hsuff; simpl; auto.
        inv H2. eapply IHlck; eauto.
        specialize (wt_suffix_of_clock _ _ H3) as Hsuff'.
        eapply Forall_incl; [|eapply incl_common_suffix; eauto]; eauto.
      Qed.

      Lemma wt_equation :
        forall P outs lasts env envo xr e e',
          to_global G = OK P ->
          to_equation env envo xr e = OK e' ->
          (forall x, Senv.IsLast vars x -> In x lasts) ->
          (forall i ck, find_clock env i = OK ck -> LT.wt_clock P.(NL.types) vars ck) ->
          Forall (fun xr0 => Senv.HasType vars xr0 bool_velus_type) (map fst xr) ->
          Forall (LT.wt_clock (L.types G) vars) (map snd xr) ->
          Forall (wt_type (L.types G)) (map (fun '(_, a) => a.(Senv.typ)) vars) ->
          NoDup (fst e) ->
          L.normalized_equation outs lasts e ->
          LT.wt_equation G vars e ->
          NLT.wt_equation P (idty vars) e'.
      Proof.
        Opaque to_cexp.
        intros ?????? [xs [|? []]] e' Hg Htr Hlasts Henvs Hxr Hckr Hen Hdup Hnorm (Hwt & Hf2);
          try (inv Htr; cases; discriminate).
        simpl_Forall.
        destruct e; simpl in *; cases_eqn Eq; monadInv Htr; simpl_Forall.
        all:try (take (Senv.HasType _ _ _) and inv it;
                 econstructor;
                 [simpl; erewrite typeofc_cexp; eauto; solve_In|
                   eauto using wt_clock_l_ce|
                   econstructor; erewrite to_global_types; eauto; eapply wt_cexp; eauto];
                 take (In _ _) and clear it; simpl_Forall; eauto).
        all:simpl; try rewrite app_nil_r in *; try congruence.
        - take (LT.wt_exp _ _ _) and inv it.
          take (Senv.HasType _ _ _) and inv it.
          repeat (econstructor; simpl).
          + solve_In. rewrite H0; eauto.
          + eapply wt_clock_l_ce; eauto.
            erewrite to_global_types; eauto.
          + simpl_Forall.
            eapply mmap_inversion, Coqlib.list_forall2_in_right in EQ; eauto; destruct_conjs.
            simpl_Forall.
            erewrite to_global_types; eauto using wt_lexp.
          + instantiate (1:=tyins). apply mmap_inversion in EQ.
            clear - EQ H4 H5. revert tyins H5.
            induction EQ; intros * Htys; inv H4; simpl in *.
            * inv Htys; auto.
            * eapply ty_lexp in H; eauto. rewrite H in *; simpl in *.
              inv Htys; constructor; auto.
          + erewrite to_global_externs; eauto.
        - simpl_Foralls. take (LT.wt_exp _ _ _) and inv it. simpl_Foralls.
          inv Hnorm. 2:inv H0; inv H.
          take (Senv.HasType _ _ _) and inv it.
          assert (Senv.causl_last e1 = None) as Nlast.
          { destruct (Senv.causl_last e1) eqn:Causl; auto. exfalso.
            take (~In _ lasts) and apply it, Hlasts. econstructor; eauto. congruence. }
          simpl in *. rewrite app_nil_r in *.
          constructor; eauto.
          + erewrite typeof_lexp; eauto.
            solve_In. rewrite Nlast; simpl. congruence.
          + eapply Henvs in EQ0. eapply wt_clock_l_ce; eauto.
          + rewrite <-H2 in *. erewrite typeof_lexp; eauto.
            erewrite to_global_types; eauto. eapply wt_constant; eauto.
          + erewrite to_global_types; eauto. eapply wt_lexp; eauto.
          + simpl_Forall. inv Hxr. split; [|split]; solve_In; try congruence.
            1,2:erewrite to_global_types; eauto using wt_clock_l_ce.
            inv HwtG; take (wt_type _ _) and inv it; eauto.
        - take (LT.wt_exp _ _ _) and inv it;
            assert (Hg':=Hg); eapply find_node_global in Hg' as (?&?&?); eauto.
          inv Hnorm. 2:inv H2; inv H1.
          eapply vars_of_spec in Eq.
          apply mmap_inversion in EQ.
          econstructor; simpl; eauto; try erewrite to_global_types; eauto.
          + erewrite <- (to_node_out n); eauto. unfold idfst in *. simpl_Forall.
            eapply Forall2_trans_ex in H7; eauto. simpl_Forall. subst.
            take (Senv.HasType _ _ _) and inv it. solve_In.
            destruct (Senv.causl_last _) eqn:Causl; auto. exfalso.
            { eapply H15, Hlasts. econstructor; eauto. congruence. }
          + erewrite <- (to_node_in n); eauto.
            clear - HwtG H3 H6 EQ. setoid_rewrite Forall2_map_2.
            remember (L.n_in n). clear Heql0. generalize dependent l0.
            generalize dependent x.
            induction l; intros; inv EQ; auto.
            inv H6; auto.
            simpl_Foralls. eapply ty_lexp in H2; eauto. simpl in *.
            rewrite H2 in H6. inv H6. destruct y as (?&((?&?)&?)).
            constructor; eauto.
          + apply wt_clock_l_ce, wt_find_base_clock.
            clear H5 H6 H9 H11 EQ.
            induction l; simpl; auto.
            inv H3. apply Forall_app.
            split; auto.
            apply LT.wt_exp_clockof in H5; auto.
          + clear H5 H6 H9 H11. generalize dependent l. induction x; intros; auto.
            inv EQ. simpl_Foralls.
            constructor; eauto using wt_lexp.
          + rewrite Forall_app; split.
            * simpl_Forall. inv Hxr. repeat split; solve_In; try congruence; eauto using wt_clock_l_ce.
              inv HwtG; take (wt_type _ _) and inv it; auto.
            * eapply Forall2_ignore1 in Eq. simpl_Forall; subst.
              simpl in *. inv H8. inv H4; inv H12; inv H13.
              split; [|split]; auto; solve_In; try congruence; eauto using wt_clock_l_ce.
              inv HwtG; take (wt_type _ _) and inv it; auto.
          + rewrite map_app, Forall_app; split; auto.
            * simpl_Forall; eauto using wt_clock_l_ce.
            * eapply Forall2_ignore1 in Eq. simpl_Forall; subst.
              simpl in *. inv H4; auto using wt_clock_l_ce with clocks.
      Qed.

      Lemma wt_block_to_equation :
        forall P outs lasts env envo d xr e' xs,
          to_global G = OK P ->
          block_to_equation env envo xr d = OK e' ->
          (forall x, Senv.IsLast vars x -> In x lasts) ->
          (forall i ck, find_clock env i = OK ck -> LT.wt_clock P.(NL.types) vars ck) ->
          Forall (fun xr0 => Senv.HasType vars xr0 bool_velus_type) (map fst xr) ->
          Forall (LT.wt_clock (L.types G) vars) (map snd xr) ->
          Forall (wt_type (L.types G)) (map (fun '(_, a) => a.(Senv.typ)) vars) ->
          L.VarsDefinedComp d xs ->
          NoDup xs ->
          L.normalized_block outs lasts d ->
          LT.wt_block G vars d ->
          NLT.wt_equation P (idty vars) e'.
      Proof.
        induction d using L.block_ind2; intros * Hg Htr Hlasts Henvs Hxr Hckr Hen Hvars Hdup Hnorm Hwt;
          inv Hvars; inv Hnorm; inv Hwt; simpl in *; try congruence.
        - eapply wt_equation in Htr; eauto.
        - monadInv Htr. take (Senv.HasType _ _ _) and inv it. take (Senv.IsLast _ _) and inv it.
          eapply NoDupMembers_det in H; eauto; subst.
          econstructor; eauto using wt_clock_l_ce.
          + take (L.typeof _ = _) and rewrite it; simpl.
            solve_In. destruct (Senv.causl_last _); try congruence; auto.
          + take (L.typeof _ = _) and rewrite it; simpl.
            erewrite to_global_types; eauto using wt_constant.
          + simpl_Forall. erewrite to_global_types; eauto. repeat split; eauto using wt_clock_l_ce.
            * inv HwtG. take (wt_type _ _) and inv it; auto.
            * inv Hxr. solve_In. congruence.
        - cases. simpl_Forall. inv H7.
          inv H6. inv H3.
          simpl in Hdup; rewrite app_nil_r in Hdup.
          eapply H4 in Htr; eauto.
          1,2:simpl; constructor; eauto with senv. all:clear H; simpl_Forall; auto.
      Qed.

    End wt_block.

    Lemma wt_clock_app :
      forall types ck l l',
        LT.wt_clock types l ck -> LT.wt_clock types (l ++ l') ck.
    Proof.
      intros * Hwt.
      eapply LT.wt_clock_incl; [|eauto].
      intros. apply Senv.HasType_app; auto.
    Qed.

    Lemma wt_node :
      forall P n n',
        to_node n = OK n' ->
        to_global G = OK P ->
        LT.wt_node G n ->
        NLT.wt_node P n'.
    Proof.
      intros * Htr Hg Wtn. inversion_clear Wtn as [?? Wti Wto Wte Hwt]; subst Γ.
      tonodeInv Htr. unfold NLT.wt_node. simpl.
      pose proof (L.n_nodup n) as (Hnd1&Hnd2).
      pose proof (L.n_syn n) as Hsyn. inversion Hsyn as [??? Hsyn1 Hsyn2 (?&Hvars&Hperm)]; clear Hsyn.
      rename H0 into Hblk. rewrite <-Hblk in *. symmetry in Hblk.
      assert (Forall (fun blk => exists xs, L.VarsDefinedComp blk xs /\ NoDup xs) blks) as Hvars'. 2:clear Hnd1 Hvars Hperm.
      { clear - Hnd1 Hnd2 Hvars Hperm.
        inv Hvars; inv H0; L.inv_VarsDefined.
        inv Hnd2; inv H1. apply Forall2_ignore2 in Hvars. simpl_Forall.
        do 2 esplit; eauto.
        eapply Common.CommonList.NoDup_concat; eauto. rewrite Hperm0, Hperm.
        apply NoDup_app'; eauto using NoDup_app_r.
        - apply fst_NoDupMembers; auto.
        - eapply Forall_forall; intros * Hinm1 Hinm2. eapply fst_InMembers, H5 in Hinm2.
          apply Hinm2. rewrite in_app_iff; auto.
      }
      monadInv Hmmap. inv Hnd2. inv H1. clear H2.
      split.
      - inv Hwt. inv H1. subst Γ'.
        eapply mmap_inversion in EQ.
        eapply envs_eq_node in Hblk.
        induction EQ; repeat (take (Forall _ (_::_)) and inv it); constructor; auto.
        destruct_conjs.
        eapply wt_block_to_equation in H; eauto; simpl; auto.
        + simpl_app. repeat rewrite map_map in *; simpl in *.
          erewrite map_ext, map_ext with (l:=l), map_ext_in with (l:=L.n_out _); eauto.
          1-3:unfold L.decl; intros; destruct_conjs; auto.
          simpl_Forall. subst; auto.
        + apply NoDupMembers_app; auto using L.node_NoDupMembers.
          * now apply Senv.NoDupMembers_senv_of_decls.
          * intros * InM1 InM2. apply Senv.InMembers_senv_of_decls in InM2. eapply H5; eauto.
            rewrite fst_InMembers, map_app, Senv.map_fst_senv_of_ins, Senv.map_fst_senv_of_decls in InM1; auto.
        + intros * Il. rewrite 2 Senv.IsLast_app in Il. destruct Il as [[Il|Il]|Il]; inv Il; simpl_In.
          * congruence.
          * simpl_Forall. contradiction.
          * unfold L.lasts_of_decls. solve_In. simpl. destruct o; try congruence. auto.
        + intros ?? Hfind.
          eapply envs_eq_find' in Hfind; eauto.
          erewrite to_global_types; eauto.
          clear - Wti Wto H2 Hfind. unfold Senv.senv_of_ins, Senv.senv_of_decls, LT.wt_clocks, idfst, idsnd in *.
          rewrite ? Senv.HasClock_app in Hfind. destruct Hfind as [Hin|[Hin|Hin]]; inv Hin; simpl_In; simpl_Forall; eauto.
          1,2:eapply LT.wt_clock_incl; [|eauto].
          1,2:intros; simpl_app; repeat rewrite Senv.HasType_app in *; intuition.
        + rewrite map_app. apply Forall_app; split; simpl_Forall; simpl_In; simpl_Forall; auto.
      - erewrite to_global_types; eauto.
        clear - Wte Hwt. inv Hwt; inv H1. intros * Hin.
        simpl_app. repeat rewrite map_map in *; simpl in *.
        rewrite Forall_app in Wte. destruct Wte.
        repeat rewrite in_app_iff in Hin. destruct Hin as [|[|]]; simpl_In; simpl_Forall; eauto.
    Qed.

  End wt_node.

  Lemma wt_transcription :
    forall G P,
      LT.wt_global G ->
      to_global G = OK P ->
      NLT.wt_global P.
  Proof.
    intros [] ? (Hbool&Hwt). revert P.
    induction nodes as [| n]. inversion 1. constructor.
    intros * Htr; simpl in *. monadInv Htr. simpl in *. monadInv EQ.
    inversion_clear Hwt as [|?? (Hwt'&Hnames) Hf ].
    constructor; simpl in *.
    - split.
      + eapply wt_node; eauto. constructor; auto.
        unfold to_global; simpl; rewrite EQ; simpl; auto.
      + erewrite to_node_name in Hnames; eauto.
        replace x1 with (NL.Global types externs x1).(NL.nodes) by auto.
        eapply to_global_names with (G:=L.Global types externs nodes); eauto.
        unfold to_global; simpl; rewrite EQ; simpl; auto.
    - eapply IHnodes in Hf; eauto.
      2:unfold to_global; simpl; erewrite EQ; simpl; auto.
      auto.
  Qed.

End TRTYPING.

Module TrTypingFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (OpAux: OPERATORS_AUX Ids Op)
       (Cks  : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (L    : LSYNTAX  Ids Op OpAux Cks Senv)
       (LT   : LTYPING  Ids Op OpAux Cks Senv L)
       (CE   : CESYNTAX Ids Op OpAux Cks)
       (CET  : CETYPING Ids Op OpAux Cks CE)
       (NL   : NLSYNTAX Ids Op OpAux Cks CE)
       (Ord  : NLORDERED Ids Op OpAux Cks CE     NL)
       (NLT  : NLTYPING  Ids Op OpAux Cks CE NL Ord CET)
       (TR   : TR Ids Op OpAux Cks Senv L CE NL)
<: TRTYPING Ids Op OpAux Cks Senv L LT CE CET NL Ord NLT TR.
  Include TRTYPING Ids Op OpAux Cks Senv L LT CE CET NL Ord NLT TR.
End TrTypingFun.
