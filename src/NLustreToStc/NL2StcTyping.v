From Velus Require Import NLustre.
From Velus Require Import Stc.

From Velus Require Import NLustreToStc.Translation.

From Velus Require Import VelusMemory.
From Velus Require Import Common Environment.
From Velus Require Import CoindToIndexed.
From Velus Require Import CommonTyping.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Permutation.

Open Scope nat.
Open Scope list.

Module Type NL2STCTYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import ComTyp: COMMONTYPING    Ids Op OpAux)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (       CStr  : COINDSTREAMS    Ids Op OpAux Cks)
       (       IStr  : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (       CIStr : COINDTOINDEXED  Ids Op OpAux        Cks CStr IStr)
       (Import CE    : COREEXPR        Ids Op OpAux ComTyp Cks      IStr)
       (Import NL    : NLUSTRE         Ids Op OpAux ComTyp Cks CStr IStr CIStr CE)
       (Import Stc   : STC             Ids Op OpAux ComTyp Cks      IStr       CE)
       (Import Trans : TRANSLATION     Ids Op OpAux Cks                 CE.Syn NL.Syn Stc.Syn NL.Mem).

  Lemma translate_eqn_wt:
    forall G Γ env eq,
      NoDupMembers Γ ->
      (forall x, Env.In x env <-> exists ck, In (x, (ck, true)) Γ) ->
      (forall x, Env.In x env ->
            ~In x (vars_defined (filter is_def_rhs [eq]))
            /\ ~In x (vars_defined (filter is_app [eq]))) ->
      NL.Typ.wt_equation G Γ eq ->
      Forall (wt_trconstr (translate G) Γ) (translate_eqn env eq).
  Proof.
    intros * ND EnvL EnvVD Wt.
    inversion Wt as [???? Hin| |?????? Find|]; simpl.
    - take (wt_rhs _ _ _ _) and inv it; [|cases_eqn Eq]; repeat (econstructor; eauto).
      + destruct islast; auto. exfalso.
        edestruct EnvVD; simpl in *; eauto. eapply EnvL; eauto.
      + apply Env.find_In, EnvL in Eq as (?&In).
        eapply NoDupMembers_det in Hin; eauto. now inv Hin.
      + destruct islast; auto. exfalso.
        eapply Env.Props.P.F.in_find_iff; eauto.
        eapply EnvL; eauto.
    - simpl_Forall. simpl_In. econstructor; eauto.
      econstructor; eauto.
    - cases.
      apply option_map_inv in Find as ((?&?)& Find &?); simpl in *; subst.
      apply find_unit_transform_units_forward in Find.
      repeat (econstructor; eauto).
      simpl_Forall. simpl_In.
      repeat (econstructor; eauto).
    - repeat (econstructor; eauto).
      simpl_Forall. simpl_In.
      repeat (econstructor; eauto).
  Qed.

  Lemma translate_eqns_wt:
    forall G Γ env eqs,
      NoDupMembers Γ ->
      (forall x, Env.In x env <-> exists ck, In (x, (ck, true)) Γ) ->
      (forall x, Env.In x env ->
            ~In x (vars_defined (filter is_def_rhs eqs))
            /\ ~In x (vars_defined (filter is_app eqs))) ->
      Forall (NL.Typ.wt_equation G Γ) eqs ->
      Forall (wt_trconstr (translate G) Γ) (translate_eqns env eqs).
  Proof.
    intros * ND envL EnvVD Wt.
    unfold translate_eqns. simpl_Forall. simpl_In. simpl_Forall.
    eapply translate_eqn_wt, Forall_forall in Wt; eauto.
    intros * In. simpl. unfold vars_defined in *.
    edestruct EnvVD as (Nin1&Nin2); eauto.
    split; [contradict Nin1|contradict Nin2]; cases_eqn Eq;
      simpl in *; rewrite app_nil_r in *; solve_In.
  Qed.

  Lemma filter_fst_idfst:
    forall A B (xs: list (ident * (A * B))) P,
      idfst (filter (fun x => P (fst x)) xs) = filter (fun x => P (fst x)) (idfst xs).
  Proof.
    induction xs; simpl; intros; auto.
    cases; simpl; now rewrite IHxs.
  Qed.

  Lemma translate_node_wt_inits:
    forall G n,
      wt_node G n ->
      wt_states (translate G) (s_lasts (translate_node n) ++ s_nexts (translate_node n)).
  Proof.
    unfold translate_node, wt_node, wt_states; simpl.
    intros G n (WT &?).
    rewrite gather_eqs_last_flat_map, gather_eqs_next_flat_map.
    apply Forall_app; split; simpl_Forall; simpl_In.
    1,2:unfold gather_eq in *; cases; destruct Hinf as [Eq|Eq]; inv Eq.
    1,2:simpl_Forall; now inv WT.
  Qed.

  Lemma translate_node_wt:
    forall G n,
      wt_node G n ->
      wt_system (translate G) (translate_node n).
  Proof.
    intros * WTn; pose proof WTn as (WT & Enums).
    assert (incl
              (map (fun '(x0, (ty, _)) => (x0, (ty, false))) (n_in n ++ n_out n) ++
                 map (fun '(x0, (ty, _, islast)) => (x0, (ty, islast))) (n_vars n))
              (map (fun '(x0, (ty, _)) => (x0, (ty, false)))
                 (n_in n ++
                    idfst
                    (filter
                       (notb
                          (fun x0 : positive * (type * clock * bool) =>
                             PS.mem (fst x0)
                               (ps_from_list
                                  (map fst (fst (fst (gather_eqs (n_eqs n)))) ++ map fst (snd (fst (gather_eqs (n_eqs n))))))))
                       (n_vars n)) ++ n_out n) ++
                 map (fun '(x0, (_, ty, _)) => (x0, (ty, true))) (idfst (fst (fst (gather_eqs (n_eqs n))))) ++
                 map (fun '(x0, (_, ty, _)) => (x0, (ty, false))) (snd (fst (gather_eqs (n_eqs n)))))) as Incl.
    { intros ? In. rewrite ?map_app, ?in_app_iff in *. destruct In as [[|]|]; simpl_In.
      - left. left. solve_In.
      - left. right. right. solve_In.
      - rewrite <-filter_notb_app, in_app_iff in Hin. destruct Hin.
        2:{ left. right. left. unfold idfst. repeat (eapply in_map_iff; do 2 esplit); eauto.
            simpl. destruct b0; auto; exfalso.
            simpl_In. apply Bool.negb_true_iff, PSE.mem_4 in Hf.
            rewrite ps_from_list_In, gather_eqs_last_defined, in_app_iff in Hf.
            apply Hf. left. rewrite n_lastd1. solve_In. }
        simpl_In. right.
        rewrite PS.mem_spec, ps_from_list_In, in_app_iff in Hf.
        pose proof (n_nodup n) as Hnd.
        destruct Hf; [left|right]; solve_In.
        + rewrite gather_eqs_last_flat_map in Hin0. simpl_In.
          unfold gather_eq in *. cases; simpl in *. destruct Hinf as [Eq|Eq]; inv Eq.
          simpl_Forall. inv WT.
          rewrite ? in_app_iff in *. destruct H3 as [[|]|]; simpl_In.
          eapply NoDup_app_r, NoDup_app_l, fst_NoDupMembers, NoDupMembers_det in Hnd; [|eapply Hin0|eapply Hin].
          now inv Hnd.
        + rewrite gather_eqs_next_flat_map in Hin0. simpl_In.
          unfold gather_eq in *. cases; simpl in *. destruct Hinf as [Eq|Eq]; inv Eq.
          simpl_Forall. inv WT.
          rewrite ? in_app_iff in *. destruct H4 as [[|]|]; simpl_In.
          * exfalso. eapply NoDup_app_In in Hnd; [|solve_In]. eapply Hnd, in_app_iff. left. solve_In.
          * exfalso. eapply NoDup_app_r, NoDup_app_In in Hnd; [eapply Hnd|]; solve_In.
          * eapply NoDup_app_r, NoDup_app_l, fst_NoDupMembers, NoDupMembers_det in Hnd; [|eapply Hin0|eapply Hin].
            now inv Hnd.
    }

    split; [|split]; try (now apply translate_node_wt_inits).
    - eapply translate_eqns_wt in WT; eauto.
      + simpl_Forall. eapply Forall_forall in WT; eauto.
        eapply wt_trconstr_incl; eauto.
      + rewrite fst_NoDupMembers, ? map_app, ? map_map, <-app_assoc.
        erewrite map_ext with (l:=n_in _), map_ext with (l:=n_out _), map_ext with (l:=n_vars _).
        rewrite Permutation_app_comm with (l:=map _ (n_out _)). apply n_nodup.
        all:intros; destruct_conjs; auto.
      + intros *. rewrite Env.In_from_list, fst_InMembers, map_map, gather_eqs_last_defined, n_lastd1.
        split; [intros In|intros (?&In)].
        * simpl_In. esplit. rewrite in_app_iff. right. solve_In.
        * apply in_app_iff in In as [|]; solve_In.
      + intros * In. rewrite Env.In_from_list, fst_InMembers, map_map, gather_eqs_last_defined in In.
        split; auto using n_lastrhs, n_lastapp.
    - clear - WT Enums. intros * In.
      eapply Enums. simpl_app.
      rewrite ? in_app_iff in *. firstorder; eauto.
      simpl_In.
      + right; left; solve_In.
      + rewrite gather_eqs_last_flat_map in H. simpl_In. simpl_Forall.
        destruct x0; simpl in *; cases; firstorder. inv H.
        inv WT. take (In _ _) and rewrite ? in_app_iff in it. firstorder; solve_In.
        right. left. solve_In.
      + rewrite gather_eqs_next_flat_map in H. simpl_In. simpl_Forall.
        destruct x0; simpl in *; cases; firstorder. inv H.
        inv WT. take (In _ _) and rewrite ? in_app_iff in it.
        firstorder; [left|right;right|right;left]; solve_In.
  Qed.

  Theorem translate_wt:
    forall G,
      wt_global G ->
      wt_program (translate G).
  Proof.
    intros; eapply transform_units_wt_program; eauto using translate_node_wt.
  Qed.

End NL2STCTYPING.

Module NL2StcTypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (ComTyp: COMMONTYPING    Ids Op OpAux)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CStr  : COINDSTREAMS    Ids Op OpAux Cks)
       (IStr  : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (CIStr : COINDTOINDEXED  Ids Op OpAux        Cks CStr IStr)
       (CE    : COREEXPR        Ids Op OpAux ComTyp Cks      IStr)
       (NL    : NLUSTRE         Ids Op OpAux ComTyp Cks CStr IStr CIStr CE)
       (Stc   : STC             Ids Op OpAux ComTyp Cks      IStr       CE)
       (Trans : TRANSLATION     Ids Op OpAux Cks                 CE.Syn NL.Syn Stc.Syn NL.Mem)
<: NL2STCTYPING Ids Op OpAux ComTyp Cks CStr IStr CIStr CE NL Stc Trans.
  Include NL2STCTYPING Ids Op OpAux ComTyp Cks CStr IStr CIStr CE NL Stc Trans.
End NL2StcTypingFun.
