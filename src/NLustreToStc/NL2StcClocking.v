From Velus Require Import NLustre.
From Velus Require Import Stc.

From Velus Require Import NLustreToStc.Translation.

From Velus Require Import VelusMemory.
From Velus Require Import Common Environment.
From Velus Require Import CoindToIndexed.
From Velus Require Import CommonProgram.
From Velus Require Import CommonTyping.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Permutation.

Open Scope nat.
Open Scope list.

Module Type NL2STCCLOCKING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import ComTyp: COMMONTYPING    Ids Op OpAux)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (       CStr  : COINDSTREAMS    Ids Op OpAux Cks)
       (       IStr  : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (       CIStr : COINDTOINDEXED  Ids Op OpAux        Cks CStr IStr)
       (Import CE    : COREEXPR        Ids Op OpAux ComTyp Cks IStr)
       (Import NL    : NLUSTRE         Ids Op OpAux ComTyp Cks CStr IStr CIStr CE)
       (Import Stc   : STC             Ids Op OpAux ComTyp Cks IStr       CE)
       (Import Trans : TRANSLATION     Ids Op OpAux        Cks            CE.Syn NL.Syn Stc.Syn NL.Mem).

  Lemma translate_eqn_wc env:
    forall G Γ eq,
      NoDupMembers Γ ->
      (forall x, Env.In x env <-> exists ck, In (x, (ck, true)) Γ) ->
      (forall x, Env.In x env ->
            ~In x (vars_defined (filter is_def_rhs [eq]))
            /\ ~In x (vars_defined (filter is_app [eq]))) ->
      wc_env (idfst Γ) ->
      NL.Clo.wc_equation G Γ eq ->
      Forall (wc_trconstr (translate G) Γ) (translate_eqn env eq).
  Proof.
    intros * ND EnvL EnvVD Wenv Wc.
    inversion Wc as [| |??????? Find Ins Outs|]; subst.
    - simpl. cases_eqn Eq; subst; repeat (constructor; auto).
      + destruct islast; auto. exfalso.
        edestruct EnvVD; simpl in *; eauto. eapply EnvL; eauto.
      + eapply Env.find_In, EnvL in Eq0 as (?&In).
        eapply NoDupMembers_det in H; eauto. now inv H.
      + now inv H0.
      + destruct islast; auto. exfalso.
        eapply Env.Props.P.F.in_find_iff; eauto.
        eapply EnvL; eauto.
    - simpl_Forall. simpl_In. econstructor; eauto.
      simpl_Forall.
      constructor; [eapply wc_env_var in Wenv; eauto|]; solve_In.
    - simpl. cases.
      constructor; [|simpl_Forall].
      + apply option_map_inv in Find as ((?&?)& Find &?); simpl in *; subst.
        apply find_unit_transform_units_forward in Find.
        econstructor; eauto.
        simpl_Forall. split; auto. do 2 esplit; eauto.
        destruct x0; auto. exfalso.
        edestruct EnvVD as (?&?); [|rewrite app_nil_r in *; eauto].
        eapply EnvL; eauto.
      + constructor. constructor; [eapply wc_env_var in Wenv; eauto|]; solve_In.
    - simpl.
      constructor; [|simpl_Forall].
      + constructor; auto.
      + econstructor; eauto.
        constructor; [eapply wc_env_var in Wenv; eauto|]; solve_In.
  Qed.

  Lemma translate_node_wc:
    forall G n,
      wc_node G n ->
      wc_system (translate G) (translate_node n).
  Proof.
    inversion_clear 1 as [? (?& Env & Heqs)].
    assert (incl
              (map (fun '(x1, (_, ck)) => (x1, (ck, false))) (n_in n ++ n_out n) ++
                 map (fun '(x1, (_, ck, islast)) => (x1, (ck, islast))) (n_vars n))
              (map (fun '(x1, (_, ck)) => (x1, (ck, false)))
                 (n_in n ++
                    idfst
                    (filter
                       (notb
                          (fun x1 : positive * (type * clock * bool) =>
                             PS.mem (fst x1)
                               (ps_from_list
                                  (map fst (fst (fst (gather_eqs (n_eqs n)))) ++ map fst (snd (fst (gather_eqs (n_eqs n))))))))
                       (n_vars n)) ++ n_out n) ++
                 map (fun '(x1, (_, _, ck)) => (x1, (ck, true))) (idfst (fst (fst (gather_eqs (n_eqs n))))) ++
                 map (fun '(x1, (_, _, ck)) => (x1, (ck, false))) (snd (fst (gather_eqs (n_eqs n)))))) as Incl.
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
          simpl_Forall. inv Heqs.
          rewrite ? in_app_iff in *. destruct H3 as [[|]|]; simpl_In.
          eapply NoDup_app_r, NoDup_app_l, fst_NoDupMembers, NoDupMembers_det in Hnd; [|eapply Hin0|eapply Hin].
          now inv Hnd.
        + rewrite gather_eqs_next_flat_map in Hin0. simpl_In.
          unfold gather_eq in *. cases; simpl in *. destruct Hinf as [Eq|Eq]; inv Eq.
          simpl_Forall. inv Heqs.
          rewrite ? in_app_iff in *. destruct H4 as [[|]|]; simpl_In.
          * exfalso. eapply NoDup_app_In in Hnd; [|solve_In]. eapply Hnd, in_app_iff. left. solve_In.
          * exfalso. eapply NoDup_app_r, NoDup_app_In in Hnd; [eapply Hnd|]; solve_In.
          * eapply NoDup_app_r, NoDup_app_l, fst_NoDupMembers, NoDupMembers_det in Hnd; [|eapply Hin0|eapply Hin].
            now inv Hnd.
    }
    repeat (split; auto); simpl.
    - unfold wc_env. simpl_Forall.
      eapply Cks.wc_clock_incl.
      1:{ etransitivity. eapply incl_map with (f:=fun xtc => (fst xtc, fst (snd xtc))), Incl. simpl_app.
          erewrite ? map_map, map_ext with (l:=n_in _), map_ext with (l:=filter _ _), map_ext with (l:=n_out _).
          apply incl_appr', incl_appr', incl_appr'.
          erewrite map_ext with (l:=fst _), map_ext with (l:=snd _). reflexivity.
          all:intros; destruct_conjs; auto. }
      eapply Forall_forall with (x:=(i,c)) in Env.
      + clear - Env. simpl_app. rewrite ? map_map in *.
        rewrite Permutation_app_comm with (l:=map _ (n_out _)); auto.
        erewrite map_ext with (l:=n_in _), map_ext with (l:=n_vars _), map_ext with (l:=n_out _); eauto.
        all:intros; destruct_conjs; auto.
      + clear - H Heqs.
        simpl_app. rewrite ? map_app, ? in_app_iff in *.
        destruct H as [|[|[|[|]]]]; auto; simpl_In.
        * right. left. solve_In.
        * rewrite gather_eqs_last_flat_map in Hin0. simpl_In.
          unfold gather_eq in *. cases; simpl in *. destruct Hinf as [Eq|Eq]; inv Eq.
          simpl_Forall. inv Heqs.
          rewrite ? in_app_iff in *. destruct H1 as [|[|]]; simpl_In.
          right; left. solve_In.
        * rewrite gather_eqs_next_flat_map in Hin. simpl_In.
          unfold gather_eq in *. cases; simpl in *. destruct Hinf as [Eq|Eq]; inv Eq.
          simpl_Forall. inv Heqs.
          rewrite ? in_app_iff in *. destruct H2 as [|[|]]; simpl_In; [left|right;right|right;left]; solve_In.
    - unfold translate_eqns. simpl_Forall. simpl_In. simpl_Forall.
      eapply translate_eqn_wc, Forall_forall in Heqs; eauto.
      eapply wc_trconstr_incl; eauto.
      + rewrite fst_NoDupMembers, ? map_app, ? map_map, <-app_assoc.
        erewrite map_ext with (l:=n_in _), map_ext with (l:=n_out _), map_ext with (l:=n_vars _).
        rewrite Permutation_app_comm with (l:=map _ (n_out _)). apply n_nodup.
        all:intros; destruct_conjs; auto.
      + intros *. rewrite Env.In_from_list, fst_InMembers, map_map, gather_eqs_last_defined, n_lastd1.
        split; [intros In|intros (?&In)].
        * simpl_In. esplit. rewrite in_app_iff. right. solve_In.
        * apply in_app_iff in In as [|]; solve_In.
      + intros * In. rewrite Env.In_from_list, fst_InMembers, map_map, gather_eqs_last_defined in In.
        split.
        * apply n_lastrhs in In. contradict In. clear - Hin In. simpl in *.
          cases_eqn Eq. simpl in *. rewrite app_nil_r in *.
          unfold vars_defined. solve_In.
        * apply n_lastapp in In. contradict In. clear - Hin In. simpl in *.
          cases_eqn Eq. simpl in *. rewrite app_nil_r in *.
          unfold vars_defined. solve_In.
      + clear - Env. eapply wc_env_Proper; [|eauto].
        simpl_app. erewrite ? map_map, map_ext with (l:=n_in _), map_ext with (l:=n_out _), map_ext with (l:=n_vars _).
        apply Permutation_app_head, Permutation_app_comm.
        1-3:intros; destruct_conjs; auto.
  Qed.

  Theorem translate_wc:
    forall G,
      wc_global G ->
      wc_program (translate G).
  Proof.
    unfold wc_global, wc_program; simpl; induction 1 as [|?? WC]; simpl; constructor; auto.
    apply translate_node_wc in WC; auto.
  Qed.

End NL2STCCLOCKING.

Module NL2StcClockingFun
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
<: NL2STCCLOCKING Ids Op OpAux ComTyp Cks CStr IStr CIStr CE NL Stc Trans.
  Include NL2STCCLOCKING Ids Op OpAux ComTyp Cks CStr IStr CIStr CE NL Stc Trans.
End NL2StcClockingFun.
