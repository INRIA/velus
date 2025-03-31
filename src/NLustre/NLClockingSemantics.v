From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import IndexedStreams.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import NLustre.NLIndexedSemantics.
From Velus Require Import CoreExpr.CEClockingSemantics.
From Coq Require Import List.

(** * Link (static) clocking predicates to (dynamic) semantic model *)

(**

These results confirm the correctness of the clocking predicates wrt the
semantics. In particular, they are useful for relating static invariants to
dynamic properties. They hold essentially due to the "additional" clocking
constraints in the NLustre semantic model.

 *)

Module Type NLCLOCKINGSEMANTICS
       (Import Ids      : IDS)
       (Import Op       : OPERATORS)
       (Import OpAux    : OPERATORS_AUX       Ids Op)
       (Import Cks      : CLOCKS              Ids Op OpAux)
       (Import CESyn    : CESYNTAX            Ids Op OpAux Cks)
       (Import Syn      : NLSYNTAX            Ids Op OpAux Cks CESyn)
       (Import Str      : INDEXEDSTREAMS      Ids Op OpAux Cks)
       (Import Ord      : NLORDERED           Ids Op OpAux Cks CESyn Syn)
       (Import CESem    : CESEMANTICS         Ids Op OpAux Cks CESyn     Str)
       (Import Sem      : NLINDEXEDSEMANTICS  Ids Op OpAux Cks CESyn Syn Str Ord CESem)
       (Import Mem      : MEMORIES            Ids Op OpAux Cks CESyn Syn)
       (Import IsD      : ISDEFINED           Ids Op OpAux Cks CESyn Syn                 Mem)
       (Import CEClo    : CECLOCKING          Ids Op OpAux Cks CESyn)
       (Import Clkg     : NLCLOCKING          Ids Op OpAux Cks CESyn Syn     Ord         Mem IsD CEClo)
       (Import CECloSem : CECLOCKINGSEMANTICS Ids Op OpAux Cks CESyn     Str     CESem           CEClo).

  Lemma sem_clocked_var_eq:
    forall G bk H vars x ck islast eq,
      Ordered_nodes G ->
      wc_global G ->
      NoDupMembers vars ->
      sem_equation G bk H eq ->
      wc_equation G vars eq ->
      Is_defined_in_eq (Var x) eq ->
      In (x, (ck, islast)) vars ->
      sem_clocked_var bk H (Var x) ck.
  Proof.
    intros * Ord WCG Nodup Sem WC Def Hin.
    generalize dependent ck; generalize dependent islast; generalize dependent x; generalize dependent vars.
    induction Sem as [?????? Hvar Hexp|
                      ???????????? Hvars ??? Hsem|
                      ??????????? Hexp Hvar| |
                      ?????? Hbk Find Hins Houts Hvars Heqs IH] using sem_equation_mult with
        (P_node := fun f xss yss =>
                     forall n H bk,
                       find_node f G = Some n ->
                       bk = clock_of xss ->
                       sem_vars H (map fst n.(n_in)) xss ->
                       sem_vars H (map fst n.(n_out)) yss ->
                       sem_clocked_vars bk H (map (fun '(x, (_, ck)) => (x, (ck, false))) n.(n_in)) ->
                       sem_clocked_vars bk H (map (fun '(x, (_, ck)) => (x, (ck, false))) n.(n_out)));
      try intros ???????? n;
      try inversion_clear WC as [| |????? node' sub Hfind' Hfai Hfao|]; try inv Def.

    - (* EqDef *)
      match goal with H1:In (?y, _) vars, H2:In (?y, _) vars |- _ =>
        eapply NoDupMembers_det with (2:=H1) in H2; eauto; inv H2 end.
      eapply sem_annotated_instant_sem_clocked_instant in Hexp; eauto.

    - (* EqApp *)
      take (In x0 _) and rename it into Hyys.
      specialize (Hsem (count rs n)); destruct Hsem as (Hsems & IHHsem).

      inversion_clear Hsems as [cks' H' ??? node Hco' Hfind Hvi Hvo Hsck].
      specialize (IHHsem _ _ _ Hfind Hco' Hvi Hvo).
      assert (Hvi' := Hvi).
      rewrite <-map_fst_idsnd in Hvi'.
      pose proof (IHHsem Hsck) as Hscv'. clear IHHsem.
      rewrite Hfind in Hfind'. inv Hfind'.

      assert (forall x y ys,
                 InMembers x (idsnd (node'.(n_in) ++ node'.(n_out))) ->
                 sub x = Some y ->
                 sem_var_instant (H' n) (Var x) ys ->
                 sem_var_instant (H  n) (Var y) ys) as Htranso.
      { setoid_rewrite InMembers_idsnd.
        eapply sem_var_instant_transfer_out_instant; eauto.
        - pose proof node'.(n_nodup) as Hnd.
          rewrite Permutation_swap, <-map_app in Hnd.
          apply fst_NoDupMembers; eauto using NoDup_app_r.
        - apply Forall2_impl_In with (2:=Hfai); intuition.
        - apply Forall2_impl_In with (2:=Hfao); intuition.
        - rewrite mask_transparent; auto.
        - rewrite mask_transparent; auto.
      }

      rewrite <-map_fst_idsnd in Hvo. unfold idsnd in Hvo. rewrite map_map in Hvo.
      specialize (Hvo n); specialize (Hvars n); simpl in *.
      rewrite mask_transparent in Hvo; auto.
      unfold sem_vars_instant in Hvo.
      rewrite Forall2_map_1 in Hvo.
      apply Forall2_swap_args in Hfao.
      apply Forall2_trans_ex with (1:=Hfao) in Hvo.
      apply Forall2_swap_args in Hvars.
      apply Forall2_trans_ex with (1:=Hvo) in Hvars.
      simpl_Forall.
      take (In _ vars) and apply NoDupMembers_det with (2:=Hin) in it; eauto; inv it.
      specialize (Hscv' n); setoid_rewrite Forall_map in Hscv'.
      eapply Forall_forall in Hscv'; eauto. destruct Hscv' as (Hscv'&_).
      destruct G; apply wc_find_node with (1:=WCG) in Hfind as (G'' & G' & HG' & Hfind).
      destruct Hfind as (WCi & WCo & WCv & WCeqs).
      assert (In (i, c) (idsnd (node'.(n_in) ++ node'.(n_out)))) as Hxin'
        by (rewrite idsnd_app, in_app; right;
            apply In_idsnd_exists; eauto).
      apply wc_env_var with (1:=WCo) in Hxin'.
      unfold clock_of in Hscv'; rewrite mask_transparent in Hscv'; auto.
      take (sem_var_instant (var_env (H' n)) _ _) and rename it into Hsvx.
      destruct x1.
      + eapply Hscv', sem_clock_instant_transfer_out_instant in Hsvx; eauto.
        split; intuition; try by_sem_det.
        destruct_conjs. unfold sem_var_instant, var_env in *. congruence.
      + assert (exists c, sem_var_instant (H' n) (Var i) (present c)) as Hsvx' by eauto.
        eapply Hscv', sem_clock_instant_transfer_out_instant in Hsvx'; eauto.
        split; intuition eauto; try by_sem_det.
        destruct_conjs. unfold sem_var_instant, var_env in *. congruence.

    - (* EqFby *)
      match goal with H1:In (?y, _) vars, H2:In (?y, _) vars |- _ =>
        eapply NoDupMembers_det with (2:=H1) in H2; eauto; inv H2 end.
      eapply sem_annotated_instant_sem_clocked_instant' in Hexp; eauto.
      unfold fby, reset.
      destruct (ls n); [reflexivity|].
      cases; split; intros Eq; inv Eq.

    - (* nodes *)
      intros * Find' Hbk' Hins' Houts' Hvars'.
      rewrite Find' in Find; rewrite <-Hbk' in Hbk; inv Find.
      intro m.
      apply Forall_forall; unfold idsnd.
      intros (x, xck) Hxin. simpl_In. split; auto.
      apply in_map with (f:=fst) in Hin as Hin'.
      apply node_output_defined_in_eqs, Is_defined_in_In in Hin' as (eq & Heqin & Hxeq).
      eapply Forall_forall in IH; eauto.
        (* as (Hsem & IH). *)
      destruct G; apply wc_find_node with (1:=WCG) in Find'
        as (G'' & G' & HG & (WCi & WCo & WCv & WCeqs)).
      eapply Forall_forall in WCeqs; eauto.
      assert (NoDupMembers (map (fun '(x, (_, ck)) => (x, (ck, false))) (n_in n ++ n_out n)
                              ++ map (fun '(x, (_, ck, islast)) => (x, (ck, islast))) (n_vars n))) as Hnd.
      { rewrite fst_NoDupMembers. simpl_app.
        erewrite 3 map_map, Permutation.Permutation_app_comm with (l':=map _ (n_vars _)),
            map_ext with (l:=n_in _), map_ext with (l:=n_vars _), map_ext with (l:=n_out _).
        apply n_nodup.
        all:intros; destruct_conjs; auto. }
      subst.
      apply IH with (x:=x) (ck:=c0) (islast:=false) in Hnd;
        eauto using wc_equation_global_app,
                    Ordered_nodes_append, wc_equation_global_cons
          with datatypes.
      2:{ rewrite map_app, 2 in_app_iff. left; right. solve_In. }
      specialize (Hins' m); specialize (Houts' m);
        specialize (Hins m); specialize (Houts m).
      simpl in *.
      unfold sem_vars_instant in Hins, Houts, Hins', Houts'.
      rewrite Forall2_map_1 in Hins', Houts'.
      apply Forall2_app with (2:=Houts') in Hins'.
      rewrite Forall2_map_1 in Hins, Houts.
      assert (Houts2:=Houts).
      apply Forall2_app with (1:=Hins) in Houts2.
      apply Forall2_Forall2 with (1:=Houts) in Houts'.
      apply Forall2_in_left with (2:=Hin) in Houts' as (s & Hsin & Hvs & Hvs').
      destruct s.
      + split; intuition eauto; try by_sem_det.
        * eapply Hnd in Hvs.
          eapply clock_vars_to_sem_clock_instant with (Hn' := var_env (H m)) in H1; eauto; try by_sem_det.
          eapply in_app; eauto.
        * exfalso. destruct_conjs. unfold sem_var_instant, var_env in *. congruence.
        * eapply clock_vars_to_sem_clock_instant; eauto.
          -- eapply in_app; eauto.
          -- apply Hnd; auto.
      + split; intuition eauto; try by_sem_det;
          assert (exists c, sem_var_instant (H m) (Var x) (present c)) as Hvs'' by eauto.
        * eapply clock_vars_to_sem_clock_instant; eauto.
          -- eapply in_app; eauto.
          -- apply Hnd; auto.
        * eapply Hnd in Hvs''.
          eapply clock_vars_to_sem_clock_instant with (Hn' := var_env (H0 m)) in Hvs''; eauto; try by_sem_det.
          eapply in_app; eauto.
        * exfalso. destruct_conjs. unfold sem_var_instant, var_env in *. congruence.
  Qed.

  Lemma sem_clocked_last_eq:
    forall G bk H vars x ck eq,
      NoDupMembers vars ->
      sem_equation G bk H eq ->
      wc_equation G vars eq ->
      Is_defined_in_eq (Last x) eq ->
      In (x, (ck, true)) vars ->
      sem_clocked_var bk H (Last x) ck.
  Proof.
    destruct eq; intros * ND Sem Wc Def InV;
      inversion Sem as [| | |?????????? Var VarCk _ _ Last]; inv Wc; inv Def.
    eapply NoDupMembers_det in InV; eauto; inv InV.
    intros k. specialize (Var k). specialize (VarCk k) as (CkPres&CkAbs). specialize (Last k).
    unfold reset, fby in Last.
    destruct (xs k); (split; [rewrite CkPres|rewrite CkAbs]).
    - split; intros (?&?); exfalso; by_sem_det.
    - split; auto.
    - split; eauto. cases; eauto.
    - split; intros; exfalso; try by_sem_det. cases; by_sem_det.
  Qed.

  Corollary sem_clocked_var_eqs:
    forall G bk H inputs vars eqs,
      Ordered_nodes G ->
      wc_global G ->
      NoDupMembers (inputs ++ vars) ->
      Forall (sem_equation G bk H) eqs ->
      Forall (wc_equation G (inputs ++ vars)) eqs ->
      Permutation.Permutation (vars_defined eqs) (map fst vars) ->
      Permutation.Permutation (lasts_defined eqs) (map fst (filter (fun '(_, (_, islast)) => islast) vars)) ->
      forall x xck islast,
        In (x, (xck, islast)) vars ->
        sem_clocked_var bk H (Var x) xck /\ if islast then sem_clocked_var bk H (Last x) xck else True.
  Proof.
    intros * OG WCG Hndup Hsem Hwc Hdef Hlast * Hin.
    split; [|cases; auto].
    - assert (In x (vars_defined eqs)) as Hxin.
      { rewrite Hdef. solve_In. }
      apply Is_defined_in_vars_defined, Is_defined_in_In in Hxin
          as (eq & Hieq & Hdeq).
      simpl_Forall.
      eapply sem_clocked_var_eq; eauto using in_or_app.
    - assert (In x (lasts_defined eqs)) as Hxin.
      { rewrite Hlast. solve_In. }
      apply Is_last_in_lasts_defined, Exists_exists in Hxin as (eq & Hieq & Hdeq).
      simpl_Forall.
      eapply sem_clocked_last_eq; eauto using in_or_app.
      inv Hdeq. constructor.
  Qed.

End NLCLOCKINGSEMANTICS.

Module NLClockingSemanticsFun
       (Ids      : IDS)
       (Op       : OPERATORS)
       (OpAux    : OPERATORS_AUX       Ids Op)
       (Cks      : CLOCKS              Ids Op OpAux)
       (CESyn    : CESYNTAX            Ids Op OpAux Cks)
       (Syn      : NLSYNTAX            Ids Op OpAux Cks CESyn)
       (Str      : INDEXEDSTREAMS      Ids Op OpAux Cks)
       (Ord      : NLORDERED           Ids Op OpAux Cks CESyn Syn)
       (CESem    : CESEMANTICS         Ids Op OpAux Cks CESyn     Str)
       (Sem      : NLINDEXEDSEMANTICS  Ids Op OpAux Cks CESyn Syn Str Ord CESem)
       (Mem      : MEMORIES            Ids Op OpAux Cks CESyn Syn)
       (IsD      : ISDEFINED           Ids Op OpAux Cks CESyn Syn                 Mem)
       (CEClo    : CECLOCKING          Ids Op OpAux Cks CESyn)
       (Clkg     : NLCLOCKING          Ids Op OpAux Cks CESyn Syn     Ord         Mem IsD CEClo)
       (CECloSem : CECLOCKINGSEMANTICS Ids Op OpAux Cks CESyn     Str     CESem           CEClo)
<: NLCLOCKINGSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem Sem Mem IsD CEClo Clkg CECloSem.
  Include NLCLOCKINGSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem Sem Mem IsD CEClo Clkg CECloSem.
End NLClockingSemanticsFun.
