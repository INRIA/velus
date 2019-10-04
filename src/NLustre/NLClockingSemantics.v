From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.Stream.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import NLustre.IsFree.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import NLustre.NLSemantics.
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
       (Import OpAux    : OPERATORS_AUX           Op)
       (Import CESyn    : CESYNTAX                Op)
       (Import Syn      : NLSYNTAX            Ids Op       CESyn)
       (Import Str      : STREAM                  Op OpAux)
       (Import Ord      : NLORDERED           Ids Op       CESyn Syn)
       (Import CESem    : CESEMANTICS         Ids Op OpAux CESyn     Str)
       (Import Sem      : NLSEMANTICS         Ids Op OpAux CESyn Syn Str Ord CESem)
       (Import Mem      : MEMORIES            Ids Op       CESyn Syn)
       (Import IsD      : ISDEFINED           Ids Op       CESyn Syn                 Mem)
       (Import CEIsF    : CEISFREE            Ids Op       CESyn)
       (Import IsF      : ISFREE              Ids Op       CESyn Syn CEIsF)
       (Import CEClo    : CECLOCKING          Ids Op       CESyn)
       (Import Clkg     : NLCLOCKING          Ids Op       CESyn Syn     Ord         Mem IsD CEIsF IsF CEClo)
       (Import CECloSem : CECLOCKINGSEMANTICS Ids Op OpAux CESyn     Str     CESem                     CEClo).

  Lemma sem_clocked_var_eq:
    forall G bk H vars x ck eq,
      Ordered_nodes G ->
      wc_global G ->
      NoDupMembers vars ->
      sem_equation G bk H eq ->
      wc_equation G vars eq ->
      Is_defined_in_eq x eq ->
      In (x, ck) vars ->
      sem_clocked_var bk H x ck.
  Proof.
    intros ??????? Ord WCG Nodup Sem WC Def Hin.
    revert dependent ck; revert dependent x; revert dependent vars.
    induction Sem as [?????? Hvar Hexp|
                      ????????? Hvars ? Hsem|
                      ????????????? Hvars ??? Hsem|
                      ???????? Hexp Hvar|
                      ?????? Hbk Find Hins Houts Hvars Heqs IH] using sem_equation_mult with
        (P_node := fun f xss yss =>
                     forall n H bk,
                       find_node f G = Some n ->
                       bk = clock_of xss ->
                       sem_vars H (map fst n.(n_in)) xss ->
                       sem_vars H (map fst n.(n_out)) yss ->
                       sem_clocked_vars bk H (idck n.(n_in)) ->
                       sem_clocked_vars bk H (idck n.(n_out)));
      try intros ??????? n;
      try inversion_clear WC as [|????? node' sub Hfind' Hfai Hfao|].

    - (* EqDef *)
      inv Def.
      match goal with H1:In (?x, _) vars, H2:In (?x, _) vars |- _ =>
        apply NoDupMembers_det with (2:=H1) in H2; eauto; subst end.
      specialize (Hvar n); specialize (Hexp n).
      unfold sem_clocked_var_instant.
      inv Hexp;
        match goal with H:_ = xs n |- _ => rewrite <-H in * end;
        intuition; eauto; by_sem_det.

    - (* EqApp *)
      inversion_clear Def as [|? ? ? ? ? Hyys|].
      inversion_clear Hsem as [cks' H' ??? node Hco' Hfind Hvi Hvo Hsck].
      specialize (IHSem _ _ _ Hfind Hco' Hvi Hvo Hsck).
      assert (Hvi' := Hvi).
      rewrite <-map_fst_idck in Hvi.
      rewrite Hfind in Hfind'; inv Hfind'.
      assert (forall x y ys,
                 InMembers x (idck (node'.(n_in) ++ node'.(n_out))) ->
                 sub x = Some y ->
                 forall n,
                   sem_var_instant (H' n) x ys ->
                   sem_var_instant (H n) y ys) as Htranso.
      { setoid_rewrite InMembers_idck.
        eapply sem_var_instant_transfer_out; eauto.
        - pose proof node'.(n_nodup) as Hnd.
          rewrite <-Permutation_app_assoc,
                  (Permutation.Permutation_app_comm node'.(n_in)),
                  Permutation_app_assoc in Hnd.
          now apply NoDupMembers_app_r in Hnd.
        - apply Forall2_impl_In with (2:=Hfai); intuition.
        - apply Forall2_impl_In with (2:=Hfao); intuition.
      }

      rewrite <-map_fst_idck in Hvo; unfold idck in Hvo; rewrite map_map in Hvo.
      specialize (Hvo n); specialize (Hvars n); simpl in *.
      unfold sem_vars_instant in Hvo.
      rewrite Forall2_map_1 in Hvo.
      apply Forall2_swap_args in Hfao.
      apply Forall2_trans_ex with (1:=Hfao) in Hvo.
      apply Forall2_swap_args in Hvars.
      apply Forall2_trans_ex with (1:=Hvo) in Hvars.
      apply Forall2_same in Hvars.
      eapply Forall_forall in Hvars
        as (s & Hins & ((x', (xty, xck)) & Hxin & ((Hoeq & yck' & Hin' & Hinst) & Hsvx)) & Hsvy);
        eauto; simpl in *.
      apply NoDupMembers_det with (2:=Hin) in Hin'; eauto; subst yck'.
      unfold idck in *. specialize (IHSem n); setoid_rewrite Forall_map in IHSem.
      eapply Forall_forall in IHSem; eauto; simpl in IHSem.
      apply wc_find_node with (1:=WCG) in Hfind as (G'' & G' & HG' & Hfind).
      destruct Hfind as (WCi & WCo & WCv & WCeqs).
      assert (In (x', xck) (idck (node'.(n_in) ++ node'.(n_out)))) as Hxin'
        by (rewrite idck_app, in_app; right;
            apply In_idck_exists; eauto).
      apply wc_env_var with (1:=WCo) in Hxin'.
      destruct s.
      + split; intuition; eauto; try by_sem_det;
          eapply IHSem, sem_clock_instant_transfer_out in Hsvx; eauto; by_sem_det.
      + split; intuition; eauto; try by_sem_det.
        * eapply sem_clock_instant_transfer_out; eauto; eapply IHSem; eauto.
        * assert (exists c, sem_var_instant (H' n) x' (present c)) as Hsvx' by eauto.
          eapply IHSem, sem_clock_instant_transfer_out in Hsvx'; eauto; by_sem_det.

    - (* EqReset *)
      inversion_clear Def as [|????? Hyys|].
      specialize (Hsem (count rs n)); destruct Hsem as (Hsems & IHHsem).

      inversion_clear Hsems as [cks' H' ??? node Hco' Hfind Hvi Hvo Hsck].
      specialize (IHHsem _ _ _ Hfind Hco' Hvi Hvo).
      assert (Hvi' := Hvi).
      rewrite <-map_fst_idck in Hvi'.
      pose proof (IHHsem Hsck) as Hscv'. clear IHHsem.
      rewrite Hfind in Hfind'. inv Hfind'.

      assert (forall x y ys,
                 InMembers x (idck (node'.(n_in) ++ node'.(n_out))) ->
                 sub x = Some y ->
                 sem_var_instant (H' n) x ys ->
                 sem_var_instant (H  n) y ys) as Htranso.
      { setoid_rewrite InMembers_idck.
        eapply sem_var_instant_transfer_out_instant; eauto.
        - pose proof node'.(n_nodup) as Hnd.
          rewrite <-Permutation_app_assoc,
                  (Permutation.Permutation_app_comm node'.(n_in)),
                  Permutation_app_assoc in Hnd.
          now apply NoDupMembers_app_r in Hnd.
        - apply Forall2_impl_In with (2:=Hfai); intuition.
        - apply Forall2_impl_In with (2:=Hfao); intuition.
        - rewrite mask_transparent; auto.
        - rewrite mask_transparent; auto.
      }

      rewrite <-map_fst_idck in Hvo. unfold idck in Hvo. rewrite map_map in Hvo.
      specialize (Hvo n); specialize (Hvars n); simpl in *.
      rewrite mask_transparent in Hvo; auto.
      unfold sem_vars_instant in Hvo.
      rewrite Forall2_map_1 in Hvo.
      apply Forall2_swap_args in Hfao.
      apply Forall2_trans_ex with (1:=Hfao) in Hvo.
      apply Forall2_swap_args in Hvars.
      apply Forall2_trans_ex with (1:=Hvo) in Hvars.
      apply Forall2_same in Hvars.
      eapply Forall_forall in Hvars
        as (s & Hins & ((x', (xty, xck)) & Hxin & ((Hoeq & yck' & Hin' & Hinst) & Hsvx)) & Hsvy);
        eauto; simpl in *.
      apply NoDupMembers_det with (2:=Hin) in Hin'; eauto; subst yck'.
      specialize (Hscv' n); setoid_rewrite Forall_map in Hscv'.
      eapply Forall_forall in Hscv'; eauto; simpl in Hscv'.
      apply wc_find_node with (1:=WCG) in Hfind as (G'' & G' & HG' & Hfind).
      destruct Hfind as (WCi & WCo & WCv & WCeqs).
      assert (In (x', xck) (idck (node'.(n_in) ++ node'.(n_out)))) as Hxin'
        by (rewrite idck_app, in_app; right;
            apply In_idck_exists; eauto).
      apply wc_env_var with (1:=WCo) in Hxin'.
      unfold clock_of in Hscv'; rewrite mask_transparent in Hscv'; auto.
      destruct s.
      + split; intuition; eauto; try by_sem_det.
        * eapply Hscv', sem_clock_instant_transfer_out_instant in Hsvx; eauto; try by_sem_det.
        * eapply Hscv', sem_clock_instant_transfer_out_instant in Hsvx; eauto.
      + split; intuition; eauto; try by_sem_det.
        * eapply sem_clock_instant_transfer_out; eauto; eapply Hscv'; eauto.
        * assert (exists c, sem_var_instant (H' n) x' (present c)) as Hsvx' by eauto.
          eapply Hscv', sem_clock_instant_transfer_out_instant in Hsvx'; eauto; by_sem_det.

    - (* EqFby *)
      inv Def.
      match goal with H1:In (?y, _) vars, H2:In (?y, _) vars |- _ =>
        eapply NoDupMembers_det with (2:=H1) in H2; eauto; subst end.
      specialize (Hexp n); specialize (Hvar n).
      unfold fby in Hvar.
      unfold sem_clocked_var_instant.
      inv Hexp; match goal with H:_ = ls n |- _ => rewrite <-H in * end;
        intuition; eauto; by_sem_det.

    - (* nodes *)
      intros * Find' Hbk' Hins' Houts' Hvars'.
      rewrite Find' in Find; rewrite <-Hbk' in Hbk; inv Find.
      intro m.
      apply Forall_forall; unfold idck.
      intros (x, xck) Hxin.
      apply In_idck_exists in Hxin as (xty & Hxin). assert (Hxin' := Hxin).
      apply in_map with (f:=fst), node_output_defined_in_eqs in Hxin.
      apply Is_defined_in_In in Hxin as (eq & Heqin & Hxeq).
      eapply Forall_forall in IH; eauto.
        (* as (Hsem & IH). *)
      apply wc_find_node with (1:=WCG) in Find'
        as (G'' & G' & HG & (WCi & WCo & WCv & WCeqs)).
      eapply Forall_forall in WCeqs; eauto.
      assert (NoDupMembers (idck (n.(n_in) ++ n.(n_vars) ++ n.(n_out))))
        as Hnd by apply NoDupMembers_idck, n_nodup.
      subst.
      apply IH with (x:=x) (ck:=xck) in Hnd;
        try (apply In_idck_exists; exists xty);
        eauto using wc_equation_global_app,
                    Ordered_nodes_append, wc_equation_global_cons
          with datatypes.
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
      apply Forall2_in_left with (2:=Hxin') in Houts' as (s & Hsin & Hvs & Hvs').
      destruct s.
      + split; intuition; eauto; try by_sem_det.
        * eapply Hnd in Hvs.
          eapply clock_vars_to_sem_clock_instant with (Hn' := H m) in H1; eauto; try by_sem_det.
          eapply in_app; eauto.
        * eapply clock_vars_to_sem_clock_instant; eauto.
          -- eapply in_app; eauto.
          -- apply Hnd; auto.
      + split; intuition; eauto; try by_sem_det;
          assert (exists c, sem_var_instant (H m) x (present c)) as Hvs'' by eauto.
        * eapply clock_vars_to_sem_clock_instant; eauto.
          -- eapply in_app; eauto.
          -- apply Hnd; auto.
        * eapply Hnd in Hvs''.
          eapply clock_vars_to_sem_clock_instant with (Hn' := H0 m) in Hvs''; eauto; try by_sem_det.
          eapply in_app; eauto.
  Qed.

  Corollary sem_clocked_var_eqs:
    forall G bk H inputs vars eqs,
      Ordered_nodes G ->
      wc_global G ->
      NoDupMembers (inputs ++ vars) ->
      Forall (sem_equation G bk H) eqs ->
      Forall (wc_equation G (inputs ++ vars)) eqs ->
      Permutation.Permutation (vars_defined eqs) (map fst vars) ->
      forall x xck,
        In (x, xck) vars ->
        sem_clocked_var bk H x xck.
  Proof.
    intros G bk H inputs vars eqs OG WCG Hndup Hsem Hwc Hdef x xck Hin.
    assert (In x (vars_defined eqs)) as Hxin
        by (now rewrite Hdef; apply in_map with (f:=fst) in Hin).
    apply Is_defined_in_vars_defined, Is_defined_in_In in Hxin
      as (eq & Hieq & Hdeq).
    eapply Forall_forall in Hsem; eauto.
    eapply Forall_forall in Hwc; eauto.
    eapply sem_clocked_var_eq; eauto.
    rewrite in_app; auto.
  Qed.

End NLCLOCKINGSEMANTICS.

Module NLClockingSemanticsFun
       (Import Ids      : IDS)
       (Import Op       : OPERATORS)
       (Import OpAux    : OPERATORS_AUX           Op)
       (Import CESyn    : CESYNTAX                Op)
       (Import Syn      : NLSYNTAX            Ids Op       CESyn)
       (Import Str      : STREAM                  Op OpAux)
       (Import Ord      : NLORDERED           Ids Op       CESyn Syn)
       (Import CESem    : CESEMANTICS         Ids Op OpAux CESyn     Str)
       (Import Sem      : NLSEMANTICS         Ids Op OpAux CESyn Syn Str Ord CESem)
       (Import Mem      : MEMORIES            Ids Op       CESyn Syn)
       (Import IsD      : ISDEFINED           Ids Op       CESyn Syn                 Mem)
       (Import CEIsF    : CEISFREE            Ids Op       CESyn)
       (Import IsF      : ISFREE              Ids Op       CESyn Syn CEIsF)
       (Import CEClo    : CECLOCKING          Ids Op       CESyn)
       (Import Clkg     : NLCLOCKING          Ids Op       CESyn Syn     Ord         Mem IsD CEIsF IsF CEClo)
       (Import CECloSem : CECLOCKINGSEMANTICS Ids Op OpAux CESyn     Str     CESem                     CEClo)
<: NLCLOCKINGSEMANTICS Ids Op OpAux CESyn Syn Str Ord CESem Sem Mem IsD CEIsF IsF CEClo Clkg CECloSem.
  Include NLCLOCKINGSEMANTICS Ids Op OpAux CESyn Syn Str Ord CESem Sem Mem IsD CEIsF IsF CEClo Clkg CECloSem.
End NLClockingSemanticsFun.
