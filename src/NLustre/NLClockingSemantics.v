Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.CoreExpr.Stream.
Require Import Velus.NLustre.NLOrdered.
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.CoreExpr.CEIsFree.
Require Import Velus.NLustre.IsFree.
Require Import Velus.NLustre.Memories.
Require Import Velus.NLustre.IsDefined.
Require Import Velus.CoreExpr.CEClocking.
Require Import Velus.NLustre.NLClocking.
Require Import Velus.CoreExpr.CESemantics.
Require Import Velus.NLustre.NLSemantics.
Require Import Velus.CoreExpr.CEClockingSemantics.
Require Import List.

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

  Lemma clock_match_node_eqs_reset:
    forall G,
      Ordered_nodes G ->
      wc_global G ->
      (forall f xss yss,
          sem_node G f xss yss ->
          forall bk H n,
            find_node f G = Some n ->
            bk = clock_of xss ->
            sem_vars H (map fst n.(n_in)) xss ->
            sem_vars H (map fst n.(n_out)) yss ->
            Forall (clock_match bk H) (idck n.(n_in)) ->
            Forall (clock_match bk H) (idck n.(n_out)))
      /\
      (forall bk H eq,
          sem_equation G bk H eq ->
          forall iface x ck,
            NoDupMembers iface ->
            wc_equation G iface eq ->
            Is_defined_in_eq x eq ->
            In (x, ck) iface ->
            clock_match bk H (x, ck))
      /\
      (forall f rs xss yss,
          sem_reset G f rs xss yss ->
          forall k bk H node,
            find_node f G = Some node ->
            bk = clock_of (mask (all_absent (xss 0)) k rs xss) ->
            sem_vars H (map fst node.(n_in)) (mask (all_absent (xss 0)) k rs xss) ->
            sem_vars H (map fst node.(n_out)) (mask (all_absent (yss 0)) k rs yss) ->
            Forall (clock_match bk H) (idck node.(n_in)) ->
            Forall (clock_match bk H) (idck node.(n_out))).
  Proof.
    intros * Hord WCG; apply sem_node_equation_reset_ind;
      [intros ?????? Hvar Hexp|
       intros ???????? Hexps Hvars Hck Hsem|
       intros ??????????? Hexps Hvars Hck ?? Hsem|
       intros ???????? Hexp Hvar Hfby|
       intros ???? IH|
       intros ?????? Hck Hf Hin Hout ?? IH].

    - (* EqDef *)
      intros iface y yck Hnd Hwc Hdef Hin n.
      inv Hdef. inv Hwc.
      match goal with H1:In (x, _) iface, H2:In (x, _) iface |- _ =>
        apply NoDupMembers_det with (1:=Hnd) (2:=H1) in H2; subst end.
      specialize (Hvar n). specialize (Hexp n).
      unfold clock_match_instant.
      inv Hexp; match goal with H:_ = xs n |- _ => rewrite <-H in * end; eauto.

    - (* EqApp *)
      intros IHHsem iface z zck Hndup Hwc Hdef Hiface.
      inversion_clear Hdef as [|? ? ? ? ? Hyys|].
      inversion_clear Hsem as [cks' H' ??? node Hco' Hfind Hvi Hvo].
      specialize (IHHsem _ _ _ Hfind Hco' Hvi Hvo).
      assert (Hvi' := Hvi).
      rewrite <-map_fst_idck in Hvi'.
      eapply sem_clocked_vars_clock_match in Hvi'; eauto.
      pose proof (IHHsem Hvi') as Hscv'. clear IHHsem.
      inversion_clear Hwc
        as [|????? node' Hfind' (isub & osub & Hfai & Hfao & Hfno)|].
      rewrite Hfind in Hfind'. inv Hfind'.

      assert (forall x y ys,
                 InMembers x (node'.(n_in) ++ node'.(n_out)) ->
                 orelse isub osub x = Some y ->
                 forall n,
                   sem_var_instant (restr_hist H' n) x ys ->
                   sem_var_instant (restr_hist H  n) y ys) as Htranso.
      { eapply sem_var_instant_transfer_out; eauto.
        - pose proof node'.(n_nodup) as Hnd.
          rewrite <-Permutation_app_assoc,
                  (Permutation.Permutation_app_comm node'.(n_in)),
                  Permutation_app_assoc in Hnd.
          now apply NoDupMembers_app_r in Hnd.
        - apply Forall2_impl_In with (2:=Hfai). intuition.
        - apply Forall2_impl_In with (2:=Hfao). intuition.
      }

      rewrite <-map_fst_idck in Hvo. unfold idck in Hvo. rewrite map_map in Hvo.
      intro n; specialize (Hvo n); specialize (Hvars n); simpl in *.
      unfold sem_vars_instant in Hvo.
      rewrite Forall2_map_1 in Hvo.
      apply Forall2_swap_args in Hfao.
      apply Forall2_trans_ex with (1:=Hfao) in Hvo.
      apply Forall2_swap_args in Hvars.
      apply Forall2_trans_ex with (1:=Hvo) in Hvars.
      apply Forall2_same in Hvars.
      eapply Forall_forall in Hvars
        as (s & Hin & ((x', (xty, xck)) & Hxin &
                       (Hoeq & yck' & Hiface' & Hinst) & Hsvx) & Hsvy); eauto.
      unfold dck in Hinst. simpl in *.
      apply NoDupMembers_det with (1:=Hndup) (2:=Hiface) in Hiface'.
      rewrite <-Hiface' in *.
      unfold idck in *. rewrite Forall_map in Hscv'.
      eapply Forall_forall in Hscv'; eauto; simpl in Hscv'.
      apply wc_find_node with (1:=WCG) in Hfind as (G'' & G' & HG' & Hfind).
      destruct Hfind as (WCi & WCo & WCv & WCeqs).
      assert (In (x', xck) (idck (node'.(n_in) ++ node'.(n_out)))) as Hxin'
        by (rewrite idck_app, in_app; right;
            apply In_idck_exists; eauto).
      apply wc_env_var with (1:=WCo) in Hxin'.
      destruct (Hscv' n) as [(Hv & Hc)|((c & Hv) & Hc)].
      + left; split.
        * apply sem_var_instant_det with (1:=Hsvx) in Hv. subst; auto.
        * eapply sem_clock_instant_transfer_out
            with (vars := idck (node'.(n_in) ++ node'.(n_out))); eauto.
          now setoid_rewrite InMembers_idck; eauto.
      + right; split.
        * exists c; apply sem_var_instant_det with (1:=Hsvx) in Hv. now subst.
        * eapply sem_clock_instant_transfer_out
            with (vars := idck (node'.(n_in) ++ node'.(n_out))); eauto.
          now setoid_rewrite InMembers_idck; eauto.

    - (* EqReset *)
      intros IHHsem iface z zck Hndup Hwc Hdef Hiface n.
      inversion_clear Hdef as [|? ? ? ? ? Hyys|].
      inversion_clear Hsem as [???? Hsems].
      specialize (Hsems (count rs n)).

      inversion_clear Hsems as [cks' H' ??? node Hco' Hfind Hvi Hvo].
      specialize (IHHsem _ _ _ _ Hfind Hco' Hvi Hvo).
      assert (Hvi' := Hvi).
      rewrite <-map_fst_idck in Hvi'.
      eapply sem_clocked_vars_clock_match in Hvi'; eauto.
      pose proof (IHHsem Hvi') as Hscv'. clear IHHsem.
      inversion_clear Hwc
        as [|????? node' Hfind' (isub & osub & Hfai & Hfao & Hfno)|].
      rewrite Hfind in Hfind'. inv Hfind'.

      assert (forall x y ys,
                 InMembers x (node'.(n_in) ++ node'.(n_out)) ->
                 orelse isub osub x = Some y ->
                 sem_var_instant (restr_hist H' n) x ys ->
                 sem_var_instant (restr_hist H  n) y ys) as Htranso.
      { eapply sem_var_instant_transfer_out'; eauto.
        - pose proof node'.(n_nodup) as Hnd.
          rewrite <-Permutation_app_assoc,
                  (Permutation.Permutation_app_comm node'.(n_in)),
                  Permutation_app_assoc in Hnd.
          now apply NoDupMembers_app_r in Hnd.
        - apply Forall2_impl_In with (2:=Hfai). intuition.
        - apply Forall2_impl_In with (2:=Hfao). intuition.
        - instantiate (1 := bk).
          rewrite mask_transparent; auto.
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
        as (s & Hin & ((x', (xty, xck)) & Hxin &
                       (Hoeq & yck' & Hiface' & Hinst) & Hsvx) & Hsvy); eauto.
      unfold dck in Hinst. simpl in *.
      apply NoDupMembers_det with (1:=Hndup) (2:=Hiface) in Hiface'.
      rewrite <-Hiface' in *.
      unfold idck in *. rewrite Forall_map in Hscv'.
      eapply Forall_forall in Hscv'; eauto; simpl in Hscv'.
      apply wc_find_node with (1:=WCG) in Hfind as (G'' & G' & HG' & Hfind).
      destruct Hfind as (WCi & WCo & WCv & WCeqs).
      assert (In (x', xck) (idck (node'.(n_in) ++ node'.(n_out)))) as Hxin'
        by (rewrite idck_app, in_app; right;
            apply In_idck_exists; eauto).
      apply wc_env_var with (1:=WCo) in Hxin'.
      destruct (Hscv' n) as [(Hv & Hc)|((c & Hv) & Hc)].
      + left; split.
        * apply sem_var_instant_det with (1:=Hsvx) in Hv. now subst.
        *{ eapply sem_clock_instant_transfer_out
             with (vars := idck (node'.(n_in) ++ node'.(n_out))); eauto.
           - unfold clock_of in Hc; rewrite mask_transparent in Hc; eauto.
           - now setoid_rewrite InMembers_idck; eauto.
         }
      + right; split.
        * exists c; apply sem_var_instant_det with (1:=Hsvx) in Hv. now subst.
        *{ eapply sem_clock_instant_transfer_out
             with (vars := idck (node'.(n_in) ++ node'.(n_out))); eauto.
           - unfold clock_of in Hc; rewrite mask_transparent in Hc; eauto.
           - now setoid_rewrite InMembers_idck; eauto.
       }

    - (* EqFby *)
      intros iface z zck Hnd Hwc Hdef Hin n.
      inv Hdef; inv Hwc.
      match goal with H1:In (?y, _) iface, H2:In (?y, _) iface |- _ =>
        apply NoDupMembers_det with (1:=Hnd) (2:=H1) in H2; subst end.
      specialize (Hexp n); specialize (Hvar n); specialize (Hfby n); rewrite Hfby in *.
      unfold fby in Hvar.
      unfold clock_match_instant.
      inv Hexp; match goal with H:_ = ls n |- _ => rewrite <-H in * end; eauto.

    - (* reset *)
      intro k; destruct (IH k); auto.

    - (* nodes *)
      intros bk' H' n' Hf' Hck' Hin' Hout' Hcm'.
      rewrite Hf in Hf'. inv Hf'.
      apply Forall_forall; unfold idck.
      intros (x, xck) Hxin.
      apply In_idck_exists in Hxin as (xty & Hxin). assert (Hxin' := Hxin).
      apply in_map with (f:=fst), node_output_defined_in_eqs in Hxin.
      apply Is_defined_in_In in Hxin as (eq & Heqin & Hxeq).
      eapply Forall_forall in IH; eauto.
        (* as (Hsem & IH). *)
      apply wc_find_node with (1:=WCG) in Hf
        as (G'' & G' & HG & (WCi & WCo & WCv & WCeqs)).
      eapply Forall_forall in WCeqs; eauto.
      assert (NoDupMembers (idck (n'.(n_in) ++ n'.(n_vars) ++ n'.(n_out))))
        as Hnd by apply NoDupMembers_idck, n_nodup.
      subst.
      apply IH with (x:=x) (ck:=xck) in Hnd;
        try (apply In_idck_exists; exists xty);
        eauto using wc_equation_global_app,
                    Ordered_nodes_append, wc_equation_global_cons
              with datatypes.
      intro n.
      specialize (Hin' n); specialize (Hout' n);
        specialize (Hin n); specialize (Hout n).
      simpl in *.
      unfold sem_vars_instant in Hin, Hout, Hin', Hout'.
      rewrite Forall2_map_1 in Hin', Hout'.
      apply Forall2_app with (2:=Hout') in Hin'.
      rewrite Forall2_map_1 in Hin, Hout.
      assert (Hout2:=Hout).
      apply Forall2_app with (1:=Hin) in Hout2.
      apply Forall2_Forall2 with (1:=Hout) in Hout'.
      apply Forall2_in_left with (2:=Hxin') in Hout' as (s & Hsin & Hvs & Hvs').
      destruct (Hnd n) as [(Hv & Hc)|((c & Hv) & Hc)].
      + left. simpl in *. split.
        * apply sem_var_instant_det with (1:=Hvs) in Hv. now subst.
        * eapply clock_vars_to_sem_clock_instant
          with (1:=Hout2) (2:=Hin') in WCo; eauto.
          eapply in_app; eauto.
      + right. simpl in *. split.
        * exists c; apply sem_var_instant_det with (1:=Hvs) in Hv. now subst.
        * eapply clock_vars_to_sem_clock_instant
          with (1:=Hout2) (2:=Hin') in WCo; eauto.
          eapply in_app; eauto.
  Qed.


  (* When a node's inputs match their clocks, then so do its outputs.
     This is a consequence (by induction throughout the node hierarchy) of
     the constraints relating streams to their clocks for each case of
     [sem_equation]. *)
  Corollary clock_match_node:
    forall G f xss yss bk H n,
      Ordered_nodes G ->
      wc_global G ->
      sem_node G f xss yss ->
      find_node f G = Some n ->
      bk = clock_of xss ->
      sem_vars H (map fst n.(n_in)) xss ->
      sem_vars H (map fst n.(n_out)) yss ->
      Forall (clock_match bk H) (idck n.(n_in)) ->
      Forall (clock_match bk H) (idck n.(n_out)).
  Proof.
    intros ??????? Ord WCG; intros.
    eapply (proj1 (clock_match_node_eqs_reset G Ord WCG)); eauto.
  Qed.

  (* A "version" of [clock_match_node] for "within" a node. *)
  Corollary clock_match_eq:
    forall G bk H iface x ck eq,
      Ordered_nodes G ->
      wc_global G ->
      NoDupMembers iface ->
      sem_equation G bk H eq ->
      wc_equation G iface eq ->
      Is_defined_in_eq x eq ->
      In (x, ck) iface ->
      clock_match bk H (x, ck).
  Proof.
    intros ??????? Ord WCG; intros.
    eapply (proj1 (proj2 (clock_match_node_eqs_reset G Ord WCG))); eauto.
  Qed.

  Corollary clock_match_eqs:
    forall G bk H inputs vars eqs,
      Ordered_nodes G ->
      wc_global G ->
      NoDupMembers (inputs ++ vars) ->
      Forall (sem_equation G bk H) eqs ->
      Forall (wc_equation G (inputs ++ vars)) eqs ->
      Permutation.Permutation (vars_defined eqs) (map fst vars) ->
      forall x xck,
        In (x, xck) vars ->
        clock_match bk H (x, xck).
  Proof.
    intros G bk H inputs vars eqs OG WCG Hndup Hsem Hwc Hdef x xck Hin.
    assert (In x (vars_defined eqs)) as Hxin
        by (now rewrite Hdef; apply in_map with (f:=fst) in Hin).
    apply Is_defined_in_vars_defined, Is_defined_in_In in Hxin
      as (eq & Hieq & Hdeq).
    eapply Forall_forall in Hsem; eauto.
    eapply Forall_forall in Hwc; eauto.
    eapply clock_match_eq; eauto.
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
