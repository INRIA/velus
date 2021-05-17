From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import CoreExpr.CESemantics.
From Coq Require Import List.

(** * Link (static) clocking predicates to (dynamic) semantic model *)

(**

These results confirm the correctness of the clocking predicates wrt the
semantics. In particular, they are useful for relating static invariants to
dynamic properties. They hold essentially due to the "additional" clocking
constraints in the NLustre semantic model.

 *)

Module Type CECLOCKINGSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Import Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (Import CESem : CESEMANTICS Ids Op OpAux Cks CESyn     Str)
       (Import CEClo : CECLOCKING  Ids Op OpAux Cks CESyn).

  Section ClockMatchInstant.

    Variables
      (Ω: list (ident * clock))
      (base: bool)
      (R: env)
      (Hcm: sem_clocked_vars_instant base R Ω).

    Lemma clock_match_instant_exp:
      forall le ck,
        wc_exp Ω le ck ->
        forall v,
          sem_exp_instant base R le v ->
          (sem_exp_instant base R le absent
           /\ sem_clock_instant base R ck false)
          \/
          ((exists c, sem_exp_instant base R le (present c))
           /\ sem_clock_instant base R ck true).
    Proof.
      induction le; intros * WCe; inv WCe.
      - intros.
        destruct base; [right|left]; eauto using sem_exp_instant, sem_clock_instant.
      - intros.
        destruct base; [right|left]; eauto using sem_exp_instant, sem_clock_instant.
      - inversion_clear 1.
        eapply Forall_forall in Hcm; eauto.
        destruct v.
        + left; split; eauto using sem_exp_instant.
          apply Hcm; auto.
        + right; split; eauto using sem_exp_instant.
          apply Hcm; eauto.
      - inversion_clear 1; eapply Forall_forall in Hcm; eauto.
        + right; split; eauto using sem_exp_instant.
          econstructor; eauto.
          apply Hcm; eauto.
        + left; split; eauto using sem_exp_instant.
          eapply Son_abs2; eauto.
          apply Hcm; eauto.
        + left; split; eauto using sem_exp_instant.
          econstructor; eauto.
          apply Hcm; auto.
      - inversion_clear 1.
        + right; split; eauto using sem_exp_instant.
          edestruct IHle as [(?&?)|(?&?)]; eauto.
          now assert (present v0 = absent) by sem_det.
        + left; split; eauto using sem_exp_instant.
          edestruct IHle as [(?&?)|((c&?)&?)]; eauto.
          now assert (present c = absent) by sem_det.
      - inversion_clear 1.
        + right; split; eauto using sem_exp_instant.
          edestruct IHle1 as [(?&?)|(?&?)]; eauto.
          now assert (present v1 = absent) by sem_det.
        + left; split; eauto using sem_exp_instant.
          edestruct IHle1 as [(?&?)|((c&?)&?)]; eauto.
          now assert (present c = absent) by sem_det.
    Qed.

    Corollary clock_match_instant_exp_contradiction:
      forall le ck b v,
        wc_exp Ω le ck ->
        sem_exp_instant base R le v ->
        sem_clock_instant base R ck b ->
        (b = true <-> v <> absent).
    Proof.
      intros le ck b v WC Hle Hck.
      eapply clock_match_instant_exp in WC as [(Hle' & Hck')|((v' & Hle') & Hck')];
        eauto.
      - apply sem_clock_instant_det with (1:=Hck) in Hck'.
        apply sem_exp_instant_det with (1:=Hle) in Hle'.
        subst; intuition.
      - apply sem_clock_instant_det with (1:=Hck) in Hck'.
        apply sem_exp_instant_det with (1:=Hle) in Hle'.
        subst; intuition; discriminate.
    Qed.

    Lemma clock_match_instant_cexp:
      forall ce ck,
        wc_cexp Ω ce ck ->
        forall v,
          sem_cexp_instant base R ce v ->
          (sem_cexp_instant base R ce absent
           /\ sem_clock_instant base R ck false)
          \/
          ((exists c, sem_cexp_instant base R ce (present c))
           /\ sem_clock_instant base R ck true).
    Proof.
      induction ce using cexp_ind2.
      - repeat inversion_clear 1.
        + subst.
          take (Forall _ (_ ++ _ :: _)) and apply Forall_app in it as (Hes1 & Hes2');
            inversion_clear Hes2' as [|?? He Hes2].
          take (Forall2 _ _ _) and apply Forall2_app_inv_r in it as (l1 & l2 & Hl1 & Hl2' & E).
          inversion_clear Hl2' as [|???? He' Hl2]; eauto.
          edestruct He as [(Hv & Hc)|((?c & Hv) & Hc)]; eauto.
          * match goal with
            | HA: sem_cexp_instant _ _ _ absent,
                  HP: sem_cexp_instant _ _ _ (present ?cv) |- _ =>
              now assert (present cv = absent) by sem_det
            end.
          * right; split; eauto using sem_cexp_instant. inv Hc; auto.
        + left; split.
          constructor; auto.
          destruct l; try contradiction.
          repeat (take (Forall _ (_::_)) and inv it).
          take (Forall2 _ _ _) and inversion_clear it.
          take (forall ck : clock, wc_cexp _ _ _ -> _) and edestruct it as [(Hv & Hc)|((?c & Hv) & Hc)]; eauto.
          * inv Hc; auto.
            match goal with
            | HA: sem_var_instant _ _ absent,
                  HP: sem_var_instant _ _ (present ?cv) |- _ =>
              now assert (present cv = absent) by sem_det
            end.
          * match goal with
            | HA: sem_cexp_instant _ _ _ absent,
                  HP: sem_cexp_instant _ _ _ (present ?cv) |- _ =>
              now assert (present cv = absent) by sem_det
            end.
      - repeat inversion_clear 1.
        + destruct l as [|oe]; try contradiction.
          take (Forall2 _ _ _) and inv it.
          repeat (take (Forall _ (_::_)) and inv it).
          take (forall ck : clock, wc_cexp _ _ _ -> _)
                 and edestruct it as [(Hv & Hc)|((?c & Hv) & Hc)]; eauto.
          -- match goal with
             | HA: sem_cexp_instant _ _ _ absent,
                   HP: sem_cexp_instant _ _ _ (present ?cv) |- _ =>
               now assert (present cv = absent) by sem_det
             end.
          -- clear Hv.
             right; split; eauto using sem_cexp_instant.
        + left; split.
          constructor; auto.
          destruct l as [|oe]; try contradiction.
          repeat (take (Forall _ (_::_)) and inv it).
          take (forall ck : clock, wc_cexp _ _ _ -> _) and
               edestruct it as [(Hv & Hc)|((?c & Hv) & Hc)]; eauto.
          match goal with
          | HA: sem_cexp_instant _ _ _ absent,
                HP: sem_cexp_instant _ _ _ (present ?cv) |- _ =>
            now assert (present cv = absent) by sem_det
          end.
      - inversion_clear 1 as [| |? ? Hwc].
        inversion_clear 1.
        eapply clock_match_instant_exp in Hwc; eauto.
        destruct Hwc as [(Hv & Hc)|((?c & Hv) & Hc)]; [left|right];
          eauto using sem_cexp_instant.
    Qed.

  End ClockMatchInstant.

  Section ClockMatch.

    Variables
      (Ω: list (ident * clock))
      (bk: stream bool)
      (H: history)
      (Hcm: sem_clocked_vars bk H Ω).

    Lemma clock_match_exp:
      forall le ck,
        wc_exp Ω le ck ->
        forall n v,
          sem_exp_instant (bk n) (H n) le v ->
          (sem_exp_instant (bk n) (H n) le absent
           /\ sem_clock_instant (bk n) (H n) ck false)
          \/
          ((exists c, sem_exp_instant (bk n) (H n) le (present c))
           /\ sem_clock_instant (bk n) (H n) ck true).
    Proof.
      intros; eapply clock_match_instant_exp with (Ω := Ω); eauto.
    Qed.

    Corollary clock_match_exp_contradiction:
      forall le ck b v,
        wc_exp Ω le ck ->
        forall n,
          sem_exp_instant (bk n) (H n) le v ->
          sem_clock_instant (bk n) (H n) ck b ->
          (b = true <-> v <> absent).
    Proof.
      intros.
      eapply clock_match_instant_exp_contradiction with (Ω := Ω); eauto.
    Qed.

    Lemma clock_match_cexp:
      forall ce ck,
        wc_cexp Ω ce ck ->
        forall n v,
          sem_cexp_instant (bk n) (H n) ce v ->
          (sem_cexp_instant (bk n) (H n) ce absent
           /\ sem_clock_instant (bk n) (H n) ck false)
          \/
          ((exists c, sem_cexp_instant (bk n) (H n) ce (present c))
           /\ sem_clock_instant (bk n) (H n) ck true).
    Proof.
      intros; eapply clock_match_instant_cexp with (Ω := Ω); eauto.
    Qed.

  End ClockMatch.

 (* Transfer named streams defined within the body of a node ([R']) out into
     the environment where the node is instantiated ([R]). *)
  Lemma sem_var_instant_transfer_out_instant:
    forall (xin : list (ident * (type * clock)))
      (xout : list (ident * (type * clock)))
      R R' les ys sub base lss yss,
      NoDupMembers (xin ++ xout) ->
      Forall2 (fun xtc le => SameVar (sub (fst xtc)) le) xin les ->
      Forall2 (fun xtc  y => sub (fst xtc) = Some y) xout ys ->
      sem_vars_instant R' (map fst xin) lss ->
      sem_vars_instant R' (map fst xout) yss ->
      sem_exps_instant base R les lss ->
      sem_vars_instant R ys yss ->
      forall x y ys,
        InMembers x (xin ++ xout) ->
        sub x = Some y ->
        sem_var_instant R' x ys ->
        sem_var_instant R y ys.
  Proof.
    intros * Hndup Hsv Hos Hxin Hxout Hles Hys * Hin Hsub Hxv.
    apply InMembers_app in Hin as [Hin|Hout].
    - clear Hxout Hys Hos.
      apply NoDupMembers_app_InMembers with (2:=Hin) in Hndup.
      apply InMembers_In in Hin as ((xty & xck) & Hin).
      unfold sem_exps_instant in Hles.
      unfold sem_vars_instant in Hxin.
      rewrite Forall2_map_1 in Hxin.
      rewrite Forall2_swap_args in Hles.
      apply Forall2_trans_ex with (1:=Hxin) in Hles. clear Hxin.
      rewrite Forall2_swap_args in Hsv.
      apply Forall2_trans_ex with (1:=Hles) in Hsv. clear Hles.
      apply Forall2_same in Hsv.
      eapply Forall_forall in Hsv
        as (le & Hle & (ls & Hlsin & Hxls & Hlels) & Hsveq); eauto.
      simpl in *.
      rewrite Hsub in Hsveq; inv Hsveq.
      inversion_clear Hlels.
      apply sem_var_instant_det with (1:=Hxv) in Hxls.
      now rewrite Hxls in *.
    - clear Hsv Hxin Hles.
      apply InMembers_In in Hout as ((xty & xck) & Hout).
      unfold sem_vars_instant in Hxout, Hys.
      rewrite Forall2_map_1 in Hxout.
      rewrite Forall2_swap_args in Hys.
      apply Forall2_trans_ex with (1:=Hxout) in Hys. clear Hxout.
      rewrite Forall2_swap_args in Hos.
      apply Forall2_trans_ex with (1:=Hys) in Hos. clear Hys.
      apply Forall2_same in Hos.
      eapply Forall_forall in Hos
        as (z & Hz & (v & Hvin & Hv & Hzv) & Hsub'); eauto.
      simpl in *.
      rewrite Hsub in Hsub'; inversion_clear Hsub'.
      apply sem_var_instant_det with (1:=Hxv) in Hv.
      now rewrite Hv in *.
  Qed.

  Corollary sem_var_instant_transfer_out:
    forall (xin : list (ident * (type * clock)))
      (xout : list (ident * (type * clock)))
      H H' les ys sub bk lss yss,
      NoDupMembers (xin ++ xout) ->
      Forall2 (fun xtc le => SameVar (sub (fst xtc)) le) xin les ->
      Forall2 (fun xtc  y => sub (fst xtc) = Some y) xout ys ->
      sem_vars H' (map fst xin) lss ->
      sem_vars H' (map fst xout) yss ->
      sem_exps bk H les lss ->
      sem_vars H ys yss ->
      forall x y ys,
        InMembers x (xin ++ xout) ->
        sub x = Some y ->
        forall n,
          sem_var_instant (H' n) x ys ->
          sem_var_instant (H  n) y ys.
  Proof.
    intros; eapply sem_var_instant_transfer_out_instant; eauto.
  Qed.

  (* Using the transfer of named streams, also transfer clocks from
     the interface. *)
  Lemma sem_clock_instant_transfer_out_instant:
    forall Ω ck sub base base' R R' xck yck v,
      instck ck sub xck = Some yck ->
      sem_clock_instant base R ck base' ->
      wc_clock Ω xck ->
      sem_clock_instant base' R' xck v ->
      (forall x y ys,
          InMembers x Ω ->
          sub x = Some y ->
          sem_var_instant R' x ys ->
          sem_var_instant R y ys) ->
      sem_clock_instant base R yck v.
  Proof.
    intros * Hinst Hcks Hwc Hsem Hxv.
    revert xck ck yck v Hinst Hcks Hwc Hsem.
    induction xck; simpl in *.
    - inversion 1; inversion 3; now subst.
    - intros ck yck v Hinst Hcks Hwc Hsem.
      destruct (instck ck sub xck) eqn:Hi; try discriminate.
      destruct (sub i) eqn:Hsi; try discriminate.
      inv Hinst. inversion_clear Hwc as [|???? Hin].
      apply In_InMembers in Hin.
      inv Hsem; eauto using sem_clock_instant.
  Qed.

  Corollary sem_clock_instant_transfer_out:
    forall Ω ck sub bk bk' (H: history) H' xck yck v n,
      instck ck sub xck = Some yck ->
      sem_clock_instant (bk n) (H n) ck (bk' n) ->
      wc_clock Ω xck ->
      sem_clock_instant (bk' n) (H' n) xck v ->
      (forall x y ys,
          InMembers x Ω ->
          sub x = Some y ->
          sem_var_instant (H' n) x ys ->
          sem_var_instant (H  n) y ys) ->
      sem_clock_instant (bk n) (H n) yck v.
  Proof.
    intros; eapply sem_clock_instant_transfer_out_instant; eauto.
  Qed.

  (* Transfer interface variable values onto interface clocks between
     an external environment ([Hn]) and an internal one ([Hn']). *)
  Lemma clock_vars_to_sem_clock_instant:
    forall Ω bkn Hn Hn' ss,
      Forall2 (fun xtc => sem_var_instant Hn (fst xtc)) Ω ss ->
      Forall2 (fun xtc => sem_var_instant Hn' (fst xtc)) Ω ss ->
      wc_env (idck Ω) ->
      forall x (xty: type) xck v,
        In (x, (xty, xck)) Ω ->
        sem_clock_instant bkn Hn xck v ->
        sem_clock_instant bkn Hn' xck v.
  Proof.
    intros Ω bkn Hn Hn' ss HHn HHn' WCenv x xty xck v Hin Hsi.
    assert (exists xty, In (x, (xty, xck)) Ω) as Hin' by eauto.
    apply In_idck_exists in Hin'.
    apply wc_env_var with (2:=Hin') in WCenv.
    clear Hin Hin' xty.
    apply Forall2_Forall2 with (1:=HHn') in HHn. clear HHn'.
    revert v Hsi. induction xck.
    - inversion_clear 1; eauto using sem_clock_instant.
    - inversion_clear WCenv as [|? ? ? WCx Hin].
      specialize (IHxck WCx).
      apply In_idck_exists in Hin as (xty & Hin).
      apply Forall2_in_left with (2:=Hin) in HHn.
      destruct HHn as (s & Hsin & Hv' & Hv).
      inversion_clear 1.
      + econstructor; eauto.
        assert (s = present (Venum b)) as Hsc by (eapply sem_var_instant_det; eauto).
        now subst.
      + econstructor; eauto.
        assert (s = absent) as Hsc by (eapply sem_var_instant_det; eauto).
        now subst.
      + eapply Son_abs2; eauto.
        assert (s = present (Venum b')) as Hsc by (eapply sem_var_instant_det; eauto).
        now subst.
  Qed.

End CECLOCKINGSEMANTICS.

Module CEClockingSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (CESem : CESEMANTICS Ids Op OpAux Cks CESyn     Str)
       (CEClo : CECLOCKING  Ids Op OpAux Cks CESyn)
<: CECLOCKINGSEMANTICS Ids Op OpAux Cks CESyn Str CESem CEClo.
  Include CECLOCKINGSEMANTICS Ids Op OpAux Cks CESyn Str CESem CEClo.
End CEClockingSemanticsFun.
