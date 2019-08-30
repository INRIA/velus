From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.Stream.
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
       (Import OpAux : OPERATORS_AUX   Op)
       (Import CESyn : CESYNTAX        Op)
       (Import Str   : STREAM          Op OpAux)
       (Import CESem : CESEMANTICS Ids Op OpAux CESyn     Str)
       (Import CEClo : CECLOCKING  Ids Op       CESyn).

  Section ClockMatchInstant.

    Variables
      (vars: list (ident * clock))
      (base: bool)
      (R: env)
      (Hcm: sem_clocked_vars_instant base R vars).

    Lemma clock_match_instant_exp:
      forall le ck,
        wc_exp vars le ck ->
        forall v,
          sem_exp_instant base R le v ->
          (sem_exp_instant base R le absent
           /\ sem_clock_instant base R ck false)
          \/
          ((exists c, sem_exp_instant base R le (present c))
           /\ sem_clock_instant base R ck true).
    Proof.
      induction le; inversion_clear 1.
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
          now assert (present c = absent) by sem_det.
        + left; split; eauto using sem_exp_instant.
          edestruct IHle as [(?&?)|((c&?)&?)]; eauto.
          now assert (present c = absent) by sem_det.
      - inversion_clear 1.
        + right; split; eauto using sem_exp_instant.
          edestruct IHle1 as [(?&?)|(?&?)]; eauto.
          now assert (present c1 = absent) by sem_det.
        + left; split; eauto using sem_exp_instant.
          edestruct IHle1 as [(?&?)|((c&?)&?)]; eauto.
          now assert (present c = absent) by sem_det.
    Qed.

    Corollary clock_match_instant_exp_contradiction:
      forall le ck b v,
        wc_exp vars le ck ->
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
        wc_cexp vars ce ck ->
        forall v,
          sem_cexp_instant base R ce v ->
          (sem_cexp_instant base R ce absent
           /\ sem_clock_instant base R ck false)
          \/
          ((exists c, sem_cexp_instant base R ce (present c))
           /\ sem_clock_instant base R ck true).
    Proof.
      induction ce.
      - repeat inversion_clear 1.
        + repeat match goal with
                 | WC: wc_cexp _ _ _, SL: sem_cexp_instant _ _ _ _ |- _ =>
                   destruct (IHce1 _ WC _ SL) as [(Hv & Hc)|((?c & Hv) & Hc)]
                 | HA: sem_cexp_instant _ _ _ absent,
                   HP: sem_cexp_instant _ _ _ (present ?cv) |- _ =>
                   now assert (present cv = absent) by sem_det
                 end.
          right; split; eauto using sem_cexp_instant. inv Hc; auto.
        + repeat match goal with
                 | WC: wc_cexp _ _ _, SL: sem_cexp_instant _ _ _ _ |- _ =>
                   destruct (IHce2 _ WC _ SL) as [(Hv & Hc)|((?c & Hv) & Hc)]
                 | HA: sem_cexp_instant _ _ _ absent,
                   HP: sem_cexp_instant _ _ _ (present ?cv) |- _ =>
                   now assert (present cv = absent) by sem_det
                 end.
          right; split; eauto using sem_cexp_instant. inv Hc; auto.
        + repeat match goal with
                 | WC: wc_cexp _ _ _, SL: sem_cexp_instant _ _ _ _ |- _ =>
                   destruct (IHce1 _ WC _ SL) as [(Hv & Hc)|((?c & Hv) & Hc)]
                 | HA: sem_cexp_instant _ _ _ absent,
                   HP: sem_cexp_instant _ _ _ (present ?cv) |- _ =>
                   now assert (present cv = absent) by sem_det
                 end.
          left; split; eauto using sem_cexp_instant.
          inv Hc; auto. now assert (present c = absent) by sem_det.
      - repeat inversion_clear 1; [right|left];
          repeat match goal with
                 | WC: wc_cexp _ _ _, SL: sem_cexp_instant _ _ _ _ |- _ =>
                   destruct (IHce1 _ WC _ SL) as [(Hv1 & Hc1)|((?c & Hv1) & Hc1)]
                 | WC: wc_cexp _ _ _, SL: sem_cexp_instant _ _ _ _ |- _ =>
                   destruct (IHce2 _ WC _ SL) as [(Hv2 & Hc2)|((?c & Hv2) & Hc2)]
                 | HA: sem_cexp_instant _ _ _ absent,
                   HP: sem_cexp_instant _ _ _ (present ?cv) |- _ =>
                   now assert (present cv = absent) by sem_det
                 | Hc: sem_exp_instant _ _ _ (present ?c),
                   Ht: sem_cexp_instant _ _ _ (present ?ct),
                   Hf: sem_cexp_instant _ _ _ (present ?cf),
                   Hv: val_to_bool ?c = Some ?b |- _ =>
                   apply (Site_eq _ _ _ _ _ _ _ _ _ Hc Ht Hf) in Hv;
                     destruct b
                 end; eauto using sem_cexp_instant.
      - inversion_clear 1 as [| |? ? Hwc].
        inversion_clear 1.
        eapply clock_match_instant_exp in Hwc; eauto.
        destruct Hwc as [(Hv & Hc)|((?c & Hv) & Hc)]; [left|right];
          eauto using sem_cexp_instant.
    Qed.

  End ClockMatchInstant.

  Section ClockMatch.

    Variables
      (vars: list (ident * clock))
      (bk: stream bool)
      (H: history)
      (Hcm: sem_clocked_vars bk H vars).

    Lemma clock_match_exp:
      forall le ck,
        wc_exp vars le ck ->
        forall n v,
          sem_exp_instant (bk n) (H n) le v ->
          (sem_exp_instant (bk n) (H n) le absent
           /\ sem_clock_instant (bk n) (H n) ck false)
          \/
          ((exists c, sem_exp_instant (bk n) (H n) le (present c))
           /\ sem_clock_instant (bk n) (H n) ck true).
    Proof.
      intros; eapply clock_match_instant_exp with (vars := vars); eauto.
    Qed.

    Corollary clock_match_exp_contradiction:
      forall le ck b v,
        wc_exp vars le ck ->
        forall n,
          sem_exp_instant (bk n) (H n) le v ->
          sem_clock_instant (bk n) (H n) ck b ->
          (b = true <-> v <> absent).
    Proof.
      intros.
      eapply clock_match_instant_exp_contradiction with (vars := vars); eauto.
    Qed.

    Lemma clock_match_cexp:
      forall ce ck,
        wc_cexp vars ce ck ->
        forall n v,
          sem_cexp_instant (bk n) (H n) ce v ->
          (sem_cexp_instant (bk n) (H n) ce absent
           /\ sem_clock_instant (bk n) (H n) ck false)
          \/
          ((exists c, sem_cexp_instant (bk n) (H n) ce (present c))
           /\ sem_clock_instant (bk n) (H n) ck true).
    Proof.
      intros; eapply clock_match_instant_cexp with (vars := vars); eauto.
    Qed.

  End ClockMatch.

 (* Transfer named streams defined within the body of a node ([R']) out into
     the environment where the node is instantiated ([R]). *)
  Lemma sem_var_instant_transfer_out_instant:
    forall (xin : list (ident * (type * clock)))
           (xout : list (ident * (type * clock)))
           R R' les ys isub osub base lss yss,
      NoDupMembers (xin ++ xout) ->
      Forall2 (fun xtc le => SameVar (isub (fst xtc)) le) xin les ->
      Forall2 (fun xtc  y => orelse isub osub (fst xtc) = Some y) xout ys ->
      (forall x, ~InMembers x xout -> osub x = None) ->
      sem_vars_instant R' (map fst xin) lss ->
      sem_vars_instant R' (map fst xout) yss ->
      sem_exps_instant base R les lss ->
      sem_vars_instant R ys yss ->
      forall x y ys,
        InMembers x (xin ++ xout) ->
        orelse isub osub x = Some y ->
        sem_var_instant R' x ys ->
        sem_var_instant R y ys.
  Proof.
    intros * Hndup Hsv Hos Hnos Hxin Hxout Hles Hys x y s Hin Hsub Hxv.
    apply InMembers_app in Hin as [Hin|Hout].
    - clear Hxout Hys Hos.
      apply NoDupMembers_app_InMembers with (2:=Hin) in Hndup.
      apply Hnos in Hndup.
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
      unfold orelse in Hsub.
      destruct (isub x); [|congruence].
      inv Hsub. inv Hsveq.
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
           H H' les ys isub osub bk lss yss,
      NoDupMembers (xin ++ xout) ->
      Forall2 (fun xtc le => SameVar (isub (fst xtc)) le) xin les ->
      Forall2 (fun xtc  y => orelse isub osub (fst xtc) = Some y) xout ys ->
      (forall x, ~InMembers x xout -> osub x = None) ->
      sem_vars H' (map fst xin) lss ->
      sem_vars H' (map fst xout) yss ->
      sem_exps bk H les lss ->
      sem_vars H ys yss ->
      forall x y ys,
        InMembers x (xin ++ xout) ->
        orelse isub osub x = Some y ->
        forall n,
          sem_var_instant (H' n) x ys ->
          sem_var_instant (H  n) y ys.
  Proof.
    intros; eapply sem_var_instant_transfer_out_instant; eauto.
  Qed.

  Lemma sem_var_instant_transfer_out':
    forall n (xin : list (ident * (type * clock)))
           (xout : list (ident * (type * clock)))
           H H' les ys isub osub (bk: stream bool) lss yss,
      NoDupMembers (xin ++ xout) ->
      Forall2 (fun xtc le => SameVar (isub (fst xtc)) le) xin les ->
      Forall2 (fun xtc  y => orelse isub osub (fst xtc) = Some y) xout ys ->
      (forall x, ~InMembers x xout -> osub x = None) ->
      sem_vars_instant (H' n) (map fst xin) (lss n) ->
      sem_vars_instant (H' n) (map fst xout) (yss n) ->
      sem_exps_instant (bk n) (H n) les (lss n) ->
      sem_vars_instant (H n) ys (yss n) ->
      forall x y ys,
        InMembers x (xin ++ xout) ->
        orelse isub osub x = Some y ->
        sem_var_instant (H' n) x ys ->
        sem_var_instant (H  n) y ys.
  Proof.
    intros * Hndup Hsv Hos Hnos Hxin Hxout Hles Hys x y s Hin Hsub Hxv.
    apply InMembers_app in Hin.
    destruct Hin as [Hin|Hout].
    - clear Hxout Hys Hos.
      apply NoDupMembers_app_InMembers with (2:=Hin) in Hndup.
      apply Hnos in Hndup.
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
      unfold orelse in Hsub.
      destruct (isub x); [|congruence].
      inv Hsub. inv Hsveq.
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

  (* Using the transfer of named streams, also transfer clocks from
     the interface. *)
  Lemma sem_clock_instant_transfer_out_instant:
    forall vars ck sub base base' R R' xck yck v,
      instck ck sub xck = Some yck ->
      sem_clock_instant base R ck base' ->
      wc_clock vars xck ->
      sem_clock_instant base' R' xck v ->
      (forall x y ys,
          InMembers x vars ->
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
    forall vars ck sub bk bk' (H: history) H' xck yck v n,
      instck ck sub xck = Some yck ->
      sem_clock_instant (bk n) (H n) ck (bk' n) ->
      wc_clock vars xck ->
      sem_clock_instant (bk' n) (H' n) xck v ->
      (forall x y ys,
          InMembers x vars ->
          sub x = Some y ->
          sem_var_instant (H' n) x ys ->
          sem_var_instant (H  n) y ys) ->
      sem_clock_instant (bk n) (H n) yck v.
  Proof.
    intros; eapply sem_clock_instant_transfer_out_instant; eauto.
  Qed.

  (* (* For variables defined in an environment [H], the semantic constraint *)
  (*    ([sem_clocked_vars]) forces the [clock_match] property. *) *)
  (* Lemma sem_clocked_vars_instant_clock_match_instant: *)
  (*   forall base R xcks xs, *)
  (*     sem_clocked_vars_instant base R xcks -> *)
  (*     sem_vars_instant R (map fst xcks) xs -> *)
  (*     Forall (clock_match_instant base R) xcks. *)
  (* Proof. *)
  (*   intros * Hsv Hvs. apply Forall_forall. *)
  (*   intros (x, xck) Hxin; unfold clock_match_instant. *)
  (*   eapply Forall_forall in Hsv; eauto. *)
  (*   unfold sem_vars_instant in Hvs. *)
  (*   rewrite Forall2_map_1 in Hvs. *)
  (*   apply Forall2_in_left with (2:=Hxin) in Hvs. *)
  (*   destruct Hvs as (v & ? & Hvs). *)
  (*   inversion Hsv as [Ht Hf]. simpl in *. *)
  (*   destruct v. *)
  (*   - intuition. *)
  (*   - right. *)
  (*     pose proof (ex_intro (fun c=>sem_var_instant _ _ (present c)) _ Hvs) as Hevs. *)
  (*     apply Ht in Hevs; eauto. *)
  (* Qed. *)

  (* Corollary sem_clocked_vars_clock_match: *)
  (*   forall bk H xcks xss, *)
  (*     sem_clocked_vars bk H xcks -> *)
  (*     sem_vars H (map fst xcks) xss -> *)
  (*     Forall (clock_match bk H) xcks. *)
  (* Proof. *)
  (*   intros * Hsv Hvs. apply Forall_forall. *)
  (*   intros (x, xck) Hxin n. *)
  (*   specialize (Hsv n); specialize (Hvs n). *)
  (*   eapply sem_clocked_vars_instant_clock_match_instant in Hvs; eauto. *)
  (*   eapply Forall_forall in Hvs; eauto. *)
  (* Qed. *)

  (* Transfer interface variable values onto interface clocks between
     an external environment ([Hn]) and an internal one ([Hn']). *)
  Lemma clock_vars_to_sem_clock_instant:
    forall vars bkn Hn Hn' ss,
      Forall2 (fun xtc => sem_var_instant Hn (fst xtc)) vars ss ->
      Forall2 (fun xtc => sem_var_instant Hn' (fst xtc)) vars ss ->
      wc_env (idck vars) ->
      forall x (xty: type) xck v,
        In (x, (xty, xck)) vars ->
        sem_clock_instant bkn Hn xck v ->
        sem_clock_instant bkn Hn' xck v.
  Proof.
    intros vars bkn Hn Hn' ss HHn HHn' WCenv x xty xck v Hin Hsi.
    assert (exists xty, In (x, (xty, xck)) vars) as Hin' by eauto.
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
        assert (s = present c) as Hsc by (eapply sem_var_instant_det; eauto).
        now subst.
      + econstructor; eauto.
        assert (s = absent) as Hsc by (eapply sem_var_instant_det; eauto).
        now subst.
      + eapply Son_abs2; eauto.
        assert (s = present c) as Hsc by (eapply sem_var_instant_det; eauto).
        now subst.
  Qed.

End CECLOCKINGSEMANTICS.

Module CEClockingSemanticsFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import CESyn : CESYNTAX        Op)
       (Import Str   : STREAM          Op OpAux)
       (Import CESem : CESEMANTICS Ids Op OpAux CESyn     Str)
       (Import CEClo : CECLOCKING  Ids Op       CESyn)
<: CECLOCKINGSEMANTICS Ids Op OpAux CESyn Str CESem CEClo.
  Include CECLOCKINGSEMANTICS Ids Op OpAux CESyn Str CESem CEClo.
End CEClockingSemanticsFun.
