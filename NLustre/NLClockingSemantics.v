Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.IsFree.
Require Import Velus.NLustre.Memories.
Require Import Velus.NLustre.IsDefined.
Require Import Velus.NLustre.NLClocking.
Require Import Velus.NLustre.NLExprSemantics.
Require Import Velus.NLustre.NLSemantics.
Require Import List.

(** * Link (static) clocking predicates to (dynamic) semantic model *)

(**

These results confirm the correctness of the clocking predicates wrt the
semantics. In particular, they are useful for relating static invariants to
dynamic properties. They hold essentially due to the "additional" clocking
constraints in the NLustre semantic model.

 *)

Module Type NLCLOCKINGSEMANTICS
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX       Op)
       (Import Clks    : CLOCKS          Ids)
       (Import ExprSyn : NLEXPRSYNTAX        Op)
       (Import Syn     : NLSYNTAX        Ids Op       Clks ExprSyn)
       (Import Str     : STREAM              Op OpAux)
       (Import Ord     : ORDERED         Ids Op       Clks ExprSyn Syn)
       (Import ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn     Str)
       (Import Sem     : NLSEMANTICS     Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem)
       (Import Mem     : MEMORIES        Ids Op       Clks ExprSyn Syn)
       (Import IsD     : ISDEFINED       Ids Op       Clks ExprSyn Syn                 Mem)
       (Import IsF     : ISFREE          Ids Op       Clks ExprSyn Syn)
       (Import Clkg    : NLCLOCKING      Ids Op       Clks ExprSyn Syn     Ord         Mem IsD IsF).

  Definition clock_match (base: stream bool) (H: history) (xc : ident * clock) : Prop :=
    forall n,
      (sem_var_instant (restr_hist H n) (fst xc) absent
       /\ sem_clock_instant (base n) (restr_hist H n) (snd xc) false)
      \/
      (exists c,
          sem_var_instant (restr_hist H n) (fst xc) (present c)
          /\ sem_clock_instant (base n) (restr_hist H n) (snd xc) true).

  Section ClockMatch.

    Variables
      (G: global)
      (vars: list (ident * clock))
      (bk: stream bool)
      (H: history)
      (Hcm: Forall (clock_match bk H) vars).

    Lemma clock_match_lexp:
      forall le ck,
        wc_lexp vars le ck ->
        forall n v,
          sem_lexp_instant (bk n) (restr_hist H n) le v ->
          (sem_lexp_instant (bk n) (restr_hist H n) le absent
           /\ sem_clock_instant (bk n) (restr_hist H n) ck false)
          \/
          (exists c,
              sem_lexp_instant (bk n) (restr_hist H n) le (present c)
              /\ sem_clock_instant (bk n) (restr_hist H n) ck true).
    Proof.
      induction le.
      - inversion_clear 1. intros.
        destruct (bk n); [right|left]; eauto using sem_lexp_instant, sem_clock_instant.
      - inversion_clear 1. intros.
        eapply Forall_forall in Hcm; eauto.
        specialize (Hcm n).
        destruct Hcm as [(Hv & Hc)|(c & Hv & Hc)]; [left|right];
          eauto using sem_lexp_instant.
      - repeat inversion_clear 1;
          repeat match goal with
                 | WC: wc_lexp _ _ _, SL: sem_lexp_instant _ _ _ _ |- _ =>
                   destruct (IHle _ WC _ _ SL) as [(Hv & Hc)|(?c & Hv & Hc)]
                 | HA: sem_lexp_instant _ _ _ absent,
                   HP: sem_lexp_instant _ _ _ (present ?cv) |- _ =>
                   now assert (present cv = absent) by sem_det
                 end.
        + right; eauto using sem_lexp_instant, sem_clock_instant.
        + left; eauto using sem_lexp_instant, sem_clock_instant.
        + left; eauto using sem_lexp_instant, sem_clock_instant.
      - repeat inversion_clear 1;
          repeat match goal with
                 | WC: wc_lexp _ _ _, SL: sem_lexp_instant _ _ _ _ |- _ =>
                   destruct (IHle _ WC _ _ SL) as [(Hv & Hc)|(?c & Hv & Hc)]
                 | HA: sem_lexp_instant _ _ _ absent,
                   HP: sem_lexp_instant _ _ _ (present ?cv) |- _ =>
                   now assert (present cv = absent) by sem_det
                 end.
        + right; eauto using sem_lexp_instant.
        + left; eauto using sem_lexp_instant.
      - repeat inversion_clear 1;
          repeat match goal with
                 | WC: wc_lexp _ _ _, SL: sem_lexp_instant _ _ _ _ |- _ =>
                   destruct (IHle1 _ WC _ _ SL) as [(Hv & Hc)|(?c & Hv & Hc)]
                 | WC: wc_lexp _ _ _, SL: sem_lexp_instant _ _ _ _ |- _ =>
                   destruct (IHle2 _ WC _ _ SL) as [(Hv & Hc)|(?c & Hv & Hc)]
                 | HA: sem_lexp_instant _ _ _ absent,
                   HP: sem_lexp_instant _ _ _ (present ?cv) |- _ =>
                   now assert (present cv = absent) by sem_det
                 end.
        + right; exists c'; eauto using sem_lexp_instant.
        + left; eauto using sem_lexp_instant.
    Qed.

    Corollary clock_match_lexp_contradiction:
      forall le ck b v,
        wc_lexp vars le ck ->
        forall n,
          sem_lexp_instant (bk n) (restr_hist H n) le v ->
          sem_clock_instant (bk n) (restr_hist H n) ck b ->
          (b = true <-> v <> absent).
    Proof.
      intros le ck b v WC n Hle Hck.
      eapply clock_match_lexp with (n:=n) in WC as [(Hle' & Hck')|(v' & Hle' & Hck')];
        eauto.
      - apply sem_clock_instant_det with (1:=Hck) in Hck'.
        apply sem_lexp_instant_det with (1:=Hle) in Hle'.
        subst; intuition.
      - apply sem_clock_instant_det with (1:=Hck) in Hck'.
        apply sem_lexp_instant_det with (1:=Hle) in Hle'.
        subst; intuition; discriminate.
    Qed.

    Lemma clock_match_cexp:
      forall ce ck,
        wc_cexp vars ce ck ->
        forall n v,
          sem_cexp_instant (bk n) (restr_hist H n) ce v ->
          (sem_cexp_instant (bk n) (restr_hist H n) ce absent
           /\ sem_clock_instant (bk n) (restr_hist H n) ck false)
          \/
          (exists c,
              sem_cexp_instant (bk n) (restr_hist H n) ce (present c)
              /\ sem_clock_instant (bk n) (restr_hist H n) ck true).
    Proof.
      induction ce.
      - repeat inversion_clear 1.
        + repeat match goal with
                 | WC: wc_cexp _ _ _, SL: sem_cexp_instant _ _ _ _ |- _ =>
                   destruct (IHce1 _ WC _ _ SL) as [(Hv & Hc)|(?c & Hv & Hc)]
                 | HA: sem_cexp_instant _ _ _ absent,
                   HP: sem_cexp_instant _ _ _ (present ?cv) |- _ =>
                   now assert (present cv = absent) by sem_det
                 end.
          right; eexists; split; eauto using sem_cexp_instant. inv Hc; auto.
        + repeat match goal with
                 | WC: wc_cexp _ _ _, SL: sem_cexp_instant _ _ _ _ |- _ =>
                   destruct (IHce2 _ WC _ _ SL) as [(Hv & Hc)|(?c & Hv & Hc)]
                 | HA: sem_cexp_instant _ _ _ absent,
                   HP: sem_cexp_instant _ _ _ (present ?cv) |- _ =>
                   now assert (present cv = absent) by sem_det
                 end.
          right; eexists; split; eauto using sem_cexp_instant. inv Hc; auto.
        + repeat match goal with
                 | WC: wc_cexp _ _ _, SL: sem_cexp_instant _ _ _ _ |- _ =>
                   destruct (IHce1 _ WC _ _ SL) as [(Hv & Hc)|(?c & Hv & Hc)]
                 | HA: sem_cexp_instant _ _ _ absent,
                   HP: sem_cexp_instant _ _ _ (present ?cv) |- _ =>
                   now assert (present cv = absent) by sem_det
                 end.
          left; split; eauto using sem_cexp_instant.
          inv Hc; auto. now assert (present c = absent) by sem_det.
      - repeat inversion_clear 1; [right|left];
          repeat match goal with
                 | WC: wc_cexp _ _ _, SL: sem_cexp_instant _ _ _ _ |- _ =>
                   destruct (IHce1 _ WC _ _ SL) as [(Hv1 & Hc1)|(?c & Hv1 & Hc1)]
                 | WC: wc_cexp _ _ _, SL: sem_cexp_instant _ _ _ _ |- _ =>
                   destruct (IHce2 _ WC _ _ SL) as [(Hv2 & Hc2)|(?c & Hv2 & Hc2)]
                 | HA: sem_cexp_instant _ _ _ absent,
                   HP: sem_cexp_instant _ _ _ (present ?cv) |- _ =>
                   now assert (present cv = absent) by sem_det
                 | Hc: sem_lexp_instant _ _ _ (present ?c),
                   Ht: sem_cexp_instant _ _ _ (present ?ct),
                   Hf: sem_cexp_instant _ _ _ (present ?cf),
                   Hv: val_to_bool ?c = Some ?b |- _ =>
                   apply (Site_eq _ _ _ _ _ _ _ _ _ Hc Ht Hf) in Hv;
                     destruct b
                 end; eauto using sem_cexp_instant.
      - inversion_clear 1 as [| |? ? Hwc].
        inversion_clear 1.
        eapply clock_match_lexp in Hwc; eauto.
        destruct Hwc as [(Hv & Hc)|(?c & Hv & Hc)]; [left|right];
          eauto using sem_cexp_instant.
    Qed.

  End ClockMatch.

  Lemma sem_var_transfer_in:
    forall (xin : list (ident * (type * clock))) H H' les isub bk lss,
      Forall2 (fun xtc le => subvar_eq (isub (fst xtc)) le) xin les ->
      sem_lexps bk H les lss ->
      sem_vars H' (map fst xin) lss ->
      forall x y ys,
        InMembers x xin ->
        isub x = Some y ->
        sem_var H y ys ->
        sem_var H' x ys.
  Proof.
    intros ** node H H' les isub bk lss Hsv Hles Hlss x y ys Hin Hsub Hvar n.
    specialize (Hles n); specialize (Hlss n); specialize (Hvar n); simpl in *.
    unfold sem_vars_instant in Hlss.
    rewrite Forall2_map_1 in Hlss.
    apply InMembers_In in Hin as ((xty, xck) & Hxin).
    apply Forall2_trans_ex with (1:=Hsv) in Hles. clear Hsv.
    apply Forall2_Forall2 with (1:=Hles) in Hlss. clear Hles.
    apply Forall2_in_left with (2:=Hxin) in Hlss
      as (ls & Hinls & (le & Hinle & Hsveq & Hsls) & Hvls).
    simpl in *. rewrite Hsub in Hsveq.
    destruct le; try contradiction. simpl in *; subst.
    inversion_clear Hsls.
    assert (ys n = ls) as Hys by sem_det.
    now rewrite Hys in *.
  Qed.

  (* Transfer named streams defined within the body of a node ([H']) out into
     the environment where the node is instantiated ([H]). *)
  Lemma sem_var_instant_transfer_out:
    forall (xin : list (ident * (type * clock)))
           (xout : list (ident * (type * clock)))
           H H' les ys isub osub bk lss yss,
      NoDupMembers (xin ++ xout) ->
      Forall2 (fun xtc le => subvar_eq (isub (fst xtc)) le) xin les ->
      Forall2 (fun xtc  y => orelse isub osub (fst xtc) = Some y) xout ys ->
      (forall x, ~InMembers x xout -> osub x = None) ->
      sem_vars H' (map fst xin) lss ->
      sem_vars H' (map fst xout) yss ->
      sem_lexps bk H les lss ->
      sem_vars H ys yss ->
      forall x y ys,
        InMembers x (xin ++ xout) ->
        orelse isub osub x = Some y ->
        forall n,
          sem_var_instant (restr_hist H' n) x ys ->
          sem_var_instant (restr_hist H  n) y ys.
  Proof.
    intros ** Hndup Hsv Hos Hnos Hxin Hxout Hles Hys x y s Hin Hsub n Hxv.
    specialize (Hxin n). specialize (Hxout n).
    specialize (Hles n). specialize (Hys n). simpl in *.
    apply InMembers_app in Hin.
    destruct Hin as [Hin|Hout].
    - clear Hxout Hys Hos.
      apply NoDupMembers_app_InMembers with (2:=Hin) in Hndup.
      apply Hnos in Hndup.
      apply InMembers_In in Hin as ((xty & xck) & Hin).
      unfold sem_lexps_instant in Hles.
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
      unfold subvar_eq in Hsveq.
      destruct (isub x); [|congruence].
      inv Hsub. destruct le; try contradiction.
      simpl in Hsveq. subst.
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

  Lemma sem_var_instant_transfer_out':
    forall n (xin : list (ident * (type * clock)))
           (xout : list (ident * (type * clock)))
           H H' les ys isub osub bk lss yss,
      NoDupMembers (xin ++ xout) ->
      Forall2 (fun xtc le => subvar_eq (isub (fst xtc)) le) xin les ->
      Forall2 (fun xtc  y => orelse isub osub (fst xtc) = Some y) xout ys ->
      (forall x, ~InMembers x xout -> osub x = None) ->
      sem_vars_instant (restr_hist H' n) (map fst xin) (lss n) ->
      sem_vars_instant (restr_hist H' n) (map fst xout) (yss n) ->
      sem_lexps_instant (bk n) (restr_hist H n) les (lss n) ->
      sem_vars_instant (restr_hist H n) ys (yss n) ->
      forall x y ys,
        InMembers x (xin ++ xout) ->
        orelse isub osub x = Some y ->
        sem_var_instant (restr_hist H' n) x ys ->
        sem_var_instant (restr_hist H  n) y ys.
  Proof.
    intros ** Hndup Hsv Hos Hnos Hxin Hxout Hles Hys x y s Hin Hsub Hxv.
    apply InMembers_app in Hin.
    destruct Hin as [Hin|Hout].
    - clear Hxout Hys Hos.
      apply NoDupMembers_app_InMembers with (2:=Hin) in Hndup.
      apply Hnos in Hndup.
      apply InMembers_In in Hin as ((xty & xck) & Hin).
      unfold sem_lexps_instant in Hles.
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
      unfold subvar_eq in Hsveq.
      destruct (isub x); [|congruence].
      inv Hsub. destruct le; try contradiction.
      simpl in Hsveq. subst.
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
  Lemma sem_clock_instant_transfer_out:
    forall vars ck sub bk bk' H H' xck yck v n,
      instck ck sub xck = Some yck ->
      sem_clock_instant (bk n) (restr_hist H n) ck (bk' n) ->
      wc_clock vars xck ->
      sem_clock_instant (bk' n) (restr_hist H' n) xck v ->
      (forall x y ys,
          InMembers x vars ->
          sub x = Some y ->
          sem_var_instant (restr_hist H' n) x ys ->
          sem_var_instant (restr_hist H  n) y ys) ->
      sem_clock_instant (bk n) (restr_hist H n) yck v.
  Proof.
    intros ** Hinst Hcks Hwc Hsem Hxv.
    revert xck ck yck v Hinst Hcks Hwc Hsem.
    induction xck; simpl in *.
    - inversion 1; inversion 3; now subst.
    - intros ck yck v Hinst Hcks Hwc Hsem.
      destruct (instck ck sub xck) eqn:Hi; try discriminate.
      destruct (sub i) eqn:Hsi; try discriminate.
      inv Hinst. inv Hwc.
      apply In_InMembers in H4.
      inv Hsem; eauto using sem_clock_instant.
  Qed.

  (* For variables defined in an environment [H], the semantic constraint
     ([sem_clocked_vars]) forces the [clock_match] property. *)
  Lemma sem_clocked_vars_clock_match:
    forall bk H xcks xss,
      sem_clocked_vars bk H xcks ->
      sem_vars H (map fst xcks) xss ->
      Forall (clock_match bk H) xcks.
  Proof.
    intros ** Hsv Hvs. apply Forall_forall. intros (x, xck) Hxin n.
    specialize (Hsv n); specialize (Hvs n).
    eapply Forall_forall in Hsv; eauto.
    unfold sem_vars_instant in Hvs.
    rewrite Forall2_map_1 in Hvs.
    apply Forall2_in_left with (2:=Hxin) in Hvs as (xs & ? & Hvs).
    inversion Hsv as [Ht Hf]. simpl in *.
    destruct xs.
    - now intuition.
    - right.
      pose proof (ex_intro (fun c=>sem_var_instant _ _ (present c)) _ Hvs) as Hevs.
      apply Ht in Hevs. eauto.
  Qed.

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
      apply Forall2_in_left with (2:=Hin) in HHn as (s & Hsin & Hv' & Hv).
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


  Lemma clock_match_node_eqs_reset:
    forall G,
      Ordered_nodes G ->
      wc_global G ->
      (forall f xss yss,
          sem_node G f xss yss ->
          forall bk H n,
            find_node f G = Some n ->
            clock_of xss bk ->
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
            clock_of (mask (all_absent (xss 0)) k rs xss) bk ->
            sem_vars H (map fst node.(n_in)) (mask (all_absent (xss 0)) k rs xss) ->
            sem_vars H (map fst node.(n_out)) (mask (all_absent (yss 0)) k rs yss) ->
            Forall (clock_match bk H) (idck node.(n_in)) ->
            Forall (clock_match bk H) (idck node.(n_out))).
  Proof.
    intros ** Hord WCG; apply sem_node_equation_reset_ind;
      [intros ?????? Hvar Hexp|
       intros ???????? Hexps Hvars Hsem|
       intros ??????????? Hexps Hvars ?? Hsem|
       intros ???????? Hexp Hvar|
       intros ???? IH|
       intros ?????? Hck Hf Hin Hout ????? IH].

    - (* EqDef *)
      intros iface y yck Hnd Hwc Hdef Hin n.
      inv Hdef. inv Hwc.
      match goal with H1:In (x, _) iface, H2:In (x, _) iface |- _ =>
        apply NoDupMembers_det with (1:=Hnd) (2:=H1) in H2; subst end.
      specialize (Hvar n). specialize (Hexp n).
      inv Hexp; match goal with H:_ = xs n |- _ => rewrite <-H in * end; eauto.

    - (* EqApp *)
      intros IHHsem iface z zck Hndup Hwc Hdef Hiface.
      (* rename ys into yss, y into ys, z into y, zck into yck. *)
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
        - intro n; specialize (Hexps n); inv Hexps; eauto.
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
      destruct (Hscv' n) as [(Hv & Hc)|(c & Hv & Hc)].
      + left; split.
        * apply sem_var_instant_det with (1:=Hsvx) in Hv. now subst.
        *{ eapply sem_clock_instant_transfer_out
             with (vars := idck (node'.(n_in) ++ node'.(n_out))); eauto.
           - clear - Hvi Hco' Hexps.
             specialize (Hco' n); specialize (Hexps n); inversion_clear Hexps as [???? E|??? E].
             + assert (cks' n = true) as ->; auto.
               rewrite <-Hco', present_list_spec; eauto.
             + assert (cks' n = false) as ->; auto.
               specialize (Hvi n).
               apply Forall2_length in Hvi; rewrite map_length, E in Hvi.
               pose proof (n_ingt0 node') as Length; rewrite Hvi in Length.
               apply Bool.not_true_is_false; rewrite <-Hco', E.
               clear - Length.
               destruct arg; simpl in *. omega.
               inversion 1; congruence.
           - now setoid_rewrite InMembers_idck; eauto.
         }
      + right. exists c; split.
        * apply sem_var_instant_det with (1:=Hsvx) in Hv. now subst.
        *{ eapply sem_clock_instant_transfer_out
             with (vars := idck (node'.(n_in) ++ node'.(n_out))); eauto.
           - clear - Hvi Hco' Hexps.
             specialize (Hco' n); specialize (Hexps n); inversion_clear Hexps as [???? E|??? E].
             + assert (cks' n = true) as ->; auto.
               rewrite <-Hco', present_list_spec; eauto.
             + assert (cks' n = false) as ->; auto.
               specialize (Hvi n).
               apply Forall2_length in Hvi; rewrite map_length, E in Hvi.
               pose proof (n_ingt0 node') as Length; rewrite Hvi in Length.
               apply Bool.not_true_is_false; rewrite <-Hco', E.
               clear - Length.
               destruct arg; simpl in *. omega.
               inversion 1; congruence.
           - now setoid_rewrite InMembers_idck; eauto.
         }

    - (* EqReset *)
      intros IHHsem iface z zck Hndup Hwc Hdef Hiface n.
      (* rename ys into yss, y into ys, z into y, zck into yck. *)
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
          specialize (Hexps n); inv Hexps; eauto.
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
      destruct (Hscv' n) as [(Hv & Hc)|(c & Hv & Hc)].
      + left; split.
        * apply sem_var_instant_det with (1:=Hsvx) in Hv. now subst.
        *{ eapply sem_clock_instant_transfer_out
             with (vars := idck (node'.(n_in) ++ node'.(n_out))); eauto.
           - clear - Hvi Hco' Hexps.
             specialize (Hco' n); specialize (Hexps n); inversion_clear Hexps as [???? E|??? E].
             + rewrite mask_transparent in Hco'; auto.
               assert (cks' n = true) as ->; auto.
               rewrite <-Hco', present_list_spec; eauto.
             + assert (cks' n = false) as ->; auto.
               specialize (Hvi n).
               rewrite mask_transparent in Hvi, Hco'; auto.
               apply Forall2_length in Hvi; rewrite map_length, E in Hvi.
               pose proof (n_ingt0 node') as Length; rewrite Hvi in Length.
               apply Bool.not_true_is_false; rewrite <-Hco', E.
               clear - Length.
               destruct arg; simpl in *. omega.
               inversion 1; congruence.
           - now setoid_rewrite InMembers_idck; eauto.
         }
      + right. exists c; split.
        * apply sem_var_instant_det with (1:=Hsvx) in Hv. now subst.
        *{ eapply sem_clock_instant_transfer_out
             with (vars := idck (node'.(n_in) ++ node'.(n_out))); eauto.
           - clear - Hvi Hco' Hexps.
             specialize (Hco' n); specialize (Hexps n); inversion_clear Hexps as [???? E|??? E].
             + assert (cks' n = true) as ->; auto.
               rewrite mask_transparent in Hco'; auto.
               rewrite <-Hco', present_list_spec; eauto.
             + assert (cks' n = false) as ->; auto.
               specialize (Hvi n).
               rewrite mask_transparent in Hvi, Hco'; auto.
               apply Forall2_length in Hvi; rewrite map_length, E in Hvi.
               pose proof (n_ingt0 node') as Length; rewrite Hvi in Length.
               apply Bool.not_true_is_false; rewrite <-Hco', E.
               clear - Length.
               destruct arg; simpl in *. omega.
               inversion 1; congruence.
           - now setoid_rewrite InMembers_idck; eauto.
       }

    - (* EqFby *)
      intros ? iface z zck Hnd Hwc Hdef Hin n.
      inv Hdef; inv Hwc.
      match goal with H1:In (?y, _) iface, H2:In (?y, _) iface |- _ =>
        apply NoDupMembers_det with (1:=Hnd) (2:=H1) in H2; subst end.
      specialize (Hexp n). specialize (Hvar n).
      unfold fby in Hvar.
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
      apply Is_defined_in_eqs_In in Hxin as (eq & Heqin & Hxeq).
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
      apply clock_of_det with (1:=Hck) (n:=n) in Hck'.
      rewrite Hck' in *.
      apply Forall2_Forall2 with (1:=Hout) in Hout'.
      apply Forall2_in_left with (2:=Hxin') in Hout' as (s & Hsin & Hvs & Hvs').
      destruct (Hnd n) as [(Hv & Hc)|(c & Hv & Hc)].
      + left. simpl in *. split.
        * apply sem_var_instant_det with (1:=Hvs) in Hv. now subst.
        * eapply clock_vars_to_sem_clock_instant
          with (1:=Hout2) (2:=Hin') in WCo; eauto.
          eapply in_app; eauto.
      + right. simpl in *. exists c. split.
        * apply sem_var_instant_det with (1:=Hvs) in Hv. now subst.
        * eapply clock_vars_to_sem_clock_instant
          with (1:=Hout2) (2:=Hin') in WCo; eauto.
          eapply in_app; eauto.
  Qed.


  (* When a node's inputs match their clocks, then so do its outputs.
     This is a consequence (by induction throughout the node hierarchy) of
     the constraints relating streams to their clocks for each case of
     [sem_equation]. *)
  Lemma clock_match_node:
    forall G f xss yss bk H n,
      Ordered_nodes G ->
      wc_global G ->
      sem_node G f xss yss ->
      find_node f G = Some n ->
      clock_of xss bk ->
      sem_vars H (map fst n.(n_in)) xss ->
      sem_vars H (map fst n.(n_out)) yss ->
      Forall (clock_match bk H) (idck n.(n_in)) ->
      Forall (clock_match bk H) (idck n.(n_out)).
  Proof.
    intros ??????? Ord WCG; intros.
    eapply (proj1 (clock_match_node_eqs_reset G Ord WCG)); eauto.
  Qed.

  (* A "version" of [clock_match_node] for "within" a node. Much of the
     reasoning from [clock_match_node] is unfortunately repeated here. It's
     not clear whether this is inevitable or whether there is a smarter way
     to do the induction (maybe by tweaking [sem_node_mult]). The essential
     difficulty is that the internal environment ([H]) is existentially
     quantified for a node, which makes it hard to state the lemma relative
     to [sem_node], and tedious to "transfer" facts known "outside" a
     node to facts known "within" it. At the time of writing, there is no
     determinism lemma for environments constrained by nodes. *)
  Lemma clock_match_eq:
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

  Lemma clock_match_eqs:
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
    apply Is_defined_in_var_defined, Is_defined_in_eqs_In in Hxin
      as (eq & Hieq & Hdeq).
    eapply Forall_forall in Hsem; eauto.
    eapply Forall_forall in Hwc; eauto.
    eapply clock_match_eq; eauto.
    rewrite in_app; auto.
  Qed.

End NLCLOCKINGSEMANTICS.

Module NLClockingSemanticsFun
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX       Op)
       (Import Clks    : CLOCKS          Ids)
       (Import ExprSyn : NLEXPRSYNTAX        Op)
       (Import Syn     : NLSYNTAX        Ids Op       Clks ExprSyn)
       (Import Str     : STREAM              Op OpAux)
       (Import Ord     : ORDERED         Ids Op       Clks ExprSyn Syn)
       (Import ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn     Str)
       (Import Sem     : NLSEMANTICS     Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem)
       (Import Mem     : MEMORIES        Ids Op       Clks ExprSyn Syn)
       (Import IsD     : ISDEFINED       Ids Op       Clks ExprSyn Syn                 Mem)
       (Import IsF     : ISFREE          Ids Op       Clks ExprSyn Syn)
       (Import Clkg    : NLCLOCKING      Ids Op       Clks ExprSyn Syn     Ord         Mem IsD IsF)
<: NLCLOCKINGSEMANTICS Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem Sem Mem IsD IsF Clkg.
  Include NLCLOCKINGSEMANTICS Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem Sem Mem IsD IsF Clkg.
End NLClockingSemanticsFun.
