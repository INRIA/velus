From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Permutation.
From Coq Require Import Decidable.
From Coq Require Import Omega.
From Coq Require Import Setoid Morphisms.

From compcert Require Import common.Errors.

From Velus Require Import Common Ident Clocks.
From Velus Require Import CheckGraph.
From Velus Require Import Operators Environment.
From Velus Require Import Lustre.LSyntax Lustre.LClocking Lustre.LCausality.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

(** * Conservation of causality through normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type NCAUSALITY
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Cau : LCAUSALITY Ids Op Syn)
       (Import Clo : LCLOCKING Ids Op Syn)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn Cau).

  Import Fresh Tactics.

  (** Some auxiliary stuff *)

  Fact in_vars_defined_concat : forall x eqs eqs',
      In eqs eqs' ->
      In x (vars_defined eqs) ->
      In x (vars_defined (concat eqs')).
  Proof.
    intros * Hin1 Hin2.
    unfold vars_defined in *. rewrite flat_map_concat_map in *.
    apply in_concat in Hin2 as [xs [Hin2 Hin3]].
    apply in_map_iff in Hin3 as [[xs' es] [? Hin3]]; simpl in *; subst.
    eapply incl_concat_map with (x0:=(xs, es)); simpl; auto.
    eapply in_concat'; eauto.
  Qed.

  Fact vars_defined_combine : forall xs es,
      length xs = length es ->
      vars_defined (combine xs es) = concat xs.
  Proof.
    intros * Hlen.
    unfold vars_defined. rewrite flat_map_concat_map, combine_map_fst'; auto.
  Qed.

  (** If an expression is wc with regards to an environment, all it's
      left-free vars appear in the environment *)

  Hint Resolve In_InMembers.
  Fact wc_exp_Is_free_left : forall G vars x e,
      wc_exp G vars e ->
      Is_free_left x e ->
      InMembers x vars.
  Proof with eauto.
    induction e using exp_ind2; intros Hwc Hfree;
      inv Hwc; inv Hfree...
    Local Ltac Forall_Exists_free H :=
      eapply Forall_Exists, Exists_exists in H as [? [_ [H ?]]]; eauto;
      simpl in H; destruct H as [? ?]; eauto.
    - (* binop *) destruct H0; eauto.
    - (* fby *)
      eapply Forall_Forall in H; eauto. clear H4.
      Forall_Exists_free H2.
    - (* arrow *)
      eapply Forall_Forall in H; eauto. clear H4.
      eapply Forall_Forall in H0; eauto. clear H5.
      destruct H2 as [Hfree|Hfree]; Forall_Exists_free Hfree.
    - (* when *)
      destruct H1 as [?|Hfree]; subst...
      eapply Forall_Forall in H; eauto. clear H4.
      Forall_Exists_free Hfree.
    - (* merge *)
      destruct H2 as [?|Hfree]; subst...
      eapply Forall_Forall in H; eauto. clear H5.
      eapply Forall_Forall in H0; eauto. clear H6.
      destruct Hfree as [Hfree|Hfree]; Forall_Exists_free Hfree.
    - (* ite *)
      eapply Forall_Forall in H; eauto. clear H6.
      eapply Forall_Forall in H0; eauto. clear H7.
      destruct H2 as [Hfree|[Hfree|Hfree]]; eauto; Forall_Exists_free Hfree.
    - (* app *)
      eapply Forall_Forall in H0; eauto. clear H5.
      Forall_Exists_free H2.
    - (* app (reset) *)
      eapply Forall_Forall in H0; eauto. clear H5.
      inv H2...
      Forall_Exists_free H3.
  Qed.

  (** A clocking + causality property : *)

  Inductive Is_free_left_ck (x : ident) : exp -> Prop :=
  | IFLvar : forall y ty ck name,
      x = y \/
      Is_free_in_clock x ck ->
      Is_free_left_ck x (Evar y (ty, (ck, name)))
  | IFLunop : forall op e ty ck name,
      Is_free_left_ck x e \/
      Is_free_in_clock x ck ->
      Is_free_left_ck x (Eunop op e (ty, (ck, name)))
  | IFLbinop : forall op e1 e2 ty ck name,
      Is_free_left_ck x e1 \/
      Is_free_left_ck x e2 \/
      Is_free_in_clock x ck ->
      Is_free_left_ck x (Ebinop op e1 e2 (ty, (ck, name)))
  | IFLfby : forall e0s es a,
      Exists (Is_free_left_ck x) e0s \/
      Exists (Is_free_in_clock x) (map clock_of_nclock a) ->
      Is_free_left_ck x (Efby e0s es a)
  | IFLarrow : forall e0s es a,
      Exists (Is_free_left_ck x) e0s \/
      Exists (Is_free_left_ck x) es \/
      Exists (Is_free_in_clock x) (map clock_of_nclock a) ->
      Is_free_left_ck x (Earrow e0s es a)
  | IFLwhen : forall es y b tys ck name,
      x = y \/
      Exists (Is_free_left_ck x) es \/
      Is_free_in_clock x ck ->
      Is_free_left_ck x (Ewhen es y b (tys, (ck, name)))
  | IFLmerge : forall ets efs y tys ck name,
      x = y \/
      Exists (Is_free_left_ck x) ets \/
      Exists (Is_free_left_ck x) efs \/
      Is_free_in_clock x ck ->
      Is_free_left_ck x (Emerge y ets efs (tys, (ck, name)))
  | IFLite : forall e ets efs tys ck name,
      Is_free_left_ck x e \/
      Exists (Is_free_left_ck x) ets \/
      Exists (Is_free_left_ck x) efs \/
      Is_free_in_clock x ck ->
      Is_free_left_ck x (Eite e ets efs (tys, (ck, name)))
  | IFLapp : forall f es a,
      Exists (Is_free_left_ck x) es ->
      Is_free_left_ck x (Eapp f es None a)
  | IFLreset : forall f es r a,
      Exists (Is_free_left_ck x) (r :: es) ->
      Is_free_left_ck x (Eapp f es (Some r) a).
  Hint Constructors Is_free_left_ck.

  Inductive Is_causal_ck (inputs : list ident) : list equation -> Prop :=
  | ICnil:
      Is_causal_ck inputs []
  | ICcons: forall eq eqs,
      Is_causal_ck inputs eqs ->
      (forall x, Exists (Is_free_left_ck x) (snd eq) ->
            In x (vars_defined eqs) \/ In x inputs) ->
      Is_causal_ck inputs (eq :: eqs).
  Hint Constructors Is_causal_ck.

  Fact Is_free_left_Is_free_left_ck : forall x e,
      Is_free_left x e ->
      Is_free_left_ck x e.
  Proof.
    induction e using exp_ind2; intros Hfree; inv Hfree;
      try (destruct a as (ty&ck&name)); auto.
    - (* binop *)
      destruct H0; auto.
    - (* fby *)
      eapply Forall_Exists in H2; eauto.
      constructor. left.
      eapply Exists_Exists; [|eauto]. intros ? [? ?]; eauto.
    - (* arrow *)
      destruct H2 as [Hfree|Hfree].
      1,2:eapply Forall_Exists in Hfree; eauto.
      + constructor. left. eapply Exists_Exists; [|eauto]. intros ? [? ?]; eauto.
      + constructor. right. left. eapply Exists_Exists; [|eauto]. intros ? [? ?]; eauto.
    - (* when *)
      destruct H1; auto.
      eapply Forall_Exists in H; eauto.
      constructor. right; left.
      eapply Exists_Exists; [|eauto]. intros ? [? ?]; eauto.
    - (* merge *)
      destruct H2 as [?|[?|?]]; auto.
      + eapply Forall_Exists in H; eauto.
        constructor. right; left.
        eapply Exists_Exists; [|eauto]. intros ? [? ?]; eauto.
      + eapply Forall_Exists in H0; eauto.
        constructor. right; right; left.
        eapply Exists_Exists; [|eauto]. intros ? [? ?]; eauto.
    - (* ite *)
      destruct H2 as [?|[?|?]]; auto.
      + eapply Forall_Exists in H; eauto.
        constructor. right; left.
        eapply Exists_Exists; [|eauto]. intros ? [? ?]; eauto.
      + eapply Forall_Exists in H0; eauto.
        constructor. right; right; left.
        eapply Exists_Exists; [|eauto]. intros ? [? ?]; eauto.
    - (* app *)
      eapply Forall_Exists in H0; eauto.
      constructor.
      eapply Exists_Exists; [|eauto]. intros ? [? ?]; eauto.
    - (* app (reset) *)
      inv H2; auto.
      eapply Forall_Exists in H0; eauto.
      constructor.
      eapply Exists_Exists; [|eauto]. intros ? [? ?]; eauto.
  Qed.

  Fact Is_causal_ck_Is_causal : forall inputs eqs,
      Is_causal_ck inputs eqs ->
      Is_causal inputs eqs.
  Proof.
    intros * Hcaus. induction Hcaus; auto.
    constructor; auto.
    intros ? Hfree. eapply H.
    eapply Exists_Exists; [|eauto].
    intros. eapply Is_free_left_Is_free_left_ck; eauto.
  Qed.

  Fact Exists_clocksof : forall x es,
      Exists (Is_free_in_clock x) (clocksof es) <->
      Exists (fun e => Exists (Is_free_in_clock x) (clockof e)) es.
  Proof.
    intros *.
    unfold clocksof. rewrite flat_map_concat_map, Exists_concat, Exists_map. reflexivity.
  Qed.

  Hint Constructors Is_free_left.

  Lemma wc_normalized_lexp_clockof_free_in : forall G vars e,
      normalized_lexp e ->
      wc_exp G vars e ->
      forall x, Exists (Is_free_in_clock x) (clockof e) ->
           Is_free_left x e \/
           exists y, exists ck', Is_free_left y e /\ In (y, ck') vars /\ Is_free_in_clock x ck'.
  Proof.
    intros * Hnormed Hwc ? Hex; induction Hnormed; inv Hwc;
      simpl in Hex; apply Exists_singl in Hex.
    - (* const *) inv Hex.
    - (* var *)
      right. exists x0. exists ck.
      repeat split; auto.
    - (* var *)
      right. exists x0. exists ck.
      repeat split; auto.
    - (* unop *)
      rewrite H4 in IHHnormed.
      specialize (IHHnormed H1 (Exists_cons_hd _ _ _ Hex)) as [IHe|[y [ck' [?[? ?]]]]]; auto.
      right. exists y. exists ck'. repeat split; auto.
    - (* binop *)
      rewrite H6 in IHHnormed1.
      specialize (IHHnormed1 H3 (Exists_cons_hd _ _ _ Hex)) as [IHe1|[y [ck' [Hfree [Hin Hex']]]]]; auto.
      right. exists y. exists ck'. repeat split; auto.
     - (* when *)
      simpl in *; rewrite app_nil_r in *.
      inv Hex; auto.
      symmetry in H7; singleton_length.
      apply Forall_singl in H3. apply Forall_singl in H6; subst.
      specialize (IHHnormed H3 (Exists_cons_hd _ _ _ H1)) as [Hex|[y [ck' [Hfree [Hin Hex]]]]]; auto.
      right. exists y. exists ck'. repeat split; auto.
  Qed.

  Corollary wc_normalized_lexps_clocksof_free_in : forall G vars es,
      Forall normalized_lexp es ->
      Forall (wc_exp G vars) es ->
      forall x, Exists (Is_free_in_clock x) (clocksof es) ->
           Exists (fun e => Is_free_left x e \/
                         exists y, exists ck', Is_free_left y e /\ In (y, ck') vars /\ Is_free_in_clock x ck') es.
  Proof.
    intros * Hnorm Hwc x Hex.
    unfold clocksof in Hex. rewrite flat_map_concat_map, Exists_concat, Exists_map in Hex.
    rewrite Exists_exists in *. destruct Hex as [e [Hin Hex]].
    exists e. split; auto.
    eapply wc_normalized_lexp_clockof_free_in; eauto.
    1,2:eapply Forall_forall in Hin; eauto.
  Qed.

  Lemma wc_normalized_lexp_Is_free_left : forall G vars e,
      normalized_lexp e ->
      wc_exp G vars e ->
      forall x, Is_free_left_ck x e ->
           Is_free_left x e \/
           exists y, exists ck', Is_free_left y e /\ In (y, ck') vars /\ Is_free_in_clock x ck'.
  Proof.
    intros * Hnormed Hwc ? Hex; induction Hnormed; inv Hwc; inv Hex.
    - (* var *)
      destruct H1; subst; eauto 10.
    - (* var *)
      destruct H1; subst; eauto 10.
    - (* unop *)
      destruct H0.
      + eapply IHHnormed in H as [?|[y [ck' [? [? ?]]]]]; eauto 10.
      + eapply wc_normalized_lexp_clockof_free_in in Hnormed as [?|[y [ck' [? [? ?]]]]]; eauto 10.
        rewrite H4; auto.
    - (* binop *)
      destruct H0 as [?|[?|?]].
      + eapply IHHnormed1 in H as [?|[y [ck' [? [? ?]]]]]; eauto 10.
      + eapply IHHnormed2 in H as [?|[y [ck' [? [? ?]]]]]; eauto 10.
      + eapply wc_normalized_lexp_clockof_free_in in Hnormed1 as [?|[y [ck' [? [? ?]]]]]; eauto 10.
        rewrite H6; auto.
     - (* when *)
       apply Forall_singl in H3.
       destruct H0 as [?|[Hex|Hex]]; auto.
       + apply Exists_singl in Hex. eapply IHHnormed in Hex as [?|[y [ck' [? [? ?]]]]]; eauto 10.
       + simpl in H7. symmetry in H7. rewrite app_nil_r in H7. singleton_length.
         apply Forall_singl in H6; subst. inv Hex; auto.
         eapply wc_normalized_lexp_clockof_free_in in Hnormed as [?|[y [ck' [? [? ?]]]]]; eauto.
         2:rewrite Hsingl; auto.
         right. exists y. exists ck'. repeat split; auto.
  Qed.

  Corollary wc_normalized_lexps_Is_free_left : forall G vars es,
      Forall normalized_lexp es ->
      Forall (wc_exp G vars) es ->
      forall x, Exists (Is_free_left_ck x) es ->
           Exists (fun e => Is_free_left x e \/
                         exists y, exists ck', Is_free_left y e /\ In (y, ck') vars /\ Is_free_in_clock x ck') es.
  Proof.
    intros * Hnorm Hwc x Hex.
    simpl_forall.
    eapply Forall_Exists in Hex; eauto. clear Hnorm.
    eapply Exists_Exists; [|eauto].
    intros ? [[? ?] ?].
    eapply wc_normalized_lexp_Is_free_left; eauto.
  Qed.

  Lemma wc_normalized_cexp_clockof_free_in : forall G vars e,
      normalized_cexp e ->
      wc_exp G vars e ->
      forall x, Exists (Is_free_in_clock x) (clockof e) ->
           Is_free_left x e \/
           exists y, exists ck', Is_free_left y e /\ In (y, ck') vars /\ Is_free_in_clock x ck'.
  Proof.
    intros * Hnormed Hwc ? Hex; induction Hnormed;
      simpl in Hex; try apply Exists_singl in Hex.
    - (* merge *)
      inv Hwc; simpl in *; rewrite app_nil_r in *.
      clear IHHnormed2 H5 H8 H10.
      symmetry in H9; singleton_length.
      apply Forall_singl in H4. apply Forall_singl in H7; subst.
      assert (Is_free_in_clock x (Con ck x0 true)) as Hfree by (right; auto).
      specialize (IHHnormed1 H4 (Exists_cons_hd _ _ _ Hfree)) as [Hex'|[y [ck' [Hfree' [Hin Hex']]]]].
      + left; auto.
      + right. exists y. exists ck'. repeat split; auto.
    - (* ite *)
      inv Hwc.
      eapply wc_normalized_lexp_clockof_free_in in H as [Hex'|[y [ck' [Hfree' [Hin Hex']]]]]; eauto.
      2: rewrite H8; eauto.
      right. exists y. exists ck'. repeat split; eauto.
    - (* lexp *)
      eapply wc_normalized_lexp_clockof_free_in in Hex; eauto.
  Qed.

  Lemma wc_normalized_cexp_Is_free_left : forall G vars e,
      normalized_cexp e ->
      wc_exp G vars e ->
      forall x, Is_free_left_ck x e ->
           Is_free_left x e \/
           exists y, exists ck', Is_free_left y e /\ In (y, ck') vars /\ Is_free_in_clock x ck'.
  Proof.
    intros * Hnormed Hwc ? Hex; induction Hnormed.
    1,2:inv Hwc; inv Hex.
    - (* merge *)
      apply Forall_singl in H4. apply Forall_singl in H5.
      simpl in *. symmetry in H9, H10. rewrite app_nil_r in H9, H10.
      repeat singleton_length.
      apply Forall_singl in H7; apply Forall_singl in H8; subst.
      destruct H0 as [?|[Hex|[Hex|Hex]]]; subst; auto.
      + apply Exists_singl in Hex.
        eapply IHHnormed1 in Hex as [?|[y [ck' [? [? ?]]]]]; auto 8.
        right. exists y. exists ck'. auto 8.
      + apply Exists_singl in Hex.
        eapply IHHnormed2 in Hex as [?|[y [ck' [? [? ?]]]]]; auto 8.
        right. exists y. exists ck'. auto 8.
      + eapply wc_normalized_cexp_clockof_free_in with (x:=x) in Hnormed1 as [?|?]; eauto 8.
        rewrite Hsingl0; repeat constructor; auto.
    - (* merge *)
      apply Forall_singl in H6. apply Forall_singl in H7.
      simpl in *. symmetry in H11, H12. rewrite app_nil_r in H11, H12.
      repeat singleton_length.
      apply Forall_singl in H9; apply Forall_singl in H10; subst.
      destruct H1 as [Hex|[Hex|[Hex|Hex]]]; subst; auto.
      + eapply wc_normalized_lexp_Is_free_left in H as [?|[y [ck' [? [? ?]]]]]; eauto 10.
      + apply Exists_singl in Hex.
        eapply IHHnormed1 in Hex as [?|[y [ck' [? [? ?]]]]]; eauto 11.
      + apply Exists_singl in Hex.
        eapply IHHnormed2 in Hex as [?|[y [ck' [? [? ?]]]]]; eauto 11.
      + eapply wc_normalized_cexp_clockof_free_in with (x:=x) in Hnormed1 as [?|[y [ck' [? [? ?]]]]]; eauto 11.
        rewrite Hsingl0; repeat constructor; auto.
    - (* lexp *)
      eapply wc_normalized_lexp_Is_free_left in Hex; eauto.
  Qed.

  Lemma wc_untupled_eq_Is_free_left : forall G vars equ,
      untupled_equation equ ->
      wc_equation G vars equ ->
      forall x, Exists (Is_free_left_ck x) (snd equ) ->
           Exists (Is_free_left x) (snd equ) \/
           exists y, exists ck', Exists (Is_free_left y) (snd equ) /\ In (y, ck') vars /\ Is_free_in_clock x ck'.
  Proof.
    intros * Hunt Hwc ? Hex; inv Hunt; simpl in *;
      apply Exists_singl in Hex; destruct Hwc as [Hwc _]; apply Forall_singl in Hwc.
    - (* app *)
      inv Hwc. inv Hex. eapply wc_normalized_lexps_Is_free_left in H; eauto.
      apply Exists_exists in H as [e [Hin [Hfree|[y [ck' [Hfree [Hin' Hfree']]]]]]].
      + left. repeat constructor.
        apply Exists_exists; eauto.
      + right. exists y. exists ck'. repeat split; auto.
        repeat constructor. apply Exists_exists; eauto.
    - (* app (reset) *)
      inv Hwc. inv Hex. inv H1; simpl in *; eauto.
      + inv H2. destruct H1 as [?|?]; subst; eauto.
        eapply wc_normalized_lexp_Is_free_left in H8 as [?|[y [ck' [? [? ?]]]]]; eauto 10.
      + eapply wc_normalized_lexps_Is_free_left in H; eauto.
        apply Exists_exists in H as [e [Hin [Hfree|[y [ck' [Hfree [Hin' Hfree']]]]]]].
        * left. do 2 constructor. right.
          apply Exists_exists; eauto.
        * right. exists y. exists ck'. repeat split; auto.
          do 2 constructor. right. apply Exists_exists; eauto.
    - (* fby *)
      inv Hwc. inv Hex.
      simpl in *. rewrite app_nil_r in *. inv H6; inv H11. inv H7; inv H11.
      destruct ann0 as (ty&ck&name); unfold clock_of_nclock, stripname in *; simpl in *.
      apply Forall_singl in H4.
      destruct H2 as [Hex|Hex]; apply Exists_singl in Hex.
      + eapply wc_normalized_lexp_Is_free_left in Hex as [?|[y [ck' [? [? ?]]]]]; eauto 10.
      + eapply wc_normalized_lexp_clockof_free_in in H as [?|[y [ck' [? [? ?]]]]]; eauto 10.
        rewrite <- H9; auto.
    - (* arrow *)
      inv Hwc. inv Hex.
      simpl in *. rewrite app_nil_r in *. inv H5; inv H10. inv H6; inv H11. inv H7; inv H11.
      destruct ann0 as (ty&ck&name); unfold clock_of_nclock, stripname in *; simpl in *.
      apply Forall_singl in H4.
      destruct H2 as [Hex|[Hex|Hex]]; apply Exists_singl in Hex.
      + eapply wc_normalized_lexp_Is_free_left in Hex as [?|[y [ck' [? [? ?]]]]]; eauto 10.
      + eapply wc_normalized_lexp_Is_free_left in Hex as [?|[y [ck' [? [? ?]]]]]; eauto 10.
      + eapply wc_normalized_lexp_clockof_free_in in H as [?|[y [ck' [? [? ?]]]]]; eauto 10.
        rewrite <- H5; auto.
    - (* cexp *)
      eapply wc_normalized_cexp_Is_free_left in H as [?|[y [ck' [? [? ?]]]]]; eauto 10.
  Qed.

  Fixpoint collect_free_in_clock (ck : clock) : list ident :=
    match ck with
    | Cbase => []
    | Con ck' id _ => id::collect_free_in_clock ck'
    end.

  Definition collect_free_in_clocks (cks : list clock) : list ident :=
    flat_map collect_free_in_clock cks.

  Fact collect_free_in_clock_In : forall ck,
      forall x, Is_free_in_clock x ck <-> In x (collect_free_in_clock ck).
  Proof.
    induction ck; intros x; split;
      intros Hin; simpl in *; inv Hin; auto.
    - right. rewrite <- IHck; auto.
    - constructor.
    - constructor. rewrite IHck; auto.
  Qed.

  Fact collect_free_in_clocks_In : forall cks,
      Forall (fun ck => forall x, Is_free_in_clock x ck -> In x (collect_free_in_clocks cks)) cks.
  Proof.
    unfold collect_free_in_clocks.
    induction cks; constructor.
    - intros x Hfree.
      rewrite flat_map_concat_map; simpl.
      apply in_or_app; left. apply collect_free_in_clock_In; auto.
    - eapply Forall_impl; eauto. intros ? Hin ? Hfree; simpl in *.
      rewrite flat_map_concat_map in *; simpl.
      apply in_or_app; right; eauto.
  Qed.

  Fact collect_free_in_clocks_In' : forall x cks,
      In x (collect_free_in_clocks cks) <->
      Exists (fun ck => Is_free_in_clock x ck) cks.
  Proof.
    unfold collect_free_in_clocks.
    induction cks; simpl; split; intro Hin. 1,2:inv Hin.
    - apply in_app_iff in Hin as [Hin|Hin].
      + left. rewrite collect_free_in_clock_In; auto.
      + right. rewrite <- IHcks; auto.
    - rewrite in_app_iff. inv Hin.
      + left. rewrite <- collect_free_in_clock_In; auto.
      + right. rewrite IHcks; auto.
  Qed.

  Fact In_anon_streams_nclocksof_normalized : forall G vars id ck es,
      Forall normalized_lexp es ->
      Forall (wc_exp G vars) es ->
      In (id, ck) (anon_streams (nclocksof es)) ->
      Exists (fun e => exists ty, e = Evar id (ty, (ck, Some id))) es.
  Proof.
    intros * Hnormed Hwc Hin.
    unfold anon_streams in Hin.
    apply map_filter_In' in Hin as [[ck' id'] [Hin Hx]].
    destruct id'; inv Hx.
    unfold nclocksof in Hin. rewrite flat_map_concat_map, in_concat in Hin.
    destruct Hin as [ncks [Hin Hin']]. simpl_In.
    eapply Forall_forall in Hnormed; eauto.
    eapply Forall_forall in Hwc; eauto.
    inv Hnormed; inv Hwc; simpl in Hin.
    1-6: destruct Hin as [Hin|Hin]; inv Hin.
    apply Exists_exists. eexists; eauto.
  Qed.

  (*
    If an equation is well-clocked on a clock ck, the variables in ck can appear
    * defined by this very equation (due to the app rule)
    * in the expression to the right of the equation
    * "pulled-in" by other variables appearing in the expression
   *)

  Fact wc_untupled_equation_clockof_free_in : forall G vars xs es,
      wc_global G ->
      NoDupMembers vars ->
      untupled_equation (xs, es) ->
      wc_equation G vars (xs, es) ->
      Forall (fun x => forall ck, In (x, ck) vars ->
                          forall ckid, Is_free_in_clock ckid ck ->
                                  In ckid xs \/
                                  Exists (Is_free_left ckid) es \/
                                  Exists (fun e => exists y, exists ck', Is_free_left y e
                                                            /\ In (y, ck') vars
                                                            /\ Is_free_in_clock ckid ck') es
             ) xs.
  Proof with eauto.
    intros * HwcG Hndup Hunt (Hwc1&Hwc2&Hwc3).
    inv Hunt.
    - (* app *)
      apply Forall_singl in Hwc1. inv Hwc1.
      simpl in *; rewrite app_nil_r in *.
      eapply WellInstantiated_is_free_in with (inputs:=collect_free_in_clocks (clocksof es0)) in H5; eauto. clear H6.
      2: { specialize (collect_free_in_clocks_In (clocksof es0)) as Hcoll.
           rewrite clocksof_nclocksof, Forall_map in Hcoll.
           eapply Forall_impl; eauto. intros [? ?] Hin ? Hfree.
           rewrite clocksof_nclocksof; eauto. }
      assert (Forall (fun x => exists a, In a lann0 /\
                                 forall ck, In (x, ck) vars ->
                                       forall ckid, Is_free_in_clock ckid ck ->
                                               In ckid xs \/
                                               Exists (Is_free_left ckid) [Eapp f es0 None lann0] \/
                                               Exists (fun e => exists y, exists ck', Is_free_left y e /\
                                                                         In (y, ck') vars /\
                                                                         Is_free_in_clock ckid ck') [Eapp f es0 None lann0]
                     ) xs) as Hf'.
      2:{ eapply Forall_impl; eauto. intros; simpl in *.
          destruct H as [? [_ ?]]; eauto. }
      eapply Forall2_ignore1' with (xs0:=xs) in H5. 2:(apply Forall2_length in Hwc2; solve_length).
      rewrite Forall2_map_2 in Hwc3. rewrite Forall2_map_2 in H5.
      eapply Forall2_Forall2 in H5; [|eapply Hwc3].
      eapply Forall2_ignore2, Forall2_impl_In; [|eapply H5].
      intros ? [? [ck' name]] Hina Hinb [Hvar Hin] ? Hvar' ? Hfree.
      assert (ck' = ck); subst.
      { eapply NoDupMembers_det in Hndup; eauto. }
      eapply Hin in Hfree as [Hin'|[Hin'|Hin']]; clear Hin.
      + eapply collect_free_in_clocks_In' in Hin'.
        eapply wc_normalized_lexps_clocksof_free_in in Hin'...
        apply Exists_exists in Hin' as [e [Hin [Hex|[y [ck' [Hex [Hin' Hfree]]]]]]].
        * right. left. repeat constructor. apply Exists_exists. eexists...
        * right. right. repeat constructor.
          exists y. exists ck'. repeat split; auto. constructor. apply Exists_exists. eexists...
      + simpl_In. destruct x as [id ck'].
        eapply In_anon_streams_nclocksof_normalized in H1...
        right. left. repeat constructor.
        rewrite Exists_exists in *. destruct H1 as [e [? [? ?]]].
        exists e; subst; auto.
      + left. apply in_map_iff in Hin' as [[? ?] [? Hin]]; subst; simpl.
        unfold anon_streams in Hin. apply map_filter_In' in Hin as [[? [?|]] [Hin Hx]]; inv Hx.
        eapply Forall2_ignore1, Forall_forall in Hwc2 as [? [? ?]]; eauto.
        inv H1; auto.
    - (* app (reset) *)
      apply Forall_singl in Hwc1. inv Hwc1.
      simpl in *; rewrite app_nil_r in *.
      eapply WellInstantiated_is_free_in with (ins:=(nclocksof es0)) (inputs:=collect_free_in_clocks (clocksof es0)) in H5; eauto. clear H6.
      2: { specialize (collect_free_in_clocks_In (clocksof es0)) as Hcoll.
           rewrite clocksof_nclocksof, Forall_map in Hcoll.
           eapply Forall_impl; eauto. intros [? ?] Hin ? Hfree.
           rewrite clocksof_nclocksof; eauto. }
      assert (Forall (fun x0 => exists a, In a lann0 /\
                                  forall ck, In (x0, ck) vars ->
                                        forall ckid, Is_free_in_clock ckid ck ->
                                                In ckid xs \/
                                                Exists (Is_free_left ckid) [Eapp f es0 (Some (Evar x (ty, cl))) lann0] \/
                                                Exists (fun e => exists y, exists ck', Is_free_left y e /\
                                                                          In (y, ck') vars /\
                                                                          Is_free_in_clock ckid ck') [Eapp f es0 (Some (Evar x (ty, cl)))lann0]
                     ) xs) as Hf'.
      2:{ solve_forall. destruct H1 as [? [_ ?]]; eauto. }
      eapply Forall2_ignore1' with (xs0:=xs) in H5. 2:(apply Forall2_length in Hwc2; solve_length).
      rewrite Forall2_map_2 in Hwc3. rewrite Forall2_map_2 in H5.
      eapply Forall2_Forall2 in H5; [|eapply Hwc3].
      eapply Forall2_ignore2, Forall2_impl_In; [|eapply H5].
      intros ? [? [ck' name]] Hina Hinb [Hvar Hin] ? Hvar' ? Hfree.
      assert (ck' = ck); subst.
      { eapply NoDupMembers_det in Hndup; eauto. }
      eapply Hin in Hfree as [Hin'|[Hin'|Hin']]; clear Hin.
      + eapply collect_free_in_clocks_In' in Hin'.
        eapply wc_normalized_lexps_clocksof_free_in in Hin'...
        apply Exists_exists in Hin' as [e [Hin [Hex|[y [ck' [Hex [Hin' Hfree]]]]]]].
        * right. left. do 2 constructor. right. apply Exists_exists. eexists...
        * right. right. repeat constructor.
          exists y. exists ck'. repeat split; auto. constructor. right. apply Exists_exists. eexists...
      + simpl_In. destruct x0 as [id ck'].
        eapply In_anon_streams_nclocksof_normalized in H1...
        right. left. do 2 constructor. right.
        rewrite Exists_exists in *. destruct H1 as [e [? [? ?]]].
        exists e; subst; auto.
      + left. apply in_map_iff in Hin' as [[? ?] [? Hin]]; subst; simpl.
        unfold anon_streams in Hin. apply map_filter_In' in Hin as [[? [?|]] [Hin Hx]]; inv Hx.
        eapply Forall2_ignore1, Forall_forall in Hwc2 as [? [? ?]]; eauto.
        inv H1; auto.
    - (* fby *)
      clear Hwc2. simpl in *.
      constructor; auto.
      intros ck Hin ? Hfree.
      apply Forall_singl in Hwc1. apply Forall2_singl in Hwc3.
      destruct ann0 as [ty [ck' name]].
      assert (ck' = ck); subst.
      { eapply NoDupMembers_det in Hndup; eauto. }
      right. inv Hwc1.
      clear H2 H5 H7. apply Forall_singl in H4.
      simpl in H6; rewrite app_nil_r, Forall2_eq in H6.
      eapply wc_normalized_lexp_clockof_free_in in H4 as [Hex|[y [ck' [Hfree' [Hin' Hex]]]]]; eauto.
      2:rewrite <- H6; auto.
      right. left. exists y. exists ck'. auto.
    - (* arrow *)
      clear Hwc2. simpl in *.
      constructor; auto.
      intros ck Hin ? Hfree.
      apply Forall_singl in Hwc1. apply Forall2_singl in Hwc3.
      destruct ann0 as [ty [ck' name]].
      assert (ck' = ck); subst.
      { eapply NoDupMembers_det in Hndup; eauto. }
      right. inv Hwc1.
      clear H2 H5 H7. apply Forall_singl in H4.
      simpl in H6; rewrite app_nil_r, Forall2_eq in H6.
      eapply wc_normalized_lexp_clockof_free_in in H4 as [Hex|[y [ck' [Hfree' [Hin' Hex]]]]]; eauto 6.
      2:rewrite <- H6; auto.
      right. left. exists y. exists ck'. auto.
    - (* cexp *)
      clear Hwc2.
      constructor; auto.
      intros ck Hin ? Hfree.
      apply Forall_singl in Hwc1.
      simpl in Hwc3; rewrite app_nil_r in Hwc3. inv Hwc3; inv H4.
      assert (y = ck); subst.
      { eapply NoDupMembers_det in Hndup; eauto. }
      right. eapply wc_normalized_cexp_clockof_free_in in Hwc1 as [HEx|[y [ck' [Hfree' [Hin' Hex']]]]]; eauto.
      2:rewrite <- H2; auto.
      right. left. exists y. exists ck'. repeat split; auto.
  Qed.

  Lemma wc_untupled_equations_clockof_causal : forall G vars inputs eqs,
      incl inputs vars ->
      NoDupMembers vars ->
      Forall untupled_equation eqs ->
      wc_global G ->
      wc_env inputs ->
      Forall (wc_equation G vars) eqs ->
      Is_causal (map fst inputs) eqs ->
      Forall (fun x => forall ck, In (x, ck) vars ->
                          forall ckid, Is_free_in_clock ckid ck ->
                                  In ckid (vars_defined eqs) \/
                                  In ckid (map fst inputs)) (vars_defined eqs).
  Proof with eauto.
    induction eqs; intros Hincl Hndup Hunt HwcG Hwenv Hwc Hcaus; inv Hunt; inv Hwc; inv Hcaus; simpl; auto.
    apply Forall_app; split; eauto.
    - destruct a as [xs es].
      specialize (wc_untupled_equation_clockof_free_in _ _ _ _ HwcG Hndup H1 H3) as Hfree.
      eapply Forall_impl; eauto. clear Hfree. intros; simpl in *.
      rewrite in_app_iff, or_assoc.
      specialize (H _ H0 _ H7) as [?|[?|Hfree]]; auto.
      apply Exists_exists in Hfree as [e [Hin [? [? [Hfree [Hinvars Hfree']]]]]].
      assert (Exists (Is_free_left x) es) as Hex.
      { rewrite Exists_exists. exists e; auto. }
      apply H6 in Hex as [Hex|Hex].
      + eapply IHeqs in H2...
        eapply Forall_forall in H2...
      + right. right.
        rewrite <- fst_InMembers in *. eapply incl_NoDup_In in Hex...
        eapply wc_env_Is_free_in_clock_In...
    - eapply IHeqs in H5; eauto.
      solve_forall. rewrite in_app_iff. eapply H0 in H4 as [?|?]...
  Qed.

  Lemma Is_causal_Is_causal_ck : forall G vars inputs eqs,
      incl inputs vars ->
      NoDupMembers vars ->
      Forall untupled_equation eqs ->
      wc_global G ->
      wc_env inputs ->
      Forall (wc_equation G vars) eqs ->
      Is_causal (map fst inputs) eqs ->
      Is_causal_ck (map fst inputs) eqs.
  Proof with eauto.
    induction eqs; intros Hincl Hndup Hunt HwcG Hwenv Hwc Hcaus; inv Hunt; inv Hwc; inv Hcaus; simpl; auto.
    constructor; auto. clear IHeqs.
    intros x Hex.
    eapply wc_untupled_eq_Is_free_left in Hex as [?|[y [ck' [? [? ?]]]]]; eauto.
    destruct a as [xs es].
    eapply H6 in H as [H|H].
    - specialize (wc_untupled_equations_clockof_causal _ _ _ _ Hincl Hndup H2 HwcG Hwenv H4 H5) as Heqs.
      eapply Forall_forall in Heqs; eauto.
    - right. rewrite <- fst_InMembers in *.
      eapply incl_NoDup_In, wc_env_Is_free_in_clock_In in H...
  Qed.

  (** ** Additional properties of Is_causal_ck *)

  Lemma Is_causal_ck_incl : forall ins1 ins2 eqs,
      incl ins1 ins2 ->
      Is_causal_ck ins1 eqs ->
      Is_causal_ck ins2 eqs.
  Proof.
    induction eqs; intros Hincl Hcaus; inv Hcaus; auto.
    constructor; auto.
    intros ? Hex. apply H2 in Hex as [?|Hex]; auto.
  Qed.

  Instance causal_ck_Proper:
    Proper (@Permutation ident ==> @eq (list equation) ==> @Basics.impl)
           Is_causal_ck.
  Proof.
    intros ? ? Hp1 ? ? Heq Hcaus; subst.
    eapply Is_causal_ck_incl; eauto.
    rewrite Hp1. reflexivity.
  Qed.

  Lemma Is_causal_ck_appr : forall eqs eqs' ins,
      Is_causal_ck ins (eqs ++ eqs') ->
      Is_causal_ck ins eqs'.
  Proof.
    induction eqs; intros * Hcaus; simpl in *; auto.
    inv Hcaus; eauto.
  Qed.

  Lemma Is_causal_ck_appl : forall eqs eqs' ins,
      Is_causal_ck ins (eqs ++ eqs') ->
      Is_causal_ck (ins++vars_defined eqs') eqs.
  Proof.
    induction eqs; intros * Hcaus; simpl in *.
    - constructor.
    - inv Hcaus. eapply IHeqs in H1. constructor; auto.
      intros x Hex. apply H2 in Hex.
      rewrite vars_defined_app in Hex. rewrite in_app_iff in *.
      destruct Hex as [[?|?]|?]; auto.
  Qed.

  Lemma Is_causal_ck_app : forall eqs eqs' ins,
      Is_causal_ck ins eqs' ->
      Is_causal_ck (ins++vars_defined eqs') eqs ->
      Is_causal_ck ins (eqs ++ eqs').
  Proof.
    induction eqs; intros * Hcaus1 Hcaus2; simpl in *.
    - auto.
    - inv Hcaus2.
      constructor; auto.
      intros x Hex. apply H2 in Hex.
      rewrite vars_defined_app. rewrite in_app_iff in *.
      destruct Hex as [?|[?|?]]; auto.
  Qed.

  Lemma Is_causal_ck_app' : forall ins eqs1 eqs2,
      Is_causal_ck ins eqs1 ->
      Is_causal_ck ins eqs2 ->
      Is_causal_ck ins (eqs1 ++ eqs2).
  Proof.
    intros * Hcaus1 Hcaus2.
    eapply Is_causal_ck_app; eauto.
    eapply Is_causal_ck_incl; eauto.
    apply incl_appl, incl_refl.
  Qed.

  Lemma Is_causal_ck_Forall : forall inputs eqs,
      Is_causal_ck inputs eqs ->
      Forall (fun eq => forall x, Exists (Is_free_left_ck x) (snd eq) -> In x (vars_defined eqs) \/ In x inputs) eqs.
  Proof.
    induction eqs; intros Hcaus; auto.
    inv Hcaus.
    constructor.
    - intros ? Hex. eapply H2 in Hex.
      simpl. rewrite in_app_iff, or_assoc. destruct Hex; auto.
    - apply IHeqs in H1. solve_forall.
      apply H0 in H1. rewrite in_app_iff, or_assoc. destruct H1; auto.
  Qed.

  Lemma Is_causal_ck_Forall' : forall inputs eqs,
      Forall (fun eq => forall x, Exists (Is_free_left_ck x) (snd eq) -> In x inputs) eqs ->
      Is_causal_ck inputs eqs.
  Proof.
    induction eqs; intros Hcaus; auto.
    inv Hcaus.
    constructor; auto.
  Qed.

  Fixpoint collect_free_left_ck (e : exp) : list ident :=
    let collect_free_lefts_ck := flat_map collect_free_left_ck in
    match e with
    | Econst _ => []
    | Evar id (_, (ck, _)) => id::(collect_free_in_clock ck)
    | Eunop _ e (_, (ck, _)) => (collect_free_left_ck e)++(collect_free_in_clock ck)
    | Ebinop _ e1 e2 (_, (ck, _)) => (collect_free_left_ck e1)++(collect_free_left_ck e2)++(collect_free_in_clock ck)
    | Efby e0s es anns =>
      (collect_free_lefts_ck e0s)++(collect_free_in_clocks (map clock_of_nclock anns))
    | Earrow e0s es anns =>
      (collect_free_lefts_ck e0s)++(collect_free_lefts_ck es)++(collect_free_in_clocks (map clock_of_nclock anns))
    | Ewhen es id _ (_, (ck, _)) =>
      id::(collect_free_lefts_ck es)++(collect_free_in_clock ck)
    | Emerge id ets efs (_, (ck, _)) =>
      id::(collect_free_lefts_ck ets)++(collect_free_lefts_ck efs)++(collect_free_in_clock ck)
    | Eite e ets efs (_, (ck, _)) =>
      (collect_free_left_ck e)++(collect_free_lefts_ck ets)++(collect_free_lefts_ck efs)++(collect_free_in_clock ck)
    | Eapp _ es None _ =>
      collect_free_lefts_ck es
    | Eapp _ es (Some r) _ =>
      (collect_free_lefts_ck es) ++ (collect_free_left_ck r)
    end.

  Definition collect_free_lefts_ck (es : list exp) :=
    flat_map collect_free_left_ck es.

  Lemma collect_free_left_ck_sound : forall e x,
      In x (collect_free_left_ck e) <-> Is_free_left_ck x e.
  Proof.
    intros e x. split; intros H.
    - induction e using exp_ind2; simpl in *. 10:destruct ro.
      Local Ltac Forall_Exists_Exists H :=
        rewrite in_flat_map' in H;
        eapply Forall_Exists in H; [|eauto];
        eapply Exists_Exists; [|eauto]; intros ? [? ?]; auto.
      + (* const *) inv H.
      + (* var *)
        destruct a as [ty [ck name]].
        inv H; auto. constructor. rewrite collect_free_in_clock_In; auto.
      + (* unop *)
        destruct a as [ty [ck name]].
        rewrite in_app_iff, <- collect_free_in_clock_In in H. destruct H; auto.
      + (* binop *)
        destruct a as [ty [ck name]].
        rewrite in_app_iff, in_app_iff, <- collect_free_in_clock_In in H. destruct H as [?|[?|?]]; auto.
      + (* fby *)
        rewrite in_app_iff in H. destruct H.
        * constructor. left. Forall_Exists_Exists H.
        * constructor. right. apply collect_free_in_clocks_In'; auto.
      + (* arrow *)
        repeat rewrite in_app_iff in H. destruct H as [H|[H|H]].
        * constructor. left. Forall_Exists_Exists H.
        * constructor. right. left. Forall_Exists_Exists H.
        * constructor. right. right. apply collect_free_in_clocks_In'; auto.
      + (* when *)
        destruct a as [tys [ck name]].
        destruct H; auto. rewrite in_app_iff, <- collect_free_in_clock_In in H; destruct H; auto.
        constructor. right. left. Forall_Exists_Exists H.
      + (* merge *)
        destruct a as [tys [ck name]].
        destruct H; auto.
        repeat rewrite in_app_iff in H. rewrite <- collect_free_in_clock_In in H.
        destruct H as [?|[?|?]]; auto.
        * constructor. right. left. Forall_Exists_Exists H.
        * constructor. right. right. left. Forall_Exists_Exists H.
      + (* ite *)
        destruct a as [tys [ck name]].
        repeat rewrite in_app_iff in H. rewrite <- collect_free_in_clock_In in H.
        destruct H as [?|[?|[?|?]]]; auto.
        * constructor. right. left. Forall_Exists_Exists H.
        * constructor. right. right. left. Forall_Exists_Exists H.
      + (* app (reset) *)
        rewrite in_app_iff in H. destruct H as [?|?]; auto.
        constructor. right. Forall_Exists_Exists H.
      + (* app *)
        constructor. Forall_Exists_Exists H.
    - induction e using exp_ind2; simpl; inv H;
        repeat rewrite in_app_iff.
      Local Ltac Forall_Exists_Exists2 H :=
        eapply Forall_Exists in H; [|eauto];
        rewrite in_flat_map';
        eapply Exists_Exists; [|eauto]; intros ? [? ?]; auto.
      + (* var *)
        destruct H1; subst; auto.
        * left; auto.
        * right. rewrite <- collect_free_in_clock_In; auto.
      + (* unop *)
        destruct H1; auto.
        right. rewrite <- collect_free_in_clock_In; auto.
      + (* binop *)
        destruct H1 as [?|[?|?]]; auto.
        right. right. rewrite <- collect_free_in_clock_In; auto.
      + (* fby *)
        rewrite collect_free_in_clocks_In'.
        destruct H3; auto.
        left. Forall_Exists_Exists2 H.
      + (* arrow *)
        rewrite collect_free_in_clocks_In'.
        destruct H3 as [?|[?|?]]; auto.
        * left. Forall_Exists_Exists2 H.
        * right. left. Forall_Exists_Exists2 H.
      + (* when *)
        simpl. rewrite in_app_iff, <- collect_free_in_clock_In.
        destruct H2 as [?|[?|?]]; auto.
        right. left. Forall_Exists_Exists2 H.
      + (* merge *)
        simpl. repeat rewrite in_app_iff. rewrite <- collect_free_in_clock_In.
        destruct H3 as [?|[?|[?|?]]]; auto.
        * right. left. Forall_Exists_Exists2 H.
        * right. right. left. Forall_Exists_Exists2 H.
      + (* ite *)
        rewrite <- collect_free_in_clock_In.
        destruct H3 as [?|[?|[?|?]]]; auto.
        * right. left. Forall_Exists_Exists2 H.
        * right. right. left. Forall_Exists_Exists2 H.
      + (* app *)
        Forall_Exists_Exists2 H3.
      + (* app (reset) *)
        inv H3; auto.
        left. Forall_Exists_Exists2 H2.
  Qed.

  Corollary collect_free_lefts_ck_sound : forall es x,
      In x (collect_free_lefts_ck es) <-> Exists (Is_free_left_ck x) es.
  Proof.
    intros es x.
    unfold collect_free_lefts_ck. rewrite flat_map_concat_map.
    split; intros.
    - apply in_concat in H as [? [Hin ?]].
      simpl_In. apply Exists_exists. exists x1. split; auto.
      rewrite collect_free_left_ck_sound in Hin; auto.
    - apply Exists_exists in H as [e [Hin Hfree]].
      eapply incl_concat_map in Hin.
      eapply Hin.
      rewrite collect_free_left_ck_sound; auto.
  Qed.

  Fact causal_insert_early' : forall dom eqs inputs,
      NoDup (vars_defined eqs++inputs) ->
      Is_causal_ck inputs eqs ->
      Forall (fun x => In x (vars_defined eqs) \/ In x inputs) dom ->
      exists eqs1, exists eqs2,
          eqs = eqs1 ++ eqs2 /\
          Forall (fun x => In x (vars_defined eqs2) \/ In x inputs) dom /\
          Forall (fun eq => not (Forall (fun x => Exists (Is_free_left_ck x) (snd eq)) dom)) eqs2.
  Proof.
    induction eqs; intros * Hndup Hcaus Hfree.
    - exists []. exists []. repeat split; simpl; auto.
    - destruct a as [xs' es']. inv Hcaus. simpl in *.
      specialize (in_dec ident_eq_dec) as Hdec.
      rewrite <- app_assoc in Hndup.
      assert (NoDup (vars_defined eqs++inputs)) as Hndup'.
      { apply NoDup_app_r in Hndup; auto. }
      specialize (IHeqs _ Hndup' H1).
      specialize (Forall_Exists_dec (fun x => ~In x xs')) with (l:=dom) as [Hdom|Hdom].
      { intros x. specialize (Hdec x xs') as [Hin|?]; auto. }
      + assert (Forall (fun x => In x (vars_defined eqs) \/ In x inputs) dom) as Hdom'.
        { solve_forall.
          rewrite in_app_iff, or_assoc in H3. destruct H3 as [?|[?|?]]; auto. contradiction. }
        specialize (IHeqs Hdom') as [eqs1 [eqs2 [? [? ?]]]]; subst.
        exists ((xs', es')::eqs1). exists eqs2. repeat split; auto.
      + exists []. eexists. repeat split; eauto.
        assert (Exists (fun x => In x xs') dom) as Hdom'.
        { eapply Exists_Exists; eauto.
          intros ? Hin; simpl in Hin. apply not_not; auto.
          apply ListDec.In_decidable. intros ? ?. apply decidable_eq_ident. } clear Hdom.
        constructor; simpl.
        * intro contra.
          simpl_forall.
          eapply Forall_Exists, Exists_exists in Hdom' as [? [_ [Hfree' Hxs']]]; eauto.
          simpl in Hfree'. destruct Hfree' as [Hfree' _]. apply H2 in Hfree'.
          eapply NoDup_app_In in Hndup; eauto.
          eapply Hndup, in_or_app; auto.
        * apply Is_causal_ck_Forall in H1.
          solve_forall. intro contra.
          solve_forall.
          eapply Forall_Exists, Exists_exists in Hdom' as [? [? [Hfree' Hxs']]]; eauto.
          simpl in Hfree'. destruct Hfree' as [Hfree' _].
          apply H0 in Hfree'.
          eapply NoDup_app_In in Hndup; eauto.
          eapply Hndup, in_or_app; auto.
  Qed.

  Lemma causal_insert_early : forall inputs eqs xs es,
      NoDup (vars_defined eqs++inputs) ->
      Is_causal_ck inputs eqs ->
      (forall x, Exists (Is_free_left_ck x) es -> In x (vars_defined eqs) \/ In x inputs) ->
      exists eqs1, exists eqs2,
          eqs = eqs1 ++ eqs2 /\
          Is_causal_ck inputs (eqs1 ++ (xs, es) :: eqs2) /\
          Forall (fun eq => (forall x, Exists (Is_free_left_ck x) es -> Exists (Is_free_left_ck x) (snd eq)) ->
                         In eq eqs1) eqs.
  Proof.
    intros * Hndup Hcaus Hfree.
    assert (Forall (fun x => In x (vars_defined eqs) \/ In x inputs) (collect_free_lefts_ck es)) as Hfree'.
    { solve_forall. eapply Hfree. rewrite collect_free_lefts_ck_sound in H; auto. }
    eapply causal_insert_early' in Hfree' as [eqs1 [eqs2 [? [Hex Hf]]]]; eauto; subst.
    exists eqs1. exists eqs2. repeat split; auto.
    apply Is_causal_ck_app.
    - constructor; eauto.
      eapply Is_causal_ck_appr in Hcaus; auto.
      intros ? Hex'. rewrite Forall_forall in Hex.
      rewrite <- collect_free_lefts_ck_sound in Hex'; eauto.
    - apply Is_causal_ck_appl in Hcaus.
      eapply Is_causal_ck_incl; [|eauto].
      simpl. apply incl_appr', incl_appr, incl_refl.
    - apply Forall_app; split.
      + apply Forall_forall. intros; auto.
      + solve_forall; simpl in *. exfalso.
        apply H0, Forall_forall. intros ? Hin.
        apply H1. rewrite collect_free_lefts_ck_sound in Hin; eauto.
  Qed.

  (** ** Causality of the second phase of normalization *)

  (** *** Recover info about the init equations in the state *)

  Definition st_inits (st : fresh_st (Op.type * clock * bool)) :=
    map (fun '(id, ((_, ck), _)) => (id, ck)) (filter (fun '(_, (ty, _, b)) => b && (ty ==b Op.bool_type)) (st_anns st)).

  Fact st_follows_inits_incl : forall st st',
      st_follows st st' ->
      incl (st_inits st) (st_inits st').
  Proof.
    intros * Hfollows.
    eapply st_follows_incl in Hfollows.
    unfold st_inits.
    apply incl_map, incl_filter; auto.
  Qed.

  Fact st_inits_find_Some : forall st x (ck : nclock) p,
      find (fun '(_, (ty, ck', isinit)) => isinit && (ck' ==b fst ck) && (ty ==b Op.bool_type)) (st_anns st) = Some (x, p) ->
      In (x, (fst ck)) (st_inits st).
  Proof.
    intros * Hfind.
    apply find_some in Hfind as [Hin Hf].
    destruct p as [[ty ck'] isinit].
    repeat rewrite Bool.andb_true_iff in Hf. destruct Hf as [[Hty Hck] ?]; auto.
    unfold st_inits. rewrite in_map_iff. exists (x, (ty, ck', isinit)); split; auto.
    - rewrite clock_eqb_eq in Hck. f_equal; auto.
    - rewrite filter_In; split; auto.
      rewrite Hty, H; auto.
  Qed.

  Fact st_inits_find_None : forall st (ck : nclock),
      find (fun '(_, (ty, ck', isinit)) => isinit && (ck' ==b fst ck) && (ty ==b Op.bool_type)) (st_anns st) = None ->
      ~In (fst ck) (map snd (st_inits st)).
  Proof.
    intros * Hfind.
    intro contra. unfold st_inits in contra. repeat simpl_In; simpl in *; inv H0; subst.
    apply filter_In in H1 as [Hin Heq].
    eapply find_none in Hfind; eauto. simpl in *.
    apply Bool.andb_true_iff in Heq as [Hb Hty]; subst; simpl in Hfind.
    rewrite Hty, equiv_decb_refl in Hfind; simpl in Hfind. congruence.
  Qed.

  Fact fresh_ident_false_st_inits : forall (st st' : fresh_st (Op.type * clock * bool)) a id,
      fresh_ident (a, false) st = (id, st') ->
      st_inits st' = st_inits st.
  Proof.
    intros * Hfresh.
    unfold st_inits. destruct a as [ty ck].
    apply fresh_ident_anns in Hfresh. rewrite Hfresh.
    simpl; auto.
  Qed.

  Fact fresh_ident_true_st_inits : forall st st' ck id,
      fresh_ident ((Op.bool_type, ck), true) st = (id, st') ->
      st_inits st' = (id, ck)::st_inits st.
  Proof.
    intros * Hfresh.
    unfold st_inits.
    apply fresh_ident_anns in Hfresh. rewrite Hfresh.
    simpl. rewrite equiv_decb_refl; auto.
  Qed.

  Fact init_var_for_clock_In_st_inits : forall ck x eqs' st st',
      init_var_for_clock ck st = (x, eqs', st') ->
      In (x, ck) (st_inits st').
  Proof.
    intros * Hinit.
    eapply init_var_for_clock_In in Hinit.
    unfold st_inits.
    simpl_In. exists (x, (Op.bool_type, ck, true)); split; auto.
    rewrite filter_In. split; auto.
    rewrite equiv_decb_refl; auto.
  Qed.

  Fact add_whens_Is_free_left : forall ck ty c,
      forall x, Is_free_left_ck x (add_whens (Econst c) ty ck) ->
           Is_free_in_clock x ck.
  Proof.
    induction ck; intros * Hfree; inv Hfree.
    destruct H0; subst; auto.
    - constructor.
    - destruct H; auto.
      apply Exists_singl in H.
      constructor; eauto.
  Qed.

  (** *** Small properties on the clocking of generated equations *)

  Fact init_var_for_clock_clocksof : forall ck id eqs' st st',
      init_var_for_clock ck st = (id, eqs', st') ->
      Forall (fun eq => clocksof (snd eq) = [ck]) eqs'.
  Proof.
    intros * Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (find _ _); repeat inv_bind.
    - destruct p; inv Hinit; auto.
    - destruct (fresh_ident _ _); inv Hinit; auto.
  Qed.

  Fact fby_iteexp_clocksof : forall e0 e ty ck name e' eqs' st st',
      fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
      Forall (fun eq => clocksof (snd eq) = [ck]) eqs'.
  Proof.
    intros * Hfby; simpl in *.
    destruct (is_constant _); repeat inv_bind; constructor; auto.
    eapply init_var_for_clock_clocksof; eauto.
  Qed.

  (** *** Perservation of weak validity *)

  Fact init_var_for_clock_weak_valid : forall inputs eqs ck x eqs' st st',
      weak_valid_after st (ps_from_list (vars_defined eqs++inputs)) ->
      init_var_for_clock ck st = (x, eqs', st') ->
      weak_valid_after st' (ps_from_list (vars_defined (eqs++eqs')++inputs)).
  Proof.
    intros * Hweak Hinit. unfold init_var_for_clock in Hinit.
    destruct (find _ _).
    - destruct p; inv Hinit. rewrite app_nil_r; auto.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
      rewrite vars_defined_app; simpl.
      eapply fresh_ident_weak_valid in Hfresh; eauto.
      rewrite (Permutation_app_comm (vars_defined _)); simpl.
      rewrite <- add_ps_from_list_cons; auto.
  Qed.

  Fact fby_iteexp_weak_valid : forall inputs eqs e0 e ty ck name e' eqs' st st',
      weak_valid_after st (ps_from_list (vars_defined eqs++inputs)) ->
      fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
      weak_valid_after st' (ps_from_list (vars_defined (eqs++eqs')++inputs)).
  Proof.
    intros * Hweak Hfby.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind.
    - rewrite app_nil_r; auto.
    - eapply init_var_for_clock_weak_valid in H; eauto.
      eapply fresh_ident_weak_valid in H0; eauto.
      rewrite vars_defined_app in *; simpl.
      rewrite <- Permutation_middle; simpl. rewrite <- add_ps_from_list_cons; auto.
  Qed.

  Fact fby_equation_weak_valid : forall to_cut inputs eq eqs eqs' st st',
      weak_valid_after st (ps_from_list (vars_defined (eq::eqs)++inputs)) ->
      fby_equation to_cut eq st = (eqs', st') ->
      weak_valid_after st' (ps_from_list (vars_defined (eqs++eqs')++inputs)).
  Proof.
    intros * Hweak Hfby.
    inv_fby_equation Hfby to_cut eq.
    - (* fby *)
      destruct x2 as [ty [ck name]]; repeat inv_bind.
      eapply fby_iteexp_weak_valid with (eqs:=([x], [Efby [x0] [x1] [(ty, (ck, name))]])::eqs) in H; simpl in *; eauto.
      destruct (PS.mem _ _); repeat inv_bind.
      + eapply fresh_ident_weak_valid in H0; eauto.
        rewrite vars_defined_app in *; simpl in *.
        rewrite <- Permutation_middle, <- Permutation_middle, perm_swap; simpl.
        rewrite <- add_ps_from_list_cons; auto.
      + rewrite vars_defined_app in *; simpl in *.
        rewrite <- Permutation_middle; auto.
    - (* arrow *)
      destruct x2 as [ty [ck name]]; repeat inv_bind.
      rewrite vars_defined_app; simpl.
      eapply init_var_for_clock_weak_valid with (eqs:=([x], [Econst Op.false_const])::eqs) in H; simpl in *; eauto.
      rewrite vars_defined_app, app_comm_cons, Permutation_middle in H; auto.
    - (* cexp *)
      rewrite vars_defined_app; simpl.
      rewrite app_nil_r, (Permutation_app_comm (vars_defined _)); auto.
  Qed.

  (** A weaker version, but useful for us *)

  Fact init_var_for_clock_weak_valid' : forall ck x eqs' st st' aft,
      weak_valid_after st aft ->
      init_var_for_clock ck st = (x, eqs', st') ->
      weak_valid_after st' aft.
  Proof.
    intros * Hweak Hinit. unfold init_var_for_clock in Hinit.
    destruct (find _ _).
    - destruct p; inv Hinit; auto.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
      eapply Facts.fresh_ident_weak_valid' in Hfresh; eauto.
  Qed.

  Fact fby_iteexp_weak_valid' : forall e0 e ty ck name e' eqs' st st' aft,
      weak_valid_after st aft ->
      fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
      weak_valid_after st' aft.
  Proof.
    intros * Hweak Hfby. unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind; auto.
    eapply init_var_for_clock_weak_valid' in H; eauto.
    eapply Facts.fresh_ident_weak_valid' in H0; eauto.
  Qed.

  (** *** With weak validity, we can get NoDup results *)

  Fact init_var_for_clock_NoDup : forall inputs eqs ck x eqs' st st',
      NoDup (vars_defined eqs++inputs) ->
      weak_valid_after st (ps_from_list (vars_defined eqs++inputs)) ->
      init_var_for_clock ck st = (x, eqs', st') ->
      NoDup (vars_defined (eqs++eqs')++inputs).
  Proof.
    intros * Hndup Hweak Hinit. unfold init_var_for_clock in Hinit.
    destruct (find _ _).
    - destruct p; inv Hinit. rewrite app_nil_r; auto.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
      rewrite vars_defined_app; simpl.
      rewrite (Permutation_app_comm (vars_defined _)); simpl.
      constructor; auto.
      eapply fresh_ident_weak_valid_nIn in Hfresh; eauto.
      rewrite ps_from_list_In in Hfresh; auto.
  Qed.

  Fact fby_iteexp_NoDup : forall inputs eqs e0 e ty ck name e' eqs' st st',
      NoDup (vars_defined eqs++inputs) ->
      weak_valid_after st (ps_from_list (vars_defined eqs++inputs)) ->
      fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
      NoDup (vars_defined (eqs++eqs')++inputs).
  Proof.
    intros * Hnd Hweak Hfby. unfold fby_iteexp in Hfby.
    destruct (is_constant _); repeat inv_bind.
    - rewrite app_nil_r; auto.
    - assert (Hnd1:=H). eapply init_var_for_clock_weak_valid in H; eauto.
      eapply init_var_for_clock_NoDup in Hnd1; eauto.
      rewrite vars_defined_app in *; simpl.
      rewrite <- Permutation_middle; simpl. constructor; auto.
      eapply fresh_ident_weak_valid_nIn in H0; eauto.
      rewrite ps_from_list_In in H0; auto.
  Qed.

  (** *** Also, ids in the valid state dont appear in the vars defined by generated equations *)

  Fact init_var_for_clock_weak_valid_nIn : forall ck x eqs' st st' id aft,
      PS.In id aft ->
      weak_valid_after st aft ->
      init_var_for_clock ck st = (x, eqs', st') ->
      ~In id (vars_defined eqs').
  Proof.
    intros * Hin Hweak Hinit contra.
    unfold init_var_for_clock in Hinit. destruct (find _ _).
    - destruct p; inv Hinit; auto.
    - destruct (fresh_ident _) eqn:Hfresh; inv Hinit; simpl in *.
      inv contra; auto.
      eapply fresh_ident_weak_valid_nIn in Hfresh; eauto.
  Qed.

  Fact fby_iteexp_weak_valid_nIn : forall e0 e a e' eqs' st st' id aft,
      PS.In id aft ->
      weak_valid_after st aft ->
      fby_iteexp e0 e a st = (e', eqs', st') ->
      ~In id (vars_defined eqs').
  Proof.
    intros * Hnin Hvalid Hfby contra. destruct a as [ty [ck name]].
    unfold fby_iteexp in Hfby.
    destruct (is_constant _); repeat inv_bind; simpl in *; auto.
    inv contra.
    - eapply fresh_ident_weak_valid_nIn in H0; eauto.
      eapply init_var_for_clock_weak_valid' in H; eauto.
    - eapply init_var_for_clock_weak_valid_nIn in H; eauto.
  Qed.

  (** *** And finally, we can keep info about what isn't in st_inits *)

  Fact init_var_for_clock_weak_valid_nIn_st_inits : forall ck x eqs' st st' id aft,
      PS.In id aft ->
      weak_valid_after st aft ->
      ~In id (map fst (st_inits st)) ->
      init_var_for_clock ck st = (x, eqs', st') ->
      ~In id (map fst (st_inits st')).
  Proof.
    intros * Hin Hweak Hnin Hinit.
    unfold init_var_for_clock in Hinit. destruct (find _ _).
    - destruct p; inv Hinit; auto.
    - destruct (fresh_ident _ _) eqn:Hfresh; inv Hinit.
      assert (Hnin':=Hfresh). eapply fresh_ident_weak_valid_nIn in Hnin'; eauto.
      eapply fresh_ident_true_st_inits in Hfresh. rewrite Hfresh.
      intro contra. inv contra; auto.
  Qed.

  Fact fby_iteexp_weak_valid_nIn_st_inits : forall e0 e a e' eqs' st st' id aft,
      PS.In id aft ->
      weak_valid_after st aft ->
      ~In id (map fst (st_inits st)) ->
      fby_iteexp e0 e a st = (e', eqs', st') ->
      ~In id (map fst (st_inits st')).
  Proof.
    intros * Hin Hweak Hnin Hfby. destruct a as [ty [ck name]].
    unfold fby_iteexp in Hfby. destruct (is_constant _); repeat inv_bind; auto.
    eapply init_var_for_clock_weak_valid_nIn_st_inits in H; eauto.
    eapply fresh_ident_false_st_inits in H0. congruence.
  Qed.

  Fact fby_equation_weak_valid_nIn_st_inits : forall to_cut eq eqs' st st' id aft,
      PS.In id aft ->
      weak_valid_after st aft ->
      ~In id (map fst (st_inits st)) ->
      fby_equation to_cut eq st = (eqs', st') ->
      ~In id (map fst (st_inits st')).
  Proof.
    intros * Hin Hweak Hnin Hfby.
    inv_fby_equation Hfby to_cut eq.
    1,2:destruct x2 as [ty [ck name]]; repeat inv_bind.
    - (* fby *)
      eapply fby_iteexp_weak_valid_nIn_st_inits with (a:=(ty, (ck, name))) in H; eauto.
      destruct (PS.mem _ _); repeat inv_bind; auto.
      eapply fresh_ident_false_st_inits in H0. congruence.
    - (* arrow *)
      eapply init_var_for_clock_weak_valid_nIn_st_inits in H; eauto.
  Qed.

  (** *** Causality invariant
      We have to talk about the causality of the whole set of equation
      (since we will be inserting init equations early).a
      The inveriant contains several part:
      * Two general no-duplication hypothesis, respectively about the vars
        defined by equations and about the st_inits
      * A strengthened causality hypothesis : the set of equations is causal,
        and the init equations appear before any equation on the same clock as them *)

  Definition is_not_app (e : exp) :=
    match e with
    | Eapp _ _ _ _ => False
    | _ => True
    end.

  Definition causal_inv inputs eqs (st : fresh_st (Op.type * clock * bool)) :=
    NoDup (vars_defined eqs ++ inputs) /\
    NoDup (map snd (st_inits st)) /\
    exists ceqs, Permutation eqs ceqs /\
            Is_causal_ck inputs ceqs /\
            Forall (fun '(x, ck) => exists eqs1, exists eqs2, exists e,
                              ceqs = eqs1 ++ ([x], [e]) :: eqs2 /\
                              clockof e = [ck] /\
                              Forall (fun eq => (exists e, snd eq = [e] /\
                                                   is_not_app e /\
                                                   clockof e = [ck]) ->
                                             In eq eqs1) (eqs1++eqs2)) (st_inits st).

  Instance causal_inv_Proper:
    Proper (@Permutation ident ==> @Permutation equation ==> @eq (fresh_st (Op.type * clock * bool)) ==> @Basics.impl)
           causal_inv.
  Proof.
    intros ? ? Hp1 ? ? Hp2 ? ? Heq Hcaus; subst.
    unfold causal_inv in *.
    destruct Hcaus as [Hndup1 [Hndup2 [ceqs [Hperm [Hcaus Hf]]]]].
    repeat (split; try exists ceqs); auto.
    - rewrite <- Hp1, <- Hp2; auto.
    - rewrite <- Hp2; auto.
    - rewrite <- Hp1; auto.
  Qed.

  Fact Is_causal_ck_causal_inv : forall inputs eqs id0,
      NoDup (vars_defined eqs ++ inputs) ->
      (exists ceqs, Permutation eqs ceqs /\
               Is_causal_ck inputs ceqs) ->
      causal_inv inputs eqs (init_st id0).
  Proof.
    intros * Hnd [ceqs [Hperm Hcaus]].
    repeat (split; try exists ceqs); auto.
    1,2: unfold st_inits; rewrite init_st_anns; simpl; constructor.
  Qed.

  Fact normalized_lexp_clockof : forall e,
      normalized_lexp e ->
      forall x, Exists (Is_free_in_clock x) (clockof e) -> Is_free_left_ck x e.
  Proof.
    intros * Hnormed ? Hex.
    inv Hnormed; simpl in *; try destruct cl as [ck name]; apply Exists_singl in Hex; auto.
    inv Hex.
  Qed.

  Fact untupled_equation_is_not_app_clockof : forall eq,
      untupled_equation eq ->
      Forall is_not_app (snd eq) ->
      forall x, Exists (Is_free_in_clock x) (clocksof (snd eq)) -> Exists (Is_free_left_ck x) (snd eq).
  Proof.
    intros eq Hunt Hisnotapp ? Hex.
    inv Hunt; simpl in *; auto.
    1,2:apply Forall_singl in Hisnotapp; inv Hisnotapp.
    constructor. inv H; simpl in *; auto.
    1,2:destruct cl as [ck ?]; apply Exists_singl in Hex; auto.
    rewrite app_nil_r in Hex.
    eapply normalized_lexp_clockof; eauto.
  Qed.

  Fact insert_in {A : Type} : forall (l1 l2 l3 l4 : list A) (x : A),
      l1 ++ l2 = l3 ++ x :: l4 ->
      In x l1 \/ In x l2.
  Proof.
    intros * Heq.
    assert (In x (l1++l2)).
    { rewrite Heq, in_app_iff. right; left; auto. }
    rewrite in_app_iff in H; auto.
  Qed.

  Fact NoDup_split {A : Type} : forall (l1 l2 l3 l4 : list A) (x : A),
      NoDup (l1 ++ x :: l2) ->
      l1 ++ x :: l2 = l3 ++ x :: l4 ->
      l1 = l3 /\ l2 = l4.
  Proof.
    induction l1; intros * Hndup Heq; simpl in *.
    - rewrite Heq in Hndup. destruct l3; simpl in *.
      2:{ exfalso.
          inv Heq. inv Hndup.
          apply H1, in_or_app. right; left; auto. }
      inv Heq; auto.
    - inv Hndup.
      destruct l3; simpl in *.
      { exfalso. inv Heq. apply H1, in_or_app. right; left; auto. }
      inv Heq.
      eapply IHl1 in H2 as [? ?]; eauto.
      split; f_equal; auto.
  Qed.

  Fact list_insert {A : Type} : forall (l1 l2 l3 l4 : list A) (x x' : A),
      NoDup (l1 ++ l2) ->
      l1 ++ l2 = l3 ++ x :: l4 ->
      exists l5, exists l6, l1 ++ x' :: l2 = l5 ++ x :: l6 /\
                  Permutation (l5 ++ l6) (x'::l3++l4) /\
                  incl l3 l5.
  Proof.
    intros * Hndup Heq.
    assert (Heq':=Heq).
    eapply insert_in in Heq as [Hin|Hin];
      eapply in_split in Hin as [l5 [l6 ?]]; subst.
    - rewrite <- app_assoc, <- app_comm_cons in *.
      eapply NoDup_split in Hndup as [? ?]; eauto; subst.
      exists l3. exists (l6++x'::l2). repeat split; auto.
      + rewrite Permutation_middle. apply Permutation_app_head.
        rewrite <- Permutation_middle. apply perm_skip. reflexivity.
      + reflexivity.
    - rewrite app_assoc in *.
      eapply NoDup_split in Hndup as [? ?]; eauto; subst.
      exists (l1 ++ x'::l5). exists l4. repeat split; auto.
      + rewrite <- app_assoc; auto.
      + rewrite <- app_assoc, <- app_comm_cons, <- Permutation_middle.
        apply perm_skip. rewrite <- app_assoc. reflexivity.
      + apply incl_appr', incl_tl, incl_refl.
  Qed.

  Fact NoDup_vars_defined : forall G eqs,
      Forall untupled_equation eqs ->
      Forall (wl_equation G) eqs ->
      NoDup (vars_defined eqs) ->
      NoDup eqs.
  Proof.
    induction eqs; intros * Hunt Hwl Hnd. constructor.
    simpl in Hnd.
    inv Hunt. inv Hwl.
    constructor.
    - intro contra. destruct a as [xs es].
      eapply untupled_equation_not_nil in H1; eauto; simpl in H1.
      destruct xs; eauto.
      eapply NoDup_app_In with (x:=i) in Hnd; simpl; eauto.
      apply Hnd. unfold vars_defined. rewrite flat_map_concat_map.
      eapply incl_concat_map; eauto; simpl; eauto.
    - apply NoDup_app_r in Hnd; auto.
  Qed.

  Fact causal_inv_insert_early : forall G inputs eqs x ck e st st',
      Forall untupled_equation eqs ->
      Forall (wl_equation G) eqs ->
      causal_inv inputs eqs st ->
      clockof e = [ck] ->
      ~In x (vars_defined eqs++inputs) ->
      ~In ck (map snd (st_inits st)) ->
      (forall x, Is_free_left_ck x e -> Is_free_in_clock x ck) ->
      (forall x, Is_free_in_clock x ck -> In x (vars_defined eqs) \/ In x inputs) ->
      st_inits st' = (x, ck)::st_inits st ->
      causal_inv inputs (eqs++[([x], [e])]) st'.
  Proof.
    intros * Hunt Hwl Hcaus Hck Hnin1 Hnin2 Hfrees Hfreesck Hinits.
    destruct Hcaus as [Hnd1 [Hnd2 [ceqs [Hperm [Hcaus Hf]]]]].
    assert (forall x, Exists (Is_free_left_ck x) [e] -> In x (vars_defined ceqs) \/ In x inputs) as Hfrees'.
    { intros ? Hex. rewrite <- Hperm. apply Exists_singl in Hex; auto. }
    eapply causal_insert_early with (xs:=[x]) in Hfrees' as [eqs1 [eqs2 [? [Hcaus' Heqs']]]]; eauto; subst.
    2:rewrite Hperm in Hnd1; auto.
    repeat (split; try exists (eqs1++([x], [e])::eqs2)); auto.
    - rewrite (Permutation_app_comm eqs _); simpl. constructor; auto.
    - rewrite Hinits. simpl. constructor; auto.
    - rewrite Permutation_app_comm, <- cons_is_app, <- Permutation_middle; auto.
    - rewrite Hinits. constructor; auto.
      + exists eqs1. exists eqs2. exists e.
        rewrite Hperm in Hunt.
        repeat split; auto.
        solve_forall; simpl in *.
        apply H0. intros ? Hex. apply Exists_singl in Hex; eauto.
        eapply Hfrees in Hex. destruct H1 as [? [Heq [Hnapp Hck']]]; subst.
        eapply untupled_equation_is_not_app_clockof in H2; simpl in *; eauto.
        rewrite app_nil_r, Hck'; auto.
      + eapply Forall_impl_In; [|eauto]. intros [? ?] ? [eqs3 [eqs4 [e' [? [? ?]]]]].
        assert (c <> ck) as Hnck.
        { intro contra; subst. apply Hnin2. simpl_In. exists (i, ck); auto. }
        rewrite H0 in Hcaus.
        assert (NoDup (eqs1++eqs2)) as Hndup'.
        { rewrite <- Hperm. eapply NoDup_vars_defined; eauto.
          apply NoDup_app_l in Hnd1; auto. }
        specialize (list_insert _ _ _ _ _ ([x], [e]) Hndup' H0) as [eqs5 [eqs6 [Hins [Hperm' Hincl]]]].
        exists eqs5. exists eqs6. exists e'. repeat split; auto. rewrite Hperm'.
        constructor; auto.
        * intros [? [? [? ?]]]; simpl in *. inv H3.
          rewrite Hck in H5. inv H5. congruence.
        * solve_forall.
  Qed.

  Fact init_var_for_clock_causal_inv : forall G inputs eqs ck x eqs' st st',
      Forall untupled_equation eqs ->
      Forall (wl_equation G) eqs ->
      (forall x, Is_free_in_clock x ck -> In x (vars_defined eqs) \/ In x inputs) ->
      weak_valid_after st (ps_from_list (vars_defined eqs++inputs)) ->
      causal_inv inputs eqs st ->
      init_var_for_clock ck st = (x, eqs', st') ->
      causal_inv inputs (eqs++eqs') st'.
  Proof.
    intros * Hunt Hwl Hck Hvalid Hinv Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (find _ _) eqn:Hfind.
    - destruct p; inv Hinit; rewrite app_nil_r; auto.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
      assert (Hfresh':=Hfresh). eapply fresh_ident_true_st_inits in Hfresh'.
      eapply causal_inv_insert_early; simpl; eauto.
      + eapply fresh_ident_weak_valid_nIn in Hfresh; eauto.
        rewrite ps_from_list_In in Hfresh; auto.
      + eapply st_inits_find_None; eauto.
      + intros * Hfree. inv Hfree.
        inv H0; apply Exists_singl in H; auto.
        eapply add_whens_Is_free_left in H; eauto.
  Qed.

  Fact fresh_ident_false_causal_inv : forall inputs eqs a x st st',
      causal_inv inputs eqs st ->
      fresh_ident (a, false) st = (x, st') ->
      causal_inv inputs eqs st'.
  Proof.
    intros * Hcaus Hfresh.
    apply fresh_ident_false_st_inits in Hfresh.
    unfold causal_inv in *. destruct Hcaus as [? [? [ceqs [? [? ?]]]]].
    repeat (split; try exists ceqs); auto. 1,2:congruence.
  Qed.

  Fact fby_iteexp_causal_inv : forall G inputs eqs e0 e ty ck name e' eqs' st st',
      Forall untupled_equation eqs ->
      Forall (wl_equation G) eqs ->
      normalized_lexp e0 ->
      clockof e0 = [ck] ->
      (forall x, Is_free_in_clock x ck -> In x (vars_defined eqs) \/ In x inputs) ->
      weak_valid_after st (ps_from_list (vars_defined eqs++inputs)) ->
      causal_inv inputs eqs st ->
      fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
      exists eqs1, exists eqs2,
          Permutation eqs' (eqs1++eqs2) /\
          causal_inv inputs (eqs++eqs1) st' /\
          Forall (fun eq => forall x, Exists (Is_free_left_ck x) (snd eq) -> Is_free_left_ck x e0) eqs2 /\
          (forall x, Is_free_left_ck x e' ->
                Is_free_left_ck x e0 \/ In (x, ck) (st_inits st') \/ In x (vars_defined eqs2)).
  Proof.
    intros * Hunt Hwl Hnormed Hck Hfreeck Hvalid [Hnd1 [Hnd2 [ceqs [Hperm [Hcaus Hf]]]]] Hfby.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind; eauto.
    - exists []. exists []. repeat rewrite app_nil_r. repeat (split; try exists ceqs); auto.
      intros ? Hfree. inv Hfree; simpl. destruct H0.
      + apply Exists_singl in H; auto.
      + unfold clock_of_nclock, stripname in H. simpl in H. rewrite <- Hck in H.
        eapply normalized_lexp_clockof in H; eauto.
    - assert (H':=H). eapply init_var_for_clock_causal_inv in H'; eauto. 2:repeat (split; try exists ceqs); auto.
      eapply fresh_ident_false_causal_inv in H'; eauto.
      remember ([x2], _) as eq2.
      exists x0; exists [eq2]; repeat (split; auto).
      + rewrite Permutation_app_comm, <- cons_is_app; auto.
      + constructor; auto.
        intros ? Hex. subst; simpl in *.
        apply Exists_singl in Hex. inv Hex. destruct H2 as [Hex|Hex].
        * apply Exists_singl, add_whens_Is_free_left in Hex.
          eapply normalized_lexp_clockof in Hnormed; eauto.
          rewrite Hck; auto.
        * eapply normalized_lexp_clockof in Hnormed; eauto.
          rewrite Hck; auto.
      + intros ? Hfree.
        inv Hfree; simpl. destruct H2 as [Hfree|[Hfree|[Hfree|Hfree]]].
        * inv Hfree. destruct H2 as [?|Hinit]; subst.
          -- eapply init_var_for_clock_In_st_inits in H; eauto.
             eapply fresh_ident_st_follows, st_follows_inits_incl in H0; auto.
          -- eapply normalized_lexp_clockof in Hnormed; eauto.
             rewrite Hck; auto.
        * apply Exists_singl in Hfree; auto.
        * apply Exists_singl in Hfree. inv Hfree. destruct H2 as [?|H2]; subst; auto.
          eapply normalized_lexp_clockof in Hnormed; eauto.
          rewrite Hck; auto.
        * eapply normalized_lexp_clockof in Hnormed; eauto.
          rewrite Hck; auto.
  Qed.

  Fact Permutation_split {A : Type} : forall (x : A) l l',
      Permutation (x::l) l' ->
      exists l1', exists l2', l' = l1' ++ x :: l2' /\ Permutation l (l1'++l2').
  Proof.
    intros * Hperm.
    assert (Hin:=Hperm). eapply Permutation_in in Hin. 2:left; auto.
    apply in_split in Hin as [l1' [l2' H]].
    exists l1'. exists l2'. split; auto.
    rewrite H, <- Permutation_middle in Hperm. apply Permutation_cons_inv in Hperm; auto.
  Qed.

  Fact Is_causal_ck_replace : forall inputs eq eqs1 eqs2 eqs',
      Is_causal_ck inputs (eqs'++eqs2) ->
      incl (vars_defined [eq]) (vars_defined eqs') ->
      Is_causal_ck inputs (eqs1 ++ eq :: eqs2) ->
      Is_causal_ck inputs (eqs1 ++ eqs' ++ eqs2).
  Proof.
    induction eqs1; intros * Hcaus1 Hincl Hcaus2; simpl in *; rewrite app_nil_r in *; auto.
    inv Hcaus2. constructor; auto.
    intros ? Hex. apply H2 in Hex.
    repeat rewrite vars_defined_app, in_app_iff in *. simpl in *.
    rewrite in_app_iff in Hex. destruct Hex as [[?|[?|?]]|?]; auto.
  Qed.

  Fact list_cut {A : Type} : forall (l1 l2 l3 l4 : list A) (x y : A),
      l1 ++ x :: l2 = l3 ++ y :: l4 ->
      NoDup (l1 ++ x :: l2) ->
      In x l3 ->
      In y l2.
  Proof.
    induction l1; intros * Heq Hnd Hin; simpl in *.
    - assert (In y (l3 ++ y :: l4)) as Hin'.
      { rewrite in_app_iff; simpl; auto. }
      assert (x <> y) as Hneq.
      { intro contra; subst. rewrite Heq in Hnd.
        eapply NoDup_app_In in Hnd; eauto. apply Hnd; left; auto. }
      rewrite <- Heq in Hin'. inv Hin'; auto. congruence.
    - destruct l3; simpl in *; inv Heq; destruct Hin; subst.
      + exfalso. inv Hnd. apply H2, in_or_app. right; left; auto.
      + inv Hnd. eapply IHl1 in H1; eauto.
  Qed.

  Fact list_cut' {A : Type} : forall (l1 l2 l3 l4 : list A) (x y : A),
      l1 ++ x :: l2 = l3 ++ y :: l4 ->
      NoDup (l1 ++ x :: l2) ->
      In x l4 ->
      In y l1.
  Proof.
    intros l1 l2 l3. revert l1 l2.
    induction l3; intros * Heq Hnd Hin; simpl in *.
    - destruct l1; simpl in *.
      + inv Heq. inv Hnd; auto.
      + inv Heq; auto.
    - destruct l1; simpl in *.
      + inv Heq. inv Hnd.
        apply H1, in_or_app. right. right. auto.
      + inv Heq. inv Hnd. apply IHl3 in H1; auto.
  Qed.

  Fact NoDup_vars_defined_In : forall x e eqs1 eqs2,
      NoDup (vars_defined(eqs1++eqs2)) ->
      In x (vars_defined eqs1) ->
      In ([x], [e]) (eqs1++eqs2) ->
      In ([x], [e]) eqs1.
  Proof.
    intros * Hnd Hin1 Hin2.
    apply in_app_iff in Hin2 as [Hin2|Hin2]; auto.
    assert (In x (vars_defined eqs2)) as Hin3.
    { unfold vars_defined. rewrite in_flat_map. exists ([x], [e]); split; simpl; auto. }
    rewrite vars_defined_app in Hnd.
    eapply NoDup_app_In in Hnd; eauto. congruence.
  Qed.

  Fact NoDup_split' {A} : forall (l1 l2 l3 l4 : list A) (x y : A),
      NoDup (l1 ++ x :: l2) ->
      x <> y ->
      l1 ++ x :: l2 = l3 ++ y :: l4 ->
      (exists l5, l3 = l1 ++ x :: l5 /\ l2 = l5 ++ y :: l4) \/
      (exists l5, l4 = l5 ++ x :: l2 /\ l1 = l3 ++ y :: l5).
  Proof.
    induction l1; intros * Hnd Hneq Heq; simpl in *.
    - destruct l3; simpl in *.
      + inv Heq; congruence.
      + inv Heq. left. exists l3; auto.
    - inv Hnd.
      destruct l3; simpl in *.
      + inv Heq. right. exists l1; auto.
      + inv Heq.
        eapply IHl1 in H3 as [[l5 [? ?]]|[l5 [? ?]]]; subst; eauto.
  Qed.

  Fact causal_replace : forall G inputs x e ck eqs eqs' st,
      Forall untupled_equation (([x], [e])::eqs) ->
      Forall (wl_equation G) (([x], [e])::eqs) ->
      is_not_app e ->
      clockof e = [ck] ->
      Forall (fun eq => clocksof (snd eq) = [ck]) eqs' ->
      (forall inputs, Is_causal_ck inputs [([x], [e])] ->
                 Is_causal_ck (inputs++map fst (filter (fun '(_, ck') => ck' ==b ck) (st_inits st))) eqs') ->
      In x (vars_defined eqs') ->
      ~In x (map fst (st_inits st)) ->
      NoDup (vars_defined (eqs' ++ eqs) ++ inputs) ->
      causal_inv inputs (([x], [e])::eqs) st ->
      causal_inv inputs (eqs'++eqs) st.
  Proof.
    intros * Hunt Hwl Hnapp Hck1 Hck2 Hcaus1 Hin Hnin Hnd [Hnd1 [Hnd2 [ceqs [Hperm [Hcaus2 Hf]]]]].
    repeat split; auto.
    apply Permutation_split in Hperm as [ceqs1 [ceqs2 [Heq Hperm']]]; subst.
    assert (NoDup (ceqs1 ++ ([x], [e]) :: ceqs2)) as Hnd'.
    { eapply NoDup_vars_defined.
        1,2,3: rewrite <- Permutation_middle, <- Hperm'; eauto.
        apply NoDup_app_l in Hnd1; auto. }
    (* since the eqs' only use the st_init based on ck, they respond to the property in Hf,
       which means the relevant st_inits are included into the vars defined by the ceqs2.
       This will be useful twice *)
    assert (Forall (fun '(x, ck') => ck' = ck -> In x (vars_defined ceqs2)) (st_inits st)) as Hinits.
    { eapply Forall_impl_In; [|eauto]. intros; destruct_conjs; clear Hf.
      intros Heq. simpl in Hck1; subst.
      destruct H0 as [eqs1 [eqs2 [? [Heq [Hck' Hf]]]]].
      assert (x <> i) as Hneq.
      { intro contra; subst. apply Hnin. simpl_In. exists (i, ck); auto. }
      assert (In ([x], [e]) (eqs1++eqs2)) as Hin'.
      { symmetry in Heq. apply insert_in in Heq; simpl in Heq.
        rewrite in_app_iff. destruct Heq as [Heq|[Heq|Heq]]; auto.
        inv Heq; congruence. }
      eapply Forall_forall in Hin'; eauto; simpl in Hin'.
      eapply list_cut in Heq; auto.
      * unfold vars_defined. rewrite flat_map_concat_map.
        apply in_concat. exists [i]; split. left; auto.
        simpl_In. exists ([i], [x0]); auto.
      * eapply Hin'. exists e; auto.
    }
    exists (ceqs1++eqs'++ceqs2). repeat split; auto.
    - rewrite Hperm', Permutation_swap; auto.
    - eapply Is_causal_ck_replace; eauto.
      2:{ simpl. intros ? Hin'. apply In_singleton in Hin'; subst; auto. }
      apply Is_causal_ck_appr in Hcaus2.
      eapply Is_causal_ck_app.
      + inv Hcaus2; auto.
      + rewrite cons_is_app in Hcaus2.
        eapply Is_causal_ck_appl, Hcaus1 in Hcaus2.
        eapply Is_causal_ck_incl; eauto.
        apply incl_app; [apply incl_refl|].
        apply incl_appr.
        intros ? Hin'. repeat simpl_In.
        rewrite filter_In in H0; destruct H0 as [Hin' Hck']. rewrite clock_eqb_eq in Hck'; subst.
        eapply Forall_forall in Hin'; eauto. simpl in *; auto.
    - solve_forall.
      destruct H1 as [eqs1 [eqs2 [? [Heq [Hck' Hf]]]]].
      (* if c = ck, then i is in ceqs2, so ([x], [e]) is in eqs1 OK ?
         if c <> ck no constraint *)
      destruct (equiv_decb c ck) eqn:Heqck.
      + rewrite clock_eqb_eq in Heqck; subst. specialize (H0 eq_refl).
        assert (In ([i], [x0]) (([x], [e])::eqs)) as Hin'.
        { rewrite Hperm', Permutation_middle. setoid_rewrite Heq.
          apply in_or_app. right. left. auto. }
        assert(Heq':=Heq). symmetry in Heq. eapply list_cut' in Heq.
        2:(setoid_rewrite Heq; auto).
        2:{ eapply NoDup_vars_defined_In with (eqs2:=(([x], [e])::ceqs1)); eauto.
            + rewrite Hperm', app_comm_cons in Hnd1. apply NoDup_app_l in Hnd1.
              rewrite vars_defined_app in *; simpl. rewrite <- Permutation_middle, Permutation_app_comm; auto.
            + rewrite <- Permutation_middle, Permutation_app_comm, <- Hperm'; auto. }
        apply in_split in Heq as [eqs3 [eqs4 Heq]]; subst.
        rewrite <- app_assoc, <- app_comm_cons in Heq'.
        apply NoDup_split in Heq' as [Heq1 Heq2]; auto; simpl in *; subst.
        exists (eqs3++eqs'++eqs4). exists eqs2. exists x0.
        repeat split; auto.
        * repeat rewrite <- app_assoc; auto.
        * simpl in Hf. repeat rewrite <- app_assoc in *.
          assert (Forall (fun equ => not (equ = ([x], [e]))) (eqs3 ++ eqs4 ++ eqs2)) as Hneq.
          { rewrite <- Permutation_middle in Hnd'. inv Hnd'.
            eapply Forall_forall. intros ? Hin'' contra; subst.
            apply H3. repeat rewrite in_app_iff in *. destruct Hin'' as [?|[?|?]]; auto.
            right. right. right. auto. }
          clear - Hf Hneq.
          repeat rewrite Forall_app in *. destruct Hf as [Hf1 [Hf2 Hf3]]. inv Hf2.
          destruct Hneq as [Hneq1 [Hneq2 Hneq3]].
          repeat split.
          1,3,4:solve_forall; repeat rewrite in_app_iff in *; simpl in *; auto.
          -- eapply H3 in H2. destruct H2 as [?|[?|?]]; auto. congruence.
          -- eapply Forall_forall. intros. repeat rewrite in_app_iff. right. left. auto.
      + rewrite clock_eqb_neq in Heqck. clear H0.
        assert (([x], [e]) <> ([i], [x0])) as Hneq.
        { intro contra. inv contra. rewrite Hck1 in Hck'. inv Hck'. congruence. }
        symmetry in Heq. eapply NoDup_split' in Heq as [[eqs5 [? ?]]|[eqs5 [? ?]]]; subst; eauto.
        3:setoid_rewrite Heq; auto.
        1: (exists eqs1; exists (eqs5++eqs'++ceqs2); exists x0). 2: (exists (ceqs1++eqs'++eqs5); exists eqs2; exists x0).
        1,2:repeat split; repeat rewrite <- app_assoc; auto.
        1,2:repeat rewrite Forall_app in *.
        * destruct Hf as [Hf1 [Hf2 Hf3]]; inv Hf3.
          repeat split; auto.
          solve_forall; simpl in *.
          destruct H4 as [? [? [? Hck'']]]; subst. simpl in H1; rewrite app_nil_r in H1.
          rewrite H1 in Hck''. inv Hck''. congruence.
        * assert (Forall (fun equ => not (equ = ([x], [e]))) (ceqs1 ++ eqs2 ++ eqs5)) as Hneq'.
          { rewrite <- (Permutation_middle ceqs1) in Hnd'. inv Hnd'.
            eapply Forall_forall. intros ? Hin'' contra; subst.
            apply H2. repeat rewrite in_app_iff in *. destruct Hin'' as [?|[?|?]]; auto.
            right. right. right. auto. }
          clear - Hf Hck2 Heqck Hneq'.
          destruct Hf as [[Hf1 Hf2] Hf3].
          repeat rewrite Forall_app in Hneq'. destruct Hneq' as [? [? ?]].
          repeat split.
          1,3,4:solve_forall; repeat rewrite in_app_iff in *; simpl in *; auto.
          -- eapply H3 in H2. destruct H2 as [?|[?|?]]; auto. congruence.
          -- solve_forall. destruct H2 as [? [? [? Hck'']]]; simpl in *; subst.
             simpl in H0; rewrite app_nil_r in H0. rewrite H0 in Hck''. inv Hck''. congruence.
  Qed.

  Fact fby_equation_causal : forall G vars to_cut inputs eq eqs eqs' st st',
      Forall untupled_equation (eq::eqs) ->
      Forall (wl_equation G) (eq::eqs) ->
      wc_equation G vars eq ->
      weak_valid_after st (ps_from_list (vars_defined (eq::eqs)++inputs)) ->
      Forall (fun id => ~In id (map fst (st_inits st))) (vars_defined [eq]) ->
      causal_inv inputs (eq::eqs) st ->
      fby_equation to_cut eq st = (eqs', st') ->
      causal_inv inputs (eqs++eqs') st'.
  Proof.
    intros * Hunt Hwl Hwc Hvalid Hnin Hinv Hfby.
    inv_fby_equation Hfby to_cut eq.
    3: { rewrite cons_is_app, Permutation_app_comm in Hinv; auto. }
    { (* fby *)
      destruct x2 as [ty [ck name]]; repeat inv_bind.
      assert (normalized_lexp x0) as Hnormed.
      { inv Hunt. inv H3; auto. inv H2. inv H1. }
      assert (clockof x0 = [ck]) as Hck.
      { destruct Hwc as [Hwc _]. apply Forall_singl in Hwc. inv Hwc; simpl in *.
        rewrite Forall2_eq, app_nil_r in H6; auto. }
      assert (weak_valid_after st (ps_from_list (vars_defined eqs++inputs))) as Hvalid2.
      { eapply weak_valid_after_Subset; eauto. rewrite <- add_ps_from_list_cons.
        apply PSP.subset_add_2. reflexivity. }
      assert (Hnd':=H). eapply fby_iteexp_NoDup in Hnd'; eauto.
      2:{ destruct Hinv as [Hnd _]; simpl in Hnd. inv Hnd; auto. }
      assert (Hfby:=H). eapply fby_iteexp_causal_inv in H as [eqs1 [eqs2 [Hperm [Hcaus [Heqs2 He']]]]]; eauto; auto.
      - destruct (PS.mem _ _); repeat inv_bind.
        + rewrite Hperm, Permutation_app_comm, (Permutation_app_comm eqs1); simpl.
          rewrite <- app_assoc, (Permutation_app_comm eqs1).
          eapply causal_replace with (eqs':=([x], [Evar x5 (ty, (ck, name))])::([x5], [x2])::eqs2) in Hcaus; simpl in *; eauto.
          2,3:rewrite app_comm_cons, Forall_app; split; eauto.
          * eapply fresh_ident_false_causal_inv; eauto.
          * eapply fby_iteexp_untupled_eq with (a:=(ty, (ck, name))) in Hfby; eauto.
            rewrite Hperm, Forall_app in Hfby; destruct Hfby; auto.
            inv Hunt. inv H2; auto. inv H1;inv H0.
          * inv Hwl. inv H2.
            apply Forall_singl in H0. inv H0; simpl in *.
            apply Forall_singl in H6. apply Forall_singl in H8.
            rewrite app_nil_r, length_annot_numstreams in *.
            eapply fby_iteexp_wl_eq with (a:=(ty, (ck, name))) in Hfby; eauto.
            rewrite Hperm, Forall_app in Hfby. destruct Hfby; auto.
          * repeat constructor; simpl.
            -- rewrite app_nil_r.
               eapply fby_iteexp_annot with (ann0:=(ty, (ck, name))) in Hfby.
               rewrite clockof_annot, Hfby; auto.
            -- eapply fby_iteexp_clocksof in Hfby; eauto.
               rewrite Hperm, Forall_app in Hfby. destruct Hfby; auto.
          * intros ? Hcaus'.
            constructor; [constructor|]; simpl; auto.
            -- inv Hcaus'. clear H2.
               eapply Is_causal_ck_Forall'.
               solve_forall; simpl in *.
               eapply H1 in H2.
               rewrite in_app_iff.
               assert (False \/ In x6 inputs0) as [Hf|?]; eauto. 2:inv Hf.
               eapply H3; auto.
            -- intros ? Hex. apply Exists_singl in Hex. apply He' in Hex.
               rewrite in_app_iff. destruct Hex as [Hex|[?|?]]; auto.
               ++ inv Hcaus'. clear H2; simpl in *.
                  assert (False \/ In x6 inputs0) as [Hf|?]; eauto. 2:inv Hf.
                  eapply H3; auto.
               ++ right. right. simpl_In.
                  exists (x6, ck); split; auto. apply filter_In; split; auto.
                  apply equiv_decb_refl.
            -- intros ? Hex. apply Exists_singl in Hex. inv Hex. destruct H1 as [?|Hex]; auto.
               inv Hcaus'; clear H2. specialize (H3 x6); simpl in H3.
               rewrite in_app_iff.
               assert (False \/ In x6 inputs0) as [Hf|?]; auto. 2:inv Hf.
               apply H3. constructor. constructor. right; simpl. constructor; auto.
          * clear - Hnin Hvalid Hfby.
            eapply fby_iteexp_weak_valid_nIn_st_inits with (a:=(ty, (ck, name))) in Hfby; eauto. 2:inv Hnin; auto.
            rewrite <- add_ps_from_list_cons. apply PSF.add_1; auto.
          * constructor; [|constructor].
            -- intro contra.
               clear Hvalid2. assert (Hfby':=Hfby). eapply fby_iteexp_weak_valid_nIn with (a:=(ty, (ck, name))) in Hfby; eauto.
               2:rewrite <- add_ps_from_list_cons; apply PSF.add_1; reflexivity.
               rewrite Hperm in Hfby.
               destruct Hcaus as [Hcaus _]. simpl in *; inv Hcaus.
               repeat rewrite vars_defined_app in *. repeat rewrite in_app_iff in *.
               destruct contra as [?|[[?|[?|?]]|?]]; subst; auto.
               eapply fresh_ident_weak_valid_nIn in H; eauto.
               2:eapply fby_iteexp_weak_valid with (eqs:=([x], [Efby [x0] [x1] [(ty, (ck, name))]])::eqs) in Hfby'; simpl in *; eauto.
               eapply H. rewrite ps_from_list_In. left; auto.
            -- eapply fby_iteexp_weak_valid in Hfby; eauto.
               eapply fresh_ident_weak_valid_nIn in H; eauto.
               rewrite ps_from_list_In, Hperm in H.
               rewrite (Permutation_app_swap eqs1), app_assoc, (Permutation_app_comm _ eqs2), <- app_assoc in H; auto.
            -- rewrite Permutation_app_comm in Hperm. rewrite Hperm, Permutation_swap in Hnd'; auto.
        + rewrite Hperm, Permutation_app_comm, (Permutation_app_comm eqs1); simpl.
          rewrite <- app_assoc, (Permutation_app_comm eqs1).
          eapply causal_replace with (eqs':=([x], [x2])::eqs2) in Hcaus; simpl in *; eauto.
          1,2:rewrite app_comm_cons, Forall_app; split; eauto.
          * eapply fby_iteexp_untupled_eq with (a:=(ty, (ck, name))) in Hfby; eauto.
            rewrite Hperm, Forall_app in Hfby; destruct Hfby; auto.
            inv Hunt. inv H1; auto. inv H0;inv H.
          * inv Hwl. inv H1.
            apply Forall_singl in H. inv H; simpl in *.
            apply Forall_singl in H5. apply Forall_singl in H7.
            rewrite app_nil_r, length_annot_numstreams in *.
            eapply fby_iteexp_wl_eq with (a:=(ty, (ck, name))) in Hfby; eauto.
            rewrite Hperm, Forall_app in Hfby. destruct Hfby; auto.
          * constructor; simpl.
            -- rewrite app_nil_r.
               eapply fby_iteexp_annot with (ann0:=(ty, (ck, name))) in Hfby.
               rewrite clockof_annot, Hfby; auto.
            -- eapply fby_iteexp_clocksof in Hfby; eauto.
               rewrite Hperm, Forall_app in Hfby. destruct Hfby; auto.
          * intros ? Hcaus'.
            constructor; auto.
            -- inv Hcaus'. clear H1.
               eapply Is_causal_ck_Forall'.
               solve_forall; simpl in *.
               eapply H0 in H1.
               assert (False \/ In x4 inputs0) as [Hf|?]; eauto. 2:inv Hf.
               eapply H2; auto. rewrite in_app_iff; auto.
            -- intros ? Hex. apply Exists_singl in Hex. apply He' in Hex.
               rewrite in_app_iff. destruct Hex as [Hex|[?|?]]; auto.
               ++ inv Hcaus'. clear H1; simpl in *.
                  assert (False \/ In x4 inputs0) as [Hf|?]; eauto. 2:inv Hf.
                  eapply H2; auto.
               ++ right. right. simpl_In.
                  exists (x4, ck); split; auto. apply filter_In; split; auto.
                  apply equiv_decb_refl.
          * clear - Hnin Hvalid Hfby.
            eapply fby_iteexp_weak_valid_nIn_st_inits with (a:=(ty, (ck, name))) in Hfby; eauto. 2:inv Hnin; auto.
            rewrite <- add_ps_from_list_cons. apply PSF.add_1; auto.
          * simpl. constructor; auto.
            -- intro contra.
               clear Hvalid2.
               eapply fby_iteexp_weak_valid_nIn with (id:=x) (a:=(ty, (ck, name))) in Hfby; [| |eauto].
               2:rewrite <- add_ps_from_list_cons. 2:apply PSF.add_1; auto.
               rewrite Hperm in Hfby.
               destruct Hcaus as [Hcaus _]. simpl in Hcaus; inv Hcaus.
               repeat rewrite vars_defined_app in *. repeat rewrite in_app_iff in *.
               destruct contra as [[?|[?|?]]|?]; auto.
            -- rewrite Permutation_app_comm in Hperm. rewrite Hperm, Permutation_swap in Hnd'; auto.
      - clear - Hinv Hck Hnormed. intros ? Hfree.
        eapply normalized_lexp_clockof in Hnormed. 2:rewrite Hck; eauto.
        destruct Hinv as [_ [_ [ceqs [Hperm [Hcaus _]]]]]. rewrite Hperm.
        eapply Permutation_in in Hperm. 2:left; eauto.
        eapply Is_causal_ck_Forall, Forall_forall in Hcaus; eauto.
        eapply Hcaus; simpl; auto. }
    { (* arrow *)
      destruct x2 as [ty [ck name]]. repeat inv_bind.
      assert (Hcaus:=H). eapply init_var_for_clock_causal_inv in Hcaus; eauto; simpl; auto.
      - eapply causal_replace with (eqs':=([x], [_])::[]) in Hcaus; simpl in *; eauto.
        + rewrite Permutation_middle in Hcaus. eassumption.
        + inv Hunt. inv H2. 2:{ inv H1. inv H0. }
          repeat constructor; eauto.
          eapply Forall_app; split; auto.
          eapply init_var_for_clock_untupled_eq in H; auto.
        + inv Hwl. inv H2. inv H0. inv H5. simpl in *. inv H7. inv H9.
          repeat constructor; eauto.
          eapply Forall_app; split; auto.
          eapply init_var_for_clock_wl in H; eauto.
        + repeat constructor.
        + intros * Hcaus'. inv Hcaus'. inv H2.
          constructor; [constructor|]; simpl.
          intros * Hex. right.
          apply Exists_singl in Hex. inv Hex.
          apply in_or_app.
          destruct H1 as [Hex|Hex].
          * inv Hex. destruct H1; subst.
            -- right.
               apply init_var_for_clock_In_st_inits in H.
               simpl_In. exists (x2, ck). split; auto.
               apply filter_In. split; auto.
               apply equiv_decb_refl.
            -- left.
               assert (In x3 (vars_defined []) \/ In x3 inputs0) as Hin.
               { apply H3. constructor; constructor; simpl; auto. }
               destruct Hin as [Hin|?]; auto. inv Hin.
          * left.
            assert (In x3 (vars_defined []) \/ In x3 inputs0) as Hin.
            { apply H3. constructor; constructor; simpl.
              destruct Hex as [Hex|[Hex|Hex]]; auto. }
            destruct Hin as [Hin|?]; auto. inv Hin.
        + inv Hnin. eapply init_var_for_clock_weak_valid_nIn_st_inits in H; eauto.
          rewrite <- add_ps_from_list_cons. apply PSF.add_1; auto.
        + destruct Hcaus as [Hcaus _]; auto.
      - intros ? Hisfree.
        destruct Hinv as [_ [_ [ceqs [Hperm [Hcaus' _]]]]].
        apply Is_causal_ck_Forall in Hcaus'. rewrite <- Hperm in Hcaus'. inv Hcaus'.
        specialize (H2 x3). rewrite <- Hperm in H2; apply H2.
        constructor. constructor. right. right. constructor; auto.
    }
  Qed.

  Fact fby_equations_causal' : forall G vars to_cut inputs eqs ceqs eqs' st st',
      Forall untupled_equation (ceqs++eqs) ->
      Forall (wl_equation G) (ceqs++eqs) ->
      Forall (wc_equation G vars) eqs ->
      weak_valid_after st (ps_from_list (vars_defined (ceqs++eqs)++inputs)) ->
      Forall (fun id => ~In id (map fst (st_inits st))) (vars_defined eqs) ->
      causal_inv inputs (ceqs++eqs) st ->
      fby_equations to_cut eqs st = (eqs', st') ->
      causal_inv inputs (ceqs++eqs') st'.
  Proof.
    induction eqs; intros * Hunt Hwl Hwc Hvalid Hnin Hinv Hfby;
      unfold fby_equations in Hfby; simpl in *; repeat inv_bind; simpl; auto.
    inv Hwc.
    rewrite <- Permutation_middle in Hinv.
    assert (Hvalid':=H). eapply fby_equation_weak_valid in Hvalid'.
    2:{ rewrite (Permutation_app_comm ceqs), <- app_comm_cons in Hvalid; eauto. }
    apply Forall_app in Hnin as [Hnin1 Hnin2].
    eapply fby_equation_causal in H as Hcaus'. 4,7:eauto.
    2,3:rewrite Permutation_middle; eauto.
    3:simpl; rewrite app_nil_r; auto. 2:rewrite Permutation_middle; auto.
    rewrite <- app_assoc, (Permutation_app_comm eqs), app_assoc in Hcaus'.
    eapply IHeqs in Hcaus'; eauto.
    - rewrite <- app_assoc in Hcaus'; eauto.
    - apply Forall_app in Hunt as [Hunt1 Hunt2]. inv Hunt2.
      repeat rewrite Forall_app. repeat split; auto.
      eapply fby_equation_untupled_eq; eauto.
    - apply Forall_app in Hwl as [Hwl1 Hwl2]. inv Hwl2.
      repeat rewrite Forall_app. repeat split; auto.
      eapply fby_equation_wl; eauto.
    - rewrite <- app_assoc in *. rewrite (Permutation_app_comm x0), app_assoc, (Permutation_app_comm ceqs), <- app_assoc; auto.
    - solve_forall. eapply fby_equation_weak_valid_nIn_st_inits in H; eauto.
      rewrite ps_from_list_In, vars_defined_app; simpl.
      repeat rewrite in_app_iff; auto.
    - unfold fby_equations; repeat inv_bind; repeat eexists; eauto; inv_bind; auto.
  Qed.

  Corollary fby_equations_causal : forall G vars to_cut inputs eqs eqs' st st',
      Forall untupled_equation eqs ->
      Forall (wc_equation G vars) eqs ->
      weak_valid_after st (ps_from_list (vars_defined eqs++inputs)) ->
      Forall (fun id => ~In id (map fst (st_inits st))) (vars_defined eqs) ->
      causal_inv inputs eqs st ->
      fby_equations to_cut eqs st = (eqs', st') ->
      causal_inv inputs eqs' st'.
  Proof.
    intros * Hunt Hwl Hvalid Hnin Hcaus Hfby.
    eapply fby_equations_causal' with (ceqs:=[]) in Hfby; simpl; eauto.
    solve_forall.
  Qed.

  Lemma normfby_node_causal : forall G n to_cut Hunt,
      wc_global G ->
      wc_node G n ->
      node_causal n ->
      node_causal (normfby_node to_cut n Hunt).
  Proof.
    intros * HwcG Hwc Hcaus.
    unfold node_causal in *; simpl.
    remember (fby_equations _ _ _) as res. symmetry in Heqres. destruct res as [eqs' st'].
    eapply fby_equations_causal with (inputs:=map fst (n_in n)) in Heqres; eauto.
    - destruct Heqres as [? [? [ceqs [Hperm [Hcaus' _]]]]].
      exists ceqs; simpl; split; auto.
      apply Is_causal_ck_Is_causal; auto.
    - destruct Hwc as [_ [_ [_ Hwc]]]; eauto.
    - eapply st_valid_weak_valid, init_st_valid.
      rewrite PS_For_all_Forall', n_defd.
      eapply Forall_incl. 1:eapply first_unused_ident_gt; reflexivity.
      rewrite <- map_app, Permutation_app_comm.
      apply incl_tl, incl_tl, incl_map, incl_appr', incl_appr', incl_appl, incl_refl.
    - eapply Forall_forall; intros ? _.
      unfold st_inits. rewrite init_st_anns. simpl; auto.
    - apply Is_causal_ck_causal_inv; auto.
      + specialize (n_nodup n) as Hnd.
        rewrite n_defd, <- map_app, <- fst_NoDupMembers, Permutation_app_comm.
        repeat rewrite app_assoc in *. apply NoDupMembers_app_l in Hnd; auto.
      + destruct Hcaus as [ceqs [Hperm Hcaus]].
        exists ceqs. split; auto.
        rewrite <- map_fst_idck.
        eapply Is_causal_Is_causal_ck; eauto.
        5:(destruct Hwc as [_ [_ [_ Hwc]]]; rewrite Hperm in Hwc; eauto).
        * unfold idck.
          apply incl_map, incl_appl, incl_refl.
        * rewrite NoDupMembers_idck.
          specialize (n_nodup n) as Hnd.
          repeat rewrite app_assoc in *. apply NoDupMembers_app_l in Hnd; auto.
        * unfold untupled_node in Hunt. rewrite <- Hperm; auto.
        * destruct Hwc; auto.
        * rewrite map_fst_idck; auto.
  Qed.

  Lemma normfby_global_causal : forall G Hunt,
      wc_global G ->
      Forall node_causal G ->
      Forall node_causal (normfby_global G Hunt).
  Proof.
    induction G; intros * Hwc Hcaus; auto.
    inv Hwc. inv Hcaus.
    constructor; eauto.
    eapply normfby_node_causal; eauto.
  Qed.

  (** ** The causality check implies causality *)

  Fact n_in_eqs_NoDupMembers : forall G n,
      untupled_node n ->
      wl_node G n ->
      NoDupMembers (n_eqs n ++ map (fun '(x, _) => ([x], [])) (n_in n)).
  Proof.
    intros * Hunt Hwl.
    unfold untupled_node in Hunt. unfold wl_node in Hwl.
    specialize (in_vars_defined_NoDup n) as Hndup.
    remember (n_eqs n) as eqs. clear Heqeqs.
    rewrite Permutation_app_comm in Hndup.
    induction eqs; simpl in *.
    - rewrite fst_NoDupMembers. rewrite map_map.
      remember (n_in n) as ins. clear Heqins.
      induction ins as [|[? [? ?]] ?]; simpl in *. constructor.
      inv Hndup. constructor; auto.
      intros contra. apply H1.
      repeat simpl_In; simpl in *; inv H.
      exists (i, (t0, c0)); auto.
    - inv Hunt. inv Hwl.
      rewrite <- app_assoc in Hndup.
      destruct a as [xs es]. constructor.
      + eapply untupled_equation_not_nil in H1; eauto; simpl in *.
        destruct xs; try congruence.
        intro contra. eapply NoDup_app_In in Hndup. 2:left; eauto.
        apply Hndup.
        rewrite fst_InMembers, map_app in contra.
        rewrite in_app_iff in *. destruct contra.
        * left. simpl_In. destruct x as [? es']; simpl in *; subst.
          unfold vars_defined. rewrite in_flat_map. exists (i::xs, es'); simpl; auto.
        * right. repeat simpl_In; simpl in *.
          inv H. exists (i, (t, c)); auto.
      + eapply IHeqs; eauto.
        apply NoDup_app_r in Hndup; auto.
  Qed.

  Fact vars_defined_incl : forall xs eqs,
      Forall2 (fun x eq => exists tl : list ident, fst eq = x :: tl) xs eqs ->
      incl xs (vars_defined eqs).
  Proof.
    induction xs; intros * Hf; inv Hf; simpl.
    - apply incl_refl.
    - apply incl_cons.
      + rewrite in_app_iff; left.
        destruct H1 as [? Hfst]. rewrite Hfst. left; auto.
      + apply incl_appr; auto.
  Qed.

  Lemma check_node_causality_correct : forall G n,
      untupled_node n ->
      wl_node G n ->
      check_node_causality n = OK tt ->
      node_causal n.
  Proof.
    intros * Hunt Hwl Hcaus. unfold check_node_causality in Hcaus.
    destruct (check_graph _) eqn:Hgraph; inv Hcaus.
    apply check_graph_spec in Hgraph.
    unfold node_causal.
    destruct Hgraph as [xs [Hperm Hord]].
    assert (exists xs, Forall2 (fun x eq => exists tl, fst eq = x::tl) xs (n_eqs n)) as [xs' Hxs'].
    { unfold untupled_node in Hunt. unfold wl_node in Hwl.
      exists (map_filter (fun eq => match (fst eq) with
                            | [] => None
                            | hd::_ => Some hd
                            end) (n_eqs n)).
      remember (n_eqs n) as eqs. clear - Hunt Hwl.
      induction eqs; simpl; auto.
      inv Hunt. inv Hwl. eapply untupled_equation_not_nil in H1; eauto.
      destruct a as [[|x xs] es]; simpl in *; try congruence.
      constructor; auto. exists xs; auto.
    }
    specialize (build_graph_dom _ _ Hxs') as Hdom.
    assert (Forall2 (fun (x : ident) (eq0 : list ident * list exp) => exists tl : list ident, fst eq0 = x :: tl)
                    (xs'++map fst (n_in n))
                    ((n_eqs n)++(map (fun '(x, _) => ([x], [])) (n_in n)))) as Hxs''.
    { eapply Forall2_app; eauto.
      rewrite Forall2_map_1, Forall2_map_2. eapply Forall2_same.
      eapply Forall_forall. intros [? [? ?]] _. exists []; simpl; auto. }
    specialize (Env.dom_elements (build_graph n)) as Hdom'.
    rewrite Hperm in Hdom'.
    assert (Permutation xs (xs' ++ map fst (n_in n))) as Hperm'.
    { eapply Env.dom_Perm; eauto.
      + rewrite <- Hperm, <- fst_NoDupMembers.
        apply Env.NoDupMembers_elements.
      + assert (NoDup xs') as Hndxs.
        { specialize (NoDup_vars_defined_n_eqs n) as Hnd.
          clear - Hxs' Hnd.
          remember (n_eqs n) as eqs. clear Heqeqs.
          revert xs' Hxs'. induction eqs; intros; inv Hxs'; constructor; simpl in *; auto.
          - destruct a. destruct H2 as [? ?]; simpl in *; subst.
            intro contra. eapply vars_defined_incl in contra; eauto.
            inv Hnd. apply not_In_app in H1 as [_ H1]; auto.
          - apply NoDup_app_r in Hnd; auto.
        }
        specialize (n_in_eqs_NoDupMembers _ _ Hunt Hwl) as Hnd.
        clear - Hxs' Hnd Hndxs.
        rewrite fst_NoDupMembers, map_app in Hnd.
        assert (forall (ins : list (ident * (Op.type * clock))) x,
                         In x (map fst ins) -> In [x] (map fst (map (fun '(x, _) => ([x], @nil exp)) ins))) as Hin.
        { intros * Hin. rewrite map_map.
          repeat simpl_In. exists (i, (t, c)); auto. }
        apply NoDup_app'; auto.
        * apply NoDup_app_r in Hnd. remember (n_in n) as ins; clear Heqins.
          induction ins as [|[? ?] ?]; simpl in *; constructor; inv Hnd; auto.
        * solve_forall. intro contra.
          eapply vars_defined_incl in H; eauto.
          specialize (in_vars_defined_NoDup n) as Hnd'.
          eapply NoDup_app_In in Hnd'; eauto.
    }
    symmetry in Hperm'. eapply Forall2_Permutation_1 in Hxs'' as [eqs' [Hperm'' Heqs']]; eauto.
    eapply WellOrdered_Is_causal in Hord; eauto.
    - exists (remove_members (list_eq_dec ident_eq_dec) (map (fun x => [x]) (map fst (n_in n))) eqs').
      split.
      + eapply remove_members_Perm with (d:=[]).
        * rewrite <- Hperm''. eapply n_in_eqs_NoDupMembers; eauto.
        * rewrite Permutation_app_comm.
          replace (map (fun x : list ident => (x, [])) (map (fun x : ident => [x]) (map fst (n_in n))))
            with (map (fun '(x, _) => ([x], @nil exp)) (n_in n)); auto.
          repeat rewrite map_map. apply map_ext. intros [? [? ?]]; auto.
      + rewrite <- app_nil_r at 1. eapply Is_causal_moves_to_input; eauto.
    - rewrite <- Hperm''. eapply build_var_map_incl.
    - rewrite <- Hperm'', Permutation_app_comm. eapply build_graph_find.
  Qed.

  Corollary check_causality_correct : forall G tts,
      untupled_global G ->
      wl_global G ->
      check_causality G = OK tts ->
      Forall node_causal G.
  Proof.
    induction G; intros * Hunt Hwl Hcheck; auto.
    inv Hunt. inv Hwl.
    unfold check_causality in Hcheck; simpl in Hcheck.
    apply bind_inversion in Hcheck as [? [? Hcheck]].
    constructor.
    + destruct x. eapply check_node_causality_correct in H; eauto.
    + apply bind_inversion in Hcheck as [? [? Hcheck]]; eauto.
  Qed.

End NCAUSALITY.

Module NCausalityFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Cau : LCAUSALITY Ids Op Syn)
       (Clo : LCLOCKING Ids Op Syn)
       (Norm : NORMALIZATION Ids Op OpAux Syn Cau)
       <: NCAUSALITY Ids Op OpAux Syn Cau Clo Norm.
  Include NCAUSALITY Ids Op OpAux Syn Cau Clo Norm.
End NCausalityFun.
