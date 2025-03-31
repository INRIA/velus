(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Coq Require Import FSets.FMapPositive.
From Coq Require Import PArith.
From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import Obc.ObcSemantics.
From Velus Require Import Obc.ObcInvariants.
From Velus Require Import Obc.ObcTyping.
From Velus Require Import Obc.Equiv.

From Velus Require Import VelusMemory.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** This pass rewrites switches that do not have a default branch to switches
    where the last branch is a default branch *)

Module Type OBCSWITCHESNORMALIZATION
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import SynObc: OBCSYNTAX     Ids Op OpAux)
       (Import ComTyp: COMMONTYPING  Ids Op OpAux)
       (Import SemObc: OBCSEMANTICS  Ids Op OpAux SynObc)
       (Import InvObc: OBCINVARIANTS Ids Op OpAux SynObc        SemObc)
       (Import TypObc: OBCTYPING     Ids Op OpAux SynObc ComTyp SemObc)
       (Import Equ   : EQUIV         Ids Op OpAux SynObc ComTyp SemObc TypObc).

  Import List.

  Definition has_default_branch: list (option stmt) -> bool :=
    existsb (or_default_with true (fun _ => false)).

  Fixpoint normalize_branches (branches: list (option stmt)) : (list (option stmt) * option stmt):=
    match branches with
    | [] => ([], None)
    | [os] => ([None], os)
    | os :: brs =>
      let (branches, lst) := normalize_branches brs in
      (os :: branches, lst)
    end.

  Definition normalize_switch (branches: list (option stmt)) (default: stmt) : (list (option stmt) * stmt) :=
    if has_default_branch branches
    then (branches, default)
    else
      let (branches, lst) := normalize_branches branches in
      (branches, or_default default lst).

  Fixpoint normalize_stmt (s: stmt): stmt :=
    match s with
    | Switch e branches default =>
      let (branches, default) := normalize_switch (map (option_map normalize_stmt) branches)
                                                  (normalize_stmt default)
      in
      Switch e branches default
    | Comp s1 s2 =>
      Comp (normalize_stmt s1) (normalize_stmt s2)
    | _ => s
    end.

  Definition normalize_method (m: method) : method :=
    match m with
      mk_method name ins vars out body nodup good =>
      mk_method name ins vars out (normalize_stmt body) nodup good
    end.

  Lemma map_m_name_normalize_method:
    forall methods,
      map m_name (map normalize_method methods) = map m_name methods.
  Proof.
    intro ms; induction ms as [|m ms]; auto.
    simpl. rewrite IHms.
    now destruct m.
  Qed.

  Program Definition normalize_class (c: class) : class :=
    match c with
      mk_class name mems objs methods nodup _ _ =>
      mk_class name mems objs (map normalize_method methods) nodup _ _
    end.
  Next Obligation.
    now rewrite map_m_name_normalize_method.
  Qed.

  Global Program Instance normalize_class_transform_unit: TransformUnit class class :=
    { transform_unit := normalize_class }.
  Next Obligation.
    unfold normalize_class; cases.
  Defined.

  Global Program Instance normalize_class_transform_state_unit: TransformStateUnit class class.
  Next Obligation.
    unfold normalize_class; cases.
  Defined.

  Definition normalize_switches : program -> program := transform_units.

  Lemma has_default_branch_true:
    forall branches,
      has_default_branch branches = true <-> Exists (fun os => os = None) branches.
  Proof.
    unfold has_default_branch; intros.
    rewrite <-Exists_existsb; try reflexivity.
    split; intros * H; subst; auto.
    destruct x; simpl in *; auto; discriminate.
  Qed.

  Corollary has_default_branch_false:
    forall branches,
      has_default_branch branches = false <-> Forall (fun os => os <> None) branches.
  Proof.
    intros; rewrite <-Bool.not_true_iff_false, has_default_branch_true, <-Forall_Exists_neg; reflexivity.
  Qed.

  Lemma normalize_branches_spec:
    forall branches,
      let (branches', default) := normalize_branches branches in
      match branches with
      | [] => branches' = []
      | _ => branches' = removelast branches ++ [None]
      end
      /\ default = last branches None.
  Proof.
    induction branches as [|? []]; simpl in *; auto; cases.
  Qed.

  Lemma normalize_stmt_eq:
    forall s,
      stmt_eval_eq (normalize_stmt s) s.
  Proof.
    induction s using stmt_ind2'; simpl; try reflexivity.
    - unfold normalize_switch.
      destruct (has_default_branch (map (Datatypes.option_map normalize_stmt) ss)) eqn: E.
      + apply stmt_eval_eq_Switch_Proper; eauto.
        apply Forall2_map_1, Forall2_same, Forall_forall.
        intros os ?; take (Forall _ _) and eapply Forall_forall in it; eauto.
        destruct os; simpl in *; constructor; auto.
      + etransitivity.
        2: { apply stmt_eval_eq_Switch_Proper; eauto.
             apply Forall2_same, Forall_forall; auto with datatypes.
        }
        apply has_default_branch_false in E.
        pose proof (normalize_branches_spec (map (Datatypes.option_map normalize_stmt) ss)) as Norm.
        destruct (normalize_branches (map (Datatypes.option_map normalize_stmt) ss)).
        destruct Norm; subst.
        Opaque removelast last.
        split; inversion_clear 1 as [| | | | |??????????? Nth|];
          destruct ss; simpl in *; subst; eauto using stmt_eval;
            rewrite <-map_cons, Forall_map in E.
        * destruct (Compare_dec.lt_eq_lt_dec c (length ss)) as [[|]|].
          -- rewrite nth_error_app1, nth_error_removelast, <-map_cons, map_nth_error' in Nth.
             ++ apply option_map_inv in Nth as (os &?&?); subst.
                econstructor; eauto.
                take (nth_error _ _ = _) and apply nth_error_In in it.
                repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
                destruct os; simpl in *; try contradiction.
                now apply it.
             ++ simpl; rewrite length_map; lia.
             ++ now rewrite length_removelast_cons, length_map.
          -- rewrite nth_error_app3 in Nth; inv Nth; simpl in *.
             ++ econstructor.
                ** eauto.
                ** erewrite app_removelast_last with (l := o :: ss) (d := None);
                     try discriminate.
                   rewrite nth_error_app3; eauto.
                   now rewrite length_removelast_cons.
                ** take (stmt_eval _ _ _ _ _) and rewrite <-map_cons in it.
                   change None with (option_map normalize_stmt None) in it.
                   rewrite CommonList.map_last in it.
                   assert (In (last (o :: ss) None) (o :: ss)) by apply last_In_cons.
                   repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
                   destruct (last (o :: ss) None); simpl in *; try contradiction.
                   now apply it.
             ++ now rewrite length_removelast_cons, length_map.
          -- contradict Nth.
             apply not_Some_is_None, nth_error_None.
             rewrite length_app, length_removelast_cons, length_map; simpl; lia.
        * pose proof Nth as Hin; apply nth_error_In in Hin.
          repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
          destruct (Compare_dec.lt_eq_lt_dec c (length ss)) as [[|]|].
          -- econstructor; eauto.
             ++ rewrite nth_error_app1, nth_error_removelast, <-map_cons,
                map_nth_error', Nth; simpl; eauto.
                ** rewrite length_map; lia.
                ** now rewrite length_removelast_cons, length_map.
             ++ destruct s0; simpl in *; try contradiction.
                now apply it.
          -- rewrite nth_error_last with (d := None) in Nth; auto.
             inv Nth.
             econstructor; eauto.
             ++ rewrite nth_error_app3; eauto.
                now rewrite length_removelast_cons, length_map.
             ++ simpl.
                rewrite <-map_cons.
                change None with (option_map normalize_stmt None).
                rewrite CommonList.map_last.
                destruct (last (o :: ss) None); simpl in *; try contradiction.
                now apply it.
          -- contradict Nth.
             apply not_Some_is_None, nth_error_None.
             simpl; lia.
    - now rewrite IHs1, IHs2.
  Qed.

  Lemma normalize_switches_find_class:
    forall p id c p',
      find_class id p = Some (c, p') ->
      find_class id (normalize_switches p) = Some (normalize_class c, normalize_switches p').
  Proof.
    intros * Find; apply find_unit_transform_units_forward in Find; auto.
  Qed.

  Lemma normalize_class_c_objs:
    forall c,
      (normalize_class c).(c_objs) = c.(c_objs).
  Proof.
    unfold normalize_class. destruct c; auto.
  Qed.

  Lemma normalize_method_m_name:
    forall m, (normalize_method m).(m_name) = m.(m_name).
  Proof. destruct m; auto. Qed.

  Lemma normalize_method_in:
    forall m, (normalize_method m).(m_in) = m.(m_in).
  Proof. destruct m; auto. Qed.

  Lemma normalize_method_out:
    forall m, (normalize_method m).(m_out) = m.(m_out).
  Proof. destruct m; auto. Qed.

  Lemma normalize_method_body:
    forall fm,
      (normalize_method fm).(m_body) = normalize_stmt fm.(m_body).
  Proof.
    now destruct fm.
  Qed.

  Lemma normalize_switches_find_method:
    forall f fm cls,
      find_method f cls.(c_methods) = Some fm ->
      find_method f (normalize_class cls).(c_methods) = Some (normalize_method fm).
  Proof.
    destruct cls; simpl.
    induction c_methods0 as [|m ms]; inversion 1.
    simpl.
    destruct (ident_eq_dec m.(m_name) f) as [He|Hne].
    - rewrite normalize_method_m_name, He, ident_eqb_refl in *.
      now injection H1; intro; subst.
    - apply ident_eqb_neq in Hne.
      rewrite normalize_method_m_name, Hne in *.
      inv c_nodupm0; auto.
  Qed.

  Lemma normalize_switches_call:
    forall p n me me' f xss rs,
      stmt_call_eval p me n f xss me' rs ->
      stmt_call_eval (normalize_switches p) me n f xss me' rs.
  Proof.
    cut ((forall p me ve stmt e',
             stmt_eval p me ve stmt e' ->
             stmt_eval (normalize_switches p) me ve stmt e')
         /\ (forall p me clsid f vs me' rvs,
                stmt_call_eval p me clsid f vs me' rvs ->
                stmt_call_eval (normalize_switches p) me clsid f vs me' rvs)).
    now destruct 1 as (Hf1 & Hf2); intros; apply Hf2; auto.
    apply stmt_eval_call_ind; intros; eauto using stmt_eval.
    take (find_class _ _ = _) and rename it into Find.
    take (find_method _ _ = _) and rename it into Findm.
    apply normalize_switches_find_class in Find.
    apply normalize_switches_find_method in Findm.
    econstructor; eauto.
    - now rewrite normalize_method_in.
    - rewrite normalize_method_in.
      rewrite normalize_method_body.
      rewrite normalize_stmt_eq; eauto.
    - now rewrite normalize_method_out; eassumption.
  Qed.

  Corollary normalize_switches_loop_call:
    forall f c ins outs prog me,
      loop_call prog c f ins outs 0 me ->
      loop_call (normalize_switches prog) c f ins outs 0 me.
  Proof.
    intros ?????; generalize 0%nat.
    cofix COINDHYP.
    intros n me Hdo.
    destruct Hdo.
    econstructor; eauto using normalize_switches_call.
  Qed.

  (** ** Switches normalization preserves well-typing. *)

  Lemma wt_exp_normalize_switches:
    forall p Γm Γv e,
      wt_exp p Γm Γv e ->
      wt_exp (normalize_switches p) Γm Γv e.
  Proof.
    induction e; inversion_clear 1; eauto using wt_exp.
  Qed.

  Lemma wt_stmt_normalize_switches:
    forall p insts Γm Γv s,
      wt_stmt p insts Γm Γv s ->
      wt_stmt (normalize_switches p) insts Γm Γv s.
  Proof.
    induction s using stmt_ind2'; inversion_clear 1; eauto using wt_exp_normalize_switches, wt_stmt.
    - econstructor; eauto using wt_exp_normalize_switches.
      intros * Hin.
      take (Forall _ _) and eapply Forall_forall in it; eauto; simpl in *; eauto.
    - eapply wt_Call
        with (cls:=normalize_class cls) (p':=normalize_switches p') (fm:=normalize_method fm);
        auto; try (now destruct fm; auto).
      + erewrite normalize_switches_find_class; eauto.
      + now apply normalize_switches_find_method.
      + apply Forall_forall; intros * Hin.
        take (Forall _ _) and eapply Forall_forall in it; eauto using wt_exp_normalize_switches.
    - econstructor; simpl_Forall; eauto using wt_exp_normalize_switches.
  Qed.

  Lemma wt_normalize_stmt:
    forall p insts Γm Γv s,
      wt_stmt p insts Γm Γv s ->
      wt_stmt p insts Γm Γv (normalize_stmt s).
  Proof.
    intros * WTs.
    induction s using stmt_ind2'; simpl; inv WTs; eauto using wt_stmt.
    unfold normalize_switch.
    destruct (has_default_branch (map (option_map normalize_stmt) ss)) eqn: E.
    - econstructor; eauto.
      + now rewrite length_map.
      + intros * Hin; apply in_map_iff in Hin as (?& Eq & Hin).
        pose proof Hin.
        apply option_map_inv in Eq as (?&?&?); subst.
        eapply Forall_forall in Hin; eauto; simpl in *.
        apply Hin; auto.
    - pose proof (normalize_branches_spec (map (option_map normalize_stmt) ss)) as Eq.
      destruct (normalize_branches (map (option_map normalize_stmt) ss)).
      destruct Eq; subst.
      econstructor; eauto.
      + destruct ss; simpl in *; subst; simpl; auto.
        rewrite length_app, length_removelast_cons, length_map; simpl; lia.
      + destruct ss; simpl in *.
        * Transparent last.
          simpl; auto.
        * change None with (option_map normalize_stmt None).
          rewrite <-map_cons, CommonList.map_last.
          pose proof (last_In_cons ss o None) as Hin.
          pose proof Hin.
          eapply Forall_forall in Hin; eauto.
          destruct (last (o :: ss) None); simpl in *; auto.
      + destruct ss.
        * simpl in *; subst; contradiction.
        * take (forall s, _ -> _) and setoid_rewrite app_removelast_last with (l := o:: ss) (d := None) in it;
            try discriminate.
          intros * Hin.
          simpl in *; subst.
          apply in_app in Hin as [Hin|Hin]; [|inv Hin; [discriminate|contradiction]].
          rewrite <-map_cons, map_removelast in Hin.
          apply in_map_iff in Hin as (?& Eq & Hin); subst.
          take (Forall _ _) and rewrite app_removelast_last with (l := o:: ss) (d := None) in it;
            try discriminate.
          apply Forall_app in it as [WT].
          eapply Forall_forall in WT; eauto.
          apply option_map_inv in Eq as (?&?&?); subst; simpl in *.
          apply WT.
          take (forall s, _ -> _) and apply it.
          apply in_app; auto.
  Qed.

  Lemma meth_vars_normalize_method:
    forall m,
      meth_vars (normalize_method m) = meth_vars m.
  Proof.
    unfold meth_vars; destruct m; auto.
  Qed.

  Lemma normalize_switches_wt_program:
    forall p,
      wt_program p ->
      wt_program (normalize_switches p).
  Proof.
    intros * WT.
    eapply transform_units_wt_program in WT; eauto; simpl.
    inversion_clear 1 as (Hos & Hms).
    constructor.
    - rewrite normalize_class_c_objs.
      apply Forall_impl_In with (2:=Hos).
      intros ic Hin Hfind.
      apply not_None_is_Some in Hfind.
      destruct Hfind as ((cls & p') & Hfind).
      apply normalize_switches_find_class in Hfind; unfold normalize_switches in Hfind; simpl in *.
      setoid_rewrite Hfind.
      discriminate.
    - destruct u; simpl in *.
      clear c_nodup0 c_nodupm0 Hos.
      induction c_methods0 as [|m ms]; simpl; auto using Forall_nil.
      apply Forall_cons2 in Hms.
      destruct Hms as ((WTm & Henums) & WTms).
      apply Forall_cons; auto. clear IHms WTms.
      split; rewrite meth_vars_normalize_method; simpl; auto.
      destruct m; simpl in *.
      apply wt_normalize_stmt; eauto.
      apply wt_stmt_normalize_switches in WTm; auto.
  Qed.

  Lemma normalize_switches_wt_memory:
    forall me p c,
      wt_memory me p c.(c_mems) c.(c_objs) ->
      wt_memory me (normalize_switches p) (normalize_class c).(c_mems) (normalize_class c).(c_objs).
  Proof.
    intros * WT.
    pose proof transform_units_wt_memory' as Spec; simpl in Spec.
    apply Spec in WT; auto.
  Qed.

  (** ** Switches normalization preserves [Can_write_in]. *)

  Lemma Can_write_in_var_normalize_stmt:
    forall s x ,
      Can_write_in_var x s <-> Can_write_in_var x (normalize_stmt s).
  Proof.
    induction s using stmt_ind2; simpl; try reflexivity.
    - split.
      + inversion_clear 1.
        take (Exists _ _) and apply Exists_exists in it as (os & Hin & CW).
        take (Forall _ _) and eapply Forall_forall in it; eauto.
        apply it in CW.
        unfold normalize_switch.
        destruct (has_default_branch (map (option_map normalize_stmt) ss)) eqn: E.
        * constructor; apply Exists_exists.
          eexists; split.
          -- apply in_map; eauto.
          -- destruct os; simpl in *; auto.
        * eapply has_default_branch_false in E.
          rewrite Forall_map in E; eapply Forall_forall in E; eauto.
          pose proof (normalize_branches_spec (map (option_map normalize_stmt) ss)) as Eq.
          destruct (normalize_branches (map (option_map normalize_stmt) ss)).
          destruct Eq; subst.
          constructor; apply Exists_exists.
          destruct ss; try contradiction.
          rewrite app_removelast_last with (l := o :: ss) (d := None) in Hin; try discriminate.
          Opaque last.
          simpl in *; subst.
          rewrite <-map_cons, map_removelast.
          apply in_app in Hin as [Hin|Hin].
          -- eexists; split.
             ++ apply in_app; left.
                eapply in_map; eauto.
             ++ destruct os; simpl in *; auto; contradiction.
          -- exists None; split; simpl.
             ++ apply in_app; auto using in_eq.
             ++ change None with (option_map normalize_stmt None).
                rewrite <-map_cons, CommonList.map_last.
                inv Hin; try contradiction.
                destruct (last (o :: ss) None); try contradiction; simpl in *; auto.
      + unfold normalize_switch.
        intro CW; constructor; apply Exists_exists.
        destruct (has_default_branch (map (option_map normalize_stmt) ss)) eqn: E.
        * inv CW.
          take (Exists _ _) and apply Exists_exists in it as (os & Hin & CW).
          apply in_map_iff in Hin as (os' &?&?); subst.
          take (Forall _ _) and eapply Forall_forall in it; eauto.
          eexists; split; eauto.
          destruct os'; simpl in *; now apply it.
        * eapply has_default_branch_false in E.
          pose proof (normalize_branches_spec (map (option_map normalize_stmt) ss)) as Eq.
          destruct (normalize_branches (map (option_map normalize_stmt) ss)).
          destruct Eq; subst.
          inv CW.
          take (Exists _ _) and apply Exists_exists in it as (os & Hin & CW).
          destruct ss.
          -- simpl in *; subst; contradiction.
          -- rewrite app_removelast_last with (l := o :: ss) (d := None); try discriminate.
             rewrite app_removelast_last with (l := o :: ss) (d := None) in E; try discriminate.
             take (Forall _ (_ :: _)) and rewrite app_removelast_last with (l := o :: ss) (d := None) in it;
               try discriminate; apply Forall_app in it as [IH1 IH2].
             rewrite Forall_map in E; apply Forall_app in E as [E1 E2].
             simpl in *; subst.
             apply in_app in Hin as [Hin|Hin]; [|inv Hin; try contradiction].
             ++ rewrite <-map_cons, map_removelast in Hin.
                apply in_map_iff in Hin as (os' &?& Hin); subst.
                eapply Forall_forall in IH1; eauto.
                eapply Forall_forall in E1; eauto.
                eexists; split.
                ** apply in_app; eauto.
                ** rewrite IH1.
                   destruct os'; simpl in *; auto; contradiction.
             ++ simpl in *.
                inv IH2; inv E2.
                eexists; split.
                ** apply in_app; auto using in_eq.
                ** change None with (option_map normalize_stmt None) in CW.
                   rewrite <-map_cons, CommonList.map_last in CW.
                   destruct (last (o :: ss) None); simpl in *; try contradiction.
                   take (forall x, _ <-> _) and now apply it.
    - intro; rewrite 2 Can_write_in_var_Comp, IHs1, IHs2; reflexivity.
  Qed.

  Lemma normalize_switches_cannot_write_inputs:
    forall p,
      wt_program p ->
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in_var x (m_body m)) (map fst (m_in m))) p ->
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in_var x (m_body m)) (map fst (m_in m)))
                     (normalize_switches p).
  Proof.
    intros * WTp HH.
    apply Forall_forall; intros * Hin;
      apply Forall_forall; intros * Hin';
        apply Forall_forall; intros ? Hin''.
    apply in_map_iff in Hin as (c &?& Hin); subst.
    edestruct In_find_unit as (?& Find); eauto using wt_program_nodup_classes.
    eapply wt_program_find_unit in Find as (WTc & ?); eauto; destruct WTc as (?& WTms).
    eapply Forall_forall in HH; eauto.
    destruct c; simpl in *.
    apply in_map_iff in Hin' as (m &?&?); subst.
    eapply Forall_forall in HH; eauto.
    eapply Forall_forall in WTms; eauto.
    destruct m; simpl in *.
    eapply Forall_forall in HH; eauto.
    rewrite <-Can_write_in_var_normalize_stmt; eauto.
  Qed.

  (** ** Switches normalization preserves [No_Overwrites]. *)

  Lemma No_Overwrites_normalize_stmt:
    forall s,
      No_Overwrites s ->
      No_Overwrites (normalize_stmt s).
  Proof.
    induction s using stmt_ind2; simpl; auto; inversion_clear 1.
    - unfold normalize_switch.
      destruct (has_default_branch (map (option_map normalize_stmt) ss)) eqn: E.
      + constructor.
        apply Forall_map, Forall_forall; intros os Hin.
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
        destruct os; simpl in *; auto.
      + apply has_default_branch_false in E.
        rewrite Forall_map in E.
        pose proof (normalize_branches_spec (map (option_map normalize_stmt) ss)) as Eq.
        destruct (normalize_branches (map (option_map normalize_stmt) ss)); destruct Eq; subst.
        constructor.
        destruct ss; simpl in *; subst; auto.
        repeat (take (Forall _ (_ :: _)) and rewrite app_removelast_last with (l := o :: ss) (d := None) in it;
                try discriminate; apply Forall_app in it).
        repeat (take (_ /\ _) and destruct it).
        apply Forall_app; split.
        * rewrite <-map_cons, map_removelast, Forall_map.
          apply Forall_forall; intros os Hin.
          repeat (take (Forall _ (removelast _)) and eapply Forall_forall in it; eauto).
          destruct os; simpl in *; auto; contradiction.
        * constructor; auto.
          simpl.
          change None with (option_map normalize_stmt None).
          rewrite <-map_cons, CommonList.map_last.
          repeat (take (Forall _ [_]) and inv it).
          destruct (last (o :: ss) None); simpl in *; auto.
    - constructor; auto; setoid_rewrite <- Can_write_in_var_normalize_stmt; auto.
  Qed.

  Lemma normalize_switches_No_Overwrites:
    forall p,
      wt_program p ->
      Forall_methods (fun m => No_Overwrites (m_body m)) p ->
      Forall_methods (fun m => No_Overwrites (m_body m)) (normalize_switches p).
  Proof.
    intros * WTp HH.
    apply Forall_forall; intros * Hin;
      apply Forall_forall; intros * Hin'.
    apply in_map_iff in Hin as (c &?&?); subst.
    edestruct In_find_unit as (?& Find); eauto using wt_program_nodup_classes.
    eapply wt_program_find_unit in Find as (WTc & ?); eauto; destruct WTc as (?& WTms).
    eapply Forall_forall in HH; eauto.
    destruct c; simpl in *.
    apply in_map_iff in Hin' as (m &?& Hin'); subst.
    eapply Forall_forall with (2 := Hin') in HH; eauto.
    eapply Forall_forall in WTms; eauto.
    destruct m; simpl in *.
    eapply No_Overwrites_normalize_stmt; eauto.
  Qed.

End OBCSWITCHESNORMALIZATION.

Module ObcSwitchesNormalizationFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (SynObc: OBCSYNTAX     Ids Op OpAux)
       (ComTyp: COMMONTYPING  Ids Op OpAux)
       (SemObc: OBCSEMANTICS  Ids Op OpAux SynObc)
       (InvObc: OBCINVARIANTS Ids Op OpAux SynObc        SemObc)
       (TypObc: OBCTYPING     Ids Op OpAux SynObc ComTyp SemObc)
       (Equ   : EQUIV         Ids Op OpAux SynObc ComTyp SemObc TypObc)
<: OBCSWITCHESNORMALIZATION Ids Op OpAux SynObc ComTyp SemObc InvObc TypObc Equ.
  Include OBCSWITCHESNORMALIZATION Ids Op OpAux SynObc ComTyp SemObc InvObc TypObc Equ.
End ObcSwitchesNormalizationFun.
