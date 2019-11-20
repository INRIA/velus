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

From Velus Require Import Stc.
From Velus Require Import Obc.

From Velus Require Import StcToObc.Translation.

From Velus Require Import VelusMemory.
From Velus Require Import Common.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Permutation.

Open Scope nat.
Open Scope list.

Module Type STC2OBCTYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import Str   : INDEXEDSTREAMS  Op OpAux)
       (Import CE    : COREEXPR    Ids Op OpAux Str)
       (Import Stc   : STC         Ids Op OpAux Str CE)
       (Import Obc   : OBC         Ids Op OpAux)
       (Import Trans : TRANSLATION Ids Op OpAux CE.Syn Stc.Syn Obc.Syn).

  Lemma wt_stmt_fold_left_shift:
    forall A xs P insts mems vars (f: A -> stmt) acc,
      wt_stmt P insts mems vars (fold_left (fun s x => Comp (f x) s) xs acc) <->
      wt_stmt P insts mems vars (fold_left (fun s (x : A) => Comp (f x) s) xs Skip)
      /\ wt_stmt P insts mems vars acc.
  Proof.
    induction xs; simpl; split; try now intuition eauto using wt_stmt.
    - rewrite IHxs; intros (?& WT); inv WT.
      rewrite IHxs; intuition.
    - rewrite IHxs; intros ((?& WT) &?); inv WT.
      rewrite IHxs; intuition.
  Qed.

  Lemma wt_stmt_fold_left_lift:
    forall A xs P insts mems vars (f: A -> stmt) acc,
      wt_stmt P insts mems vars (fold_left (fun s x => Comp s (f x)) xs acc) <->
      wt_stmt P insts mems vars (fold_left (fun s (x : A) => Comp s (f x)) xs Skip)
      /\ wt_stmt P insts mems vars acc.
  Proof.
    induction xs; simpl; split; try now intuition eauto using wt_stmt.
    - rewrite IHxs; intros (?& WT); inv WT.
      rewrite IHxs; intuition.
    - rewrite IHxs; intros ((?& WT) &?); inv WT.
      rewrite IHxs; intuition.
  Qed.

  Section Expressions.

    Variable nvars  : list (ident * type).
    Variable mems   : list (ident * type).
    Variable vars   : list (ident * type).
    Variable memset : PS.t.

    Hypothesis NvarsSpec:
      forall x ty,
        In (x, ty) nvars ->
        if PS.mem x memset then In (x, ty) mems else In (x, ty) vars.

    Ltac FromMemset :=
      match goal with
      | H: In (?x, _) nvars |- context [ bool_var memset ?x ] =>
        unfold bool_var; simpl;
        apply NvarsSpec in H; cases
      | H: In (?x, _) nvars |- context [ PS.mem ?x memset ] =>
        apply NvarsSpec in H; cases
      end.

    Lemma translate_exp_wt:
      forall e,
        CE.Typ.wt_exp nvars e ->
        wt_exp mems vars (translate_exp memset e).
    Proof.
      induction e; simpl; intro WTle; inv WTle; auto using wt_exp.
      - FromMemset; eauto using wt_exp.
      - constructor; auto; now rewrite typeof_correct.
      - constructor; auto; now rewrite 2 typeof_correct.
    Qed.
    Hint Resolve translate_exp_wt.

    Corollary translate_arg_wt:
      forall e clkvars ck,
        CE.Typ.wt_exp nvars e ->
        wt_exp mems vars (translate_arg memset clkvars ck e).
    Proof.
      unfold translate_arg, var_on_base_clock; intros * WT.
      inv WT; auto; simpl.
      apply NvarsSpec in H; destruct (PS.mem x memset); simpl; auto using wt_exp.
      cases; auto using wt_exp.
    Qed.
    Hint Resolve translate_arg_wt.

    Remark typeof_bool_var_is_bool_type:
      forall x,
        typeof (bool_var memset x) = bool_type.
    Proof.
      unfold bool_var; intros; simpl; cases.
    Qed.
    Hint Resolve typeof_bool_var_is_bool_type.

    Lemma translate_cexp_wt:
      forall p insts x e,
        wt_cexp nvars e ->
        In (x, typeofc e) vars ->
        wt_stmt p insts mems vars (translate_cexp memset x e).
    Proof.
      induction e; simpl; intros WTe Hv; inv WTe.
      - match goal with H:typeofc e1 = typeofc e2 |- _ => rewrite <-H in * end.
        FromMemset; eauto using wt_stmt, wt_exp.
      - assert (Hv' := Hv).
        match goal with H:typeofc _ = typeofc _ |- _ => rewrite H in Hv' end.
        constructor; auto.
        now rewrite typeof_correct.
      - constructor; auto.
        now rewrite typeof_correct.
    Qed.

    Lemma Control_wt:
      forall p insts ck s,
        wt_clock nvars ck ->
        wt_stmt p insts mems vars s ->
        wt_stmt p insts mems vars (Control memset ck s).
    Proof.
      induction ck; intros s WTc WTs;
        inversion_clear WTc as [|??? Hin]; auto.
      destruct b; simpl; eauto; FromMemset; eauto using wt_stmt, wt_exp.
    Qed.

  End Expressions.
  Hint Resolve translate_exp_wt translate_cexp_wt Control_wt.

  Lemma step_wt:
    forall P s,
      wt_system P s ->
      wt_method (translate P) (s_subs s)
                (map (fun xc : ident * (const * clock) => (fst xc, type_const (fst (snd xc)))) (s_lasts s))
                (step_method s).
  Proof.
    unfold wt_system, wt_method; intros * WT; simpl.
    unfold translate_tcs, meth_vars.

    pose proof (s_nodup_variables s) as NodupVars.
    unfold variables in NodupVars.
    assert (incl (calls_of (s_tcs s)) (s_subs s)) as Subs
        by (rewrite s_subs_calls_of; apply incl_refl).
    assert (incl (resets_of (s_tcs s)) (s_subs s)) as Subs'
        by (eapply incl_tran; eauto; apply s_reset_incl; auto).

    induction (s_tcs s) as [|tc tcs]; inversion_clear WT as [|?? WTtc];
      simpl; eauto using wt_stmt.

    simpl in NodupVars;
      pose proof NodupVars as NodupVars';
      rewrite Permutation_app_comm in NodupVars';
      apply NoDup_app_weaken in NodupVars';
        apply NoDup_app_weaken in NodupVars.
    assert (incl (calls_of tcs) (s_subs s))
      by (destruct tc; simpl in *; auto;
          apply incl_cons' in Subs as (? & ?); auto).
    assert (incl (resets_of tcs) (s_subs s))
      by (destruct tc; simpl in *; auto;
          apply incl_cons' in Subs' as (? & ?); auto).

    rewrite 2 idty_app in WTtc.
    set (mems := map (fun xc : ident * (const * clock) => (fst xc, type_const (fst (snd xc)))) (s_lasts s)) in *;
      set (vars := idty (s_in s) ++ idty (s_vars s) ++ idty (s_out s)) in *;
      set (nvars := vars ++ mems) in *.
    apply wt_stmt_fold_left_shift; intuition.
    constructor; eauto using wt_stmt.
    assert (forall x ty,
               In (x, ty) nvars ->
               if PS.mem x (ps_from_list (map fst (s_lasts s)))
               then In (x, ty) mems
               else In (x, ty) vars)
    as NvarsSpec.
    { clear.
      assert (map fst (s_lasts s) = map fst mems) as ->
          by (subst mems; rewrite map_map; simpl; auto).
      subst nvars.
      assert (NoDupMembers (vars ++ mems)) as Nodup.
      { subst vars mems.
        apply fst_NoDupMembers.
        rewrite 3 map_app, 3 map_fst_idty, map_map; simpl.
        rewrite <-2 app_assoc. apply s_nodup.
      }
      intros * Hin; apply in_app in Hin as [Hin|Hin].
      - pose proof Hin.
        eapply In_InMembers, NoDupMembers_app_InMembers in Hin; eauto.
        cases_eqn E.
        apply PSE.MP.Dec.F.mem_iff, ps_from_list_In, fst_InMembers in E.
        contradiction.
      - pose proof Hin.
        rewrite Permutation_app_comm in Nodup.
        apply in_map with (f := fst) in Hin; simpl in Hin.
        apply ps_from_list_In in Hin; rewrite PSE.MP.Dec.F.mem_iff in Hin.
        rewrite Hin; auto.
    }
    destruct tc; inversion_clear WTtc as [| |????? Find|???????? Find Outs Ins ? Exps];
      simpl in *; eauto.
    - eapply Control_wt; eauto.
      constructor; eauto.
      now rewrite typeof_correct.
    - apply incl_cons' in Subs' as (? & ?).
      apply find_system_translate in Find as (?&?&?&?&?); subst.
      eapply Control_wt; eauto.
      econstructor; eauto.
      + apply exists_reset_method.
      + simpl; constructor.
      + simpl; constructor.
    - apply incl_cons' in Subs as (? & ?).
      apply find_system_translate in Find as (?&?&?&?&?); subst.
      eapply Control_wt; eauto.
      econstructor; eauto.
      + apply exists_step_method.
      + simpl; clear - Outs; induction Outs as [|? (?&(?&?))]; simpl; constructor; auto.
      + simpl; clear - Ins; induction Ins as [|? (?&(?&?))]; simpl; constructor; auto.
        now rewrite typeof_arg_correct.
      + clear - Exps NvarsSpec; induction Exps; simpl; constructor; eauto.
        eapply translate_arg_wt; eauto.
  Qed.
  Hint Resolve step_wt.

  Lemma reset_mems_wt:
    forall P insts mems lasts,
      (forall x c ck, In (x, (c, ck)) lasts -> In (x, type_const c) mems) ->
      wt_stmt (translate P) insts mems [] (reset_mems lasts).
  Proof.
    unfold reset_mems; intros * Spec.
    induction lasts as [|(x, (c, ck))]; simpl; eauto using wt_stmt.
    rewrite wt_stmt_fold_left_lift; split; auto.
    - apply IHlasts.
      intros; eapply Spec; right; eauto.
    - constructor; eauto using wt_stmt.
      constructor; eauto using wt_exp; simpl; auto.
      eapply Spec; left; eauto.
  Qed.

  Lemma reset_insts_wt_permutation:
    forall subs subs' prog insts mems vars,
      Permutation subs' subs ->
      wt_stmt prog insts mems vars (reset_insts subs) ->
      wt_stmt prog insts mems vars (reset_insts subs').
  Proof.
    unfold reset_insts.
    induction 1; simpl; auto; intros * WT.
    - apply wt_stmt_fold_left_lift in WT as (? & ?);
        rewrite wt_stmt_fold_left_lift; split; auto.
    - apply wt_stmt_fold_left_lift in WT as (?& WT');
        rewrite wt_stmt_fold_left_lift; split; auto.
      inversion_clear WT' as [| | |?? WT| |]; inv WT; eauto using wt_stmt.
  Qed.

  Lemma reset_insts_wt:
    forall P insts mems s,
      wt_system P s ->
      incl (s_subs s) insts ->
      wt_stmt (translate P) insts mems [] (reset_insts (s_subs s)).
  Proof.
    unfold wt_system; intros * WT Spec.
    eapply reset_insts_wt_permutation; try apply s_subs_calls_of.
    rewrite s_subs_calls_of in Spec.
    unfold reset_insts.
    induction (s_tcs s) as [|[] tcs]; simpl in *;
      inversion_clear WT as [|?? WTtc]; eauto using wt_stmt.
    apply incl_cons' in Spec as (? & ?).
    rewrite wt_stmt_fold_left_lift; split; auto.
    constructor; eauto using wt_stmt.
    inversion_clear WTtc as [| | |???????? Find].
    apply find_system_translate in Find as (?&?&?&?&?); subst.
    econstructor; eauto.
    - apply exists_reset_method.
    - constructor.
    - simpl; constructor.
    - simpl; constructor.
  Qed.

  Lemma reset_wt:
    forall P s,
      wt_system P s ->
      wt_method (translate P) (s_subs s)
                (map (fun xc : ident * (const * clock) => (fst xc, type_const (fst (snd xc)))) (s_lasts s))
                (reset_method s).
  Proof.
    unfold wt_system, wt_method; intros * WT; simpl.
    unfold translate_tcs, meth_vars, translate_reset; simpl.
    constructor.
    - clear WT.
      apply reset_mems_wt.
      intros * Hin; induction (s_lasts s) as [|(x', (c', ck'))];
        simpl; inv Hin; auto.
      left; congruence.
    - apply reset_insts_wt; auto.
      apply incl_refl.
  Qed.
  Hint Resolve reset_wt.

  Lemma translate_system_wt:
    forall P s,
      wt_system P s ->
      wt_class (translate P) (translate_system s).
  Proof.
    unfold wt_system; intros * WT.
    constructor; simpl; eauto using Forall_cons.
    rewrite s_subs_calls_of.
    induction (s_tcs s) as [|[]]; simpl; inversion_clear WT as [|?? WTtc]; auto;
      constructor; simpl; auto.
    inversion_clear WTtc as [| | |???????? Find].
    apply find_system_translate in Find as (?&?& -> &?); discriminate.
  Qed.
  Hint Resolve translate_system_wt.

  Theorem translate_wt:
    forall P,
      Stc.Typ.wt_program P ->
      wt_program (translate P).
  Proof.
    intros * WT.
    induction P as [|b]; simpl; auto with obctyping.
    inv WT.
    constructor; auto.
    unfold translate.
    now apply Forall_map.
  Qed.

End STC2OBCTYPING.

Module Stc2ObcTypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Op)
       (Str   : INDEXEDSTREAMS  Op OpAux)
       (CE    : COREEXPR    Ids Op OpAux Str)
       (Stc   : STC         Ids Op OpAux Str CE)
       (Obc   : OBC         Ids Op OpAux)
       (Trans : TRANSLATION Ids Op OpAux CE.Syn Stc.Syn Obc.Syn)
<: STC2OBCTYPING Ids Op OpAux Str CE Stc Obc Trans.
  Include STC2OBCTYPING Ids Op OpAux Str CE Stc Obc Trans.
End Stc2ObcTypingFun.
