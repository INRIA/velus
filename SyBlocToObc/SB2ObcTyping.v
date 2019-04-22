Require Import Velus.SyBloc.
Require Import Velus.Obc.

Require Import Velus.SyBlocToObc.Translation.

Require Import Velus.RMemory.
Require Import Velus.Common.

Require Import List.
Import List.ListNotations.
Require Import Permutation.

Open Scope nat.
Open Scope list.

Module Type SB2OBCTYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import Str   : STREAM          Op OpAux)
       (Import CE    : COREEXPR    Ids Op OpAux Str)
       (Import SB    : SYBLOC      Ids Op OpAux Str CE)
       (Import Obc   : OBC         Ids Op OpAux)
       (Import Trans : TRANSLATION Ids Op OpAux CE.Syn SB.Syn Obc.Syn).

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

    Lemma translate_lexp_wt:
      forall e,
        wt_lexp nvars e ->
        wt_exp mems vars (translate_lexp memset e).
    Proof.
      induction e; simpl; intro WTle; inv WTle; auto using wt_exp.
      - FromMemset; eauto using wt_exp.
      - constructor; auto; now rewrite typeof_correct.
      - constructor; auto; now rewrite 2 typeof_correct.
    Qed.
    Hint Resolve translate_lexp_wt.

    Corollary translate_arg_wt:
      forall e clkvars ck,
        wt_lexp nvars e ->
        wt_exp mems vars (translate_arg memset clkvars ck e).
    Proof.
      unfold translate_arg; intros; cases; auto using wt_exp.
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
        match goal with H:typeofc e1 = typeofc e2 |- _ => rewrite H in Hv' end.
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
  Hint Resolve translate_lexp_wt translate_cexp_wt Control_wt.

  Lemma step_wt:
    forall P b,
      wt_block P b ->
      wt_method (translate P) (b_blocks b)
                (map (fun xc : ident * (const * clock) => (fst xc, type_const (fst (snd xc)))) (b_lasts b))
                (step_method b).
  Proof.
    unfold wt_block, wt_method; intros * WT; simpl.
    unfold translate_eqns, meth_vars.

    pose proof (b_nodup_variables b) as NodupVars.
    unfold variables in NodupVars.
    assert (incl (calls_of (b_eqs b)) (b_blocks b)) as Blocks
        by (rewrite b_blocks_calls_of; apply incl_refl).
    assert (incl (resets_of (b_eqs b)) (b_blocks b)) as Blocks'
        by (eapply incl_tran; eauto; apply b_reset_incl; auto).

    induction (b_eqs b) as [|eq eqs]; inversion_clear WT as [|?? WTeq];
      simpl; eauto using wt_stmt.

    simpl in NodupVars;
      pose proof NodupVars as NodupVars'; apply NoDup_comm, NoDup_app_weaken in NodupVars';
        apply NoDup_app_weaken in NodupVars.
    assert (incl (calls_of eqs) (b_blocks b))
      by (destruct eq; simpl in *; auto;
          apply incl_cons' in Blocks as (? & ?); auto).
    assert (incl (resets_of eqs) (b_blocks b))
      by (destruct eq; simpl in *; auto;
          apply incl_cons' in Blocks' as (? & ?); auto).

    rewrite 2 idty_app in WTeq.
    set (mems := map (fun xc : ident * (const * clock) => (fst xc, type_const (fst (snd xc)))) (b_lasts b)) in *;
      set (vars := idty (b_in b) ++ idty (b_vars b) ++ idty (b_out b)) in *;
      set (nvars := vars ++ mems) in *.
    apply wt_stmt_fold_left_shift; intuition.
    constructor; eauto using wt_stmt.
    assert (forall x ty,
               In (x, ty) nvars ->
               if PS.mem x (ps_from_list (map fst (b_lasts b)))
               then In (x, ty) mems
               else In (x, ty) vars)
    as NvarsSpec.
    { clear.
      assert (map fst (b_lasts b) = map fst mems) as ->
          by (subst mems; rewrite map_map; simpl; auto).
      subst nvars.
      assert (NoDupMembers (vars ++ mems)) as Nodup.
      { subst vars mems.
        apply fst_NoDupMembers.
        rewrite 3 map_app, 3 map_fst_idty, map_map; simpl.
        rewrite <-2 app_assoc. apply b_nodup.
      }
      intros * Hin; apply in_app in Hin as [Hin|Hin].
      - pose proof Hin.
        eapply In_InMembers, NoDupMembers_app_InMembers in Hin; eauto.
        cases_eqn E.
        apply PSE.MP.Dec.F.mem_iff, ps_from_list_In, fst_InMembers in E.
        contradiction.
      - pose proof Hin.
        apply NoDupMembers_app_comm in Nodup.
        apply in_map with (f := fst) in Hin; simpl in Hin.
        apply ps_from_list_In in Hin; rewrite PSE.MP.Dec.F.mem_iff in Hin.
        rewrite Hin; auto.
    }
    destruct eq; inversion_clear WTeq as [| |????? Find|???????? Find Outs Ins ? Exps];
      simpl in *; eauto.
    - eapply Control_wt; eauto.
      constructor; eauto.
      now rewrite typeof_correct.
    - apply incl_cons' in Blocks' as (? & ?).
      apply find_block_translate in Find as (?&?&?&?&?); subst.
      eapply Control_wt; eauto.
      econstructor; eauto.
      + apply exists_reset_method.
      + simpl; constructor.
      + simpl; constructor.
    - apply incl_cons' in Blocks as (? & ?).
      apply find_block_translate in Find as (?&?&?&?&?); subst.
      eapply Control_wt; eauto.
      econstructor; eauto.
      + apply exists_step_method.
      + simpl; clear - Outs; induction Outs; simpl; constructor; auto.
      + simpl; clear - Ins; induction Ins; simpl; constructor; auto.
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
    forall blocks blocks' prog insts mems vars,
      Permutation blocks' blocks ->
      wt_stmt prog insts mems vars (reset_insts blocks) ->
      wt_stmt prog insts mems vars (reset_insts blocks').
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
    forall P insts mems b,
      wt_block P b ->
      incl (b_blocks b) insts ->
      wt_stmt (translate P) insts mems [] (reset_insts (b_blocks b)).
  Proof.
    unfold wt_block; intros * WT Spec.
    eapply reset_insts_wt_permutation; try apply b_blocks_calls_of.
    rewrite b_blocks_calls_of in Spec.
    unfold reset_insts.
    induction (b_eqs b) as [|[] eqs]; simpl in *;
      inversion_clear WT as [|?? WTeq]; eauto using wt_stmt.
    apply incl_cons' in Spec as (? & ?).
    rewrite wt_stmt_fold_left_lift; split; auto.
    constructor; eauto using wt_stmt.
    inversion_clear WTeq as [| | |???????? Find].
    apply find_block_translate in Find as (?&?&?&?&?); subst.
    econstructor; eauto.
    - apply exists_reset_method.
    - constructor.
    - simpl; constructor.
    - simpl; constructor.
  Qed.

  Lemma reset_wt:
    forall P b,
      wt_block P b ->
      wt_method (translate P) (b_blocks b)
                (map (fun xc : ident * (const * clock) => (fst xc, type_const (fst (snd xc)))) (b_lasts b))
                (reset_method b).
  Proof.
    unfold wt_block, wt_method; intros * WT; simpl.
    unfold translate_eqns, meth_vars, translate_reset; simpl.
    constructor.
    - clear WT.
      apply reset_mems_wt.
      intros * Hin; induction (b_lasts b) as [|(x', (c', ck'))];
        simpl; inv Hin; auto.
      left; congruence.
    - apply reset_insts_wt; auto.
      apply incl_refl.
  Qed.
  Hint Resolve reset_wt.

  Lemma translate_block_wt:
    forall P b,
      wt_block P b ->
      wt_class (translate P) (translate_block b).
  Proof.
    unfold wt_block; intros * WT.
    constructor; simpl; eauto using Forall_cons.
    rewrite b_blocks_calls_of.
    induction (b_eqs b) as [|[]]; simpl; inversion_clear WT as [|?? WTeq]; auto;
      constructor; simpl; auto.
    inversion_clear WTeq as [| | |???????? Find].
    apply find_block_translate in Find as (?&?& -> &?); discriminate.
  Qed.
  Hint Resolve translate_block_wt.

  Lemma translate_wt:
    forall P,
      SB.Typ.wt_program P ->
      wt_program (translate P).
  Proof.
    intros * WT.
    pose proof (wt_program_NoDup _ WT) as Hnodup.
    induction P as [|b]; auto with obctyping.
    inversion_clear WT as [|? ? WT' WTb Hnr]; inv Hnodup.
    simpl; constructor; eauto.
    simpl; rewrite map_c_name_translate;
      auto using NoDup_cons.
  Qed.

End SB2OBCTYPING.

Module SB2ObcTypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Op)
       (Str   : STREAM          Op OpAux)
       (CE    : COREEXPR    Ids Op OpAux Str)
       (SB    : SYBLOC      Ids Op OpAux Str CE)
       (Obc   : OBC         Ids Op OpAux)
       (Trans : TRANSLATION Ids Op OpAux CE.Syn SB.Syn Obc.Syn)
<: SB2OBCTYPING Ids Op OpAux Str CE SB Obc Trans.
  Include SB2OBCTYPING Ids Op OpAux Str CE SB Obc Trans.
End SB2ObcTypingFun.
