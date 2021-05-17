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

From Coq Require Import List.
From Coq Require Import Setoid.
From Coq Require Import Permutation.

From Velus Require Import Common.
From Velus Require Export CommonProgram.
From Velus Require Import Environment.
From Velus Require Import VelusMemory.
From Velus Require Import Operators.

Section WTProg.

  Context {U Prog: Type}.
  Context `{PU : ProgramUnit U} `{P: Program U Prog}.

  Variable wt_unit: Prog -> U -> Prop.

  Definition wt_program (p: Prog) :=
    Forall' (fun us u =>
               wt_unit (update p us) u
               /\ Forall (fun u' => (name u <> name u')%type) us)
            (units p).

  Lemma wt_program_find_unit:
    forall p f u p',
      wt_program p ->
      find_unit f p = Some (u, p') ->
      wt_unit p' u /\ wt_program p'.
  Proof.
    unfold wt_program, find_unit; induction 1 as [|u' ? []]; try discriminate; intros * Find.
    destruct (ident_eq_dec (name u') f); auto.
    inv Find; rewrite units_of_update.
    split; auto.
    eapply Forall'_impl; eauto; simpl.
    setoid_rewrite update_idempotent; auto.
  Qed.

  Lemma wt_program_find_unit':
    forall p f u p',
      wt_program p ->
      find_unit f p = Some (u, p') ->
      wt_unit p' u /\ wt_program p' /\ equiv_program p p'.
  Proof.
    unfold wt_program, find_unit. induction 1 as [|u' ? []]; try discriminate; intros * Find.
    destruct (ident_eq_dec (name u') f); auto; subst.
    inv Find; rewrite units_of_update.
    repeat split; auto.
    - eapply Forall'_impl; eauto; simpl.
      setoid_rewrite update_idempotent; auto.
    - apply equiv_program_update.
  Qed.

  Lemma wt_program_app:
    forall p us us',
      units p = us ++ us' ->
      wt_program p ->
      Forall' (fun us u => Forall (fun u' => name u <> name u')%type (us ++ us')) us
      /\ wt_program (update p us').
  Proof.
    unfold wt_program; intros * E WT.
    rewrite E in WT.
    split.
    - clear E; induction us; constructor; auto;
        rewrite <-app_comm_cons in WT; inversion WT as [|?? []]; subst; clear WT; auto.
    - apply Forall'_app_r in WT.
      rewrite units_of_update.
      eapply Forall'_impl; eauto.
      now setoid_rewrite update_idempotent.
  Qed.

  Lemma wt_program_find_unit_chained:
    forall p f g u p' up,
      wt_program p ->
      find_unit f p = Some (u, p') ->
      find_unit g p' = Some up ->
      find_unit g p = Some up.
  Proof.
    intros * WTp Hfc Hfc'.
    destruct up.
    rewrite <-Hfc'.
    assert (equiv_program p p') by (eapply find_unit_equiv_program; eauto).
    apply find_unit_spec in Hfc as (?& us & E &?).
    rewrite <- app_last_app in E.
    eapply find_unit_later; eauto.
    eapply wt_program_app in WTp as [Hndp]; eauto.
    apply find_unit_spec in Hfc' as (?& us' & E' &?).
    rewrite E' in Hndp.
    subst; clear - Hndp.
    induction Hndp as [|?? Hndp]; constructor; auto.
    do 2 apply Forall_app_weaken in Hndp; inv Hndp; auto.
  Qed.

  Remark find_unit_suffix_same:
    forall p p' f up,
      find_unit f p = Some up ->
      wt_program p' ->
      suffix p p' ->
      find_unit f p' = Some up.
  Proof.
    intros * Hfind WT Sub.
    rewrite <-Hfind.
    inversion_clear Sub as [??? E' E].
    apply equiv_program_sym in E'.
    eapply find_unit_later; eauto.
    eapply wt_program_app in WT as [Hndp]; eauto.
    destruct up; apply find_unit_spec in Hfind as (?&?& E'' &?).
    rewrite E'' in Hndp.
    subst; clear - Hndp.
    induction Hndp as [|?? Hndp]; constructor; auto.
    do 2 apply Forall_app_weaken in Hndp; inv Hndp; auto.
  Qed.

  Lemma wt_program_NoDup:
    forall p,
      wt_program p ->
      NoDup (map name (units p)).
  Proof.
    unfold wt_program.
    intros * Wt.
    induction Wt; simpl; constructor; auto.
    destruct H as (_&Name).
    intros Hin. apply in_map_iff in Hin as (?&Hin&Hname).
    eapply Forall_forall in Name; [|eauto]. congruence.
  Qed.

  Variable Is_called_in: ident -> U -> Prop.

  Hypothesis wt_unit_Is_called_in:
    forall p u f,
      wt_unit p u ->
      Is_called_in f u ->
      find_unit f p <> None.

  Lemma wt_program_Ordered_program:
    forall p,
      wt_program p ->
      Ordered_program Is_called_in p.
  Proof.
    unfold wt_program, Ordered_program.
    intro; induction (units p) as [|u us]; intros * WT; simpl;
      inversion_clear WT as [|?? []]; constructor; auto.
    split; auto.
    intros * Called.
    eapply wt_unit_Is_called_in in Called; eauto.
    apply not_None_is_Some in Called as ((?&?)& Find).
    intuition eauto.
    apply find_unit_In in Find as [? Hin].
    rewrite units_of_update in Hin.
    eapply Forall_forall in Hin; eauto; subst; auto.
  Qed.

End WTProg.

Section TransfoWT.

  Context {U U' Prog Prog': Type}
          `{TransformUnit U U'}
          `{ProgInst: Program U Prog} `{Program U' Prog'}
          `{@TransformProgramWithoutUnits Prog Prog' _ ProgInst}.

  Lemma transform_units_wt_program:
    forall p (wt_unit: Prog -> U -> Prop) (wt_unit': Prog' -> U' -> Prop),
      (forall p u, wt_unit p u -> wt_unit' (transform_units p) (transform_unit u)) ->
      wt_program wt_unit p ->
      wt_program wt_unit' (transform_units p).
  Proof.
    unfold wt_program, transform_units; intros * Spec WT; rewrite units_of_update;
      induction WT as [|?? (WT & Ndp)]; simpl; constructor.
    - split.
      + rewrite update_idempotent.
        apply Spec in WT.
        now rewrite transform_program_without_units_update, units_of_update in WT.
      + apply Forall_map, Forall_forall; intros * Hin.
        eapply Forall_forall in Hin; eauto; simpl in Hin.
        now rewrite 2 transform_unit_conservative_name.
    - eapply Forall'_impl; eauto; simpl; intros * (?&?).
      split; auto.
      now rewrite update_idempotent in *.
  Qed.

End TransfoWT.

Module Type COMMONTYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op).

  Definition env  := Env.t value.
  Definition tenv := list (ident * type).
  Definition mem  := memory value.

  Definition wt_env_value (e: env) '((x, ty): ident * type) :=
    match Env.find x e with
    | Some v => wt_value v ty
    | None => True
    end.

  Definition wt_env (e: env) (Γ: tenv) :=
    Forall (wt_env_value e) Γ.

  Hint Unfold wt_env.

  Lemma wt_env_empty:
    forall Γ,
      wt_env (Env.empty _) Γ.
  Proof.
    induction Γ as [|(?&?)]; constructor; auto.
    unfold wt_env_value; rewrite Env.gempty; auto.
  Qed.
  Hint Resolve wt_env_empty.

  Lemma env_find_wt_value:
    forall Γ e x ty v,
      wt_env e Γ ->
      In (x, ty) Γ ->
      Env.find x e = Some v ->
      wt_value v ty.
  Proof.
    intros * WTe Hin Hfind.
    apply Forall_forall with (1:=WTe) in Hin.
    unfold wt_env_value in Hin.
    now rewrite Hfind in Hin.
  Qed.

  Lemma wt_env_value_add:
    forall e v x y ty,
      (y = x /\ wt_value v ty) \/ (y <> x /\ wt_env_value e (y, ty)) ->
      wt_env_value (Env.add x v e) (y, ty).
  Proof.
    intros * Hor. unfold wt_env_value; simpl.
    destruct Hor as [[Heq Hwt]|[Hne Hwt]].
    - subst. now rewrite Env.gss.
    - now rewrite Env.gso with (1:=Hne).
  Qed.

  Lemma wt_env_add:
    forall Γ e x t v,
      NoDupMembers Γ ->
      wt_env e Γ ->
      In (x, t) Γ ->
      wt_value v t ->
      wt_env (Env.add x v e) Γ.
  Proof.
    intros * Hndup WTenv Hin WTv.
    unfold wt_env.
    induction Γ as [|y]; auto.
    apply Forall_cons2 in WTenv.
    destruct WTenv as (WTx & WTenv).
    destruct y as (y & ty).
    apply nodupmembers_cons in Hndup.
    destruct Hndup as (Hnin & Hndup).
    inv Hin.
    - match goal with H:(y, ty) = _ |- _ => injection H; intros; subst end.
      constructor.
      + apply wt_env_value_add; left; auto.
      + apply Forall_impl_In with (2:=WTenv).
        destruct a as (y & ty).
        intros Hin HTy.
        apply NotInMembers_NotIn with (b:=ty) in Hnin.
        apply wt_env_value_add; right; split.
        intro; subst; contradiction.
        now apply HTy.
    - constructor; auto.
      apply wt_env_value_add.
      destruct (ident_eq_dec x y);
        [subst; left; split|right]; auto.
      apply NotInMembers_NotIn with (b:=t) in Hnin.
      contradiction.
  Qed.
  Hint Resolve wt_env_add.

  Lemma wt_env_value_remove:
    forall env x y ty,
      wt_env_value env (y, ty) ->
      wt_env_value (Env.remove x env) (y, ty).
  Proof.
    unfold wt_env_value; simpl.
    intros * WTenv.
    destruct (ident_eq_dec x y); subst.
    now rewrite Env.grs.
    now rewrite Env.gro; auto.
  Qed.

  Lemma wt_env_remove:
    forall x env Γv,
      wt_env env Γv ->
      wt_env (Env.remove x env) Γv.
  Proof.
    induction Γv as [|(y, yt) Γv]; auto.
    setoid_rewrite Forall_cons2.
    destruct 1 as (Hy & HΓv).
    split; [|now apply IHΓv].
    now apply wt_env_value_remove.
  Qed.
  Hint Resolve wt_env_remove.

  Lemma wt_env_adds_opt:
    forall Γv env ys outs rvs,
      NoDupMembers Γv ->
      NoDup ys ->
      wt_env env Γv ->
      Forall2 (fun y (xt: ident * type) => In (y, snd xt) Γv) ys outs ->
      Forall2 (fun vo xt => wt_option_value vo (snd xt)) rvs outs ->
      wt_env (Env.adds_opt ys rvs env) Γv.
  Proof.
    intros * NodupM Nodup WTenv Hin WTv.
    assert (length ys = length rvs) as Length
        by (transitivity (length outs); [|symmetry];
            eapply Forall2_length; eauto).
    revert env0 rvs outs WTenv WTv Length Hin.
    induction ys, rvs, outs; intros * WTenv WTv Length Hin;
      inv Length; inv Nodup; inv Hin; inv WTv; auto.
    destruct o.
    - rewrite Env.adds_opt_cons_cons'; auto.
      eapply IHys; eauto.
    - rewrite Env.adds_opt_cons_cons_None; auto.
      eapply IHys; eauto.
  Qed.
  Hint Resolve wt_env_adds_opt.

  Section WTMemory.

    Context {U Prog: Type}.
    Context `{PU : ProgramStateUnit U type} `{P : Program U Prog}.

    Inductive wt_memory: mem -> Prog -> tenv -> list (ident * ident) -> Prop :=
      wt_mem_intro: forall M p mems insts,
        wt_env (values M) mems ->
        Forall (wt_inst M p) insts ->
        wt_memory M p mems insts

    with wt_inst: mem -> Prog -> (ident * ident) -> Prop :=
    | wt_inst_empty: forall M p i f,
        find_inst i M = None ->
        wt_inst M p (i, f)
    | wt_inst_some: forall M p i f Mi u p',
        find_inst i M = Some Mi ->
        find_unit f p = Some (u, p') ->
        wt_memory Mi p' (state_variables u) (instance_variables u) ->
        wt_inst M p (i, f).

    (* XXX: why does this fail? *)
    (*
      Scheme wt_mem_ind_2 := Minimality for wt_mem Sort Prop
      with wt_mem_inst_ind_2 := Minimality for wt_mem_inst Sort Prop.
      Combined Scheme wt_mem_inst_ind' from wt_mem_ind_2, wt_mem_inst_ind_2.
     *)

    Section wt_memory_inst_ind.

      Variable Pmem  : mem -> Prog -> tenv -> list (ident * ident) -> Prop.
      Variable Pinst : mem -> Prog -> (ident * ident) -> Prop.

      Hypothesis wt_mem_intro_Case:
        forall M p mems insts,
          wt_env (values M) mems ->
          Forall (wt_inst M p) insts ->
          Forall (Pinst M p) insts ->
          Pmem M p mems insts.

      Hypothesis wt_inst_empty_Case:
        forall M p i f,
          find_inst i M = None ->
          Pinst M p (i, f).

      Hypothesis wt_inst_some_Case:
        forall M p i f Mi u p',
          find_inst i M = Some Mi ->
          find_unit f p = Some (u, p') ->
          Pmem Mi p' (state_variables u) (instance_variables u) ->
          Pinst M p (i, f).

      Fixpoint wt_memory_mult
               (M: mem) (p: Prog) (mems: tenv) (insts: list (ident * ident))
               (WT: wt_memory M p mems insts) {struct WT} : Pmem M p mems insts
      with wt_inst_mult
             (M: mem) (p: Prog) (oc: ident * ident)
             (WT: wt_inst M p oc) {struct WT} : Pinst M p oc.
      Proof.
        - destruct WT.
          apply wt_mem_intro_Case; auto.
          take (Forall _ _) and induction it; constructor; auto.
        - destruct WT.
          + now apply wt_inst_empty_Case.
          + eapply wt_inst_some_Case; eauto.
      Defined.

      Combined Scheme wt_memory_inst_ind from wt_memory_mult, wt_inst_mult.

    End wt_memory_inst_ind.

    Lemma wt_memory_empty:
      forall p mems insts,
        wt_memory (empty_memory _) p mems insts.
    Proof.
      constructor; simpl; auto.
      induction insts as [|(?, ?)]; auto.
      apply Forall_cons; auto.
      apply wt_inst_empty.
      apply find_inst_gempty.
    Qed.
    Hint Resolve wt_memory_empty.

    Lemma wt_memory_mems_cons:
      forall M p mems insts x t,
        wt_memory M p ((x, t) :: mems) insts <->
        wt_env_value (values M) (x, t) /\ wt_memory M p mems insts.
    Proof.
      split.
      - inversion_clear 1 as [???? WTmems]; inv WTmems.
        intuition; constructor; auto.
      - intros [? WT]; inv WT.
        constructor; auto.
    Qed.

    Lemma wt_memory_insts_cons:
      forall M p mems insts i f,
        wt_memory M p mems ((i, f) :: insts) <->
        wt_inst M p (i, f) /\ wt_memory M p mems insts.
    Proof.
      split.
      - inversion_clear 1 as [????? WTinsts]; inv WTinsts.
        intuition; constructor; auto.
      - intros [? WT]; inv WT.
        constructor; auto.
    Qed.

    Lemma wt_inst_add_val:
      forall p i x v M,
        wt_inst M p i ->
        wt_inst (add_val x v M) p i.
    Proof.
      inversion_clear 1.
      - left; auto.
      - eright; eauto.
    Qed.

    Lemma wt_memory_add_val:
      forall p mems insts x t v M,
        NoDupMembers mems ->
        wt_memory M p mems insts ->
        In (x, t) mems ->
        wt_value v t ->
        wt_memory (add_val x v M) p mems insts.
    Proof.
      inversion_clear 2; intros.
      constructor; simpl.
      - eapply wt_env_add; eauto.
      - apply Forall_forall; intros (?&?) Hin.
        eapply wt_inst_add_val.
        eapply Forall_forall in Hin; eauto.
    Qed.
    Hint Resolve wt_memory_add_val.
 
    Lemma wt_inst_add_inst_neq:
      forall p i f j Mj M,
        wt_inst M p (i, f) ->
        j <> i ->
        wt_inst (add_inst j Mj M) p (i, f).
    Proof.
      inversion_clear 1.
      - left; rewrite find_inst_gso; auto.
      - eright; eauto.
        rewrite find_inst_gso; auto.
    Qed.

    Lemma wt_inst_add_inst_eq:
      forall p f i u p' Mi M,
        wt_inst M p (i, f) ->
        find_unit f p = Some (u, p') ->
        wt_memory Mi p' (state_variables u) (instance_variables u) ->
        wt_inst (add_inst i Mi M) p (i, f).
    Proof.
      inversion_clear 1; intros; eright; eauto; apply find_inst_gss.
    Qed.

    Lemma wt_memory_add_inst:
      forall p mems insts i f u p' Mi M,
        NoDupMembers insts ->
        wt_memory M p mems insts ->
        In (i, f) insts ->
        find_unit f p = Some (u, p') ->
        wt_memory Mi p' (state_variables u) (instance_variables u) ->
        wt_memory (add_inst i Mi M) p mems insts.
    Proof.
      inversion_clear 2 as [????? WT]; intros.
      constructor; simpl; auto.
      apply Forall_forall; intros (i', f') Hin.
      eapply Forall_forall in WT; eauto.
      destruct (ident_eq_dec i i').
      - subst.
        assert (f' = f) as ->
            by (eapply NoDupMembers_det; eauto).
        eapply wt_inst_add_inst_eq; eauto.
      - apply wt_inst_add_inst_neq; auto.
    Qed.
    Hint Resolve wt_memory_add_inst.

    Lemma wt_inst_suffix:
      forall p p' mem oc wt_unit,
        wt_inst mem p' oc ->
        wt_program wt_unit p ->
        suffix p' p ->
        wt_inst mem p oc.
    Proof.
      induction 1; intros.
      - left; auto.
      - eright; eauto.
        eapply find_unit_suffix_same; eauto.
    Qed.
    Hint Resolve wt_inst_suffix.

    Lemma wt_memory_suffix:
      forall p p' mems insts mem wt_unit,
        wt_memory mem p' mems insts ->
        wt_program wt_unit p ->
        suffix p' p ->
        wt_memory mem p mems insts.
    Proof.
      induction 1 as [????? WTmem_inst]; intros * Sub.
      constructor; auto.
      induction insts as [|(o, c)]; inv WTmem_inst; auto.
      constructor; eauto.
    Qed.

    Lemma wt_memory_chained:
      forall p p' mems insts mem f u wt_unit,
        wt_program wt_unit p ->
        find_unit f p = Some (u, p') ->
        wt_memory mem p' mems insts ->
        wt_memory mem p mems insts.
    Proof.
      intros.
      eapply wt_memory_suffix; eauto.
      eapply find_unit_suffix; eauto.
    Qed.
    Hint Resolve wt_memory_chained.

    Lemma wt_memory_other:
      forall M p u us mems insts,
        units p = u :: us ->
        Forall (fun oc => snd oc <> name u) insts ->
        (wt_memory M p mems insts <-> wt_memory M (update p us) mems insts).
    Proof.
      intros * E Spec.
      split; intros * WT; inv WT; constructor; auto;
        apply Forall_forall; intros (i, f) Hin;
          do 2 (take (Forall _ insts) and eapply Forall_forall in it; eauto);
          simpl in *;
          take (wt_inst _ _ _) and inv it; try (now left); eright; eauto.
      - take (find_unit _ _ = _) and eapply find_unit_cons in it as [[E' Find]|[E' Find]]; eauto;
          contradiction.
      - eapply find_unit_cons; eauto.
    Qed.

    Global Add Parametric Morphism : (wt_env)
        with signature (Env.Equal ==> @Permutation (ident * type) ==> Basics.impl)
          as wt_env_permutation.
    Proof.
      unfold wt_env; intros e e' Ee env env' <- WT.
      apply Forall_forall; intros (?&?) Hin; eapply Forall_forall in WT; eauto.
      unfold wt_env_value in *.
      now rewrite <-Ee.
    Qed.

    Global Add Parametric Morphism : (wt_memory)
        with signature (equal_memory ==> eq ==> @Permutation (ident * type) ==> @Permutation (ident * ident) ==> Basics.impl)
          as wt_memory_permutation.
    Proof.
      intro M; induction M as [? IH] using memory_ind';
        intros M' EM p mems mems' Emems insts insts' Einsts WT.
      inversion_clear WT as [????? Insts].
      constructor.
      - now rewrite <-EM, <-Emems.
      - rewrite <-Einsts.
        apply Forall_forall; intros (i, f) Hin; eapply Forall_forall in Insts; eauto.
        assert (find_inst i M ⌈≋⌉ find_inst i M') as E by (now rewrite EM).
        inv Insts.
        + left.
          take (find_inst _ _ = _) and rewrite it in E; inv E; auto.
        + take (find_inst _ _ = _) and rewrite it in E; inv E; auto.
          eright; eauto.
          eapply IH; eauto.
    Qed.

  End WTMemory.

  Hint Resolve wt_env_empty wt_env_add wt_env_remove wt_env_adds_opt
       wt_memory_empty wt_memory_add_val wt_memory_add_inst
       wt_memory_chained.

  Section TransfoWT.

    Context {U U' Prog Prog': Type}
            `{PSU: ProgramStateUnit U type} `{PSU': ProgramStateUnit U' type}
            `{P: Program U Prog} `{Program U' Prog'}
            `{@TransformStateUnit _ _ _ PSU PSU'}
            `{@TransformProgramWithoutUnits Prog Prog' _ P}.

    Lemma transform_units_wt_memory:
      forall me (p: Prog) mems insts,
        wt_memory me p mems insts <->
        wt_memory me (transform_units p) mems insts.
    Proof.
      induction me as [? IH] using memory_ind'.
      split; intros * WT;
        inversion_clear WT as [????? WTinsts]; constructor; auto;
          apply Forall_forall; intros (?&?) Hin;
            eapply Forall_forall in WTinsts; eauto;
              inv WTinsts; try now left.
      - eright; eauto.
        + apply find_unit_transform_units_forward; eauto.
        + eapply IH; eauto.
          now destruct (transform_unit_conservative_state u) as [-> ->].
      - edestruct find_unit_transform_units_backward as (u' &?&?&?&?); eauto.
        subst.
        eright; eauto.
        eapply IH; eauto.
        now destruct (transform_unit_conservative_state u') as [<- <-].
    Qed.

    Corollary transform_units_wt_memory':
      forall p u me,
        wt_memory me p (state_variables u) (instance_variables u) <->
        wt_memory me (transform_units p) (state_variables (transform_unit u)) (instance_variables (transform_unit u)).
    Proof.
      intros; split; destruct (transform_unit_conservative_state u) as [-> ->];
        now apply transform_units_wt_memory.
    Qed.

  End TransfoWT.

End COMMONTYPING.

Module CommonTypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
<: COMMONTYPING Ids Op OpAux.
  Include COMMONTYPING Ids Op OpAux.
End CommonTypingFun.
