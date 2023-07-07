From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Sorting.Mergesort.
From Coq Require Import Morphisms.
From Coq Require Import Setoid.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import IndexedStreams.
From Velus Require Import Stc.StcSemantics.
From Velus Require Import Stc.StcTyping.
From Velus Require Import Stc.StcClocking.
From Velus Require Import Stc.StcIsFree.
From Velus Require Import Stc.StcWellDefined.

From Velus Require Import VelusMemory.

(** * Scheduling of N-Lustre equations *)

(**

  The scheduler routines are parameterized over an external scheduler
  (EXT_NLSCHEDULER) that provides a schedule function.

  The schedule function should map a list of equations to a list of priority
  values (positive integers). If the output list has the same length as the
  input list, the equations are sorted in ascending order of their priorities.

  The idea is to allow an external scheduler to be written in OCaml. The
  scheduler should order the equations by their dependencies. If this is
  impossible, it should print an explanatory error message and return the
  empty list.

 *)

Module Type EXT_STCSCHEDULER
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS Ids Op OpAux)
       (Import CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX Ids Op OpAux Cks CESyn).

  Parameter schedule : ident -> list trconstr -> list positive.

End EXT_STCSCHEDULER.

Module Type STCSCHEDULE
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX    Ids Op)
       (Import ComTyp : COMMONTYPING     Ids Op OpAux)
       (Import Cks    : CLOCKS           Ids Op OpAux)
       (Import Str    : INDEXEDSTREAMS   Ids Op OpAux Cks)
       (Import CE     : COREEXPR         Ids Op OpAux ComTyp Cks Str)
       (Import StcSyn : STCSYNTAX        Ids Op OpAux Cks CE.Syn)
       (Import Ord    : STCORDERED       Ids Op OpAux Cks CE.Syn StcSyn)
       (Import StcSem : STCSEMANTICS     Ids Op OpAux Cks CE.Syn StcSyn Ord Str CE.Sem)
       (Import StcTyp : STCTYPING        Ids Op OpAux Cks CE.Syn StcSyn CE.Typ)
       (Import StcClo : STCCLOCKING      Ids Op OpAux Cks CE.Syn StcSyn Ord CE.Clo)
       (Import Free   : STCISFREE        Ids Op OpAux Cks CE.Syn StcSyn                         CE.IsF)
       (Import Wdef   : STCWELLDEFINED   Ids Op OpAux Cks CE.Syn StcSyn Ord CE.IsF Free)
       (Import Sch    : EXT_STCSCHEDULER Ids Op OpAux Cks CE.Syn StcSyn).

  Section OCombine.
    Context {A B: Type}.

    Fixpoint ocombine (l : list A) (l' : list B) : option (list (A * B)) :=
      match l, l' with
      | [], [] => Some []
      | x::xs, y::ys =>
        match ocombine xs ys with
        | None => None
        | Some rs => Some ((x, y) :: rs)
        end
      | _, _ => None
      end.

    Lemma ocombine_combine:
      forall l l' ll,
        ocombine l l' = Some ll ->
        combine l l' = ll.
    Proof.
      induction l, l'; simpl;
        try (now inversion_clear 1; auto).
      intros * HH; cases_eqn Hoc; inv HH; auto with datatypes.
    Qed.

    Lemma ocombine_length:
      forall l l' ll,
        ocombine l l' = Some ll ->
        length l = length l'.
    Proof.
      induction l, l'; simpl; inversion 1; auto.
      destruct (ocombine l l') eqn:Hoc.
      now rewrite (IHl _ _ Hoc).
      inv H.
    Qed.

  End OCombine.

  Module SchTcOrder <: Orders.TotalLeBool'.

    Definition t : Type := (positive * trconstr)%type.

    (* The arguments are inversed to put the list in the reverse order
       expected by [Is_well_sch]. *)
    Definition leb (s1 s2 : t) : bool := ((fst s2) <=? (fst s1))%positive.

    Lemma leb_total:
      forall s1 s2,
        leb s1 s2 = true \/ leb s2 s1 = true.
    Proof.
      destruct s1 as (p1 & eq1).
      destruct s2 as (p2 & eq2).
      unfold leb; simpl.
      setoid_rewrite POrderedType.Positive_as_OT.leb_compare.
      destruct (p1 ?= p2)%positive eqn:Hp; auto.
      apply Pos.compare_gt_iff in Hp.
      apply Pos.compare_lt_iff in Hp.
      rewrite Hp; auto.
    Qed.

  End SchTcOrder.

  Module SchSort := Sort SchTcOrder.

  Definition schedule_tcs (f: ident) (tcs: list trconstr) : list trconstr :=
    let sch := Sch.schedule f tcs in
    match ocombine sch tcs with
    | None        => tcs
    | Some schtcs => map snd (SchSort.sort schtcs)
    end.

  Lemma schedule_tcs_permutation:
    forall f tcs,
      Permutation (schedule_tcs f tcs) tcs.
  Proof.
    unfold schedule_tcs.
    intros f tcs.
    destruct (ocombine (schedule f tcs) tcs) eqn:Hoc; auto.
    rewrite <-SchSort.Permuted_sort.
    pose proof (ocombine_length _ _ _ Hoc) as Hlen.
    apply ocombine_combine in Hoc.
    rewrite <-Hoc, map_snd_combine; auto.
  Qed.

  Add Parametric Morphism : (insts_of)
      with signature @Permutation trconstr ==> @Permutation (ident * ident)
        as steps_of_permutation.
  Proof.
    induction 1; simpl; auto.
    - cases; rewrite IHPermutation.
    - cases; apply perm_swap.
    - etransitivity; eauto.
  Qed.

  Add Parametric Morphism : (inst_resets_of)
      with signature @Permutation trconstr ==> @Permutation (ident * ident)
        as iresets_of_permutation.
  Proof.
    induction 1; simpl; auto.
    - cases; rewrite IHPermutation.
    - cases; apply perm_swap.
    - etransitivity; eauto.
  Qed.

  Add Parametric Morphism : (state_resets_of)
      with signature @Permutation trconstr ==> @Permutation ident
        as resets_of_permutation.
  Proof.
    induction 1; simpl; auto.
    - cases; rewrite IHPermutation.
    - cases; apply perm_swap.
    - etransitivity; eauto.
  Qed.

  Add Parametric Morphism : (lasts_of)
      with signature @Permutation trconstr ==> @Permutation (ident * type)
        as lasts_of_permutation.
  Proof.
    induction 1; simpl; auto.
    - cases; rewrite IHPermutation.
    - cases; apply perm_swap.
    - etransitivity; eauto.
  Qed.

  Add Parametric Morphism : (nexts_of)
      with signature @Permutation trconstr ==> @Permutation (ident * type)
        as nexts_of_permutation.
  Proof.
    induction 1; simpl; auto.
    - cases; rewrite IHPermutation.
    - cases; apply perm_swap.
    - etransitivity; eauto.
  Qed.

  Add Parametric Morphism : (variables)
      with signature @Permutation trconstr ==> @Permutation ident
        as variables_permutation.
  Proof.
    unfold variables.
    induction 1; simpl; auto.
    - now rewrite IHPermutation.
    - rewrite <-2 Permutation_app_assoc; apply Permutation_app_tail, Permutation_app_comm.
    - etransitivity; eauto.
  Qed.

  Add Parametric Morphism A P: (Exists P)
      with signature @Permutation A ==> Basics.impl
        as Exists_permutation.
  Proof.
    induction 1; intros Ex; auto.
    - inv Ex.
      + now left.
      + right; auto.
    - inversion_clear Ex as [|?? Ex'].
      + now right; left.
      + inv Ex'.
        * now left.
        * now right; right.
  Qed.

  Program Definition schedule_system {prefs} (b: @system prefs) : @system prefs :=
    {| s_name  := b.(s_name);
       s_subs  := b.(s_subs);
       s_in    := b.(s_in);
       s_vars  := b.(s_vars);
       s_lasts := b.(s_lasts);
       s_nexts := b.(s_nexts);
       s_out   := b.(s_out);
       s_tcs   := schedule_tcs b.(s_name) b.(s_tcs);

       s_ingt0             := b.(s_ingt0);
       s_nodup             := b.(s_nodup);
       s_nodup_states_subs := b.(s_nodup_states_subs);
       s_good              := b.(s_good)
    |}.
  Next Obligation.
    rewrite schedule_tcs_permutation. apply s_vars_out_in_tcs.
  Qed.
  Next Obligation.
    rewrite schedule_tcs_permutation. apply s_lasts_in_tcs.
  Qed.
  Next Obligation.
    intros ??.
    unfold last_consistency, Last_with_reset_in, Is_reset_state_in.
    repeat setoid_rewrite schedule_tcs_permutation.
    eapply s_last_consistency.
  Qed.
  Next Obligation.
    rewrite schedule_tcs_permutation. apply s_nexts_in_tcs.
  Qed.
  Next Obligation.
    intros ??.
    unfold next_consistency, Next_with_reset_in, Is_reset_state_in.
    repeat setoid_rewrite schedule_tcs_permutation.
    eapply s_next_consistency.
  Qed.
  Next Obligation.
    rewrite schedule_tcs_permutation. apply s_state_reset_incl.
  Qed.
  Next Obligation.
    rewrite schedule_tcs_permutation. apply s_subs_in_tcs.
  Qed.
  Next Obligation.
    rewrite schedule_tcs_permutation. apply s_subs_insts_of.
  Qed.
  Next Obligation.
    intros ??.
    unfold Inst_with_reset_in, Is_reset_inst_in.
    repeat setoid_rewrite schedule_tcs_permutation.
    apply s_inst_consistency.
  Qed.
  Next Obligation.
    rewrite schedule_tcs_permutation. apply s_inst_reset_incl.
  Qed.

  Definition schedule {prefs} (P: @program prefs) : program :=
    Program P.(types) P.(externs) (map schedule_system P.(systems)).

  Lemma schedule_system_name {prefs} :
    forall (s: @system prefs), (schedule_system s).(s_name) = s.(s_name).
  Proof. destruct s; auto. Qed.

  Lemma schedule_map_name {prefs} :
    forall (P: list (@system prefs)),
      map s_name (map schedule_system P) = map s_name P.
  Proof.
    induction P as [|b]; auto.
    destruct b; simpl.
    simpl in *; now rewrite IHP.
  Qed.

  Lemma scheduler_find_system {prefs} :
    forall (P: @program prefs) P' f s,
      find_system f P = Some (s, P') ->
      find_system f (schedule P) = Some (schedule_system s, schedule P').
  Proof.
    intros []; induction systems0 as [|s']; [now inversion 1|].
    intros * Hfind.
    setoid_rewrite find_unit_cons; simpl; eauto.
    eapply find_unit_cons in Hfind as [[E Hfind]|[E Hfind]]; simpl in *; eauto.
    inv Hfind; auto.
  Qed.

  Lemma scheduler_find_system' {prefs} :
    forall (P: @program prefs) f s P',
      find_system f (schedule P) = Some (s, P') ->
      exists s' P'',
        find_system f P = Some (s', P'')
        /\ s = schedule_system s'
        /\ P' = schedule P''.
  Proof.
    intros []; induction systems0 as [|sys]; [now inversion 1|].
    intros * Hfind; unfold find_system, find_unit in *; simpl in *.
    destruct (ident_eq_dec sys.(s_name) f); eauto.
    inv Hfind; eauto.
  Qed.

  Lemma scheduler_wt_trconstr {prefs} :
    forall (P: @program prefs) vars tc,
      wt_trconstr P vars tc ->
      wt_trconstr (schedule P) vars tc.
  Proof.
    intros []; induction systems0 as [|b].
    - destruct tc; inversion_clear 1; eauto with stctyping.
    - destruct tc; inversion_clear 1; eauto with stctyping;
        match goal with H:find_system _ _ = _ |- _ =>
                        apply scheduler_find_system in H end;
        eauto with stctyping.
  Qed.

  Lemma scheduler_wt_system {prefs} :
    forall (P: @program prefs) s,
      wt_system P s ->
      wt_system (schedule P) (schedule_system s).
  Proof.
    unfold wt_system; simpl; intros * (WT&?); split; auto.
    rewrite schedule_tcs_permutation.
    apply Forall_impl with (2 := WT), scheduler_wt_trconstr.
  Qed.

  Lemma scheduler_wt_program {prefs} :
    forall (P: @program prefs),
      wt_program P ->
      wt_program (schedule P).
  Proof.
    intros []; induction systems0 as [|s]; inversion_clear 1 as [|?? []];
      unfold schedule; simpl; constructor; intuition.
    - simpl in *.
      take (wt_system _ _) and apply scheduler_wt_system in it as WT; auto.
    - change (Forall (fun s' =>
                        (fun x => s_name (schedule_system s) <> x) s'.(s_name))
                     (map schedule_system systems0)).
      rewrite <-Forall_map, schedule_map_name, Forall_map.
      destruct s; auto.
  Qed.

  Lemma scheduler_wc_trconstr {prefs} :
    forall (P: @program prefs) vars tc,
      wc_trconstr P vars tc ->
      wc_trconstr (schedule P) vars tc.
  Proof.
    intros []; induction systems0 as [|s P IH]; auto.
    intros vars tc Hwc.
    destruct tc; inv Hwc; eauto with stcclocking.
    econstructor; auto.
    - now apply scheduler_find_system; eauto.
    - eauto.
    - eauto.
  Qed.

  Lemma scheduler_wc_system {prefs} :
    forall (P: @program prefs) s,
      wc_system P s ->
      wc_system (schedule P) (schedule_system s).
  Proof.
    inversion_clear 1 as [? (?&?& Htcs)].
    constructor; simpl; auto.
    intuition.
    rewrite schedule_tcs_permutation; auto.
    induction Htcs; constructor; auto.
    apply scheduler_wc_trconstr; auto.
  Qed.

  Lemma scheduler_wc_program {prefs} :
    forall (P: @program prefs),
      wc_program P ->
      wc_program (schedule P).
  Proof.
    intros []; induction systems0; intros * WT; inv WT;
      unfold schedule; simpl; constructor; simpl in *; auto.
    - take (wc_system _ _) and apply scheduler_wc_system in it; auto.
    - apply IHsystems0; auto.
  Qed.

  Lemma scheduler_initial_state {prefs} :
    forall S (P: @program prefs) f,
      initial_state P f S ->
      initial_state (schedule P) f S.
  Proof.
    induction S as [? IH] using memory_ind'.
    inversion_clear 1 as [????? Find ? Insts].
    apply scheduler_find_system in Find.
    econstructor; eauto.
    simpl; intros * Hin.
    apply Insts in Hin as (?&?&?).
    eexists; intuition; eauto.
  Qed.
  Global Hint Resolve scheduler_initial_state : stcsem.

  Lemma scheduler_state_closed {prefs} :
    forall S (P: @program prefs) f,
      state_closed P f S ->
      state_closed (schedule P) f S.
  Proof.
    induction S as [? IH] using memory_ind'.
    inversion_clear 1 as [????? Find ? Insts].
    apply scheduler_find_system in Find.
    econstructor; eauto.
    simpl; intros * Hin; pose proof Hin.
    apply Insts in Hin as (?&?&?).
    eexists; intuition; eauto.
  Qed.
  Global Hint Resolve scheduler_state_closed : stcsem.

  Theorem scheduler_sem_system {prefs} :
    forall (P: @program prefs) f xs S S' ys,
      sem_system P f xs S S' ys ->
      sem_system (schedule P) f xs S S' ys.
  Proof.
    intros * Sem.
    eapply sem_system_mult with
      (P_system := fun f S xs ys S' =>
                     sem_system (schedule P) f S xs ys S')
      (P_trconstr := fun base R S I S' tc =>
                       sem_trconstr (schedule P) base R S I S' tc)
      in Sem; eauto with stcsem.
    - intros * ???.
      econstructor; eauto.
      cases; eauto with stcsem.
    - intros * ?????????.
      match goal with H: find_system _ _ = _ |- _ => apply scheduler_find_system in H end.
      eapply SSystem with (I := I); eauto with stcsem; simpl.
      rewrite schedule_tcs_permutation; eauto with stcsem.
  Qed.
  Global Hint Resolve scheduler_sem_system : stcsem.

  Corollary scheduler_loop {prefs} :
    forall n (P: @program prefs) f xss yss S,
      loop P f xss yss S n ->
      loop (schedule P) f xss yss S n.
  Proof.
    cofix COFIX; inversion_clear 1.
    econstructor; eauto with stcsem.
  Qed.

  Lemma scheduler_ordered {prefs} :
    forall (P: @program prefs),
      Ordered_systems P ->
      Ordered_systems (schedule P).
  Proof.
    unfold Ordered_systems, Ordered_program; simpl.
    induction 1 as [|? us [Spec Names]]; simpl; constructor; simpl; auto.
    split; auto.
    - intros * Hin; apply Spec in Hin as (?&?&?& Find).
      intuition; apply scheduler_find_system in Find; eauto.
    - clear - Names; induction us; simpl; inv Names; constructor; auto.
  Qed.

  Lemma scheduler_normal_args_tc {prefs} :
    forall (P: @program prefs) tc,
      normal_args_tc P tc ->
      normal_args_tc (schedule P) tc.
  Proof.
    induction 1; eauto with stcsyn.
    econstructor; auto.
    - apply scheduler_find_system; eauto.
    - auto.
  Qed.

Lemma scheduler_normal_args_system {prefs} :
  forall (P: @program prefs) s,
    normal_args_system P s ->
    normal_args_system (schedule P) (schedule_system s).
Proof.
  intros * Normal.
  apply Forall_forall; simpl.
  setoid_rewrite schedule_tcs_permutation.
  intros; eapply Forall_forall in Normal; eauto.
  apply scheduler_normal_args_tc; auto.
Qed.

Lemma scheduler_normal_args {prefs} :
  forall (P: @program prefs),
    normal_args P ->
    normal_args (schedule P).
Proof.
  unfold normal_args; simpl; induction 1 as [|?? NAS]; simpl; constructor; auto.
  apply scheduler_normal_args_system in NAS; auto.
Qed.

End STCSCHEDULE.

Module StcScheduleFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX    Ids Op)
       (ComTyp : COMMONTYPING     Ids Op OpAux)
       (Cks    : CLOCKS           Ids Op OpAux)
       (Str    : INDEXEDSTREAMS   Ids Op OpAux Cks)
       (CE     : COREEXPR         Ids Op OpAux ComTyp Cks Str)
       (StcSyn : STCSYNTAX        Ids Op OpAux Cks CE.Syn)
       (Ord    : STCORDERED       Ids Op OpAux Cks CE.Syn StcSyn)
       (Sem    : STCSEMANTICS     Ids Op OpAux Cks CE.Syn StcSyn Ord Str CE.Sem)
       (Typ    : STCTYPING        Ids Op OpAux Cks CE.Syn StcSyn CE.Typ)
       (Clo    : STCCLOCKING      Ids Op OpAux Cks CE.Syn StcSyn Ord CE.Clo)
       (Free   : STCISFREE        Ids Op OpAux Cks CE.Syn StcSyn                         CE.IsF)
       (Wdef   : STCWELLDEFINED   Ids Op OpAux Cks CE.Syn StcSyn Ord CE.IsF Free)
       (Sch    : EXT_STCSCHEDULER Ids Op OpAux Cks CE.Syn StcSyn)
<: STCSCHEDULE Ids Op OpAux ComTyp Cks Str CE StcSyn Ord Sem Typ Clo Free Wdef Sch.
  Include STCSCHEDULE Ids Op OpAux ComTyp Cks Str CE StcSyn Ord Sem Typ Clo Free Wdef Sch.
End StcScheduleFun.
