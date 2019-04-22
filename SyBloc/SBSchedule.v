Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Mergesort.
Require Import Morphisms.
Require Import Setoid.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.CoreExpr.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.SyBloc.SBIsBlock.
Require Import Velus.SyBloc.SBOrdered.
Require Import Velus.CoreExpr.Stream.
Require Import Velus.SyBloc.SBSemantics.
Require Import Velus.SyBloc.SBTyping.
Require Import Velus.SyBloc.SBIsVariable.
Require Import Velus.SyBloc.SBIsLast.
Require Import Velus.SyBloc.SBIsDefined.
Require Import Velus.SyBloc.SBClocking.
Require Import Velus.SyBloc.SBIsFree.
Require Import Velus.SyBloc.SBWellDefined.

Require Import RMemory.

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

Module Type EXT_NLSCHEDULER
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX Op)
       (Import Syn   : SBSYNTAX Ids Op CESyn).

  Parameter schedule : ident -> list equation -> list positive.

End EXT_NLSCHEDULER.

Module Type SBSCHEDULE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX       Op)
       (Import Str   : STREAM              Op OpAux)
       (Import CE    : COREEXPR        Ids Op OpAux Str)
       (Import SBSyn : SBSYNTAX        Ids Op       CE.Syn)
       (Import Block : SBISBLOCK       Ids Op       CE.Syn SBSyn)
       (Import Ord   : SBORDERED       Ids Op       CE.Syn SBSyn Block)
       (Import SBSem : SBSEMANTICS     Ids Op OpAux CE.Syn SBSyn Block Ord Str CE.Sem)
       (Import SBTyp : SBTYPING        Ids Op       CE.Syn SBSyn CE.Typ)
       (Import Var   : SBISVARIABLE    Ids Op       CE.Syn SBSyn)
       (Import Last  : SBISLAST        Ids Op       CE.Syn SBSyn)
       (Import Def   : SBISDEFINED     Ids Op       CE.Syn SBSyn Var Last)
       (Import SBClo : SBCLOCKING      Ids Op       CE.Syn SBSyn Last Var Def Block Ord CE.Clo)
       (Import Free  : SBISFREE        Ids Op       CE.Syn SBSyn                        CE.IsF)
       (Import Wdef  : SBWELLDEFINED   Ids Op       CE.Syn SBSyn Block Ord Var Last Def CE.IsF Free)
       (Import Sch   : EXT_NLSCHEDULER Ids Op       CE.Syn SBSyn).

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
      intros * HH; cases_eqn Hoc; inv HH.
      erewrite IHl; eauto.
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

  Module SchEqOrder <: Orders.TotalLeBool'.

    Definition t : Type := (positive * equation)%type.

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

  End SchEqOrder.

  Module SchSort := Sort SchEqOrder.

  Definition schedule_eqs (f : ident) (eqs : list equation) : list equation :=
    let sch := Sch.schedule f eqs in
    match ocombine sch eqs with
    | None => eqs
    | Some scheqs =>
      map snd (SchSort.sort scheqs)
    end.

  Lemma schedule_eqs_permutation:
    forall f eqs,
      Permutation (schedule_eqs f eqs) eqs.
  Proof.
    unfold schedule_eqs.
    intros f eqs.
    destruct (ocombine (schedule f eqs) eqs) eqn:Hoc; auto.
    rewrite <-SchSort.Permuted_sort.
    pose proof (ocombine_length _ _ _ Hoc) as Hlen.
    apply ocombine_combine in Hoc.
    rewrite <-Hoc, map_snd_combine; auto.
  Qed.

  Add Parametric Morphism : (calls_of)
      with signature @Permutation equation ==> @Permutation (ident * ident)
        as calls_of_permutation.
  Proof.
    induction 1; simpl; auto.
    - cases; rewrite IHPermutation.
    - cases; apply perm_swap.
    - etransitivity; eauto.
  Qed.

  Add Parametric Morphism : (resets_of)
      with signature @Permutation equation ==> @Permutation (ident * ident)
        as resets_of_permutation.
  Proof.
    induction 1; simpl; auto.
    - cases; rewrite IHPermutation.
    - cases; apply perm_swap.
    - etransitivity; eauto.
  Qed.

  Add Parametric Morphism : (lasts_of)
      with signature @Permutation equation ==> @Permutation ident
        as lasts_of_permutation.
  Proof.
    induction 1; simpl; auto.
    - cases; rewrite IHPermutation.
    - cases; apply perm_swap.
    - etransitivity; eauto.
  Qed.

  Add Parametric Morphism : (variables)
      with signature @Permutation equation ==> @Permutation ident
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

  Add Parametric Morphism s k: (Is_state_in s k)
      with signature @Permutation equation ==> Basics.impl
        as Is_state_in_permutation.
  Proof.
    unfold Is_state_in; intros * E St.
    now rewrite <-E.
  Qed.

  Program Definition schedule_block (b: block) : block :=
    {| b_name   := b.(b_name);
       b_blocks := b.(b_blocks);
       b_in     := b.(b_in);
       b_vars   := b.(b_vars);
       b_lasts  := b.(b_lasts);
       b_out    := b.(b_out);
       b_eqs    := schedule_eqs b.(b_name) b.(b_eqs);

       b_ingt0              := b.(b_ingt0);
       b_nodup              := b.(b_nodup);
       b_nodup_lasts_blocks := b.(b_nodup_lasts_blocks);
       b_good               := b.(b_good)
    |}.
  Next Obligation.
    do 2 setoid_rewrite schedule_eqs_permutation at 1;
      apply b_blocks_in_eqs.
  Qed.
  Next Obligation.
    rewrite schedule_eqs_permutation; apply b_blocks_calls_of.
  Qed.
  Next Obligation.
    rewrite schedule_eqs_permutation; apply b_lasts_in_eqs.
  Qed.
  Next Obligation.
    rewrite schedule_eqs_permutation; apply b_vars_out_in_eqs.
  Qed.
  Next Obligation.
    unfold Step_with_reset_in; rewrite schedule_eqs_permutation in *;
      now apply b_no_single_reset.
  Qed.
  Next Obligation.
    unfold Step_with_reset_in in H; rewrite schedule_eqs_permutation in H.
    apply b_reset_in in H.
    cases; rewrite schedule_eqs_permutation; auto.
  Qed.
  Next Obligation.
    rewrite schedule_eqs_permutation; apply b_reset_incl.
  Qed.

  Definition schedule (P: program) : program :=
    map schedule_block P.

  Lemma schedule_block_name:
    forall b, (schedule_block b).(b_name) = b.(b_name).
  Proof. destruct b; auto. Qed.

  Lemma schedule_map_name:
    forall P,
      map b_name (schedule P) = map b_name P.
  Proof.
    induction P as [|b]; auto.
    destruct b; simpl.
    now rewrite IHP.
  Qed.

  Lemma scheduler_find_block:
    forall P P' f b,
      find_block f P = Some (b, P') ->
      find_block f (schedule P) = Some (schedule_block b, schedule P').
  Proof.
    induction P as [|bl]; [now inversion 1|].
    intros * Hfind.
    simpl in *.
    destruct (ident_eqb bl.(b_name) f); auto.
    inv Hfind; auto.
  Qed.

  Lemma scheduler_find_block':
    forall P f b P',
      find_block f (schedule P) = Some (b, P') ->
      exists bl P'',
        find_block f P = Some (bl, P'')
        /\ b = schedule_block bl
        /\ P' = schedule P''.
  Proof.
    induction P as [|bl]; [now inversion 1|].
    intros * Hfind.
    simpl in *.
    destruct (ident_eqb bl.(b_name) f); eauto.
    inv Hfind; eauto.
  Qed.

  Lemma scheduler_wt_equation:
    forall P vars lasts eq,
      wt_equation P vars lasts eq ->
      wt_equation (schedule P) vars lasts eq.
  Proof.
    induction P as [|b].
    - destruct eq; inversion_clear 1; eauto.
    - destruct eq; inversion_clear 1; eauto;
        match goal with H:find_block _ _ = _ |- _ =>
                        apply scheduler_find_block in H end;
        eauto using wt_equation.
  Qed.

  Lemma scheduler_wt_block:
    forall P b,
      wt_block P b ->
      wt_block (schedule P) (schedule_block b).
  Proof.
    unfold wt_block; simpl; intros * WT.
    rewrite schedule_eqs_permutation.
    apply Forall_impl with (2 := WT), scheduler_wt_equation.
  Qed.

  Lemma scheduler_wt_program:
    forall P,
      wt_program P ->
      wt_program (schedule P).
  Proof.
    induction P as [|b]; inversion_clear 1; simpl;
      constructor; auto.
    - now apply scheduler_wt_block.
    - change (Forall (fun b'=>
                        (fun x => b_name (schedule_block b) <> x) b'.(b_name))
                     (schedule P)).
      rewrite <-Forall_map, schedule_map_name, Forall_map.
      destruct b; auto.
  Qed.

  Lemma scheduler_wc_equation:
    forall P vars eq,
      wc_equation P vars eq ->
      wc_equation (schedule P) vars eq.
  Proof.
    induction P as [|b P IH]; auto.
    intros vars eq Hwc.
    destruct eq; inv Hwc; eauto using wc_equation.
    econstructor; auto.
    - now apply scheduler_find_block; eauto.
    - match goal with H:exists _, _ |- _ =>
                      destruct H as (isub & osub & Hn_in & Hn_out) end.
      exists isub, osub.
      match goal with H:find_block _ _ = Some (?b, _) |- _ => destruct b end; auto.
  Qed.

  Lemma scheduler_wc_block:
    forall P b,
      wc_block P b ->
      wc_block (schedule P) (schedule_block b).
  Proof.
    inversion_clear 1 as [? (?&?& Heqs)].
    constructor; simpl; auto.
    intuition.
    rewrite schedule_eqs_permutation; auto.
    induction Heqs; constructor; auto.
    apply scheduler_wc_equation; auto.
  Qed.

  Lemma scheduler_wc_program:
    forall P,
      wc_program P ->
      wc_program (schedule P).
  Proof.
    induction P; intros * WT; inv WT; simpl; constructor; auto.
    now apply scheduler_wc_block.
  Qed.

  Lemma scheduler_initial_state:
    forall S P b,
      initial_state P b S ->
      initial_state (schedule P) b S.
  Proof.
    induction S as [? IH] using memory_ind'.
    inversion_clear 1 as [????? Find ? Insts].
    apply scheduler_find_block in Find.
    econstructor; eauto.
    simpl; intros * Hin.
    apply Insts in Hin as (?&?&?).
    eexists; intuition; eauto.
  Qed.
  Hint Resolve scheduler_initial_state.

  Lemma scheduler_state_closed:
    forall S P b,
      state_closed P b S ->
      state_closed (schedule P) b S.
  Proof.
    induction S as [? IH] using memory_ind'.
    inversion_clear 1 as [????? Find ? Insts].
    apply scheduler_find_block in Find.
    econstructor; eauto.
    simpl; intros * Hin; pose proof Hin.
    apply Insts in Hin as (?&?&?).
    eexists; intuition; eauto.
  Qed.
  Hint Resolve scheduler_state_closed.

  Lemma scheduler_transient_states_closed:
    forall blocks P I,
      transient_states_closed P blocks I ->
      transient_states_closed (schedule P) blocks I.
  Proof.
    induction 1; constructor; auto.
  Qed.
  Hint Resolve scheduler_transient_states_closed.

  Theorem scheduler_sem_block:
    forall P b xs S S' ys,
      sem_block P b xs S S' ys ->
      sem_block (schedule P) b xs S S' ys.
  Proof.
    intro P;
      induction 1 using sem_block_mult
        with (P_equation := fun base R S I S' eq =>
                              sem_equation (schedule P) base R S I S' eq);
      eauto using sem_equation.
    - econstructor; eauto.
      cases; eauto.
    - match goal with H: find_block _ _ = _ |- _ => apply scheduler_find_block in H end.
      econstructor; eauto; simpl.
      rewrite schedule_eqs_permutation; eauto.
  Qed.

  Corollary scheduler_loop:
    forall P f xss yss S0,
      loop P f xss yss S0 0 ->
      loop (schedule P) f xss yss S0 0.
  Proof.
    generalize 0%nat.
    cofix COFIX; inversion_clear 1.
    econstructor; eauto.
    apply scheduler_sem_block; eauto.
  Qed.

  Lemma scheduler_ordered:
    forall P,
      Ordered_blocks P ->
      Ordered_blocks (schedule P).
  Proof.
    induction 1 as [|????? Names]; simpl; constructor; simpl; auto.
    - apply Forall_forall; intros (?&?) Hin;
        eapply Forall_forall in Hin; eauto; destruct Hin as (?& Find); intuition.
      destruct Find as (?&?& Find); apply scheduler_find_block in Find; eauto.
    - clear - Names; induction P; simpl; inv Names; constructor; auto.
  Qed.

  Lemma scheduler_normal_args_eq:
    forall P eq,
      normal_args_eq P eq ->
      normal_args_eq (schedule P) eq.
  Proof.
    induction 1; eauto using normal_args_eq.
    econstructor; auto.
    - apply scheduler_find_block; eauto.
    - auto.
  Qed.

Lemma scheduler_normal_args_block:
  forall P b,
    normal_args_block P b ->
    normal_args_block (schedule P) (schedule_block b).
Proof.
  intros * Normal.
  apply Forall_forall; simpl.
  setoid_rewrite schedule_eqs_permutation.
  intros; eapply Forall_forall in Normal; eauto.
  apply scheduler_normal_args_eq; auto.
Qed.

Lemma scheduler_normal_args:
  forall P,
    normal_args P ->
    normal_args (schedule P).
Proof.
  induction P as [|b]; auto.
  intros (?&?); split; auto.
  change (schedule_block b :: schedule P) with (schedule (b :: P)).
  apply scheduler_normal_args_block; auto.
Qed.

End SBSCHEDULE.

Module SBScheduleFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX       Op)
       (Str   : STREAM              Op OpAux)
       (CE    : COREEXPR        Ids Op OpAux Str)
       (Syn   : SBSYNTAX        Ids Op       CE.Syn)
       (Block : SBISBLOCK       Ids Op       CE.Syn Syn)
       (Ord   : SBORDERED       Ids Op       CE.Syn Syn Block)
       (Sem   : SBSEMANTICS     Ids Op OpAux CE.Syn Syn Block Ord Str CE.Sem)
       (Typ   : SBTYPING        Ids Op       CE.Syn Syn CE.Typ)
       (Var   : SBISVARIABLE    Ids Op       CE.Syn Syn)
       (Last  : SBISLAST        Ids Op       CE.Syn Syn)
       (Def   : SBISDEFINED     Ids Op       CE.Syn Syn Var Last)
       (Clo   : SBCLOCKING      Ids Op       CE.Syn Syn Last Var Def Block Ord CE.Clo)
       (Free  : SBISFREE        Ids Op       CE.Syn Syn                        CE.IsF)
       (Wdef  : SBWELLDEFINED   Ids Op       CE.Syn Syn Block Ord Var Last Def CE.IsF Free)
       (Sch   : EXT_NLSCHEDULER Ids Op       CE.Syn Syn)
<: SBSCHEDULE Ids Op OpAux Str CE Syn Block Ord Sem Typ Var Last Def Clo Free Wdef Sch.
  Include SBSCHEDULE Ids Op OpAux Str CE Syn Block Ord Sem Typ Var Last Def Clo Free Wdef Sch.
End SBScheduleFun.
