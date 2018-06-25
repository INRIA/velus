Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Mergesort.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLSemantics.

Require Import Velus.NLustre.IsFree.
Require Import Velus.NLustre.NLTyping.
Require Import Velus.NLustre.Memories.
Require Import Velus.NLustre.IsDefined.
Require Import Velus.NLustre.NLClocking.

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
       (Import Clks  : CLOCKS   Ids)
       (Import Syn   : NLSYNTAX Ids Op Clks).

  Parameter schedule : ident -> list equation -> list positive.

End EXT_NLSCHEDULER.

Module Type NLSCHEDULE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX       Op)
       (Import Clks  : CLOCKS          Ids)
       (Import Syn   : NLSYNTAX        Ids Op       Clks)
       (Import Str   : STREAM              Op OpAux)
       (Import Ord   : ORDERED         Ids Op       Clks Syn)
       (Import Sem   : NLSEMANTICS     Ids Op OpAux Clks Syn Str Ord)
       (Import Mem   : MEMORIES        Ids Op       Clks Syn)
       (Import IsD   : ISDEFINED       Ids Op       Clks Syn         Mem)
       (Import IsF   : ISFREE          Ids Op       Clks Syn)
       (Import Typ   : NLTYPING        Ids Op       Clks Syn)
       (Import Clo   : NLCLOCKING      Ids Op       Clks Syn         Mem IsD IsF)
       (Import Sch   : EXT_NLSCHEDULER Ids Op       Clks Syn).

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
      intros ll HH.
      destruct (ocombine l l') eqn:Hoc.
      2:now inv HH.
      rewrite (IHl _ _ Hoc).
      now inv HH.
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

  Lemma map_snd_combine:
    forall {A B} (l: list A) (l': list B),
      length l = length l' ->
      map snd (combine l l') = l'.
  Proof.
    induction l, l'; inversion 1; auto.
    simpl. now rewrite (IHl _ H1).
  Qed.

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

  Require Import Morphisms.

  Instance var_defined_Permutation_Proper:
    Proper (@Permutation equation ==> Permutation (A:=ident)) vars_defined.
  Proof.
    intros eqs eqs' Hperm.
    unfold vars_defined, concatMap.
    induction Hperm; auto; simpl.
    - rewrite IHHperm; auto.
    - now rewrite <-Permutation_app_assoc,
                  (Permutation_app_comm (var_defined y)),
                  Permutation_app_assoc.
    - now rewrite IHHperm1, IHHperm2.
  Qed.

  Program Definition schedule_node (n: node): node :=
    match n with
      mk_node name nin nout vars eqs
              ingt0 outgt0 defd vout nodup good =>
      mk_node name nin nout vars (schedule_eqs n.(n_name) eqs)
              ingt0 outgt0 _ _ nodup _
    end.
  Next Obligation.
    now setoid_rewrite schedule_eqs_permutation.
  Qed.
  Next Obligation.
    setoid_rewrite schedule_eqs_permutation; auto.
  Qed.
  Next Obligation.
    setoid_rewrite schedule_eqs_permutation; auto.
  Qed.

  Definition schedule (G: global) : global :=
    map schedule_node G.

  Lemma schedule_node_name:
    forall n,
      (schedule_node n).(n_name) = n.(n_name).
  Proof.
    destruct n; auto.
  Qed.

  Lemma scheduler_wc_global:
    forall G,
      wc_global G ->
      wc_global (schedule G).
  Proof.
    intros G HG.
    induction G as [|n G Hwc IH]; auto.
    inv HG.
    constructor; [|now apply Hwc].
    inv H1.
    destruct n.
    constructor; auto.
    simpl in *.
    now rewrite schedule_eqs_permutation.
  Qed.

  Lemma schedule_map_name:
    forall G,
      map n_name (schedule G) = map n_name G.
  Proof.
    induction G as [|n G IH]; auto.
    destruct n.
    simpl. now rewrite IH.
  Qed.

  Lemma scheduler_find_node:
    forall G f n,
      find_node f G = Some n ->
      find_node f (schedule G) = Some (schedule_node n).
  Proof.
    induction G as [|n' G IH]; [now inversion 1|].
    intros f n Hfind.
    simpl in *.
    destruct (ident_eqb n'.(n_name) f) eqn:Heq.
    - inv Hfind.
      destruct n; simpl in *.
      now rewrite Heq.
    - destruct n'. simpl in *. rewrite Heq; auto.
  Qed.

  Lemma scheduler_find_node':
    forall G f n,
      find_node f (schedule G) = Some n ->
      exists n',
        find_node f G = Some n'
        /\ n = schedule_node n'.
  Proof.
    induction G as [|n' G IH]; [now inversion 1|].
    intros f n Hfind.
    simpl in *.
    destruct n'; simpl in *.
    destruct (ident_eqb n_name0 f) eqn:Heq; eauto.
    inv Hfind; eauto.
  Qed.

  Lemma scheduler_wt_equation:
    forall G vars eq,
      wt_equation G vars eq ->
      wt_equation (schedule G) vars eq.
  Proof.
    induction G as [|n G IH].
    now destruct eq; inversion_clear 1; eauto with nltyping.
    destruct eq; inversion_clear 1; eauto with nltyping;
      match goal with H:find_node _ _ = _ |- _ =>
                      apply scheduler_find_node in H end;
      destruct n0; eauto with nltyping.
  Qed.

  Lemma scheduler_wt_global:
    forall G,
      wt_global G ->
      wt_global (schedule G).
  Proof.
    intros G HG.
    induction G as [|n G Hwt IH]; auto.
    inv HG. simpl.
    apply wtg_cons; auto.
    - unfold wt_node in *.
      destruct n; simpl in *.
      rewrite schedule_eqs_permutation.
      eapply Forall_impl with (2:=H2).
      apply scheduler_wt_equation.
    - change (Forall (fun n'=>
                        (fun x => n_name (schedule_node n) <> x) n'.(n_name))
                     (schedule G)).
      rewrite <-Forall_map.
      rewrite schedule_map_name.
      rewrite Forall_map.
      destruct n; auto.
  Qed.

  Lemma scheduler_sem_node:
    forall G f xss yss,
      sem_node G f xss yss ->
      sem_node (schedule G) f xss yss.
  Proof.
    intros G.
    induction 1 using sem_node_mult
    with (P_equation := fun bk H eq =>
                          sem_equation G bk H eq ->
                          sem_equation (schedule G) bk H eq)
         (P_reset := fun f r xss yss =>
                       sem_reset G f r xss yss ->
                       sem_reset (schedule G) f r xss yss);
      try (now inversion_clear 1; eauto).
    - constructor; intro k; specialize (H k); destruct H as (?&?&?).
      do 2 eexists; intuition; eauto.
    - match goal with H:find_node _ _ = _ |- _ =>
                    apply scheduler_find_node in H end.
      econstructor; eauto; destruct n; simpl in *; eauto.
      rewrite schedule_eqs_permutation.
      match goal with H: Forall (fun e => sem_equation _ _ _ e -> _) _ |- _ =>
                      eapply Forall_impl_In with (2:=H) end.
      intros eq Hin Hsem.
      eapply Hsem, In_Forall; eauto.
  Qed.

End NLSCHEDULE.

Module NLScheduleFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX       Op)
       (Clks  : CLOCKS          Ids)
       (Syn   : NLSYNTAX        Ids Op       Clks)
       (Str   : STREAM              Op OpAux)
       (Ord   : ORDERED         Ids Op       Clks Syn)
       (Sem   : NLSEMANTICS     Ids Op OpAux Clks Syn Str Ord)
       (Mem   : MEMORIES        Ids Op       Clks Syn)
       (IsD   : ISDEFINED       Ids Op       Clks Syn         Mem)
       (IsF   : ISFREE          Ids Op       Clks Syn)
       (Typ   : NLTYPING        Ids Op       Clks Syn)
       (Clo   : NLCLOCKING      Ids Op       Clks Syn         Mem IsD IsF)
       (Sch   : EXT_NLSCHEDULER Ids Op       Clks Syn)
       <: NLSCHEDULE Ids Op OpAux Clks Syn Str Ord Sem Mem IsD IsF Typ Clo Sch.
  Include NLSCHEDULE Ids Op OpAux Clks Syn Str Ord Sem Mem IsD IsF Typ Clo Sch.
End NLScheduleFun.
