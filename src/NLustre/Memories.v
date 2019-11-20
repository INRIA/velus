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

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Coq Require Import PArith.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.

From Coq Require Import Morphisms.
From Coq Require Import Permutation.

(** * Collecting memory cells *)

(**

  The [memories] function collects the set of variables that will turn
  into heap variables after compilation, ie. variables denoting an
  [fby] equation.

  We (ought to) have the following equivalence:
    [forall x, PS.In x (memories eqs) <-> ~ Is_Variable x eqs]

 *)

Module Type MEMORIES
       (Ids            : IDS)
       (Op             : OPERATORS)
       (Import CESyn   : CESYNTAX     Op)
       (Import Syn     : NLSYNTAX Ids Op CESyn).

  Definition memory_eq (mems: PS.t) (eq: equation) : PS.t :=
    match eq with
    | EqFby x _ _ _ => PS.add x mems
    | _ => mems
    end.

  Definition memories (eqs: list equation) : PS.t :=
    List.fold_left memory_eq eqs PS.empty.

  (** ** Properties *)

  Lemma In_fold_left_memory_eq:
    forall x eqs m,
      PS.In x (fold_left memory_eq eqs m)
      <-> PS.In x (fold_left memory_eq eqs PS.empty) \/ PS.In x m.
  Proof.
    induction eqs as [|eq]; simpl.
    - split; auto.
      intros [Hin|]; auto.
      apply not_In_empty in Hin; contradiction.
    - setoid_rewrite IHeqs; split.
      + intros [?|Hin]; auto.
        destruct eq; simpl; auto.
        apply PS.add_spec in Hin as [|]; auto.
        subst; rewrite PS.add_spec; auto.
      + intros [[?|Hin]|?]; auto.
        * destruct eq; simpl; try (apply not_In_empty in Hin; contradiction).
          apply PS.add_spec in Hin as [|Hin]; try (apply not_In_empty in Hin; contradiction).
          subst; rewrite PS.add_spec; auto.
        * destruct eq; simpl; auto.
          rewrite PS.add_spec; auto.
  Qed.

  Instance List_fold_left_memory_eq_Proper (eqs: list equation) :
    Proper (PS.eq ==> PS.eq) (fold_left memory_eq eqs).
  Proof.
    induction eqs as [|[]]; intros * ?? E; simpl; auto.
    apply IHeqs; rewrite E; reflexivity.
  Qed.

  Lemma in_memories_var_defined:
    forall x eqs,
      PS.In x (memories eqs) ->
      In x (vars_defined eqs).
  Proof.
    unfold memories.
    intros * Hin.
    induction eqs as [|eq]; simpl in *.
    - now apply PSF.empty_iff in Hin.
    - apply In_fold_left_memory_eq in Hin as [Hin|Hin].
      + apply in_app; auto.
      + destruct eq; simpl in Hin;
          try (apply PSF.empty_iff in Hin; contradiction).
        apply PS.add_spec in Hin as [|Hin];
          try (apply PSF.empty_iff in Hin; contradiction).
        subst; simpl; left; auto.
  Qed.

  Lemma in_memories_is_fby:
    forall eqs eq,
      In eq eqs ->
      NoDup (vars_defined eqs) ->
      forall x, In x (var_defined eq) ->
      PS.mem x (memories eqs) = is_fby eq.
  Proof.
    unfold memories.
    induction eqs as [|eq eqs]; simpl; try now intuition.
    intros eq' Hin Hndup ? Hin'.
    apply NoDup_app'_iff in Hndup as (Hndup_eq & Hndup_eqs & Hndup_def).
    destruct Hin as [|Hin].
    - subst eq'.
      assert (PS.mem x (fold_left memory_eq eqs PS.empty) = false).
      { apply PSP.Dec.F.not_mem_iff; intro.
        eapply Forall_forall in Hndup_def; eauto.
        eapply Hndup_def; eauto.
        now apply in_memories_var_defined.
      }
      destruct eq; simpl in *; auto.
      apply In_fold_left_memory_eq.
      right; apply PS.add_spec; intuition.
    - erewrite <-IHeqs; eauto.
      destruct eq; simpl; auto.
      assert (x <> i).
      { intro; subst x.
        eapply Forall_forall in Hndup_def; [|simpl; eauto].
        apply Hndup_def; simpl; eauto.
        unfold vars_defined. rewrite flat_map_concat_map.
        eapply in_concat'; eauto.
        now apply in_map.
      }
      destruct (PS.mem x (fold_left memory_eq eqs PS.empty)) eqn: E.
      + rewrite PS.mem_spec in *.
        rewrite In_fold_left_memory_eq; auto.
      + rewrite <-PSP.Dec.F.not_mem_iff in *.
        rewrite In_fold_left_memory_eq, PS.add_spec, PSF.empty_iff.
        intros [?|[?|?]]; auto.
  Qed.

  Lemma in_memories_filter_is_fby:
    forall x eqs,
      PS.In x (memories eqs) <-> In x (vars_defined (filter is_fby eqs)).
  Proof.
    unfold memories.
    induction eqs as [|eq eqs].
    - split; intro HH; try apply not_In_empty in HH; intuition.
    - destruct eq; simpl; (try now rewrite IHeqs).
      split; intro HH.
      + apply In_fold_left_memory_eq in HH.
        destruct HH as [HH|HH].
        * right; now apply IHeqs.
        * apply PS.add_spec in HH.
          destruct HH as [HH|HH]; subst; auto.
          contradiction (not_In_empty x).
      + apply In_fold_left_memory_eq.
        destruct HH as [HH|HH].
        * rewrite PS.add_spec; intuition.
        * apply IHeqs in HH; now left.
  Qed.


  Remark filter_mem_fst:
    forall A B p (xs: list (ident * (A * B))),
      map fst (filter (fun (x:ident*(A*B)) => PS.mem (fst x) p) xs)
      = filter (fun x => PS.mem x p) (map fst xs).
  Proof.
    induction xs as [|x xs]; auto.
    simpl.
    destruct (PS.mem (fst x) p); simpl;
      now rewrite IHxs.
  Qed.

  Lemma notb_filter_mem_fst:
    forall A B p (xs: list (ident * (A * B))),
      map fst (filter (notb (fun (x:ident*(A*B)) => PS.mem (fst x) p)) xs)
      = filter (notb (fun x => PS.mem x p)) (map fst xs).
  Proof.
    unfold notb; simpl.
    induction xs as [|x xs]; auto; simpl.
    destruct (negb (PS.mem (fst x) p)); simpl;
      now rewrite IHxs.
  Qed.

  Lemma fst_partition_memories_var_defined:
    forall n,
      Permutation
        (map fst (fst (partition
                         (fun x => PS.mem (fst x) (memories n.(n_eqs)))
                         n.(n_vars))))
        (vars_defined (filter is_fby n.(n_eqs))).
  Proof.
    intro n.
    match goal with |- Permutation (map fst (fst (partition ?p ?l))) _ =>
      assert (Permutation (map fst (fst (partition p l)))
                          (map fst (filter p n.(n_vars))))
                      as Hperm by now rewrite fst_partition_filter
    end.
    rewrite Hperm; clear Hperm.
    match goal with |- context[filter ?p ?l] =>
      rewrite <-(app_nil_r (filter p l))
    end.

    assert (NoDup (filter (fun x => PS.mem (fst x) (memories (n_eqs n))) (n_out n))).
    {
      apply NoDupMembers_NoDup, fst_NoDupMembers.
      rewrite filter_mem_fst.
      apply nodup_filter.
      pose proof (n.(n_nodup)) as Hnodup.
      do 2 apply NoDupMembers_app_r in Hnodup.
      now apply fst_NoDupMembers.
    }

    assert (filter (fun x=>PS.mem (fst x) (memories n.(n_eqs))) n.(n_out) = [])
      as Hfout.
    { simpl.
      apply Permutation_nil.
      apply NoDup_Permutation; auto using NoDup. intros x.
      split; try (now intuition); []. intro Hin.

      apply filter_In in Hin as [Hin Hmem].

      assert (In (fst x) (map fst (n_out n)))
        by now eapply in_map.

      assert (In (fst x) (vars_defined (filter is_fby (n_eqs n))))
        by now apply in_memories_filter_is_fby.

      eapply n.(n_vout); eauto.
    }

    rewrite <-Hfout; clear Hfout.
    rewrite filter_app, filter_mem_fst, <-n_defd.
    remember (memories n.(n_eqs)) as mems.
    set (P:=fun eqs eq=> In eq eqs ->
                      forall x, In x (var_defined eq) ->
                           PS.mem x mems = is_fby eq).
    assert (forall eq, P n.(n_eqs) eq) as Peq.
    { subst P mems.
      intro. intro Hin.
      apply in_memories_is_fby; auto.
      rewrite n_defd.
      apply fst_NoDupMembers.
      pose proof (n.(n_nodup)) as Hnodup.
      now apply NoDupMembers_app_r in Hnodup.
    }
    clear Heqmems.
    induction n.(n_eqs) as [|eq eqs]; auto.
    assert (forall eq, P eqs eq) as Peq'
        by (intros e Hin; apply Peq; now constructor 2).
    specialize (IHeqs Peq'). clear Peq'.
    destruct eq eqn:Heq; simpl;
      specialize (Peq eq); red in Peq; subst eq;
        simpl in Peq.

    + (* Case: EqDef *)
      rewrite Peq; eauto.
    + (* Case: EqApp *)
      assert (Pfilter: Permutation (filter (fun x => PS.mem x mems) l) []).
      {
        assert (Hmem_in: forall x, In x l -> PS.mem x mems = false)
          by now apply Peq; eauto.

        assert (Hfilter: filter (fun x => PS.mem x mems) l = []).
        {
          clear - Hmem_in.
          induction l as [ | a i IHi] ; auto; simpl.
          rewrite Hmem_in; try now constructor.
          apply IHi. intros.
          apply Hmem_in. now constructor 2.
        }

        now rewrite Hfilter.
      }

      unfold vars_defined; unfold var_defined; simpl.
      now rewrite <- filter_app, IHeqs, Pfilter.

    + (* Case: EqFby *)
      unfold vars_defined;
        simpl; unfold var_defined; simpl.
      rewrite Peq; eauto.
  Qed.

  Lemma snd_partition_memories_var_defined:
    forall n,
      Permutation
        (map fst (snd (partition
                         (fun x => PS.mem (fst x) (memories n.(n_eqs)))
                         n.(n_vars)) ++ n.(n_out)))
        (vars_defined (filter (notb is_fby) n.(n_eqs))).
  Proof.
    intro n.
    match goal with |- Permutation (map fst (snd (partition ?p ?l) ++ _)) _ =>
      assert (Permutation (map fst (snd (partition p l)))
                          (map fst (filter (notb p) n.(n_vars))))
                      as Hperm by (now rewrite snd_partition_filter)
    end.
    rewrite map_app, Hperm, <-map_app; clear Hperm.

    assert (filter (notb (fun x => PS.mem (fst x) (memories n.(n_eqs)))) n.(n_out) = n.(n_out))
      as Hfout.
    { simpl.
      pose proof (n_vout n) as Out.
      setoid_rewrite <-in_memories_filter_is_fby in Out.
      unfold notb.
      induction (n_out n) as [|(x, t)]; simpl; auto.
      destruct (PS.mem x (memories (n_eqs n))) eqn: E; simpl.
      - apply PSE.MP.Dec.F.mem_iff in E.
        exfalso; eapply Out; eauto.
        simpl; auto.
      - rewrite IHl; auto.
        intros ???; eapply Out; eauto.
        simpl; auto.
    }

    rewrite <-Hfout; clear Hfout.
    rewrite filter_app, notb_filter_mem_fst, <-n_defd.
    remember (memories n.(n_eqs)) as mems.
    set (P := fun eqs eq =>  In eq eqs ->
                          forall x, In x (var_defined eq) ->
                               PS.mem x mems = is_fby eq).
    assert (forall eq, P n.(n_eqs) eq) as Peq.
    { subst P mems.
      intro. intro Hin.
      apply in_memories_is_fby; auto.
      rewrite n_defd.
      apply fst_NoDupMembers.
      pose proof (n.(n_nodup)) as Hnodup.
      now apply NoDupMembers_app_r in Hnodup.
    }
    clear Heqmems.
    unfold notb, vars_defined.
    induction n.(n_eqs) as [|eq eqs]; auto.
    assert (forall eq, P eqs eq) as Peq'
        by (intros e Hin; apply Peq; now constructor 2).
    specialize (IHeqs Peq'). clear Peq'.
    destruct eq eqn:Heq; simpl;
      specialize (Peq eq); red in Peq; subst eq;
        simpl in Peq.

    + rewrite Peq; eauto.
      simpl; auto.

    + assert (Hmem_in: forall x, In x l -> PS.mem x mems = false)
        by now apply Peq; eauto.

      assert (Hfilter: filter (fun x => negb (PS.mem x mems)) l = l).
      { clear - Hmem_in.
        induction l as [ | a i IHi] ; auto; simpl.
        rewrite Hmem_in; simpl; try now constructor.
        rewrite IHi; auto.
        intros.
        apply Hmem_in. now constructor 2.
      }

      rewrite <-filter_app; setoid_rewrite Hfilter.
      apply Permutation_app_head; auto.

    + rewrite Peq; eauto.
  Qed.

End MEMORIES.

Module MemoriesFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (CESyn   : CESYNTAX     Op)
       (Syn     : NLSYNTAX Ids Op CESyn)
       <: MEMORIES Ids Op CESyn Syn.
  Include MEMORIES Ids Op CESyn Syn.
End MemoriesFun.
