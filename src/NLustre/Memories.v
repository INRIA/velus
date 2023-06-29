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
 *)

Module Type MEMORIES
       (Ids          : IDS)
       (Op           : OPERATORS)
       (OpAux        : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Import Syn   : NLSYNTAX Ids  Op OpAux Cks CESyn).

  Definition memory_eq (mems: (PS.t * PS.t)) (eq: equation) : (PS.t * PS.t) :=
    match eq with
    | EqFby x _ _ _ _ => (PS.add x (fst mems), snd mems)
    | EqLast x _ _ _ _ => (fst mems, PS.add x (snd mems))
    | _ => mems
    end.

  Definition memories (eqs: list equation) : (PS.t * PS.t) :=
    List.fold_left memory_eq eqs (PS.empty, PS.empty).

  (** ** Properties *)

  Lemma memory_eq1 : forall x m eq,
      PS.In x (fst (memory_eq m eq))
      <-> PS.In x (fst (memory_eq (PS.empty, PS.empty) eq)) \/ PS.In x (fst m).
  Proof.
    intros ?? []; simpl; rewrite ?PS.add_spec, ?PSF.empty_iff.
    all:split; auto; intros; repeat (take (_ \/ _) and destruct it); auto; try now exfalso.
  Qed.

  Lemma memory_eq2 : forall x m eq,
      PS.In x (snd (memory_eq m eq))
      <-> PS.In x (snd (memory_eq (PS.empty, PS.empty) eq)) \/ PS.In x (snd m).
  Proof.
    intros ?? []; simpl; rewrite ?PS.add_spec, ?PSF.empty_iff.
    all:split; auto; intros; repeat (take (_ \/ _) and destruct it); auto; try now exfalso.
  Qed.

  Lemma In_fold_left_memory_eq1: forall x eqs m,
      PS.In x (fst (fold_left memory_eq eqs m))
      <-> Exists (fun eq => PS.In x (fst (memory_eq (PS.empty, PS.empty) eq))) eqs \/ PS.In x (fst m).
  Proof.
    induction eqs as [|eq]; simpl.
    - split; auto.
      intros [Ex|]; auto. inv Ex.
    - intros ?. rewrite IHeqs, memory_eq1.
      split; intros; repeat (take (_ \/ _) and destruct it); auto.
      inv H; auto.
  Qed.

  (* Global Instance List_fold_left_memory_eq_Proper (eqs: list equation) : *)
  (*   Proper (PS.eq ==> PS.eq) (fold_left memory_eq eqs). *)
  (* Proof. *)
  (*   induction eqs as [|[]]; intros * ?? E; simpl; auto. *)
  (*   apply IHeqs; rewrite E; reflexivity. *)
  (* Qed. *)

  Lemma in_memories_var_defined:
    forall x eqs,
      PS.In x (fst (memories eqs)) ->
      In x (vars_defined eqs).
  Proof.
    intros * In. unfold memories in *.
    rewrite In_fold_left_memory_eq1, ?PSF.empty_iff in In.
    destruct In as [In|[]]. simpl_Exists.
    unfold vars_defined. solve_In.
    destruct x0; simpl in *; rewrite ?PS.add_spec, ?PSF.empty_iff in *; try now exfalso.
    destruct In; auto.
  Qed.

  Lemma in_memories_filter_is_fby:
    forall x eqs,
      PS.In x (fst (memories eqs)) <-> In x (vars_defined (filter is_fby eqs)).
  Proof.
    intros. unfold memories, vars_defined.
    rewrite In_fold_left_memory_eq1, ?PSF.empty_iff.
    split; [intros [In|[]]|intros In].
    - simpl_Exists.
      destruct x0; simpl in *; rewrite ?PS.add_spec, ?PSF.empty_iff in *; try now exfalso.
      destruct In; subst; try now exfalso.
      solve_In. now constructor.
    - simpl_In.
      left. solve_Exists.
      destruct x0; simpl in *; try congruence.
      rewrite ?PS.add_spec, ?PSF.empty_iff.
      destruct Hinf; auto.
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
                         (fun x => PS.mem (fst x) (fst (memories n.(n_eqs))))
                         n.(n_vars))))
        (vars_defined (filter is_fby n.(n_eqs))).
  Proof.
    intro n.
    rewrite fst_partition_filter.
    apply NoDup_Permutation.
    - apply fst_NoDupMembers, NoDupMembers_filter, fst_NoDupMembers.
      eauto using NoDup_app_l, NoDup_app_r, n_nodup.
    - pose proof (NoDup_var_defined_n_eqs n) as ND.
      rewrite <-is_filtered_vars_defined in ND.
      eauto using NoDup_app_l, NoDup_app_r.
    - intros.
      split; intros In.
      + apply in_memories_filter_is_fby. simpl_In; auto using PSF.mem_2.
      + assert (List.In x (vars_defined (n_eqs n))) as In'
            by (apply in_memories_var_defined, in_memories_filter_is_fby; auto).
        rewrite n_defd in In'. apply in_app_iff in In' as [In'|In'].
        * solve_In. now apply in_memories_filter_is_fby.
        * exfalso. eapply n_vout; eauto.
  Qed.

  Lemma snd_partition_memories_var_defined:
    forall n,
      Permutation
        (map fst (snd (partition
                         (fun x => PS.mem (fst x) (fst (memories n.(n_eqs))))
                         n.(n_vars))) ++ map fst n.(n_out))
        (vars_defined (filter (notb is_fby) n.(n_eqs))).
  Proof.
    intro n.
    eapply Permutation_app_inv_l.
    rewrite app_assoc, <-map_app, <-permutation_partition, fst_partition_memories_var_defined, <-n_defd.
    induction (n_eqs n) as [|[]]; simpl; auto.
    - rewrite <-Permutation_middle; auto.
    - rewrite Permutation_swap. apply Permutation_app_head; auto.
  Qed.

  (** ** Fbys and Lasts in an equation *)

  Inductive Is_fby_in_eq : ident -> equation -> Prop :=
  | DefEqFby:
      forall x ck v e r,
        Is_fby_in_eq x (EqFby x ck v e r).

  Definition Is_fby_in x (eqs: list equation) : Prop :=
    List.Exists (Is_fby_in_eq x) eqs.

  Lemma Is_fby_in_vars_defined : forall x eqs,
      Is_fby_in x eqs <-> In x (vars_defined (filter is_fby eqs)).
  Proof.
    unfold Is_fby_in, vars_defined. split; intros In.
    - simpl_Exists. inv In. solve_In. simpl. auto.
    - simpl_In. destruct x0; simpl in *; try now exfalso.
      destruct Hinf; subst; [|now exfalso].
      solve_Exists. constructor.
  Qed.

  Inductive Is_last_in_eq : ident -> equation -> Prop :=
  | DefEqLast:
      forall x ty ck c0 ckrs,
        Is_last_in_eq x (EqLast x ty ck c0 ckrs).

  Definition Is_last_in x (eqs: list equation) : Prop :=
    List.Exists (Is_last_in_eq x) eqs.

  Lemma Is_last_in_lasts_defined : forall x eqs,
      Is_last_in x eqs <-> In x (lasts_defined eqs).
  Proof.
    unfold Is_last_in, lasts_defined. split; intros In.
    - simpl_Exists. inv In. solve_In. simpl. auto.
    - simpl_In. destruct x0; simpl in *; try now exfalso.
      destruct Hinf; subst; [|now exfalso].
      solve_Exists. constructor.
  Qed.

  Lemma fby_last_NoDup : forall n,
      forall x, Is_last_in x (n_eqs n) -> ~Is_fby_in x (n_eqs n).
  Proof.
    intros *. rewrite Is_fby_in_vars_defined, Is_last_in_lasts_defined.
    apply n_lastfby.
  Qed.

End MEMORIES.

Module MemoriesFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Syn   : NLSYNTAX Ids  Op OpAux Cks CESyn)
       <: MEMORIES Ids Op OpAux Cks CESyn Syn.
  Include MEMORIES Ids Op OpAux Cks CESyn Syn.
End MemoriesFun.
