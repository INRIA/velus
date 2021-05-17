From Coq Require Import FSets.FMapPositive.
From Coq Require Import PArith.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.Memories.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcIsReset.
From Velus Require Import Stc.StcIsNext.
From Velus Require Environment.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Morphisms.

(* Open Scope positive. *)
Open Scope list.

(** * Translation *)

Module Type TRANSLATION
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX      Op)
       (Import SynNL : NLSYNTAX  Ids Op CESyn)
       (SynStc       : STCSYNTAX Ids Op CESyn)
       (Import Mem   : MEMORIES  Ids Op CESyn SynNL).

  Definition gather_eq (acc: list (ident * (const * clock)) * list (ident * ident)) (eq: equation):
    list (ident * (const * clock)) * list (ident * ident) :=
    match eq with
    | EqDef _ _ _ => acc
    | EqApp [] _ _ _ _ => acc
    | EqApp (x :: _) _ f _ _ => (fst acc, (x, f) :: snd acc)
    | EqFby x ck c0 _ _ => ((x, (c0, ck)) :: fst acc, snd acc)
    end.

  Definition gather_eqs (eqs: list equation) : list (ident * (const * clock)) * list (ident * ident) :=
    fold_left gather_eq eqs ([], []).

  (** ** Translation *)

  Definition translate_eqn (eqn: equation) : list SynStc.trconstr :=
    match eqn with
    | EqDef x ck e =>
      [ SynStc.TcDef x ck e ]
    | EqApp [] _ _ _ _ =>
      []                        (* This way we can ensure b_blocks_in_eqs *)
    | EqApp (x :: xs) ck f les xrs =>
      let ckrs := map (fun '(xr, ckr) => Con ckr xr true) xrs in
      (SynStc.TcStep x (x :: xs) ck ckrs f les)
        ::(map (fun ckr => SynStc.TcInstReset x ckr f) ckrs)
    | EqFby x ck c0 e xrs =>
      let ckrs := map (fun '(xr, ckr) => Con ckr xr true) xrs in
      (SynStc.TcNext x ck ckrs e)
        ::(map (fun ckr => SynStc.TcReset x ckr c0) ckrs)
    end.

  (*   (** Remark: eqns ordered in reverse order of execution for coherence with *)
  (*      [Is_well_sch]. *) *)

  Definition translate_eqns (eqns: list equation) : list SynStc.trconstr :=
    flat_map translate_eqn eqns.

  (** Properties of translation functions *)

  Lemma ps_from_list_gather_eqs_memories:
    forall eqs, PS.eq (ps_from_list (map fst (fst (gather_eqs eqs)))) (memories eqs).
  Proof.
    induction eqs as [|eq eqs IH]; [reflexivity|].
    unfold memories, gather_eqs.
    assert (forall eqs F S,
               PS.eq (ps_from_list (map fst (fst (fold_left gather_eq eqs (F, S)))))
                     (fold_left memory_eq eqs (ps_from_list (map fst F)))) as HH.
    {
      clear eq eqs IH; induction eqs as [|eq eqs IH]; [reflexivity|].
      intros F S.
      destruct eq;
        [ now apply IH
        | now destruct l; apply IH
        | ].
      simpl; rewrite IH; rewrite add_ps_from_list_cons; reflexivity.
    }
    rewrite HH; reflexivity.
  Qed.

  Lemma gather_eqs_fst_spec:
    forall eqs, Permutation (map fst (fst (gather_eqs eqs))) (gather_mems eqs).
  Proof.
    intro eqs.
    assert (Hgen: forall F S,
               Permutation (map fst (fst (fold_left gather_eq eqs (F, S))))
                           (map fst F ++ gather_mems eqs)).
    {
      induction eqs as [ | eq eqs IHeqs ]; intros F S; simpl.
      - now rewrite app_nil_r.
      - destruct eq.
        + simpl; rewrite IHeqs; auto.
        + destruct l; simpl; rewrite IHeqs; auto.
        + simpl. rewrite IHeqs.
          simpl. now rewrite <-Permutation_middle.
    }
    now apply Hgen.
  Qed.

  Lemma gather_eqs_snd_spec:
    forall eqs, Permutation (snd (gather_eqs eqs)) (gather_insts eqs).
  Proof.
    intro eqs.
    assert (Hgen: forall F S,
               Permutation (snd (fold_left gather_eq eqs (F, S)))
                           (S ++ gather_insts eqs)).
    {
      induction eqs as [ | eq eqs IHeqs ]; intros F S; simpl.
      - now rewrite app_nil_r.
      - destruct eq as [ | is ck f les | ]; simpl; try rewrite IHeqs; auto.
        unfold gather_insts.
        destruct is; rewrite IHeqs; auto;
          rewrite <-app_comm_cons, Permutation_middle; auto.
    }

    now apply Hgen.
  Qed.

  Lemma fst_snd_gather_eqs_var_defined:
    forall eqs,
      Permutation (map fst (snd (gather_eqs eqs)) ++ gather_app_vars eqs)
                  (vars_defined (filter is_app eqs)).
  Proof.
    intro eqs.
    assert (Hperm: Permutation (map fst (gather_insts eqs) ++ gather_app_vars eqs)
                               (vars_defined (filter is_app eqs))).
    {
      induction eqs as [|[] eqs]; simpl; auto.
      destruct l as [ | x xs ]; simpl; auto.
      assert (Happ: gather_app_vars (EqApp (x :: xs) c i l0 l1 :: eqs)
                    = xs ++ gather_app_vars eqs)
        by now unfold gather_app_vars.

      assert (Hinst: map fst (gather_insts (EqApp (x :: xs) c i l0 l1 :: eqs))
                     = x :: map fst (gather_insts eqs))
        by now unfold gather_insts.

      simpl.
      apply Permutation_cons; auto.
      rewrite Permutation_swap.
      apply Permutation_app; auto.
    }

    rewrite <- Hperm.
    apply Permutation_app_tail.
    now rewrite gather_eqs_snd_spec.
  Qed.

  Lemma fst_fst_gather_eqs_var_defined:
    forall eqs,
      Permutation (map fst (fst (gather_eqs eqs)))
                  (vars_defined (filter is_fby eqs)).
  Proof.
    intro eqs.
    assert (Hperm: Permutation (gather_mems eqs)
                               (vars_defined (filter is_fby eqs))).
    {
      induction eqs as [|eq eqs]; auto.
      destruct eq; try (now simpl; auto).
    }

    rewrite <- Hperm.
    apply gather_eqs_fst_spec.
  Qed.

  Lemma In_fst_fold_left_gather_eq:
    forall eqs xc mems insts,
      In xc (fst (fold_left gather_eq eqs (mems, insts))) <->
      In xc mems \/ In xc (fst (fold_left gather_eq eqs ([], insts))).
  Proof.
    induction eqs as [|[]]; simpl; intros; auto.
    - split; auto; intros [|]; auto; contradiction.
    - destruct l; simpl in *; auto.
    - rewrite IHeqs; symmetry; rewrite IHeqs.
      split; intros [Hin|Hin']; auto.
      + now left; right.
      + destruct Hin' as [[|]|]; auto; try contradiction.
        now left; left.
      + destruct Hin; auto.
        now right; left; left.
  Qed.

  Lemma In_snd_fold_left_gather_eq:
    forall eqs xf mems insts,
      In xf (snd (fold_left gather_eq eqs (mems, insts))) <->
      In xf insts \/ In xf (snd (fold_left gather_eq eqs (mems, []))).
  Proof.
    induction eqs as [|[]]; simpl; intros; auto.
    - split; auto; intros [|]; auto; contradiction.
    - destruct l; simpl in *; auto.
      rewrite IHeqs; symmetry; rewrite IHeqs.
      split; intros [Hin|Hin']; auto.
      + now left; right.
      + destruct Hin' as [[|]|]; auto; try contradiction.
        now left; left.
      + destruct Hin; auto.
        now right; left; left.
  Qed.

  Lemma gather_mems_nexts_of : forall eqs,
      Permutation (gather_mems eqs) (SynStc.nexts_of (translate_eqns eqs)).
  Proof.
    intros *.
    unfold gather_mems, translate_eqns.
    induction eqs as [|[]]; simpl; auto.
    - destruct l; simpl; auto.
      induction l1; simpl; auto.
    - induction l; simpl; auto.
  Qed.

  Lemma resets_of_incl : forall eqs,
      incl (SynStc.resets_of (translate_eqns eqs)) (SynStc.nexts_of (translate_eqns eqs)).
  Proof.
    induction eqs as [|[]]; simpl in *; auto.
    - reflexivity.
    - destruct l; auto.
      induction l1; simpl; auto.
    - induction l; simpl; auto using incl_tl, incl_cons, in_eq.
  Qed.

  Lemma iresets_of_incl : forall eqs,
      incl (SynStc.iresets_of (translate_eqns eqs)) (SynStc.steps_of (translate_eqns eqs)).
  Proof.
    induction eqs as [|[]]; simpl in *; auto.
    - reflexivity.
    - destruct l; simpl; auto using incl_tl', incl_tl.
      induction l1; simpl; auto using incl_tl, incl_cons, in_eq.
    - induction l; simpl; auto.
  Qed.

  Corollary iresets_of_incl' : forall eqs,
      incl (map fst (SynStc.iresets_of (translate_eqns eqs))) (map fst (SynStc.steps_of (translate_eqns eqs))).
  Proof.
    intros. apply incl_map, iresets_of_incl.
  Qed.

  Hint Resolve n_ingt0.

  Module Import StcIsReset := StcIsResetFun Ids Op CESyn SynStc.
  Module Import StcIsNext := StcIsNextFun Ids Op CESyn SynStc.

  (* =translate_node= *)
  Program Definition translate_node (n: node) : SynStc.system :=
    let gathered := gather_eqs n.(n_eqs) in
    let nexts := fst gathered in
    let resets_ids := ps_from_list (map fst (fst gathered)) in
    let subs := snd gathered in
    let partitioned := partition (fun x => PS.mem (fst x) resets_ids) n.(n_vars) in
    let vars := snd partitioned in
    {| SynStc.s_name  := n.(n_name);
       SynStc.s_subs  := subs;
       SynStc.s_in    := n.(n_in);
       SynStc.s_vars  := vars;
       SynStc.s_nexts := nexts;
       SynStc.s_out   := n.(n_out);
       SynStc.s_tcs   := translate_eqns n.(n_eqs)
    |}.
  Next Obligation.
    rewrite fst_fst_gather_eqs_var_defined, <-fst_partition_memories_var_defined.
    setoid_rewrite ps_from_list_gather_eqs_memories.
    rewrite Permutation_app_comm, <-app_assoc, NoDup_swap,
    <-app_assoc, (app_assoc _ _ (map fst (n_in n))),
    <-map_app, <-permutation_partition, Permutation_app_comm, <-app_assoc.
    apply NoDup_swap; rewrite <-2 map_app; apply fst_NoDupMembers, n_nodup.
  Qed.
  Next Obligation.
    rewrite fst_fst_gather_eqs_var_defined.
    eapply (NoDup_app_weaken _ (gather_app_vars n.(n_eqs))).
    rewrite <-app_assoc.
    rewrite fst_snd_gather_eqs_var_defined.
    rewrite Permutation_app_comm.
    eapply (NoDup_app_weaken _ (vars_defined (filter is_def n.(n_eqs)))).
    rewrite Permutation_app_comm.
    unfold vars_defined.
    setoid_rewrite flat_map_concat_map.
    rewrite <- 2 concat_app.
    rewrite <- 2 map_app.
    rewrite is_filtered_eqs.
    pose proof (NoDup_var_defined_n_eqs) as HH.
    unfold vars_defined in HH. setoid_rewrite flat_map_concat_map in HH.
    apply HH.
  Qed.
  Next Obligation.
    setoid_rewrite gather_eqs_snd_spec.
    unfold gather_insts, translate_eqns.
    induction (n_eqs n) as [|[]]; simpl; auto; try reflexivity.
    destruct l; simpl; auto.
    - rewrite IHl. induction l1; simpl; try reflexivity.
      rewrite <-Permutation_middle; simpl.
      rewrite <-IHl1. intuition.
    - rewrite IHl. induction l; simpl; try reflexivity.
      rewrite <-IHl0. reflexivity.
  Qed.
  Next Obligation.
    rewrite gather_eqs_snd_spec.
    unfold gather_insts, translate_eqns.
    induction (n_eqs n) as [|[]]; simpl; auto.
    destruct l; simpl; auto.
    - constructor.
      induction l1; simpl; auto.
    - induction l; simpl; auto.
  Qed.
  Next Obligation.
    rewrite gather_eqs_fst_spec.
    apply gather_mems_nexts_of.
  Qed.
  Next Obligation.
    pose proof (translate_node_obligation_3 n) as Nodup; simpl in *.
    rewrite gather_eqs_fst_spec, gather_mems_nexts_of in Nodup.
    apply NoDup_app_weaken in Nodup.
    unfold SynStc.reset_consistency.
    unfold translate_eqns in *; intros.
    induction (n_eqs n) as [|[]]; simpl in *.
    - inv H.
    - inv H. inv H1.
      rewrite IHl; auto.
      split; intro H. right; auto. inv H; auto. inv H2.
    - destruct l; simpl in *; auto.
      rewrite SynStc.Next_with_reset_in_cons_not_next in H. 2:congruence.
      induction l1 as [|(?&?) ?]; simpl in *; auto.
      + rewrite Is_reset_in_reflect in *; auto.
      + rewrite SynStc.Next_with_reset_in_cons_not_next in H. 2:congruence.
        rewrite Is_reset_in_reflect in *; simpl in *. auto.
    - inv Nodup.
      rewrite SynStc.nexts_of_app in H2, H3.
      split; intros.
      + right.
        inv H; [inv H4|apply Exists_app' in H4 as [Ex|Ex]].
        * apply Exists_app'; left.
          apply Exists_map, Exists_exists.
          exists ckr; split; auto using SynStc.Is_reset_in_tc.
        * exfalso. clear - Ex.
          induction l; simpl in *; inv Ex; auto. inv H0.
        * apply Exists_app'; right.
          apply NoDup_app_r in H3.
          apply IHl; auto.
      + inv H; [inv H4|apply Exists_app' in H4 as [Ex|Ex]];
          (inv H0; [inv H1|apply Exists_app' in H1 as [Ex'|Ex']]).
        * rewrite Exists_map in Ex'. apply Exists_exists in Ex' as (?&In&Res).
          inv Res; auto.
        * apply Exists_exists in Ex' as (?&In&Res).
          exfalso.
          apply H2, in_or_app, or_intror, resets_of_incl, resets_of_In. exists ckr.
          apply Exists_exists; eauto.
        * rewrite Exists_map in Ex. apply Exists_exists in Ex as (?&?&Next); inv Next.
        * rewrite Exists_map in Ex. apply Exists_exists in Ex as (?&?&Next); inv Next.
        * rewrite Exists_map in Ex'. apply Exists_exists in Ex' as (?&?&Ex'). inv Ex'.
          exfalso.
          eapply H2, in_or_app, or_intror, nexts_of_In, Next_with_reset_in_Is_next_in; eauto.
        * apply NoDup_app_r in H3.
          rewrite IHl; auto.
  Qed.
  Next Obligation.
    unfold translate_eqns.
    induction (n_eqs n) as [|[]]; simpl; auto.
    - inversion 1.
    - destruct l; simpl; auto.
      induction l1; simpl; auto.
    - induction l; simpl; auto using incl_tl, incl_cons, in_eq.
  Qed.
  Next Obligation.
    rewrite <-map_app.
    assert (Permutation (map fst
                             (snd
                                (partition
                                   (fun x0 =>
                                      PS.mem (fst x0) (ps_from_list (map fst (fst (gather_eqs (n_eqs n))))))
                                   (n_vars n)) ++ n_out n))
                        (map fst
                             (snd
                                (partition
                                   (fun x0 =>
                                      PS.mem (fst x0) (memories (n_eqs n)))
                                   (n_vars n)) ++ n_out n))) as E.
    { rewrite 2 map_app; apply Permutation_app_tail, Permutation_map.
      now setoid_rewrite ps_from_list_gather_eqs_memories.
    }
    rewrite E; clear E.
    rewrite snd_partition_memories_var_defined.
    unfold SynStc.variables, translate_eqns, vars_defined.
    induction (n_eqs n) as [|[]]; simpl; auto.
    destruct l; simpl; auto.
    - constructor. apply Permutation_app_head.
      induction l1; simpl; auto.
    - induction l; simpl; auto.
  Qed.
  Next Obligation.
    pose proof (translate_node_obligation_3 n) as Nodup; simpl in *.
    pose proof (translate_node_obligation_5 n) as Insts; simpl in *.
    rewrite Insts in Nodup. clear Insts.
    apply NoDup_app_r in Nodup.
    unfold SynStc.ireset_consistency.
    unfold translate_eqns in *; intros.
    induction (n_eqs n) as [|[]]; simpl in *.
    - inv H.
    - inv H. inv H1.
      rewrite IHl; auto.
      split; intro H. right; auto. inv H; auto. inv H2.
    - destruct l; simpl in *; auto.
      inv Nodup.
      rewrite SynStc.steps_of_app, map_app in H2, H3.
      split; intros.
      + right.
        inv H; [inv H4|apply Exists_app' in H4 as [Ex|Ex]].
        * apply Exists_app'; left.
          apply Exists_map, Exists_exists.
          exists ckr; split; auto using SynStc.Is_ireset_in_tc.
        * exfalso. clear - Ex.
          induction l1; simpl in *; inv Ex; auto. inv H0.
        * apply Exists_app'; right.
          apply NoDup_app_r in H3.
          apply IHl; auto.
      + inv H; [inv H4|apply Exists_app' in H4 as [Ex|Ex]];
          (inv H0; [inv H1|apply Exists_app' in H1 as [Ex'|Ex']]).
        * rewrite Exists_map in Ex'. apply Exists_exists in Ex' as (?&In&Res).
          inv Res; auto.
        * apply Exists_exists in Ex' as (?&In&Res).
          exfalso.
          apply H2, in_or_app, or_intror, iresets_of_incl', SynStc.iresets_of_In. exists ckr.
          apply Exists_exists; eauto.
        * rewrite Exists_map in Ex. apply Exists_exists in Ex as (?&?&Next); inv Next.
        * rewrite Exists_map in Ex. apply Exists_exists in Ex as (?&?&Next); inv Next.
        * rewrite Exists_map in Ex'. apply Exists_exists in Ex' as (?&?&Ex'). inv Ex'.
          exfalso.
          eapply H2, in_or_app, or_intror, SynStc.steps_of_In, SynStc.Step_with_ireset_in_Is_step_in; eauto.
        * apply NoDup_app_r in H3.
          rewrite IHl; auto.
    - inv H. inv H1.
      rewrite SynStc.steps_of_app, map_app in Nodup.
      apply NoDup_app_r in Nodup.
      apply Exists_app' in H1 as [Ex|Ex].
      + exfalso. clear - Ex. induction l; inv Ex; auto. inv H0.
      + rewrite IHl; auto.
        unfold SynStc.Is_ireset_in.
        rewrite Exists_cons, Exists_app'. intuition.
        * inv H2.
        * exfalso. clear - H0. induction l; inv H0; auto. inv H1.
  Qed.
  Next Obligation.
    unfold translate_eqns.
    induction (n_eqs n) as [|[]]; simpl; auto.
    - inversion 1.
    - destruct l; simpl; auto.
      induction l1; simpl; auto using incl_tl, incl_cons, in_eq.
    - induction l; simpl; auto.
  Qed.
  Next Obligation.
    pose proof n.(n_good) as [ValidApp].
    split; [|split; [|split]]; auto.
    - rewrite (Permutation_app_comm n.(n_in)).
      rewrite Permutation_app_assoc.
      rewrite Forall_map in *.
      match goal with |- context [snd (partition ?p ?l)] =>
                      apply (Forall_app_weaken _ (fst (partition p l))) end.
      rewrite <-(Permutation_app_assoc (fst _)).
      rewrite <- (permutation_partition _ n.(n_vars)).
      rewrite <-(Permutation_app_assoc n.(n_vars)).
      rewrite Permutation_app_comm; auto.
    - pose proof (n_defd n) as Perm.
      apply Forall_forall; rewrite Forall_forall in ValidApp.
      intros * Hin.
      rewrite fst_fst_gather_eqs_var_defined in Hin.
      rewrite <-is_filtered_vars_defined in Perm.
      assert (In x (vars_defined (filter is_def (n_eqs n)) ++
                                       vars_defined (filter is_app (n_eqs n)) ++
                                       vars_defined (filter is_fby (n_eqs n)))) as Hin'
          by (rewrite 2 in_app; intuition).
      eapply Permutation_in in Perm; eauto.
      apply in_map_iff in Perm as (? & E & Perm).
      rewrite <-E; apply ValidApp.
      apply in_map, in_app; auto.
    - pose proof (n_defd n) as Perm.
      apply Forall_forall; rewrite Forall_forall in ValidApp.
      intros * Hin.
      assert (In x (map fst (snd (gather_eqs (n_eqs n))) ++ gather_app_vars (n_eqs n))) as Hin'
          by (apply in_app; auto).
      rewrite fst_snd_gather_eqs_var_defined in Hin'.
      rewrite <-is_filtered_vars_defined in Perm.
      assert (In x (vars_defined (filter is_def (n_eqs n)) ++
                                 vars_defined (filter is_app (n_eqs n)) ++
                                 vars_defined (filter is_fby (n_eqs n)))) as Hin''
          by (rewrite 2 in_app; intuition).
      eapply Permutation_in in Perm; eauto.
      apply in_map_iff in Perm as (? & E & Perm).
      rewrite <-E; apply ValidApp.
      apply in_map, in_app; auto.
  Qed.

  Definition translate (G: global) : SynStc.program :=
    map translate_node G.

  Lemma find_system_translate:
    forall f G s prog',
      SynStc.find_system f (translate G) = Some (s, prog') ->
      exists n, find_node f G = Some n
           /\ s = translate_node n.
  Proof.
    induction G as [|n G]; [now inversion 1|].
    intros * Hfind.
    simpl in Hfind.
    destruct (EquivDec.equiv_dec n.(n_name) f) as [Heq|Hneq].
    - rewrite Heq, ident_eqb_refl in Hfind.
      injection Hfind; intros; subst.
      exists n. split; auto.
      simpl. now rewrite Heq, ident_eqb_refl.
    - apply ident_eqb_neq in Hneq. rewrite Hneq in Hfind.
      apply IHG in Hfind. destruct Hfind as (n' & Hfind & Hcls).
      exists n'. simpl. rewrite Hneq. auto.
  Qed.

  Lemma find_node_translate:
    forall f G n,
      find_node f G = Some n ->
      exists s P,
        SynStc.find_system f (translate G) = Some (s, P)
        /\ s = translate_node n.
  Proof.
    induction G as [|node g]; [now inversion 1|].
    intros * Hfind.
    simpl in Hfind.
    destruct (EquivDec.equiv_dec node.(n_name) f) as [Heq|Hneq].
    - rewrite Heq, ident_eqb_refl in Hfind.
      injection Hfind; intros; subst node.
      exists (translate_node n), (translate g). split; auto.
      simpl. now rewrite Heq, ident_eqb_refl.
    - apply ident_eqb_neq in Hneq. rewrite Hneq in Hfind.
      apply IHg in Hfind. destruct Hfind as (s & P & Hfind & Hbl).
      exists s, P. split; auto. simpl. now rewrite Hneq.
  Qed.

End TRANSLATION.

Module TranslationFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (CESyn  : CESYNTAX      Op)
       (SynNL  : NLSYNTAX  Ids Op CESyn)
       (SynStc : STCSYNTAX Ids Op CESyn)
       (Mem    : MEMORIES  Ids Op CESyn SynNL)
<: TRANSLATION Ids Op CESyn SynNL SynStc Mem.
  Include TRANSLATION Ids Op CESyn SynNL SynStc Mem.
End TranslationFun.
