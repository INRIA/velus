From Coq Require Import FSets.FMapPositive.
From Coq Require Import PArith.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.Memories.
From Velus Require Import Stc.StcSyntax.
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
    | EqFby x ck c0 _ => ((x, (c0, ck)) :: fst acc, snd acc)
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
    | EqApp (x :: xs) ck f les None =>
      [ SynStc.TcCall x (x :: xs) ck false f les ]
    | EqApp (x :: xs) ck f les (Some (r, ckr)) =>
      [ SynStc.TcReset x (Con ckr r true) f;
          SynStc.TcCall x (x :: xs) ck true f les ]
    | EqFby x ck _ e =>
      [ SynStc.TcNext x ck e ]
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
      destruct l as [ | x xs ]; auto.
      assert (Happ: gather_app_vars (EqApp (x :: xs) c i l0 o :: eqs)
                    = xs ++ gather_app_vars eqs)
        by now unfold gather_app_vars.

      assert (Hinst: map fst (gather_insts (EqApp (x :: xs) c i l0 o :: eqs))
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

  Lemma Forall_ValidId_idty:
    forall A B (xs: list (ident * (A * B))),
      Forall ValidId (idty xs) <-> Forall ValidId xs.
  Proof.
    induction xs as [|x xs]; split; inversion_clear 1; simpl; eauto;
      destruct x as (x & tyck); constructor; try rewrite IHxs in *; auto.
  Qed.

  Hint Resolve n_ingt0.

  (* =translate_node= *)
  (* TODO: fst (gather_eqs) should be a PS.t
     (i.e., do ps_from_list directly) *)
  Program Definition translate_node (n: node) : SynStc.system :=
    let gathered := gather_eqs n.(n_eqs) in
    let lasts := fst gathered in
    let lasts_ids := ps_from_list (map fst (fst gathered)) in
    let subs := snd gathered in
    let partitioned := partition (fun x => PS.mem (fst x) lasts_ids) n.(n_vars) in
    let vars := snd partitioned in
    {| SynStc.s_name  := n.(n_name);
       SynStc.s_subs  := subs;
       SynStc.s_in    := n.(n_in);
       SynStc.s_vars  := vars;
       SynStc.s_lasts := lasts;
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
    rewrite gather_eqs_snd_spec.
    unfold gather_insts, translate_eqns.
    induction (n_eqs n) as [|[]]; simpl; auto.
    destruct l; simpl; auto.
    destruct o as [(?&?)|]; simpl; auto.
  Qed.
  Next Obligation.
    rewrite gather_eqs_fst_spec.
    unfold gather_mems, translate_eqns.
    induction (n_eqs n) as [|[]]; simpl; auto.
    destruct l; simpl; auto.
    destruct o as [(?&?)|]; simpl; auto.
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
    destruct o as [(?&?)|]; simpl; rewrite IHl; auto.
  Qed.
  Next Obligation.
    unfold translate_eqns.
    induction (n_eqs n) as [|[]]; simpl; auto.
    - inversion 1.
    - destruct l; simpl; auto.
      destruct o as [(?&?)|]; simpl.
      + apply incl_cons.
        * constructor; auto.
        * apply incl_tl; auto.
      + apply incl_tl; auto.
  Qed.
  Next Obligation.
    unfold SynStc.reset_consistency.
    unfold translate_eqns in *; intros.
    destruct rst.
    - induction (n_eqs n) as [|[]]; simpl in *.
      + inv H.
      + inversion_clear H as [?? Step|]; try inv Step.
        right; apply IHl; auto.
      + destruct l; simpl in *; auto.
        destruct o as [(?&?)|]; simpl in *;
          inversion_clear H as [?? Step|?? Step']; try inv Step.
        *{ inversion_clear Step' as [?? Step|]; try inv Step.
           - left; constructor.
           - right; right; apply IHl; auto.
         }
        * right; apply IHl; auto.
      + inversion_clear H as [?? Step|]; try inv Step.
        right; apply IHl; auto.
    - pose proof (translate_node_obligation_4 n) as Eq;
        pose proof (translate_node_obligation_3 n) as Nodup.
      assert (forall s, SynStc.Reset_in s (translate_eqns (n_eqs n)) ->
                   SynStc.Step_with_reset_in s true (translate_eqns (n_eqs n)))
        as ResetSpec.
      { unfold translate_eqns in *.
        clear; intros.
        induction (n_eqs n) as [|[]]; simpl in *.
        - inv H.
        - inversion_clear H as [?? Rst|?]; try inv Rst.
          right; apply IHl; auto.
        - destruct l; simpl in *; auto.
          destruct o as [(?&?)|].
          + inversion_clear H as [?? Rst|?? Rst];
              inversion_clear Rst as [?? Rst'|]; try inv Rst'.
            * right; left; constructor.
            * apply Exists_app; apply IHl; auto.
          + inversion_clear H as [?? Rst|]; try inv Rst.
            apply Exists_app; apply IHl; auto.
        - inversion_clear H as [?? Rst|?]; try inv Rst.
          right; apply IHl; auto.
      }
      unfold gather_eqs in Nodup; rewrite Permutation_app_comm in Nodup;
      eapply NoDup_app_weaken in Nodup;
      rewrite Eq in Nodup; clear Eq; simpl in ResetSpec.
      unfold translate_eqns in *.
      intros * Reset.
      apply ResetSpec in Reset; clear ResetSpec.
      induction (n_eqs n) as [|[]]; simpl in *.
      + inv H.
      + inversion_clear H as [?? Step|]; try inv Step.
        inversion_clear Reset as [?? Rst|]; try inv Rst.
        apply IHl; auto.
      + destruct l; simpl in *; auto.
        destruct o as [(?&?)|]; simpl in *; inversion_clear Nodup as [|?? Notin];
          inversion_clear Reset as [?? Rst|?? Rst']; try inv Rst;
            inversion_clear H as [?? Step|?? Step']; try inv Step.
        *{ inversion_clear Step' as [?? Step|?? Hin]; try inv Step.
           inversion_clear Rst' as [?? Rst|]; try inv Rst.
           - apply Notin.
             clear - Hin; induction Hin as [?? Step|[]];
               try inv Step; simpl; auto.
           - apply IHl; auto.
         }
        * apply Notin.
          clear - Rst'; induction Rst' as [?? Step|[]];
            try inv Step; simpl; auto.
        * apply IHl; auto.
      + inversion_clear H as [?? Step|]; try inv Step.
        inversion_clear Reset as [?? Rst|]; try inv Rst.
        apply IHl; auto.
  Qed.
  Next Obligation.
    pose proof n.(n_good) as [ValidApp].
    split; [|split; [|split]]; auto.
    - rewrite (Permutation_app_comm n.(n_in)).
      rewrite Permutation_app_assoc.
      match goal with |- context [snd (partition ?p ?l)] =>
                      apply (Forall_app_weaken _ (fst (partition p l))) end.
      rewrite <-(Permutation_app_assoc (fst _)).
      rewrite <- (permutation_partition _ n.(n_vars)).
      rewrite <-(Permutation_app_assoc n.(n_vars)).
      rewrite Permutation_app_comm; auto.
    - pose proof (n_defd n) as Perm.
      unfold ValidId, NotReserved in *.
      apply Forall_forall; rewrite Forall_forall in ValidApp.
      intros * Hin.
      apply in_map with (f := fst) in Hin.
      rewrite fst_fst_gather_eqs_var_defined in Hin.
      rewrite <-is_filtered_vars_defined in Perm.
      assert (In (fst x) (vars_defined (filter is_def (n_eqs n)) ++
                                       vars_defined (filter is_app (n_eqs n)) ++
                                       vars_defined (filter is_fby (n_eqs n)))) as Hin'
          by (rewrite 2 in_app; intuition).
      eapply Permutation_in in Perm; eauto.
      apply in_map_iff in Perm as (? & E & Perm).
      rewrite <-E; apply ValidApp.
      apply in_app; auto.
    - pose proof (n_defd n) as Perm.
      unfold ValidId, NotReserved in *.
      apply Forall_forall; rewrite Forall_forall in ValidApp.
      intros * Hin.
      apply in_map with (f := fst) in Hin.
      assert (In (fst x) (map fst (snd (gather_eqs (n_eqs n))) ++ gather_app_vars (n_eqs n))) as Hin'
          by (apply in_app; auto).
      rewrite fst_snd_gather_eqs_var_defined in Hin'.
      rewrite <-is_filtered_vars_defined in Perm.
      assert (In (fst x) (vars_defined (filter is_def (n_eqs n)) ++
                                       vars_defined (filter is_app (n_eqs n)) ++
                                       vars_defined (filter is_fby (n_eqs n)))) as Hin''
          by (rewrite 2 in_app; intuition).
      eapply Permutation_in in Perm; eauto.
      apply in_map_iff in Perm as (? & E & Perm).
      rewrite <-E; apply ValidApp.
      apply in_app; auto.
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
