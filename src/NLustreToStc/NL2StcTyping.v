From Velus Require Import NLustre.
From Velus Require Import Stc.

From Velus Require Import NLustreToStc.Translation.

From Velus Require Import VelusMemory.
From Velus Require Import Common.
From Velus Require Import CoindToIndexed.
From Velus Require Import CommonTyping.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Permutation.

Open Scope nat.
Open Scope list.

Module Type NL2STCTYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import ComTyp: COMMONTYPING    Ids Op OpAux)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (       CStr  : COINDSTREAMS    Ids Op OpAux Cks)
       (       IStr  : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (       CIStr : COINDTOINDEXED  Ids Op OpAux        Cks CStr IStr)
       (Import CE    : COREEXPR        Ids Op OpAux ComTyp Cks      IStr)
       (Import NL    : NLUSTRE         Ids Op OpAux ComTyp Cks CStr IStr CIStr CE)
       (Import Stc   : STC             Ids Op OpAux ComTyp Cks      IStr       CE)
       (Import Trans : TRANSLATION     Ids Op OpAux Cks                 CE.Syn NL.Syn Stc.Syn NL.Mem).

  Lemma translate_eqn_wt:
    forall G vars vars' mems eq,
      NL.Typ.wt_equation G vars eq ->
      Permutation (vars' ++ mems) vars ->
      (forall x ty, In (x, ty) (gather_mem_eq eq) -> In (x, ty) mems) ->
      (forall x ty, In (x, ty) vars -> NL.IsV.Is_variable_in_eq x eq -> In (x, ty) vars') ->
      Forall (wt_trconstr (translate G) vars' mems) (translate_eqn eq).
  Proof.
    inversion_clear 1 as [??? Hin|?????? Find|];
      intros * SpecVars SpecMems SpecVars'; simpl.
    - constructor; auto.
      constructor; try rewrite SpecVars; auto with nldef.
    - destruct xs; auto.
      apply option_map_inv in Find as ((?&?)& Find &?); simpl in *; subst.
      apply find_unit_transform_units_forward in Find.
      constructor; auto.
      + econstructor; eauto.
        2,3:rewrite SpecVars; eauto using wt_clock.
        simpl; eapply Forall2_impl_In; eauto.
        intros ? (? & (?&?)) ? ? Hin.
        apply SpecVars' in Hin; auto with nldef.
      + rewrite map_map, Forall_map.
        apply Forall_forall. intros (?&?) Hin.
        econstructor; eauto.
        econstructor; eauto.
        * rewrite Forall_map in H4. eapply Forall_forall in H4 as (?&?); eauto.
          rewrite SpecVars; eauto.
        * rewrite Forall_map in H4. eapply Forall_forall in H4 as (?&?); eauto.
        * rewrite Forall_map in H5. eapply Forall_forall in H5; eauto.
          rewrite SpecVars; auto.
    - constructor; auto.
      + constructor; try rewrite SpecVars; auto.
        apply SpecMems; simpl; auto.
      + rewrite map_map, Forall_map.
        apply Forall_forall. intros (?&?) Hin'.
        econstructor; eauto.
        2:econstructor; eauto.
        * apply SpecMems; simpl; auto.
        * rewrite Forall_map in H4. eapply Forall_forall in H4 as (?&?); eauto.
          rewrite SpecVars; eauto.
        * rewrite Forall_map in H4. eapply Forall_forall in H4 as (?&?); eauto.
        * rewrite Forall_map in H5. eapply Forall_forall in H5; eauto.
          rewrite SpecVars; auto.
  Qed.

  Lemma translate_eqns_wt:
    forall eqs G vars vars' mems,
      Forall (NL.Typ.wt_equation G vars) eqs ->
      Permutation (vars' ++ mems) vars ->
      (forall x ty, In (x, ty) (gather_mems eqs) -> In (x, ty) mems) ->
      (forall x ty, In (x, ty) vars -> NL.IsV.Is_variable_in x eqs -> In (x, ty) vars') ->
      Forall (wt_trconstr (translate G) vars' mems) (translate_eqns eqs).
  Proof.
    unfold translate_eqns.
    induction eqs; intros * WT SpecVars SpecMems SpecVars';
      inv WT; simpl; try constructor.
    apply Forall_app; split; auto.
    - eapply translate_eqn_wt; eauto.
      + intros * Hin_mems.
        apply SpecMems; auto.
        unfold gather_mems; simpl.
        apply in_app; auto.
      + intros * Hin IsV.
        apply SpecVars'; auto.
        left; auto.
    - eapply IHeqs; eauto.
      + intros * Hin_mems.
        apply SpecMems; auto.
        unfold gather_mems; simpl.
        apply in_app; auto.
      + intros * Hin IsV.
        apply SpecVars'; auto.
        right; auto.
  Qed.
  Lemma filter_fst_idty:
    forall A B (xs: list (ident * (A * B))) P,
      idty (filter (fun x => P (fst x)) xs) = filter (fun x => P (fst x)) (idty xs).
  Proof.
    induction xs; simpl; intros; auto.
    cases; simpl; now rewrite IHxs.
  Qed.

  Lemma fst_partition_memories_gather_mems:
    forall G n,
      wt_node G n ->
      Permutation
        (idty (fst (partition
                      (fun x => PS.mem (fst x) (NL.Mem.memories n.(n_eqs)))
                      n.(n_vars))))
        (gather_mems n.(n_eqs)).
  Proof.
    unfold wt_node; intros * WT.
    rewrite fst_partition_filter.
    apply NoDup_Permutation.
    - apply NoDupMembers_NoDup, fst_NoDupMembers.
      rewrite map_fst_idty, filter_mem_fst.
      apply nodup_filter.
      pose proof (n.(n_nodup)) as Hnodup.
      apply NoDupMembers_app_r, NoDupMembers_app_l in Hnodup.
      now apply fst_NoDupMembers.
    - apply n_nodup_gather_mems.
    - assert (forall x, In x (vars_defined (filter is_fby (n_eqs n))) ->
                   InMembers x (n_vars n)) as Spec
          by (intro; rewrite <-fst_partition_memories_var_defined, fst_partition_filter,
                     filter_mem_fst, filter_In, fst_InMembers; intuition).
      pose proof (filter_fst_idty _ _(n_vars n)
                                  (fun x => PS.mem x (Mem.memories (n_eqs n)))) as E;
        setoid_rewrite E; clear E.
      setoid_rewrite filter_In.
      setoid_rewrite <-PSE.MP.Dec.F.mem_iff.
      unfold Mem.memories, gather_mems in *.
      destruct WT as (WT&?).
      induction (n_eqs n) as [|[]]; inversion_clear WT as [|?? WTeq]; simpl; auto.
      + split; try contradiction.
        setoid_rewrite PSE.MP.Dec.F.empty_iff; intuition.
      + inversion_clear WTeq as [| |????? Hint].
        * intros (x, t).
          rewrite In_fold_left_memory_eq, PSE.MP.Dec.F.add_iff, PSE.MP.Dec.F.empty_iff, <-IHl; auto; simpl;
            [|intros * Hin'; apply Spec; simpl; auto].
          intuition try congruence.
          -- subst.
             left.
             assert (In (x, t) (idty (n_in n ++ n_vars n ++ n_out n))) as Hin'
                 by (rewrite 2 idty_app, 2 in_app; auto).
             f_equal.
             eapply NoDupMembers_det; eauto.
             apply NoDupMembers_idty, n_nodup.
          -- take ((_,_) = _) and inv it.
             simpl in Spec.
             assert (InMembers x (n_vars n)) as Hin by auto.
             pose proof (n_nodup n) as Hnodup.
             rewrite fst_NoDupMembers, 2 map_app, NoDup_swap, <- 2 map_app, <-fst_NoDupMembers in Hnodup.
             eapply NoDupMembers_app_InMembers, NotInMembers_app in Hnodup as (? & ?); eauto.
             rewrite 2 idty_app, 2 in_app in Hint; destruct Hint as [Hint|[Hint|Hint]]; auto;
               apply In_InMembers in Hint; rewrite InMembers_idty in Hint; contradiction.
  Qed.

  Lemma translate_node_wt_inits:
    forall G n,
      wt_node G n ->
      wt_nexts (translate G) (translate_node n).(s_nexts).
  Proof.
    unfold translate_node, gather_eqs, wt_node, wt_nexts; simpl.
    intros G n (WT &?).
    cut (forall inits insts,
            wt_nexts (translate G) inits ->
            Forall (fun '(_, (c, t, _)) => wt_const (NL.Syn.types G) c t) (fst (fold_left gather_eq (n_eqs n) (inits, insts)))).
    - intros HH; apply HH; constructor.
    - induction WT as [|eq ? WTeq]; intros * WTinits; simpl; auto.
      destruct eq; simpl; cases.
      eapply IHWT; eauto.
      constructor; auto.
      inv WTeq; auto.
  Qed.

  Lemma translate_node_wt:
    forall G n,
      wt_node G n ->
      wt_system (translate G) (translate_node n).
  Proof.
    intros * WTn; split; [|split]; try (now apply translate_node_wt_inits);
      pose proof WTn as (WT & Henums).
    - eapply translate_eqns_wt; eauto.
      + simpl.
        repeat rewrite idty_app.
        rewrite <-app_assoc.
        apply Permutation_app_head.
        rewrite Permutation_app_comm, app_assoc.
        apply Permutation_app_tail.
        setoid_rewrite gather_eqs_fst_spec; rewrite <-fst_partition_memories_gather_mems; eauto.
        setoid_rewrite ps_from_list_gather_eqs_memories.
        rewrite <-idty_app.
        apply Permutation_map.
        rewrite <-permutation_partition; auto.
      + setoid_rewrite gather_eqs_fst_spec; auto.
      + simpl.
        intros * Hin IsV.
        rewrite 2 idty_app, 2 in_app.
        rewrite 2 idty_app, 2 in_app in Hin; destruct Hin as [|[|]]; auto.
        right; left.
        setoid_rewrite ps_from_list_gather_eqs_memories.
        rewrite snd_partition_filter.
        pose proof (filter_fst_idty _ _(n_vars n)
                                    (fun x => negb (PS.mem x (Mem.memories (n_eqs n))))) as E;
          setoid_rewrite E; clear E.
        rewrite filter_In, Bool.negb_true_iff, <-PSE.MP.Dec.F.not_mem_iff.
        intuition.
        eapply not_Is_variable_in_memories; eauto.
        apply NoDup_defs_node.
    - simpl.
      repeat rewrite idty_app.
      setoid_rewrite ps_from_list_gather_eqs_memories.
      setoid_rewrite snd_partition_filter.
      intros * Hin.
      eapply Henums with (x := x).
      repeat rewrite idty_app.
      repeat rewrite in_app in *.
      destruct Hin as [|[Hin|]]; auto.
      change (filter (fun x => negb (PS.mem (fst x) (Mem.memories (n_eqs n))))) with
          (filter (fun x : positive * (type * clock) => (fun y => negb (PS.mem y (Mem.memories (n_eqs n)))) (fst x)))
        in Hin.
      rewrite filter_fst_idty in Hin.
      apply in_filter in Hin; auto.
  Qed.

  Theorem translate_wt:
    forall G,
      wt_global G ->
      wt_program (translate G).
  Proof.
    intros; eapply transform_units_wt_program; eauto using translate_node_wt.
  Qed.

End NL2STCTYPING.

Module NL2StcTypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (ComTyp: COMMONTYPING    Ids Op OpAux)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CStr  : COINDSTREAMS    Ids Op OpAux Cks)
       (IStr  : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (CIStr : COINDTOINDEXED  Ids Op OpAux        Cks CStr IStr)
       (CE    : COREEXPR        Ids Op OpAux ComTyp Cks      IStr)
       (NL    : NLUSTRE         Ids Op OpAux ComTyp Cks CStr IStr CIStr CE)
       (Stc   : STC             Ids Op OpAux ComTyp Cks      IStr       CE)
       (Trans : TRANSLATION     Ids Op OpAux Cks                 CE.Syn NL.Syn Stc.Syn NL.Mem)
<: NL2STCTYPING Ids Op OpAux ComTyp Cks CStr IStr CIStr CE NL Stc Trans.
  Include NL2STCTYPING Ids Op OpAux ComTyp Cks CStr IStr CIStr CE NL Stc Trans.
End NL2StcTypingFun.
