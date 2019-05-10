From Velus Require Import NLustre.
From Velus Require Import SyBloc.

From Velus Require Import NLustreToSyBloc.Translation.

From Velus Require Import RMemory.
From Velus Require Import Common.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Permutation.

Open Scope nat.
Open Scope list.

Module Type NL2SBCLOCKING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import Str   : STREAM          Op OpAux)
       (Import CE    : COREEXPR    Ids Op OpAux Str)
       (Import NL    : NLUSTRE     Ids Op OpAux Str CE)
       (Import SB    : SYBLOC      Ids Op OpAux Str CE)
       (Import Trans : TRANSLATION Ids Op       CE.Syn NL.Syn SB.Syn NL.Mem).


  (* Lemma translate_eqn_wt: *)
  (*   forall G vars vars' mems eq, *)
  (*     NL.Typ.wt_equation G vars eq -> *)
  (*     Permutation (vars' ++ mems) vars -> *)
  (*     (forall x ty, In (x, ty) vars -> In x (gather_mem_eq eq) -> In (x, ty) mems) -> *)
  (*     (forall x ty, In (x, ty) vars -> NL.IsV.Is_variable_in_eq x eq -> In (x, ty) vars') -> *)
  (*     Forall (wt_equation (translate G) vars' mems) (translate_eqn eq). *)
  (* Proof. *)
  (*   inversion_clear 1 as [??? Hin|????? Find|?????? Find|]; *)
  (*     intros * SpecVars SpecMems SpecVars'; simpl. *)
  (*   - constructor; auto. *)
  (*     constructor; try rewrite SpecVars; auto. *)
  (*   - destruct xs; auto. *)
  (*     constructor; auto. *)
  (*     apply find_node_translate in Find as (?&?&?&?); subst. *)
  (*     econstructor; try rewrite SpecVars; eauto. *)
  (*     simpl; eapply Forall2_impl_In; eauto. *)
  (*     intros ? () ** Hin. *)
  (*     apply SpecVars' in Hin; auto. *)
  (*   - destruct xs; auto. *)
  (*     apply find_node_translate in Find as (?&?&?&?); subst. *)
  (*     constructor; auto. *)
  (*     + econstructor; eauto. *)
  (*       rewrite SpecVars; auto using wt_clock. *)
  (*     + constructor; auto. *)
  (*       econstructor; try rewrite SpecVars; eauto. *)
  (*       simpl; eapply Forall2_impl_In; eauto. *)
  (*       intros ? () ** Hin. *)
  (*       apply SpecVars' in Hin; auto. *)
  (*   - constructor; auto. *)
  (*     constructor; try rewrite SpecVars; auto. *)
  (*     apply SpecMems; simpl; auto. *)
  (*     congruence. *)
  (* Qed. *)

  (* Lemma translate_eqns_wt: *)
  (*   forall eqs G vars vars' mems, *)
  (*     Forall (NL.Typ.wt_equation G vars) eqs -> *)
  (*     Permutation (vars' ++ mems) vars -> *)
  (*     (forall x ty, In (x, ty) vars -> In x (gather_mems eqs) -> In (x, ty) mems) -> *)
  (*     (forall x ty, In (x, ty) vars -> Is_variable_in x eqs -> In (x, ty) vars') -> *)
  (*     Forall (wt_equation (translate G) vars' mems) (translate_eqns eqs). *)
  (* Proof. *)
  (*   unfold translate_eqns, concatMap. *)
  (*   induction eqs; intros * WT SpecVars SpecMems SpecVars'; *)
  (*     inv WT; simpl; try constructor. *)
  (*   apply Forall_app; split; auto. *)
  (*   - eapply translate_eqn_wt; eauto. *)
  (*     + intros * Hin Hin_mems. *)
  (*       apply SpecMems; auto. *)
  (*       unfold gather_mems, concatMap; simpl. *)
  (*       apply in_app; auto. *)
  (*     + intros * Hin IsV. *)
  (*       apply SpecVars'; auto. *)
  (*       left; auto. *)
  (*   - eapply IHeqs; eauto. *)
  (*     + intros * Hin Hin_mems. *)
  (*       apply SpecMems; auto. *)
  (*       unfold gather_mems, concatMap; simpl. *)
  (*       apply in_app; auto. *)
  (*     + intros * Hin IsV. *)
  (*       apply SpecVars'; auto. *)
  (*       right; auto. *)
  (* Qed. *)

  (* Definition fby_eq (acc: list (ident * type)) (eq: NL.Syn.equation) : list (ident * type) := *)
  (*   match eq with *)
  (*   | NL.Syn.EqDef x _ _ *)
  (*   | NL.Syn.EqApp x _ _ _ _ => acc *)
  (*   | NL.Syn.EqFby x _ c _ => (x, type_const c) :: acc *)
  (*   end. *)

  (* Definition fbys (eqs: list NL.Syn.equation) : list (ident * type) := *)
  (*   fold_left fby_eq eqs []. *)

  (* Lemma in_fbys_spec: *)
  (*   forall x t eqs acc, *)
  (*     In (x, t) (fold_left fby_eq eqs acc) <-> In (x, t) (fbys eqs) \/ In (x, t) acc. *)
  (* Proof. *)
  (*   unfold fbys. *)
  (*   induction eqs as [|[]]; simpl; auto. *)
  (*   - firstorder. *)
  (*   - intros. *)
  (*     rewrite IHeqs; symmetry; rewrite IHeqs. *)
  (*     split; simpl; intuition. *)
  (* Qed. *)

  (* Lemma n_nodup_fbys: *)
  (*   forall n, *)
  (*     NoDup (fbys (n_eqs n)). *)
  (* Proof. *)
  (*   intro. *)
  (*   pose proof (NoDup_var_defined_n_eqs n) as Hnodup. *)
  (*   assert (NoDup (@nil (ident * type))) as Hnodup_acc by constructor. *)
  (*   assert (forall x, In x (vars_defined (n_eqs n)) -> ~ InMembers x (@nil (ident * type))) *)
  (*     as Spec by (inversion 2). *)
  (*   unfold fbys, vars_defined, concatMap in *. *)
  (*   revert Hnodup_acc Spec; generalize (@nil (ident * type)). *)
  (*   induction (n_eqs n) as [|[]]; simpl in *; intros; auto. *)
  (*   - inv Hnodup; auto. *)
  (*   - apply NoDup_comm, NoDup_app_weaken in Hnodup; auto. *)
  (*     apply IHl; auto. *)
  (*     intros; apply Spec, in_app; auto. *)
  (*   - inv Hnodup; apply IHl; auto. *)
  (*     + constructor; auto. *)
  (*       apply NotInMembers_NotIn; auto. *)
  (*     + intros ? Hin. *)
  (*       apply NotInMembers_cons; split; auto. *)
  (*       simpl; intro; subst; contradiction. *)
  (* Qed. *)

  (* Lemma fbys_gather_eqs_aux: *)
  (*   forall eqs l mems mems', *)
  (*     Permutation (map (fun x => (fst x, type_const (fst (snd x)))) mems) mems' -> *)
  (*     Permutation *)
  (*       (map (fun x => (fst x, type_const (fst (snd x)))) *)
  (*            (fst (fold_left gather_eq eqs (mems, l)))) *)
  (*       (fold_left fby_eq eqs mems'). *)
  (* Proof. *)
  (*   induction eqs as [|[]]; simpl; intros; try constructor; auto. *)
  (*   - cases. *)
  (*   - apply IHeqs; simpl; constructor; auto. *)
  (* Qed. *)

  (* Lemma fbys_gather_eqs: *)
  (*   forall eqs, *)
  (*     Permutation *)
  (*       (map (fun x => (fst x, type_const (fst (snd x)))) (fst (gather_eqs eqs))) *)
  (*       (fbys eqs). *)
  (* Proof. *)
  (*   unfold gather_eqs, fbys; intro. *)
  (*   apply fbys_gather_eqs_aux; auto. *)
  (* Qed. *)


  (* Lemma fst_partition_memories_fbys: *)
  (*   forall G n, *)
  (*     wt_node G n -> *)
  (*     Permutation *)
  (*       (idty (fst (partition *)
  (*                     (fun x => PS.mem (fst x) (NL.Mem.memories n.(n_eqs))) *)
  (*                     n.(n_vars)))) *)
  (*       (fbys n.(n_eqs)). *)
  (* Proof. *)
  (*   unfold wt_node; intros * WT. *)
  (*   rewrite fst_partition_filter. *)
  (*   apply NoDup_Permutation. *)
  (*   - apply NoDupMembers_NoDup, fst_NoDupMembers. *)
  (*     rewrite map_fst_idty, filter_mem_fst. *)
  (*     apply nodup_filter. *)
  (*     pose proof (n.(n_nodup)) as Hnodup. *)
  (*     apply NoDupMembers_app_r, NoDupMembers_app_l in Hnodup. *)
  (*     now apply fst_NoDupMembers. *)
  (*   - apply n_nodup_fbys. *)
  (*   - assert (forall x, In x (vars_defined (filter is_fby (n_eqs n))) -> *)
  (*                  InMembers x (n_vars n)) as Spec *)
  (*         by (intro; rewrite <-fst_partition_memories_var_defined, fst_partition_filter, *)
  (*                    filter_mem_fst, filter_In, fst_InMembers; intuition). *)
  (*     pose proof (filter_fst_idty _ _(n_vars n) *)
  (*                                 (fun x => PS.mem x (Mem.memories (n_eqs n)))) as E; *)
  (*       setoid_rewrite E; clear E. *)
  (*     setoid_rewrite filter_In. *)
  (*     setoid_rewrite <-PSE.MP.Dec.F.mem_iff. *)
  (*     unfold Mem.memories, fbys in *. *)
  (*     induction (n_eqs n) as [|[]]; inversion_clear WT as [|?? WTeq]; simpl; auto. *)
  (*     + split; try contradiction. *)
  (*       setoid_rewrite PSE.MP.Dec.F.empty_iff; intuition. *)
  (*     + inversion_clear WTeq as [| | |???? Hint]. *)
  (*       intros (x, t); split. *)
  (*       *{ intros * (Hin & Mem); apply in_fbys_spec; *)
  (*          apply In_fold_left_memory_eq in Mem as [Mem|Mem]. *)
  (*          - apply In_fold_left_memory_eq in Mem as [Mem|Mem]; *)
  (*              [|rewrite PSE.MP.Dec.F.empty_iff in Mem; contradiction]. *)
  (*            left; apply IHl; auto. *)
  (*            intros * Hin'; apply Spec; simpl; auto. *)
  (*          - apply PSE.MP.Dec.F.add_iff in Mem as [E|Mem]; *)
  (*              [|rewrite PSE.MP.Dec.F.empty_iff in Mem; contradiction]. *)
  (*            inv E. *)
  (*            right; constructor; simpl. *)
  (*            assert (In (x, t) (idty (n_in n ++ n_vars n ++ n_out n))) as Hin' *)
  (*                by (rewrite 2 idty_app, 2 in_app; auto). *)
  (*            f_equal. *)
  (*            eapply NoDupMembers_det; eauto. *)
  (*            apply NoDupMembers_idty, n_nodup. *)
  (*        } *)
  (*       *{ intros * Hin; rewrite In_fold_left_memory_eq; *)
  (*          apply in_fbys_spec in Hin as [Hin|Hin]. *)
  (*          - apply IHl in Hin; auto. *)
  (*            + intuition. *)
  (*            + intros * Hin'; apply Spec; simpl; auto. *)
  (*          - inversion_clear Hin as [E|]; try contradiction; inv E. *)
  (*            rewrite PSE.MP.Dec.F.add_iff; intuition. *)
  (*            simpl in Spec. *)
  (*            assert (InMembers x (n_vars n)) as Hin by auto. *)
  (*            pose proof (n_nodup n) as Hnodup. *)
  (*            rewrite fst_NoDupMembers, 2 map_app, NoDup_swap, <- 2 map_app, <-fst_NoDupMembers in Hnodup. *)
  (*            eapply NoDupMembers_app_InMembers, NotInMembers_app in Hnodup as (); eauto. *)
  (*            rewrite 2 idty_app, 2 in_app in Hint; destruct Hint as [Hint|[|Hint]]; auto; *)
  (*              apply In_InMembers in Hint; rewrite InMembers_idty in Hint; contradiction. *)
  (*        } *)
  (* Qed. *)

  (* Lemma translate_node_wt: *)
  (*   forall G n, *)
  (*     wt_node G n -> *)
  (*     wt_block (translate G) (translate_node n). *)
  (* Proof. *)
  (*   unfold wt_node, wt_block; intros * WT; simpl. *)
  (*   eapply translate_eqns_wt; eauto. *)
  (*   - repeat rewrite idty_app. *)
  (*     rewrite <-app_assoc. *)
  (*     apply Permutation_app_head. *)
  (*     rewrite Permutation_app_comm, app_assoc. *)
  (*     apply Permutation_app_tail. *)
  (*     rewrite fbys_gather_eqs, <-fst_partition_memories_fbys; eauto. *)
  (*     setoid_rewrite ps_from_list_gather_eqs_memories. *)
  (*     rewrite <-idty_app. *)
  (*     apply Permutation_map. *)
  (*     rewrite <-permutation_partition; auto. *)
  (*   - setoid_rewrite fbys_gather_eqs. *)
  (*     unfold gather_mems, concatMap, fbys. *)
  (*     induction (n_eqs n) as [|[] eqs]; simpl; intros * Hin Mem; try contradiction; *)
  (*       inversion_clear WT as [|?? WTeq]; auto. *)
  (*     inv WTeq. *)
  (*     apply in_fbys_spec. *)
  (*     destruct Mem as [|Mem]. *)
  (*     + subst. *)
  (*       right; constructor. *)
  (*       f_equal. *)
  (*       eapply NoDupMembers_det; eauto. *)
  (*       apply NoDupMembers_idty, n_nodup. *)
  (*     + left; auto. *)
  (*   - intros * Hin IsV. *)
  (*     rewrite 2 idty_app, 2 in_app. *)
  (*     rewrite 2 idty_app, 2 in_app in Hin; destruct Hin as [|[|]]; auto. *)
  (*     right; left. *)
  (*     setoid_rewrite ps_from_list_gather_eqs_memories. *)
  (*     rewrite snd_partition_filter. *)
  (*     pose proof (filter_fst_idty _ _(n_vars n) *)
  (*                                 (fun x => negb (PS.mem x (Mem.memories (n_eqs n))))) as E; *)
  (*       setoid_rewrite E; clear E. *)
  (*     rewrite filter_In, Bool.negb_true_iff, <-PSE.MP.Dec.F.not_mem_iff. *)
  (*     intuition. *)
  (*     eapply not_Is_variable_in_memories; eauto. *)
  (*     apply NoDup_defs_node. *)
  (* Qed. *)
  (* Hint Resolve translate_node_wt. *)

  Lemma translate_eqn_wc:
    forall G vars eq,
      wc_env vars ->
      NL.Clo.wc_equation G vars eq ->
      Forall (wc_equation (translate G) vars) (translate_eqn eq).
  Proof.
    inversion_clear 2 as [|?????? Find (?&?& Ins & Outs &?)|];
      simpl; auto using Forall_cons.
    apply find_node_translate in Find as (?&?&?&?); subst.
    cases.
    - constructor.
      + do 2 (constructor; auto).
        eapply wc_env_var; eauto.
      + do 2 (econstructor; eauto).
    - do 2 (econstructor; eauto).
  Qed.

  Lemma gather_eqs_n_vars_wc:
    forall n G,
      Forall (NL.Clo.wc_equation G (idck (n_in n ++ n_vars n ++ n_out n))) (n_eqs n) ->
      Permutation (idck (fst (gather_eqs (n_eqs n))))
                  (idck
                     (fst
                        (partition
                           (fun x : positive * (type * clock) =>
                              PS.mem (fst x) (ps_from_list (map fst (fst (gather_eqs (n_eqs n))))))
                           (n_vars n)))).
  Proof.
    intros * WC.
    rewrite fst_partition_filter.
    apply NoDup_Permutation.
    - apply NoDupMembers_NoDup, NoDupMembers_idck, fst_NoDupMembers.
      rewrite fst_fst_gather_eqs_var_defined.
      pose proof (NoDup_var_defined_n_eqs n) as Hnodup;
        rewrite <-is_filtered_vars_defined in Hnodup.
      rewrite Permutation_app_comm in Hnodup; apply NoDup_app_weaken in Hnodup.
      rewrite Permutation_app_comm in Hnodup; apply NoDup_app_weaken in Hnodup.
      auto.
    - apply NoDupMembers_NoDup, fst_NoDupMembers.
      rewrite map_fst_idck, filter_mem_fst.
      apply nodup_filter.
      pose proof (n.(n_nodup)) as Hnodup.
      apply NoDupMembers_app_r, NoDupMembers_app_l in Hnodup.
      now apply fst_NoDupMembers.
    - intros (x, ck).
      setoid_rewrite ps_from_list_gather_eqs_memories.
      assert (forall x, In x (vars_defined (filter is_fby (n_eqs n))) ->
                   InMembers x (n_vars n)) as Spec
          by (intro; rewrite <-fst_partition_memories_var_defined, fst_partition_filter,
                     filter_mem_fst, filter_In, fst_InMembers; intuition).
      pose proof (filter_fst_idck (n_vars n)
                                  (fun x => PS.mem x (Mem.memories (n_eqs n)))) as E;
        setoid_rewrite E; clear E.
      setoid_rewrite filter_In.
      setoid_rewrite <-PSE.MP.Dec.F.mem_iff.
      unfold Mem.memories, gather_eqs in *.
      generalize (@nil (ident * ident)).
      induction (n_eqs n) as [|[]]; inversion_clear WC as [|?? WCeq]; simpl; intros; auto.
      + split; try contradiction.
        setoid_rewrite PSE.MP.Dec.F.empty_iff; intuition.
      + cases.
      + inversion_clear WCeq as [| |???? Hinc].
        rewrite In_fold_left_memory_eq, PSE.MP.Dec.F.add_iff, PSE.MP.Dec.F.empty_iff.
        split.
        *{ intros * Hin.
           unfold idck in Hin.
           apply in_map_iff in Hin as ((x', (c', ck')) & E & Hin); simpl in *; inv E.
           apply In_fst_fold_left_gather_eq in Hin as [Hin|Hin].
           - inversion_clear Hin as [E|]; try contradiction; inv E.
             intuition.
             assert (InMembers x (n_vars n)) by auto.
             pose proof (n_nodup n) as Hnodup.
             rewrite fst_NoDupMembers, 2 map_app, NoDup_swap, <- 2 map_app, <-fst_NoDupMembers in Hnodup.
             eapply NoDupMembers_app_InMembers, NotInMembers_app in Hnodup as (? & ?); eauto.
             rewrite 2 idck_app, 2 in_app in Hinc; destruct Hinc as [Hinc|[|Hinc]]; auto;
               apply In_InMembers in Hinc; rewrite InMembers_idck in Hinc; contradiction.
           - assert (In (x, ck) (idck (fst (fold_left gather_eq l0 ([], l1)))))
               as Hin' by (apply in_map_iff; eexists; intuition; eauto; simpl; auto).
             apply IHl in Hin'; intuition.
         }
         *{ intros * (Hin & [Mem|Mem]).
            - assert (In (x, ck) (idck (fst (fold_left gather_eq l0 ([], l1))))) as Hin'
                  by (apply IHl; auto; intros * Hin';
                      apply Spec; simpl; auto).
              unfold idck in Hin'; apply in_map_iff in Hin' as ((x', (c', ck')) & E & Hin'); simpl in *; inv E.
              apply in_map_iff; exists (x, (c', ck)); simpl.
              rewrite In_fst_fold_left_gather_eq; intuition.
            - destruct Mem as [E|]; try contradiction; inv E.
              apply in_map_iff; exists (x, (c0, c)); simpl.
              rewrite In_fst_fold_left_gather_eq; intuition.
              f_equal.
              assert (In (x, ck) (idck (n_in n ++ n_vars n ++ n_out n)))
                by (rewrite 2 idck_app, 2 in_app; auto).
              eapply NoDupMembers_det; eauto.
              apply NoDupMembers_idck, n_nodup.
          }
  Qed.

  Lemma wc_equations_permutation:
    forall P vars vars' eqs,
      Permutation vars vars' ->
      Forall (wc_equation P vars) eqs ->
      Forall (wc_equation P vars') eqs.
  Proof.
    intros * E WC.
    eapply Forall_impl with (2 := WC); eauto.
    setoid_rewrite E; auto.
  Qed.

  Lemma translate_node_wc:
    forall G n,
      wc_node G n ->
      wc_block (translate G) (translate_node n).
  Proof.
    inversion_clear 1 as [? (?& Env & Heqs)].
    constructor; simpl; auto.
    assert (Permutation (idck
                           (n_in n ++
                                 snd
                                 (partition
                                    (fun x : positive * (type * clock) =>
                                       PS.mem (fst x) (ps_from_list (map fst (fst (gather_eqs (n_eqs n))))))
                                    (n_vars n)) ++ n_out n) ++ idck (fst (gather_eqs (n_eqs n))))
                        (idck (n_in n ++ n_vars n ++ n_out n))) as E.
    { repeat rewrite idck_app.
      rewrite Permutation_app_comm, Permutation_swap, gather_eqs_n_vars_wc,
      <-2 idck_app, app_assoc, <-permutation_partition, idck_app; eauto.
    }
    intuition.
    - now rewrite E.
    - apply Permutation_sym in E.
      eapply wc_equations_permutation with (1 := E).
      unfold translate_eqns.
      clear - Heqs Env; induction (n_eqs n); simpl; inv Heqs; auto.
      apply Forall_app; split; auto.
      eapply translate_eqn_wc; eauto.
  Qed.

  Lemma translate_wc:
    forall G,
      wc_global G ->
      wc_program (translate G).
  Proof.
    intros * WC.
    induction G; simpl; inv WC; auto.
    constructor; auto.
    eapply translate_node_wc; eauto.
  Qed.

End NL2SBCLOCKING.

Module NL2SBClockingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Op)
       (Str   : STREAM          Op OpAux)
       (CE    : COREEXPR    Ids Op OpAux Str)
       (NL    : NLUSTRE     Ids Op OpAux Str CE)
       (SB    : SYBLOC      Ids Op OpAux Str CE)
       (Trans : TRANSLATION Ids Op       CE.Syn NL.Syn SB.Syn NL.Mem)
<: NL2SBCLOCKING Ids Op OpAux Str CE NL SB Trans.
  Include NL2SBCLOCKING Ids Op OpAux Str CE NL SB Trans.
End NL2SBClockingFun.
