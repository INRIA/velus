Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Memories.
Require Import Velus.SyMac.SMSyntax.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLSemantics.
Require Import Velus.SyMac.SMSemantics.
Require Import Velus.NLustreToSyMac.Translation.
Require Import Velus.RMemory.

Require Import List.
Import List.ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import Morphisms.

Open Scope list.
Open Scope nat.

Module Type CORRECTNESS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS      Ids)
       (Import SynNL : NLSYNTAX    Ids Op       Clks)
       (SynSM        : SMSYNTAX    Ids Op       Clks)
       (Import Str   : STREAM          Op OpAux)
       (Import Ord   : ORDERED     Ids Op       Clks SynNL)
       (Import SemNL : NLSEMANTICS Ids Op OpAux Clks SynNL       Str Ord)
       (SemSM        : SMSEMANTICS Ids Op OpAux Clks       SynSM Str)
       (Import Mem   : MEMORIES    Ids Op       Clks SynNL)
       (Import Trans : TRANSLATION Ids Op       Clks SynNL SynSM Mem).

  Definition memory_spec (m: SemSM.memory) (memids: PS.t) (R: env) :=
    forall x v,
      PM.find x R = Some v ->
      PS.mem x memids = true ->
      SemSM.get_mem x m = Some v.

  Definition memories_spec (M: SemSM.memories) (memids: PS.t) (H: history) :=
    forall n, memory_spec (SemSM.restr_mem M n) memids (SemSM.restr_hist H n).

  Section Global.

    Variable G: SynNL.global.
    Let P := translate G.

    Section SemInstant.

      Variable base: bool.
      Variable R: env.

      Lemma var_instant_correctness:
        forall x v,
          sem_var_instant R x v ->
          SemSM.sem_var_instant R x v.
      Proof.
        induction 1; constructor; auto.
      Qed.
      Hint Resolve var_instant_correctness.

      Lemma clock_instant_correctness:
        forall ck b,
          sem_clock_instant base R ck b ->
          SemSM.sem_clock_instant base R ck b.
      Proof.
        induction 1; eauto using SemSM.sem_clock_instant.
      Qed.

      Variable m: SemSM.memory.
      Variable memids: PS.t.
      Hypothesis Spec: memory_spec m memids R.
      (* Variable mems: list (ident * const). *)
      (* Let memids := ps_from_list (map fst mems). *)

      Lemma typeof_correctness:
        forall e,
          SynSM.typeof (translate_lexp memids e) = typeof e.
      Proof.
        induction e; intros; simpl; auto.
        destruct (PS.mem i memids); auto.
      Qed.
      (* Hint Resolve typeof_correctness. *)

      Lemma lexp_instant_correctness:
        forall e v,
          sem_lexp_instant base R e v ->
          SemSM.sem_lexp_instant base R m (translate_lexp memids e) v.
      Proof.
        induction 1; simpl; eauto using SemSM.sem_lexp_instant.
        - destruct (PS.mem x memids) eqn: E.
          + do 2 constructor.
            unfold SemSM.get_mem.
            match goal with H: sem_var_instant R x v |- _ =>
                            inversion_clear H as [?? Find] end.
            apply Spec; auto.
          + eauto using SemSM.sem_lexp_instant.
        - econstructor; eauto.
          now rewrite typeof_correctness.
        - econstructor; eauto.
          now rewrite 2 typeof_correctness.
      Qed.
      Hint Resolve lexp_instant_correctness.

      Lemma lexps_instant_correctness:
        forall es vs,
          sem_lexps_instant base R es vs ->
          SemSM.sem_lexps_instant base R m (map (translate_lexp memids) es) vs.
      Proof.
        induction 1; constructor; auto.
      Qed.

      Lemma cexp_instant_correctness:
        forall ce v,
          sem_cexp_instant base R ce v ->
          SemSM.sem_cexp_instant base R m (translate_cexp memids ce) v.
      Proof.
        induction 1; simpl; eauto using SemSM.sem_cexp_instant.
      Qed.

    End SemInstant.
    Hint Resolve var_instant_correctness clock_instant_correctness
         lexp_instant_correctness lexps_instant_correctness
         cexp_instant_correctness.

    Section Sem.

      Variable bk: stream bool.
      Variable H: history.

      Lemma var_correctness:
        forall x xs,
          sem_var bk H x xs ->
          SemSM.sem_var H x xs.
      Proof.
        intros ** Sem n; specialize (Sem n); auto.
      Qed.
      Hint Resolve var_correctness.

      Lemma vars_correctness:
        forall xs xss,
          sem_vars bk H xs xss ->
          SemSM.sem_vars H xs xss.
      Proof.
        intros ** Sem n; specialize (Sem n);
          induction Sem; constructor; auto.
      Qed.

      Variable M: SemSM.memories.
      Variable memids: PS.t.
      Hypothesis Spec: memories_spec M memids H.
      (* Variable mems: list (ident * const). *)
      (* Let memids := ps_from_list (map fst mems). *)

      Lemma laexp_correctness:
        forall ck e xs,
          sem_laexp bk H ck e xs ->
          SemSM.sem_laexp bk H M ck (translate_lexp memids e) xs.
      Proof.
        intros ** Sem n; specialize (Sem n); simpl in Sem.
        induction Sem; constructor; auto.
      Qed.

      Lemma caexp_correctness:
        forall ck ce xs,
          sem_caexp bk H ck ce xs ->
          SemSM.sem_caexp bk H M ck (translate_cexp memids ce) xs.
      Proof.
        intros ** Sem n; specialize (Sem n); simpl in Sem.
        induction Sem; constructor; auto.
      Qed.

      Lemma laexps_correctness:
        forall ck es vs,
          sem_laexps bk H ck es vs ->
          SemSM.sem_laexps bk H M ck (map (translate_lexp memids) es) vs.
      Proof.
        intros ** Sem n; specialize (Sem n); simpl in Sem.
        induction Sem.
        - econstructor 1; eauto.
        - constructor; auto.
          now rewrite all_absent_map.
      Qed.

      Lemma sem_caexp_laexp:
        forall ck e xs,
          SemSM.sem_caexp bk H M ck (SynSM.Eexp e) xs
          <-> SemSM.sem_laexp bk H M ck e xs.
      Proof.
        split; intros ** Sem n; specialize (Sem n).
        - inv Sem; match goal with H: SemSM.sem_cexp_instant _ _ _ _ _ |- _ => inv H end;
            constructor; auto.
        - induction Sem; repeat constructor; auto.
      Qed.

    End Sem.
    Hint Resolve var_correctness vars_correctness
         laexp_correctness caexp_correctness laexps_correctness.


    Theorem correctness:
      forall f xss oss,
        sem_node G f xss oss ->
        exists ma,
          (forall n, find_node f G = Some n -> ma = translate_node n)
          /\ exists M, SemSM.sem_mode P SynSM.Last ma step M xss oss.
    Proof.
      induction 1 as [| | | |???? IHNode|] using sem_node_mult with
          (P_equation := fun b H e =>
                           sem_equation G b H e ->
                           exists M mems,
                             Forall (SemSM.sem_equation P SynSM.Last b H M mems)
                                    (translate_eqn (ps_from_list (map fst mems)) e))
          (P_reset := fun f r xss oss =>
                        sem_reset G f r xss oss ->
                        True);
        eauto.
      - repeat (econstructor; eauto).
        apply caexp_correctness; auto.

      - intro Sem; clear Sem.
        destruct IHsem_node as (ma & Spec & M & Sem).
        match goal with
          H: sem_node _ _ _ _ |- _ =>
          inversion_clear H as [??????? Find]
        end.
        pose proof Find as Find'.
        apply Spec in Find'.
        apply find_node_translate in Find as (ma' & ? & Find & E).
        subst.
        simpl.
        assert (exists y, hd_error x = Some y) as (y & ?).
        { apply length_hd_error.
          repeat match goal with H: sem_vars _ _ _ _ |- _ => specialize (H 0); simpl in H end.
          repeat match goal with H: Forall2 _ _ _ |- _ => apply Forall2_length in H end.
          match goal with H: length x = _ |- _ => rewrite H end.
          repeat try match goal with H: _ = ?x |- _ => rewrite <-H end.
          rewrite map_length; apply n.(n_outgt0).
        }
        exists (madd_obj y M (@empty_memory SemSM.mvalues)).
        repeat (econstructor; eauto).
        apply mfind_inst_gss.

      - admit.

      - intro Sem; clear Sem; simpl.
        exists (madd_mem x {| SemSM.first := xs; SemSM.inter := [] |} (@empty_memory SemSM.mvalues)).
        exists [(x, c0)].
        econstructor; eauto.
        econstructor; eauto.
        + apply sem_caexp_laexp; eauto.
        + econstructor.
          * apply mfind_mem_gss.
          * simpl; now rewrite ident_eqb_refl.
          * simpl; intro n.
            match goal with H: xs = _ |- _ => now rewrite H end.

      - exists (translate_node n); split; eauto.
        + intros.
          match goal with
          | H: find_node ?f ?G = Some _,
               H': find_node f G = Some _ |- _ => rewrite H in H'; inv H'
          end; auto.
        +

    Qed.
