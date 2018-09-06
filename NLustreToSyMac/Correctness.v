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

Require Import List.
Import List.ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import Morphisms.

Open Scope positive.
Open Scope list.

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

  Definition memory_spec (m: SemSM.memory) (mems: list (ident * const)) x :=
    PS.mem x (ps_from_list (map fst mems)) = true <-> exists lv, RMemory.mfind_mem x m = Some lv.

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

      Lemma typeof_correctness:
        forall e mems,
          SynSM.typeof (translate_lexp mems e) = typeof e.
      Proof.
        induction e; intros; simpl; auto.
        destruct (PS.mem i mems); auto.
      Qed.
      (* Hint Resolve typeof_correctness. *)

      Variable m: SemSM.memory.
      Variable mems: list (ident * const).
      Let memids := ps_from_list (map fst mems).

      Lemma lexp_instant_correctness:
        forall e b v,
          sem_lexp_instant base R e v ->
          SemSM.sem_lexp_instant b base R m 0 mems (translate_lexp memids e) v.
      Proof.
        induction 1; simpl; eauto using SemSM.sem_lexp_instant.
        - destruct (PS.mem x memids) eqn: E.
          + do 2 constructor.
            unfold SemSM.get_mem.
            destruct b.
            * admit.
            * admit.
          + eauto using SemSM.sem_lexp_instant.
        - econstructor; eauto.
          now rewrite typeof_correctness.
        - econstructor; eauto.
          now rewrite 2 typeof_correctness.
      Qed.
      Hint Resolve lexp_instant_correctness.

      Lemma lexps_instant_correctness:
        forall es b vs,
          sem_lexps_instant base R es vs ->
          SemSM.sem_lexps_instant b base R m 0 mems (map (translate_lexp memids) es) vs.
      Proof.
        induction 1; constructor; auto.
      Qed.

      Lemma cexp_instant_correctness:
        forall ce b v,
          sem_cexp_instant base R ce v ->
          SemSM.sem_cexp_instant b base R m 0 mems (translate_cexp memids ce) v.
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
      Variable mems: list (ident * const).
      Let memids := ps_from_list (map fst mems).

      Lemma caexp_correctness:
        forall ck ce xs,
          sem_caexp bk H ck ce xs ->
          SemSM.sem_caexp bk H M 0 mems ck (translate_cexp memids ce) xs.
      Proof.
        intros ** Sem n; specialize (Sem n); simpl in Sem.
        induction Sem; constructor; auto;
          apply cexp_instant_correctness; auto.
      Qed.

      Lemma laexps_correctness:
        forall ck es vs,
          sem_laexps bk H ck es vs ->
          SemSM.sem_laexps bk H M 0 mems ck (map (translate_lexp memids) es) vs.
      Proof.
        intros ** Sem n; specialize (Sem n); simpl in Sem.
        induction Sem.
        - econstructor 1; eauto.
          now apply lexps_instant_correctness.
        - constructor; auto.
          + now rewrite all_absent_map.
          + now apply lexps_instant_correctness.
      Qed.

    End Sem.
    Hint Resolve var_correctness vars_correctness
         caexp_correctness laexps_correctness.


    Theorem correctness:
      forall f xss oss,
        sem_node G f xss oss ->
        exists ma,
          (forall n, find_node f G = Some n -> ma = translate_node n)
          /\ exists M, SemSM.sem_mode P 0 ma step M xss oss.
    Proof.
      induction 1 as [| | | |???? IHNode|] using sem_node_mult with
          (P_equation := fun b H e =>
                           sem_equation G b H e ->
                           exists M mems,
                             Forall (SemSM.sem_equation P 0 b H M mems)
                                    (translate_eqn (ps_from_list (map fst mems)) e))
          (P_reset := fun f r xss oss =>
                        sem_reset G f r xss oss ->
                        True);
        eauto.
      - repeat (econstructor; eauto).

      - intro Sem; clear Sem.
        (* match goal with *)
        (*   H: sem_node _ _ _ _ |- _ => *)
        (*   inversion_clear H as [??????? Find] *)
        (* end. *)
        destruct IHsem_node as (ma & Spec & M & Sem).
        match goal with
          H: sem_node _ _ _ _ |- _ =>
          inversion_clear H as [??????? Find]
        end.
        pose proof Find as Find'.
        apply Spec in Find'.
        apply find_node_translate in Find as (ma' & ? & Find & E).
        subst.
        (* apply find_node_translate in Find. *)
        (* destruct Find as (ma' & P' & Find' & E). *)

        simpl.
        do 2 econstructor.
        constructor; eauto.
        econstructor; eauto.
        +
          SearchAbout SynSM.find_machine.


  sem_det. admit.

      - admit.

      - admit.

      - admit.

      - exists (translate_node n); split; eauto.
    Qed.
