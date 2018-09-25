Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Memories.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLSemantics.
Require Import Velus.SyBloc.SBSemantics.
Require Import Velus.NLustreToSyBloc.Translation.
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
       (SynSB        : SBSYNTAX    Ids Op       Clks)
       (Import Str   : STREAM          Op OpAux)
       (Import Ord   : ORDERED     Ids Op       Clks SynNL)
       (Import SemNL : NLSEMANTICS Ids Op OpAux Clks SynNL       Str Ord)
       (SemSB        : SBSEMANTICS Ids Op OpAux Clks       SynSB Str)
       (Import Mem   : MEMORIES    Ids Op       Clks SynNL)
       (Import Trans : TRANSLATION Ids Op       Clks SynNL SynSB Mem).

  Fixpoint memvar_lexp (x: ident) (e: SynSB.lexp) :=
    match e with
    | SynSB.Ereg y _ => x = y
    | SynSB.Ewhen e _ _ => memvar_lexp x e
    | SynSB.Eunop _ e _ => memvar_lexp x e
    | SynSB.Ebinop _ e1 e2 _ => memvar_lexp x e1 \/ memvar_lexp x e2
    | _ => False
    end.

  Fixpoint memvar_cexp (x: ident) (ce: SynSB.cexp) :=
    match ce with
    | SynSB.Emerge _ e1 e2 => memvar_cexp x e1 \/ memvar_cexp x e2
    | SynSB.Eite e t f => memvar_lexp x e \/ memvar_cexp x t \/ memvar_cexp x f
    | SynSB.Eexp e => memvar_lexp x e
    end.

  Definition memory_spec (m: SemSB.memory) (memids: PS.t) (R: env) :=
    forall x v,
      PM.find x R = Some v ->
      PS.mem x memids = true ->
      SemSB.get_reg x m = Some v.

  Definition memories_spec (M: SemSB.memories) (memids: PS.t) (H: history) :=
    forall n, memory_spec (SemSB.restr_mem M n) memids (SemSB.restr_hist H n).

  Section Global.

    Variable G: SynNL.global.
    Let P := translate G.

    Section SemInstant.

      Variable base: bool.
      Variable R: env.

      Lemma var_instant_correctness:
        forall x v,
          sem_var_instant R x v ->
          SemSB.sem_var_instant R x v.
      Proof.
        induction 1; constructor; auto.
      Qed.
      Hint Resolve var_instant_correctness.

      Lemma clock_instant_correctness:
        forall ck b,
          sem_clock_instant base R ck b ->
          SemSB.sem_clock_instant base R ck b.
      Proof.
        induction 1; eauto using SemSB.sem_clock_instant.
      Qed.

      Variable m: SemSB.memory.
      Variable memids: PS.t.
      (* Variable mems: list (ident * const). *)
      (* Let memids := ps_from_list (map fst mems). *)

      Lemma typeof_correctness:
        forall e,
          SynSB.typeof (translate_lexp memids e) = typeof e.
      Proof.
        induction e; intros; simpl; auto.
        destruct (PS.mem i memids); auto.
      Qed.
      (* Hint Resolve typeof_correctness. *)

      Hypothesis Spec: memory_spec m memids R.

      Lemma lexp_instant_correctness:
        forall e v,
          sem_lexp_instant base R e v ->
          SemSB.sem_lexp_instant base R m (translate_lexp memids e) v.
      Proof.
        induction 1; simpl; eauto using SemSB.sem_lexp_instant.
        - destruct (PS.mem x memids) eqn: E.
          + do 2 constructor.
            unfold SemSB.get_reg.
            match goal with H: sem_var_instant R x v |- _ =>
                            inversion_clear H as [?? Find] end.
            apply Spec; auto.
          + eauto using SemSB.sem_lexp_instant.
        - econstructor; eauto.
          now rewrite typeof_correctness.
        - econstructor; eauto.
          now rewrite 2 typeof_correctness.
      Qed.
      Hint Resolve lexp_instant_correctness.

      Lemma lexps_instant_correctness:
        forall es vs,
          sem_lexps_instant base R es vs ->
          SemSB.sem_lexps_instant base R m (map (translate_lexp memids) es) vs.
      Proof.
        induction 1; constructor; auto.
      Qed.

      Lemma cexp_instant_correctness:
        forall ce v,
          sem_cexp_instant base R ce v ->
          SemSB.sem_cexp_instant base R m (translate_cexp memids ce) v.
      Proof.
        induction 1; simpl; eauto using SemSB.sem_cexp_instant.
      Qed.

      Lemma sem_lexp_instant_madd_mem:
        forall x mv e v,
          SemSB.sem_lexp_instant base R m e v ->
          ~ memvar_lexp x e ->
          SemSB.sem_lexp_instant base R (madd_mem x mv m) e v.
      Proof.
        induction 1; simpl; intros; eauto using SemSB.sem_lexp_instant.
        - do 2 constructor.
          match goal with H: SemSB.sem_mem_var_instant _ _ _ |- _ => inv H end.
          unfold SemSB.get_reg in *.
          rewrite mfind_mem_gso; auto.
        - econstructor; eauto.
        - econstructor; eauto.
      Qed.
      Hint Resolve sem_lexp_instant_madd_mem.

      Lemma sem_cexp_instant_madd_mem:
        forall x mv ce v,
          SemSB.sem_cexp_instant base R m ce v ->
          ~ memvar_cexp x ce ->
          SemSB.sem_cexp_instant base R (madd_mem x mv m) ce v.
      Proof.
        induction 1; simpl; intros; eauto using SemSB.sem_cexp_instant.
        - econstructor; eauto.
        - econstructor 2; eauto.
        - econstructor; eauto.
        - econstructor; eauto.
          + apply IHsem_cexp_instant1; auto.
          + apply IHsem_cexp_instant2; auto.
        - econstructor; eauto.
          + apply IHsem_cexp_instant1; auto.
          + apply IHsem_cexp_instant2; auto.
      Qed.

      Lemma sem_lexps_instant_madd_mem:
        forall x mv es vs,
          SemSB.sem_lexps_instant base R m es vs ->
          Forall (fun e => ~ memvar_lexp x e) es ->
          SemSB.sem_lexps_instant base R (madd_mem x mv m) es vs.
      Proof.
        induction 1; simpl; intros Nmv; inv Nmv.
        - constructor.
        - constructor; auto.
          apply IHForall2; auto.
      Qed.

      Lemma sem_lexp_instant_madd_obj:
        forall x m' e v,
          SemSB.sem_lexp_instant base R m e v ->
          SemSB.sem_lexp_instant base R (madd_obj x m' m) e v.
      Proof.
        induction 1; simpl; intros; eauto using SemSB.sem_lexp_instant.
        do 2 constructor.
        match goal with H: SemSB.sem_mem_var_instant _ _ _ |- _ => inv H end.
        unfold SemSB.get_reg in *.
        now rewrite mfind_mem_add_inst.
      Qed.
      Hint Resolve sem_lexp_instant_madd_obj.

      Lemma sem_cexp_instant_madd_obj:
        forall x m' ce v,
          SemSB.sem_cexp_instant base R m ce v ->
          SemSB.sem_cexp_instant base R (madd_obj x m' m) ce v.
      Proof.
        induction 1; simpl; intros; eauto using SemSB.sem_cexp_instant.
      Qed.

      Lemma sem_lexps_instant_madd_obj:
        forall x m' es vs,
          SemSB.sem_lexps_instant base R m es vs ->
          SemSB.sem_lexps_instant base R (madd_obj x m' m) es vs.
      Proof.
        induction 1; simpl; intros; constructor; auto.
      Qed.

    End SemInstant.
    Hint Resolve var_instant_correctness clock_instant_correctness
         lexp_instant_correctness lexps_instant_correctness
         cexp_instant_correctness
         sem_cexp_instant_madd_mem sem_lexps_instant_madd_mem
         sem_cexp_instant_madd_obj sem_lexps_instant_madd_obj.

    Lemma pm_map_add:
      forall {A B} (m: PM.t A) (f: A -> B) x v,
        PM.map f (PM.add x v m) = PM.add x (f v) (PM.map f m).
    Proof.
    Admitted.

    Lemma restr_mem_madd_mem:
      forall x mvs M n,
        SemSB.restr_mem (madd_mem x mvs M) n =
        madd_mem x (SemSB.restr_mvalues n mvs) (SemSB.restr_mem M n).
    Proof.
      intros.
      unfold SemSB.restr_mem, madd_mem; simpl.
      f_equal.
      - now rewrite pm_map_add, mm_values_map.
      - now rewrite mm_instances_map.
    Qed.

    Lemma restr_mem_madd_obj:
      forall x M' M n,
        SemSB.restr_mem (madd_obj x M' M) n =
        madd_obj x (SemSB.restr_mem M' n) (SemSB.restr_mem M n).
    Proof.
      intros.
      unfold SemSB.restr_mem, madd_obj; simpl.
      f_equal.
      - now rewrite mm_values_map.
      - now rewrite pm_map_add, mm_instances_map.
    Qed.

    Section Sem.

      Variable bk: stream bool.
      Variable H: history.

      Lemma var_correctness:
        forall x xs,
          sem_var bk H x xs ->
          SemSB.sem_var H x xs.
      Proof.
        intros ** Sem n; specialize (Sem n); auto.
      Qed.
      Hint Resolve var_correctness.

      Lemma vars_correctness:
        forall xs xss,
          sem_vars bk H xs xss ->
          SemSB.sem_vars H xs xss.
      Proof.
        intros ** Sem n; specialize (Sem n);
          induction Sem; constructor; auto.
      Qed.

      Variable M: SemSB.memories.
      Variable memids: PS.t.
      Hypothesis Spec: memories_spec M memids H.
      (* Variable mems: list (ident * const). *)
      (* Let memids := ps_from_list (map fst mems). *)

      Lemma laexp_correctness:
        forall ck e xs,
          sem_laexp bk H ck e xs ->
          SemSB.sem_laexp bk H M ck (translate_lexp memids e) xs.
      Proof.
        intros ** Sem n; specialize (Sem n); simpl in Sem.
        induction Sem; constructor; auto.
      Qed.

      Lemma caexp_correctness:
        forall ck ce xs,
          sem_caexp bk H ck ce xs ->
          SemSB.sem_caexp bk H M ck (translate_cexp memids ce) xs.
      Proof.
        intros ** Sem n; specialize (Sem n); simpl in Sem.
        induction Sem; constructor; auto.
      Qed.

      Lemma laexps_correctness:
        forall ck es vs,
          sem_laexps bk H ck es vs ->
          SemSB.sem_laexps bk H M ck (map (translate_lexp memids) es) vs.
      Proof.
        intros ** Sem n; specialize (Sem n); inv Sem.
        - econstructor 1; eauto.
        - constructor; auto.
          now rewrite all_absent_map.
      Qed.

      Lemma sem_caexp_laexp:
        forall ck e xs,
          SemSB.sem_caexp bk H M ck (SynSB.Eexp e) xs
          <-> SemSB.sem_laexp bk H M ck e xs.
      Proof.
        split; intros ** Sem n; specialize (Sem n).
        - inv Sem; match goal with H: SemSB.sem_cexp_instant _ _ _ _ _ |- _ => inv H end;
            constructor; auto.
        - induction Sem; repeat constructor; auto.
      Qed.

      Lemma sem_caexp_madd_mem:
        forall x mvs ck ce xs,
          SemSB.sem_caexp bk H M ck ce xs ->
          ~ memvar_cexp x ce ->
          SemSB.sem_caexp bk H (madd_mem x mvs M) ck ce xs.
      Proof.
        intros ** Sem ? n; specialize (Sem n); inv Sem;
          econstructor; eauto;
            rewrite restr_mem_madd_mem; auto.
      Qed.

      Lemma sem_laexps_madd_mem:
        forall x mvs ck es xss,
          SemSB.sem_laexps bk H M ck es xss ->
          Forall (fun e => ~ memvar_lexp x e) es ->
          SemSB.sem_laexps bk H (madd_mem x mvs M) ck es xss.
      Proof.
        intros ** Sem ? n; specialize (Sem n); inv Sem.
        - econstructor; eauto.
          rewrite restr_mem_madd_mem; auto.
        - econstructor 2; eauto.
          rewrite restr_mem_madd_mem; auto.
        - constructor 3.
      Qed.

      Lemma sem_caexp_madd_obj:
        forall x M' ck ce xs,
          SemSB.sem_caexp bk H M ck ce xs ->
          SemSB.sem_caexp bk H (madd_obj x M' M) ck ce xs.
      Proof.
        intros ** Sem n; specialize (Sem n); inv Sem;
          econstructor; eauto;
            rewrite restr_mem_madd_obj; auto.
      Qed.
      Hint Resolve sem_caexp_madd_obj.

      Lemma sem_laexps_madd_obj:
        forall x M' ck es xss,
          SemSB.sem_laexps bk H M ck es xss ->
          SemSB.sem_laexps bk H (madd_obj x M' M) ck es xss.
      Proof.
        intros ** Sem n; specialize (Sem n); inv Sem.
        - econstructor; eauto.
          rewrite restr_mem_madd_obj; auto.
        - econstructor 2; eauto.
          rewrite restr_mem_madd_obj; auto.
        - constructor 3.
      Qed.
      Hint Resolve sem_laexps_madd_obj.

      (* Lemma sem_equation_madd_mem: *)
      (*   forall x mvs eqs, *)
      (*     (* ~Is_defined_in_eqs x eqs -> *) *)
      (*     Forall (SemSB.sem_equation P bk H M) eqs -> *)
      (*     Forall (SemSB.sem_equation P bk H (madd_mem x mvs M)) eqs. *)
      (* Proof. *)
      (*   intros ** (* Hnd *) Hsem. *)
      (*   induction eqs as [|eq eqs IH]; [now constructor|]. *)
      (*   (* apply not_Is_defined_in_cons in Hnd. *) *)
      (*   (* destruct Hnd as [Hnd Hnds]. *) *)
      (*   apply Forall_cons2 in Hsem as [Hsem Hsems]. *)
      (*   constructor; auto. *)
      (*   destruct Hsem; eauto using SemSB.sem_equation. *)
      (*   - econstructor; eauto. *)
      (*     apply sem_caexp_madd_mem; auto. *)
      (*     admit. *)
      (*   - econstructor; eauto. *)
      (*     apply sem_caexp_madd_mem; eauto. *)
      (*     admit. *)
      (*     admit. *)
      (*   - econstructor; eauto. *)
      (*     apply sem_laexps_madd_mem; auto. *)
      (*     admit. *)
      (* Admitted. *)
      Inductive inst_in_eq: ident -> SynSB.equation -> Prop :=
      | DefEqReset:
          forall x ck m r,
            inst_in_eq x (SynSB.EqReset ck m x r)
      | DefEqCall:
          forall x xs ck m es,
            inst_in_eq x (SynSB.EqCall xs ck m x es).

      Definition inst_in_eqs (x: ident) (eqs: list SynSB.equation) : Prop :=
        List.Exists (inst_in_eq x) eqs.

      Lemma not_inst_in_eq_cons:
        forall x eq eqs,
          ~ inst_in_eqs x (eq :: eqs)
          <-> ~ inst_in_eq x eq /\ ~ inst_in_eqs x eqs.
      Proof.
        split.
        - intro Hndef; split; intro;
            eapply Hndef; constructor (assumption).
        - intros [? ?] Hdef_all.
          inv Hdef_all; eauto.
      Qed.



      Lemma sem_equation_madd_obj:
        forall M' x eqs,
          ~ inst_in_eqs x eqs ->
          Forall (SemSB.sem_equation P bk H M) eqs ->
          Forall (SemSB.sem_equation P bk H (madd_obj x M' M)) eqs.
      Proof.
        intros * Hnd Hsem.
        induction eqs as [|eq eqs IH]; [now constructor|].
        apply not_inst_in_eq_cons in Hnd as [Hnd Hnds].
        apply Forall_cons2 in Hsem as [Hsem Hsems].
        constructor; auto.
        induction eq; inv Hsem; eauto using SemSB.sem_equation.
        - econstructor; eauto.
          match goal with H: SemSB.next_reg _ _ _ |- _ => inv H end.
          econstructor; eauto.
        - econstructor; eauto.
          unfold sub_inst; rewrite mfind_inst_gso; auto.
          intro; apply Hnd; subst.
          constructor.
        - econstructor; eauto.
          unfold sub_inst; rewrite mfind_inst_gso; auto.
          intro; apply Hnd; subst.
          constructor.
      Qed.

    End Sem.
    Hint Resolve var_correctness vars_correctness
         laexp_correctness caexp_correctness laexps_correctness.

    Fixpoint well_formed_eqs (eqs: list SynSB.equation) : Prop :=
        match eqs with
        | [] => True
        | SynSB.EqReset _ _ x _ :: eqs => ~ inst_in_eqs x eqs /\ well_formed_eqs eqs
        | SynSB.EqCall _ _ _ x _ :: eqs => ~ inst_in_eqs x eqs /\ well_formed_eqs eqs
        | _ :: eqs => well_formed_eqs eqs
        end.

    Lemma memories_spec_madd_obj:
      forall M memids H x M',
        memories_spec M memids H ->
        memories_spec (madd_obj x M' M) memids H.
    Proof.
      intros ** Spec n x' v Find Mem.
      specialize (Spec n x' v Find Mem).
      unfold SemSB.get_reg in *.
      now rewrite restr_mem_madd_obj, mfind_mem_add_inst.
    Qed.
    Hint Resolve memories_spec_madd_obj.

    Lemma sem_msem_eq:
      forall bk H eqs M eq memids (* argIn *),
        (forall f xss oss,
            sem_node G f xss oss ->
            exists M, SemSB.sem_block P f M xss oss) ->
        (forall f r xss oss,
            sem_reset G f r xss oss ->
            exists M, SemSB.sem_block P f M xss oss
                 /\ SemSB.reset_regs r M) ->
        sem_equation G bk H eq ->
        memories_spec M memids H ->
        well_formed_eqs (translate_eqn memids eq ++ eqs) ->
        (* Is_well_sch mems argIn (eq :: eqs) -> *)
        Forall (SemSB.sem_equation P bk H M) eqs ->
        exists M', Forall (SemSB.sem_equation P bk H M') (translate_eqn memids eq ++ eqs).
    Proof.
      intros ** IHnode IHreset Heq Spec WF Heqs.
      inv Heq; simpl.
      - repeat (econstructor; eauto).
      - edestruct IHnode as (M' & Block); eauto.
        exists (madd_obj (hd default x) M' M).
        econstructor; eauto.
        + econstructor; eauto.
          apply mfind_inst_gss.
        + apply sem_equation_madd_obj; auto.
          apply WF.
      - edestruct IHreset as (M' & Block & Reset); eauto.
        exists (madd_obj (hd default x) M' M).
        econstructor; eauto.
        + econstructor; eauto.
          apply mfind_inst_gss.
        + econstructor; eauto.
          * econstructor; eauto.
            apply mfind_inst_gss.
          * apply sem_equation_madd_obj; auto.
            apply WF.
      - exists (madd_mem x {| SynSB.content := hold (sem_const c0) ls; SynSB.reset := fun _ => false |} M).
          SearchAbout mfind_inst. apply laexps_correctness; auto.

    Theorem correctness:
      forall f xss oss,
        sem_node G f xss oss ->
        exists M, SemSB.sem_block P f M xss oss.
    Proof.
      induction 1 as [| | | |???? IHNode|] using sem_node_mult with
          (P_equation := fun b H e =>
                           (* sem_equation G b H e -> *)
                           exists M mems,
                             memories_spec M (ps_from_list (map (@fst ident const) mems)) H ->
                             Forall (SemSB.sem_equation P b H M)
                                    (translate_eqn (ps_from_list (map fst mems)) e))
          (P_reset := fun f r xss oss =>
                        (* sem_reset G f r xss oss -> *)
                        exists M, SemSB.sem_block P f M xss oss
                             /\ SemSB.reset_regs r M
          );
        eauto.
      - repeat (econstructor; eauto).

      -
        (* intro Sem; clear Sem. *)
        destruct IHsem_node as (M & Sem).
        match goal with
          H: sem_node _ _ _ _ |- _ =>
          inversion_clear H as [??????? Find]
        end.
        apply find_node_translate in Find as (bl & ? & Find & E).
        subst.
        simpl.
        exists (madd_obj (hd default x) M (@empty_memory SemSB.mvalues)).
        repeat (econstructor; eauto);
          apply mfind_inst_gss.

      -
        (* intro Sem; clear Sem. *)
        destruct IHsem_node as (M & Block & Reset); auto.
        match goal with H: sem_reset _ _ _ _ _ |- _ => inversion_clear H as [???? Sem] end.
        simpl.
        exists (madd_obj (hd default x) M (@empty_memory SemSB.mvalues)).
        econstructor.
        pose proof (Sem 0) as Sem0; inv Sem0.
        edestruct find_node_translate as (bl & P' & ? & ?); eauto.
        subst.
        repeat (econstructor; eauto);
          apply mfind_inst_gss.

      -
        (* intro Sem; clear Sem; simpl. *)
        exists (madd_mem x {| SemSB.content := xs; SemSB.reset := fun _ => false; SemSB.init := c0 |} (@empty_memory SemSB.mvalues)).
        exists [(x, c0)].
        econstructor; eauto.
        econstructor; eauto.
        + apply sem_caexp_laexp; eauto.
        + econstructor.
          * apply mfind_mem_gss.
          * simpl; subst; reflexivity.

      - admit.

      - eexists.
        match goal with
          H: find_node _ _ = _ |- _ => apply find_node_translate in H as (bl & ? & Find & E)
        end.
        subst.
        econstructor; eauto.
        + simpl; rewrite map_fst_idty; eauto.
        + simpl; rewrite map_fst_idty; eauto.
        + simpl.

    Qed.
