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

  Fixpoint memvar_lexp (x: ident) (e: SynSM.lexp) :=
    match e with
    | SynSM.Emem y _ => x = y
    | SynSM.Ewhen e _ _ => memvar_lexp x e
    | SynSM.Eunop _ e _ => memvar_lexp x e
    | SynSM.Ebinop _ e1 e2 _ => memvar_lexp x e1 \/ memvar_lexp x e2
    | _ => False
    end.

  Fixpoint memvar_cexp (x: ident) (ce: SynSM.cexp) :=
    match ce with
    | SynSM.Emerge _ e1 e2 => memvar_cexp x e1 \/ memvar_cexp x e2
    | SynSM.Eite e t f => memvar_lexp x e \/ memvar_cexp x t \/ memvar_cexp x f
    | SynSM.Eexp e => memvar_lexp x e
    end.

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

      Hypothesis Spec: memory_spec m memids R.

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

      Lemma sem_lexp_instant_madd_mem:
        forall x mv e v,
          SemSM.sem_lexp_instant base R m e v ->
          ~ memvar_lexp x e ->
          SemSM.sem_lexp_instant base R (madd_mem x mv m) e v.
      Proof.
        induction 1; simpl; intros Nmv; eauto using SemSM.sem_lexp_instant.
        - do 2 constructor.
          match goal with H: SemSM.sem_mem_var_instant _ _ _ |- _ => inv H end.
          unfold SemSM.get_mem in *.
          rewrite mfind_mem_gso; auto.
        - econstructor; eauto.
        - econstructor; eauto.
      Qed.
      Hint Resolve sem_lexp_instant_madd_mem.

      Lemma sem_cexp_instant_madd_mem:
        forall x mv ce v,
          SemSM.sem_cexp_instant base R m ce v ->
          ~ memvar_cexp x ce ->
          SemSM.sem_cexp_instant base R (madd_mem x mv m) ce v.
      Proof.
        induction 1; simpl; intros Nmv; eauto using SemSM.sem_cexp_instant.
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
          SemSM.sem_lexps_instant base R m es vs ->
          Forall (fun e => ~ memvar_lexp x e) es ->
          SemSM.sem_lexps_instant base R (madd_mem x mv m) es vs.
      Proof.
        induction 1; simpl; intros Nmv; inv Nmv.
        - constructor.
        - constructor; auto.
          apply IHForall2; auto.
      Qed.

    End SemInstant.
    Hint Resolve var_instant_correctness clock_instant_correctness
         lexp_instant_correctness lexps_instant_correctness
         cexp_instant_correctness
         sem_cexp_instant_madd_mem sem_lexps_instant_madd_mem.

    Lemma pm_map_add:
      forall {A B} (m: PM.t A) (f: A -> B) x v,
        PM.map f (PM.add x v m) = PM.add x (f v) (PM.map f m).
    Proof.
    Admitted.

    Lemma restr_mem_madd_mem:
      forall x mvs M n,
        SemSM.restr_mem (madd_mem x mvs M) n =
        madd_mem x (SemSM.restr_mvalues n mvs) (SemSM.restr_mem M n).
    Proof.
      intros.
      unfold SemSM.restr_mem, madd_mem; simpl.
      f_equal.
      - now rewrite pm_map_add, mm_values_map.
      - now rewrite mm_instances_map.
    Qed.

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
        intros ** Sem n; specialize (Sem n); inv Sem.
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

      Lemma sem_caexp_madd_mem:
        forall x mvs ck ce xs,
          SemSM.sem_caexp bk H M ck ce xs ->
          ~ memvar_cexp x ce ->
          SemSM.sem_caexp bk H (madd_mem x mvs M) ck ce xs.
      Proof.
        intros ** Sem ? n; specialize (Sem n); inv Sem;
          econstructor; eauto;
            rewrite restr_mem_madd_mem; auto.
      Qed.

      Lemma sem_laexps_madd_mem:
        forall x mvs ck es xss,
          SemSM.sem_laexps bk H M ck es xss ->
          Forall (fun e => ~ memvar_lexp x e) es ->
          SemSM.sem_laexps bk H (madd_mem x mvs M) ck es xss.
      Proof.
        intros ** Sem ? n; specialize (Sem n); inv Sem.
        - econstructor; eauto.
          rewrite restr_mem_madd_mem; auto.
        - econstructor 2; eauto.
          rewrite restr_mem_madd_mem; auto.
        - constructor 3.
      Qed.

      Lemma sem_equation_madd_mem:
        forall x mvs mems k eqs,
          (* ~Is_defined_in_eqs x eqs -> *)
          Forall (SemSM.sem_equation P k bk H M mems) eqs ->
          Forall (SemSM.sem_equation P k bk H (madd_mem x mvs M) mems) eqs.
      Proof.
        intros ** (* Hnd *) Hsem.
        induction eqs as [|eq eqs IH]; [now constructor|].
        (* apply not_Is_defined_in_cons in Hnd. *)
        (* destruct Hnd as [Hnd Hnds]. *)
        apply Forall_cons2 in Hsem as [Hsem Hsems].
        constructor; auto.
        destruct Hsem; eauto using SemSM.sem_equation.
        - econstructor; eauto.
          apply sem_caexp_madd_mem; auto.
          admit.
        - admit.
        - econstructor; eauto.
          apply sem_laexps_madd_mem; auto.
          admit.
      Admitted.

    End Sem.
    Hint Resolve var_correctness vars_correctness
         laexp_correctness caexp_correctness laexps_correctness.


  Lemma msem_equation_madd_obj:
    forall G bk H M M' x eqs,
      ~Is_defined_in_eqs x eqs ->
      Forall (msem_equation G bk H M) eqs ->
      Forall (msem_equation G bk H (add_objs x M' M)) eqs.
  Proof.
    Hint Constructors msem_equation.
    intros * Hnd Hsem.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_defined_in_cons in Hnd.
    destruct Hnd as [Hnd Hnds].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Hsem Hsems].
    constructor; [|now apply IH with (1:=Hnds) (2:=Hsems)].
    destruct Hsem as [|??? x' ??????? Hsome
                         |??? x' ?????????? Hsome|];
      eauto;
      assert (sub_inst_n x' (add_objs x M' M) M'0)
        by (apply not_Is_defined_in_eq_EqApp in Hnd;
            unfold sub_inst_n, sub_inst, add_objs in *; intro;
            rewrite mfind_inst_gso; auto; intro; subst x; destruct xs;
            inv Hsome; apply Hnd; now constructor);
      eauto.
  Qed.

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
                             memories_spec M (ps_from_list (map fst mems)) H ->
                             Forall (SemSM.sem_equation P SynSM.Last b H M mems)
                                    (translate_eqn (ps_from_list (map fst mems)) e))
          (P_reset := fun f r xss oss =>
                        sem_reset G f r xss oss ->
                        exists ma,
                          (forall n, find_node f G = Some n -> ma = translate_node n)
                          /\ exists M, SemSM.sem_mode P SynSM.Last ma step M xss oss
                                 /\ SemSM.sem_mode P (SynSM.Inter 0) ma reset M (fun _ => []) (fun _ => []));
        eauto.
      - repeat (econstructor; eauto).

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
        (* assert (exists y, hd_error x = Some y) as (y & ?). *)
        (* { apply length_hd_error. *)
        (*   repeat match goal with H: sem_vars _ _ _ _ |- _ => specialize (H 0); simpl in H end. *)
        (*   repeat match goal with H: Forall2 _ _ _ |- _ => apply Forall2_length in H end. *)
        (*   match goal with H: length x = _ |- _ => rewrite H end. *)
        (*   repeat try match goal with H: _ = ?x |- _ => rewrite <-H end. *)
        (*   rewrite map_length; apply n.(n_outgt0). *)
        (* } *)
        exists (madd_obj (hd default x) M (@empty_memory SemSM.mvalues)).
        repeat (econstructor; eauto).
        apply mfind_inst_gss.

      - intro Sem; clear Sem.
        destruct IHsem_node as (ma & Spec & M & Step & Reset); auto.
        match goal with H: sem_reset _ _ _ _ _ |- _ => inversion_clear H as [???? Sem] end.
        simpl.
        exists (madd_obj (hd default x) M (@empty_memory SemSM.mvalues)).
        econstructor.
        pose proof (Sem 0) as Sem0; inv Sem0.
        edestruct find_node_translate as (ma' & P' & ? & ?); eauto.
        subst.
        econstructor.
        + econstructor; eauto.
          * intro; eapply SemSM.SNil.
          * apply mfind_inst_gss.
          * erewrite <-Spec; eauto.
          * constructor.
        + constructor; eauto.
          econstructor; eauto.
          * apply mfind_inst_gss.
          * erewrite <-Spec; eauto.

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

      - admit.

      - exists (translate_node n); split; eauto.
        + intros.
          match goal with
          | H: find_node ?f ?G = Some _,
               H': find_node f G = Some _ |- _ => rewrite H in H'; inv H'
          end; auto.
        + admit.

    Qed.
