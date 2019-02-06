Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Logic.FunctionalExtensionality.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Memories.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLExprSemantics.
Require Import Velus.NLustre.NLSemantics.
Require Import Velus.NLustre.MemSemantics.
Require Import Velus.SyBloc.SBSemantics.
Require Import Velus.NLustreToSyBloc.Translation.
Require Import Velus.RMemory.
Require Import Velus.NLustre.IsFree.
Require Import Velus.NLustre.IsVariable.
Require Import Velus.NLustre.IsDefined.
Require Import Velus.NLustre.NoDup.
Require Import Velus.NLustre.NLClocking.
Require Import Velus.NLustre.NLClockingSemantics.

Require Import List.
Import List.ListNotations.

Open Scope list.
Open Scope nat.

Module Type CORRECTNESS
       (Import Ids      : IDS)
       (Import Op       : OPERATORS)
       (Import OpAux    : OPERATORS_AUX           Op)
       (Import Clks     : CLOCKS              Ids)
       (Import ExprSyn  : NLEXPRSYNTAX            Op)
       (Import SynNL    : NLSYNTAX            Ids Op       Clks ExprSyn)
       (Import SynSB    : SBSYNTAX            Ids Op       Clks ExprSyn)
       (Import Str      : STREAM                  Op OpAux)
       (Import Ord      : ORDERED             Ids Op       Clks ExprSyn SynNL)
       (Import ExprSem  : NLEXPRSEMANTICS     Ids Op OpAux Clks ExprSyn             Str)
       (Import SemNL    : NLSEMANTICS         Ids Op OpAux Clks ExprSyn SynNL       Str Ord ExprSem)
       (Import SemSB    : SBSEMANTICS         Ids Op OpAux Clks ExprSyn       SynSB Str     ExprSem)
       (Import Mem      : MEMORIES            Ids Op       Clks ExprSyn SynNL)
       (Import Trans    : TRANSLATION         Ids Op       Clks ExprSyn SynNL SynSB                       Mem)
       (Import IsD      : ISDEFINED           Ids Op       Clks ExprSyn SynNL                             Mem)
       (Import IsV      : ISVARIABLE          Ids Op       Clks ExprSyn SynNL                             Mem IsD)
       (Import IsF      : ISFREE              Ids Op       Clks ExprSyn SynNL)
       (Import NoD      : NODUP               Ids Op       Clks ExprSyn SynNL                             Mem IsD IsV)
       (Import MemSem   : MEMSEMANTICS        Ids Op OpAux Clks ExprSyn SynNL       Str Ord ExprSem SemNL Mem IsD IsV IsF NoD)
       (Import NLClk    : NLCLOCKING          Ids Op       Clks ExprSyn SynNL           Ord               Mem IsD     IsF)
       (Import NLClkSem : NLCLOCKINGSEMANTICS Ids Op OpAux Clks ExprSyn SynNL       Str Ord ExprSem SemNL Mem IsD     IsF     NLClk).

  Lemma In_snd_gather_eqs_Is_node_in:
    forall eqs i f,
      In (i, f) (snd (gather_eqs eqs)) ->
      Is_node_in f eqs.
  Proof.
    unfold gather_eqs.
    intro.
    generalize (@nil (ident * const)).
    induction eqs as [|[]]; simpl; try contradiction; intros ** Hin; auto.
    - right; eapply IHeqs; eauto.
    - destruct i.
      + right; eapply IHeqs; eauto.
      + apply In_snd_fold_left_gather_eq in Hin as [Hin|Hin].
        * destruct Hin as [E|]; try contradiction; inv E.
          left; constructor.
        * right; eapply IHeqs; eauto.
    - right; eapply IHeqs; eauto.
  Qed.

  Lemma Ordered_nodes_blocks:
    forall G,
      Ordered_nodes G ->
      Ordered_blocks (translate G).
  Proof.
    induction 1 as [|??? IH NodeIn Nodup]; simpl; constructor; auto.
    - destruct nd; simpl in *; clear - NodeIn.
      apply Forall_forall; intros ** Hin.
      destruct x; apply In_snd_gather_eqs_Is_node_in in Hin.
      apply NodeIn in Hin as [? E]; split; auto.
      clear NodeIn.
      induction nds as [|n].
      + inv E.
      + simpl; destruct (ident_eqb (n_name n) i0) eqn: Eq.
        * inv E; eauto.
        * inv E; eauto.
          rewrite ident_eqb_refl in Eq; discriminate.
    - clear - Nodup.
      induction Nodup; simpl; auto.
  Qed.

  Lemma msem_eqs_reset_lasts:
    forall G bk H M M' n,
      memory_closed_n M (n_eqs n) ->
      Forall (msem_equation G bk H M M') (n_eqs n) ->
      reset_lasts (translate_node n) (M 0).
  Proof.
    intros ** Closed Heqs.
    split.
    - intros ** Hin.
      destruct n; simpl in *.
      unfold gather_eqs in *.
      clear - Heqs Hin.
      revert Hin; generalize (@nil (ident * ident)).
      induction n_eqs0 as [|[] ? IH]; simpl in *; intros; try contradiction;
        inversion_clear Heqs as [|?? Heq]; inv Heq; eauto.
      + destruct i; try discriminate; eauto.
      + destruct i; try discriminate; eauto.
      + apply In_fst_fold_left_gather_eq in Hin as [Hin|]; eauto.
        destruct Hin as [E|]; try contradiction; inv E.
        match goal with H: mfby _ _ _ _ _ _ |- _ => destruct H as (?&?) end; auto.
    - specialize (Closed 0); destruct Closed as [? Vals].
      intros ** Find.
      assert (In x (SynNL.gather_mem (n_eqs n))) as Hin
          by (apply Vals, not_None_is_Some; eauto).
      destruct n; simpl in *.
      unfold gather_eqs in *.
      clear - Hin Find Heqs.
      revert Hin; generalize (@nil (ident * ident)).
      induction n_eqs0 as [|[] ? IH]; simpl in *; intros; try contradiction;
        inversion_clear Heqs as [|?? Heq]; inv Heq; eauto.
      + destruct i; try discriminate; eauto.
      + destruct i; try discriminate; eauto.
      + destruct Hin.
        * subst.
          match goal with H: mfby _ _ _ _ _ _ |- _ => destruct H as (Find'&?) end.
          rewrite Find in Find'; inv Find'.
          exists c0; split; auto.
          apply In_fst_fold_left_gather_eq; left; left; auto.
        * edestruct IH as (c1 &?& Hin); eauto.
          exists c1; split; auto.
          apply In_fst_fold_left_gather_eq; right; eauto.
  Qed.

  Lemma msem_eqs_In_snd_gather_eqs_spec:
    forall eqs G bk H M M' x f,
      Forall (msem_equation G bk H M M') eqs ->
      In (x, f) (snd (gather_eqs eqs)) ->
      exists xss Mx Mx' yss,
        (msem_node G f xss Mx Mx' yss
         \/ exists r, msem_reset G f r xss Mx Mx' yss)
        /\ sub_inst_n x M Mx.
  Proof.
    unfold gather_eqs.
    intro; generalize (@nil (ident * const)).
    induction eqs as [|[]]; simpl; intros ** Heqs Hin;
      inversion_clear Heqs as [|?? Heq];
      try inversion_clear Heq as [|????????????? Hd|???????????????? Hd|];
        try contradiction; eauto.
    - destruct i; try discriminate.
      apply In_snd_fold_left_gather_eq in Hin as [Hin|]; eauto.
      destruct Hin as [E|]; try contradiction; inv E; inv Hd.
      do 4 eexists; split; eauto.
    - destruct i; try discriminate.
      apply In_snd_fold_left_gather_eq in Hin as [Hin|]; eauto.
      destruct Hin as [E|]; try contradiction; inv E; inv Hd.
      do 4 eexists; split; eauto.
  Qed.

  Lemma msem_node_initial_state:
    forall G f xss M M' yss,
      Ordered_nodes G ->
      msem_node G f xss M M' yss ->
      initial_state (translate G) f (M 0).
  Proof.
    induction G as [|node ? IH].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros ** Hord Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [???????? Clock Hfind Ins ????? Heqs].
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hord; inversion_clear Hord as [|??? NodeIn].
    pose proof Hfind as Hfind'.
    simpl in Hfind.
    assert (Ordered_blocks (translate_node node :: translate G))
           by (change (translate_node node :: translate G) with (translate (node :: G));
               apply Ordered_nodes_blocks; auto).
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - inversion Hfind; subst n.
      apply find_node_translate in Hfind' as (?&?&?&?); subst.
      eapply Forall_msem_equation_global_tl in Heqs; eauto.
      econstructor; eauto.
      + eapply msem_eqs_reset_lasts; eauto.
      + intros ** Hin.
        assert (b' <> n_name node).
        { destruct node; simpl in *.
          apply In_snd_gather_eqs_Is_node_in in Hin.
          apply NodeIn; auto.
        }
        destruct node; simpl in *.
        edestruct msem_eqs_In_snd_gather_eqs_spec
          as (?& Mx &?&?& [Node|(rs & Reset)] & Sub); eauto.
        * apply IH in Node; auto.
          eexists; split; eauto.
          apply initial_state_tail; simpl; auto.
        * inversion_clear Reset as [?????? Nodes].
          destruct (Nodes (count rs 0)) as (M0 &?& Node & Mmask &?).
          apply IH in Node; auto.
          specialize (Mmask 0); specialize (Sub 0).
          rewrite <-Mmask in Sub; auto.
          eexists; split; eauto.
          apply initial_state_tail; simpl; auto.
    - assert (n_name node <> f) by now apply ident_eqb_neq.
      eapply msem_node_cons in Hsem; eauto.
      simpl; rewrite <-initial_state_tail; eauto.
  Qed.

  Definition sem_equations_n
             (P: program) (bk: stream bool) (H: history)
             (E: stream state) (T: stream transient_states) (E': stream state)
             (eqs: list equation) :=
    forall n, Forall (sem_equation P (bk n) (restr_hist H n) (E n) (T n) (E' n)) eqs.

  Definition sem_block_n
             (P: program) (f: ident)
             (E: stream state) (xss yss: stream (list value)) (E': stream state) :=
    forall n, sem_block P f (E n) (xss n) (yss n) (E' n).

  Definition add_n (x: ident) (Mx: stream state) (I: stream transient_states) :=
    fun n => Env.add x (Mx n) (I n).

  Inductive Is_state_in_eq: ident -> equation -> Prop :=
  | StateEqCall:
      forall x xs ck rst f es,
        Is_state_in_eq x (EqCall x xs ck rst f es)
  | StateEqReset:
      forall x ck f,
        Is_state_in_eq x (EqReset x ck f).

  Definition Is_state_in_eqs (x: ident) (eqs: list equation) : Prop :=
    List.Exists (Is_state_in_eq x) eqs.

  Lemma not_Is_state_in_cons:
    forall x eq eqs,
      ~Is_state_in_eqs x (eq :: eqs)
      <-> ~Is_state_in_eq x eq /\ ~Is_state_in_eqs x eqs.
  Proof.
    split.
    - intro H; split; intro; apply H; constructor(assumption).
    - intros [? ?] H; inv H; eauto.
  Qed.

  Lemma sem_equations_n_add_n:
    forall P eqs bk H S S' Is x Sx,
      sem_equations_n P bk H S Is S' eqs ->
      ~ Is_state_in_eqs x eqs ->
      sem_equations_n P bk H S (add_n x Sx Is) S' eqs.
  Proof.
    induction eqs as [|eq eqs]; intros ** Sem Notin n; constructor.
    - specialize (Sem n); inversion_clear Sem as [|?? Sem'].
      inv Sem'; eauto using SemSB.sem_equation.
      + econstructor; eauto.
        unfold add_n; rewrite Env.gso; auto.
        intro E; apply Notin; rewrite E; do 2 constructor.
      + econstructor; eauto.
        unfold add_n; rewrite Env.gso; auto.
        intro E; apply Notin; rewrite E; do 2 constructor.
    - apply IHeqs.
      + intro n'; specialize (Sem n'); inv Sem; auto.
      + apply not_Is_state_in_cons in Notin as []; auto.
  Qed.

  Inductive translate_eqn_nodup_states: SynNL.equation -> list equation -> Prop :=
    | TrNodupEqDef:
        forall x ck e eqs,
          translate_eqn_nodup_states (SynNL.EqDef x ck e) eqs
    | TrNodupEqApp:
        forall xs ck f es r eqs x,
          hd_error xs = Some x ->
          ~ Is_state_in_eqs x eqs ->
          translate_eqn_nodup_states (EqApp xs ck f es r) eqs
    | TrNodupEqFby:
        forall x ck c e eqs,
          translate_eqn_nodup_states (EqFby x ck c e) eqs.

  Lemma equation_correctness:
    forall G eq eqs bk H M M' Is vars,
      (forall f xss M M' yss,
          msem_node G f xss M M' yss ->
          sem_block_n (translate G) f M xss yss M') ->
      Ordered_nodes G ->
      wc_equation G vars eq ->
      Forall (clock_match bk H) vars ->
      translate_eqn_nodup_states eq eqs ->
      msem_equation G bk H M M' eq ->
      sem_equations_n (translate G) bk H M Is M' eqs ->
      exists Is', sem_equations_n (translate G) bk H M Is' M' (translate_eqn eq ++ eqs).
  Proof.
    intros ** IHnode Hord WC ClkM TrNodup Heq Heqs.
    destruct Heq as [| |????????????????????? Var Hr Reset|?????????? Arg Var Mfby];
      inv TrNodup; simpl.

    - do 3 (econstructor; eauto).

    - match goal with
      | H: hd_error ?l = Some x,
           H': hd_error ?l = _ |- _ => rewrite H' in H; inv H
      end.
      erewrite hd_error_Some_hd; eauto.
      destruct xs; try discriminate.
      exists (add_n x Mx Is); intro.
      constructor; auto.
      + econstructor; eauto.
        * split; eauto; reflexivity.
        * apply Env.gss.
        * now apply IHnode.
      + apply sem_equations_n_add_n; auto.

    - match goal with
      | H: hd_error ?l = Some x,
           H': hd_error ?l = _ |- _ => rewrite H' in H; inv H
      end.
      erewrite hd_error_Some_hd; eauto.
      destruct xs; try discriminate.
      exists (fun n => Env.add x (if rs n then Mx 0 else Mx n) (Is n)); intro.
      pose proof (msem_reset_spec Hord Reset) as Spec.
      inversion_clear Reset as [?????? Nodes].
      destruct (Nodes (count rs n)) as (Mn & Mn' & Node_n & Mmask_n & Mmask'_n);
        destruct (Nodes (count rs 0)) as (M0 & M0' & Node_0 & Mmask_0 & Mmask'_0).
      apply IHnode in Node_n.
      specialize (Node_n n); specialize (Mmask_n n); specialize (Mmask'_n n).
      rewrite 2 mask_transparent, Mmask_n, Mmask'_n in Node_n; auto.
      specialize (Var n); specialize (Hr n).
      assert (forall Mx, sem_equations_n (translate G) bk H M (add_n x Mx Is) M' eqs) as Heqs'
          by now intro; apply sem_equations_n_add_n.
      assert (clock_match bk H (y, ck)) as Cky.
      { eapply Forall_forall; eauto.
        inv WC; eauto.
      }
      specialize (Cky n); simpl in Cky.
      destruct (rs n) eqn: E.
      + specialize (Heqs' (fun n => Mx 0) n).
        assert (Env.find x (Env.add x (Mx 0) (Is n)) = Some (Mx 0))
          by apply Env.gss.
        constructor; auto; [|constructor; auto].
        *{ destruct (ys n); try discriminate.
           econstructor; eauto.
           - eapply Son; eauto.
             destruct Cky as [[]|(?&?&?)]; auto.
             assert (present c = absent) by sem_det; discriminate.
           - instantiate (1 := empty_memory _); simpl.
             rewrite <-Mmask_0; auto.
             eapply msem_node_initial_state; eauto.
         }
        *{ eapply SemSB.SEqCall with (Is := Mx 0); eauto.
           - instantiate (1 := empty_memory _); congruence.
           - eapply sem_block_equal_memory; eauto; reflexivity.   (* TODO: fix rewriting here? *)
         }
      + specialize (Heqs' Mx n).
        assert (Env.find x (Env.add x (Mx n) (Is n)) = Some (Mx n))
          by apply Env.gss.
        destruct (ys n) eqn: E'.
        *{ do 2 (econstructor; eauto using SemSB.sem_equation).
           - apply Son_abs1; auto.
             destruct Cky as [[]|(c &?&?)]; auto.
             assert (present c = absent) by sem_det; discriminate.
           - simpl; split; eauto; reflexivity.
           - econstructor; eauto.
             instantiate (1 := empty_memory _); discriminate.
         }
        *{ do 2 (econstructor; eauto using SemSB.sem_equation).
           - change true with (negb false).
             eapply Son_abs2; eauto.
             destruct Cky as [[]|(?&?&?)]; auto.
             assert (present c = absent) by sem_det; discriminate.
           - simpl; split; eauto; reflexivity.
           - econstructor; eauto.
             instantiate (1 := empty_memory _); discriminate.
         }

    - do 2 (econstructor; auto).
      destruct Mfby as (?&?& Spec).
      specialize (Spec n); destruct (find_val x (M n)) eqn: E; try contradiction.
      specialize (Var n); specialize (Arg n).
      pose proof Arg as Arg'.
      destruct (ls n); destruct Spec as (?& Hxs); rewrite Hxs in Var; inv Arg'; eauto using sem_equation.
  Qed.

  Lemma not_Is_defined_not_Is_state_in_eqs:
    forall x eqs,
      ~ Is_defined_in_eqs x eqs ->
      ~ Is_state_in_eqs x (translate_eqns eqs).
  Proof.
    unfold translate_eqns, concatMap.
    induction eqs as [|eq]; simpl; intros Notin Hin.
    - inv Hin.
    - apply Exists_app' in Hin as [Hin|].
      + destruct eq; simpl in Hin.
        * inversion_clear Hin as [?? Hin'|?? Hin']; inv Hin'.
        *{ destruct i; try destruct o; inversion_clear Hin as [?? Hin'|?? Hin'].
           - inv Hin'; apply Notin; do 3 constructor; auto.
           - inversion_clear Hin' as [?? Hin|?? Hin]; inv Hin;
               apply Notin; do 3 constructor; auto.
           - inv Hin'; apply Notin; do 3 constructor; auto.
           - inv Hin'.
         }
        * inversion_clear Hin as [?? Hin'|?? Hin']; inv Hin'.
      + apply IHeqs; auto.
        apply not_Is_defined_in_cons in Notin as []; auto.
  Qed.

  Lemma Nodup_defs_translate_eqns:
    forall eq eqs G bk H M M',
      msem_equation G bk H M M' eq ->
      NoDup_defs (eq :: eqs) ->
      translate_eqn_nodup_states eq (translate_eqns eqs).
  Proof.
    destruct eq; inversion_clear 1; inversion_clear 1; econstructor; eauto.
    - apply not_Is_defined_not_Is_state_in_eqs.
      assert (In x i) by (now apply hd_error_Some_In); auto.
    - apply not_Is_defined_not_Is_state_in_eqs.
      assert (In x i) by (now apply hd_error_Some_In); auto.
  Qed.

  Corollary equations_correctness:
    forall G bk H M M' eqs vars,
      (forall f xss M M' yss,
          msem_node G f xss M M' yss ->
          sem_block_n (translate G) f M xss yss M') ->
      Ordered_nodes G ->
      Forall (wc_equation G vars) eqs ->
      Forall (clock_match bk H) vars ->
      NoDup_defs eqs ->
      Forall (msem_equation G bk H M M') eqs ->
      exists Is, sem_equations_n (translate G) bk H M Is M' (translate_eqns eqs).
  Proof.
    intros ** WC ?? Heqs.
    unfold translate_eqns, concatMap.
    induction eqs as [|eq eqs IHeqs]; simpl; inv WC.
    - exists (fun n => Env.empty state); constructor.
    - apply Forall_cons2 in Heqs as [Heq Heqs].
      apply IHeqs in Heqs as (?&?); auto.
      + eapply equation_correctness; eauto.
        eapply Nodup_defs_translate_eqns; eauto.
      + eapply NoDup_defs_cons; eauto.
  Qed.

  Lemma clock_of_correctness:
    forall xss bk,
      ExprSem.clock_of xss bk ->
      forall n, clock_of (xss n) (bk n).
  Proof. auto. Qed.

  Lemma same_clock_correctness:
    forall xss,
      ExprSem.same_clock xss ->
      forall n, same_clock (xss n).
  Proof. auto. Qed.
  Hint Resolve clock_of_correctness same_clock_correctness.

  Lemma not_Is_node_in_not_Is_block_in:
    forall eqs f,
      ~ Is_node_in f eqs ->
      ~ Is_block_in f (translate_eqns eqs).
  Proof.
    unfold translate_eqns, concatMap.
    induction eqs as [|eq]; simpl; intros ** Hnin Hin.
    - inv Hin.
    - apply not_Is_node_in_cons in Hnin as (Hnineq & Hnin).
      apply IHeqs in Hnin.
      destruct eq; simpl in *.
      + inversion_clear Hin as [?? E|?? Hins]; try inv E; auto.
      + destruct i; auto.
        destruct o as [|]; inversion_clear Hin as [?? E|?? Hins]; auto.
        * inv E; apply Hnineq; constructor.
        * inversion_clear Hins as [?? E|?? Hins']; auto.
          inv E; apply Hnineq; constructor.
        * inv E; apply Hnineq; constructor.
      + inversion_clear Hin as [?? E|?? Hins]; try inv E; auto.
  Qed.

  Theorem correctness:
    forall G f xss M M' yss,
      Ordered_nodes G ->
      wc_global G ->
      msem_node G f xss M M' yss ->
      sem_block_n (translate G) f M xss yss M'.
  Proof.
    induction G as [|node ? IH].
    inversion 3;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros ** Hord WC Hsem n.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [???????? Clock Hfind Ins Outs ???? Heqs].
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hord; inversion_clear Hord as [|??? NodeIn].
    pose proof Hfind as Hfind'.
    simpl in Hfind.
    assert (Ordered_blocks (translate_node node :: translate G))
      by (change (translate_node node :: translate G) with (translate (node :: G));
          apply Ordered_nodes_blocks; auto).
    inversion WC as [|??? (?&?&?& WCeqs)]; subst.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - inversion Hfind; subst n0.
      apply find_node_translate in Hfind' as (?&?&?&?); subst.
      eapply Forall_msem_equation_global_tl in Heqs; eauto.
      pose proof (NoDup_defs_node node).
      eapply equations_correctness in Heqs as (?&Heqs); eauto.
      + econstructor; eauto.
        * specialize (Ins n); destruct node; simpl in *.
          rewrite map_fst_idty; eauto.
        * specialize (Outs n); destruct node; simpl in *.
          rewrite map_fst_idty; eauto.
        * apply sem_equations_cons2; eauto.
          apply not_Is_node_in_not_Is_block_in; auto.
      + rewrite idck_app, Forall_app; split.
        * eapply sem_clocked_vars_clock_match; eauto.
          rewrite map_fst_idck; eauto.
        *{ apply Forall_forall; intros (x, ck) ?.
           rewrite idck_app in WCeqs.
           eapply clock_match_eqs with (eqs := node.(n_eqs)); eauto.
           - rewrite <-idck_app, NoDupMembers_idck.
             apply n_nodup.
           - eapply msem_sem_equations; eauto.
           - rewrite map_fst_idck.
             apply n_defd.
         }
    - assert (n_name node <> f) by now apply ident_eqb_neq.
      eapply msem_node_cons, IH in Hsem; eauto.
      apply sem_block_cons2; auto using Ordered_blocks.
  Qed.

End CORRECTNESS.
