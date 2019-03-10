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
    intros ** Closed Heqs ?? Hin.
    destruct n; simpl in *.
    unfold gather_eqs in *.
    clear - Heqs Hin.
    revert Hin; generalize (@nil (ident * ident)).
    induction n_eqs0 as [|[] ? IH]; simpl in *; intros; try contradiction;
      inversion_clear Heqs as [|?? Heq]; inv Heq; eauto.
    - destruct i; try discriminate; eauto.
    - destruct i; try discriminate; eauto.
    - apply In_fst_fold_left_gather_eq in Hin as [Hin|]; eauto.
      destruct Hin as [E|]; try contradiction; inv E.
      match goal with H: mfby _ _ _ _ _ _ |- _ => destruct H as (?&?) end; auto.
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
    inversion_clear Hsem' as [???????? Clock Hfind Ins ????? Heqs Closed].
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hord; inversion_clear Hord as [|??? NodeIn].
    pose proof Hfind as Hfind'.
    simpl in Hfind.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - inversion Hfind; subst n.
      apply find_node_translate in Hfind' as (?&?&Hfind'&?); subst.
      pose proof Hfind';
        simpl in Hfind'; rewrite Hnf in Hfind'; inv Hfind'.
      eapply msem_equations_cons in Heqs; eauto.
      econstructor; eauto.
      + eapply msem_eqs_reset_lasts; eauto.
      + intros ** Hin.
        destruct node; simpl in *.
        edestruct msem_eqs_In_snd_gather_eqs_spec
          as (?& Mx &?&?& [Node|(rs & Reset)] & Sub); eauto.
        inversion_clear Reset as [?????? Nodes].
        destruct (Nodes (count rs 0)) as (M0 &?& Node & Mmask &?).
        apply IH in Node; auto.
        specialize (Mmask 0); specialize (Sub 0).
        rewrite <-Mmask in Sub; auto.
        eexists; split; eauto.
    - assert (n_name node <> f) by now apply ident_eqb_neq.
      eapply msem_node_cons in Hsem; eauto.
      simpl; rewrite <-initial_state_other; eauto.
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

  (* Lemma transient_states_closed_add: *)
  (*   forall P insts I x f M, *)
  (*     transient_states_closed P insts I -> *)
  (*     transient_states_closed P ([(x, f)] ++ insts) (Env.add x M I). *)
  (* Proof. *)
  (*   intros ** Trans. *)
  (*   apply Forall_app; split. *)
  (*   - constructor; auto. *)
  (*     setoid_rewrite Env.gss; inversion_clear 1. *)
  (*     admit. *)
  (*   - SearchAbout Forall app. *)
  (*   unfold transient_states_closed.  *)

  Inductive memory_closed_rec: global -> ident -> memory val -> Prop :=
    memory_closed_rec_intro:
      forall G f M n,
        find_node f G = Some n ->
        (forall x, find_val x M <> None -> In x (gather_mems n.(n_eqs))) ->
        (forall i M', find_inst i M = Some M' ->
              exists f',
                In (i, f') (gather_insts n.(n_eqs))
                /\ memory_closed_rec G f' M') ->
        memory_closed_rec G f M.

  Definition memory_closed_rec_n (G: global) (f: ident) (M: memories) : Prop :=
    forall n, memory_closed_rec G f (M n).

  Lemma memory_closed_rec_other:
    forall M G f node,
      Ordered_nodes (node :: G) ->
      node.(n_name) <> f ->
      (memory_closed_rec (node :: G) f M
       <-> memory_closed_rec G f M).
  Proof.
    induction M as [? IH] using memory_ind'; unfold sub_inst in *.
    split; inversion_clear 1 as [???? Find ? Insts].
    - apply find_node_other in Find; auto.
      econstructor; eauto.
      intros ** Find'; pose proof Find';
        apply Insts in Find' as (?& Hin & Closed).
      erewrite IH in Closed; eauto.
      rewrite <-gather_eqs_snd_spec in Hin.
      apply In_snd_gather_eqs_Is_node_in in Hin.
      intro; subst; contradict Hin.
      eapply find_node_later_not_Is_node_in; eauto.
    - pose proof Find; eapply find_node_other in Find; eauto.
      econstructor; eauto.
      intros ** Find'; pose proof Find';
        apply Insts in Find' as (?& Hin & Closed).
      erewrite <-IH in Closed; eauto.
      rewrite <-gather_eqs_snd_spec in Hin.
      apply In_snd_gather_eqs_Is_node_in in Hin.
      intro; subst; contradict Hin.
      eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Lemma memory_closed_rec_n_other:
    forall M G f node,
      Ordered_nodes (node :: G) ->
      node.(n_name) <> f ->
      (memory_closed_rec_n (node :: G) f M
       <-> memory_closed_rec_n G f M).
  Proof.
    split; intros Closed n; specialize (Closed n).
    - apply memory_closed_rec_other in Closed; auto.
    - apply memory_closed_rec_other; auto.
  Qed.

  Lemma msem_equations_memory_closed_rec:
    forall eqs G bk H M M' n x f Mx,
      (forall f xss M M' yss,
          msem_node G f xss M M' yss ->
          memory_closed_rec_n G f M) ->
      Forall (msem_equation G bk H M M') eqs ->
      find_inst x (M n) = Some Mx ->
      In (x, f) (gather_insts eqs) ->
      memory_closed_rec G f Mx.
  Proof.
    unfold gather_insts, concatMap.
    induction eqs as [|eq]; simpl; intros ** IH Heqs Find Hin;
      inversion_clear Heqs as [|?? Heq]; try contradiction.
    apply in_app in Hin as [Hin|]; eauto.
    destruct eq; simpl in Hin; try contradiction.
    destruct i; try contradiction.
    inversion_clear Hin as [E|]; try contradiction; inv E.
    inversion_clear Heq as [|????????????? Hd Sub ??? Node|
                            ???????????????? Hd Sub ????? Rst|];
      unfold sub_inst_n, sub_inst in Sub;
      inv Hd; rewrite Sub in Find; inv Find.
    - eapply IH; eauto.
    - inversion_clear Rst as [?????? Nodes].
      specialize (Nodes (count rs n)); destruct Nodes as (?&?& Node & Mask &?).
      apply IH in Node.
      rewrite <-Mask; auto.
  Qed.

  Lemma msem_node_memory_closed_rec_n:
    forall G f xss M M' yss,
      Ordered_nodes G ->
      msem_node G f xss M M' yss ->
      memory_closed_rec_n G f M.
  Proof.
    induction G as [|node]; intros ????? Ord;
      inversion_clear 1 as [????????? Find ?????? Heqs Closed]; try now inv Find.
    pose proof Find; simpl in Find.
    destruct (ident_eqb node.(n_name) f) eqn:Eq.
    - inv Find.
      econstructor; eauto.
      + apply Closed.
      + intros ** Find_i.
        assert (exists f', In (i, f') (gather_insts (n_eqs n))) as (f' & Hin)
            by (eapply InMembers_In, Closed, not_None_is_Some; eauto).
        eexists; split; eauto.
        assert (f' <> n.(n_name)).
        { rewrite <-gather_eqs_snd_spec in Hin.
          apply In_snd_gather_eqs_Is_node_in in Hin.
          intro; subst; contradict Hin; eapply find_node_not_Is_node_in; eauto.
        }
        apply memory_closed_rec_other; auto.
        assert (~ Is_node_in (n_name n) (n_eqs n))
          by (eapply find_node_not_Is_node_in; eauto).
        apply msem_equations_cons in Heqs; auto.
        inv Ord.
        eapply msem_equations_memory_closed_rec; eauto.
    - apply ident_eqb_neq in Eq.
      apply memory_closed_rec_n_other; auto.
      inv Ord.
      eapply IHG; eauto.
      econstructor; eauto.
      eapply msem_equations_cons; eauto using Ordered_nodes.
      eapply find_node_later_not_Is_node_in; eauto using Ordered_nodes.
  Qed.

  (* Lemma state_closed_find_block_other: *)
  (*   forall S bl P P' b b', *)
  (*     find_block b P = Some (bl, P') -> *)
  (*     state_closed P b' S -> *)
  (*     state_closed P' b' S. *)
  (* Proof. *)
  (*   inversion_clear 2. *)
  (*   - econstructor; eauto. *)
  (*     SearchAbout find_block Ordered_blocks.  *)

  Lemma memory_closed_rec_state_closed:
    forall M G f,
      memory_closed_rec G f M ->
      state_closed (translate G) f M.
  Proof.
    induction M as [? IH] using memory_ind'.
    inversion_clear 1 as [???? Find ? Insts].
    apply find_node_translate in Find as (?&?&?&?); subst.
    econstructor; eauto.  ; simpl. (* IN BLOCLS ! *)
    - intros ** ??; rewrite gather_eqs_fst_spec; auto.
    - unfold sub_inst in *.
      intros ** Find; pose proof Find as Find'.
      apply Insts in Find as (?&?& Closed).
      setoid_rewrite gather_eqs_snd_spec; eexists; split; eauto.
      eapply IH in Closed; eauto.
      SearchAbout state_closed cons.

      SearchAbout gather_mems.

  Lemma equation_correctness:
    forall G eq eqs bk H M M' Is vars insts,
      (forall f xss M M' yss,
          msem_node G f xss M M' yss ->
          sem_block_n (translate G) f M xss yss M') ->
      Ordered_nodes G ->
      wc_equation G vars eq ->
      Forall (clock_match bk H) vars ->
      translate_eqn_nodup_states eq eqs ->
      (forall n, transient_states_closed (translate G) insts (Is n)) ->
      msem_equation G bk H M M' eq ->
      sem_equations_n (translate G) bk H M Is M' eqs ->
      exists Is',
        sem_equations_n (translate G) bk H M Is' M' (translate_eqn eq ++ eqs)
        /\ forall n, transient_states_closed (translate G) (gather_inst_eq eq ++ insts) (Is' n).
  Proof.
    intros ** IHnode Hord WC ClkM TrNodup Closed Heq Heqs.
    destruct Heq as [| |????????????????????? Var Hr Reset|?????????? Arg Var Mfby];
      inv TrNodup; simpl.

    - eexists; split; eauto.
      do 2 (econstructor; eauto).

    - destruct xs; try discriminate.
      match goal with
      | H: hd_error ?l = Some x,
           H': hd_error ?l = _ |- _ =>
        rewrite H' in H; inv H; simpl in H'; inv H'
      end.
      exists (add_n x Mx Is); split.
      + constructor; auto.
        *{ econstructor; eauto.
           - eexists; split; eauto; reflexivity.
           - apply Env.gss.
           - now apply IHnode.
         }
        * apply sem_equations_n_add_n; auto.
      + apply msem_node_memory_closed_rec_n in H5; auto.   admit.

    - destruct xs; try discriminate.
      match goal with
      | H: hd_error ?l = Some x,
           H': hd_error ?l = _ |- _ =>
        rewrite H' in H; inv H; simpl in H'; inv H'
      end.
      exists (fun n => Env.add x (if rs n then Mx 0 else Mx n) (Is n)); split.
      + intro.
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
        *{ specialize (Heqs' (fun n => Mx 0) n).
           assert (Env.find x (Env.add x (Mx 0) (Is n)) = Some (Mx 0))
             by apply Env.gss.
           constructor; auto; [|constructor; auto].
           - destruct (ys n); try discriminate.
             econstructor; eauto.
             + eapply Son; eauto.
               destruct Cky as [[]|(?&?&?)]; auto.
               assert (present c = absent) by sem_det; discriminate.
             + simpl; rewrite <-Mmask_0; auto.
             eapply msem_node_initial_state; eauto.
           - eapply SemSB.SEqCall with (Is := Mx 0); eauto.
             + congruence.
             + eapply sem_block_equal_memory; eauto; reflexivity.   (* TODO: fix rewriting here? *)
         }
        *{ specialize (Heqs' Mx n).
           assert (Env.find x (Env.add x (Mx n) (Is n)) = Some (Mx n))
             by apply Env.gss.
           destruct (ys n) eqn: E'.
           - do 2 (econstructor; eauto using SemSB.sem_equation).
             + apply Son_abs1; auto.
               destruct Cky as [[]|(c &?&?)]; auto.
               assert (present c = absent) by sem_det; discriminate.
             + simpl; eexists; split; eauto; reflexivity.
             + econstructor; eauto.
               discriminate.
           - do 2 (econstructor; eauto using SemSB.sem_equation).
             + change true with (negb false).
               eapply Son_abs2; eauto.
               destruct Cky as [[]|(?&?&?)]; auto.
               assert (present c = absent) by sem_det; discriminate.
             + simpl; eexists; split; eauto; reflexivity.
             + econstructor; eauto.
               discriminate.
         }
      + admit.

    - do 3 (econstructor; auto).
      destruct Mfby as (?&?& Spec).
      specialize (Spec n); destruct (find_val x (M n)) eqn: E; try contradiction.
      specialize (Var n); specialize (Arg n).
      pose proof Arg as Arg'.
      destruct (ls n); destruct Spec as (?& Hxs); rewrite Hxs in Var; inv Arg';
        econstructor; eauto; simpl; auto.
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
      exists Is, sem_equations_n (translate G) bk H M Is M' (translate_eqns eqs)
            /\ forall n, transient_states_closed (translate G) (gather_insts eqs) (Is n).
  Proof.
    intros ** WC ?? Heqs.
    unfold translate_eqns, concatMap.
    induction eqs as [|eq eqs IHeqs]; simpl; inv WC.
    - exists (fun n => Env.empty state); split; constructor.
    - apply Forall_cons2 in Heqs as [Heq Heqs].
      apply IHeqs in Heqs as (?&?&?); auto.
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

  Lemma memory_closed_state_closed_lasts:
    forall M eqs (n: nat),
      memory_closed (M n) eqs ->
      state_closed_lasts (map fst (fst (gather_eqs eqs))) (M n).
  Proof.
    intros ** (?&?) ??.
    setoid_rewrite gather_eqs_fst_spec; auto.
  Qed.

  Lemma memory_closed_state_closed_insts:
    forall P M eqs (n: nat),
      memory_closed (M n) eqs ->
      state_closed_insts P (snd (gather_eqs eqs)) (M n).
  Proof.
    intros ** (?&?) ???.
    setoid_rewrite gather_eqs_snd_spec.
    admit.
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
    inversion_clear Hsem' as [???????? Clock Hfind Ins Outs ???? Heqs Closed Closed'].
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
      eapply msem_equations_cons in Heqs; eauto.
      pose proof (NoDup_defs_node node).
      eapply equations_correctness in Heqs as (I & Heqs); eauto.
      + econstructor; eauto.
        * specialize (Ins n); destruct node; simpl in *.
          rewrite map_fst_idty; eauto.
        * specialize (Outs n); destruct node; simpl in *.
          rewrite map_fst_idty; eauto.
        (* * intro; eapply msem_node_absent in Hsem; eauto. *)
        * apply sem_equations_cons; eauto.
          apply not_Is_node_in_not_Is_block_in; auto.
        *{ econstructor; eauto.
           - now apply memory_closed_state_closed_lasts.
           - admit.
         }
        *  simpl. SearchAbout gather_eqs snd. unfold transient_states_closed; simpl. admit.
        *{ econstructor; eauto.
           - now apply memory_closed_state_closed_lasts.
           - admit.
         }
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
