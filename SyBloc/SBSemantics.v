Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Setoid.
Require Import Morphisms.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.RMemory.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.NLustre.NLExprSemantics.
Require Import Velus.NLustre.Stream.

Module Type SBSEMANTICS
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX       Op)
       (Import Clks    : CLOCKS          Ids)
       (Import ExprSyn : NLEXPRSYNTAX        Op)
       (Import Syn     : SBSYNTAX        Ids Op Clks ExprSyn)
       (Import Str     : STREAM              Op OpAux)
       (Import ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn Str).

  (* Record mvalue := *)
  (*   Mvalue { content_i: val; *)
  (*            reset_i: bool *)
  (*          }. *)

  Record mvalues :=
    Mvalues { content: stream val;
              reset: stream bool
            }.

  (* Definition memory := RMemory.memory mvalue. *)
  Definition memories := RMemory.memory mvalues.

  Inductive reset_regs: stream bool -> memories -> Prop :=
    reset_regs_intro:
      forall M rs,
        (forall x mvs,
            find_val x M = Some mvs ->
            forall n, rs n = true -> mvs.(reset) n = true) ->
        (forall x M',
            sub_inst x M M' ->
            reset_regs rs M') ->
        reset_regs rs M.

  Inductive mfby: ident -> val -> stream value -> memories -> stream value -> Prop :=
    mfby_intro:
      forall x mvs v0 ls M xs,
        find_val x M = Some mvs ->
        mvs.(content) 0 = v0 ->
        (forall n, match ls n with
              | absent =>
                mvs.(content) (S n) = (if mvs.(reset) (S n) then v0 else mvs.(content) n)
                /\ xs n = absent
              | present v =>
                mvs.(content) (S n) = (if mvs.(reset) (S n) then v0 else v)
                /\ xs n = present (mvs.(content) n)
              end) ->
        mfby x v0 ls M xs.

  Definition fby_eq (mems: PS.t) (eq: equation) : PS.t :=
    match eq with
    | EqFby x _ _ _ => PS.add x mems
    | _ => mems
    end.

  Definition fbys (eqs: list equation) : PS.t :=
    fold_left fby_eq eqs PS.empty.

  Definition inst_eq (insts: PS.t) (eq: equation) : PS.t :=
    match eq with
    | EqReset _ _ i _ => PS.add i insts
    | EqCall _ _ _ i _ => PS.add i insts
    | _ => insts
    end.

  Definition insts (eqs: list equation) : PS.t :=
    fold_left inst_eq eqs PS.empty.

  Definition well_structured_memories (eqs: list equation) (M: memories) :=
    (forall x,
        find_val x M <> None <-> PS.In x (fbys eqs))
    /\ forall x,
      find_inst x M <> None <-> PS.In x (insts eqs).

  Section BlockSemantics.

    Variable P: program.

    Inductive sem_equation: stream bool -> history -> memories -> equation -> Prop :=
    | SEqDef:
        forall bk H M x xs ck ce,
          sem_var H x xs ->
          sem_caexp bk H ck ce xs ->
          sem_equation bk H M (EqDef x ck ce)
    | SEqFby:
        forall bk H M x ck c0 e xs ls,
          sem_var H x xs ->
          sem_laexp bk H ck e ls ->
          mfby x (sem_const c0) ls M xs ->
          sem_equation bk H M (EqFby x ck c0 e)
    | SEqReset:
        forall bk H M ck b i r rs M',
          sem_var H r rs ->
          sub_inst i M M' ->
          reset_regs (reset_of rs) M' ->
          sem_equation bk H M (EqReset ck b i r)
    | SEqCall:
        forall bk H M ys M' ck b i es ess oss,
          sem_laexps bk H ck es ess ->
          sub_inst i M M' ->
          sem_block b M' ess oss ->
          sem_vars H ys oss ->
          sem_equation bk H M (EqCall ys ck b i es)

    with sem_block: ident -> memories -> stream (list value) -> stream (list value) -> Prop :=
           SBlock:
             forall b bl P' M H xss yss bk,
               clock_of xss bk ->
               find_block b P = Some (bl, P') ->
               sem_vars H (map fst bl.(b_in)) xss ->
               sem_vars H (map fst bl.(b_out)) yss ->
               same_clock xss ->
               same_clock yss ->
               (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
               Forall (sem_equation bk H M) bl.(b_eqs) ->
               well_structured_memories bl.(b_eqs) M ->
               sem_block b M xss yss.

  End BlockSemantics.

  Section sem_block_mult.
    Variable P: program.

    Variable P_equation: stream bool -> history -> memories -> equation -> Prop.
    Variable P_block: ident -> memories -> stream (list value) -> stream (list value) -> Prop.

    Hypothesis EqDefCase:
      forall bk H M x xs ck ce,
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        P_equation bk H M (EqDef x ck ce).

    Hypothesis EqFbyCase:
      forall bk H M x ck c0 e xs ls,
        sem_var H x xs ->
        sem_laexp bk H ck e ls ->
        mfby x (sem_const c0) ls M xs ->
        P_equation bk H M (EqFby x ck c0 e).

    Hypothesis EqResetCase:
      forall bk H M ck b i r rs M',
        sem_var H r rs ->
        sub_inst i M M' ->
        reset_regs (reset_of rs) M' ->
        P_equation bk H M (EqReset ck b i r).

    Hypothesis EqCallCase:
      forall bk H M ys M' ck b i es ess oss,
        sem_laexps bk H ck es ess ->
        sub_inst i M M' ->
        sem_block P b M' ess oss ->
        sem_vars H ys oss ->
        P_block b M' ess oss ->
        P_equation bk H M (EqCall ys ck b i es).

    Hypothesis BlockCase:
      forall b bl P' M H xss yss bk,
        clock_of xss bk ->
        find_block b P = Some (bl, P') ->
        sem_vars H (map fst bl.(b_in)) xss ->
        sem_vars H (map fst bl.(b_out)) yss ->
        same_clock xss ->
        same_clock yss ->
        (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
        Forall (sem_equation P bk H M) bl.(b_eqs) ->
        well_structured_memories bl.(b_eqs) M ->
        Forall (P_equation bk H M) bl.(b_eqs) ->
        P_block b M xss yss.

    Fixpoint sem_equation_mult
            (b: stream bool) (H: history) (M: memories) (e: equation)
            (Sem: sem_equation P b H M e) {struct Sem}
      : P_equation b H M e
    with sem_block_mult
           (f: ident) (M: memories) (xss oss: stream (list value))
           (Sem: sem_block P f M xss oss) {struct Sem}
         : P_block f M xss oss.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem.
        eapply BlockCase; eauto.
        match goal with H: well_structured_memories _ _ |- _ => clear H end.
        match goal with H: Forall _ _ |- _ => induction H; auto end.
    Qed.

    Combined Scheme sem_equation_block_ind from
             sem_equation_mult, sem_block_mult.

  End sem_block_mult.

  (** Morphisms properties *)

  Add Parametric Morphism P b M: (sem_block P b M)
      with signature eq_str ==> eq_str ==> Basics.impl
        as sem_node_eq_str.
  Proof.
    intros ** E1 ? ? E2 Block.
    inv Block.
    econstructor; eauto; intro; try rewrite <-E1; try rewrite <-E2; auto.
  Qed.

  Lemma sem_block_wf:
    forall P f M xss yss,
      sem_block P f M xss yss ->
      wf_streams xss /\ wf_streams yss.
  Proof.
    intros ** Sem; split; inv Sem;
      assert_const_length xss; assert_const_length yss; auto.
  Qed.

  Lemma sem_EqCall_gt0:
    forall P bk H M xs ck b i es,
      sem_equation P bk H M (EqCall xs ck b i es) ->
      0 < length xs.
  Proof.
    inversion_clear 1 as [| | |????????????? Block' Vars].
    inversion_clear Block' as [??????????? Out].
    specialize (Out 0); specialize (Vars 0); simpl in *;
      apply Forall2_length in Out; apply Forall2_length in Vars.
    rewrite <-Out in Vars; rewrite Vars, map_length; apply b_outgt0.
  Qed.

  Lemma In_fold_left_fby_eq:
    forall x eqs m,
      PS.In x (fold_left fby_eq eqs m)
      <-> PS.In x (fbys eqs) \/ PS.In x m.
  Proof.
    unfold fbys.
    induction eqs as [|eq].
    - split; auto.
      destruct 1 as [H|].
      apply not_In_empty in H; contradiction.
      auto.
    - split.
      + intro H.
        simpl; rewrite IHeqs.
        simpl in H; apply IHeqs in H; destruct H; auto.
        destruct eq; auto.
        apply PS.add_spec in H.
        destruct H.
        rewrite H; left; right; apply PS.add_spec; intuition.
        intuition.
      + destruct 1 as [H|H].
        * simpl in H; rewrite IHeqs in H; apply IHeqs; destruct H; auto.
          right.
          destruct eq; try (apply not_In_empty in H; contradiction).
          simpl; apply PS.add_spec.
          apply PS.add_spec in H; destruct H;
            try apply not_In_empty in H; intuition.
        * apply IHeqs; right; destruct eq; auto.
          apply PS.add_spec; auto.
  Qed.

  Lemma In_fold_left_inst_eq:
    forall x eqs m,
      PS.In x (fold_left inst_eq eqs m)
      <-> PS.In x (insts eqs) \/ PS.In x m.
  Proof.
    unfold insts.
    induction eqs as [|eq].
    - split; auto.
      destruct 1 as [H|].
      apply not_In_empty in H; contradiction.
      auto.
    - split.
      + intro H.
        simpl; rewrite IHeqs.
        simpl in H; apply IHeqs in H; destruct H; auto.
        destruct eq; auto; apply PS.add_spec in H; destruct H; auto;
          rewrite H; left; right; apply PS.add_spec; auto.
      + destruct 1 as [H|H].
        * simpl in H; rewrite IHeqs in H; apply IHeqs; destruct H; auto.
          right.
          destruct eq; try (apply not_In_empty in H; contradiction);
            simpl; apply PS.add_spec;
              apply PS.add_spec in H; destruct H; auto;
                apply not_In_empty in H; contradiction.
        * apply IHeqs; right; destruct eq; auto;
            apply PS.add_spec; auto.
  Qed.

  Lemma well_structured_def:
    forall M x ck e eqs,
      well_structured_memories (EqDef x ck e :: eqs) M <->
      well_structured_memories eqs M.
  Proof.
    split; eauto.
  Qed.

  Lemma well_structured_add_inst_call:
    forall M M' xs ck f i es eqs,
      well_structured_memories eqs M ->
      well_structured_memories (EqCall xs ck f i es :: eqs) (add_inst i M' M).
  Proof.
    intros ** WS.
    constructor; unfold fbys, insts; simpl; split; intro H.
    - rewrite find_val_add_inst in H; apply WS in H; auto.
    - rewrite find_val_add_inst; apply WS in H; auto.
    - rewrite In_fold_left_inst_eq.
      destruct (ident_eqb x i) eqn: E;
        [apply ident_eqb_eq in E; subst|apply ident_eqb_neq in E].
      + right; apply PSE.MP.Dec.F.add_1; auto.
      + rewrite find_inst_gso in H; auto.
        apply WS in H; auto.
    - destruct (ident_eqb x i) eqn: E;
        [apply ident_eqb_eq in E; subst|apply ident_eqb_neq in E].
      + rewrite find_inst_gss; intro; discriminate.
      + rewrite find_inst_gso; auto.
        apply WS.
        apply In_fold_left_inst_eq in H as [|H]; auto.
        apply PSE.MP.Dec.F.add_3 in H; auto.
        contradict H; apply not_In_empty.
  Qed.

  Lemma well_structured_reset_call:
    forall M xs ck f i es ck_r r eqs,
      well_structured_memories (EqCall xs ck f i es :: eqs) M ->
      well_structured_memories (EqReset ck_r f i r :: EqCall xs ck f i es :: eqs) M.
  Proof.
    inversion_clear 1 as [Vals Insts].
    constructor; unfold fbys, insts in *; simpl in *.
    - intro; rewrite Vals; reflexivity.
    - intro; rewrite Insts.
      rewrite 2 In_fold_left_inst_eq.
      split; intros [H|H']; auto.
      + rewrite PSE.MP.Dec.F.add_iff; auto.
      + apply PSE.MP.Dec.F.add_iff in H' as []; auto.
        rewrite PSE.MP.Dec.F.add_iff; auto.
  Qed.

  Corollary well_structured_add_inst_reset_call:
    forall M M' xs ck f i es ck_r r eqs,
      well_structured_memories eqs M ->
      well_structured_memories (EqReset ck_r f i r :: EqCall xs ck f i es :: eqs) (add_inst i M' M).
  Proof.
    intros; apply well_structured_reset_call, well_structured_add_inst_call; auto.
  Qed.

  Lemma well_structured_add_val_fby:
    forall M mvs x ck v0 e eqs,
      well_structured_memories eqs M ->
      well_structured_memories (EqFby x ck v0 e :: eqs) (add_val x mvs M).
  Proof.
    intros ** WS.
    constructor; unfold fbys, insts; simpl; split; intro H.
    - rewrite In_fold_left_fby_eq.
      destruct (ident_eqb x x0) eqn: E;
        [apply ident_eqb_eq in E; subst|apply ident_eqb_neq in E].
      + right; apply PSE.MP.Dec.F.add_1; auto.
      + rewrite find_val_gso in H; auto.
        apply WS in H; auto.
    - destruct (ident_eqb x x0) eqn: E;
        [apply ident_eqb_eq in E; subst|apply ident_eqb_neq in E].
      + rewrite find_val_gss; intro; discriminate.
      + rewrite find_val_gso; auto.
        apply WS.
        apply In_fold_left_fby_eq in H as [|H]; auto.
        apply PSE.MP.Dec.F.add_3 in H; auto.
        contradict H; apply not_In_empty.
    - rewrite find_inst_add_val in H; apply WS in H; auto.
    - rewrite find_inst_add_val; apply WS in H; auto.
  Qed.

End SBSEMANTICS.
